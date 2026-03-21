import ViE.State
import ViE.Unicode

namespace ViE.Buffer.EditQueue

open ViE

inductive InsertOp where
  | char (c : Char)
  | newline
  | backspace
  deriving Inhabited

structure WorkerState where
  buffer : FileBuffer
  cursor : Point
  tabStop : Nat
  deriving Inhabited

structure WorkerKey where
  sessionId : Nat
  bufferId : Nat
  deriving Repr, BEq, Ord, Inhabited

structure WorkerEntry where
  baseSig : UInt64
  submitted : Nat
  applied : Nat
  task : Task (Except IO.Error WorkerState)

private def bufferSig (b : FileBuffer) : UInt64 :=
  mixHash (hash b.table.tree.length) (hash b.table.tree.lineBreaks)

initialize workersRef : IO.Ref (Lean.RBMap WorkerKey WorkerEntry compare) ←
  IO.mkRef Lean.RBMap.empty

initialize sessionCounterRef : IO.Ref Nat ← IO.mkRef 1

def ensureSessionId (s : EditorState) : IO EditorState := do
  if s.editSessionId != 0 then
    pure s
  else
    let sid ← sessionCounterRef.modifyGet fun n => (n, n + 1)
    pure { s with editSessionId := sid }

private def applyInsertOp (ws : WorkerState) (op : InsertOp) : WorkerState :=
  match op with
  | .char c =>
      match ViE.getOffsetFromPointInBufferWithTabStop ws.buffer ws.cursor.row ws.cursor.col ws.tabStop with
      | none => ws
      | some offset =>
          let b' := { ws.buffer with table := ws.buffer.table.insert offset (c.toString) offset, dirty := true }
          let b'' := FileBuffer.clearCache (FileBuffer.recomputeMissingEol b')
          let delta := ViE.Unicode.charWidthAt ws.tabStop ws.cursor.col.val c
          { ws with buffer := b'', cursor := { ws.cursor with col := ⟨ws.cursor.col.val + delta⟩ } }
  | .newline =>
      match ViE.getOffsetFromPointInBufferWithTabStop ws.buffer ws.cursor.row ws.cursor.col ws.tabStop with
      | none => ws
      | some offset =>
          let b' := { ws.buffer with table := ws.buffer.table.insert offset "\n" offset, dirty := true }
          let b'' := FileBuffer.clearCache (FileBuffer.recomputeMissingEol b')
          { ws with buffer := b'', cursor := { row := ⟨ws.cursor.row.val + 1⟩, col := 0 } }
  | .backspace =>
      if ws.cursor.col.val > 0 then
        let prevC := ViE.prevCol ws.tabStop ws.buffer ws.cursor.row ws.cursor.col
        match ViE.getOffsetFromPointInBufferWithTabStop ws.buffer ws.cursor.row prevC ws.tabStop,
              ViE.getOffsetFromPointInBufferWithTabStop ws.buffer ws.cursor.row ws.cursor.col ws.tabStop with
        | some startOff, some endOff =>
            let len := endOff - startOff
            if len > 0 then
              let b' := { ws.buffer with table := ws.buffer.table.delete startOff len endOff, dirty := true }
              let b'' := FileBuffer.clearCache (FileBuffer.recomputeMissingEol b')
              { ws with buffer := b'', cursor := { ws.cursor with col := prevC } }
            else
              ws
        | _, _ => ws
      else if ws.cursor.row.val > 0 then
        let prevRow : Row := ⟨ws.cursor.row.val - 1⟩
        match ws.buffer.table.getLineRange prevRow.val with
        | some (start, len) =>
            let b' := { ws.buffer with table := ws.buffer.table.delete (start + len) 1 (start + len), dirty := true }
            let b'' := FileBuffer.clearCache (FileBuffer.recomputeMissingEol b')
            let newLen := ViE.lineDisplayWidth ws.tabStop b'' prevRow
            { ws with buffer := b'', cursor := { row := prevRow, col := ⟨newLen⟩ } }
        | none => ws
      else
        ws

private def applyWorkerStateToBuffer (s : EditorState) (bufferId : Nat) (ws : WorkerState) : EditorState :=
  let s1 := s.updateCurrentWorkspace fun cur =>
    { cur with
      buffers := cur.buffers.map fun b =>
        if b.id == bufferId then
          { ws.buffer with id := b.id, filename := b.filename, loaded := true, dirty := true }
        else
          b
    }
  let active := s1.getCurrentWorkspace.layout.findView s1.getCurrentWorkspace.activeWindowId
  let s2 :=
    match active with
    | some v =>
        if v.bufferId == bufferId then
          s1.setCursor ws.cursor
        else
          s1
    | none => s1
  { s2 with dirty := true }

private def enqueueInsertOp (s : EditorState) (op : InsertOp) : IO EditorState := do
  let ws := s.getCurrentWorkspace
  match ws.layout.findView ws.activeWindowId with
  | none => pure s
  | some view =>
      let bufferId := view.bufferId
      let key : WorkerKey := { sessionId := s.editSessionId, bufferId := bufferId }
      let snapshot : WorkerState := {
        buffer := s.getActiveBuffer
        cursor := view.cursor
        tabStop := s.config.tabStop
      }
      let sig := bufferSig snapshot.buffer
      let workers ← workersRef.get
      match workers.find? key with
      | none =>
          let t ← IO.asTask (pure (applyInsertOp snapshot op))
          let e : WorkerEntry := { baseSig := sig, submitted := 1, applied := 0, task := t }
          workersRef.set (workers.insert key e)
      | some e =>
          if e.baseSig == sig then
            let prev := e.task
            let t ← IO.asTask do
              match prev.get with
              | .ok st => pure (applyInsertOp st op)
              | .error err => throw err
            let e' : WorkerEntry := { e with submitted := e.submitted + 1, task := t }
            workersRef.set (workers.insert key e')
          else
            let t ← IO.asTask (pure (applyInsertOp snapshot op))
            let e' : WorkerEntry := { baseSig := sig, submitted := 1, applied := 0, task := t }
            workersRef.set (workers.insert key e')
      let s' :=
        match op with
        | .char c =>
            let delta := ViE.Unicode.charWidthAt s.config.tabStop view.cursor.col.val c
            s.setCursor { view.cursor with col := ⟨view.cursor.col.val + delta⟩ }
        | .newline =>
            s.setCursor { row := ⟨view.cursor.row.val + 1⟩, col := 0 }
        | .backspace =>
            if view.cursor.col.val > 0 then
              let prevC := ViE.prevCol s.config.tabStop s.getActiveBuffer view.cursor.row view.cursor.col
              s.setCursor { view.cursor with col := prevC }
            else if view.cursor.row.val > 0 then
              let prevRow : Row := ⟨view.cursor.row.val - 1⟩
              let newLen := ViE.lineDisplayWidth s.config.tabStop s.getActiveBuffer prevRow
              s.setCursor { row := prevRow, col := ⟨newLen⟩ }
            else
              s
      pure { s' with dirty := true }

def enqueueInsertChar (s : EditorState) (c : Char) : IO EditorState :=
  enqueueInsertOp s (.char c)

def enqueueInsertNewline (s : EditorState) : IO EditorState :=
  enqueueInsertOp s .newline

def enqueueBackspace (s : EditorState) : IO EditorState :=
  enqueueInsertOp s .backspace

def awaitActiveInsertOps (s : EditorState) : IO EditorState := do
  let ws := s.getCurrentWorkspace
  match ws.layout.findView ws.activeWindowId with
  | none => pure s
  | some view =>
      let bufferId := view.bufferId
      let key : WorkerKey := { sessionId := s.editSessionId, bufferId := bufferId }
      let workers ← workersRef.get
      match workers.find? key with
      | none => pure s
      | some e =>
          if e.applied >= e.submitted then
            workersRef.set (workers.erase key)
            pure s
          else
            let res := e.task.get
            workersRef.set (workers.erase key)
            match res with
            | .ok wsState => pure (applyWorkerStateToBuffer s bufferId wsState)
            | .error err => pure { s with message := s!"Insert worker error: {err}" }

def drainCompletedInsertOps (s : EditorState) : IO (EditorState × Bool) := do
  let workers ← workersRef.get
  let keys : Array WorkerKey := workers.fold (init := #[]) (fun acc k _ => acc.push k)
  let mut map := workers
  let mut st := s
  let mut changed := false
  for k in keys do
    match map.find? k with
    | none => pure ()
      | some e =>
          if e.applied >= e.submitted then
            map := map.erase k
          else
            let done ← IO.hasFinished e.task
            if done then
              let res := e.task.get
              map := map.erase k
              match res with
              | .ok wsState =>
                  if k.sessionId == s.editSessionId then
                    st := applyWorkerStateToBuffer st k.bufferId wsState
                  else
                    pure ()
                  changed := true
              | .error err =>
                  st := { st with message := s!"Insert worker error (session {k.sessionId}, buffer {k.bufferId}): {err}", dirty := true }
                  changed := true
  workersRef.set map
  pure (st, changed)

end ViE.Buffer.EditQueue
