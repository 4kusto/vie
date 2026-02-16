import ViE.State
import ViE.Types
import ViE.Buffer.Content
import ViE.Buffer.LowIO
import ViE.Workspace

namespace ViE.Buffer

open ViE

def createNewBuffer (state : EditorState) (content : TextBuffer) (filename : Option String) : (Nat × EditorState) :=
  let s' := state.updateCurrentWorkspace fun ws =>
    let id := ws.nextBufferId
    let buildLeafBits := state.config.searchBloomBuildLeafBits
    let buf : FileBuffer := ViE.Buffer.fileBufferFromTextBufferWithConfig id filename content buildLeafBits
    { ws with buffers := buf :: ws.buffers, nextBufferId := id + 1 }
  let ws := s'.getCurrentWorkspace
  (ws.nextBufferId - 1, s')

def addBuffer (state : EditorState) (buf : FileBuffer) : (Nat × EditorState) :=
  let s' := state.updateCurrentWorkspace fun ws =>
    let id := ws.nextBufferId
    let newBuf := { buf with id := id }
    { ws with buffers := newBuf :: ws.buffers, nextBufferId := id + 1 }
  let ws := s'.getCurrentWorkspace
  (ws.nextBufferId - 1, s')

def removeBuffer (state : EditorState) (bufId : Nat) : EditorState :=
  state.updateCurrentWorkspace fun ws =>
    { ws with buffers := ws.buffers.filter (fun b => b.id != bufId) }

def ensureBufferLoadedById (state : EditorState) (bufId : Nat) : IO EditorState := do
  let ws := state.getCurrentWorkspace
  match ws.buffers.find? (fun b => b.id == bufId) with
  | none => pure state
  | some buf =>
      if buf.loaded || buf.filename.isNone then
        pure state
      else
        let fname := buf.filename.getD ""
        let loadedBuf ← ViE.loadBufferByteArrayWithConfig fname state.config
        let merged := {
          loadedBuf with
            id := buf.id
            dirty := buf.dirty
            loaded := true
            table := { loadedBuf.table with undoLimit := state.config.historyLimit }
        }
        let s' := state.updateCurrentWorkspace fun ws =>
          { ws with buffers := ws.buffers.map (fun b => if b.id == buf.id then merged else b) }
        pure { s' with message := s!"Loaded \"{fname}\"" }

def ensureActiveBufferLoaded (state : EditorState) : IO EditorState := do
  let ws := state.getCurrentWorkspace
  match ws.layout.findView ws.activeWindowId with
  | none => pure state
  | some v => ensureBufferLoadedById state v.bufferId

def findBufferByFilename (state : EditorState) (fname : String) : Option Nat :=
  let ws := state.getCurrentWorkspace
  ws.buffers.find? (fun b => b.filename == some fname) |>.map (fun b => b.id)

/-- Open a file buffer in the active window. Loads from disk if necessary. -/
def openBuffer (state : EditorState) (filename : String) : IO EditorState := do
  let resolvedPath := state.getCurrentWorkspace.resolvePath filename
  match findBufferByFilename state resolvedPath with
  | some bid =>
    -- Switch to existing buffer; load if it is a lazy placeholder.
    let s' := state.updateActiveView fun v => { v with bufferId := bid, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
    let s'' ← ensureBufferLoadedById s' bid
    return { s'' with message := s!"Switched to \"{filename}\"" }
  | none =>
    try
      let loadedBuf ← ViE.loadBufferByteArrayWithConfig resolvedPath state.config
      -- Assign new ID and add to workgroup
      let s' := state.updateCurrentWorkspace fun ws =>
        let id := ws.nextBufferId
        let buf := { loadedBuf with
          id := id
          table := { loadedBuf.table with undoLimit := state.config.historyLimit }
        }
        { ws with buffers := buf :: ws.buffers, nextBufferId := id + 1 }

      let ws := s'.getCurrentWorkspace
      let bid := ws.nextBufferId - 1

      let s'' := s'.updateActiveView fun v => { v with bufferId := bid, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
      return { s'' with message := s!"Loaded \"{filename}\"" }
    catch e =>
      return { state with message := s!"Error loading file: {e}" }


end ViE.Buffer
