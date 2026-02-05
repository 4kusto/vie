import ViE.State
import ViE.Types
import ViE.Window.Analysis

namespace ViE.Window

open ViE

def switchWindow (state : EditorState) (dir : Direction) : EditorState :=
  let ws := state.getCurrentWorkspace
  let bounds := ViE.Window.getAllWindowBounds ws.layout (if state.windowHeight > 0 then state.windowHeight - 1 else 0) state.windowWidth
  let current := bounds.find? (fun (id, _, _, _, _) => id == ws.activeWindowId)

  match current with
  | none => state
  | some (_, r, c, h, w) =>
    -- Find candidates with orthogonal overlap
    let candidates := bounds.filter fun (id, r', c', h', w') =>
      id != ws.activeWindowId &&
      match dir with
      | .left => c' < c && (r' < r + h && r' + h' > r)
      | .right => c' >= c + w && (r' < r + h && r' + h' > r)
      | .up => r' < r && (c' < c + w && c' + w' > c)
      | .down => r' >= r + h && (c' < c + w && c' + w' > c)

    -- Filter again for adjacency/overlap
    let best := candidates.foldl (fun acc p =>
      let (_, r', c', _, _) := p
      match acc with
      | none => some p
      | some (_, br, bc, _, _) =>
         match dir with
         | .left => if c' > bc then some p else some acc.get!
         | .right => if c' < bc then some p else some acc.get!
         | .up => if r' > br then some p else some acc.get!
         | .down => if r' < br then some p else some acc.get!
    ) none

    match best with
    | some (id, _, _, _, _) => state.updateCurrentWorkspace fun ws => { ws with activeWindowId := id }
    | none => state

def closeActiveWindow (state : EditorState) : EditorState :=
  let doClose (st : EditorState) : EditorState :=
    let ws := st.getCurrentWorkspace
    match ws.layout.remove ws.activeWindowId with
    | none => { st with shouldQuit := true }
    | some newLayout =>
      st.updateCurrentWorkspace fun ws =>
        let newIds := ViE.Window.getWindowIds newLayout
        let newActiveId := match newIds with
          | [] => 0 -- Should not happen if layout valid
          | h :: _ => h
        { ws with layout := newLayout, activeWindowId := newActiveId }

  let activeBuf := state.getActiveBuffer
  let explorerOpt := state.explorers.find? (fun (id, _) => id == activeBuf.id)
  match explorerOpt with
  | none => doClose state
  | some (bufId, explorer) =>
      let s1 := { state with explorers := state.explorers.filter (fun (id, _) => id != bufId) }
      let s2 :=
        match explorer.previewWindowId with
        | none => s1
        | some previewId =>
          s1.updateCurrentWorkspace fun ws =>
            match ws.layout.remove previewId with
            | some newLayout => { ws with layout := newLayout }
            | none => ws
      let s3 :=
        match explorer.previewBufferId with
        | some previewBufId => ViE.Buffer.removeBuffer s2 previewBufId
        | none => s2
      doClose s3

def splitWindow (state : EditorState) (direction : Bool) : EditorState :=
  -- direction: true = vertical (top/bottom), false = horizontal (left/right)
  let s' := state.updateCurrentWorkspace fun ws =>
    let activeId := ws.activeWindowId
    let nextId := ws.nextWindowId
    let currentView := ws.layout.findView activeId |>.getD initialView
    let newView := currentView

    let rec updateLayout (l : Layout) : Layout :=
      match l with
      | Layout.window wid v =>
        if wid == activeId then
          if direction then Layout.vsplit (Layout.window wid v) (Layout.window nextId newView) 0.5
          else Layout.hsplit (Layout.window wid v) (Layout.window nextId newView) 0.5
        else Layout.window wid v
      | Layout.hsplit left right r => Layout.hsplit (updateLayout left) (updateLayout right) r
      | Layout.vsplit top bottom r => Layout.vsplit (updateLayout top) (updateLayout bottom) r

    { ws with layout := updateLayout ws.layout, nextWindowId := nextId + 1 }

  { s' with message := "Split window" }

/-- Result of resize operation: None (not found), Some (layout, handled) -/
abbrev ResizeResult := Option (Layout × Bool)

def resizeWindow (state : EditorState) (dir : Direction) (amount : Float) : EditorState :=
  state.updateCurrentWorkspace fun ws =>
    let activeId := ws.activeWindowId

    let rec traverse (l : Layout) : ResizeResult :=
      match l with
      | Layout.window wid v =>
        if wid == activeId then some (Layout.window wid v, false) else none
      | Layout.hsplit left right r =>
        match traverse left with
        | some (newLeft, handled) =>
          if handled then some (Layout.hsplit newLeft right r, true)
          else
            -- We are in left child, unhandled.
            match dir with
            | .left | .right => -- Horizontal resize
              let delta := if dir == .right then amount else -amount
              let newR := max 0.05 (min 0.95 (r + delta))
              some (Layout.hsplit newLeft right newR, true)
            | _ => some (Layout.hsplit newLeft right r, false)
        | none =>
          match traverse right with
          | some (newRight, handled) =>
            if handled then some (Layout.hsplit left newRight r, true)
            else
              -- We are in right child, unhandled.
              match dir with
              | .left | .right => -- Horizontal resize
                -- Consistent direction: Right (l) -> Increase ratio (move split right). Left (h) -> Decrease ratio (move split left).
                let delta := if dir == .right then amount else -amount
                let newR := max 0.05 (min 0.95 (r + delta))
                some (Layout.hsplit left newRight newR, true)
              | _ => some (Layout.hsplit left newRight r, false)
          | none => none
      | Layout.vsplit top bottom r =>
        match traverse top with
        | some (newTop, handled) =>
          if handled then some (Layout.vsplit newTop bottom r, true)
          else
            -- Top child
            match dir with
            | .up | .down => -- Vertical resize
               -- Top child: Down (j) -> Increase ratio (move split down). Up (k) -> Decrease ratio (move split up).
               let delta := if dir == .down then amount else -amount
               let newR := max 0.05 (min 0.95 (r + delta))
               some (Layout.vsplit newTop bottom newR, true)
            | _ => some (Layout.vsplit newTop bottom r, false)
        | none =>
          match traverse bottom with
          | some (newBottom, handled) =>
            if handled then some (Layout.vsplit top newBottom r, true)
            else
               -- Bottom child
               match dir with
               | .up | .down => -- Vertical resize
                 -- Bottom child: Down (j) -> Increase ratio (move split down). Up (k) -> Decrease ratio (move split up).
                 let delta := if dir == .down then amount else -amount
                 let newR := max 0.05 (min 0.95 (r + delta))
                 some (Layout.vsplit top newBottom newR, true)
               | _ => some (Layout.vsplit top newBottom r, false)
          | none => none

    match traverse ws.layout with
    | some (newLayout, _) => { ws with layout := newLayout }
    | none => ws

def cycleWindow (state : EditorState) : EditorState :=
  state.updateCurrentWorkspace fun ws =>
    let ids := ViE.Window.getWindowIds ws.layout
    if ids.isEmpty then ws
    else
      let current := ws.activeWindowId
      -- Manual index search to avoid import issues if any
      let rec findNext (list : List Nat) (sawCurrent : Bool) : Option Nat :=
        match list with
        | [] => if sawCurrent then ids.head? else none
        | id :: rest =>
          if sawCurrent then some id
          else if id == current then findNext rest true
          else findNext rest false

      match findNext ids false with
      | some nextId => { ws with activeWindowId := nextId }
      | none => { ws with activeWindowId := match ids with | [] => ws.activeWindowId | h :: _ => h }

def enforceScroll (state : EditorState) : EditorState :=
  let (h, w) := state.getActiveWindowBounds
  -- Active window height already excludes the global status line.
  let linesInView := if h > 0 then h else 1

  -- Vertical Scroll
  let (sRow, sCol) := state.getScroll
  let cursor := state.getCursor

  let state :=
    if cursor.row.val < sRow.val then
      state.setScroll cursor.row sCol
    else if cursor.row.val >= sRow.val + linesInView then
      let newScrollRow : Row := ⟨cursor.row.val - (linesInView - 1)⟩
      state.setScroll newScrollRow sCol
    else
      state

  -- Refresh scroll after potential update
  let (sRow, sCol) := state.getScroll

  -- Horizontal Scroll
  let lnWidth := if state.config.showLineNumbers then 4 else 0
  let colsInView := if w > lnWidth then w - lnWidth else 1

  let state :=
    if cursor.col.val < sCol.val then
      state.setScroll sRow cursor.col
    else if cursor.col.val >= sCol.val + colsInView then
      let newScrollCol : Col := ⟨sCol.val + colsInView - 1⟩
      state.setScroll sRow newScrollCol
    else
      state

  state

end ViE.Window
