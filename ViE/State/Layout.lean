import ViE.State.Config
import ViE.Types
import ViE.Buffer.Content

namespace ViE

/-- Get current workgroup -/
def EditorState.getCurrentWorkgroup (s : EditorState) : WorkgroupState :=
  s.workgroups[s.currentGroup]!

/-- Update current workgroup -/
def EditorState.updateCurrentWorkgroup (s : EditorState) (f : WorkgroupState → WorkgroupState) : EditorState :=
  { s with workgroups := s.workgroups.set! s.currentGroup (f (s.getCurrentWorkgroup)) }

/-- Get current workspace within the active workgroup -/
def EditorState.getCurrentWorkspace (s : EditorState) : WorkspaceState :=
  let wg := s.getCurrentWorkgroup
  wg.workspaces[wg.currentWorkspace]!

/-- Update current workspace within the active workgroup -/
def EditorState.updateCurrentWorkspace (s : EditorState) (f : WorkspaceState → WorkspaceState) : EditorState :=
  s.updateCurrentWorkgroup fun wg =>
    if h : wg.currentWorkspace < wg.workspaces.size then
      let ws := wg.workspaces[wg.currentWorkspace]!
      let updated := f ws
      { wg with workspaces := wg.workspaces.set! wg.currentWorkspace updated }
    else
      wg

/-- Switch to workgroup n -/
def EditorState.switchToWorkgroup (s : EditorState) (n : Nat) : EditorState :=
  if n < s.workgroups.size then
    { s with currentGroup := n }
  else
    s

/- Helper functions to access/modify the active view -/

def Layout.findView (l : Layout) (id : Nat) : Option ViewState :=
  match l with
  | .window wid v => if wid == id then some v else none
  | .hsplit left right _ => (left.findView id).orElse (fun _ => right.findView id)
  | .vsplit top bottom _ => (top.findView id).orElse (fun _ => bottom.findView id)

/-- Update a view in the layout tree. Returns (updated layout, found flag) -/
def Layout.updateView (l : Layout) (id : Nat) (f : ViewState → ViewState) : Layout :=
  let rec update (l : Layout) : Layout × Bool :=
    match l with
    | .window wid v =>
      if wid == id then (.window wid (f v), true) else (l, false)
    | .hsplit left right ratio =>
      let (newLeft, found) := update left
      if found then
        (.hsplit newLeft right ratio, true)
      else
        let (newRight, found') := update right
        (.hsplit newLeft newRight ratio, found')
    | .vsplit top bottom ratio =>
      let (newTop, found) := update top
      if found then
        (.vsplit newTop bottom ratio, true)
      else
        let (newBottom, found') := update bottom
        (.vsplit newTop newBottom ratio, found')
  (update l).1


def Layout.remove (l : Layout) (id : Nat) : Option Layout :=
  match l with
  | .window wid _ => if wid == id then none else some l
  | .hsplit left right ratio =>
    match left.remove id with
    | none => some right
    | some newLeft =>
      match right.remove id with
      | none => some newLeft
      | some newRight => some (.hsplit newLeft newRight ratio)
  | .vsplit top bottom ratio =>
    match top.remove id with
    | none => some bottom
    | some newTop =>
      match bottom.remove id with
      | none => some newTop
      | some newBottom => some (.vsplit newTop newBottom ratio)


def EditorState.getActiveBuffer (s : EditorState) : FileBuffer :=
  let ws := s.getCurrentWorkspace
  match ws.layout.findView ws.activeWindowId with
  | some v => ws.buffers.find? (fun b => b.id == v.bufferId) |>.getD initialBuffer
  | none => initialBuffer


def EditorState.updateActiveBuffer (s : EditorState) (f : FileBuffer -> FileBuffer) : EditorState :=
  s.updateCurrentWorkspace fun ws =>
    let view := ws.layout.findView ws.activeWindowId
    match view with
    | some v =>
      let newBuffers := ws.buffers.map fun b => if b.id == v.bufferId then FileBuffer.clearCache (f b) else b
      { ws with buffers := newBuffers }
    | none => ws


def EditorState.getScroll (s : EditorState) : Row × Col :=
  let ws := s.getCurrentWorkspace
  match ws.layout.findView ws.activeWindowId with
  | some v => (v.scrollRow, v.scrollCol)
  | none => (Row.zero, Col.zero)

def EditorState.updateActiveView (s : EditorState) (f : ViewState → ViewState) : EditorState :=
  s.updateCurrentWorkspace fun ws =>
    { ws with layout := ws.layout.updateView ws.activeWindowId f }


def EditorState.getActiveWindowBounds (s : EditorState) : Nat × Nat :=
  let ws := s.getCurrentWorkspace
  let rec findBounds (l : Layout) (h w : Nat) : Option (Nat × Nat) :=
    match l with
    | .window id _ => if id == ws.activeWindowId then some (h, w) else none
    | .hsplit left right ratio =>
      let leftW := (Float.ofNat w * ratio).toUInt64.toNat
      (findBounds left h leftW).orElse (fun _ => findBounds right h (if w > leftW then w - leftW - 1 else 0))
    | .vsplit top bottom ratio =>
      let topH := (Float.ofNat h * ratio).toUInt64.toNat
      (findBounds top topH w).orElse (fun _ => findBounds bottom (if h > topH then h - topH - 1 else 0) w)

  -- Reserve 1 line for global status/command
  let layoutH := if s.windowHeight > 0 then s.windowHeight - 1 else 0
  (findBounds ws.layout layoutH s.windowWidth).getD (layoutH, s.windowWidth)


def getAllWindowBounds (l : Layout) (h w : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  let rec traverse (l : Layout) (r c h w : Nat) (acc : List (Nat × Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat × Nat × Nat) :=
    match l with
    | .window id _ => (id, r, c, h, w) :: acc
    | .hsplit left right ratio =>
      let leftW := (Float.ofNat w * ratio).toUInt64.toNat
      let acc' := traverse left r c h leftW acc
      traverse right r (c + leftW + 1) h (if w > leftW then w - leftW - 1 else 0) acc'
    | .vsplit top bottom ratio =>
      let topH := (Float.ofNat h * ratio).toUInt64.toNat
      let acc' := traverse top r c topH w acc
      traverse bottom (r + topH + 1) c (if h > topH then h - topH - 1 else 0) w acc'
  traverse l 0 0 h w []


def getWindowIds (l : Layout) : List Nat :=
  match l with
  | .window id _ => [id]
  | .hsplit left right _ => getWindowIds left ++ getWindowIds right
  | .vsplit top bottom _ => getWindowIds top ++ getWindowIds bottom

end ViE
