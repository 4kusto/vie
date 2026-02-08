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
    if wg.currentWorkspace < wg.workspaces.size then
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

def Layout.findWindowIdByBufferId (l : Layout) (bufferId : Nat) : Option Nat :=
  match l with
  | .window wid v => if v.bufferId == bufferId then some wid else none
  | .hsplit left right _ => (left.findWindowIdByBufferId bufferId).orElse (fun _ => right.findWindowIdByBufferId bufferId)
  | .vsplit top bottom _ => (top.findWindowIdByBufferId bufferId).orElse (fun _ => bottom.findWindowIdByBufferId bufferId)

def Layout.containsWindow (l : Layout) (windowId : Nat) : Bool :=
  match l with
  | .window wid _ => wid == windowId
  | .hsplit left right _ => left.containsWindow windowId || right.containsWindow windowId
  | .vsplit top bottom _ => top.containsWindow windowId || bottom.containsWindow windowId

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
  let ws := s.getCurrentWorkspace
  let view := ws.layout.findView ws.activeWindowId
  let s' :=
    s.updateCurrentWorkspace fun ws =>
      match view with
      | some v =>
        let newBuffers := ws.buffers.map fun b =>
          if b.id == v.bufferId then
            let updated := FileBuffer.recomputeMissingEol (f b)
            FileBuffer.clearCache updated
          else b
        { ws with buffers := newBuffers }
      | none => ws
  match view, s'.searchState with
  | some v, some ss =>
      {
        s' with
          searchState := some {
            ss with
              lineCacheBufferId := some v.bufferId
              lineMatches := Lean.RBMap.empty
              lineOrder := #[]
          }
      }
  | _, _ => s'


def EditorState.getScroll (s : EditorState) : Row × Col :=
  let ws := s.getCurrentWorkspace
  match ws.layout.findView ws.activeWindowId with
  | some v => (v.scrollRow, v.scrollCol)
  | none => (Row.zero, Col.zero)

def EditorState.updateActiveView (s : EditorState) (f : ViewState → ViewState) : EditorState :=
  s.updateCurrentWorkspace fun ws =>
    { ws with layout := ws.layout.updateView ws.activeWindowId f }

def WorkspaceState.isFloatingWindow (ws : WorkspaceState) (windowId : Nat) : Bool :=
  ws.floatingWindows.contains windowId

def WorkspaceState.setWindowFloating (ws : WorkspaceState) (windowId : Nat) (enabled : Bool) : WorkspaceState :=
  if enabled then
    if ws.floatingWindows.contains windowId then ws
    else { ws with floatingWindows := windowId :: ws.floatingWindows }
  else
    {
      ws with
        floatingWindows := ws.floatingWindows.filter (fun wid => wid != windowId)
        floatingWindowOffsets := ws.floatingWindowOffsets.filter (fun (wid, _, _) => wid != windowId)
    }

def WorkspaceState.toggleWindowFloating (ws : WorkspaceState) (windowId : Nat) : WorkspaceState :=
  ws.setWindowFloating windowId (!ws.isFloatingWindow windowId)

def WorkspaceState.pruneFloatingWindows (ws : WorkspaceState) : WorkspaceState :=
  let rec idsOf (l : Layout) : List Nat :=
    match l with
    | .window id _ => [id]
    | .hsplit left right _ => idsOf left ++ idsOf right
    | .vsplit top bottom _ => idsOf top ++ idsOf bottom
  let ids := idsOf ws.layout
  {
    ws with
      floatingWindows := ws.floatingWindows.filter (fun wid => ids.contains wid)
      floatingWindowOffsets := ws.floatingWindowOffsets.filter (fun (wid, _, _) => ids.contains wid)
  }

def WorkspaceState.getFloatingWindowIds (ws : WorkspaceState) : Array Nat :=
  ws.floatingWindows.foldl (fun acc wid =>
    match ws.layout.findView wid with
    | some _ => acc.push wid
    | none => acc) #[]

def WorkspaceState.floatingWindowIndex? (ws : WorkspaceState) (windowId : Nat) : Option Nat :=
  let ids := ws.getFloatingWindowIds
  let rec loop (i : Nat) : Option Nat :=
    if i >= ids.size then
      none
    else if ids[i]! == windowId then
      some i
    else
      loop (i + 1)
  loop 0

def WorkspaceState.getFloatingWindowOffset (ws : WorkspaceState) (windowId : Nat) : Int × Int :=
  match ws.floatingWindowOffsets.find? (fun (wid, _, _) => wid == windowId) with
  | some (_, rowOff, colOff) => (rowOff, colOff)
  | none => (0, 0)

def WorkspaceState.setFloatingWindowOffset (ws : WorkspaceState) (windowId : Nat) (rowOff colOff : Int) : WorkspaceState :=
  let rest := ws.floatingWindowOffsets.filter (fun (wid, _, _) => wid != windowId)
  { ws with floatingWindowOffsets := (windowId, rowOff, colOff) :: rest }

def WorkspaceState.adjustFloatingWindowOffset (ws : WorkspaceState) (windowId : Nat) (dRow dCol : Int) : WorkspaceState :=
  let (rowOff, colOff) := ws.getFloatingWindowOffset windowId
  ws.setFloatingWindowOffset windowId (rowOff + dRow) (colOff + dCol)

structure FloatingWindowBorderFlags where
  top : Bool := true
  right : Bool := true
  bottom : Bool := true
  left : Bool := true
  deriving Inhabited

def WorkspaceState.layoutAllFloating (ws : WorkspaceState) (l : Layout) : Bool :=
  match l with
  | .window id _ => ws.isFloatingWindow id
  | .hsplit left right _ => ws.layoutAllFloating left && ws.layoutAllFloating right
  | .vsplit top bottom _ => ws.layoutAllFloating top && ws.layoutAllFloating bottom

def WorkspaceState.findFloatingSubtree (ws : WorkspaceState) (windowId : Nat) : Option Layout :=
  let rec go (l : Layout) : Option Layout :=
    if !l.containsWindow windowId then
      none
    else if ws.layoutAllFloating l then
      -- Outermost subtree containing the target where all descendants are floating.
      some l
    else
      match l with
      | .hsplit left right _ => (go left).orElse (fun _ => go right)
      | .vsplit top bottom _ => (go top).orElse (fun _ => go bottom)
      | .window _ _ => none
  go ws.layout

def computeFloatingWindowBounds (rows cols idx : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let availableRows := if rows > 1 then rows - 1 else rows
  if availableRows < 6 || cols < 16 then
    none
  else
    let hMax := availableRows - 2
    let wMax := cols - 4
    let h := min hMax (max 8 ((availableRows * 3) / 5))
    let w := min wMax (max 24 ((cols * 3) / 5))
    let topBase := (availableRows - h) / 2
    let leftBase := (cols - w) / 2
    let top := min (availableRows - h) (topBase + idx)
    let left := min (cols - w) (leftBase + (2 * idx))
    some (top, left, h, w)

def EditorState.getFloatingWindowBounds (s : EditorState) (windowId : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let ws := s.getCurrentWorkspace
  let floatingIds := ws.getFloatingWindowIds
  let rec indexOf (ids : Array Nat) (target : Nat) (i : Nat := 0) : Option Nat :=
    if i >= ids.size then none
    else if ids[i]! == target then some i
    else indexOf ids target (i + 1)

  let splitByRatio (total : Nat) (ratio : Float) : Option (Nat × Nat) :=
    if total < 2 then
      none
    else
      let raw := (Float.ofNat total * ratio).toUInt64.toNat
      let first := max 1 (min (total - 1) raw)
      some (first, total - first)

  let rec idsOfLayout (l : Layout) : List Nat :=
    match l with
    | .window id _ => [id]
    | .hsplit left right _ => idsOfLayout left ++ idsOfLayout right
    | .vsplit top bottom _ => idsOfLayout top ++ idsOfLayout bottom

  let minFloatingIndexOf (l : Layout) : Option Nat :=
    let ids := idsOfLayout l
    let rec loop (xs : List Nat) (best : Option Nat) : Option Nat :=
      match xs with
      | [] => best
      | id :: rest =>
        match indexOf floatingIds id, best with
        | some i, none => loop rest (some i)
        | some i, some b => loop rest (some (min i b))
        | none, _ => loop rest best
    loop ids none

  let rec locateInFloatingSubtree
      (l : Layout) (top left h w : Nat)
      : Option (Nat × Nat × Nat × Nat) :=
    match l with
    | .window id _ =>
      if id == windowId then some (top, left, h, w) else none
    | .hsplit leftL rightL ratio =>
      match splitByRatio w ratio with
      | none => none
      | some (leftW, rightW) =>
        (locateInFloatingSubtree leftL top left h leftW).orElse
          (fun _ => locateInFloatingSubtree rightL top (left + leftW) h rightW)
    | .vsplit topL bottomL ratio =>
      match splitByRatio h ratio with
      | none => none
      | some (topH, bottomH) =>
        (locateInFloatingSubtree topL top left topH w).orElse
          (fun _ => locateInFloatingSubtree bottomL (top + topH) left bottomH w)

  let floatingSubtreeBounds : Option (Nat × Nat × Nat × Nat) :=
    match ws.findFloatingSubtree windowId with
    | none => none
    | some subtree =>
      match minFloatingIndexOf subtree with
      | none => none
      | some groupIdx =>
        match computeFloatingWindowBounds s.windowHeight s.windowWidth groupIdx with
        | some (top, left, h, w) =>
          locateInFloatingSubtree subtree top left h w
        | none => none
  let baseBounds :=
    match floatingSubtreeBounds with
    | some b => some b
    | none =>
      match ws.floatingWindowIndex? windowId with
      | none => none
      | some idx => computeFloatingWindowBounds s.windowHeight s.windowWidth idx

  let toNatNonNeg (v : Int) : Nat :=
    if v < 0 then 0 else Int.toNat v

  let applyOffset (b : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
    let (top, left, h, w) := b
    let (rowOff, colOff) := ws.getFloatingWindowOffset windowId
    let availableRows := if s.windowHeight > 1 then s.windowHeight - 1 else s.windowHeight
    let maxTop := if availableRows > h then availableRows - h else 0
    let maxLeft := if s.windowWidth > w then s.windowWidth - w else 0
    let rawTop := Int.ofNat top + rowOff
    let rawLeft := Int.ofNat left + colOff
    let top' := min maxTop (toNatNonNeg rawTop)
    let left' := min maxLeft (toNatNonNeg rawLeft)
    (top', left', h, w)

  baseBounds.map applyOffset

def EditorState.getFloatingWindowBorderFlags (s : EditorState) (windowId : Nat) : FloatingWindowBorderFlags :=
  let ws := s.getCurrentWorkspace
  let rec locateFlags
      (l : Layout)
      (acc : FloatingWindowBorderFlags)
      : Option FloatingWindowBorderFlags :=
    match l with
    | .window id _ =>
      if id == windowId then some acc else none
    | .hsplit left right _ =>
      let leftFlags := { acc with right := false }
      match locateFlags left leftFlags with
      | some f => some f
      | none =>
        let rightFlags := { acc with left := true }
        locateFlags right rightFlags
    | .vsplit top bottom _ =>
      let topFlags := { acc with bottom := false }
      match locateFlags top topFlags with
      | some f => some f
      | none =>
        let bottomFlags := { acc with top := true }
        locateFlags bottom bottomFlags
  match ws.findFloatingSubtree windowId with
  | some subtree =>
    (locateFlags subtree { top := true, right := true, bottom := true, left := true }).getD
      { top := true, right := true, bottom := true, left := true }
  | none => { top := true, right := true, bottom := true, left := true }


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

def EditorState.getActiveWindowScrollBounds (s : EditorState) : Nat × Nat :=
  let ws := s.getCurrentWorkspace
  let activeId := ws.activeWindowId
  if ws.isFloatingWindow activeId then
    match s.getFloatingWindowBounds activeId with
    | some (_, _, h, w) =>
      -- Floating window has a border, so scrollable area is smaller than outer bounds.
      let borderFlags := s.getFloatingWindowBorderFlags activeId
      let topBottomBorders := (if borderFlags.top then 1 else 0) + (if borderFlags.bottom then 1 else 0)
      let contentRows := if h > topBottomBorders then h - topBottomBorders else 1
      let h' := contentRows + 1
      let sideBorders := (if borderFlags.left then 1 else 0) + (if borderFlags.right then 1 else 0)
      let w' := if w > sideBorders then w - sideBorders else 1
      (h', w')
    | none =>
      s.getActiveWindowBounds
  else
    s.getActiveWindowBounds


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
