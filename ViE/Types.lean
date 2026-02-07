import Lean
import ViE.Data.PieceTable

namespace ViE



/-- Editor Mode -/
inductive Mode where
  | normal
  | insert
  | command
  | searchForward
  | searchBackward
  | visual
  | visualBlock
  deriving Repr, BEq, Inhabited

instance : ToString Mode where
  toString
    | .normal => "NORMAL"
    | .insert => "INSERT"
    | .command => "COMMAND"
    | .searchForward => "SEARCH"
    | .searchBackward => "SEARCH"
    | .visual => "VISUAL"
    | .visualBlock => "VISUAL BLOCK"

/-- Row index (0-based) with dimensional safety -/
structure Row where
  val : Nat
  deriving Repr, BEq, Ord, Hashable

/-- Column index (0-based) with dimensional safety -/
structure Col where
  val : Nat
  deriving Repr, BEq, Ord

/-- Cursor position with dimensional type safety -/
structure Point where
  row : Row
  col : Col
  deriving Repr, BEq

-- Row helper functions
namespace Row
  def zero : Row := ⟨0⟩
  def succ (r : Row) : Row := ⟨r.val + 1⟩
  def pred (r : Row) : Row := ⟨r.val.pred⟩
  instance : ToString Row := ⟨fun r => toString r.val⟩
end Row

instance : OfNat Row n := ⟨⟨n⟩⟩
instance : LT Row := ⟨fun a b => a.val < b.val⟩
instance : LE Row := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : Row) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : Row) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
instance : Min Row := ⟨fun a b => if a.val ≤ b.val then a else b⟩
instance : Max Row := ⟨fun a b => if a.val ≥ b.val then a else b⟩
instance : Add Row := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub Row := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : HAdd Row Nat Row := ⟨fun r n => ⟨r.val + n⟩⟩
instance : HSub Row Nat Row := ⟨fun r n => ⟨r.val - n⟩⟩
instance : Coe Row Nat := ⟨(·.val)⟩

instance : GetElem (List α) Row α (fun l r => r.val < l.length) where
  getElem l r h := l[r.val]

instance : GetElem (Array α) Row α (fun a r => r.val < a.size) where
  getElem a r h := a[r.val]

-- Col helper functions
namespace Col
  def zero : Col := ⟨0⟩
  def succ (c : Col) : Col := ⟨c.val + 1⟩
  def pred (c : Col) : Col := ⟨c.val.pred⟩
  instance : ToString Col := ⟨fun c => toString c.val⟩
end Col

instance : OfNat Col n := ⟨⟨n⟩⟩
instance : LT Col := ⟨fun a b => a.val < b.val⟩
instance : LE Col := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : Col) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : Col) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
instance : Min Col := ⟨fun a b => if a.val ≤ b.val then a else b⟩
instance : Max Col := ⟨fun a b => if a.val ≥ b.val then a else b⟩
instance : Add Col := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub Col := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : HAdd Col Nat Col := ⟨fun c n => ⟨c.val + n⟩⟩
instance : HSub Col Nat Col := ⟨fun c n => ⟨c.val - n⟩⟩
instance : Coe Col Nat := ⟨(·.val)⟩

instance : GetElem (List α) Col α (fun l c => c.val < l.length) where
  getElem l c h := l[c.val]

instance : GetElem (Array α) Col α (fun a c => c.val < a.size) where
  getElem a c h := a[c.val]

-- Point helper functions
namespace Point
  def zero : Point := ⟨Row.zero, Col.zero⟩
  def make (row : Row) (col : Col) : Point := ⟨row, col⟩
  def fromNat (r c : Nat) : Point := ⟨⟨r⟩, ⟨c⟩⟩
end Point

-- Inhabited instances
instance : Inhabited Row := ⟨Row.zero⟩
instance : Inhabited Col := ⟨Col.zero⟩
instance : Inhabited Point := ⟨Point.zero⟩

/-- A line is an array of characters for O(1) indexing -/
abbrev Line := Array Char

/-- A text buffer is an array of lines (2D character array) -/
abbrev TextBuffer := Array Line

structure EditorConfig where
  showLineNumbers : Bool
  vSplitStr : String
  hSplitStr : String
  emptyLineMarker : String
  statusBarStyle : String
  resetStyle : String
  fileIcon : String
  dirIcon : String
  searchHighlightStyle : String
  searchHighlightCursorStyle : String
  searchBloomCacheMax : Nat
  searchBloomBuildLeafBits : Bool
  historyLimit : Nat := 100
  deriving Inhabited

inductive SearchDirection where
  | forward
  | backward
  deriving Repr, Inhabited, BEq

structure SearchState where
  pattern : String
  direction : SearchDirection
  useBloom : Bool
  lastMatch : Option Nat
  lastSearchOffset : Nat
  cache : Array Nat
  cacheMax : Nat
  lineMatches : Lean.RBMap Row (String × Array (Nat × Nat)) compare
  lineOrder : Array Row
  lineCacheMax : Nat
  bloomCache : Lean.RBMap Nat ByteArray compare
  bloomOrder : Array Nat
  bloomCacheMax : Nat
  deriving Inhabited

inductive RegisterKind where
  | charwise
  | linewise
  | blockwise
  deriving Repr, Inhabited, BEq

structure Register where
  kind : RegisterKind
  text : String
  blockLines : List String
  blockWidth : Nat
  deriving Repr, Inhabited

inductive Key where
  | char (c : Char)
  | ctrl (c : Char)
  | alt (c : Char)
  | esc
  | backspace
  | enter
  | left | right | up | down
  | unknown (c : Char)
  deriving Repr, BEq, Inhabited

structure RenderCache where
  /-- Visual string for a line, cached to avoid re-calculating widths/tabs/etc. -/
  -- Cache key includes scroll column and available width to avoid stale renders.
  lineMap : Lean.RBMap Row (String × Nat × Nat) compare
  /-- Raw line string cache (no display transform). -/
  rawLineMap : Lean.RBMap Row String compare
  /-- Display-column to byte-offset index cache for a line. -/
  lineIndexMap : Lean.RBMap Row (Array (Nat × Nat)) compare
  deriving Inhabited

namespace RenderCache
  def find (c : RenderCache) (r : Row) : Option (String × Nat × Nat) :=
    c.lineMap.find? r

  def findRaw (c : RenderCache) (r : Row) : Option String :=
    c.rawLineMap.find? r

  def findIndex (c : RenderCache) (r : Row) : Option (Array (Nat × Nat)) :=
    c.lineIndexMap.find? r

  def update (c : RenderCache) (r : Row) (s : String) (scrollCol : Nat) (availableWidth : Nat) : RenderCache :=
    { c with lineMap := c.lineMap.insert r (s, scrollCol, availableWidth) }

  def updateRaw (c : RenderCache) (r : Row) (s : String) : RenderCache :=
    { c with rawLineMap := c.rawLineMap.insert r s }

  def updateIndex (c : RenderCache) (r : Row) (idx : Array (Nat × Nat)) : RenderCache :=
    { c with lineIndexMap := c.lineIndexMap.insert r idx }
end RenderCache

structure FileBuffer where
  id : Nat
  filename : Option String
  dirty : Bool
  table : PieceTable
  missingEol : Bool
  cache : RenderCache
  deriving Inhabited

-- Manual Repr instance
instance : Repr FileBuffer where
  reprPrec buf _ :=
    s!"FileBuffer(id={buf.id}, file={buf.filename}, dirty={buf.dirty}, lines={buf.table.lineCount})"

def initialFileBuffer : FileBuffer := {
  id := 0
  filename := none
  dirty := false
  table := ViE.PieceTable.fromString ""
  missingEol := false
  cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
}

namespace FileBuffer
  def lineCount (buf : FileBuffer) : Nat :=
    buf.table.lineCount

  def recomputeMissingEol (buf : FileBuffer) : FileBuffer :=
    let len := buf.table.length
    let missing := if len == 0 then false else !buf.table.endsWithNewline
    { buf with missingEol := missing }

  def clearCache (buf : FileBuffer) : FileBuffer :=
    { buf with cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty } }
end FileBuffer

structure ViewState where
  bufferId : Nat
  cursor : Point
  scrollRow : Row
  scrollCol : Col
  deriving Repr, Inhabited

/-- File entry for explorer -/
structure FileEntry where
  name : String
  path : String
  isDirectory : Bool
  deriving Repr, Inhabited

/-- Explorer state for file navigation -/
inductive ExplorerMode where
  | files
  | workgroups
  | workspaces
  deriving Repr, Inhabited, BEq

structure ExplorerState where
  currentPath : String
  entries : List FileEntry
  selectedIndex : Nat
  mode : ExplorerMode
  previewWindowId : Option Nat
  previewBufferId : Option Nat
  deriving Repr, Inhabited


inductive Layout where
  | window (id : Nat) (view : ViewState)
  | hsplit (left right : Layout) (ratio : Float)
  | vsplit (top bottom : Layout) (ratio : Float)
  deriving Repr, Inhabited

/-- Temporary input state that doesn't need to persist -/
structure InputState where
  previousKey : Option Char
  countBuffer : String
  commandBuffer : String
  pendingKeys : String
  lastInputTime : Nat
  lastSearchInputTime : Nat
  lastSearchRunTime : Nat
  pendingSearch : Bool
  deriving Repr, Inhabited


/-- State for a single workspace (project unit). -/
structure WorkspaceState where
  name : String
  rootPath : Option String
  buffers : List FileBuffer
  nextBufferId : Nat
  layout : Layout
  activeWindowId : Nat
  nextWindowId : Nat
  deriving Repr, Inhabited

/-- State for a single workgroup (collection of workspaces). -/
structure WorkgroupState where
  name : String
  workspaces : Array WorkspaceState
  currentWorkspace : Nat
  deriving Repr, Inhabited

structure EditorState where
  mode : Mode
  -- Workgroup management
  workgroups : Array WorkgroupState
  currentGroup : Nat
  -- Global State
  message : String
  shouldQuit : Bool
  config : EditorConfig
  clipboard : Option Register -- Yank buffer
  selectionStart : Option Point -- Visual mode anchor
  explorers : List (Nat × ExplorerState) -- BufferId × Explorer state
  searchState : Option SearchState
  -- Temporary input state
  inputState : InputState
  -- UI dimensions (updated frequently)
  windowHeight : Nat
  windowWidth : Nat
  -- Rendering optimization
  dirty : Bool

/-- Key mapping function type. -/
structure KeyMap where
  normal : EditorState → Key → IO EditorState
  insert : EditorState → Key → IO EditorState
  command : EditorState → Key → IO EditorState
  visual : EditorState → Key → IO EditorState
  visualBlock : EditorState → Key → IO EditorState

/-- Command action type: arguments -> state -> IO new state -/
abbrev CommandAction := List String → EditorState → IO EditorState

/-- Map of command names to actions -/
abbrev CommandMap := List (String × CommandAction)

/-- The complete user configuration. -/
structure Config where
  settings : EditorConfig
  bindings : KeyMap
  commands : CommandMap

inductive Direction where
  | left
  | right
  | up
  | down
  deriving Repr, BEq, Inhabited

structure SessionState where
  files : List String
  activeFileIndex : Nat
  cursors : List (Nat × Nat) -- Row, Col per file
  deriving Repr, Inhabited


end ViE
