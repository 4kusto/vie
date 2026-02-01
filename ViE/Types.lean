import ViE.Data.PieceTable

namespace ViE

open ViE.PieceTable

inductive Mode where
  | normal
  | insert
  | command
  | visual
  | visualBlock
  deriving Repr, BEq, Inhabited

instance : ToString Mode where
  toString
    | .normal => "NORMAL"
    | .insert => "INSERT"
    | .command => "COMMAND"
    | .visual => "VISUAL"
    | .visualBlock => "VISUAL BLOCK"

/-- Workspace configuration -/
structure Workspace where
  rootPath : Option String := none
  displayName : String := "Untitled"
deriving Repr

/-- Row index (0-based) with dimensional safety -/
structure Row where
  val : Nat
  deriving Repr, BEq, Ord

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
  @[simp] def add (r : Row) (n : Nat) : Row := ⟨r.val + n⟩
  @[simp] def sub (r : Row) (n : Nat) : Row := ⟨r.val - n⟩
  instance : OfNat Row n := ⟨⟨n⟩⟩
  instance : LT Row := ⟨fun a b => a.val < b.val⟩
  instance : LE Row := ⟨fun a b => a.val ≤ b.val⟩
  instance (a b : Row) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
  instance (a b : Row) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
  instance : Min Row := ⟨fun a b => if a.val ≤ b.val then a else b⟩
  instance : Max Row := ⟨fun a b => if a.val ≥ b.val then a else b⟩
  instance : HAdd Row Nat Row := ⟨fun r n => ⟨r.val + n⟩⟩
  instance : HAdd Row Nat Nat := ⟨fun r n => r.val + n⟩
  instance : HSub Row Row Nat := ⟨fun a b => a.val - b.val⟩
  instance : HSub Row Nat Row := ⟨fun r n => ⟨r.val - n⟩⟩
  instance : HSub Row Nat Nat := ⟨fun r n => r.val - n⟩
  instance : ToString Row := ⟨fun r => toString r.val⟩
end Row

-- Col helper functions
namespace Col
  def zero : Col := ⟨0⟩
  def succ (c : Col) : Col := ⟨c.val + 1⟩
  def pred (c : Col) : Col := ⟨c.val.pred⟩
  @[simp] def add (c : Col) (n : Nat) : Col := ⟨c.val + n⟩
  @[simp] def sub (c : Col) (n : Nat) : Col := ⟨c.val - n⟩
  instance : OfNat Col n := ⟨⟨n⟩⟩
  instance : LT Col := ⟨fun a b => a.val < b.val⟩
  instance : LE Col := ⟨fun a b => a.val ≤ b.val⟩
  instance (a b : Col) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
  instance (a b : Col) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
  instance : Min Col := ⟨fun a b => if a.val ≤ b.val then a else b⟩
  instance : Max Col := ⟨fun a b => if a.val ≥ b.val then a else b⟩
  instance : HAdd Col Nat Col := ⟨fun c n => ⟨c.val + n⟩⟩
  instance : HAdd Col Nat Nat := ⟨fun c n => c.val + n⟩
  instance : HSub Col Nat Col := ⟨fun c n => ⟨c.val - n⟩⟩
  instance : HSub Col Col Nat := ⟨fun a b => a.val - b.val⟩
  instance : ToString Col := ⟨fun c => toString c.val⟩
end Col

-- Point helper functions
namespace Point
  def zero : Point := ⟨Row.zero, Col.zero⟩
  def make (row col : Nat) : Point := ⟨⟨row⟩, ⟨col⟩⟩
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

structure FileBuffer where
  id : Nat
  filename : Option String
  dirty : Bool
  table : PieceTable
  missingEol : Bool
  deriving Inhabited

-- Manual Repr instance
instance : Repr FileBuffer where
  reprPrec buf _ :=
    s!"FileBuffer(id={buf.id}, file={buf.filename}, dirty={buf.dirty}, lines={PieceTree.lineBreaks buf.table.tree + 1})"

def initialFileBuffer : FileBuffer := {
  id := 0
  filename := none
  dirty := false
  table := PieceTable.fromString ""
  missingEol := false
}

namespace FileBuffer
  def lineCount (buf : FileBuffer) : Nat :=
    PieceTree.lineBreaks buf.table.tree + 1
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
structure ExplorerState where
  currentPath : String
  entries : List FileEntry
  selectedIndex : Nat
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
  deriving Repr, Inhabited


/-- State for a single workgroup (independent buffer set and layout) -/
structure WorkgroupState where
  buffers : List FileBuffer
  nextBufferId : Nat
  layout : Layout
  activeWindowId : Nat
  nextWindowId : Nat
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
  workspace : Workspace
  clipboard : Option TextBuffer -- Yank buffer
  selectionStart : Option Point -- Visual mode anchor
  explorers : List (Nat × ExplorerState) -- BufferId × Explorer state
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
