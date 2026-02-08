import ViE.State
import ViE.Unicode

namespace ViE.UI
open ViE

/-- Pad a string on the left with spaces until it reaches the given width. -/
def leftPad (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else "".pushn ' ' (width - s.length) ++ s

/-- Take characters from substring until visual width limit is reached. -/
def takeVisual (s : Substring.Raw) (width : Nat) : String :=
  Unicode.takeByDisplayWidth s width

def rightPadVisual (s : String) (width : Nat) : String :=
  let w := Unicode.stringWidth s
  if w >= width then
    s
  else
    s ++ "".pushn ' ' (width - w)

structure Rect where
  row : Nat
  col : Nat
  height : Nat
  width : Nat
  deriving Inhabited

def getWorkspaceBuffer (st : EditorState) (id : Nat) : FileBuffer :=
  let ws := st.getCurrentWorkspace
  ws.buffers.find? (fun b => b.id == id) |>.getD initialFileBuffer

end ViE.UI
