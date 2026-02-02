import ViE.Types

open ViE

namespace Test.Layout

def assert (msg : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    throw (IO.userError s!"Assertion failed: {msg}")

def test : IO Unit := do
  IO.println "Starting Layout Test..."

  -- 1. Construct Layouts
  let view1 : ViewState := { bufferId := 1, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
  let win1 := Layout.window 1 view1

  let view2 : ViewState := { bufferId := 2, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
  let win2 := Layout.window 2 view2

  -- 2. Test Split Construction
  let hsplit := Layout.hsplit win1 win2 0.5

  match hsplit with
  | .hsplit l r ratio =>
      assert "HSplit match" true
      assert "HSplit ratio" (ratio == 0.5)
  | _ => assert "HSplit construction failed" false

  let vsplit := Layout.vsplit hsplit win1 0.3
  match vsplit with
  | .vsplit t b ratio =>
      assert "VSplit match" true
      assert "VSplit ratio" (ratio == 0.3)
      match t with
      | .hsplit _ _ _ => assert "VSplit top is HSplit" true
      | _ => assert "VSplit top incorrect" false
  | _ => assert "VSplit construction failed" false

  IO.println "LayoutTest passed!"

end Test.Layout
