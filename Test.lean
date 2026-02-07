import Test.Undo
import Test.Buffer
import Test.Layout
import Test.Integration
import Test.Keybinds
import Test.Mode
import Test.CursorReproduction
import Test.PasteReproduction
import Test.Workspace
import Test.PreviewData
import Test.WorkgroupExplorer
import Test.ExplorerPreview
import Test.PieceTable.Basic
import Test.PieceTable.UndoRedo
import Test.PieceTable.Appended
import Test.PieceTable.Stress
import Test.PieceTable.Search
import Test.MissingEol
import Test.Scroll

def test : IO Unit := do
  IO.println "Running all tests..."
  Test.Undo.test
  Test.Buffer.test
  Test.Layout.test
  Test.Integration.test
  Test.Keybinds.test
  Test.Mode.test
  Test.CursorReproduction.test
  Test.PasteReproduction.test
  Test.Workspace.test
  Test.PreviewData.test
  Test.WorkgroupExplorer.test
  Test.ExplorerPreview.test
  Test.Scroll.test
  Test.PieceTable.Basic.test
  Test.PieceTable.UndoRedo.test
  Test.PieceTable.Appended.test
  Test.PieceTable.Stress.test
  Test.PieceTable.Search.test
  Test.MissingEol.test
  IO.println "All tests finished."

def main : IO Unit := do
  test
