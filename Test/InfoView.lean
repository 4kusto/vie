import ViE
import Test.Utils

namespace Test.InfoView
open Test.Utils

def makeTestConfig : ViE.Config := {
  settings := ViE.defaultConfig
  commands := ViE.Command.defaultCommandMap
  bindings := ViE.Key.makeKeyMap ViE.Command.defaultCommandMap
}

def test : IO Unit := do
  IO.println "Starting InfoView Test..."

  let s0 : ViE.EditorState :=
    ({ ViE.initialState with message := "", floatingOverlay := none, mode := .normal, infoViewRequested := false }).updateActiveBuffer fun b =>
      { b with filename := some "Main.lean" }
  let s0' ← ViE.Lsp.Lean.syncInfoViewWindow s0
  let ws0 := s0'.getCurrentWorkspace
  assertEqual "InfoView hidden when not requested" 1 (ViE.Window.getWindowIds ws0.layout |>.length)

  let sNonLean := ({ s0 with infoViewRequested := true }).updateActiveBuffer fun b =>
    { b with filename := some "note.md" }
  let sNonLean' ← ViE.Lsp.Lean.syncInfoViewWindow sNonLean
  let wsNonLean := sNonLean'.getCurrentWorkspace
  assertEqual "InfoView hidden for non-Lean buffer" 1 (ViE.Window.getWindowIds wsNonLean.layout |>.length)

  let sLean := ({ s0 with infoViewRequested := true }).updateActiveBuffer fun b =>
    { b with table := ViE.PieceTable.fromString "abc\n" }
  let sLean' ← ViE.Lsp.Lean.syncInfoViewWindow sLean
  let wsLean := sLean'.getCurrentWorkspace
  assertEqual "InfoView split creates second window" 2 (ViE.Window.getWindowIds wsLean.layout |>.length)
  let infoBufOpt := wsLean.buffers.find? (fun b => b.filename == some ViE.Lsp.Lean.infoViewVirtualPath)
  assertEqual "InfoView buffer exists" true infoBufOpt.isSome
  match infoBufOpt with
  | none =>
      assertEqual "InfoView content check skipped unexpectedly" true false
  | some infoBuf =>
      let line0 := ViE.getLineFromBuffer infoBuf 0 |>.getD ""
      let line1 := ViE.getLineFromBuffer infoBuf 1 |>.getD ""
      assert "InfoView includes file line" (line0.startsWith "File: Main.lean")
      assertEqual "InfoView position line" "Position: 1:1  Byte: 0" line1

  let cfg := makeTestConfig
  let sMoved ← ViE.update cfg sLean' (ViE.Key.char 'l')
  let wsMoved := sMoved.getCurrentWorkspace
  let movedInfoBufOpt := wsMoved.buffers.find? (fun b => b.filename == some ViE.Lsp.Lean.infoViewVirtualPath)
  assertEqual "InfoView buffer exists after cursor move" true movedInfoBufOpt.isSome
  match movedInfoBufOpt with
  | none =>
      assertEqual "InfoView cursor move check skipped unexpectedly" true false
  | some infoBuf =>
      let line1 := ViE.getLineFromBuffer infoBuf 1 |>.getD ""
      assertEqual "InfoView position updates on cursor move" "Position: 1:2  Byte: 1" line1

  let sOff := { sLean' with infoViewRequested := false }
  let sOff' ← ViE.Lsp.Lean.syncInfoViewWindow sOff
  let wsOff := sOff'.getCurrentWorkspace
  assertEqual "InfoView off closes split window" 1 (ViE.Window.getWindowIds wsOff.layout |>.length)
  assertEqual "InfoView off removes buffer" true ((wsOff.buffers.find? (fun b => b.filename == some ViE.Lsp.Lean.infoViewVirtualPath)).isNone)

  let sInfoOnly := ViE.Window.closeActiveWindow sLean'
  let sInfoOnly' ← ViE.Lsp.Lean.syncInfoViewWindow sInfoOnly
  let wsInfoOnly := sInfoOnly'.getCurrentWorkspace
  assertEqual "InfoView-only fallback requests quit" true sInfoOnly'.shouldQuit
  assertEqual "InfoView-only fallback removes InfoView buffer" true ((wsInfoOnly.buffers.find? (fun b => b.filename == some ViE.Lsp.Lean.infoViewVirtualPath)).isNone)

  IO.println "InfoView Test passed!"

end Test.InfoView
