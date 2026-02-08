import ViE.State.Config
import ViE.Command.Explorer
import ViE.Window.Analysis
import ViE.Window.Actions
import Test.Utils

namespace Test.ExplorerPreview

open Test.Utils
open ViE

def findEntryIndex (entries : List FileEntry) (name : String) : Option Nat :=
  let rec loop (list : List FileEntry) (idx : Nat) : Option Nat :=
    match list with
    | [] => none
    | e :: rest =>
      if e.name == name then
        some idx
      else
        loop rest (idx + 1)
  loop entries 0

def test : IO Unit := do
  IO.println "Starting Explorer Preview Test..."

  let s0 := { ViE.initialState with windowHeight := 40, windowWidth := 120 }
  let path := "Test/test_paths/dir0/dir1"
  let s1 ← ViE.Feature.openExplorer s0 path
  let buf := s1.getActiveBuffer
  let ws1 := s1.getCurrentWorkspace
  assert "File explorer opens in floating window" (ws1.isFloatingWindow ws1.activeWindowId)
  let baseBufId := s0.getActiveBuffer.id
  let baseWinId :=
    (ViE.Window.getWindowIds ws1.layout).find? (fun wid =>
      if wid == ws1.activeWindowId then
        false
      else
        match ws1.layout.findView wid with
        | some v => v.bufferId == baseBufId
        | none => false)
  let baseWindowStillExists :=
    (ViE.Window.getWindowIds ws1.layout).any (fun wid =>
      if wid == ws1.activeWindowId then
        false
      else
        match ws1.layout.findView wid with
        | some v => v.bufferId == baseBufId
        | none => false)
  assert "Opening explorer keeps original buffer window intact" baseWindowStillExists
  let explorerOpt := s1.explorers.find? (fun (id, _) => id == buf.id)
  match explorerOpt with
  | none =>
    throw (IO.userError "Explorer buffer not registered")
  | some (_, explorer) =>
    let idx1 := findEntryIndex explorer.entries "file1.txt"
    let idx2 := findEntryIndex explorer.entries "file2.txt"
    assert "file1.txt exists in explorer entries" idx1.isSome
    assert "file2.txt exists in explorer entries" idx2.isSome
    let row1 : Row := ⟨2 + idx1.get!⟩
    let row2 : Row := ⟨2 + idx2.get!⟩

    let exAfterOpen := s1.explorers.find? (fun (id, _) => id == buf.id) |>.map (fun (_, ex) => ex)
    match exAfterOpen with
    | none => throw (IO.userError "Explorer buffer not registered after open")
    | some exOpen =>
      assert "Preview window created on open" exOpen.previewWindowId.isSome
      let previewFloating :=
        match exOpen.previewWindowId with
        | some wid => s1.getCurrentWorkspace.isFloatingWindow wid
        | none => false
      assert "Preview window opens in floating window" previewFloating
      let pairSideBySide :=
        match exOpen.previewWindowId with
        | some wid =>
          let ws1 := s1.getCurrentWorkspace
          match s1.getFloatingWindowBounds ws1.activeWindowId, s1.getFloatingWindowBounds wid with
          | some (et, el, eh, ew), some (pt, pl, ph, pw) =>
            et == pt && eh == ph && ((el + ew <= pl) || (pl + pw <= el))
          | _, _ => false
        | none => false
      assert "Explorer/preview floating pair is side-by-side" pairSideBySide

    let s2 := s1.updateActiveView fun v => { v with cursor := { row := row1, col := 0 } }
    let s3 ← ViE.Feature.refreshExplorerPreview s2

    let exAfterOpt := s3.explorers.find? (fun (id, _) => id == buf.id)
    match exAfterOpt with
    | none =>
      throw (IO.userError "Explorer buffer not registered after preview")
    | some (_, exAfter) =>
      assert "Preview window created" exAfter.previewWindowId.isSome
      assert "Preview buffer created" exAfter.previewBufferId.isSome
      let ws := s3.getCurrentWorkspace
      let previewWinId := exAfter.previewWindowId.get!
      let previewView := ws.layout.findView previewWinId |>.getD initialView
      let previewBuf := ws.buffers.find? (fun b => b.id == previewView.bufferId) |>.getD initialBuffer
      assert "Preview filename has prefix" ((previewBuf.filename.getD "").startsWith "preview://")
      assert "Preview filename contains file1.txt" ((previewBuf.filename.getD "").contains "file1.txt")

      let dirIdx := findEntryIndex exAfter.entries "dir0"
      assert "dir0 exists in explorer entries" dirIdx.isSome
      let dirRow : Row := ⟨2 + dirIdx.get!⟩
      let s3a := s3.updateActiveView fun v => { v with cursor := { row := dirRow, col := 0 } }
      let s3b ← ViE.Feature.handleExplorerEnter s3a
      let idsAfterDir := ViE.Window.getWindowIds s3b.getCurrentWorkspace.layout
      assert "Preview window kept on directory navigation" (idsAfterDir.contains previewWinId)

      let newExplorerOpt := s3b.explorers.find? (fun (id, _) => id == s3b.getActiveBuffer.id)
      match newExplorerOpt with
      | none => throw (IO.userError "Explorer buffer not registered after directory nav")
      | some (_, exAfterDir) =>
        assert "Preview window id preserved on directory nav" (exAfterDir.previewWindowId == exAfter.previewWindowId)

      let s4 := s3.updateActiveView fun v => { v with cursor := { row := row2, col := 0 } }
      let s5 ← ViE.Feature.refreshExplorerPreview s4
      let ws5 := s5.getCurrentWorkspace
      let previewView2 := ws5.layout.findView previewWinId |>.getD initialView
      let previewBuf2 := ws5.buffers.find? (fun b => b.id == previewView2.bufferId) |>.getD initialBuffer
      assert "Preview filename updates to file2.txt" ((previewBuf2.filename.getD "").contains "file2.txt")

      let s5a := s5.updateActiveView fun v => { v with cursor := { row := row2, col := 0 } }
      let explorerWinId := s5a.getCurrentWorkspace.activeWindowId
      let s5b ← ViE.Feature.handleExplorerEnter s5a
      let ws5b := s5b.getCurrentWorkspace
      assert "Opening file from floating explorer leaves non-floating window" (!ws5b.isFloatingWindow ws5b.activeWindowId)
      match baseWinId with
      | some wid =>
          assert "Opening file from explorer uses original buffer window" (ws5b.activeWindowId == wid)
      | none =>
          throw (IO.userError "Base window id not found after explorer open")
      let idsAfterOpen := ViE.Window.getWindowIds s5b.getCurrentWorkspace.layout
      assert "Explorer window removed on file open" (!idsAfterOpen.contains explorerWinId)
      assert "Preview window removed on file open" (!idsAfterOpen.contains previewWinId)
      let bufIdsAfterOpen := s5b.getCurrentWorkspace.buffers.map (fun b => b.id)
      let previewBufId := exAfter.previewBufferId.getD 0
      assert "Preview buffer removed on file open" (!bufIdsAfterOpen.contains previewBufId)

      let sClose := ViE.Window.closeActiveWindow s5
      let idsAfter := ViE.Window.getWindowIds sClose.getCurrentWorkspace.layout
      assert "Preview window removed on explorer close" (!idsAfter.contains previewWinId)
      let bufIdsAfterClose := sClose.getCurrentWorkspace.buffers.map (fun b => b.id)
      assert "Preview buffer removed on explorer close" (!bufIdsAfterClose.contains previewBufId)

      let s6 ← ViE.Feature.toggleExplorerPreview s5
      let exAfterClose := s6.explorers.find? (fun (id, _) => id == buf.id) |>.map (fun (_, ex) => ex)
      match exAfterClose with
      | none => throw (IO.userError "Explorer buffer missing after close")
      | some exClose =>
        assert "Preview window cleared" exClose.previewWindowId.isNone

  IO.println "Explorer Preview Test passed!"

end Test.ExplorerPreview
