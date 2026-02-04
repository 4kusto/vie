import ViE.State.Config
import ViE.State.Layout
import ViE.Workspace
import ViE.Command.Impl
import ViE.App
import ViE.Buffer.Content
import ViE.Basic
import Test.Utils

namespace Test.Workspace

open Test.Utils
open ViE

def addWorkspace (state : EditorState) (ws : WorkspaceState) : EditorState :=
  state.updateCurrentWorkgroup fun wg =>
    { wg with workspaces := wg.workspaces.push ws }

def switchWorkspace (state : EditorState) (idx : Nat) : EditorState :=
  state.updateCurrentWorkgroup fun wg =>
    if idx < wg.workspaces.size then
      { wg with currentWorkspace := idx }
    else
      wg

def test : IO Unit := do
  IO.println "Starting Workspace Test..."

  let s0 := ViE.initialState
  let wg0 := s0.getCurrentWorkgroup
  assertEqual "Initial workgroups size" 10 s0.workgroups.size
  assertEqual "Initial workgroup count" 1 wg0.workspaces.size
  assertEqual "Initial workspace index" 0 wg0.currentWorkspace
  assertEqual "Initial workspace name" "ViE" s0.getCurrentWorkspace.name

  let ws1 := makeWorkspaceState "Project A" (some "/tmp/project-a") 10
  let s1 := addWorkspace s0 ws1
  let wg1 := s1.getCurrentWorkgroup
  assertEqual "Workgroup has 2 workspaces" 2 wg1.workspaces.size

  let s2 := switchWorkspace s1 1
  assertEqual "Switched to workspace 1" "Project A" s2.getCurrentWorkspace.name
  assertEqual "Active buffer comes from workspace 1" 10 (s2.getActiveBuffer.id)

  let resolved := s2.getCurrentWorkspace.resolvePath "file.txt"
  assertEqual "ResolvePath uses workspace root" "/tmp/project-a/file.txt" resolved

  let resolvedAbs := s2.getCurrentWorkspace.resolvePath "/abs/file.txt"
  assertEqual "ResolvePath keeps absolute path" "/abs/file.txt" resolvedAbs

  IO.println "Starting Workspace Command Test..."
  let s3 ← ViE.Command.cmdWs ["new", "Project B", "/tmp/project-b"] s2
  assertEqual "Workspace created and switched" "Project B" s3.getCurrentWorkspace.name
  assertEqual "Workspace rootPath set" (some "/tmp/project-b") s3.getCurrentWorkspace.rootPath
  assertEqual "Active buffer id is new workspace buffer" 11 s3.getActiveBuffer.id

  let s4 ← ViE.Command.cmdWs ["rename", "Project B2"] s3
  assertEqual "Workspace rename applied" "Project B2" s4.getCurrentWorkspace.name

  let s5 ← ViE.Command.cmdWs ["new", "Project C"] s4
  assertEqual "Workspace C created" "Project C" s5.getCurrentWorkspace.name

  let s6 ← ViE.Command.cmdWs ["prev"] s5
  assertEqual "Workspace prev switches back" "Project B2" s6.getCurrentWorkspace.name

  let s7 ← ViE.Command.cmdWs ["0"] s6
  assertEqual "Workspace switch by index" "ViE" s7.getCurrentWorkspace.name

  let s8 ← ViE.Command.cmdWs ["list"] s7
  assertEqual "Workspace list opens explorer buffer" (some "explorer://workgroup") s8.getActiveBuffer.filename
  let wsListText := s8.getActiveBuffer.table.toString
  assertEqual "Workspace list contains New Workspace entry" true (wsListText.contains "[New Workspace]")
  assertEqual "Workspace list contains Rename Workspace entry" true (wsListText.contains "[Rename Workspace]")
  assertEqual "Workspace list contains Project B2" true (wsListText.contains "Project B2")
  assertEqual "Workspace list marks current workspace" true (wsListText.contains "*")

  let s8a := s8.updateActiveView fun v => { v with cursor := {row := ⟨2⟩, col := 0} }
  let s8b ← ViE.Feature.handleExplorerEnter s8a
  assertEqual "New workspace enters command mode" Mode.command s8b.mode
  assertEqual "New workspace command prompt" "ws new " s8b.inputState.commandBuffer

  let s8c := s8.updateActiveView fun v => { v with cursor := {row := ⟨3⟩, col := 0} }
  let s8d ← ViE.Feature.handleExplorerEnter s8c
  assertEqual "Rename workspace enters command mode" Mode.command s8d.mode
  assertEqual "Rename workspace command prompt" true (s8d.inputState.commandBuffer.startsWith "ws rename ")

  let s8e ← ViE.Command.cmdWorkspace ["rename", ""] s8
  assertEqual "Rename workspace rejects empty" "Workspace name cannot be empty" s8e.message

  let s8f ← ViE.Command.cmdWorkspace ["rename", "Project B2"] s8
  assertEqual "Rename workspace rejects duplicate" true (s8f.message.contains "already exists")

  let s9 ← ViE.Command.cmdWs ["open", "/tmp/project-d"] s8
  assertEqual "Workspace open uses path name" "project-d" s9.getCurrentWorkspace.name
  assertEqual "Workspace open rootPath set" (some "/tmp/project-d") s9.getCurrentWorkspace.rootPath

  let s10 ← ViE.Command.cmdWs ["open", "--name", "Project E", "/tmp/project-e"] s9
  assertEqual "Workspace open --name prefix" "Project E" s10.getCurrentWorkspace.name
  assertEqual "Workspace open --name prefix rootPath" (some "/tmp/project-e") s10.getCurrentWorkspace.rootPath

  let s11 ← ViE.Command.cmdWs ["open", "/tmp/project-f", "--name", "Project F"] s10
  assertEqual "Workspace open --name suffix" "Project F" s11.getCurrentWorkspace.name
  assertEqual "Workspace open --name suffix rootPath" (some "/tmp/project-f") s11.getCurrentWorkspace.rootPath

  let s12 ← ViE.Command.cmdWs ["close"] s11
  assertEqual "Workspace close switches to previous" "Project E" s12.getCurrentWorkspace.name

  IO.println "Starting Workspace Restore Test..."
  let bufA : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 0 none #[stringToLine "WS-A"]
  let bufB : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 10 none #[stringToLine "WS-B"]
  let wsA : WorkspaceState := {
    name := "WS-A"
    rootPath := none
    buffers := [bufA]
    nextBufferId := 1
    layout := .window 0 { initialView with bufferId := 0 }
    activeWindowId := 0
    nextWindowId := 1
  }
  let wsB : WorkspaceState := {
    name := "WS-B"
    rootPath := none
    buffers := [bufB]
    nextBufferId := 11
    layout := .window 0 { initialView with bufferId := 10 }
    activeWindowId := 0
    nextWindowId := 1
  }
  let s12a := s12.updateCurrentWorkgroup fun wg =>
    { wg with workspaces := #[wsA, wsB], currentWorkspace := 0 }
  let s12b ← ViE.Feature.openWorkspaceExplorer s12a
  let s12c := s12b.updateActiveView fun v => { v with cursor := {row := ⟨5⟩, col := 0} }
  let s12d ← ViE.Feature.handleExplorerEnter s12c
  assertEqual "Workspace selection switches current workspace" "WS-B" s12d.getCurrentWorkspace.name
  assertEqual "Workspace selection restores active buffer" "WS-B" s12d.getActiveBuffer.table.toString

  IO.println "Starting Workspace Restore Layout Test..."
  let bufC : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 20 none #[stringToLine "WS-C1"]
  let bufD : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 21 none #[stringToLine "WS-C2"]
  let layoutC : Layout :=
    .hsplit
      (.window 0 { initialView with bufferId := 20 })
      (.window 1 { initialView with bufferId := 21, cursor := ⟨⟨0⟩, ⟨2⟩⟩ })
      0.3
  let wsC : WorkspaceState := {
    name := "WS-C"
    rootPath := none
    buffers := [bufC, bufD]
    nextBufferId := 22
    layout := layoutC
    activeWindowId := 1
    nextWindowId := 2
  }
  let s12e := s12.updateCurrentWorkgroup fun wg =>
    { wg with workspaces := #[wsA, wsC], currentWorkspace := 0 }
  let s12f ← ViE.Feature.openWorkspaceExplorer s12e
  let s12g := s12f.updateActiveView fun v => { v with cursor := {row := ⟨5⟩, col := 0} }
  let s12h ← ViE.Feature.handleExplorerEnter s12g
  assertEqual "Workspace layout restore (active buffer)" "WS-C2" s12h.getActiveBuffer.table.toString
  let ratio := match s12h.getCurrentWorkspace.layout with
    | .hsplit _ _ r => r
    | _ => 0.0
  assertEqual "Workspace layout restore (ratio)" 0.3 ratio
  let cursor := s12h.getCursor
  assertEqual "Workspace layout restore (cursor row)" 0 cursor.row.val
  assertEqual "Workspace layout restore (cursor col)" 2 cursor.col.val

  IO.println "Starting Workspace Restore VSplit Test..."
  let bufE : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 30 none #[stringToLine "WS-D1"]
  let bufF : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 31 none #[stringToLine "WS-D2"]
  let layoutD : Layout :=
    .vsplit
      (.window 0 { initialView with bufferId := 30, cursor := ⟨⟨1⟩, ⟨0⟩⟩, scrollRow := ⟨1⟩, scrollCol := ⟨2⟩ })
      (.window 1 { initialView with bufferId := 31, cursor := ⟨⟨2⟩, ⟨3⟩⟩, scrollRow := ⟨0⟩, scrollCol := ⟨1⟩ })
      0.7
  let wsD : WorkspaceState := {
    name := "WS-D"
    rootPath := none
    buffers := [bufE, bufF]
    nextBufferId := 32
    layout := layoutD
    activeWindowId := 1
    nextWindowId := 2
  }
  let s12i := s12.updateCurrentWorkgroup fun wg =>
    { wg with workspaces := #[wsA, wsC, wsD], currentWorkspace := 0 }
  let s12j ← ViE.Feature.openWorkspaceExplorer s12i
  let s12k := s12j.updateActiveView fun v => { v with cursor := {row := ⟨6⟩, col := 0} }
  let s12l ← ViE.Feature.handleExplorerEnter s12k
  assertEqual "Workspace vsplit restore (active buffer)" "WS-D2" s12l.getActiveBuffer.table.toString
  let ratio2 := match s12l.getCurrentWorkspace.layout with
    | .vsplit _ _ r => r
    | _ => 0.0
  assertEqual "Workspace vsplit restore (ratio)" 0.7 ratio2
  let cursor2 := s12l.getCursor
  assertEqual "Workspace vsplit restore (cursor row)" 2 cursor2.row.val
  assertEqual "Workspace vsplit restore (cursor col)" 3 cursor2.col.val
  let (sRow, sCol) := s12l.getScroll
  assertEqual "Workspace vsplit restore (scroll row)" 0 sRow.val
  assertEqual "Workspace vsplit restore (scroll col)" 1 sCol.val

  IO.println "Starting Workspace Multi-View Restore Test..."
  let bufG : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 40 none #[stringToLine "WS-E1"]
  let bufH : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 41 none #[stringToLine "WS-E2"]
  let bufI : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer 42 none #[stringToLine "WS-E3"]
  let layoutE : Layout :=
    .hsplit
      (.vsplit
        (.window 0 { initialView with bufferId := 40, cursor := ⟨⟨0⟩, ⟨1⟩⟩, scrollRow := ⟨0⟩, scrollCol := ⟨0⟩ })
        (.window 1 { initialView with bufferId := 41, cursor := ⟨⟨2⟩, ⟨2⟩⟩, scrollRow := ⟨1⟩, scrollCol := ⟨1⟩ })
        0.4)
      (.window 2 { initialView with bufferId := 42, cursor := ⟨⟨3⟩, ⟨0⟩⟩, scrollRow := ⟨2⟩, scrollCol := ⟨2⟩ })
      0.6
  let wsE : WorkspaceState := {
    name := "WS-E"
    rootPath := none
    buffers := [bufG, bufH, bufI]
    nextBufferId := 43
    layout := layoutE
    activeWindowId := 1
    nextWindowId := 3
  }
  let s12m := s12.updateCurrentWorkgroup fun wg =>
    { wg with workspaces := #[wsA, wsC, wsD, wsE], currentWorkspace := 0 }
  let s12n ← ViE.Feature.openWorkspaceExplorer s12m
  let s12o := s12n.updateActiveView fun v => { v with cursor := {row := ⟨7⟩, col := 0} }
  let s12p ← ViE.Feature.handleExplorerEnter s12o
  assertEqual "Multi-view restore (active buffer)" "WS-E2" s12p.getActiveBuffer.table.toString
  let (sr2, sc2) := s12p.getScroll
  assertEqual "Multi-view restore (scroll row)" 1 sr2.val
  assertEqual "Multi-view restore (scroll col)" 1 sc2.val
  let cursor3 := s12p.getCursor
  assertEqual "Multi-view restore (cursor row)" 2 cursor3.row.val
  assertEqual "Multi-view restore (cursor col)" 2 cursor3.col.val
  assertEqual "Multi-view restore (layout hsplit ratio)" 0.6 (match s12p.getCurrentWorkspace.layout with | .hsplit _ _ r => r | _ => 0.0)
  let subRatio := match s12p.getCurrentWorkspace.layout with
    | .hsplit left _ _ =>
        match left with
        | .vsplit _ _ r => r
        | _ => 0.0
    | _ => 0.0
  assertEqual "Multi-view restore (layout vsplit ratio)" 0.4 subRatio

  IO.println "Starting Workspace Startup Target Test..."
  let base := "Test/test_paths"

  let dirOnly := s!"{base}/dir0"
  let (wsDirOnly, fileDirOnly) ← ViE.resolveStartupTarget (some dirOnly)
  assertEqual "Directory arg sets workspace" (some dirOnly) wsDirOnly
  assertEqual "Directory arg has no file" none fileDirOnly

  let fileNested := s!"{base}/dir0/dir1/dir2/file0.txt"
  let (wsFileNested, fileFileNested) ← ViE.resolveStartupTarget (some fileNested)
  assertEqual "File arg sets workspace to parent dir" (some s!"{base}/dir0/dir1/dir2") wsFileNested
  assertEqual "File arg keeps filename" (some fileNested) fileFileNested

  let fileTop := s!"{base}/file0.txt"
  let (wsFileTop, fileFileTop) ← ViE.resolveStartupTarget (some fileTop)
  assertEqual "Top-level file sets workspace to base" (some base) wsFileTop
  assertEqual "Top-level file keeps filename" (some fileTop) fileFileTop

  IO.println "Starting Explorer Path Resolution Test..."
  let s13 := s12.updateCurrentWorkspace fun ws =>
    { ws with rootPath := some "Test", name := "Test" }
  let s14 ← ViE.Feature.openExplorer s13 "Test"
  assertEqual "Explorer opens workspace root without duplication" (some "explorer://Test") s14.getActiveBuffer.filename

  IO.println "WorkspaceTest passed!"

end Test.Workspace
