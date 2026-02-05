import ViE.State.Config
import ViE.State.Layout
import ViE.Command.Explorer
import ViE.State.Config
import ViE.Command.Impl
import Test.Utils

namespace Test.WorkgroupExplorer

open Test.Utils
open ViE

def addWorkspace (state : EditorState) (ws : WorkspaceState) : EditorState :=
  state.updateCurrentWorkgroup fun wg =>
    { wg with workspaces := wg.workspaces.push ws }

def addWorkgroup (state : EditorState) (name : String) : EditorState :=
  let nextBufId := state.workgroups.foldl (fun m g =>
    g.workspaces.foldl (fun m2 ws => max m2 ws.nextBufferId) m) 0
  let newWg := createEmptyWorkgroup name nextBufId
  { state with workgroups := state.workgroups.push newWg }

def setCursorRow (state : EditorState) (row : Nat) : EditorState :=
  state.updateActiveView fun v => { v with cursor := { v.cursor with row := ⟨row⟩ } }

def test : IO Unit := do
  IO.println "Starting Workgroup Explorer Test..."

  let s0 := ViE.initialState
  let ws1 := makeWorkspaceState "Project A" (some "/tmp/project-a") 10
  let ws2 := makeWorkspaceState "Project B" (some "/tmp/project-b") 20
  let s1 := addWorkspace (addWorkspace s0 ws1) ws2
  let s1 := addWorkgroup s1 "Group B"
  let s1 := addWorkgroup s1 "Group C"

  let s2 ← ViE.Command.cmdWg ["list"] s1
  assertEqual "Explorer buffer is active" (some "explorer://workgroups") s2.getActiveBuffer.filename

  let bufText := s2.getActiveBuffer.table.toString
  assertEqual "Explorer contains Workgroup header" true (bufText.contains "Workgroup Explorer")
  assertEqual "Explorer contains New Workgroup entry" true (bufText.contains "[New Workgroup]")
  assertEqual "Explorer contains Rename Workgroup entry" true (bufText.contains "[Rename Workgroup]")
  assertEqual "Explorer contains Group 0" true (bufText.contains "0")
  assertEqual "Explorer contains Group B" true (bufText.contains "Group B")
  assertEqual "Explorer marks current workgroup" true (bufText.contains "*")

  let explorerOpt := s2.explorers.find? (fun (id, _) => id == s2.getActiveBuffer.id)
  match explorerOpt with
  | none => throw (IO.userError "Workgroup explorer not registered")
  | some (_, explorer) =>
    assertEqual "Workgroup explorer preview window exists" true explorer.previewWindowId.isSome
    let previewWinId := explorer.previewWindowId.get!
    let wsPrev := s2.getCurrentWorkspace
    let previewView := wsPrev.layout.findView previewWinId |>.getD initialView
    let previewBuf := wsPrev.buffers.find? (fun b => b.id == previewView.bufferId) |>.getD initialBuffer
    let previewText := previewBuf.table.toString
    assertEqual "Workgroup preview includes Project A" true (previewText.contains "Project A")
    assertEqual "Workgroup preview includes Project B" true (previewText.contains "Project B")

  let s3 := setCursorRow s2 2
  let s4 ← ViE.Feature.handleExplorerEnter s3
  assertEqual "New workgroup enters command mode" Mode.command s4.mode
  assertEqual "New workgroup command prompt" "wg new " s4.inputState.commandBuffer

  let s3b := setCursorRow s2 3
  let s4b ← ViE.Feature.handleExplorerEnter s3b
  assertEqual "Rename workgroup enters command mode" Mode.command s4b.mode
  assertEqual "Rename workgroup command prompt" true (s4b.inputState.commandBuffer.startsWith "wg rename ")

  let s4c ← ViE.Command.cmdWg ["rename", ""] s2
  assertEqual "Rename workgroup rejects empty" "Workgroup name cannot be empty" s4c.message

  let s4d ← ViE.Command.cmdWg ["rename", "Group B"] s2
  assertEqual "Rename workgroup rejects duplicate" true (s4d.message.contains "already exists")

  let s5 ← ViE.Command.cmdWg ["list"] s1
  let s6 := setCursorRow s5 5
  let s7 ← ViE.Feature.handleExplorerEnter s6
  assertEqual "Switched to workgroup index 1" 1 s7.currentGroup
  assertEqual "Switch restores workgroup layout" true (s7.getActiveBuffer.filename != some "explorer://workgroup")

  IO.println "WorkgroupExplorerTest passed!"

end Test.WorkgroupExplorer
