import ViE.App
import ViE.Buffer.Manager
import ViE.Checkpoint
import ViE.State.Config
import Test.Utils

namespace Test.Checkpoint

open Test.Utils
open ViE

def testLoadSessionInvalid : IO Unit := do
  IO.println "Starting Checkpoint Parse Invalid Test..."
  IO.FS.writeFile ViE.Checkpoint.sessionFile "--ACTIVE--\nnot-a-number\n"
  let loaded <- ViE.Checkpoint.loadSession
  assertEqual "Invalid checkpoint parses as none" none loaded

def testLoadSessionValid : IO Unit := do
  IO.println "Starting Checkpoint Parse Valid Test..."
  let content :=
    "/tmp/file-a.txt\n" ++
    "0 0\n" ++
    "/tmp/file-b.txt\n" ++
    "3 4\n" ++
    "--ACTIVE--\n" ++
    "1\n"
  IO.FS.writeFile ViE.Checkpoint.sessionFile content
  let loaded <- ViE.Checkpoint.loadSession
  let expected : Option (List String × Nat × List (Nat × Nat)) :=
    some (["/tmp/file-a.txt", "/tmp/file-b.txt"], 1, [(0, 0), (3, 4)])
  assertEqual "Valid checkpoint parsing" expected loaded

def testBuildRestoredWorkspace : IO Unit := do
  IO.println "Starting Restored Workspace Build Test..."
  let stamp <- IO.monoMsNow
  let root := s!"/tmp/vie-checkpoint-{stamp}"
  IO.FS.createDirAll root

  let f1 := s!"{root}/a.txt"
  let f2 := s!"{root}/b.txt"
  IO.FS.writeFile f1 "alpha\nbeta\n"
  IO.FS.writeFile f2 "line0\nline1\nline2\n"

  let ws <- ViE.buildRestoredWorkspace ViE.defaultConfig (some root) [f1, f2] 1 [(0, 0), (1, 2)]

  assertEqual "Restored workspace buffer count" 2 ws.buffers.length
  assertEqual "Restored workspace nextBufferId" 2 ws.nextBufferId
  let active := ws.layout.findView ws.activeWindowId |>.getD ViE.initialView
  assertEqual "Restored active buffer id" 1 active.bufferId
  assertEqual "Restored cursor row" 1 active.cursor.row.val
  assertEqual "Restored cursor col" 2 active.cursor.col.val

  match ws.buffers with
  | b1 :: b2 :: _ =>
      assertEqual "Restored first file path" (some f1) b1.filename
      assertEqual "Restored second file path" (some f2) b2.filename
      assertEqual "Restored inactive buffer is lazy" false b1.loaded
      assertEqual "Restored active buffer is loaded" true b2.loaded
  | _ =>
      throw (IO.userError "Expected two restored buffers")

  let s0 := ({ ViE.initialState with config := ViE.defaultConfig }).updateCurrentWorkspace (fun _ => ws)
  let s1 := s0.updateCurrentWorkspace fun ws =>
    { ws with layout := ws.layout.updateView ws.activeWindowId (fun v => { v with bufferId := 0 }) }
  let s2 ← ViE.Buffer.ensureActiveBufferLoaded s1
  let activeLoaded := s2.getActiveBuffer
  assertEqual "Lazy buffer loads on activation" true activeLoaded.loaded
  assertEqual "Lazy loaded buffer keeps file path" (some f1) activeLoaded.filename

def testBuildRestoredWorkspaceCustomTabStop : IO Unit := do
  IO.println "Starting Restored Workspace Custom TabStop Test..."
  let stamp <- IO.monoMsNow
  let root := s!"/tmp/vie-checkpoint-tab-{stamp}"
  IO.FS.createDirAll root

  let f1 := s!"{root}/tab.txt"
  IO.FS.writeFile f1 "\talpha\n"
  let settings := { ViE.defaultConfig with tabStop := 8 }

  let ws <- ViE.buildRestoredWorkspace settings (some root) [f1] 0 [(0, 8)]
  let active := ws.layout.findView ws.activeWindowId |>.getD ViE.initialView
  assertEqual "Restored custom tabStop cursor row" 0 active.cursor.row.val
  assertEqual "Restored custom tabStop cursor col" 8 active.cursor.col.val

def test : IO Unit := do
  testLoadSessionInvalid
  testLoadSessionValid
  testBuildRestoredWorkspace
  testBuildRestoredWorkspaceCustomTabStop

end Test.Checkpoint
