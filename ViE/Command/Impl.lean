import ViE.State
import ViE.Types
import ViE.Window.Actions
import ViE.Buffer.Manager
import ViE.Command.Explorer
import ViE.Loader
import ViE.Checkpoint
import ViE.Command.Parser
import ViE.Workspace

namespace ViE.Command

open ViE.Window
open ViE.Buffer
open ViE.Feature

def cmdEdit (args : List String) (state : EditorState) : IO EditorState := do
  match args with
  | [fname] =>
    -- Resolve path relative to workspace
    let resolvedPath := state.getCurrentWorkspace.resolvePath fname
    ViE.Buffer.openBuffer state resolvedPath
  | [] => return { state with message := "No file name" }
  | _ => return { state with message := "Too many arguments" }

def cmdWrite (args : List String) (state : EditorState) : IO EditorState :=
  match ViE.Command.parseFilenameArg args state.getActiveBuffer.filename with
  | .ok fname =>
    ViE.saveBuffer state fname
  | .error msg =>
    return { state with message := msg }

def cmdQuit (_ : List String) (state : EditorState) : IO EditorState :=
  return (ViE.Window.closeActiveWindow state)

def cmdQuitForce (_ : List String) (state : EditorState) : IO EditorState :=
  return { state with shouldQuit := true }

def cmdWriteQuit (args : List String) (state : EditorState) : IO EditorState := do
  match ViE.Command.parseFilenameArg args state.getActiveBuffer.filename with
  | .ok fname =>
    let state' ← ViE.saveBuffer state fname
    return (ViE.Window.closeActiveWindow state')
  | .error msg =>
    return { state with message := msg }

def cmdSplit (_ : List String) (state : EditorState) : IO EditorState :=
  return ViE.Window.splitWindow state true

def cmdVSplit (_ : List String) (state : EditorState) : IO EditorState :=
  return ViE.Window.splitWindow state false

def cmdSet (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | ["number"] => return { state with config := { state.config with showLineNumbers := true }, message := "number set" }
  | ["nonumber"] => return { state with config := { state.config with showLineNumbers := false }, message := "number unset" }
  | _ => return { state with message := s!"Unknown setting or args: {args}" }

def cmdWincmd (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | ["w"] => return ViE.Window.cycleWindow state
  | ["h"] => return ViE.Window.switchWindow state .left
  | ["j"] => return ViE.Window.switchWindow state .down
  | ["k"] => return ViE.Window.switchWindow state .up
  | ["l"] => return ViE.Window.switchWindow state .right
  | ["s"] => return ViE.Window.splitWindow state true
  | ["v"] => return ViE.Window.splitWindow state false
  | ["q"] => return (ViE.Window.closeActiveWindow state)
  | _ => return { state with message := s!"Unknown wincmd: {args}" }

def cmdUndo (_ : List String) (state : EditorState) : IO EditorState :=
  return ViE.EditorState.undo state

def cmdRedo (_ : List String) (state : EditorState) : IO EditorState :=
  return ViE.EditorState.redo state

def cmdWinLeft (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .left
def cmdWinDown (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .down
def cmdWinUp (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .up
def cmdWinRight (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .right
def cmdWinCycle (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.cycleWindow state

def cmdCd (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | [path] =>
    let ws := state.getCurrentWorkspace
    let absPath := if path.startsWith "/" then path
                   else match ws.rootPath with
                        | some root => root ++ "/" ++ path
                        | none => path
    let s' := state.updateCurrentWorkspace fun ws =>
      { ws with rootPath := some absPath, name := ws.name }
    return { s' with message := s!"Workspace path: {absPath}" }
  | [] =>
    let s' := state.updateCurrentWorkspace fun ws =>
      { ws with rootPath := none, name := ws.name }
    return { s' with message := "Workspace cleared" }
  | _ => return { state with message := "Usage: :cd [path]" }

def cmdWorkspace (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | ["open", path] => cmdCd [path] state
  | ["rename", name] =>
    let trimmed := name.trimAscii.toString
    if trimmed.isEmpty then
      return { state with message := "Workspace name cannot be empty" }
    else
      let wg := state.getCurrentWorkgroup
      let currentName := state.getCurrentWorkspace.name
      let duplicate := wg.workspaces.any (fun ws => ws.name == trimmed && ws.name != currentName)
      if duplicate then
        return { state with message := s!"Workspace name already exists: {trimmed}" }
      else
        let s' := state.updateCurrentWorkspace fun ws =>
          { ws with name := trimmed }
        return { s' with message := s!"Workspace renamed to: {trimmed}" }
  | _ => return { state with message := "Usage: :workspace <open|rename> <args>" }

def cmdPwd (_ : List String) (state : EditorState) : IO EditorState :=
  match state.getCurrentWorkspace.rootPath with
  | some path => return { state with message := path }
  | none => return { state with message := "No workspace set" }

def cmdWg (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | ["list"] =>
    ViE.Feature.openWorkgroupExplorer state
  | ["new"] =>
    let name := s!"Group {state.workgroups.size}"
    let nextBufId := state.workgroups.foldl (fun m g =>
      g.workspaces.foldl (fun m2 ws => max m2 ws.nextBufferId) m) 0
    let newWg := createEmptyWorkgroup name nextBufId
    let newState := { state with
      workgroups := state.workgroups.push newWg,
      currentGroup := state.workgroups.size -- switch to new one using the size before push
    }
    return { newState with message := s!"Created workgroup: {name}" }
  | ["new", name] =>
    let nextBufId := state.workgroups.foldl (fun m g =>
      g.workspaces.foldl (fun m2 ws => max m2 ws.nextBufferId) m) 0
    let newWg := createEmptyWorkgroup name nextBufId
    let newState := { state with
      workgroups := state.workgroups.push newWg,
      currentGroup := state.workgroups.size
    }
    return { newState with message := s!"Created workgroup: {name}" }
  | ["close"] =>
    if state.workgroups.size <= 1 then
      return { state with message := "Cannot close the last workgroup" }
    else
      if h_idx : state.currentGroup < state.workgroups.size then
        let newGroups := state.workgroups.eraseIdx state.currentGroup h_idx
        let newIdx := if state.currentGroup >= newGroups.size then newGroups.size - 1 else state.currentGroup
        return { state with
          workgroups := newGroups,
          currentGroup := newIdx,
          message := "Workgroup closed"
        }
      else
        return { state with message := "Error: invalid workgroup index" }
  | ["rename", name] =>
    let trimmed := name.trimAscii.toString
    if trimmed.isEmpty then
      return { state with message := "Workgroup name cannot be empty" }
    else
      let currentName := state.getCurrentWorkgroup.name
      let duplicate := state.workgroups.any (fun wg => wg.name == trimmed && wg.name != currentName)
      if duplicate then
        return { state with message := s!"Workgroup name already exists: {trimmed}" }
      else
        let current := state.workgroups[state.currentGroup]!
        let updated := { current with name := trimmed }
        return { state with
          workgroups := state.workgroups.set! state.currentGroup updated,
          message := s!"Workgroup renamed to: {trimmed}"
        }
  | ["next"] =>
    let nextIdx := (state.currentGroup + 1) % state.workgroups.size
    let wg := state.workgroups[nextIdx]!
    return { state with currentGroup := nextIdx, message := s!"Switched to: {wg.name}" }
  | ["prev"] =>
    let prevIdx := if state.currentGroup == 0 then state.workgroups.size - 1 else state.currentGroup - 1
    let wg := state.workgroups[prevIdx]!
    return { state with currentGroup := prevIdx, message := s!"Switched to: {wg.name}" }
  | [n] =>
    match n.toNat? with
    | some num =>
      if num < state.workgroups.size then
        let wg := state.workgroups[num]!
        return { state with currentGroup := num, message := s!"Switched to: {wg.name}" }
      else
        return { state with message := s!"Workgroup index out of range (0-{state.workgroups.size - 1})" }
    | none => return { state with message := "Invalid workgroup number" }
  | [] =>
    let wg := state.workgroups[state.currentGroup]!
    return { state with message := s!"Current workgroup: {wg.name} (index {state.currentGroup})" }
  | _ => return { state with message := "Usage: :wg <new|list|close|rename|next|prev|index> [args]" }

def cmdWs (args : List String) (state : EditorState) : IO EditorState :=
  let wg := state.getCurrentWorkgroup
  let maxBufId := wg.workspaces.foldl (fun m ws => max m ws.nextBufferId) 0

  let resolvePath (p : String) : String :=
    if p.startsWith "/" then p
    else
      match state.getCurrentWorkspace.rootPath with
      | some root => root ++ "/" ++ p
      | none => p

  let parseOpenArgs (rest : List String) : Option (Option String × String) :=
    match rest with
    | ["--name", name, path] => some (some name, path)
    | [path, "--name", name] => some (some name, path)
    | [path] => some (none, path)
    | [name, path] => some (some name, path)
    | _ => none

  match args with
  | ["list"] =>
    ViE.Feature.openWorkspaceExplorer state
  | "open" :: rest =>
    match parseOpenArgs rest with
    | some (maybeName, path) =>
      let absPath := resolvePath path
      let name := maybeName.getD ((System.FilePath.fileName absPath).getD "Workspace")
      let newWs := makeWorkspaceState name (some absPath) maxBufId
      let newState := state.updateCurrentWorkgroup fun wg =>
        { wg with
          workspaces := wg.workspaces.push newWs,
          currentWorkspace := wg.workspaces.size
        }
      return { newState with message := s!"Opened workspace: {name} ({absPath})" }
    | none =>
      return { state with message := "Usage: :ws open [--name <name>] <path>" }
  | ["new"] =>
    let name := s!"Workspace {wg.workspaces.size}"
    let newWs := makeWorkspaceState name none maxBufId
    let newState := state.updateCurrentWorkgroup fun wg =>
      { wg with
        workspaces := wg.workspaces.push newWs,
        currentWorkspace := wg.workspaces.size
      }
    return { newState with message := s!"Created workspace: {name}" }
  | ["new", name] =>
    let newWs := makeWorkspaceState name none maxBufId
    let newState := state.updateCurrentWorkgroup fun wg =>
      { wg with
        workspaces := wg.workspaces.push newWs,
        currentWorkspace := wg.workspaces.size
      }
    return { newState with message := s!"Created workspace: {name}" }
  | ["new", name, path] =>
    let absPath := resolvePath path
    let newWs := makeWorkspaceState name (some absPath) maxBufId
    let newState := state.updateCurrentWorkgroup fun wg =>
      { wg with
        workspaces := wg.workspaces.push newWs,
        currentWorkspace := wg.workspaces.size
      }
    return { newState with message := s!"Created workspace: {name} ({absPath})" }
  | ["close"] =>
    if wg.workspaces.size <= 1 then
      return { state with message := "Cannot close the last workspace" }
    else
      if h_idx : wg.currentWorkspace < wg.workspaces.size then
        let prevIdx := if wg.currentWorkspace == 0 then wg.workspaces.size - 1 else wg.currentWorkspace - 1
        let newSpaces := wg.workspaces.eraseIdx wg.currentWorkspace h_idx
        let newIdx := if prevIdx < newSpaces.size then prevIdx else newSpaces.size - 1
        let newState := state.updateCurrentWorkgroup fun wg =>
          { wg with workspaces := newSpaces, currentWorkspace := newIdx }
        let newWs := newSpaces[newIdx]!
        return { newState with message := s!"Workspace closed. Switched to: {newWs.name}" }
      else
        return { state with message := "Error: invalid workspace index" }
  | ["rename", name] =>
    let trimmed := name.trimAscii.toString
    if trimmed.isEmpty then
      return { state with message := "Workspace name cannot be empty" }
    else
      let wg := state.getCurrentWorkgroup
      let duplicate := wg.workspaces.any (fun ws => ws.name == trimmed)
      if duplicate then
        return { state with message := s!"Workspace name already exists: {trimmed}" }
      else
        let s' := state.updateCurrentWorkspace fun ws =>
          { ws with name := trimmed }
        return { s' with message := s!"Workspace renamed to: {trimmed}" }
  | ["next"] =>
    let nextIdx := (wg.currentWorkspace + 1) % wg.workspaces.size
    let ws := wg.workspaces[nextIdx]!
    let newState := state.updateCurrentWorkgroup fun wg =>
      { wg with currentWorkspace := nextIdx }
    return { newState with message := s!"Switched to: {ws.name}" }
  | ["prev"] =>
    let prevIdx := if wg.currentWorkspace == 0 then wg.workspaces.size - 1 else wg.currentWorkspace - 1
    let ws := wg.workspaces[prevIdx]!
    let newState := state.updateCurrentWorkgroup fun wg =>
      { wg with currentWorkspace := prevIdx }
    return { newState with message := s!"Switched to: {ws.name}" }
  | [n] =>
    match n.toNat? with
    | some num =>
      if num < wg.workspaces.size then
        let ws := wg.workspaces[num]!
        let newState := state.updateCurrentWorkgroup fun wg =>
          { wg with currentWorkspace := num }
        return { newState with message := s!"Switched to: {ws.name}" }
      else
        return { state with message := s!"Workspace index out of range (0-{wg.workspaces.size - 1})" }
    | none => return { state with message := "Invalid workspace number" }
  | [] =>
    let ws := wg.workspaces[wg.currentWorkspace]!
    return { state with message := s!"Current workspace: {ws.name} (index {wg.currentWorkspace})" }
  | _ => return { state with message := "Usage: :ws <new|open|list|close|rename|next|prev|index> [args]" }

def cmdExplorer (args : List String) (state : EditorState) : IO EditorState :=
  let path := match args with
     | [] => state.getCurrentWorkspace.rootPath.getD "."
     | [p] => p
     | _ => "."
  ViE.Feature.openExplorer state path

def cmdWgExplorer (_ : List String) (state : EditorState) : IO EditorState :=
  ViE.Feature.openWorkgroupExplorer state

def cmdReload (_ : List String) (state : EditorState) : IO EditorState := do
  let success ← ViE.Loader.buildConfig
  if success then
    -- Save session
    ViE.Checkpoint.saveSession state
    -- Restart
    ViE.Loader.restartEditor []
    return { state with shouldQuit := true }
  else
    return { state with message := "Configuration build failed" }


def defaultCommandMap : CommandMap := [
  ("e", cmdEdit),
  ("w", cmdWrite),
  ("q", cmdQuit),
  ("q!", cmdQuitForce),
  ("qa", cmdQuitForce),
  ("qa!", cmdQuitForce),
  ("wq", cmdWriteQuit),
  ("sp", cmdSplit),
  ("split", cmdSplit),
  ("hs", cmdSplit),
  ("hsplit", cmdSplit),
  ("vs", cmdVSplit),
  ("vsplit", cmdVSplit),
  ("set", cmdSet),
  ("wincmd", cmdWincmd),
  ("wh", cmdWinLeft),
  ("wj", cmdWinDown),
  ("wk", cmdWinUp),
  ("wl", cmdWinRight),
  ("wc", cmdWinCycle),
  ("cd", cmdCd),
  ("workspace", cmdWorkspace),
  ("ws", cmdWs),
  ("pwd", cmdPwd),
  ("wg", cmdWg),
  ("ee", cmdExplorer),
  ("wgex", cmdWgExplorer),
  ("undo", cmdUndo),
  ("u", cmdUndo),
  ("redo", cmdRedo),
  ("reload", cmdReload),
  ("refresh", cmdReload)
]

end ViE.Command
