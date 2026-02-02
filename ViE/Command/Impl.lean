import ViE.State
import ViE.Types
import ViE.Window.Actions
import ViE.Buffer.Manager
import ViE.Command.Explorer
import ViE.Loader
import ViE.Checkpoint
import ViE.Command.Parser

namespace ViE.Command

open ViE.Window
open ViE.Buffer
open ViE.Feature

def cmdEdit (args : List String) (state : EditorState) : IO EditorState := do
  match args with
  | [fname] =>
    -- Resolve path relative to workspace
    let resolvedPath := state.workspace.resolvePath fname
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
    let absPath := if path.startsWith "/" then path
                   else match state.workspace.rootPath with
                        | some root => root ++ "/" ++ path
                        | none => path
    return { state with
      workspace := { state.workspace with rootPath := some absPath },
      message := s!"Workspace path: {absPath}"
    }
  | [] =>
    return { state with
      workspace := defaultWorkspace,
      message := "Workspace cleared"
    }
  | _ => return { state with message := "Usage: :cd [path]" }

def cmdWorkspace (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | ["open", path] => cmdCd [path] state
  | ["rename", name] =>
    return { state with
      workspace := { state.workspace with name := name },
      message := s!"Workspace renamed to: {name}"
    }
  | _ => return { state with message := "Usage: :workspace <open|rename> <args>" }

def cmdPwd (_ : List String) (state : EditorState) : IO EditorState :=
  match state.workspace.rootPath with
  | some path => return { state with message := path }
  | none => return { state with message := "No workspace set" }

def cmdWg (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | ["new"] =>
    let name := s!"Group {state.workgroups.size}"
    let nextBufId := state.workgroups.foldl (fun m g => max m g.nextBufferId) 0
    let newWg := createEmptyWorkgroup name nextBufId
    let newState := { state with
      workgroups := state.workgroups.push newWg,
      currentGroup := state.workgroups.size -- switch to new one using the size before push
    }
    return { newState with message := s!"Created workgroup: {name}" }
  | ["new", name] =>
    let nextBufId := state.workgroups.foldl (fun m g => max m g.nextBufferId) 0
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
    let current := state.workgroups[state.currentGroup]!
    let updated := { current with name := name }
    return { state with
      workgroups := state.workgroups.set! state.currentGroup updated,
      message := s!"Workgroup renamed to: {name}"
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
  | _ => return { state with message := "Usage: :wg <new|close|rename|next|prev|index> [args]" }

def cmdExplorer (args : List String) (state : EditorState) : IO EditorState :=
  let path := match args with
     | [] => state.workspace.rootPath.getD "."
     | [p] => p
     | _ => "."
  ViE.Feature.openExplorer state path

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
  ("pwd", cmdPwd),
  ("wg", cmdWg),
  ("ee", cmdExplorer),
  ("undo", cmdUndo),
  ("u", cmdUndo),
  ("redo", cmdRedo),
  ("reload", cmdReload),
  ("refresh", cmdReload)
]

end ViE.Command
