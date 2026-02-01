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

def cmdWinLeft (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .left
def cmdWinDown (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .down
def cmdWinUp (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .up
def cmdWinRight (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.switchWindow state .right
def cmdWinCycle (_ : List String) (state : EditorState) : IO EditorState := return ViE.Window.cycleWindow state

def cmdCd (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | [path] =>
    -- Change workspace
    let absPath := if path.startsWith "/" then path
                   else match state.workspace.rootPath with
                        | some root => root ++ "/" ++ path
                        | none => path
    return { state with
      workspace := { rootPath := some absPath },
      message := s!"Workspace: {absPath}"
    }
  | [] =>
    -- Clear workspace
    return { state with
      workspace := defaultWorkspace,
      message := "Workspace cleared"
    }
  | _ => return { state with message := "Usage: :cd [path]" }

def cmdPwd (_ : List String) (state : EditorState) : IO EditorState :=
  match state.workspace.rootPath with
  | some path => return { state with message := path }
  | none => return { state with message := "No workspace set" }

def cmdWg (args : List String) (state : EditorState) : IO EditorState :=
  match args with
  | [n] =>
    match n.toNat? with
    | some num =>
      if num < 10 then
        let s' := state.switchToWorkgroup num
        return { s' with message := s!"Switched to workgroup {num}" }
      else
        return { state with message := "Workgroup number must be 0-9" }
    | none => return { state with message := "Invalid workgroup number" }
  | [] => return { state with message := s!"Current workgroup: {state.currentGroup}" }
  | _ => return { state with message := "Usage: :wg [0-9]" }

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
  ("pwd", cmdPwd),
  ("wg", cmdWg),
  ("ee", cmdExplorer),
  ("reload", cmdReload),
  ("refresh", cmdReload)
]

end ViE.Command
