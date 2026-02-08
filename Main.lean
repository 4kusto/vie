import ViE
import ViE.Color

open ViE.Color

def customConfig : ViE.EditorConfig := {
  ViE.defaultConfig with
  showLineNumbers := true
  tabStop := 4
  statusBarStyle := (toBg Color.brightBlack) ++ (toFg Color.white)
  --fileIcon := "File: "
  --dirIcon := "Dir : "
}

def customKeyMap (commands : ViE.CommandMap) : ViE.KeyMap := {
  ViE.Key.makeKeyMap commands with
  normal := fun s k => match k with
    -- Example custom binding: 'X' to quit
    | ViE.Key.char 'X' => pure { s with shouldQuit := true }
    | _ => (ViE.Key.makeKeyMap commands).normal s k
  visual := fun s k => match k with
    | ViE.Key.char 'o' => pure (ViE.Window.cycleWindow s)
    | _ => (ViE.Key.makeKeyMap commands).visual s k
}

def myCustomCommand (_ : List String) (state : ViE.EditorState) : IO ViE.EditorState := do
  return { state with message := "Executed custom command!" }

def main (args : List String) : IO Unit := do
  let myCommands : ViE.CommandMap := [
    ("mycmd", myCustomCommand),
    ("o", ViE.Command.cmdWinCycle)
  ]

  let commands := ViE.Command.defaultCommandMap ++ myCommands

  let config : ViE.Config := {
    settings := customConfig
    bindings := customKeyMap commands
    commands := commands
  }

  ViE.start config args
