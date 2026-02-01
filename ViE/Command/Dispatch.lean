import ViE.State
import ViE.IO

import ViE.Loader
import ViE.Checkpoint
import ViE.Types
import ViE.Buffer.Content
import ViE.Window.Actions
import ViE.Window.Analysis
import ViE.Buffer
import ViE.Command.Explorer
import ViE.Command.Parser

open ViE.Window
open ViE.Buffer
open ViE.Feature
open ViE.Command

namespace ViE.Command

def executeCommand (commands : CommandMap) (state : EditorState) : IO EditorState := do
  let fullCmd := state.inputState.commandBuffer
  let parts := fullCmd.splitOn " "
  match parts with
  | [] => return state
  | cmd :: args =>
    match commands.lookup cmd with
    | some action => action args state
    | none => return { state with message := s!"Unknown command: {fullCmd}" }

end ViE.Command
