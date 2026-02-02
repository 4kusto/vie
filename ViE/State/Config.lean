import Lean
import ViE.Types
import ViE.Basic
import ViE.Color
import ViE.Workspace
import ViE.Data.PieceTable

namespace ViE


def defaultStatus := (ViE.Color.toBg <|
  (ViE.Color.fromHex "333333").getD
   .brightBlack) ++ (ViE.Color.toFg .white)

def defaultWorkspace : Workspace := {
  rootPath := none
  name := "ViE"
}

def defaultConfig : EditorConfig := {
  showLineNumbers := false
  vSplitStr := "│"
  hSplitStr := "─"
  emptyLineMarker := "~"
  statusBarStyle := defaultStatus
  resetStyle := ViE.Color.reset
  fileIcon := "📄 "
  dirIcon := "📁 "
}

def initialInputState : InputState := {
  previousKey := none
  countBuffer := ""
  commandBuffer := ""
  pendingKeys := ""
  lastInputTime := 0
}


def initialBuffer : FileBuffer := {
  id := 0
  filename := none
  dirty := false
  table := PieceTable.fromString ""
  missingEol := false
  cache := { lineMap := Lean.RBMap.empty }
}


def initialView : ViewState := {
  bufferId := 0
  cursor := Point.zero
  scrollRow := Row.zero
  scrollCol := Col.zero
}

def initialWorkgroupState : WorkgroupState := {
  name := "1"
  buffers := [initialBuffer]
  nextBufferId := 1
  layout := .window 0 initialView
  activeWindowId := 0
  nextWindowId := 1
}

def createEmptyWorkgroup (name : String) (nextBufId : Nat) : WorkgroupState := {
  name := name
  buffers := [{ initialBuffer with id := nextBufId }]
  nextBufferId := nextBufId + 1
  layout := .window 0 initialView
  activeWindowId := 0
  nextWindowId := 1
}


/-- Helper to create an array of initial workgroup states -/
def makeInitialWorkgroups : Array WorkgroupState :=
  #[initialWorkgroupState]


def initialState : EditorState := {
  mode := .normal
  -- Initialize 10 workgroups
  workgroups := makeInitialWorkgroups
  currentGroup := 0
  message := "Welcome to Lean Editor"
  shouldQuit := false
  config := defaultConfig
  workspace := defaultWorkspace
  clipboard := none
  selectionStart := none
  explorers := []
  inputState := initialInputState
  windowHeight := 0
  windowWidth := 0
  dirty := true
}

end ViE
