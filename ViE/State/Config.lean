import Lean
import ViE.Types
import ViE.Basic
import ViE.Color
import ViE.Data.PieceTable

namespace ViE


def defaultStatus := (ViE.Color.toBg <|
  (ViE.Color.fromHex "333333").getD
   .brightBlack) ++ (ViE.Color.toFg .white)

def defaultWorkspaceName : String := "ViE"

def defaultConfig : EditorConfig := {
  showLineNumbers := false
  vSplitStr := "│"
  hSplitStr := "─"
  emptyLineMarker := "~"
  statusBarStyle := defaultStatus
  resetStyle := ViE.Color.reset
  fileIcon := "📄 "
  dirIcon := "📁 "
  searchHighlightStyle := (ViE.Color.toBg .white) ++ (ViE.Color.toFg .black)
  searchHighlightCursorStyle := (ViE.Color.toBg .yellow) ++ (ViE.Color.toFg .black)
  tabStop := 4
  searchBloomCacheMax := 1024
  searchBloomBuildLeafBits := true
}

def initialInputState : InputState := {
  previousKey := none
  countBuffer := ""
  commandBuffer := ""
  pendingKeys := ""
  lastInputTime := 0
  lastSearchInputTime := 0
  lastSearchRunTime := 0
  pendingSearch := false
}


def initialBuffer : FileBuffer := {
  id := 0
  filename := none
  dirty := false
  table := PieceTable.fromString ""
  missingEol := false
  cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
}


def initialView : ViewState := {
  bufferId := 0
  cursor := Point.zero
  scrollRow := Row.zero
  scrollCol := Col.zero
}

def makeWorkspaceState (name : String) (rootPath : Option String) (nextBufId : Nat) : WorkspaceState := {
  name := name
  rootPath := rootPath
  buffers := [{ initialBuffer with id := nextBufId }]
  nextBufferId := nextBufId + 1
  layout := .window 0 { initialView with bufferId := nextBufId }
  activeWindowId := 0
  nextWindowId := 1
}

def initialWorkgroupState : WorkgroupState := {
  name := "1"
  workspaces := #[makeWorkspaceState defaultWorkspaceName none 0]
  currentWorkspace := 0
}

def createEmptyWorkgroup (name : String) (nextBufId : Nat) : WorkgroupState := {
  name := name
  workspaces := #[makeWorkspaceState defaultWorkspaceName none nextBufId]
  currentWorkspace := 0
}


/-- Helper to create an array of initial workgroup states -/
def makeInitialWorkgroups : Array WorkgroupState := Id.run do
  let mut groups : Array WorkgroupState := #[]
  let mut nextBufId := 0
  for i in [0:10] do
    let name := s!"{i}"
    let wg := createEmptyWorkgroup name nextBufId
    groups := groups.push wg
    nextBufId := nextBufId + 1
  groups


def initialState : EditorState := {
  mode := .normal
  -- Initialize 10 workgroups
  workgroups := makeInitialWorkgroups
  currentGroup := 0
  message := "Welcome to Lean Editor"
  shouldQuit := false
  config := defaultConfig
  clipboard := none
  selectionStart := none
  explorers := []
  searchState := none
  floatingOverlay := none
  floatingInputCommand := none
  inputState := initialInputState
  windowHeight := 0
  windowWidth := 0
  dirty := true
}

end ViE
