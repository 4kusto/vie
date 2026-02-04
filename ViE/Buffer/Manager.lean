import ViE.State
import ViE.Types
import ViE.Buffer.Content
import ViE.Buffer.LowIO
import ViE.Workspace

namespace ViE.Buffer

open ViE

def createNewBuffer (state : EditorState) (content : TextBuffer) (filename : Option String) : (Nat × EditorState) :=
  let s' := state.updateCurrentWorkspace fun ws =>
    let id := ws.nextBufferId
    let buf : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer id filename content
    { ws with buffers := buf :: ws.buffers, nextBufferId := id + 1 }
  let ws := s'.getCurrentWorkspace
  (ws.nextBufferId - 1, s')

def addBuffer (state : EditorState) (buf : FileBuffer) : (Nat × EditorState) :=
  let s' := state.updateCurrentWorkspace fun ws =>
    let id := ws.nextBufferId
    let newBuf := { buf with id := id }
    { ws with buffers := newBuf :: ws.buffers, nextBufferId := id + 1 }
  let ws := s'.getCurrentWorkspace
  (ws.nextBufferId - 1, s')

def removeBuffer (state : EditorState) (bufId : Nat) : EditorState :=
  state.updateCurrentWorkspace fun ws =>
    { ws with buffers := ws.buffers.filter (fun b => b.id != bufId) }

def findBufferByFilename (state : EditorState) (fname : String) : Option Nat :=
  let ws := state.getCurrentWorkspace
  ws.buffers.find? (fun b => b.filename == some fname) |>.map (fun b => b.id)

/-- Open a file buffer in the active window. Loads from disk if necessary. -/
def openBuffer (state : EditorState) (filename : String) : IO EditorState := do
  let resolvedPath := state.getCurrentWorkspace.resolvePath filename
  match findBufferByFilename state resolvedPath with
  | some bid =>
    -- Switch to existing buffer
    let s' := state.updateActiveView fun v => { v with bufferId := bid, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
    return { s' with message := s!"Switched to \"{filename}\"" }
  | none =>
    try
      let loadedBuf ← ViE.loadBufferByteArray resolvedPath
      -- Assign new ID and add to workgroup
      let s' := state.updateCurrentWorkspace fun ws =>
        let id := ws.nextBufferId
        let buf := { loadedBuf with
          id := id
          table := { loadedBuf.table with undoLimit := state.config.historyLimit }
        }
        { ws with buffers := buf :: ws.buffers, nextBufferId := id + 1 }

      let ws := s'.getCurrentWorkspace
      let bid := ws.nextBufferId - 1

      let s'' := s'.updateActiveView fun v => { v with bufferId := bid, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
      return { s'' with message := s!"Loaded \"{filename}\"" }
    catch e =>
      return { state with message := s!"Error loading file: {e}" }


end ViE.Buffer
