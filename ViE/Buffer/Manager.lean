import ViE.State
import ViE.Types
import ViE.Buffer.Content
import ViE.Buffer.LowIO

namespace ViE.Buffer

open ViE

def createNewBuffer (state : EditorState) (content : TextBuffer) (filename : Option String) : (Nat × EditorState) :=
  let s' := state.updateCurrentWorkgroup fun wg =>
    let id := wg.nextBufferId
    let buf : FileBuffer := ViE.Buffer.fileBufferFromTextBuffer id filename content
    { wg with buffers := buf :: wg.buffers, nextBufferId := id + 1 }
  let wg := s'.getCurrentWorkgroup
  (wg.nextBufferId - 1, s')

def findBufferByFilename (state : EditorState) (fname : String) : Option Nat :=
  let wg := state.getCurrentWorkgroup
  wg.buffers.find? (fun b => b.filename == some fname) |>.map (fun b => b.id)

/-- Open a file buffer in the active window. Loads from disk if necessary. -/
def openBuffer (state : EditorState) (filename : String) : IO EditorState := do
  let resolvedPath := state.workspace.resolvePath filename
  match findBufferByFilename state resolvedPath with
  | some bid =>
    -- Switch to existing buffer
    let s' := state.updateActiveView fun v => { v with bufferId := bid, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
    return { s' with message := s!"Switched to \"{filename}\"" }
  | none =>
    try
      let loadedBuf ← ViE.loadBufferByteArray resolvedPath
      -- Assign new ID and add to workgroup
      let s' := state.updateCurrentWorkgroup fun wg =>
        let id := wg.nextBufferId
        let buf := { loadedBuf with
          id := id
          table := { loadedBuf.table with undoLimit := state.config.historyLimit }
        }
        { wg with buffers := buf :: wg.buffers, nextBufferId := id + 1 }

      let wg := s'.getCurrentWorkgroup
      let bid := wg.nextBufferId - 1

      let s'' := s'.updateActiveView fun v => { v with bufferId := bid, cursor := {row:=0, col:=0}, scrollRow:=0, scrollCol:=0 }
      return { s'' with message := s!"Loaded \"{filename}\"" }
    catch e =>
      return { state with message := s!"Error loading file: {e}" }


end ViE.Buffer
