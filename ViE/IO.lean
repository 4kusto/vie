import ViE.State
import ViE.Basic
import ViE.Buffer

namespace ViE


/-- Save buffer to file with error handling using atomic write. -/
def saveBuffer (state : EditorState) (filename : String) : IO EditorState := do
  let tempFilename := filename ++ ".tmp"
  try
    let buffer := state.getActiveBuffer

    -- Get content from PieceTable
    let content := PieceTable.toString buffer.table

    -- Ensure POSIX compliance (end with newline)
    -- If missingEol is true, we preserve the "no newline at EOF" state (unless user added one).
    -- If missingEol is false, we enforce a trailing newline.
    let finalContent :=
      if buffer.missingEol then
        content
      else
        if !content.isEmpty && content.back != '\n' then
          content ++ "\n"
        else
          content

    -- Write to temporary file first
    IO.FS.writeFile tempFilename finalContent

    -- Rename temp file to target file (atomic on POSIX)
    IO.FS.rename tempFilename filename

    -- After save, reload as clean mmap
    let newBuffer ← loadBufferByteArrayWithConfig filename state.config
    let newBuffer := { newBuffer with id := buffer.id, dirty := false }

    -- Update the buffer in the current workgroup
    let state' := state.updateActiveBuffer fun _ => newBuffer

    return { state' with message := s!"\"{filename}\" saved" }
  catch e =>
    -- Try to clean up temp file if it exists (ignoring errors)
    try
      IO.FS.removeFile tempFilename
    catch _ => pure ()

    -- Keep dirty flag on error to prevent data loss
    return { state with message := s!"Error saving \"{filename}\": {e}" }


end ViE
