import ViE.State
import ViE.IO

namespace ViE.Checkpoint

def sessionFile : String := "/tmp/editor_session.tmp"

/-- Save current session state to a temporary file. -/
def saveSession (state : EditorState) : IO Unit := do
  let ws := state.getCurrentWorkspace
  let buffers := ws.buffers.filter (fun b => b.filename.isSome)

  let activeBuffer := state.getActiveBuffer
  let activeIdx := buffers.findIdx? (fun b => b.id == activeBuffer.id) |>.getD 0

  -- Create content:
  -- FILE1
  -- ROW COL
  -- ...
  -- --ACTIVE--
  -- INDEX

  let mut content := ""
  for b in buffers do
    content := content ++ b.filename.get! ++ "\n"
    if b.id == activeBuffer.id then
       let cursor := state.getCursor
       content := content ++ s!"{cursor.row} {cursor.col}\n"
    else
       content := content ++ "0 0\n"

  content := content ++ "--ACTIVE--\n"
  content := content ++ s!"{activeIdx}\n"

  IO.FS.writeFile sessionFile content

/-- Load session state from temporary file. -/
def loadSession : IO (Option (List String × Nat × List (Nat × Nat))) := do
  if ← System.FilePath.pathExists sessionFile then
    let content ← IO.FS.readFile sessionFile
    -- Clean up the file immediately so next run doesn't pick it up if not intended
    IO.FS.removeFile sessionFile

    let lines := content.splitOn "\n"
    let rec parseFiles (lines : List String) (accFiles : List String) (accCursors : List (Nat × Nat)) : Option (List String × Nat × List (Nat × Nat)) :=
      match lines with
      | [] => none
      | "--ACTIVE--" :: idxStr :: _ =>
        let idx := idxStr.toNat!
        some (accFiles.reverse, idx, accCursors.reverse)
      | fname :: coords :: rest =>
        let parts := coords.splitOn " "
        match parts with
        | [r, c] =>
           let cursor := (r.toNat!, c.toNat!)
           parseFiles rest (fname :: accFiles) (cursor :: accCursors)
        | _ => none -- Parse error
      | _ => none

    return parseFiles lines [] []
  else
    return none

end ViE.Checkpoint
