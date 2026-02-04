import Lean
import ViE.Types
import ViE.Data.PieceTable

namespace ViE


/-- Load buffer from file using PieceTable -/
def loadBufferByteArray (filename : String) : IO FileBuffer := do
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        -- Directory: return empty buffer
        return {
          id := 0
          filename := some filename
          dirty := false
          table := PieceTable.fromString ""
          missingEol := false
          cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
        }
      else
        -- Read file as ByteArray
        let data ← IO.FS.readBinFile filename

        -- Check if file ends with newline (POSIX compliance)
        let missingEol := data.size > 0 && data[data.size - 1]! != 10

        let table := PieceTable.fromByteArray data

        return {
          id := 0
          filename := some filename
          dirty := false
          table := table
          missingEol := missingEol
          cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
        }
    else
      -- File doesn't exist, return empty buffer
      return {
        id := 0
        filename := some filename
        dirty := false
        table := PieceTable.fromString ""
        missingEol := false
        cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
      }
  catch _ =>
    -- On error, return empty buffer
    return {
      id := 0
      filename := some filename
      dirty := false
      table := PieceTable.fromString ""
      missingEol := false
      cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
    }

def loadPreviewBufferByteArray (filename : String) (maxBytes : Nat) : IO FileBuffer := do
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        return {
          id := 0
          filename := some filename
          dirty := false
          table := PieceTable.fromString ""
          missingEol := false
          cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
        }
      else
        let data ← IO.FS.withFile filename IO.FS.Mode.read fun handle =>
          handle.read (USize.ofNat maxBytes)
        let missingEol := data.size > 0 && data[data.size - 1]! != 10
        let table := PieceTable.fromByteArray data
        return {
          id := 0
          filename := some filename
          dirty := false
          table := table
          missingEol := missingEol
          cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
        }
    else
      return {
        id := 0
        filename := some filename
        dirty := false
        table := PieceTable.fromString ""
        missingEol := false
        cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
      }
  catch _ =>
    return {
      id := 0
      filename := some filename
      dirty := false
      table := PieceTable.fromString ""
      missingEol := false
      cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
    }

end ViE
