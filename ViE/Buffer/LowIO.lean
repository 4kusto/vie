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
          cache := { lineMap := Lean.RBMap.empty }
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
          cache := { lineMap := Lean.RBMap.empty }
        }
    else
      -- File doesn't exist, return empty buffer
      return {
        id := 0
        filename := some filename
        dirty := false
        table := PieceTable.fromString ""
        missingEol := false
        cache := { lineMap := Lean.RBMap.empty }
      }
  catch _ =>
    -- On error, return empty buffer
    return {
      id := 0
      filename := some filename
      dirty := false
      table := PieceTable.fromString ""
      missingEol := false
      cache := { lineMap := Lean.RBMap.empty }
    }

end ViE
