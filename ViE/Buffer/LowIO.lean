import Lean
import ViE.Types
import ViE.Data.PieceTable

namespace ViE


/-- Load buffer from file using PieceTable -/
def emptyBuffer (filename : Option String) (buildLeafBits : Bool) (buildOnEdit : Bool) : FileBuffer := {
  id := 0
  filename := filename
  dirty := false
  loaded := true
  table := PieceTable.fromString "" buildLeafBits buildOnEdit
  missingEol := false
  cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
}

def bufferFromData (filename : String) (data : ByteArray) (buildLeafBits buildOnEdit : Bool) : FileBuffer :=
  let missingEol := data.size > 0 && data[data.size - 1]! != 10
  let table := PieceTable.fromByteArray data buildLeafBits buildOnEdit
  {
    id := 0
    filename := some filename
    dirty := false
    loaded := true
    table := table
    missingEol := missingEol
    cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
  }

def loadBufferByteArray (filename : String) : IO FileBuffer := do
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        -- Directory: return empty buffer
        return emptyBuffer (some filename) true false
      else
        -- Read file as ByteArray
        let data ← IO.FS.readBinFile filename
        return bufferFromData filename data true false
    else
      -- File doesn't exist, return empty buffer
      return emptyBuffer (some filename) true false
  catch _ =>
    -- On error, return empty buffer
    return emptyBuffer (some filename) true false

def loadBufferByteArrayWithConfig (filename : String) (config : EditorConfig) : IO FileBuffer := do
  let buildLeafBits := config.searchBloomBuildLeafBits
  let buildOnEdit := config.searchBloomBuildOnEdit
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        return emptyBuffer (some filename) buildLeafBits buildOnEdit
      else
        let data ← IO.FS.readBinFile filename
        return bufferFromData filename data buildLeafBits buildOnEdit
    else
      return emptyBuffer (some filename) buildLeafBits buildOnEdit
  catch _ =>
    return emptyBuffer (some filename) buildLeafBits buildOnEdit

def loadPreviewBufferByteArrayWithConfig (filename : String) (maxBytes : Nat) (config : EditorConfig) : IO FileBuffer := do
  let buildLeafBits := config.searchBloomBuildLeafBits
  let buildOnEdit := config.searchBloomBuildOnEdit
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        return emptyBuffer (some filename) buildLeafBits buildOnEdit
      else
        let data ← IO.FS.withFile filename IO.FS.Mode.read fun handle =>
          handle.read (USize.ofNat maxBytes)
        return bufferFromData filename data buildLeafBits buildOnEdit
    else
      return emptyBuffer (some filename) buildLeafBits buildOnEdit
  catch _ =>
    return emptyBuffer (some filename) buildLeafBits buildOnEdit

end ViE
