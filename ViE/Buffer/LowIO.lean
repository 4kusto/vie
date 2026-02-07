import Lean
import ViE.Types
import ViE.Data.PieceTable

namespace ViE


/-- Load buffer from file using PieceTable -/
def emptyBuffer (filename : Option String) (buildLeafBits : Bool) : FileBuffer := {
  id := 0
  filename := filename
  dirty := false
  table := PieceTable.fromString "" buildLeafBits
  missingEol := false
  cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
}

def bufferFromData (filename : String) (data : ByteArray) (buildLeafBits : Bool) : FileBuffer :=
  let missingEol := data.size > 0 && data[data.size - 1]! != 10
  let table := PieceTable.fromByteArray data buildLeafBits
  {
    id := 0
    filename := some filename
    dirty := false
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
        return emptyBuffer (some filename) true
      else
        -- Read file as ByteArray
        let data ← IO.FS.readBinFile filename
        return bufferFromData filename data true
    else
      -- File doesn't exist, return empty buffer
      return emptyBuffer (some filename) true
  catch _ =>
    -- On error, return empty buffer
    return emptyBuffer (some filename) true

def loadBufferByteArrayWithConfig (filename : String) (config : EditorConfig) : IO FileBuffer := do
  let buildLeafBits := config.searchBloomBuildLeafBits
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        return emptyBuffer (some filename) buildLeafBits
      else
        let data ← IO.FS.readBinFile filename
        return bufferFromData filename data buildLeafBits
    else
      return emptyBuffer (some filename) buildLeafBits
  catch _ =>
    return emptyBuffer (some filename) buildLeafBits

def loadPreviewBufferByteArray (filename : String) (maxBytes : Nat) : IO FileBuffer := do
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        return emptyBuffer (some filename) true
      else
        let data ← IO.FS.withFile filename IO.FS.Mode.read fun handle =>
          handle.read (USize.ofNat maxBytes)
        return bufferFromData filename data true
    else
      return emptyBuffer (some filename) true
  catch _ =>
    return emptyBuffer (some filename) true

def loadPreviewBufferByteArrayWithConfig (filename : String) (maxBytes : Nat) (config : EditorConfig) : IO FileBuffer := do
  let buildLeafBits := config.searchBloomBuildLeafBits
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        return emptyBuffer (some filename) buildLeafBits
      else
        let data ← IO.FS.withFile filename IO.FS.Mode.read fun handle =>
          handle.read (USize.ofNat maxBytes)
        return bufferFromData filename data buildLeafBits
    else
      return emptyBuffer (some filename) buildLeafBits
  catch _ =>
    return emptyBuffer (some filename) buildLeafBits

end ViE
