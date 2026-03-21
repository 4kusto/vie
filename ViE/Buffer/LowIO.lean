-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import Lean
import ViE.Types
import ViE.Data.PieceTable

namespace ViE

private def loadCacheShardCount : Nat := 16
private abbrev LoadCacheMap := Lean.RBMap String FileBuffer compare

initialize loadCacheShards : Array (IO.Ref LoadCacheMap) ← do
  let mut shards : Array (IO.Ref LoadCacheMap) := #[]
  for _ in [0:loadCacheShardCount] do
    let r ← IO.mkRef (Lean.RBMap.empty : LoadCacheMap)
    shards := shards.push r
  pure shards

private def loadCacheKey (filename : String) (buildLeafBits buildOnEdit : Bool) : String :=
  s!"{filename}#bits={if buildLeafBits then "1" else "0"}#edit={if buildOnEdit then "1" else "0"}"

private def loadCacheShardIdx (key : String) : Nat :=
  (hash key).toNat % loadCacheShardCount

private def loadCacheGet (key : String) : IO (Option FileBuffer) := do
  let idx := loadCacheShardIdx key
  match loadCacheShards[idx]? with
  | none => pure none
  | some shard =>
      let m ← shard.get
      pure (m.find? key)

private def loadCacheInsert (key : String) (buf : FileBuffer) : IO Unit := do
  let idx := loadCacheShardIdx key
  match loadCacheShards[idx]? with
  | none => pure ()
  | some shard =>
      shard.modify fun m => m.insert key buf

private def loadCacheErase (key : String) : IO Unit := do
  let idx := loadCacheShardIdx key
  match loadCacheShards[idx]? with
  | none => pure ()
  | some shard =>
      shard.modify fun m => m.erase key

def invalidateBufferLoadCache (filename : String) : IO Unit := do
  for bits in [false, true] do
    for onEdit in [false, true] do
      loadCacheErase (loadCacheKey filename bits onEdit)

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
  let key := loadCacheKey filename buildLeafBits buildOnEdit
  try
    let path := System.FilePath.mk filename
    if ← path.pathExists then
      if ← path.isDir then
        return emptyBuffer (some filename) buildLeafBits buildOnEdit
      else
        match (← loadCacheGet key) with
        | some cached => return cached
        | none =>
            let data ← IO.FS.readBinFile filename
            let buf := bufferFromData filename data buildLeafBits buildOnEdit
            loadCacheInsert key buf
            return buf
    else
      return emptyBuffer (some filename) buildLeafBits buildOnEdit
  catch _ =>
    return emptyBuffer (some filename) buildLeafBits buildOnEdit

def prefetchBufferByteArrayWithConfig (filename : String) (config : EditorConfig) : IO Unit := do
  let _ ← IO.asTask do
    let _ ← loadBufferByteArrayWithConfig filename config
    pure ()
  pure ()

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
