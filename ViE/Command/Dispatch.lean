import ViE.State
import ViE.IO

import ViE.Loader
import ViE.Checkpoint
import ViE.Types
import ViE.Buffer.Content
import ViE.Window.Actions
import ViE.Window.Analysis
import ViE.Buffer
import ViE.Command.Explorer
import ViE.Command.Parser
import ViE.State.Search
import ViE.Data.PieceTable.Tree

open ViE.Window
open ViE.Buffer
open ViE.Feature
open ViE.Command

namespace ViE.Command

def collectMatchesInBytes (haystack : ByteArray) (needle : ByteArray) : Array (Nat × Nat) :=
  let n := needle.size
  let h := haystack.size
  if n == 0 || h < n then
    #[]
  else
    let rec loop (fuel : Nat) (i : Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
      match fuel with
      | 0 => acc
      | fuel + 1 =>
          if i + n > h then
            acc
          else
            match ViE.PieceTree.findPatternInBytes haystack needle i with
            | some idx =>
                if idx + n > h then
                  acc
                else
                  let nextI := if idx + n > i then idx + n else i + 1
                  loop fuel nextI (acc.push (idx, idx + n))
            | none => acc
    loop (h + 1) 0 #[]

def collectMatchesInPieceTable (pt : PieceTable) (pattern : ByteArray) : Array (Nat × Nat) :=
  let n := pattern.size
  if n == 0 then
    #[]
  else
    let total := pt.tree.length
    let rec loop (fuel : Nat) (offset : Nat)
      (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat)
      (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
      match fuel with
      | 0 => acc
      | fuel + 1 =>
          if offset >= total then
            acc
          else
            let (res, cache', order') :=
              ViE.PieceTree.searchNext pt.tree pt pattern offset ViE.searchChunkSize false cache order 0
            match res with
            | some idx =>
                if idx + n > total then
                  acc
                else
                  let nextOffset := if idx + n > offset then idx + n else offset + 1
                  loop fuel nextOffset cache' order' (acc.push (idx, idx + n))
            | none => acc
    loop (total + 1) 0 Lean.RBMap.empty #[] #[]

def replaceFirstInLine (line : String) (old : String) (new : String) : String :=
  if old.isEmpty then
    line
  else
    let parts := line.splitOn old
    match parts with
    | [] => line
    | p :: rest =>
        if rest.isEmpty then
          line
        else
          p ++ new ++ (String.intercalate old rest)

def replaceAllInLine (line : String) (old : String) (new : String) : String :=
  if old.isEmpty then
    line
  else
    String.intercalate new (line.splitOn old)

def parseSubstitute (cmd : String) : Option (Bool × String × String × String) :=
  let (isGlobal, rest) :=
    if cmd.startsWith "%s/" then
      (true, (cmd.drop 3).toString)
    else if cmd.startsWith "s/" then
      (false, (cmd.drop 2).toString)
    else
      (false, "")
  if rest.isEmpty then
    none
  else
    let parts := rest.splitOn "/"
    match parts with
    | old :: new :: flagsParts =>
        let flags := String.intercalate "/" flagsParts
        some (isGlobal, old, new, flags)
    | _ => none

def parseGlobal (cmd : String) : Option (Bool × String × String) :=
  if cmd.startsWith "g/" || cmd.startsWith "v/" then
    let isInvert := cmd.startsWith "v/"
    let rest := (cmd.drop 2).toString
    let parts := rest.splitOn "/"
    match parts with
    | pat :: cmdParts =>
        let subcmd := String.intercalate "/" cmdParts
        some (isInvert, pat, (subcmd.trimAscii).toString)
    | _ => none
  else
    none

def lineRangeWithNewline (pt : PieceTable) (row : Nat) : Option (Nat × Nat) :=
  match pt.getLineRange row with
  | some (startOff, len) =>
      let endOff := startOff + len
      if endOff < pt.tree.length then
        let b := ViE.PieceTree.getBytes pt.tree endOff 1 pt
        if b.size == 1 && b[0]! == (UInt8.ofNat 10) then
          some (startOff, len + 1)
        else
          some (startOff, len)
      else
        some (startOff, len)
  | none => none

def collectMatchesInLine (pt : PieceTable) (row : Nat) (pattern : ByteArray) : Array (Nat × Nat) :=
  match pt.getLineRange row with
  | some (startOff, len) =>
      let bytes := ViE.PieceTree.getBytes pt.tree startOff len pt
      let localMatches := collectMatchesInBytes bytes pattern
      localMatches.map (fun (s, e) => (startOff + s, startOff + e))
  | none => #[]

def execGlobal (cmd : String) (state : EditorState) : EditorState :=
  match parseGlobal cmd with
  | none => { state with message := s!"Invalid global: {cmd}" }
  | some (isInvert, pat, subcmd) =>
      if pat.isEmpty then
        { state with message := "Empty global pattern" }
      else
        let buf := state.getActiveBuffer
        let cursor := state.getCursor
        let cursorOffset := ViE.getOffsetFromPointInBuffer buf cursor.row.val cursor.col.val |>.getD 0
        let patBytes := pat.toUTF8
        let lineCount := buf.lineCount
        let matchingRows : Array Nat := Id.run do
          let mut rows : Array Nat := #[]
          for row in [0:lineCount] do
            let hasMatch := (collectMatchesInLine buf.table row patBytes).size > 0
            if (if isInvert then !hasMatch else hasMatch) then
              rows := rows.push row
          return rows
        if subcmd == "d" then
          let ranges : Array (Nat × Nat) := Id.run do
            let mut acc : Array (Nat × Nat) := #[]
            for row in matchingRows do
              match lineRangeWithNewline buf.table row with
              | some (startOff, len) => acc := acc.push (startOff, startOff + len)
              | none => pure ()
            return acc
          let newTable := buf.table.applyDeletions cursorOffset ranges
          let newBuf := { buf with table := newTable, dirty := true }
          state.updateActiveBuffer (fun _ => newBuf)
        else if subcmd.startsWith "s/" then
          match parseSubstitute subcmd with
          | none => { state with message := s!"Invalid substitute: {subcmd}" }
          | some (_isGlobal, old, new, flags) =>
              if old.isEmpty then
                { state with message := "Empty substitute pattern" }
              else
                let doGlobal := flags.contains 'g'
                let oldBytes := old.toUTF8
                let matches1 : Array (Nat × Nat) := Id.run do
                  let mut acc : Array (Nat × Nat) := #[]
                  for row in matchingRows do
                    let lineMatches := collectMatchesInLine buf.table row oldBytes
                    if doGlobal then
                      acc := acc.append lineMatches
                    else
                      match lineMatches[0]? with
                      | some first => acc := acc.push first
                      | none => pure ()
                  return acc
                let newTable := buf.table.applyReplacements cursorOffset matches1 new
                let newBuf := { buf with table := newTable, dirty := true }
                state.updateActiveBuffer (fun _ => newBuf)
        else
          { state with message := s!"Unsupported global subcommand: {subcmd}" }

def execSubstitute (cmd : String) (state : EditorState) : EditorState :=
  match parseSubstitute cmd with
  | none => { state with message := s!"Invalid substitute: {cmd}" }
  | some (isGlobal, old, new, flags) =>
      if old.isEmpty then
        { state with message := "Empty substitute pattern" }
      else
        let doGlobal := flags.contains 'g'
        let buf := state.getActiveBuffer
        let cursor := state.getCursor
        let cursorOffset := ViE.getOffsetFromPointInBuffer buf cursor.row.val cursor.col.val |>.getD 0
        let patBytes := old.toUTF8
        let matches1 :=
          if isGlobal then
            if doGlobal then
              collectMatchesInPieceTable buf.table patBytes
            else
              Id.run do
                let lineCount := buf.lineCount
                let mut acc : Array (Nat × Nat) := #[]
                for row in [0:lineCount] do
                  match buf.table.getLineRange row with
                  | some (startOff, len) =>
                      let bytes := ViE.PieceTree.getBytes buf.table.tree startOff len buf.table
                      match (collectMatchesInBytes bytes patBytes)[0]? with
                      | some (s, e) => acc := acc.push (startOff + s, startOff + e)
                      | none => pure ()
                  | none => pure ()
                return acc
          else
            match buf.table.getLineRange cursor.row.val with
            | some (startOff, len) =>
                let bytes := ViE.PieceTree.getBytes buf.table.tree startOff len buf.table
                let localMatches := collectMatchesInBytes bytes patBytes
                localMatches.map (fun (s, e) => (startOff + s, startOff + e))
            | none => #[]
        let matches2 :=
          if doGlobal || isGlobal then
            matches1
          else
            match matches1[0]? with
            | some first => #[first]
            | none => #[]
        let newTable := buf.table.applyReplacements cursorOffset matches2 new
        let newBuf := { buf with table := newTable, dirty := true }
        state.updateActiveBuffer (fun _ => newBuf)

def executeCommand (commands : CommandMap) (state : EditorState) : IO EditorState := do
  let fullCmd := state.inputState.commandBuffer
  if fullCmd.startsWith "s/" || fullCmd.startsWith "%s/" then
    return execSubstitute fullCmd state
  if fullCmd.startsWith "g/" || fullCmd.startsWith "v/" then
    return execGlobal fullCmd state
  let parts := fullCmd.splitOn " "
  match parts with
  | [] => return state
  | cmd :: args =>
    match commands.lookup cmd with
    | some action => action args state
    | none => return { state with message := s!"Unknown command: {fullCmd}" }

end ViE.Command
