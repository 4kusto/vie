namespace ViE.Command

/-- Parse filename argument from command args.
    Returns the filename from args, or the current buffer's filename if no args provided.
    Returns error message if multiple args or no filename available. -/
def parseFilenameArg (args : List String) (currentFilename : Option String) : Except String String :=
  match args with
  | [fname] => .ok fname
  | [] => match currentFilename with
    | some fname => .ok fname
    | none => .error "No file name"
  | _ => .error "Too many arguments"

end ViE.Command
