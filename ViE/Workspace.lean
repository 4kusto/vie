import ViE.Types

namespace ViE

/--
Resolve a path to an absolute path.
- Absolute input is used as-is.
- Relative input is resolved from `basePath` when provided, otherwise from current directory.
- Uses `realPath` when possible; falls back to normalized absolute syntax when the path does not exist.
-/
def resolveAbsolutePath (basePath : Option String) (path : String) : IO String := do
  let candidate : System.FilePath ←
    if path.startsWith "/" then
      pure (System.FilePath.mk path)
    else
      match basePath with
      | some base => pure <| System.FilePath.mk (base ++ "/" ++ path)
      | none =>
          let cwd ← IO.currentDir
          pure <| System.FilePath.mk (cwd.toString ++ "/" ++ path)
  try
    let resolved ← IO.FS.realPath candidate
    pure resolved.toString
  catch _ =>
    pure candidate.normalize.toString

/-- Resolve a file path relative to workspace -/
def WorkspaceState.resolvePath (ws : WorkspaceState) (path : String) : String :=
  if path.startsWith "/" then
    -- Absolute path, use as-is
    path
  else
    -- Relative path, resolve from workspace
    match ws.rootPath with
    | some root => root ++ "/" ++ path
    | none => path  -- No workspace, use as-is

end ViE
