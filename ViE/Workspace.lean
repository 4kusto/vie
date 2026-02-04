import ViE.Types

namespace ViE

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
