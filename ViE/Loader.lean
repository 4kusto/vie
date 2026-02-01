namespace ViE.Loader

def getUserConfigDir : IO String := do
  let xdgConfig ← IO.getEnv "XDG_CONFIG_HOME"
  match xdgConfig with
  | some dir => return dir ++ "/vie"
  | none =>
    let home ← IO.getEnv "HOME"
    match home with
    | some h => return h ++ "/.config/vie"
    | none => return "./config"

def getCustomBinaryPath : IO String := do
  let dir ← getUserConfigDir
  return dir ++ "/.lake/build/bin/vie"

def buildConfig : IO Bool := do
  let dir ← getUserConfigDir
  try
    let out ← IO.Process.output {
      cmd := "lake"
      args := #["build"]
      cwd := dir
    }
    return out.exitCode == 0
  catch _ =>
    return false

/-- Restart the editor by spawning a new process and waiting for it. -/
def restartEditor (args : List String) : IO Unit := do
  let binPath ← getCustomBinaryPath
  -- Spawn the new process. It will take over the terminal.
  let child ← IO.Process.spawn {
    cmd := binPath
    args := args.toArray
  }
  -- Wait for the new process to finish instead of exiting.
  -- This prevents the shell prompt from flickering or appearing.
  let _ ← child.wait
  IO.Process.exit 0

end ViE.Loader
