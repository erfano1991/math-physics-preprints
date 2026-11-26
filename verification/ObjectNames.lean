import Lean

open Lean

/-- Read names from the most complete object-file part, including private data. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  for arg in args do
    let mod := arg.toName
    let path ← findOLean mod
    let mut files := #[path]
    for lvl in [OLeanLevel.server, OLeanLevel.private] do
      let file := lvl.adjustFileName path
      if ← file.pathExists then files := files.push file
    let parts ← readModuleDataParts files
    let some (data, _) := parts.back? | throw <| IO.userError s!"empty object file for {mod}"
    IO.println s!"MOD\t{mod}\t{data.constNames.size}\t{path}"
    for name in data.constNames do
      IO.println s!"OBJ\t{mod}\t{name}"
