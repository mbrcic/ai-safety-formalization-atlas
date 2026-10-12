/-
Kernel replay of exactly one module per argument, for `scripts/kernel_replay.sh`.

`leanchecker M` does not replay M alone: it selects every module whose name has
M as a prefix (`target.isPrefixOf m` in the toolchain's `LeanChecker.lean`) and
replays them all at once in one process. A per-module loop over the atlas
therefore replayed each parent module's whole subtree again on the parent's
turn -- `AISafetyAtlas.Inference.Complexity` cost 26 s and 9.8 GB that way
against 3.7 s and 2.7 GB alone -- and that duplication, not the kernel, is what
made the nightly replay outgrow its budget.

`replayFromImports` below is copied verbatim from the toolchain's
`src/lean/LeanChecker.lean`; only module selection differs. The shell script
compares the copy against the installed toolchain before running and refuses to
run if they differ, so a toolchain bump cannot leave this replaying under rules
the shipped checker no longer uses.
-/
import Lean.CoreM
import Lean.Replay

open Lean

-- BEGIN verbatim replayFromImports
unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions
-- END verbatim replayFromImports

/-- Constants the module itself adds, read from its most private olean part
without importing anything. Zero means a pure aggregator: nothing to replay, so
its import closure -- the largest in the tree for the root -- is never loaded. -/
unsafe def ownConstantCount (module : Name) : IO Nat := do
  let mFile ← findOLean module
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  return parts[parts.size-1].1.constNames.size

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  for arg in args do
    let module := arg.toName
    if module.isAnonymous then
      throw <| IO.userError s!"Could not resolve module: {arg}"
    let n ← ownConstantCount module
    if n == 0 then
      IO.println s!"skip {module}"
    else
      replayFromImports module
      IO.println s!"ok {module} {n}"
  return 0
