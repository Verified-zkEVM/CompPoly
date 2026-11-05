/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
import Lean

/-!
# Kernel replay: re-check every CompPoly declaration in Lean's kernel

`lake exe axiomsweep` reads axiom dependencies from the built `.olean`s, which record what
was *added* to the environment. A declaration can be added without the kernel checking it,
under `set_option debug.skipKernelTC true` or by meta code calling
`addDeclWithoutChecking`; the sweep then reports it with whatever axioms its term mentions,
for instance a "proof" of `False` with none at all.

This tool closes that gap the way the toolchain's `leanchecker` does, with core's
`Lean.Kernel.Environment.replay`: every constant of every module under a root is sent to the
kernel, against an environment loaded from the `.olean`s of the modules it imports.

## Chunks

`leanchecker` replays each module in its own task, all at once; on this library that needs
more memory than a CI runner has. Replaying everything in one pass does not fit either,
since the replayed constants accumulate. So the modules are put in import order (each after
everything it imports) and cut into contiguous chunks, and each chunk is replayed by a
child process against a base environment of everything its modules import from outside
the chunk.

Every module is in exactly one chunk, so every constant is checked once. A contiguous
chunk of the import order cannot be imported back through a module outside it: if `M`
in the chunk imports `N` outside it, `N` comes before the chunk, and so does everything
`N` imports. The child checks this anyway and fails if its base environment loaded any
module of its chunk. (A realised lemma such as `foo.eq_1` can be stored by several
modules; every copy is checked, as described below.)

Like `leanchecker`, replay skips `unsafe` and `partial` constants, which carry no proofs.

Run after `lake build` and `lake test`:

```
lake exe kernelreplay                        # roots CompPoly and CompPolyTests
lake exe kernelreplay --jobs 2               # two chunks at a time
lake exe kernelreplay --root MOD --chunk-size 8
lake exe kernelreplay --require-modules FILE # also fail if a listed module is out of scope
lake env lean --run KernelReplay.lean --self-script KernelReplay.lean   # without building
```

## Exported parts and duplicate names

Later chunks are checked against the *exported* parts of earlier modules, but each module's
own chunk checks its *private* part. Meta code can make the two differ (the exported copy of a
constant need only share its name, universe parameters and type), so each chunk first checks
that every exported constant is the private one, or an axiom of the same signature and
safety. A name stored by several modules, such as a realised `foo.eq_1`, is checked once per
copy: every theorem copy beyond the first goes to the kernel under a fresh name, and any other
duplicate must be identical. No copy is skipped.
-/

open Lean

namespace KernelReplay

/-- Root modules replayed when no `--root` is given; the same as `axiomsweep`'s. -/
def defaultRoots : Array Name := #[`CompPoly, `CompPolyTests]

structure Config where
  roots : Array Name := #[]
  /-- Modules per chunk. -/
  chunkSize : Nat := 16
  /-- Chunks replayed at once. -/
  jobs : Nat := 1
  /-- Set in a child: the chunk it replays. -/
  chunk? : Option Nat := none
  /-- A file listing, one per line, modules that must be among those replayed. -/
  requireModules? : Option String := none
  /-- When run as `lean --run FILE`, that `FILE`, so children are spawned the same way. -/
  selfScript? : Option String := none

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--root" :: mod :: rest, cfg => parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | "--chunk-size" :: n :: rest, cfg => match n.toNat? with
    | some k@(_ + 1) => parseArgs rest { cfg with chunkSize := k }
    | _ => .error s!"kernelreplay: --chunk-size needs a positive number, got {n}"
  | "--jobs" :: n :: rest, cfg => match n.toNat? with
    | some k@(_ + 1) => parseArgs rest { cfg with jobs := k }
    | _ => .error s!"kernelreplay: --jobs needs a positive number, got {n}"
  | "--chunk" :: n :: rest, cfg => match n.toNat? with
    | some k => parseArgs rest { cfg with chunk? := some k }
    | none => .error s!"kernelreplay: --chunk needs a number, got {n}"
  | "--require-modules" :: f :: rest, cfg =>
    parseArgs rest { cfg with requireModules? := some f }
  | "--self-script" :: f :: rest, cfg => parseArgs rest { cfg with selfScript? := some f }
  | arg :: _, _ => .error s!"kernelreplay: unknown or incomplete argument: {arg}\n\
      usage: lake exe kernelreplay [--root MOD]* [--chunk-size N] [--jobs N] \
      [--require-modules FILE] [--self-script FILE]"

/-- What replay needs from one module's `.olean` parts (exported, server, private). -/
structure ModuleParts where
  imports : Array Import
  /-- The exported part: what modules importing this one are checked against. -/
  exported : ModuleData
  /-- The last part present, which holds every constant with its proof. -/
  priv : ModuleData

/-- Read a module's `.olean` parts. -/
unsafe def readParts (m : Name) : IO ModuleParts := do
  let mFile ← findOLean m
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {m} does not exist \
      (build it first with `lake build` and `lake test`)"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then
    throw <| IO.userError s!"no module data in {mFile}"
  else
    -- A `module` file is written as three parts; with one missing, the exported part would
    -- be taken for the private one and its theorems checked only as axioms.
    if parts[0].1.isModule && parts.size != 3 then
      throw <| IO.userError s!"module {m} has {parts.size} of its 3 `.olean` parts"
    return { imports := parts[0].1.imports, exported := parts[0].1,
             priv := parts[parts.size - 1].1 }

/-- Every module under a root, in import order (each after the modules it imports), with its
module data. -/
unsafe def modulesInOrder (roots : Array Name) :
    IO (Array (Name × ModuleParts)) := do
  let underRoot (m : Name) : Bool := roots.any (·.isPrefixOf m)
  let mut order := #[]
  let mut done : Std.HashSet Name := {}
  let mut started : Std.HashSet Name := {}
  -- Iterative post-order DFS; `true` marks a module whose imports are all done.
  let mut stack : List (Name × Bool) := roots.toList.reverse.map (·, false)
  let mut data : Std.HashMap Name ModuleParts := {}
  while true do
    match stack with
    | [] => break
    | (m, expanded) :: rest =>
      stack := rest
      if done.contains m then continue
      if expanded then
        done := done.insert m
        let some d := data[m]? | throw <| IO.userError s!"kernelreplay: lost {m}"
        order := order.push (m, d)
        continue
      if started.contains m then continue
      started := started.insert m
      let parts ← readParts m
      data := data.insert m parts
      let deps := parts.imports.filterMap fun i =>
        if underRoot i.module && !done.contains i.module then some i.module else none
      stack := deps.toList.map (·, false) ++ (m, true) :: stack
  return order

/-- Two copies of one constant name agree on what importers see: name, universe parameters
and type. -/
def sameSignature (a b : ConstantInfo) : Bool :=
  a.toConstantVal == b.toConstantVal

/-- Whether an exported copy is a sound stand-in for the private constant it exports: the same
constant, or an axiom of the same signature. The module system exports theorems, unexposed
definitions and opaques as safe axioms, hiding their values; such an axiom adds nothing the
private constant does not justify, because that constant's own chunk checks it, so its type
is inhabited. That needs a private constant the kernel checks: not `unsafe`, not `partial`
(replay skips both). An *unsafe* exported axiom, as for a `partial def`'s `_unsafe_rec`, is
always accepted, since only unsafe code can use it. -/
def exportedMatches (exported priv : ConstantInfo) : Bool :=
  exported == priv ||
    (sameSignature exported priv &&
      match exported with
      | .axiomInfo a => a.isUnsafe || (!priv.isUnsafe && !priv.isPartial)
      | _ => false)

/-- A theorem copy renamed so the kernel checks its proof even when another constant with the
same name is in scope. References to the old name, in `all` and in the proof, are renamed too,
so the proof cannot lean on the copy kept under the old name. -/
def renamedTheorem (fresh : Name) : ConstantInfo → Option ConstantInfo
  | .thmInfo t =>
    let value := t.value.replace fun
      | .const n ls => if n == t.name then some (.const fresh ls) else none
      | _ => none
    some (.thmInfo { t with name := fresh, value, all := t.all.map fun n =>
      if n == t.name then fresh else n })
  | _ => none

/-- Replay chunk `i`. Returns the exit code. -/
unsafe def replayChunk (roots : Array Name) (chunkSize i : Nat) : IO UInt32 := do
  let order ← modulesInOrder roots
  let chunk := order.extract (i * chunkSize) ((i + 1) * chunkSize)
  let inChunk : Std.HashSet Name := chunk.foldl (·.insert ·.1) {}
  -- Every exported copy must be justified by the private constant this chunk checks, because
  -- later chunks are checked against the exported copies.
  for (m, parts) in chunk do
    let privMap : Std.HashMap Name ConstantInfo :=
      parts.priv.constNames.zip parts.priv.constants |>.foldl (fun acc (n, c) => acc.insert n c) {}
    for name in parts.exported.constNames, e in parts.exported.constants do
      match privMap[name]? with
      | none =>
        IO.eprintln s!"kernelreplay: {m} exports {name}, which its private part does not hold"
        return 1
      | some p =>
        unless exportedMatches e p do
          IO.eprintln s!"kernelreplay: {m} exports {name} with a different value, kind or \
            safety than the constant it checks"
          return 1
  -- Collect the chunk's constants. A name stored by several modules (a realised lemma such
  -- as `foo.eq_1`) keeps one copy under its own name; every other theorem copy is checked
  -- under a fresh name, so no proof is dropped.
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut extraCopies : Array ConstantInfo := #[]
  -- The imports the chunk's modules take from outside it, keeping `import all`: under the
  -- module system a build checks a file against the exported part of each import, plus
  -- the private part of the ones it imports with `import all`, and so does this replay.
  -- Loading every import's private part, as `leanchecker` does, holds all of Mathlib's
  -- proofs in memory for nothing.
  let mut baseImports : Std.HashMap Name Import := {}
  let mut allModules := true
  for (m, parts) in chunk do
    allModules := allModules && parts.priv.isModule
    for name in parts.priv.constNames, ci in parts.priv.constants do
      match newConstants[name]? with
      | none => newConstants := newConstants.insert name ci
      | some prev =>
        unless sameSignature prev ci do
          IO.eprintln s!"kernelreplay: {name} is stored by two modules of chunk {i} (one is \
            {m}) with different signatures"
          return 1
        -- Both copies must be theorems (each is checked), or identical safe non-theorems.
        -- A theorem next to an axiom of the same name is refused: the environment that
        -- `axiomsweep` reads keeps the theorem, so the axiom would go unreported.
        if (ci matches .thmInfo _) && (prev matches .thmInfo _) then
          extraCopies := extraCopies.push ci
        else unless prev == ci && !ci.isUnsafe do
          IO.eprintln s!"kernelreplay: {name} is stored by two modules of chunk {i} (one is \
            {m}) as different constants, or as a theorem and a non-theorem"
          return 1
    for imp in parts.imports do
      unless inChunk.contains imp.module do
        let prev := baseImports.getD imp.module { module := imp.module, importAll := false }
        baseImports := baseImports.insert imp.module
          { prev with importAll := prev.importAll || imp.importAll }
  -- A file outside the module system is built against the private part of everything.
  let level := if allModules then OLeanLevel.exported else OLeanLevel.private
  let base ← importModules (baseImports.toArray.map (·.2)) {} (trustLevel := 1024)
    (level := level)
  -- A chunk constant the base already holds came from a module outside the chunk; its own
  -- chunk (or, outside the roots, its library) accounts for that copy. This chunk's copy must
  -- have the same signature and, if a theorem, is checked under a fresh name. A copy the base
  -- loaded from a module *of this chunk* means the chunk is not closed under imports.
  let orderMap : Std.HashMap Name ModuleParts := order.foldl (fun acc (m, p) => acc.insert m p) {}
  for (name, ci) in newConstants do
    let some b := base.find? name | continue
    -- What the base copy really is: its private constant if it comes from a module under the
    -- roots (whose own chunk checks it), else what the base holds (Mathlib and core, trusted
    -- as the build trusts them).
    let mut bPriv := b
    let mut fromRoots := false
    if let some idx := base.getModuleIdxFor? name then
      if let some m := base.header.moduleNames[idx.toNat]? then
        if inChunk.contains m then
          IO.eprintln s!"kernelreplay: chunk {i}'s base environment loaded {name} from \
            {m}, a module of the chunk; the chunk is not closed under imports"
          return 1
        if let some parts := orderMap[m]? then
          fromRoots := true
          match (parts.priv.constNames.zip parts.priv.constants).find? (·.1 == name) with
          | some (_, c) => bPriv := c
          | none =>
            IO.eprintln s!"kernelreplay: the base holds {name} from {m}, whose private part \
              does not"
            return 1
    -- Outside the roots (Mathlib, core) the base holds exported copies, where a theorem is an
    -- axiom; those are trusted as the build trusts them, and this chunk's copy is still
    -- checked under a fresh name below.
    if fromRoots && (ci matches .thmInfo _) != (bPriv matches .thmInfo _) then
      IO.eprintln s!"kernelreplay: chunk {i} holds {name} as a theorem and its base \
        environment as a non-theorem, or the other way round"
      return 1
    unless sameSignature ci b do
      IO.eprintln s!"kernelreplay: chunk {i} holds {name}, which its base environment \
        already holds with a different signature"
      return 1
    unless ci matches .thmInfo _ || ci == bPriv do
      IO.eprintln s!"kernelreplay: chunk {i} holds {name}, which its base environment \
        already holds as a different non-theorem constant"
      return 1
    newConstants := newConstants.erase name
    if ci matches .thmInfo _ then extraCopies := extraCopies.push ci
  -- Fresh names for the extra theorem copies.
  let mut k := 0
  for ci in extraCopies do
    let mut fresh := Name.mkNum (`_kernelReplayCopy ++ ci.name) k
    while base.contains fresh || newConstants.contains fresh do
      k := k + 1
      fresh := Name.mkNum (`_kernelReplayCopy ++ ci.name) k
    k := k + 1
    let some renamed := renamedTheorem fresh ci | unreachable!
    newConstants := newConstants.insert fresh renamed
  try
    discard <| base.toKernelEnv.replay newConstants
  catch e =>
    IO.eprintln s!"kernelreplay: the kernel rejected a declaration in chunk {i} \
      ({chunk.map (·.1)}):\n{e}"
    return 1
  IO.println s!"kernelreplay: chunk {i}: {newConstants.size} constants from {chunk.size} \
    modules passed the kernel ({extraCopies.size} duplicate theorem copies checked under \
    fresh names)"
  return 0

end KernelReplay

open KernelReplay in
unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  if let some i := cfg.chunk? then
    try
      return (← replayChunk roots cfg.chunkSize i)
    catch e =>
      IO.eprintln s!"kernelreplay: chunk {i}: {e}"
      return 1
  -- Parent: count the modules, then run one child per chunk, `jobs` at a time.
  let order ← try modulesInOrder roots catch e =>
    IO.eprintln s!"kernelreplay: {e}"
    return 2
  -- Every required module must be in the import closure of the roots: one that no root imports
  -- is invisible to replay and to `axiomsweep` alike.
  if let some f := cfg.requireModules? then
    let replayed : Std.HashSet Name := order.foldl (·.insert ·.1) {}
    let required := (← IO.FS.lines f).filter (!·.trimAscii.isEmpty)
      |>.map (·.trimAscii.toString.toName)
    let missing := required.filter (!replayed.contains ·)
    unless missing.isEmpty do
      IO.eprintln s!"kernelreplay: {missing.size} required module(s) are not imported by \
        {roots}: {missing}"
      return 1
    IO.println s!"kernelreplay: all {required.size} required modules are in scope"
  let chunks := (order.size + cfg.chunkSize - 1) / cfg.chunkSize
  IO.println s!"kernelreplay: {order.size} modules under {roots}, in {chunks} chunks of \
    {cfg.chunkSize}"
  let self ← IO.appPath
  let rootArgs := roots.toList.flatMap fun r => ["--root", r.toString]
  let selfArgs := match cfg.selfScript? with
    | some f => ["--run", f]
    | none => []
  let mut failed : Array Nat := #[]
  let mut next := 0
  while next < chunks do
    let batch := (List.range cfg.jobs).filterMap fun k =>
      if next + k < chunks then some (next + k) else none
    let tasks ← batch.mapM fun i => IO.asTask do
      let child ← IO.Process.spawn { cmd := self.toString, args := (selfArgs ++ rootArgs ++
        ["--chunk-size", toString cfg.chunkSize, "--chunk", toString i]).toArray }
      child.wait
    for i in batch, task in tasks do
      match task.get with
      | .ok 0 => pure ()
      | _ => failed := failed.push i
    next := next + batch.length
  unless failed.isEmpty do
    IO.eprintln s!"kernelreplay: {failed.size} chunk(s) failed: {failed}"
    return 1
  IO.println s!"kernelreplay: all {order.size} modules passed the kernel."
  return 0
