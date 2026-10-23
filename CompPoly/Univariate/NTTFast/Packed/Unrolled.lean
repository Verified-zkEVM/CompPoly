/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

/-! # Generated straight-line kernels

The packed kernels are straight-line code over sixteen words, which the C compiler turns into
vector instructions, and the proofs relate each to a field-array model of the same shape. Both
are generated here from one description, in two dialects: `words` reads and writes packed
words with bounds proofs, `fields` reads and splices field arrays. Each generator expands to the
`let`s of its kernel, referring to the binders of the definition it is used in by name; word
arithmetic refers to the modulus `p` of a `Mont32Field p` instance.
-/

namespace CompPoly.CPolynomial.NTTFast.Packed.Unrolled
open Lean

/-- Packed words with proved bounds, or field arrays. -/
meta inductive Dialect where
  | words
  | fields

meta def name (s : String) : Ident := mkIdent (Name.mkSimple s)

meta def lit (k : Nat) : Term := Syntax.mkNumLit (toString k)

/-- Word `k` after index `idx` of `arr`. -/
meta def read (d : Dialect) (arr idx : Term) (k : Nat) : MacroM Term :=
  match d with
  | .words => `($(name "readUOffset") $arr $idx $(lit k)
      (by simp only [USize.reduceToNat]; omega))
  | .fields => `($(name "readField") $arr $idx $(lit k))

meta def add (d : Dialect) (x y : Term) : MacroM Term :=
  match d with
  | .words => `($(name "add") $(name "p") $x $y)
  | .fields => `($(name "fieldAdd") $x $y)

meta def sub (d : Dialect) (x y : Term) : MacroM Term :=
  match d with
  | .words => `($(name "sub") $(name "p") $x $y)
  | .fields => `($(name "fieldSub") $x $y)

meta def mul (d : Dialect) (x y : Term) : MacroM Term :=
  match d with
  | .words => `($(name "mul") $(name "p") $x $y)
  | .fields => `($(name "fieldMul") $x $y)

/-- Overwrite sixteen words of `b` from index `idx`. -/
meta def store16 (d : Dialect) (b idx : Term) (vs : Array Term) : MacroM Term :=
  match d with
  | .words => `($(name "write16U") $b $idx $vs*)
  | .fields => `($(name "splice") $b ($idx).toNat #[$vs,*])

/-- `let x := v` for each binding, then `body`. -/
meta def lets (bs : Array (Ident × Term)) (body : Term) : MacroM Term :=
  bs.foldrM (fun (x, v) b ↦ `(let $x:ident := $v; $b)) body

/-- Sixteen radix-four DIF butterflies across the quarters at `i0, …, i3` with twiddles from
`th` at `j`, `j1` and `tl` at `j`: lane `k` reads `x0_k, …, x3_k`, combines them into
`a0_k, …, a3_k` and outputs `y0_k, …, y3_k`. -/
meta def step16 (d : Dialect) : MacroM Term := do
  let b := name "b"
  let v (s : String) (q k : Nat) : Term := name s!"{s}{q}_{k}"
  let mut bs := #[]
  for k in [0:16] do
    let tw (arr j : String) := read d (name arr) (name j) k
    for q in [0:4] do
      bs := bs.push (name s!"x{q}_{k}", ← read d b (name s!"i{q}") k)
    bs := bs.push (name s!"a0_{k}", ← add d (v "x" 0 k) (v "x" 2 k))
    bs := bs.push (name s!"a1_{k}", ← add d (v "x" 1 k) (v "x" 3 k))
    bs := bs.push (name s!"a2_{k}", ← mul d (← tw "th" "j") (← sub d (v "x" 0 k) (v "x" 2 k)))
    bs := bs.push (name s!"a3_{k}", ← mul d (← tw "th" "j1") (← sub d (v "x" 1 k) (v "x" 3 k)))
    bs := bs.push (name s!"y0_{k}", ← add d (v "a" 0 k) (v "a" 1 k))
    bs := bs.push (name s!"y1_{k}", ← mul d (← tw "tl" "j") (← sub d (v "a" 0 k) (v "a" 1 k)))
    bs := bs.push (name s!"y2_{k}", ← add d (v "a" 2 k) (v "a" 3 k))
    bs := bs.push (name s!"y3_{k}", ← mul d (← tw "tl" "j") (← sub d (v "a" 2 k) (v "a" 3 k)))
  for q in [0:4] do
    bs := bs.push (b, ← store16 d b (name s!"i{q}") ((Array.range 16).map (v "y" q)))
  lets bs b

/-- The twiddles `w{s}_t` of layer `s + 1` of a sixteen-point block, from `t3`, `t2`, `t1`. -/
meta def twiddles (d : Dialect) (s : Nat) : MacroM (Array (Ident × Term)) := do
  let tws := #["t3", "t2", "t1"]
  let mut bs := #[]
  for t in [1:8 >>> s] do
    bs := bs.push (name s!"w{s}_{t}", ← read d (name tws[s]!) (lit 0) t)
  return bs

/-- The four final DIF layers of a sixteen-point block: layer `s` pairs points `k` and
`k + 2 ^ (4 - s)`; the difference of every pair but the first in its group is multiplied by
twiddle `w{s - 1}_t`. `x s k` names point `k` after layer `s`; `tw s` are the twiddle reads
emitted before layer `s + 1`. -/
meta def layers (d : Dialect) (x : Nat → Nat → String) (tw : Nat → MacroM (Array (Ident × Term))) :
    MacroM (Array (Ident × Term)) := do
  let mut bs := #[]
  for s in [1:5] do
    bs := bs ++ (← tw (s - 1))
    let h := 16 >>> s
    for group in [0:8 / h] do
      let g := 2 * h * group
      for t in [0:h] do
        let lo : Term := name (x (s - 1) (g + t))
        let hi : Term := name (x (s - 1) (g + t + h))
        bs := bs.push (name (x s (g + t)), ← add d lo hi)
        let diff ← sub d lo hi
        bs := bs.push (name (x s (g + t + h)),
          ← if t = 0 then pure diff else mul d (name s!"w{s - 1}_{t}") diff)
  return bs

/-- A sixteen-point block at `i` of `b` through its four final DIF layers, twiddles read before
each layer; `finish` receives the outputs. -/
meta def leaf16 (finish : Array Term → MacroM Term) : MacroM Term := do
  let mut bs := #[]
  for k in [0:16] do
    bs := bs.push (name s!"x0_{k}", ← read .fields (name "b") (name "i") k)
  bs := bs ++ (← layers .fields (fun s k ↦ s!"x{s}_{k}") (twiddles .fields))
  lets bs (← finish ((Array.range 16).map fun k ↦ (name s!"x4_{k}" : Term)))

/-- Eight sixteen-point blocks at `i0, …, i7` through their four final DIF layers, one per vector
lane; word `t` of every lane goes to half `half` of the natural-order line `bitrev (16 c + t)`,
optionally scaled. The touched output takes proved stores, given `hout`. -/
meta def lastHalf : MacroM Term := do
  let mut bs := #[]
  for s in [0:3] do
    bs := bs ++ (← twiddles .words s)
  for v in [0:8] do
    for k in [0:16] do
      bs := bs.push (name s!"x{v}_0_{k}", ← read .words (name "b") (name s!"i{v}") k)
    bs := bs ++ (← layers .words (fun s k ↦ s!"x{v}_{s}_{k}") fun _ ↦ pure #[])
  let store (t : Nat) : MacroM Term := do
    let ws ← (Array.range 8).mapM fun v ↦
      `($(name "scaleWord") $(name "p") $(name "factor") $(name "scale")
        $(name s!"x{v}_4_{t}"))
    `($(name "store8") $(name "o")
      (4 * (16 * ($(name "reverse32") (16 * $(name "c") + $(lit t)).toUInt32 >>>
        $(name "shift")).toUSize + 8 * $(name "half"))) $ws*
      ($(name "lastHalf_store") $(name "hout")
        ($(name "reverse32") (16 * $(name "c") + $(lit t)).toUInt32)))
  bs := bs.push (name "o", ← `($(name "touchLast") $(name "out")
    ($(name "lastHalf_usize") $(name "hout"))))
  for t in [0:16] do
    bs := bs.push (name "o", ← store t)
  lets bs (← `($(name "o").1))

/-- Sixteen radix-two DIF butterflies between the words from `i0` and from `i1`, with twiddles
from `w` at `j`. -/
meta def pair16 : MacroM Term := do
  let b := name "b"
  let mut bs := #[]
  for k in [0:16] do
    bs := bs.push (name s!"x{k}", ← read .words b (name "i0") k)
    bs := bs.push (name s!"y{k}", ← read .words b (name "i1") k)
    bs := bs.push (name s!"w{k}", ← read .words (name "w") (name "j") k)
  let sums ← (Array.range 16).mapM fun k ↦ add .words (name s!"x{k}") (name s!"y{k}")
  let diffs ← (Array.range 16).mapM fun k ↦ do
    mul .words (name s!"w{k}") (← sub .words (name s!"x{k}") (name s!"y{k}"))
  bs := bs.push (b, ← store16 .words b (name "i0") sums)
  lets bs (← store16 .words b (name "i1") diffs)

/-- The sixteen words of `b` from word `q`, given `h : LineFits b q`. -/
meta def line : MacroM Term := do
  let ws ← (Array.range 16).mapM fun k ↦
    `($(name "b").ugetUInt32LE (($(name "q") + $(lit k)) * 4)
      (by rw [($(name "lineFits_toNat") $(name "h") $(lit k) (by decide)).1]
          exact ($(name "lineFits_toNat") $(name "h") $(lit k) (by decide)).2))
  `(⟨$ws,*⟩)

/-- The transpose of a `16 × 16` tile of the streams `s0, …, s15` at word `q`, stored from word
`p` of `out` if every stream's line fits. -/
meta def transposeStep : MacroM Term := do
  let h := name "h"
  let mut bs := #[]
  for t in [0:16] do
    let mut proj : Term := h
    for _ in [0:t] do
      proj ← `($proj.2)
    if t < 15 then proj ← `($proj.1)
    bs := bs.push (name s!"x{t}", ← `($(name "line") $(name s!"s{t}") $(name "q") $proj))
  let store (u : Nat) : MacroM Term := do
    let p : Term ← if u = 0 then pure (name "p") else `($(name "p") + $(lit (16 * u)))
    let vs ← (Array.range 16).mapM fun t ↦ `($(name s!"x{t}").$(name s!"w{u}"):ident)
    `($(name "write16U") $(name "out") $p $vs*)
  for u in [0:15] do
    bs := bs.push (name "out", ← store u)
  let fits ← (Array.range 16).mapM fun t ↦ `($(name "LineFits") $(name s!"s{t}") $(name "q"))
  let cond ← fits[:15].foldrM (fun f c ↦ `($f ∧ $c)) fits[15]!
  let body ← lets bs (← store 15)
  `(if $h:ident : $cond then $body else $(name "out"))

end CompPoly.CPolynomial.NTTFast.Packed.Unrolled

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The body of a sixteen-lane radix-four kernel on packed words. -/
macro "step16_words%" : term => step16 .words

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The body of a sixteen-lane radix-four kernel on field arrays. -/
macro "step16_fields%" : term => step16 .fields

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The final DIF layers of the block at `i` of a field array, spliced back. -/
macro "leaf16_fields%" : term =>
  leaf16 fun ys ↦ `($(name "splice") $(name "b") ($(name "i")).toNat #[$ys,*])

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The final DIF layers of the block at `i` of a field array, as a line. -/
macro "leaf16_line%" : term => leaf16 fun ys ↦ `(⟨$ys,*⟩)

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The body of the fused final-layer kernel on packed words. -/
macro "lastHalf_words%" : term => lastHalf

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The body of the sixteen-lane radix-two kernel on packed words. -/
macro "pair16_words%" : term => pair16

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The sixteen words of a line. -/
macro "line_words%" : term => line

open CompPoly.CPolynomial.NTTFast.Packed.Unrolled in
/-- The body of the `16 × 16` tile transpose on packed words. -/
macro "transposeStep_words%" : term => transposeStep
