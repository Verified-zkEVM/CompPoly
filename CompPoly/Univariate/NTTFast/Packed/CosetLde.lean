/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.NativeLast
public import CompPoly.Univariate.NTTFast.Packed.DifSpec
public import CompPoly.Univariate.NTTFast.Coset
public import CompPoly.Data.Tasks
import CompPoly.Univariate.NTTFast.Packed.Unrolled

/-! # Batched coset low-degree extension over packed words

The low-degree extension of a row-major `h × w` matrix, `h = 2 ^ logH`, by `2 ^ bits`: each
column holds the values of a polynomial `p` of degree below `h` on the subgroup of order `h`,
and output row `r` holds the values of every column's `p` at `shift · ω ^ bitrev r`, where `ω`
generates the subgroup of order `H = h · 2 ^ bits`. That is Plonky3's `coset_lde_batch`, in the
bit-reversed row order its two-adic FRI commitment commits.

In that order the output splits into `2 ^ bits` blocks of `h` rows: block `t` holds the coset
`shift · ω ^ c · ⟨ω ^ (2 ^ bits)⟩`, `c = bitrev t`, in DIF order. So each column is one inverse
transform followed by `2 ^ bits` forward transforms of size `h`, each of the coefficients
scaled by the powers of `shift · ω ^ c` (and by `1 / h`), with no padding and no reversal.

Tasks transpose row ranges of the input into columns, extend each column, and transpose row
ranges of the extended columns back into rows. The result stays in those row chunks, which a
commitment hashes in parallel; `joinRows` copies them into one buffer.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode)

/-- The scaled coset powers `(1 / h) · (shift · ω ^ c) ^ j`, `j < h`, of coset `c` of the
subgroup of order `h = 2 ^ (D.logN - bits)` in `D`'s. -/
def cosetTable (D : NTT.Domain (FastField p)) (bits : Nat) (shift : FastField p) (c : Nat) : Array
    (FastField p) :=
  (NTTFast.powers (shift * D.omega ^ c) (2 ^ (D.logN - bits))).map
    (((2 ^ (D.logN - bits) : Nat) : FastField p)⁻¹ * ·)

/-- A reusable plan for low-degree extensions of `2 ^ (domain.logN - bits)`-row matrices onto
the coset `shift · ⟨domain.omega⟩`, with certified cached twiddles and coset tables. -/
structure LdePlan (p : ℕ) [Mont32Field p] where
  domain : NTT.Domain (FastField p)
  bits : Nat
  bits_le : bits ≤ domain.logN
  shift : FastField p
  log_bound : domain.logN ≤ 32
  byte_bound : 4 * domain.n < USize.size
  forwardTwiddles : Array ByteArray
  inverseTwiddles : Array ByteArray
  cosetTables : Array ByteArray
  forward_eq : forwardTwiddles =
    (NTTFast.Plan.twiddleTable (powDomain domain bits bits_le)).map encode
  inverse_eq : inverseTwiddles =
    (NTTFast.Plan.twiddleTable (powDomain domain bits bits_le).inverse).map encode
  tables_eq : cosetTables =
    (Array.range (2 ^ bits)).map fun c ↦ encode (cosetTable domain bits shift c)

namespace LdePlan

/-- Encode the twiddles of the subgroup of order `2 ^ (D.logN - bits)` and the coset tables
once. -/
def ofDomain (D : NTT.Domain (FastField p)) (bits : Nat) (hb : bits ≤ D.logN) (shift : FastField p)
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) : LdePlan p where
  domain := D
  bits := bits
  bits_le := hb
  shift := shift
  log_bound := h32
  byte_bound := hu
  forwardTwiddles := (NTTFast.Plan.twiddleTable (powDomain D bits hb)).map Native.encodeFields
  inverseTwiddles :=
    (NTTFast.Plan.twiddleTable (powDomain D bits hb).inverse).map Native.encodeFields
  cosetTables := (Array.range (2 ^ bits)).map fun c ↦
    Native.encodeFields (cosetTable D bits shift c)
  forward_eq := by
    apply congrArg (Array.map · _)
    funext a
    exact Native.encodeFields_eq a
  inverse_eq := by
    apply congrArg (Array.map · _)
    funext a
    exact Native.encodeFields_eq a
  tables_eq := by
    apply congrArg (Array.map · _)
    funext c
    exact Native.encodeFields_eq _

/-- The rows of the input matrix. -/
abbrev logH (P : LdePlan p) : Nat := P.domain.logN - P.bits

end LdePlan

namespace Native

/-- The products of words `i, …, i + 15` of `t` and `a`, stored from word `i` of `out`. -/
@[noinline, specialize]
def mul16 (p : ℕ) [Mont32Field p] (t a : @& ByteArray) (i : USize) (out : ByteArray)
    (h : 4 * (i.toNat + 15) + 3 < t.size ∧ 4 * (i.toNat + 15) + 3 < a.size ∧
      t.size < USize.size ∧ a.size < USize.size) : ByteArray :=
  mul16_words%

/-- The products of words `0, …, n - 1` of `t` and `a`. -/
@[specialize]
def mulWords (p : ℕ) [Mont32Field p] (t a : @& ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := zeroWords n
  for block in [:n / 16] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < t.size ∧ 4 * (i + 15) + 3 < a.size ∧
        t.size < USize.size ∧ a.size < USize.size then
      out := mul16 p t a (USize.ofNatLT i (by omega)) out
        (by simpa only [USize.toNat_ofNatLT] using h)
  for k in [16 * (n / 16):n] do
    out := write out k (mul p (read t k) (read a k))
  return out

/-- The transpose of the `16 × 16` tile whose line `t` is words `q + t * qs, …, q + t * qs + 15`
of `s`, line `u` stored from word `p + u * ps` of `out`. -/
@[noinline] def tileStrided (s : @& ByteArray) (q qs : USize) (out : ByteArray) (p ps : USize) :
    ByteArray :=
  tile16_strided%

/-- Rows `r0, …, r0 + rows - 1` of a row-major matrix of width `w`, transposed: column `j` at
words `j * rows, …`. Whole `16 × 16` tiles move as tiles, the rest word by word. -/
def transposeRows (m : @& ByteArray) (w r0 rows : Nat) : ByteArray := Id.run do
  let mut out := zeroWords (w * rows)
  for rt in [:rows / 16] do
    for ct in [:w / 16] do
      out := tileStrided m ((r0 + 16 * rt) * w + 16 * ct).toUSize w.toUSize out
        (16 * ct * rows + 16 * rt).toUSize rows.toUSize
  for j in [:w] do
    let r1 := if j < 16 * (w / 16) then 16 * (rows / 16) else 0
    for r in [r1:rows] do
      out := write out (j * rows + r) (read m ((r0 + r) * w + j))
  return out

/-- Column `j` from the transposed row ranges `ps`, each `rows` rows long. -/
def gatherColumn (ps : @& Array ByteArray) (rows j : Nat) : ByteArray :=
  ps.foldl (fun out p ↦ p.copySlice (4 * (j * rows)) out out.size (4 * rows))
    (ByteArray.emptyWithCapacity (4 * (ps.size * rows)))

/-- The transpose of the `8 × 8` tile whose line `t` is words `q, …, q + 7` of `s{t}`, line `u`
stored from word `p + u * ps` of `out`. Eight lines of eight words fit the vector registers. -/
@[noinline] def tile8 (s0 s1 s2 s3 s4 s5 s6 s7 : @& ByteArray) (q : USize) (out : ByteArray)
    (p ps : USize) : ByteArray :=
  tile8_sources%

/-- `count` transposed `8 × 8` tiles of the columns `s0, …, s7`: the tile at column word `q + 8 * k`
goes to the rows of width `w` from word `p + 8 * k * w` of `out`. The columns are bound once, so
tiles do not touch their reference counts. -/
def rowsTiles (s0 s1 s2 s3 s4 s5 s6 s7 : @& ByteArray) (w : USize) :
    Nat → USize → USize → ByteArray → ByteArray
  | 0, _, _, out => out
  | count + 1, q, p, out =>
    rowsTiles s0 s1 s2 s3 s4 s5 s6 s7 w count (q + 8) (p + 8 * w)
      (tile8 s0 s1 s2 s3 s4 s5 s6 s7 q out p w)

/-- Rows `r0, …, r0 + rows - 1` of the row-major matrix with columns `cs`. Whole `8 × 8` tiles
move as tiles, a block of up to 512 rows at a time so that each block is completed in cache; the
rest moves word by word. -/
def rowsOfColumns (cs : @& Array ByteArray) (r0 rows : Nat) : ByteArray := Id.run do
  let w := cs.size
  let block := min rows 512
  let mut out := zeroWords (rows * w)
  for rb in [:rows / block] do
    for ct in [:w / 8] do
      let s (t : Nat) : ByteArray := cs.getD (8 * ct + t) .empty
      out := rowsTiles (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) w.toUSize (block / 8)
        (r0 + rb * block).toUSize (rb * block * w + 8 * ct).toUSize out
  for r in [:rows] do
    let j1 := if r < 8 * (rows / 8) then 8 * (w / 8) else 0
    for j in [j1:w] do
      out := write out (r * w + j) (read (cs.getD j .empty) (r0 + r))
  return out

/-- The coefficients of a column, scaled by `h`: its unnormalized inverse transform. -/
@[specialize]
def columnCoefficients (P : LdePlan p) (col : ByteArray) : ByteArray :=
  leafNatural p P.inverseTwiddles P.logH 0 false col

/-- Block `t` of a column's extension: the DIF-order values on coset `bitrev t` of the
coefficients `c`, scaled by `h`. -/
@[specialize]
def cosetBlock (P : LdePlan p) (c : ByteArray) (t : Nat) : ByteArray :=
  leafReversed p P.forwardTwiddles P.logH
    (mulWords p (P.cosetTables.getD (NTT.Transform.bitRevNat P.bits t) .empty) c (2 ^ P.logH))

/-- The number of row ranges the input transpose splits into. -/
def rangeCount (logRows : Nat) : Nat := 2 ^ min 4 logRows

/-- The number of output chunks per block of `2 ^ logRows` rows. -/
def chunkCount (logRows : Nat) : Nat := 2 ^ min 3 logRows

/-- The extension of the `w`-column matrix `m`, as row chunks in commitment order. Tasks
transpose row ranges of `m` into columns; each column's coefficients are one task, and each of
its coset blocks another; each output chunk transposes rows of one block as soon as that block's
columns are done. -/
@[specialize]
def cosetLde (P : LdePlan p) (w : Nat) (m : ByteArray) : Array ByteArray :=
  let R := rangeCount P.logH
  let rows := 2 ^ P.logH / R
  let pieces := Tasks.join (Tasks.spawnAll R fun k ↦ transposeRows m w (k * rows) rows)
  let coeffs := (Array.range w).map fun j ↦ pieces.bind fun ps ↦ Task.spawn fun _ ↦
    columnCoefficients P (gatherColumn ps rows j)
  let C := chunkCount P.logH
  let rows' := 2 ^ P.logH / C
  let chunks := (Array.range (2 ^ P.bits)).flatMap fun t ↦
    let block := Tasks.join (coeffs.map fun c ↦ c.bind fun c ↦ Task.spawn fun _ ↦ cosetBlock P c t)
    (Array.range C).map fun k ↦ block.bind fun cs ↦ Task.spawn fun _ ↦
      rowsOfColumns cs (k * rows') rows'
  chunks.map Task.get

/-- Row chunks joined into one row-major buffer. -/
def joinRows (chunks : Array ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) (ByteArray.emptyWithCapacity (chunks.foldl (· + ·.size) 0))

end Native

/-- `Native.cosetLde` as compiled for one modulus: an instance sets `run` to it at its concrete
`p`, where the compiler specializes the kernels. -/
class PackedCosetLde (p : ℕ) [Mont32Field p] where
  /-- The compiled extension. -/
  run : LdePlan p → Nat → ByteArray → Array ByteArray
  run_eq : run = Native.cosetLde := by rfl

/-- The extension of the `w`-column packed row-major matrix `m`, as row chunks in commitment
order, with the field's compiled kernels. -/
@[inline] def LdePlan.cosetLde [PackedCosetLde p] (P : LdePlan p) (w : Nat) (m : ByteArray) :
    Array ByteArray :=
  PackedCosetLde.run P w m


end CompPoly.CPolynomial.NTTFast.Packed
