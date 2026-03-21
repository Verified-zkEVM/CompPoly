/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/

import CompPoly.Univariate.NTT.FastMul
import CompPoly.Fields.KoalaBear

/-!
  # Univariate Multiplication Benchmark

  Manual benchmark for comparing NTT-based multiplication against the
  existing raw polynomial multiplication across a range of operand sizes.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Benchmark

/-- Sweep of operand sizes to make the crossover point visible. -/
def benchSizes : Array Nat :=
  #[4, 8, 12, 16, 24, 32, 48, 64, 96, 128,
    192, 256, 384, 512, 768, 1024, 1536, 2048, 2560, 3000]

def bestLogN (requiredLen : Nat) : Nat :=
  Nat.clog 2 requiredLen

def bestDomainForLength? (requiredLen : Nat) : Option (Domain KoalaBear.Field) :=
  let logN := bestLogN requiredLen
  if hlogN : logN ≤ KoalaBear.twoAdicity then
    let bits : Fin (KoalaBear.twoAdicity + 1) := ⟨logN, Nat.lt_succ_of_le hlogN⟩
    some {
      logN := logN
      omega := KoalaBear.twoAdicGenerators[bits]
      primitive := by
        simpa using KoalaBear.isPrimitiveRoot_twoAdicGenerator bits
      natCast_ne_zero := by
        change (((2 ^ logN : Nat) : KoalaBear.Field) ≠ 0)
        intro hzero
        have hpow_pos : 0 < 2 ^ logN := by
          positivity
        have hpow_le : 2 ^ logN ≤ 2 ^ KoalaBear.twoAdicity := by
          exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlogN
        have hpow_lt : 2 ^ logN < KoalaBear.fieldSize := by
          have htop : 2 ^ KoalaBear.twoAdicity < KoalaBear.fieldSize := by
            native_decide
          exact lt_of_le_of_lt hpow_le htop
        have hdiv : KoalaBear.fieldSize ∣ 2 ^ logN := by
          exact (ZMod.natCast_eq_zero_iff (2 ^ logN) KoalaBear.fieldSize).mp hzero
        exact (not_le_of_gt hpow_lt) (Nat.le_of_dvd hpow_pos hdiv)
    }
  else
    none

def mkPoly (n seed : Nat) : CPolynomial.Raw KoalaBear.Field :=
  Array.ofFn (fun i : Fin n => (((i.1 + 1) * seed + i.1 * i.1 + 17) : KoalaBear.Field))

def checkSize : Nat := 512

def p : CPolynomial.Raw KoalaBear.Field := mkPoly checkSize 60

def q : CPolynomial.Raw KoalaBear.Field := mkPoly checkSize 29

def avgMsString (totalMs reps : Nat) : String :=
  s!"{(Float.ofNat totalMs) / (Float.ofNat reps)}"

def speedupString (nttMs rawMs : Nat) : String :=
  if nttMs == 0 then
    "inf"
  else
    s!"{(Float.ofNat rawMs) / (Float.ofNat nttMs)}"

def repeatsFor (n : Nat) : Nat :=
  if n ≤ 32 then 50
  else if n ≤ 128 then 20
  else if n ≤ 512 then 5
  else if n ≤ 1536 then 2
  else 1

def timeRepeated {α : Type} (reps : Nat) (f : Unit → α) : IO (Nat × α) := do
  let actualReps := max reps 1
  let start <- IO.monoMsNow
  let mut last := f ()
  for _ in [1:actualReps] do
    last := f ()
  let stop <- IO.monoMsNow
  pure (stop - start, last)

#eval show IO Unit from do
  IO.println s!"sizes tested = {benchSizes.size}"
  IO.println "size | reps | logN | domain | ntt avg ms | raw avg ms | winner | raw/ntt"
  IO.println "-----------------------------------------------------------------------"
  let mut crossover? : Option Nat := none
  for i in [0:benchSizes.size] do
    let n := benchSizes[i]!
    let reps := repeatsFor n
    let p := mkPoly n (41 + 13 * i)
    let q := mkPoly n (73 + 17 * i)
    let reqLen := Domain.requiredLength p q
    let some benchDomain := bestDomainForLength? reqLen
      | throw <| IO.userError
          s!"no KoalaBear domain supports required length {reqLen} for size {n}"
    let (nttMs, nttRes) <- timeRepeated reps (fun _ => FastMul.fastMulImpl benchDomain p q)
    let (rawMs, rawRes) <- timeRepeated reps (fun _ => p * q)
    unless nttRes = rawRes do
      throw <| IO.userError s!"benchmark mismatch at size {n}"
    let winner := if nttMs ≤ rawMs then "NTT" else "raw"
    if crossover?.isNone && nttMs ≤ rawMs then
      crossover? := some n
    IO.println
      s!"{n} | {reps} | {benchDomain.logN} | {benchDomain.n} | {avgMsString nttMs reps} | {avgMsString rawMs reps} | {winner} | {speedupString nttMs rawMs}x"
  match crossover? with
  | some n => IO.println s!"first measured crossover: NTT wins at size {n}"
  | none => IO.println "no measured crossover in this sweep"

end Benchmark
end NTT
end CPolynomial
end CompPoly
