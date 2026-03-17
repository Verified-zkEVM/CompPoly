/-
  Simple manual benchmark for comparing NTT-based multiplication against the
  existing raw polynomial multiplication.

  Run with:

    lake env lean tests/CompPolyTests/Univariate/NTT/Benchmark.lean
-/

import CompPoly.Univariate.NTT.FastMul
import CompPoly.Fields.KoalaBear

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Benchmark

def benchLogN : Nat := 13

def benchBits : Fin (KoalaBear.twoAdicity + 1) := ⟨benchLogN, by decide⟩

def benchDomain : Domain KoalaBear.Field where
  logN := benchLogN
  omega := KoalaBear.twoAdicGenerators[benchBits]
  primitive := by
    simpa [benchLogN, benchBits] using KoalaBear.isPrimitiveRoot_twoAdicGenerator benchBits
  natCast_ne_zero := by
    change ((8192 : Nat) : KoalaBear.Field) ≠ 0
    decide

def mkPoly (n seed : Nat) : CPolynomial.Raw KoalaBear.Field :=
  Array.ofFn (fun i : Fin n => (((i.1 + 1) * seed + i.1 * i.1 + 17) : KoalaBear.Field))

def p : CPolynomial.Raw KoalaBear.Field := mkPoly 3000 60

def q : CPolynomial.Raw KoalaBear.Field := mkPoly 3000 29

def secsString (ms : Nat) : String :=
  s!"{(Float.ofNat ms) / 1000.0}"

example : FastMul.fastMulImpl benchDomain p q = p * q := by
  native_decide

#eval show IO Unit from do
  let start <- IO.monoMsNow
  let r := FastMul.fastMulImpl benchDomain p q
  let stop <- IO.monoMsNow
  let elapsed := stop - start
  IO.println s!"ntt fastMulImpl: {secsString elapsed}s ({elapsed} ms), size={r.size}"

#eval show IO Unit from do
  let start <- IO.monoMsNow
  let r := p * q
  let stop <- IO.monoMsNow
  let elapsed := stop - start
  IO.println s!"raw mul: {secsString elapsed}s ({elapsed} ms), size={r.size}"

end Benchmark
end NTT
end CPolynomial
end CompPoly
