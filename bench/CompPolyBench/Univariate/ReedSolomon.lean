/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.ReedSolomon.NTTEncode

/-!
# Reed-Solomon encoding benchmarks

The definitional encoder against the certified NTT one. `ReedSolomon.encode`
evaluates the message polynomial at every domain node by Horner, which is
`Θ(n · k)`; `ReedSolomon.nttCodeword` is the forward NTT, `Θ(n log n)`. They
are *equal*, not merely equivalent — `forwardImpl_eq_encode`
(`ReedSolomon/NTTEncode.lean:71`) — so the group digest checks the pair rather
than only cross-checking two implementations of a shared spec.

Rate one half, the FRI setting: a message of `n / 2` elements encoded to `n`.

`workUnits` is `n`, the codeword length: the number of evaluations the problem
asks for, whichever way they are produced.

The quadratic row is why the sizes stop where they do. At `n = 2^10` one
`encode` is already a millisecond; at `2^12` it is past the sample budget. So
the paired groups run at `2^8` and `2^10` and a third group carries the NTT
encoder alone at `2^14`, which is the shape `runAdditiveNttFastLargeCase`
already uses for the same reason.
-/

public section

open CompPoly

namespace CompPolyBench

/-- Time the two encoders at one size, over KoalaBear's native-word representation. -/
private def runEncodeGroup (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity)
    (withQuadratic : Bool) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let n := 2 ^ logN
  let k := n / 2
  let (values, gen) := (koalaBearArray k false).run gen
  let fastValues := koalaBearFastArray values
  let domain := CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN
  let rsDomain := ReedSolomon.nttDomainToRS domain
  let messageAt (j : Nat) : Vector KoalaBear.Fast.Field k :=
    ⟨Array.ofFn (n := k) fun i ↦ fastValues.getD ((i.1 + j) % k) 1, by simp⟩
  let messages := #[messageAt 0, messageAt 1]
  let message (i : Nat) : Vector KoalaBear.Fast.Field k := messages.getD (i % 2) (messageAt 0)
  let hk : k ≤ domain.n := by
    simp only [CPolynomial.NTT.Domain.n, k, n]
    exact Nat.div_le_self _ _
  let shape := s!"n = 2^{logN}, rate 1/2, two messages"
  let checksum (v : Vector KoalaBear.Fast.Field _) : Nat :=
    checksumArray checksumKoalaBearFast v.toArray
  let sink (v : Vector KoalaBear.Fast.Field _) : UInt64 :=
    arraySampleSink (fun x ↦ natSink (checksumKoalaBearFast x)) v.toArray
  let nttRecord ← runTimedSpec
    { name := "rs-encode-koalabear-ntt", representation := "Vector",
      method := "nttCodeword", field := "koalabear", inputShape := shape,
      digestIterations := digestPeriod 2, workUnits := n }
    preset (fun i ↦ ReedSolomon.nttCodeword domain (message i) hk) checksum
    (sink := sink)
  let records ← if withQuadratic then do
      let encodeRecord ← runTimedSpec
        { name := "rs-encode-koalabear", representation := "Vector",
          method := "encode (Horner per node)", field := "koalabear", inputShape := shape,
          digestIterations := digestPeriod 2, workUnits := n }
        preset (fun i ↦ ReedSolomon.encode rsDomain (message i)) checksum
        (sink := sink)
      pure #[encodeRecord, nttRecord]
    else pure #[nttRecord]
  pure ({ groupKey := s!"rs-encode-koalabear-l{logN}",
          title := s!"Reed-Solomon encoding, KoalaBear, n = 2^{logN}",
          records := records }, gen)

/-- Registry entries for the Reed-Solomon encoding benchmarks. -/
def reedSolomonTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"rs-encode-koalabear-l8", "Reed-Solomon encoding, KoalaBear, n = 2^8"⟩
    (runEncodeGroup 8 (by decide) true),
  BenchTask.fromGroupRunner
    ⟨"rs-encode-koalabear-l10", "Reed-Solomon encoding, KoalaBear, n = 2^10"⟩
    (runEncodeGroup 10 (by decide) true),
  BenchTask.fromGroupRunner
    ⟨"rs-encode-koalabear-l14", "Reed-Solomon encoding, KoalaBear, n = 2^14"⟩
    (runEncodeGroup 14 (by decide) false)
]

end CompPolyBench
