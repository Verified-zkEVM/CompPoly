# CompPoly Development Roadmap

## Vision

CompPoly aims to be the premier formally verified library for computable polynomial operations over finite fields, serving as the mathematical foundation for zero-knowledge circuit verification. We aim to provide efficient, proven-correct implementations of univariate, multivariate, and multilinear polynomial arithmetic that seamlessly integrate with the Lean 4/Mathlib ecosystem.

## V1.0 Criteria

1. Zero `sorry`s in all shipped modules.
1. Complete core API for `CPolynomial`, `CMvPolynomial`, `CMlPolynomial`, including evaluation + interpolation + conversions.
1. At least one "fast path" implemented + proven correct (FFT/NTT multiplication OR fast multilinear transforms).
<!-- 1. Benchmarks exist for core ops and are reproducible (CI integration optional for v1.0). -->
<!-- 1. Property tests exist for core ops (eval, mul, interpolation). -->
1. Proof ergonomics baseline: common operations (add, mul, eval) mostly simp/grind-driven, documented.
1. At least one real integration example (ArkLib or RT extraction exemplar) demonstrating use as a dependency.
1. Minimal docs: README + module docs sufficient for contributors.
1. CI stability: all tests pass consistently.

## Development Phases

### Phase 1: Theoretical Foundation

**Goal**: Establish complete mathematical foundations and close critical gaps.

#### Priorities

1. **Theoretical completeness**
   - Prove all remaining `sorry`s 
   - Implement `nodal` and `interpolate` for Lagrange interpolation
   - Implement `AddCommGroup`/`Semiring`/`CommSemiring`/`Ring`/`CommRing` instances for `CPolynomialC` and `QuotientCPolynomial`
   - Prove isomorphism between `QuotientCPolynomial`, `CPolynomialC`, and Mathlib's relevant `Polynomial` types
   - Prove remaining algebraic instances for `CMvPolynomial` etc and ring isomorphisms with Mathlib's `MvPolynomial`

1. **API completenes**
   - Add `monomial` constructors for univariate and multivariate polynomials
   - Implement monomial order support (`MonomialOrder.degree`, `leadingCoeff`)
   - `degreeLT`, `degreeLE`: Bounded-degree submodules for univariate polynomials
   - `mem_degreeLT`, `mem_degreeLE`: Membership characterizations for bounded-degree polynomials
   - `degreeLTEquiv`: Linear equivalence for coefficient access
   - `restrictDegree`: Degree restrictions for multilinear extensions
   - `vars`: Variable set extraction
   - `aeval`, `bind₁`: Algebra evaluation and substitution
   - `algebra`, `module`: Algebra and module structures
   - `degrees`, `eval₂Hom`: Degree utilities and evaluation homomorphisms
   - `finSuccEquiv`, `optionEquivLeft`: Variable manipulation equivalences
   - `instCommRingMvPolynomial`, `isEmptyAlgEquiv`: Additional ring and algebra structures
   - `smulZeroClass`, `sumToIter`: Scalar multiplication and iteration utilities

1. **Further data types**
   - Basic field definitions (currently in Arklib) ported into CompPoly
      - computable field extensions with interface
   - Implement a specialized Bivariate polynomial type, e.g. as `CPolynomial (CPolynomial R)` with specialized polynomial operations (that can then be optimized)

**Success Criteria**: Zero `sorry`s in core operations, all ring structures complete, clean build with no warnings, reasonable proof ergonomics.

---

### Phase 2: Performance & Efficiency

**Goal**: Optimize critical operations for production use in ZK verification.

#### Priorities
1. **Fast field arithmetic**
   - Optimized implementations of off-the-shelf available Field instances to enable performance, including for prime and other finite fields

1. **Polynomial multiplication**
   - Implement FFT/NTT-based multiplication (O(n log n) vs current O(n²))
   - Focus on NTT for finite field arithmetic
   - Maintain correctness proofs alongside optimizations

1. **Exponentiation optimization**
   - Replace repeated multiplication with repeated squaring
   - Reduce complexity from O(n) to O(log n) multiplications

1. **Evaluation optimizations**
   - Implement batch evaluation at multiple points
   - Add Horner's method where beneficial
   - Optimize for common ZK evaluation patterns

1. **Complete multilinear transform functions**
   - Complete documentation of zeta/Möbius transform formulas
   - Prove equivalence between fast and spec implementations
   - Add performance guarantees and complexity proofs

1. **Add rename operations**
   - Implement `rename` / `renameEquiv` for variable renaming
   - Critical for circuit composition and protocol flexibility

1. **Bivariate polynomial operations**
   - Implement efficient bivariate polynomial type: `CPolynomial (CPolynomial R)` or specialized representation, with optimized operations
   - Efficient factorization algorithms for bivariate polynomials
   - Integration with existing `CMvPolynomial 2 R` with equivalence proofs
   - Critical for sum-check protocols, FRI commitments, and zkVM constraint systems

1. **Error-correcting interpolation algorithms**
   - Implement Berlekamp-Welch algorithm for Reed-Solomon decoding
   - Implement Guruswami-Sudan list-decoding algorithm
   - Proofs of correctness
   - Integration with FRI commitments and polynomial commitment schemes

**Success Criteria**: notable speedup for large polynomial operations, verified correctness, benchmarks demonstrating competitive performance with industry-standard implementations.

---

### Phase 3: Further Optimization and Integration

**Goal**: Turn CompPoly into an integration-ready, downstream-friendly library by adding interoperability layers, serialization, proof automation, and extraction compatibility.

#### Priorities 

1. **Lowering / interop with LLZK / PrimeIR polynomial dialects**
	- Explore representing CompPoly structures in the MLIR pipeline
	- Evaluate tradeoffs: “fast Lean code” vs “Lean spec + lowering to fast backend”
	- Goal: enable verification of PrimeIR/LLZK polynomial implementations against CompPoly semantics
2.	**Serialization (bytes/JSON/protocol/hashing)**
	- Define serialization format(s) for polynomial types
	- Compatibility with ArkLib protocol serialization needs
	- Consider: to/from bytes, to/from JSON, canonical encoding for hashing
<!-- 3.	**FFT-based interpolation variants (post-FFT/NTT)**
	- Implement FFT-based Lagrange interpolation when the evaluation domain is an FFT/NTT-friendly subgroup
	- Add fast barycentric interpolation for repeated interpolation queries over a fixed set of nodes
	- Provide `interpolateFFT` / `interpolateNTT` APIs that reuse precomputed twiddle factors and domain metadata
	- Prove equivalence to the spec (naive) `interpolate` implementation and document complexity (O(n log n))
	- Include edge-case handling: non-power-of-two domains, zero-padding strategies, and domain mismatch errors -->
4.	**Proof ergonomics: simp/grind sets + tactics**
	- Identify rewrite bottlenecks when porting Mathlib poly proofs → CompPoly
	- Build simp sets and grind sets for common operations
	- Goal: “one-liner conversions” (or near) between spec polynomials and computable polynomials

6.	**Integration with ArkLib / Hax + Rust libraries (e.g. plonky3)**
	- Make CompPoly the canonical polynomial backend for ArkLib specs where applicable
	- Add bridging lemmas and conversion utilities across representations (CompPoly ↔ Mathlib ↔ extracted Rust ↔ downstream libs)
	- Document and implement invariants required for robust interop (canonical ordering, normalization, domain metadata)
	- Ensure hax-extracted Rust polynomial structures can be mapped into CompPoly with minimal proof overhead
	- Validate the integration with at least one downstream example (e.g. ArkLib protocol component or plonky3 polynomial routine)

**Success criteria**: CompPoly is integration-ready—it supports canonical serialization, has strong simp/grind-based proof ergonomics, includes a validated interop pathway with LLZK/PrimeIR-style representations, and demonstrates at least one end-to-end Rust extraction → Lean translation → refinement proof against CompPoly.

---

### Phase 4: Integration & Polish

**Goal**: Ensure seamless integration, excellent developer experience, and production readiness.

#### Priorities
1. **Documentation & examples**
   - Comprehensive module-level documentation
   - Usage examples for common ZK verification patterns
   - Performance characteristics guide
   - Best practices documentation

2. **Performance benchmarking suite**
   - Property-based tests/proofs of correctness for all operations
   - Performance benchmarks and regression tests
   - Edge case coverage

3. **Integration with ArkLib and other libraries**
   - Ensure all equivalences are proven and documented
   - Add conversion utilities and compatibility layers
   - Seamless integration with Verified-zkEVM ecosystem

4. **Developer experience & community**
   - Consistent API design patterns
   - Helpful error messages
   - Type aliases for common use cases
   - Advanced optimizations based on usage patterns
   - Community feedback and refinements

**Success Criteria**: Excellent documentation, comprehensive test coverage, smooth integration with Arklib, active community adoption, etc.

---

## Success Metrics

- **Mathematical completeness**: Zero `sorry`s in core operations, all ring structures proven, formal verification of correctness properties
- **Performance**: Competitive with unverified implementations for large polynomials (target: within 2x of optimized C/Rust implementations for degree ≥ 10⁴)
- **API completeness**: Full feature parity with Mathlib's `Polynomial` and `MvPolynomial` APIs, plus ZK-specific extensions
- **Usability**: Complete documentation with examples, clear integration guides, beginner-friendly tutorials
- **Adoption**: Seamless integration with Verified-zkEVM ecosystem, adoption by ZK protocol implementations, community contributions
- **Research impact**: Foundation for formally verified ZK systems, potential for academic publications on verified polynomial arithmetic

---

*Last updated: January 2026*
