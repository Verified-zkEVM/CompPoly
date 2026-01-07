# CompPoly Development Roadmap

## Vision

CompPoly aims to be the premier formally verified library for computable polynomial operations over finite fields, serving as the mathematical foundation for zero-knowledge circuit verification. We aim to provide efficient, proven-correct implementations of univariate, multivariate, and multilinear polynomial arithmetic that seamlessly integrate with the Lean 4/Mathlib ecosystem.

## Current Status

CompPoly provides a solid foundation with:

- ✅ **Univariate polynomials** (`CPolynomial`): Full arithmetic operations, evaluation, division
- ✅ **Multivariate polynomials** (`CMvPolynomial`): Complete `CommSemiring` instance with `RingEquiv` to Mathlib
- ✅ **Multilinear polynomials** (`CMlPolynomial`): Dual representation (coefficient + evaluation) with efficient transforms
- ✅ **Mathematical rigor**: Proven equivalences with Mathlib's polynomial types
- ⚠️ **Gaps**: Some proof obligations (`sorry`s), missing API completeness, performance optimizations pending

## V1.0 Criteria

TODO

## Development Phases

### Phase 1: Foundation Completion

**Goal**: Establish complete mathematical foundations and close critical gaps.

#### Priorities
1. **Complete proof obligations**
   - Prove the remaining `sorry`s and helper lemma proofs
   - Implement `nodal` and `interpolate` for Lagrange interpolation

2. **Complete ring structures**
   - Implement `Semiring`/`CommSemiring` for `CPolynomialC`
   - Enable full integration with Mathlib's ring theory by:
       - proving relevant isomorphisms
       - implementing remaining relevant functions and definitions

3. **API completeness**
   - Add `monomial` constructors for univariate and multivariate polynomials
   - Implement monomial order support (`MonomialOrder.degree`, `leadingCoeff`)
   - `restrictDegree`: Degree restrictions for multilinear extensions
   - `vars`: Variable set extraction
   - `aeval`, `bind₁`: Algebra evaluation and substitution
   - `algebra`, `module`: Algebra and module structures
   - `degrees`, `eval₂Hom`: Degree utilities and evaluation homomorphisms
   - `finSuccEquiv`, `optionEquivLeft`: Variable manipulation equivalences
   - `instCommRingMvPolynomial`, `isEmptyAlgEquiv`: Additional ring and algebra structures
   - `smulZeroClass`, `sumToIter`: Scalar multiplication and iteration utilities

**Success Criteria**: Zero `sorry`s in core operations, all ring structures complete, clean build with no warnings.

---

### Phase 2: Performance & Efficiency

**Goal**: Optimize critical operations for production use in ZK verification.

#### Priorities
1. **Polynomial multiplication**
   - Implement FFT/NTT-based multiplication (O(n log n) vs current O(n²))
   - Focus on NTT for finite field arithmetic
   - Maintain correctness proofs alongside optimizations

2. **Exponentiation optimization**
   - Replace repeated multiplication with repeated squaring
   - Reduce complexity from O(n) to O(log n) multiplications

3. **Evaluation optimizations**
   - Implement batch evaluation at multiple points
   - Add Horner's method where beneficial
   - Optimize for common ZK evaluation patterns

4. **Complete multilinear transform functions**
   - Complete documentation of zeta/Möbius transform formulas
   - Prove equivalence between fast and spec implementations
   - Add performance guarantees and complexity proofs

5. **Add rename operations**
   - Implement `rename` / `renameEquiv` for variable renaming
   - Critical for circuit composition and protocol flexibility

**Success Criteria**: 10-100x speedup for large polynomial operations, verified correctness, benchmarks demonstrating competitive performance with industry-standard implementations (e.g., matching or exceeding unverified libraries for polynomials of degree 10⁴-10⁶).

---

### Phase 3: Further Optimization and Integration

**Goal**: Turn CompPoly into an integration-ready, downstream-friendly library by adding interoperability layers, serialization, proof automation, and extraction compatibility.

#### Priorities 

1. **Lowering / interop with LLZK / ZKIR polynomial dialects**
	- Explore representing CompPoly structures in the MLIR pipeline
	- Evaluate tradeoffs: “fast Lean code” vs “Lean spec + lowering to fast backend”
	- Goal: enable verification of ZKIR/LLCK polynomial implementations against CompPoly semantics
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
5.	**RT/Rust extraction mapping to CompPoly + automation**
	- Define a canonical “extracted polynomial” representation that mirrors common Rust polynomial data structures (dense coeffs, sparse maps, evaluation form)
	- Build conversion theorems and rewrite rules that map extracted representations into `CPolynomial` / `CMvPolynomial` / `CMlPolynomial`
	- Provide helper tactics (or `simp`/`grind` sets) to discharge routine coercions, normalization, and extensionality goals arising from extraction
	- Establish a workflow for verifying Rust polynomial implementations against CompPoly specs (e.g. equational refinement + property tests)
	- Identify minimum requirements on Rust-side representations (normalization invariants, canonical ordering) to make proofs robust and automation-friendly
	- Produce at least one end-to-end example: extract a Rust polynomial routine, translate it to Lean, and prove it refines the CompPoly implementation

**Success criteria**: CompPoly is integration-ready—it supports canonical serialization, has strong simp/grind-based proof ergonomics, includes a validated interop pathway with LLCK/ZKIR-style representations, and demonstrates at least one end-to-end Rust extraction → Lean translation → refinement proof against CompPoly.

---

### Phase 4: Integration & Polish (Long-term - Ongoing)

**Goal**: Ensure seamless integration, excellent developer experience, and production readiness.

#### Priorities
1. **Documentation & examples**
   - Comprehensive module-level documentation
   - Usage examples for common ZK verification patterns
   - Performance characteristics guide
   - Best practices documentation

2. **Performance benchmarking suite**
   - Property-based tests for all operations
   - Performance benchmarks and regression tests
   - Edge case coverage

3. **Integration with ArkLib and other libraries**
   - Ensure all equivalences are proven and documented
   - Add conversion utilities and compatibility layers
   - Document when to use CompPoly vs Mathlib types
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
