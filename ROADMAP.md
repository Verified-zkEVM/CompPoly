# CompPoly Development Roadmap

## Vision

CompPoly aims to be the premier formally verified library for computable polynomial operations over finite fields, serving as the mathematical foundation for zero-knowledge circuit verification. We provide efficient, proven-correct implementations of univariate, multivariate, and multilinear polynomial arithmetic that seamlessly integrate with the Lean 4/Mathlib ecosystem.

## Current Status

CompPoly provides a solid foundation with:

- ✅ **Univariate polynomials** (`CPolynomial`): Full arithmetic operations, evaluation, division
- ✅ **Multivariate polynomials** (`CMvPolynomial`): Complete `CommSemiring` instance with `RingEquiv` to Mathlib
- ✅ **Multilinear polynomials** (`CMlPolynomial`): Dual representation (coefficient + evaluation) with efficient transforms
- ✅ **Mathematical rigor**: Proven equivalences with Mathlib's polynomial types
- ⚠️ **Gaps**: Some proof obligations (`sorry`s), missing API completeness, performance optimizations pending

## Development Phases

### Phase 1: Foundation Completion

**Goal**: Establish complete mathematical foundations and close critical gaps.

#### Priorities
1. **Complete proof obligations**
   - Prove the remaining `sorry`s and helper lemma proofs
   - Implement `nodal` and `interpolate` for Lagrange interpolation

2. **Complete ring structures**
   - Implement `Semiring`/`CommSemiring` for `CPolynomialC`
   - Enable full integration with Mathlib's ring theory

3. **API completeness (quick wins)**
   - Add `monomial` constructors for univariate and multivariate polynomials
   - Fix linter warnings and code quality issues

**Success Criteria**: Zero `sorry`s in core operations, all ring structures complete, clean build with no warnings.

---

### Phase 2: Performance & Efficiency

**Goal**: Optimize critical operations for production use in ZK verification.

#### Priorities
1. **Polynomial multiplication**
   - Implement FFT/NTT-based multiplication (O(n log n) vs current O(n²))
   - Focus on NTT for finite field arithmetic (essential for ZK)
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

### Phase 3: API Expansion

**Goal**: Complete the planned API and add essential operations for ZK circuit verification.

#### Priorities
1. **Add sparse polynomial support**
   - Add efficient representation for sparse polynomials
   - Critical for large-scale circuit verification

2. **Core API completion** (from README plans)
   - `restrictDegree`: Degree restrictions for multilinear extensions
   - `vars`: Variable set extraction
   - `aeval`, `bind₁`: Algebra evaluation and substitution
   - `algebra`, `module`: Algebra and module structures
   - `degrees`, `eval₂Hom`: Degree utilities and evaluation homomorphisms
   - `finSuccEquiv`, `optionEquivLeft`: Variable manipulation equivalences
   - `instCommRingMvPolynomial`, `isEmptyAlgEquiv`: Additional ring and algebra structures
   - `smulZeroClass`, `sumToIter`: Scalar multiplication and iteration utilities

3. **Monomial ordering**
   - Implement monomial order support (`MonomialOrder.degree`, `leadingCoeff`)
   - Useful for Gröbner basis computations and some ZK systems

**Success Criteria**: Full feature parity with planned API, all operations proven correct, API documentation for new features.

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

3. **Integration with sister ZK repository**
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

**Success Criteria**: Excellent documentation, comprehensive test coverage, smooth integration with sister ZK repositories, active community adoption.

---

## Technical Priorities Summary

### High Priority (Blocking or High Impact)
- Complete mathematical foundations (Phase 1)
- FFT/NTT implementation (Phase 2)
- Repeated squaring optimization (Phase 2)

### Medium Priority (Important for Completeness)
- Complete multilinear transform functions (Phase 2)
- `rename` operations (Phase 2)
- API expansion (Phase 3)

### Low Priority (Polish & Enhancement)
- Sparse polynomial support (Phase 3)
- Monomial ordering (Phase 3)
- Advanced optimizations (Phase 4)

## Contributing

We welcome contributions at all phases! Good starting points:

- **Phase 1**: Help close proof obligations, implement missing constructors
- **Phase 2**: Contribute performance optimizations (with proofs!)
- **Phase 3**: Implement planned API operations
- **Phase 4**: Improve documentation, add examples, write tests

See individual TODO comments in the codebase for specific tasks. All contributions should maintain the library's emphasis on formal verification and mathematical rigor.

## Success Metrics

- **Mathematical completeness**: Zero `sorry`s in core operations, all ring structures proven, formal verification of correctness properties
- **Performance**: Competitive with unverified implementations for large polynomials (target: within 2x of optimized C/Rust implementations for degree ≥ 10⁴)
- **API completeness**: Full feature parity with Mathlib's `MvPolynomial` API, plus ZK-specific extensions
- **Usability**: Complete documentation with examples, clear integration guides, beginner-friendly tutorials
- **Adoption**: Seamless integration with Verified-zkEVM ecosystem, adoption by ZK protocol implementations, community contributions
- **Research impact**: Foundation for formally verified ZK systems, potential for academic publications on verified polynomial arithmetic

---

*Last updated: January 2026*
