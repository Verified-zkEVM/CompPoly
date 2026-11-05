# Writing Vocabulary

Use this page with the [writing guide](writing.md) to clarify technical meanings and review wording.
Its entries are advice, not a list of every permitted English word or an STE dictionary check.

## How to add a term

1. Find the concept in Mathlib, the Lean documentation, or its mathematical source.
2. Prefer the established term over a local synonym.
3. Record the intended meaning and grammatical role when the word can cause ambiguity.
4. Use a qualifier when two technical meanings occur in the same passage.
5. Add a missing term or meaning when the contribution first needs it.

A noun and a verb need separate technical uses, even when they have the same spelling. Listing
"check" as a noun does not approve every verb use of that word. A category example is not a reason
to reject another established term from that field.

## Terms and context

These distinctions help a reader identify the intended concept. They do not prohibit the ordinary
meaning of a word in a different context:

| Term | Technical use | Clarify when necessary |
|---|---|---|
| admission | A `sorry` on which a declaration depends | Distinguish an admitted result from a proved result. The axiom sweep reports admissions as `sorryAx` taint. |
| axiom-clean | A declaration that depends only on `propext`, `Classical.choice`, and `Quot.sound` | Name the check that established it, such as `lake exe axiomsweep --check` or `#print axioms`. |
| bound | A numerical or order constraint, as a noun | As a technical verb, state which quantity it bounds. |
| carrier | The Lean type that stores the elements of a field or ring, such as `ZMod p` or `Native32.FastField` | Say "fast carrier" or "specification carrier" when two carriers of the same field occur. |
| certificate | Data that a Lean checker re-checks to establish a property, such as a Rabin irreducibility certificate or a Pratt primality certificate | Name the property and the checker. A certificate is not trusted. A generated certificate is not a proof until the kernel checks it. |
| certified | A value or instance that carries a Lean proof of a named property, such as a certified cardinality | Name the property. Do not use "certified" for a tested value. |
| check | A test or condition, as a noun | As a verb, it means to evaluate a specified condition or test. CompPoly permits this use as a local terminology choice, not an STE dictionary approval. Say "the kernel checks" or "CI checks" to name the actor. |
| code | Source code, or an error-correcting code such as a Reed–Solomon code | Use "source code" or "implementation" when both meanings occur. |
| complete, completeness | The property that an algorithm returns every solution, as in a kernel basis, or the completeness of a decoder | Ordinary uses such as "complete the template" stay permitted. Name the property in a correctness statement. |
| computable | A Lean definition that the compiler can generate code for, that is, one not marked `noncomputable` | Distinguish "computable" from "fast" and from "verified". The library name "computable polynomials" refers to `CPolynomial` and related types. |
| digest | A `Nat` value that the benchmark validation pass folds over the outputs of a group | Agreeing digests are evidence that implementations agree on the benchmark inputs. They are not a proof. A mismatch shows that two implementations disagree. |
| extension | A field extension, such as `Ext P` for `F[X]/f` | Say "field extension", "extensionality lemma", or "file extension" when the context is ambiguous. |
| fast implementation | A definition that computes the same function as a specification definition, with a proof of equality | Name the refinement theorem, such as a `@[csimp]` lemma or an `_eq_` theorem. |
| field | An algebraic field, or a member of a Lean structure | Write "structure field" when the distinction matters. |
| instance | A typeclass instance, or a mathematical problem instance | Qualify the typeclass or problem when both occur. |
| kernel | The Lean kernel, the kernel (null space) of a matrix, or a performance-critical routine | Write "Lean kernel", "kernel of the matrix" or "null space", and "arithmetic kernel" or "fast kernel" when more than one meaning occurs. |
| module | A Lean module, or an algebraic module | Write "Lean module" or "module over `R`" when the distinction matters. |
| Montgomery residue | A stored value `a·R mod p` that represents the field element `a` | Distinguish the stored residue from the canonical value that `toNat` or serialization produces. |
| native | Compiled machine code, as in `CompPolyNativeSmoke`. Machine-word arithmetic, as in `Native32`. Compiler trust, as in `native_decide`. | Always qualify: "native code", "native-word arithmetic", or "native-compiler trust". The TCB policy forbids native-compiler trust. |
| proof | A Lean proof or a mathematical proof | Name the kind of proof before comparing the two. A certificate or a test is not a proof. |
| reduction | Modular reduction, Montgomery reduction, row reduction of a matrix, or kernel evaluation of a term | Write "modular reduction", "row reduction", or "kernel reduction" when the context is ambiguous. |
| sound, soundness | The property that every output, or every accepted input, satisfies a stated specification | Name the property and its hypotheses, such as "every returned vector solves the system". Ordinary prose can use "correct" for an argument. |
| specification | The mathematically clear definition that a fast implementation must equal | Use "specification" or "spec definition" consistently in a passage. |
| trusted, trusted code base (TCB) | A component whose correctness a result assumes without a Lean proof | For proofs, the TCB is the Lean kernel with the standard axioms, and it excludes the compiler. Call a generator "untrusted" when the kernel re-checks its output. |
| valid, validate | Satisfaction of a specified predicate, or the benchmark `--validate-only` digest check | Define or name the predicate. A validated benchmark group has agreeing digests. It is not a proved result. |
| verify, verified | A formal-verification result: a Lean proof that connects a definition to its specification | Use "check" or "test" for routine repository tests and compiled examples. |

## Technical nouns

These examples identify relevant subject fields. Preserve established terms and their spellings.
Introduce a longer or unfamiliar term before using an abbreviation:

| Field | Examples |
|---|---|
| Algebra | field, ring, module, polynomial, coefficient, degree, monic polynomial, modulus, irreducible polynomial, quotient ring, root of unity, coset |
| Representations | `CPolynomial`, `CMvPolynomial`, `CMlPolynomial`, dense representation, sparse representation, coefficient form, evaluation form, Boolean hypercube, Lagrange basis |
| Fields | prime field, extension field, binary field, tower field, carrier, Montgomery residue, limb, characteristic, GHASH |
| Transforms | NTT, additive NTT, butterfly, twiddle factor, novel polynomial basis, subspace polynomial |
| Coding theory | Reed–Solomon code, codeword, unique decoding, list decoding, Guruswami–Sudan decoder, error locator, Hamming distance |
| Linear algebra | matrix, polynomial matrix, row reduction, reduced row echelon form, kernel basis, approximant basis |
| Certificates and trust | certificate, Rabin certificate, Pratt certificate, checker, generator, trusted code base, axiom, admission, taint, axiom baseline |
| Serialization | codec, byte encoding, round trip, framing, canonical value |
| Lean | declaration, theorem, lemma, hypothesis, docstring, namespace, typeclass, instance, tactic, elaboration, Lean kernel, `@[csimp]` lemma, refinement theorem, code generation |
| Benchmarks | benchmark group, preset, digest, verdict, ratio, frozen baseline, candidate, harness drift, reference machine |
| Repository tools | branch, commit, pull request, build, linter, CI, workflow, stack |

## Technical verbs

Use these verbs for the stated subject-field actions. Keep a verb's meaning consistent within a
passage. Explain the operation or name the relevant declaration when its meaning is not clear:

| Field | Examples of actions |
|---|---|
| Mathematics | prove a claim, define an object, assume a hypothesis, bound a quantity, evaluate a polynomial, interpolate values, factor a polynomial |
| Arithmetic | multiply, square, invert an element, reduce modulo `f`, convert to or from Montgomery form |
| Coding and serialization | encode a message, decode a word, serialize a value, deserialize bytes |
| Certificates | generate certificate data, regenerate a file, check a certificate, certify a modulus |
| Lean | instantiate a variable, specialize a theorem, unfold a definition, rewrite an expression, elaborate a term, compile a module |
| Benchmarks | measure a group, freeze a baseline, compare two binaries, validate digests |
| Repository tools | build a target, run a linter, regenerate `CompPoly.lean`, rebase a branch, merge a PR, review a contribution |

## Words to avoid

This table gives prompts for an editing pass over ordinary prose. It does not define STE word
approval. Use a replacement only when it preserves the meaning and grammatical role. Rewrite the
sentence when a direct replacement does not work:

| Avoid | Use |
|---|---|
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that, or name the condition and the action |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some", if the quantity is not specified |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t.", "wlog" | compare, explicit pairings, with respect to, without loss of generality |
| "respectively" | explicit pairings when the reference would otherwise be unclear |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial", "blazing" | the measurement or the reason |
| "clearly", "obviously", "trivially", "basically" | the reason, or delete the word |
| "it is worth noting that", "it is important to" | delete the phrase when it adds no information |
| "optimisation", "optimise", "optimising", "specialisation", "specialise", "initialisation" | the "-ize" spelling, such as "optimization" (rule W8) |
| "now", "no longer", "previously", "formerly", "currently", "new" | in library reference text, the fact about the present state (rule C3) |

"The following are equivalent" is a permitted mathematical introduction. Words such as "simply"
and "essentially" can occur in technical terms, including "simply connected" and "essentially
surjective". Read their meaning rather than deleting them as isolated words. "Fast" is a
CompPoly term for a fast implementation. A claim that one implementation is faster than another
needs an A/B verdict.
