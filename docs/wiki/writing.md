# Writing Guide

This guide helps you write clear, precise, correct technical text. Its rules are advice. If a
passage is clear and correct, leave it alone, even if it does not follow a rule or the checker
reports it. Accuracy comes first, then clarity. An existing repository convention is not a reason
to keep unclear writing.

The [vocabulary](writing-vocabulary.md) records technical meanings and wording to avoid.
[CONTRIBUTING.md](../../CONTRIBUTING.md#writing) gives the contribution requirements.
The [writing workflow](write-technical-prose.md) describes how to edit a passage.

## Scope

Apply this guide when you add or revise documentation, Lean comments and docstrings, commit
messages, PR and issue descriptions, and review comments. Read the surrounding text for context.
Correct related defects that affect the passage, but keep unrelated rewrites in a separate change.

Keep formulas, identifiers, commands, source quotations, official titles, generated output, and
license terms accurate. Do not rewrite them to satisfy a prose rule. These exclusions do not cover
explanations that an author puts in quotation marks. Headings and table labels can be fragments,
but they must use clear and consistent terms.

Generated files, such as the Rabin certificate data modules, get their text from a generator.
Change the generator and regenerate the file. Do not edit the generated text by hand.
[`generated-files.md`](generated-files.md) lists these files.

## How to use STE

The guide draws on ASD-STE100 Simplified Technical English (STE), Issue 9, and adapts it freely
for CompPoly. It claims no STE conformance and does not reproduce or check the official dictionary.
Consult [ASD's official Issue 9](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf)
when a source rule or dictionary entry matters. Use the project vocabulary to clarify technical
meanings, not to decide which English words are permitted.

Technical accuracy takes priority over the rules in this guide. A rule can conflict with a term or
language pattern that is standard in cryptography research and engineering, computer science, or
mathematics. In that case, keep the standard form and apply the rules to the rest of the sentence.
A wording that is only a habit in this repository is not a standard form.

## Text types

Choose a text type from its purpose, not from its Markdown marker:

| Type | Purpose | Examples | Suggested sentence length |
|---|---|---|---|
| Procedural | Tell a reader how to do a task | Validation commands, the optimization loop, workflow steps | 20 words |
| Descriptive | Explain a result, concept, or observation | Module docstrings, design notes, PR explanations | 25 words |

A numbered list can describe results. A paragraph can contain an instruction. Use these lengths
as prompts to review a sentence, not targets that require a rewrite. Keep commands distinct from
explanations and warnings.

## Rules

The identifiers below are CompPoly labels. STE references identify a source principle, not exact
equivalence to a source rule. All the rules below are advice. A checker suggestion alone does
not require an edit. Contribution requirements remain in CONTRIBUTING.md.

### Words

- **W1.** Prefer a common, simple word with the intended meaning.
  Use an established technical term when the subject requires it. Rephrase if a replacement would
  change the meaning. (STE 1.1 to 1.4, 9.1, 9.2)
- **W2.** Use technical terms with their stated meanings and grammatical roles. Qualify a term
  when the passage could support more than one meaning, such as "kernel" or "native".
  (STE 1.5 to 1.13)
- **W3.** Use one term for one concept within a passage. Do not rotate synonyms for variety.
  Introduce a different technical meaning before you use it. (STE 1.11, 9.4)
- **W4.** Limit a multi-word noun to three words. Split a dense noun group with words such as
  "of", "for", or "on". Preserve established terms under W5. (STE 2.1, 2.2)
- **W5.** Introduce a longer technical noun in full. Then use a clear shorter name, a defined
  abbreviation, or suitable hyphenation. Do not invent an abbreviation only to shorten the text.
  (STE 2.2)
- **W6.** Replace phrasal verbs with a direct verb when the replacement preserves the meaning.
  For example, write "find" rather than "figure out". (STE 9.3)
- **W7.** Write English words instead of Latin abbreviations in prose. For example, write
  "for example" instead of "e.g.". Preserve official titles and source quotations. (STE GR-6)
- **W8.** Use Oxford spelling in prose: British spelling with "-ize" endings, such as "behaviour",
  "optimization", and "analyse". American spelling is also correct. Keep one spelling within a
  file. Preserve official names, identifiers, and quotations with a different spelling. Lean
  declaration names follow the American spelling of Mathlib. (STE 1.14, 9.4)
- **W9.** Use gender-neutral language when gender is not relevant. Use "they" for a person whose
  pronouns you do not know. (STE GR-7)

### Verbs

- **V1.** Prefer simple tenses, the imperative, and the infinitive. Avoid complex verb forms
  when a simpler construction gives the same information. Preserve time and uncertainty:
  "the build may have failed" does not mean "the build failed".
  (STE 3.1 to 3.4, CompPoly adaptation)
- **V3.** Use the active voice. Name the person, tool, kernel, or mathematical object that
  performs the action. Make clear who or what does each action. Do not invent an actor. (STE 3.6)
- **V4.** Use the passive voice in descriptive text only when the actor is unknown. A participle
  can describe a state without forming a passive construction: "the degree is bounded".
  (STE 3.3, 3.6)
- **V5.** Express an action with a verb rather than an abstract noun phrase. Write "the kernel
  checks each step", not "the kernel performs a check of each step". (STE 3.7)
- **V6.** Use "that" after "prove", "show", "assume", or "make sure" when it separates a claim
  from the preceding verb. Do not add it before an object: "prove the theorem". (STE GR-1)

### Sentences

- **S1.** Review sentences longer than the suggested length for their text type. If a split makes
  the sentence clearer, split at a logical boundary and keep its conditions and qualifications.
  The [word-count conventions](#word-count) explain the checker's estimates. (STE 5.1, 6.3)
- **S2.** Give a sentence one topic. Give a work step one instruction, except for actions that
  must occur together. (STE 4.1, 5.2)
- **S3.** Put a condition before an instruction when the reader needs it before acting.
  For example, "If `CompPoly.lean` changes, commit the regenerated file." (STE 5.4)
- **S4.** Use the imperative for work steps. Distinguish an instruction from a requirement or a
  description. Preserve the force of "must", "may", and "can" when you revise a requirement.
  (STE 5.3, CompPoly adaptation)
- **S5.** Keep the articles, subjects, and verbs that a sentence needs. Do not use contractions
  to shorten prose. (STE 4.2, 4.5)
- **S6.** Connect related sentences so the reader can follow the argument. State the connection
  rather than expecting punctuation alone to express it. (STE 4.4)
- **S7.** Give each pronoun a clear antecedent. After "this" or "these", name the object when
  the reference could be ambiguous. (STE GR-3, GR-4)
- **S8.** Put instructions in the procedure, not inside a note. Readers can skip notes. Use them
  for supporting information. (STE 5.5)

### Paragraphs and lists

- **P1.** Give each paragraph one topic. Introduce that topic before its details. (STE 6.4, 6.5)
- **P2.** Keep a paragraph to six sentences or fewer. Split it where the subject or purpose
  changes. (STE 6.6)
- **P3.** Introduce information gradually. Define unfamiliar terms and notation before using
  them in an explanation. (STE 6.1)
- **L1.** Use a vertical list when it makes steps, cases, or conditions easier to distinguish.
  A short series does not always need a list. (STE 4.3)
- **L2.** Introduce a list with a clear purpose and a colon. Each item must connect to that
  introduction. Items can complete the introductory sentence or be complete sentences. (STE 4.3)
- **L3.** Keep the grammatical form and punctuation consistent within a list. Start prose items
  with a capital letter. Preserve the case of identifiers.
  (STE 4.3, CompPoly formatting convention)
- **L4.** Number work steps when their order matters. Do not imply an order for independent
  facts. (STE 5.2)

### Punctuation and emphasis

- **U1.** Replace a prose semicolon with an appropriate sentence boundary or conjunction.
  Do not change code punctuation. (STE 8.1)
- **U2.** Avoid a dash between clauses. State the relationship in words or use two sentences.
  A dash can separate a term from its description. This rule does not restrict mathematical
  notation or ranges. (CompPoly addition, from the principle of STE 4.4)
- **U3.** Use hyphens to group related words when that grouping makes the term clearer.
  Preserve the conventional spelling of an established technical term. (STE 8.2)
- **U4.** Use parentheses for references, identifiers, abbreviations, explanations, or
  alternatives. (STE 8.3) Keep information needed for an instruction in the instruction itself.
  (CompPoly addition)
- **U5.** Use emphasis for a term, label, warning, or specific requirement. Avoid emphasis across
  an entire paragraph. (CompPoly addition)

### Word count

STE 8.4 to 8.7 defines word counting. Each of these elements counts as one word:

- A number, or a number with its unit.
- An abbreviation or an alphanumeric identifier.
- Quoted text, a title, or a label.
- A proper name.
- A hyphenated group.

Do not add hyphens or quotation marks to hide a long sentence. Text in parentheses counts as one
word in the enclosing sentence. Check the parenthetical text separately for sentence length. A list
introduction ends at its colon for word counting. Each list item counts separately.

STE 8.6 treats a formula as quoted text, so it counts as one word. CompPoly also groups an entire
Lean expression, command, URL, or citation key as one word. This local convention extends the
STE categories where quoted text or alphanumeric identifiers do not already cover the element.
Ordinary link text keeps its words.
The checker approximates these conventions. Read the actual sentence when its count is doubtful.

### Claims and source evidence

This advice helps you write claims that agree with their sources and evidence. Contribution
requirements remain in CONTRIBUTING.md:

- **C1.** State only what the code or recorded evidence establishes. Identify `sorry`
  admissions, conditional results, and checks that you did not run.
- **C2.** Preserve the strength of a claim. Keep hypotheses, quantifiers, negations, error bounds,
  and qualifications. Do not turn a possible result into an established one.
- **C3.** Describe the present library in its reference documentation. Put change history in
  commit messages, PR descriptions, and documents whose purpose is to record history. Examples
  are an audit and the optimization log in `benchmark-best-times.md`.
- **C4.** Replace internal session notes and temporary planning codes with accessible explanations
  or maintained references. A reader of the merged tree must be able to find the cited source.
- **C5.** Replace unsupported quality claims with a fact or evidence. Words such as "robust" or
  "comprehensive" do not supply that evidence. For a speed claim, give the A/B verdict and ratio.
- **C6.** Give an argument or a precise reference instead of calling a result "obvious" or
  "trivial". Established technical names such as "trivial group" stay permitted.
- **C7.** Remove repetition that adds no useful context. Repeat a condition when the reader
  needs it at the point of use.
- **C8.** Make the source of each mathematical claim traceable. Use the
  [citation standards](../../CONTRIBUTING.md#citation-standards) rather than a second citation
  policy here.
- **C9.** State trust and evidence boundaries exactly. Name the component that checks a claim,
  such as the Lean kernel, a compiled test, or the benchmark digest gate. Name what stays
  trusted. Do not call a tested or measured function "verified" unless a Lean proof connects it to
  its specification.

Rule C9 protects statements about certificates and the
[trusted code base](../../AGENTS.md#trusted-code-base-tcb-policy). "The kernel re-checks every
step" and "the generator is untrusted" are exact claims. Keep the checker, the checked object, and
the consequence of a failed check when you edit such a sentence.

### Mathematical and Lean conventions

"Let", "fix", and "suppose" can introduce mathematical notation. They do not issue a work step.
"We" can refer to the author and reader in an argument. A state such as "`C` is closed under
addition" is not an instruction or a passive action.

STE permits one word as a technical noun and as a technical verb when each use fits its category
(STE 1.5, 1.7, 1.12, 1.13). The vocabulary records the noun and verb uses separately.
STE approves "check" as a noun. CompPoly also permits "check" as a verb for evaluation of a
specified condition or test. This is a local terminology choice, not an STE dictionary approval.

Qualify words such as "kernel", "field", "instance", "native", and "reduction" when their meaning
changes between mathematics, Lean, and compiled code. The
[vocabulary](writing-vocabulary.md#terms-and-context) gives the usual qualifiers.

## Examples

These examples come from CompPoly's prose at [commit `9be21b0`](https://github.com/Verified-zkEVM/CompPoly/tree/9be21b026e43ff9b032113dc9b766d2b17fd6c3c). They show when to revise a passage and when to keep
accurate wording:

| Before | After | Reason |
|---|---|---|
| "We enthusiastically welcome contributions to CompPoly!" ([contribution guide at commit `9be21b0`](https://github.com/Verified-zkEVM/CompPoly/blob/9be21b026e43ff9b032113dc9b766d2b17fd6c3c/CONTRIBUTING.md)) | Contribute a definition, a proof, a fast implementation, a test, or a documentation change. | State the useful action (C5). |
| "Nothing here is trusted — the kernel re-checks every step through `CompPoly.RabinCert.runChain`, so incorrect data fails to compile rather than producing a false theorem." (generated certificate docstring) | Nothing here is trusted. The kernel re-checks every step through `CompPoly.RabinCert.runChain`, so incorrect data fails to compile and does not produce a false theorem. | Replace the clause-joining dash (U2). Keep the trust claim, the checker, and the consequence of a failure (C9). Make the change in the generator. |
| "A `mismatch` verdict means the candidate computes something else; it is a bug, not a measurement." ([contribution guide at commit `9be21b0`](https://github.com/Verified-zkEVM/CompPoly/blob/9be21b026e43ff9b032113dc9b766d2b17fd6c3c/CONTRIBUTING.md)) | A `mismatch` verdict means that the candidate computes a different result. The verdict shows a bug, not a measurement. | Replace the semicolon (U1). Add "that" after the verb (V6). |
| "This is stricter than a plain build." ([quickstart at commit `9be21b0`](https://github.com/Verified-zkEVM/CompPoly/blob/9be21b026e43ff9b032113dc9b766d2b17fd6c3c/docs/wiki/quickstart.md)) | `./scripts/lint-style.sh` is stricter than a plain build. | Name the antecedent of "this" (S7). |
| "This is native implementation evidence, not a proof of the compiler or a performance benchmark." (`tests/README.md`) | The smoke test gives evidence about the native implementation. It does not prove that the compiler is correct, and it is not a performance benchmark. | Name the subject (S7). Keep each limit on the evidence (C2, C9). |
| "This was observed, not hypothesized." (`docs/wiki/field-extensions.md`) | The build failure was observed, not hypothesized. | Name the subject (S7). Keep the distinction between observation and hypothesis (C1). |
| "`native_decide` is forbidden." (`AGENTS.md`) | Keep as written. | The sentence is short and keeps the requirement strength (S4). |
| "Let `f` be a monic polynomial of degree `d`." | Keep as written. | "Let" introduces notation. It is not a work step. |

Use the [writing workflow](write-technical-prose.md) to compare a mathematical rewrite with its
source. A shorter sentence is not an improvement if it changes the statement.
