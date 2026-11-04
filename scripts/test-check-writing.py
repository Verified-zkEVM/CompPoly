#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Tests for the advisory writing checker, `scripts/check-writing.py`."""

from __future__ import annotations

import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
# The checker import must not leave a `__pycache__` directory in `scripts/`.
sys.dont_write_bytecode = True


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


WRITING = load("check_writing", "check-writing.py")


def findings(text: str, path: str = "doc.md") -> list[str]:
    blocks = WRITING.file_blocks(path, text)
    return sorted({item.rule for item in WRITING.check_blocks(blocks)})


class WritingRuleTests(unittest.TestCase):
    def test_semicolon_excerpt_starts_before_the_semicolon(self) -> None:
        for text in ["This works; it is fine.", "; The lemma holds."]:
            with self.subTest(text=text):
                blocks = WRITING.file_blocks("page.md", text + "\n")
                excerpts = [item.excerpt for item in WRITING.check_blocks(blocks)
                            if item.rule == "U1"]
                self.assertEqual(excerpts, [text])

    def test_vocabulary_is_parsed(self) -> None:
        sample = ('# Sample vocabulary\n\n## Words to avoid\n\n'
                  '| Avoid | Use |\n|---|---|\n'
                  '| "ceremony", "e.g." | alternatives |\n'
                  '| "previously", "now", "new" | present state (rule C3) |\n'
                  '| "optimisation" | Oxford spelling (rule W8) |\n')
        with tempfile.TemporaryDirectory() as directory:
            vocabulary = Path(directory) / "vocabulary.md"
            vocabulary.write_text(sample, encoding="utf-8")
            general, history, spelling = WRITING.avoid_words(vocabulary)
        self.assertEqual(general, ["ceremony", "e.g."])
        self.assertEqual(history, ["previously"])
        self.assertEqual(spelling, ["optimisation"])

    def test_sentence_length(self) -> None:
        long_sentence = " ".join(["word"] * 26) + "."
        self.assertEqual(findings(long_sentence), ["S1"])
        self.assertEqual(findings(" ".join(["word"] * 25) + "."), [])
        self.assertEqual(findings("1. " + " ".join(["word"] * 21) + "."), ["S1"])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + "."), [])

    def test_text_in_parentheses_is_a_separate_sentence(self) -> None:
        inner = " ".join(["word"] * 40)
        self.assertEqual(findings(f"The bound holds ({inner})."), ["S1"])
        self.assertEqual(findings(f"The bound holds (see ({inner}))."), ["S1"])
        self.assertEqual(findings("The bound holds (for each code)."), [])

    def test_one_word_elements(self) -> None:
        sentence = ("The bound `Code.dist_le_of_mem (h : x ∈ C)` and $\\delta \\le 1 - \\sqrt{\\rho}$ "
                    "from [BCIKS20, Theorem 1.2] and [the page](https://example.org/a.b) hold "
                    "(for every code that this page lists) here.")
        self.assertEqual(findings(sentence), [])
        counted = WRITING.mask(sentence, collapse_parentheses=True)
        self.assertEqual(WRITING.word_count(counted), 13)

    def test_sentence_can_start_with_a_lowercase_filename(self) -> None:
        text = " ".join(["word"] * 20) + ". pr-scope.py " + " ".join(["word"] * 20) + "."
        self.assertEqual(findings(text), [])
        self.assertEqual(len(WRITING.sentences(text)), 2)

    def test_license_text_is_exempt_but_later_prose_is_checked(self) -> None:
        legal = "## Licensing\n\nEnsure these terms; do not change them.\n"
        self.assertEqual(findings(legal, "CONTRIBUTING.md"), [])
        nested = legal + "\n### Conditions\n\nWe utilize these terms.\n"
        self.assertEqual(findings(nested, "CONTRIBUTING.md"), [])
        resumed = nested + "\n## Next steps\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(resumed, "CONTRIBUTING.md"), ["W1"])
        self.assertEqual(findings("Ensure these terms; do not change them.", "LICENSE.md"), [])
        fenced = "```md\n## License\n```\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(fenced), ["W1"])

    def test_mathematical_terms_are_not_blanket_vocabulary_bans(self) -> None:
        for text in ["The following are equivalent.", "Every valid transcript has a witness.",
                     "The space is simply connected.", "This functor is essentially surjective.",
                     "Complete the pull request template."]:
            self.assertNotIn("W1", findings(text), text)

    def test_paragraph_length(self) -> None:
        self.assertEqual(findings(" ".join(["One sentence."] * 7)), ["P2"])
        self.assertEqual(findings(" ".join(["One sentence."] * 6)), [])

    def test_punctuation(self) -> None:
        self.assertEqual(findings("The code is linear; it is also cyclic."), ["U1"])
        self.assertEqual(findings("The code is linear — it is also cyclic."), ["U2"])
        self.assertEqual(findings("The Reed–Solomon code has rate 1–2 in this range."), [])
        self.assertEqual(findings("Write `a; b` in Lean."), [])

    def test_definition_separator_is_not_a_clause_join(self) -> None:
        for dash in ["—", "–", "--"]:
            for term in ["`Δ₀(u, v)`", "``Δ₀(u, v)``", "$\\delta$", "**Relative distance**"]:
                with self.subTest(dash=dash, term=term):
                    self.assertEqual(findings(f"- {term} {dash} `hammingDist u v`."), [])
        self.assertNotIn("U2", findings("- `Λ(C, δ, f)` and `Λ(C, δ)` — write `Code.Lambda C δ`."))
        self.assertEqual(findings("- `Gadget/` (§2.1) — the gadget matrix."), [])
        self.assertEqual(findings("- `EvalSplit.lean` (§4, Eq. (12)) — the matrix split."), [])

    def test_definition_description_is_still_checked(self) -> None:
        self.assertEqual(findings("- `δ` — We utilize the lemma."), ["W1"])
        self.assertEqual(findings("- `δ` — relative distance — it is bounded."), ["U2"])
        self.assertEqual(findings("- `δ` — relative distance.\n  The code is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` (§2.1) is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("| Term | Description |\n|---|---|\n| `C` is linear — it is cyclic. | Bound |"), ["U2"])

    def test_words(self) -> None:
        self.assertEqual(findings("Use a ring, e.g. the integers."), ["W7"])
        self.assertEqual(findings("We utilize the lemma."), ["W1"])
        self.assertEqual(findings("Set up the build."), ["W6"])
        self.assertEqual(findings("The word ends in a vowel."), [])
        self.assertEqual(findings("Don't run the build."), ["S5"])
        self.assertEqual(findings("The prover's message is short."), [])

    def test_verbs(self) -> None:
        self.assertEqual(findings("The lemma has changed."), ["V1"])
        self.assertEqual(findings("The verifier is rejecting the proof string."), ["V1"])
        self.assertEqual(findings("The polynomials have bounded degree."), [])
        self.assertEqual(findings("The witness is missing."), [])
        self.assertNotIn("V2", findings("Using the lemma, we bound the error."))
        self.assertEqual(findings("Folding halves the length of the word."), [])
        self.assertEqual(findings("Everything it writes, and nothing else, is ignored."), [])
        self.assertEqual(findings("Nothing in it, as far as we know, assumes odd characteristic."), [])
        self.assertEqual(findings("During a merge, the base is the merge base."), [])
        self.assertEqual(findings("The request may have failed."), [])

    def test_bare_this(self) -> None:
        self.assertEqual(findings("The bound is tight. This is the main result."), ["S7"])
        self.assertEqual(findings("The bound is tight. This lemma is the main result."), [])

    def test_history_words_apply_to_library_text_only(self) -> None:
        self.assertEqual(findings("The lemma is no longer needed.", "docs/wiki/page.md"), ["C3"])
        self.assertEqual(findings("The lemma is no longer needed.", "CompPoly/Fields/README.md"),
                         ["C3"])
        self.assertEqual(findings("-- The lemma is no longer needed.", "tests/A.lean"), ["C3"])
        self.assertEqual(findings("The lemma is no longer needed.", "body.md"), [])
        self.assertEqual(findings("The new code is now linear.", "docs/wiki/page.md"), [])

    def test_ise_spelling(self) -> None:
        self.assertEqual(findings("The optimisation loop measures ratios."), ["W8"])
        self.assertEqual(findings("Each optimisations pass is optimised."), ["W8"])
        self.assertEqual(findings("The optimization loop measures ratios."), [])
        self.assertEqual(findings("The behaviour of the loop is stable."), [])
        self.assertEqual(findings("Call `optimiseBehaviour` here."), [])

    def test_compoly_terms_are_not_flagged(self) -> None:
        for text in ["The kernel re-checks every step through `runChain`.",
                     "Nothing here is trusted.",
                     "The fast implementation is faster on every row.",
                     "Encoding a codeword is linear.",
                     "The certificate is generated by an untrusted script."]:
            self.assertEqual(findings(text), [], text)

    def test_exempt_text(self) -> None:
        text = ("Avoid \"e.g.; it's robust\" in prose.\n\n# Heading; with e.g. a dash — here\n\n"
                "```\nlet x := 1; e.g.\n```\n\n<!-- e.g.; utilize -->\n")
        self.assertEqual(findings(text), [])

    def test_table_cells_and_header(self) -> None:
        text = "| Rule; header | Use |\n|---|---|\n| One cell; two | Fine. |\n"
        self.assertEqual(findings(text), ["U1"])


class LeanExtractionTests(unittest.TestCase):
    def test_doc_comments_and_line_numbers(self) -> None:
        source = ('/-! # Title\n\nThe module; with a problem. -/\n'
                  'def f : Nat := 1 -- a trailing comment; also a problem\n'
                  'def s : String := "-- not a comment; ok"\n'
                  '/-- The definition utilizes `x; y`. -/\n'
                  'theorem t : True := trivial\n')
        blocks = WRITING.lean_blocks("A.lean", source)
        lines = {block.line: block.text for block in blocks}
        self.assertIn(3, lines)
        self.assertIn(4, lines)
        self.assertIn(6, lines)
        self.assertNotIn(5, lines)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(3, "U1"), (4, "U1"), (6, "W1")})

    def test_character_literals_do_not_start_strings(self) -> None:
        source = ("def quote : Char := '\"'\n"
                  "def escaped : Char := '\\''\n"
                  "def x' : Nat := 1\n"
                  "/-- The definition utilizes a quote. -/\n"
                  "def y : Nat := 2\n")
        blocks = WRITING.lean_blocks("A.lean", source)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(4, "W1")})


class PathTests(unittest.TestCase):
    def test_generated_files_are_not_checked_in_base_mode(self) -> None:
        for path in ["CompPoly.lean",
                     "CompPoly/Fields/KoalaBear/Ext5/QuinticCertData.lean",
                     "CompPoly/Fields/KoalaBear/Ext6/SexticCertData.lean",
                     "CompPoly/Fields/Binary/BF64/BaseCertificate.lean",
                     "CompPoly/Fields/Binary/Aes/Certificate.lean",
                     "bench/out/report-medium.md", ".lake/packages/x/README.md"]:
            self.assertFalse(WRITING.checked_path(path), path)
        for path in ["CompPoly/Fields/KoalaBear/Ext5/QuinticIrreducible.lean",
                     "docs/wiki/writing.md", "CONTRIBUTING.md", "tests/README.md"]:
            self.assertTrue(WRITING.checked_path(path), path)
        self.assertFalse(WRITING.checked_path("scripts/check-writing.py"))


class ChangedLineTests(unittest.TestCase):
    def test_only_changed_blocks_are_checked(self) -> None:
        # Keep the fixture independent of user configuration and inherited Git routing.
        git_env = {key: value for key, value in os.environ.items()
                   if not key.startswith("GIT_")}
        git_env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_SYSTEM=os.devnull,
                       GIT_CONFIG_GLOBAL=os.devnull)
        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.dict(os.environ, git_env, clear=True),
        ):
            root = Path(directory)

            def run(*args: str) -> None:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)

            run("init", "-q", "-b", "main", "--template=")
            run("config", "core.hooksPath", os.devnull)
            run("config", "commit.gpgsign", "false")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            (root / "page.md").write_text("Old text; with a semicolon.\n\nA clean line.\n")
            run("add", "page.md")
            run("commit", "-q", "-m", "base")
            run("checkout", "-q", "-b", "topic")
            (root / "page.md").write_text(
                "Old text; with a semicolon.\n\nA clean line.\n\nNew text; also bad.\n")
            (root / "untracked.md").write_text("Untracked; ignored.\n")
            with mock.patch.object(WRITING, "ROOT", root):
                blocks = WRITING.changed_blocks("main")
            self.assertEqual([block.line for block in blocks], [5])


class AdvisoryV2Tests(unittest.TestCase):
    vocabulary = """## Technical -ing nouns

| Term | Technical meaning |
|---|---|
| `encoding`, `folding`, `sampling` | Protocol constructions |
| `gas metering`, `working tree`, `dangling symlink` | Resource accounting and repository data |

## Other terms

| `making` | Outside the technical noun table |

## Words to avoid

| Avoid | Use |
|---|---|
| "utilize" | use |
| "no longer" | present fact (rule C3) |
"""

    def test_technical_ing_nouns_are_vocabulary_defined(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'vocabulary.md'
            path.write_text(self.vocabulary)
            self.assertEqual(WRITING.technical_ing_nouns(path),
                             {'encoding', 'folding', 'sampling', 'gas metering',
                              'working tree', 'dangling symlink'})

    def test_preposition_forms_do_not_trigger_a_morphology_warning(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'vocabulary.md'
            path.write_text(self.vocabulary)
            cases = ['Before making a change, run the tests.',
                     'Instead of calling the function, use the cached value.',
                     'The bound follows by assuming P.',
                     'The bound follows from sampling.',
                     'Nothing changes before folding.',
                     'The budget accounts for gas metering.',
                     'Run the tests before\nmaking a change.']
            for text in cases:
                with self.subTest(text=text):
                    found = WRITING.check_blocks(WRITING.file_blocks('page.md', text), path)
                    self.assertFalse(any(f.rule == 'V2' for f in found))

    def test_introductory_hints_use_whole_technical_phrases(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "vocabulary.md"
            path.write_text(self.vocabulary, encoding="utf-8")
            cases = [("Working tree inspection, a Git task, is complete.", False),
                     ("Working\ntree inspection, a Git task, is complete.", False),
                     ("Dangling symlink detection, a filesystem task, is complete.", False),
                     ("Working through the cases, the result follows.", True),
                     ("Working trees inspection, a distinct phrase, needs review.", True),
                     ("Assuming P, we have the bound.", False),
                     ("Writing f = g, the equality follows.", False),
                     ("Using the API, we build the result.", False),
                     ("Existing Lake targets, source linters, and documentation checks have distinct scopes.", False),
                     ("Resulting equations, after reduction, are equal.", False)]
            for text, expected in cases:
                with self.subTest(text=text):
                    found = WRITING.check_blocks(WRITING.file_blocks("page.md", text), path)
                    self.assertEqual(any(item.rule == "V2" for item in found), expected)
            # A hint or its absence does not establish grammatical correctness.

    def test_vocabulary_heading_levels_and_section_boundaries(self) -> None:
        text = self.vocabulary.replace("## Technical -ing nouns", "### TECHNICAL -ING NOUNS ###")
        text = text.replace("## Other terms", "### Other terms")
        text = text.replace("## Words to avoid", "### WORDS TO AVOID ###")
        text += '\n### Another table\n\n| "ceremony" | not part of the avoid list |\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "vocabulary.md"
            path.write_text(text, encoding="utf-8")
            self.assertIn("gas metering", WRITING.technical_ing_nouns(path))
            self.assertNotIn("making", WRITING.technical_ing_nouns(path))
            self.assertEqual(WRITING.avoid_words(path)[0], ["utilize"])

    def test_missing_required_vocabulary_section_has_a_clear_error(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "vocabulary.md"
            path.write_text("# Unconfigured vocabulary\n", encoding="utf-8")
            with mock.patch("sys.stdin", io.StringIO("Clean prose.\n")):
                with mock.patch("sys.stderr", io.StringIO()) as error:
                    with self.assertRaises(SystemExit) as result:
                        WRITING.main(["check-writing.py", "--stdin", "body", "--vocabulary", str(path)])
            self.assertEqual(result.exception.code, 2)
            self.assertIn("missing the 'Words to avoid' section", error.getvalue())



class WritingRegressionTests(unittest.TestCase):
    def test_wrapped_technical_phrases_keep_their_meaning(self) -> None:
        for text in ['The code has correlated\nagreement.',
                     'The variable has expected\nvalue zero.']:
            self.assertNotIn('V1', findings(text))


    def test_wrapped_phrasal_and_history_terms_remain_visible(self) -> None:
        self.assertIn('W6', findings('Carry\nout the test.'))
        self.assertIn('C3', findings('The lemma is no\nlonger needed.', 'docs/wiki/page.md'))


    def test_wrapped_straight_quotes_are_one_exempt_element(self) -> None:
        text = ('"essentially\nsurjective". Review their meaning. Do not delete them as '
                'isolated words. "Negligible" retains its technical meaning.')
        self.assertEqual(findings(text), [])
        text = 'The text "quoted\nwords; ignored" is literal.\nActual prose; checked.'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'U1'], [3])


    def test_findings_point_to_the_source_line(self) -> None:
        text = ('The [reference](https://example.org/a(b)) and `x` agree.\n'
                'The quoted "a; b" is code here.\n'
                'The last line; needs a conjunction.\n')
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        item = next(f for f in found if f.rule == 'U1')
        self.assertEqual(item.line, 3)
        self.assertIn('last line;', item.excerpt)
        self.assertNotIn('Code', item.excerpt)

    def test_line_numbers_in_lists_and_lean_comments(self) -> None:
        cases = [('- First line.\n  Second line; needs a conjunction.\n', 'page.md', 2),
                 ('/-! First line.\nSecond line; needs a conjunction.\n-/', 'A.lean', 2),
                 ('-- First line.\n-- Second line; needs a conjunction.\n', 'A.lean', 2)]
        for text, path, line in cases:
            with self.subTest(path=path, text=text):
                found = WRITING.check_blocks(WRITING.file_blocks(path, text))
                self.assertEqual([f.line for f in found if f.rule == 'U1'], [line])

    def test_word_findings_keep_source_spelling_and_line(self) -> None:
        text = 'A clean line with `code`.\nWe utilize the lemma.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([(f.line, f.excerpt) for f in found if f.rule == 'W1'], [(2, 'utilize')])

    def test_parenthetical_length_finding_points_inside_the_parenthesis(self) -> None:
        text = 'A short sentence (\n' + ' '.join(['word'] * 30) + ').'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'S1'], [2])

    def test_possession_is_not_a_perfect_tense(self) -> None:
        for text in ['The code has correlated agreement.', 'The graph has labelled edges.',
                     'The vector has centered norm.',
                     'The vector has squared norm.', 'The variable has expected value zero.',
                     'The tree has left and right children.', 'The polynomials have known degree.']:
            with self.subTest(text=text):
                self.assertNotIn('V1', findings(text))
        self.assertIn('V1', findings('The prover has squared the norm.'))
        self.assertIn('V1', findings('The proof has changed.'))

    def test_technical_predicates_are_not_progressive_actions(self) -> None:
        for text in ['The commitment scheme is hiding and binding.',
                     'The sequence is increasing.', 'The sequence is decreasing.',
                     'The sequence is nondecreasing.', 'The polynomial is vanishing.',
                     'The tree is accepting.', 'The composite is winning.']:
            with self.subTest(text=text):
                self.assertNotIn('V1', findings(text))
        self.assertIn('V1', findings('The verifier is rejecting the message.'))

    def test_ing_nouns_and_nonverbs_are_not_introductory_verb_clauses(self) -> None:
        for text in ['Nothing, at present.', 'Hamming distance, as defined above, is a metric.',
                     'String concatenation, as usual, is associative.',
                     'Folding is done in blocks, so the bound applies.',
                     'Batching reduces the cost, so use the bound.']:
            with self.subTest(text=text):
                self.assertNotIn('V2', findings(text))
        self.assertNotIn('V2', findings('Using the lemma, we bound the error.'))

    def test_this_way_has_an_explicit_noun(self) -> None:
        self.assertNotIn('S7', findings('This way, the prover sends one message.'))
        self.assertIn('S7', findings('This is the main result.'))

    def test_definition_separators_allow_links_and_alternatives(self) -> None:
        for term in ['[`File.lean`](path)', '`A` / `B`', '[the term](https://example.org)', '[the term](https://example.org/a(b))',
                     '`A` and [`B`](path)']:
            with self.subTest(term=term):
                self.assertNotIn('U2', findings(f'- {term} — the description.'))
                self.assertIn('U2', findings(f'- {term} — first clause — second clause.'))
        self.assertNotIn('U2', findings('| Term | Meaning |\n|---|---|\n| `A` | — |'))

    def test_latin_abbreviations_have_one_finding(self) -> None:
        for word in ['e.g.', 'i.e.', 'etc.', 'cf.', 'resp.']:
            pattern = WRITING.word_pattern([word])
            blocks = WRITING.file_blocks('page.md', f'Use {word} here.')
            found = [f for b in blocks for f in WRITING.check_block(b, pattern, None)]
            self.assertEqual([f.rule for f in found], ['W7'])

    def test_final_e_verbs_keep_ing_inflections(self) -> None:
        pattern = WRITING.word_pattern(['ensure', 'utilize', 'leverage'])
        for word in ['ensure', 'ensures', 'ensured', 'ensuring', 'utilizing', 'leveraging']:
            self.assertIsNotNone(pattern.fullmatch(word), word)
        self.assertIsNone(pattern.fullmatch('reassuring'))

    def test_fences_use_their_opening_character_and_length(self) -> None:
        for opening, inner in [('~~~~', '```'), ('````', '```'), ('~~~', '```')]:
            text = f'{opening}\n{inner}\nNot prose; ignored.\n{opening}\n\nReal prose; checked.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(6, 'U1')])

    def test_visible_prose_after_comments_and_thematic_breaks(self) -> None:
        for text in ['<!-- comment --> Visible prose; checked.',
                     '---\nVisible prose; checked.\n---', '#1431 has prose; checked.']:
            self.assertIn('U1', findings(text), text)
        self.assertEqual(findings('    Example code; ignored.\n'), [])
        self.assertEqual(findings('---\nstatus: current; metadata\n---\nClean prose.'), [])

    def test_literal_comment_markers_do_not_hide_prose(self) -> None:
        for text in ['The token `<!--` opens a comment.\nReal prose; checked.\n',
                     '```\n<!--\n```\nReal prose; checked.\n',
                     'The token `<!--` is code, as is `-->`.\nReal prose; checked.\n',
                     'The token `some\n<!--\ntext` is literal.\nReal prose; checked.\n',
                     'The text \\<!-- is literal.\nReal prose; checked.\n',
                     'The text \\<!-- literal; --> stays visible.']:
            with self.subTest(text=text):
                self.assertIn('U1', findings(text))
        text = 'A clean line.\n    A bad line; this is paragraph continuation.\n'
        self.assertIn('U1', findings(text))

    def test_indented_list_continuations_remain_prose(self) -> None:
        for text in ['- Outer item.\n\n    - Inner prose; checked.\n',
                     '1. Outer item.\n\n    1. Inner prose; checked.\n',
                     '- Outer item.\n\n    More prose; checked.\n']:
            with self.subTest(text=text):
                self.assertIn('U1', findings(text))

    def test_lean_comment_indentation_does_not_hide_prose(self) -> None:
        cases = [
            ("/--\n    Actual prose; checked.\n-/", 2),
            ("  /-\n        Actual prose; checked.\n  -/", 2),
            ("/-- First line.\n\n        Actual prose; checked.\n-/", 3),
            ("/--\n    ```lean\n    example; code\n    ```\n\n    Actual prose; checked.\n-/", 6),
        ]
        for text, line in cases:
            with self.subTest(text=text):
                found = WRITING.check_blocks(WRITING.file_blocks("A.lean", text))
                self.assertEqual([(item.line, item.rule) for item in found], [(line, "U1")])
                self.assertEqual(found[0].excerpt, "Actual prose; checked.")
        self.assertEqual(findings("    Example code; ignored.\n", "page.md"), [])

    def test_raw_lean_strings_do_not_create_comments(self) -> None:
        for value in ['r#"a " -- fake; comment"#', 'r"a\\"']:
            text = f'def s := {value}\n-- Real prose; checked.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(2, 'U1')])

    def test_escaped_newlines_in_lean_strings_keep_comment_locations(self) -> None:
        text = 'def s := "a\\\nb"\n-- Actual prose; checked.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
        self.assertEqual([(f.line, f.rule) for f in found], [(3, 'U1')])

    def test_annotation_properties_are_escaped(self) -> None:
        item = WRITING.Finding('a%,line=9::b.md', 2, 'U1', 'message', 'excerpt')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            WRITING.report([item], True, True)
        self.assertIn('file=a%25%2Cline=9%3A%3Ab.md,line=2,', output.getvalue())



class ChangedFileRegressionTests(unittest.TestCase):
    def test_generated_aes_certificate_is_skipped_in_base_mode(self) -> None:
        directory = self.root / "CompPoly/Fields/Binary/Aes"
        directory.mkdir(parents=True)
        for name in ["Certificate.lean", "Basic.lean"]:
            (directory / name).write_text("-- Prose; checked only in the maintained module.\n")
        self.git("add", ".")
        found = WRITING.check_blocks(WRITING.changed_blocks("main"))
        self.assertEqual([(item.path, item.rule) for item in found],
                         [("CompPoly/Fields/Binary/Aes/Basic.lean", "U1")])

    def setUp(self) -> None:
        super().setUp()
        environment = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
        environment.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                           GIT_CONFIG_SYSTEM=os.devnull)
        patcher = mock.patch.dict(os.environ, environment, clear=True)
        patcher.start(); self.addCleanup(patcher.stop)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        patcher = mock.patch.object(WRITING, 'ROOT', self.root)
        patcher.start(); self.addCleanup(patcher.stop)
        self.git('init', '-q', '-b', 'main', '--template=')
        self.git('config', 'user.email', 'test@example.org')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'commit.gpgsign', 'false')
        self.git('config', 'core.hooksPath', os.devnull)
        self.git('commit', '-q', '--allow-empty', '-m', 'base')
        self.git('checkout', '-q', '-b', 'topic')

    def git(self, *args: str) -> None:
        subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)

    def test_git_settings_and_quoted_paths_do_not_hide_changes(self) -> None:
        names = ['page.md', 'space name.md', 'café.md', 'quote"name.md', 'back\\slash.md',
                 'line\nbreak.md', ':(glob)nothing.md', ':(literal)foo.md', 'a[1].md', 'a*.md']
        for name in names:
            (self.root / name).write_text('Good line.\nBad line; checked.\n')
        self.git('add', '.')
        for option in ['diff.noprefix', 'diff.mnemonicPrefix', 'core.quotePath']:
            for value in ['true', 'false']:
                with self.subTest(option=option, value=value):
                    self.git('config', option, value)
                    found = WRITING.check_blocks(WRITING.changed_blocks('main'))
                    self.assertEqual({f.path for f in found if f.rule == 'U1'}, set(names))
                    self.assertEqual({f.line for f in found if f.rule == 'U1'}, {2})

    def test_inter_hunk_context_does_not_include_unchanged_prose(self) -> None:
        original = "First line.\n\nUnchanged prose; outside the changes.\n\nLast line.\n"
        (self.root / "page.md").write_text(original, encoding="utf-8")
        self.git("add", ".")
        self.git("commit", "-q", "-m", "base prose")
        self.git("branch", "-f", "main", "HEAD")
        revised = original.replace("First line.", "First changed line.").replace("Last line.", "Last changed line.")
        (self.root / "page.md").write_text(revised, encoding="utf-8")
        self.git("config", "diff.interHunkContext", "50")
        self.assertEqual(WRITING.added_lines("main"), {"page.md": {1, 5}})
        self.assertEqual(WRITING.check_blocks(WRITING.changed_blocks("main")), [])

    def test_renames_check_only_edited_prose(self) -> None:
        old, new = 'old café.md', 'new name.md'
        text = 'Existing prose; unchanged.\n\nA clean line.\n'
        (self.root/old).write_text(text)
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'main', 'HEAD')
        self.git('mv', old, new)
        (self.root/new).write_text(text + '\nNew prose; checked.\n')
        self.git('add', '.')
        found = WRITING.check_blocks(WRITING.changed_blocks('main'))
        self.assertEqual([(f.path, f.line) for f in found if f.rule == 'U1'], [(new, 5)])

    def test_non_utf8_and_unsupported_symlinks_are_advisory(self) -> None:
        (self.root / 'invalid.md').write_bytes(b'Caf\xe9; text.\n')
        (self.root / 'dangling.md').symlink_to('missing-target')
        (self.root / "directory.md").symlink_to(".", target_is_directory=True)
        (self.root / "loop.md").symlink_to("loop.md")
        (self.root / 'good.md').write_text('Actual prose; checked.\n')
        self.git('add', '.')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', '--base', 'main']), 0)
        self.assertIn('not UTF-8', output.getvalue())
        self.assertIn('symlink', output.getvalue().lower())
        self.assertEqual(output.getvalue().count("[Input]"), 4)
        self.assertIn('U1', output.getvalue())
        self.assertNotIn('No writing problems', output.getvalue())
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', str(self.root/'invalid.md')]), 0)
        self.assertIn('not UTF-8', output.getvalue())
        for name in ["directory.md", "loop.md"]:
            with self.subTest(name=name), mock.patch("sys.stdout", io.StringIO()) as output:
                self.assertEqual(WRITING.main(["check-writing.py", str(self.root / name)]), 0)
                self.assertIn("[Input]", output.getvalue())

    def test_valid_symlink_target_is_not_treated_as_changed_prose(self) -> None:
        (self.root / "target.txt").write_text("First line.\n\nTarget prose; on a later line.\n", encoding="utf-8")
        link = self.root / "alias.md"
        link.symlink_to("target.txt")
        self.git("add", ".")
        for arguments in [["--base", "main"], [str(link)]]:
            with self.subTest(arguments=arguments), mock.patch("sys.stdout", io.StringIO()) as output:
                self.assertEqual(WRITING.main(["check-writing.py", *arguments]), 0)
                self.assertIn("[Input]", output.getvalue())
                self.assertIn("Symlink source was not checked", output.getvalue())
                self.assertNotIn("[U1]", output.getvalue())
                self.assertNotIn("No writing", output.getvalue())

    def test_missing_regular_files_directories_and_permissions_are_errors(self) -> None:
        for path in [self.root / "missing.md", self.root]:
            with self.subTest(path=path), mock.patch("sys.stderr", io.StringIO()):
                with self.assertRaises(SystemExit) as result:
                    WRITING.main(["check-writing.py", str(path)])
                self.assertEqual(result.exception.code, 2)
        source = self.root / "permission.md"
        source.write_text("Clean prose.\n", encoding="utf-8")
        with mock.patch.object(Path, "read_text", side_effect=PermissionError("access denied")):
            with mock.patch("sys.stderr", io.StringIO()) as error:
                with self.assertRaises(SystemExit) as result:
                    WRITING.main(["check-writing.py", str(source)])
        self.assertEqual(result.exception.code, 2)
        self.assertIn("access denied", error.getvalue())

    def test_invalid_byte_stdin_has_an_input_diagnostic(self) -> None:
        environment = dict(os.environ, PYTHONIOENCODING='utf-8:surrogateescape')
        result = subprocess.run([sys.executable, WRITING.__file__, '--stdin', 'body'],
                                input=b'\xff\n', capture_output=True, env=environment, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b'not UTF-8', result.stdout)
        self.assertNotIn(b'No writing problems', result.stdout)

    def test_missing_base_and_broken_configuration_are_errors(self) -> None:
        with mock.patch('sys.stderr', io.StringIO()) as error:
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check-writing.py', '--base', 'missing-base'])
        self.assertEqual(result.exception.code, 2)
        self.assertIn('git failed', error.getvalue())
        with mock.patch("sys.stdin", io.StringIO("Clean prose.\n")), mock.patch('sys.stderr', io.StringIO()):
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check-writing.py', '--stdin', 'body', '--vocabulary',
                              str(self.root/'missing-vocabulary')])
        self.assertEqual(result.exception.code, 2)



if __name__ == "__main__":
    unittest.main()
