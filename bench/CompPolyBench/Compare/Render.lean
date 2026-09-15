/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Compare.Verdict

/-!
# Rendering an A/B Comparison

One Markdown table across every compared group, preceded by the facts a reader
needs to weigh it: how many runs each side had, the threshold, whether the
machine drifted between the sides, and a tally of verdicts.
-/

public section

namespace CompPolyBench

/-- Render thousandths as a decimal ratio, `0.954` or `12.500`. -/
def renderRatio (milli : Nat) : String :=
  let frac := toString (milli % 1000)
  toString (milli / 1000) ++ "." ++ String.ofList (List.replicate (3 - frac.length) '0') ++ frac

/-- Row label: the name, plus its digest class when the group has more than one. -/
def renderRowLabel (key : RowKey) : String :=
  if key.digestClass.isEmpty then key.name else key.name ++ " · " ++ key.digestClass

/-- Median per-iteration cost of one side, or `-` when the side lacks the row. -/
def renderSideCell : Option SideSummary → String
  | some summary => toString summary.median
  | none => "-"

/-- Per-operation cost on both sides, only where the row declares work units. -/
def renderPerUnitCell (row : RowComparison) : String :=
  if row.workUnits ≤ 1 then "-"
  else
    let cell (side : Option SideSummary) : String :=
      match side with
      | some summary => toString (summary.median / row.workUnits)
      | none => "-"
    cell row.baseline ++ " → " ++ cell row.candidate

/-- Dispersion of the invocation medians on each side. -/
def renderCompareSpread (row : RowComparison) : String :=
  let cell (side : Option SideSummary) : String :=
    match side with
    | some summary =>
        let base := renderTenthsPercent summary.spreadTenths
        let base := if summary.anyUnreplicated then base ++ " (n<5)" else base
        if summary.anySevere then base ++ " !" else base
    | none => "-"
  cell row.baseline ++ " / " ++ cell row.candidate

/-- The verdict cell; fatal verdicts and suspect flags are bold so they stand out. -/
def renderVerdict (row : RowComparison) : String :=
  let base := if row.verdict.fatal then "**" ++ row.verdict.label ++ "**" else row.verdict.label
  match row.suspect with
  | some reason => base ++ " **SUSPECT: " ++ reason ++ "**"
  | none => base

/-- Table columns; the per-unit column is included only when some row has work units. -/
def compareColumns (withPerUnit : Bool) : List (String × Bool × (RowComparison → String)) :=
  [
    ("Group", false, fun row ↦ row.key.groupKey),
    ("Row", false, fun row ↦ renderRowLabel row.key),
    ("Baseline (ps/iter)", true, fun row ↦ renderSideCell row.baseline),
    ("Candidate (ps/iter)", true, fun row ↦ renderSideCell row.candidate),
    ("Ratio", true, fun row ↦ (row.ratioMilli.map renderRatio).getD "-")
  ] ++ (if withPerUnit then [("Per unit (ps)", true, renderPerUnitCell)] else []) ++ [
    ("Spread", true, renderCompareSpread),
    ("Verdict", false, renderVerdict)
  ]

/-- Count rows with a given verdict. -/
def countVerdict (rows : Array RowComparison) (p : Verdict → Bool) : Nat :=
  (rows.filter fun row ↦ p row.verdict).size

/-- One line listing a side's files. -/
def renderFilesLine (label : String) (files : Array System.FilePath) : String :=
  let runs := if files.size == 1 then "1 run" else s!"{files.size} runs"
  s!"- {label}: {runs} — " ++
    String.intercalate ", " (files.toList.map fun path ↦ "`" ++ path.toString ++ "`")

/-- The full Markdown report. -/
def renderCompareMarkdown (report : CompareReport) : String :=
  let rows := report.rows
  let judged := countVerdict rows fun v ↦ !v.fatal
  let tally (name : String) (p : Verdict → Bool) : String := s!"{countVerdict rows p} {name}"
  let suspects := (rows.filter fun row ↦ row.suspect.isSome).size
  let unreplicatedRows := (rows.filter fun row ↦
    (row.baseline.map (·.anyUnreplicated)).getD false ||
      (row.candidate.map (·.anyUnreplicated)).getD false).size
  let driftLine :=
    if report.drift.isEmpty then
      "- Harness drift: not measured (harness groups absent on one side)"
    else
      "- Harness drift (candidate / baseline): " ++
        String.intercalate ", " (report.drift.toList.map fun line ↦
          line.label ++ " " ++ renderRatio line.ratioMilli)
  let warnings :=
    (if report.drift.any (·.warn) then
      ["- WARNING: harness drift outside ±10% (" ++
        String.intercalate ", " ((report.drift.filter (·.warn)).toList.map fun line ↦
          line.label ++ " " ++ renderRatio line.ratioMilli) ++
        "): the machine was not steady across the two sides."]
    else []) ++
    (if unreplicatedRows > 0 then
      [s!"- WARNING: {unreplicatedRows} rows have an invocation with fewer than " ++
        s!"{replicationThreshold} samples; their spread is indicative only."]
    else []) ++
    (if report.floorChecked then []
    else ["- Floor checks skipped: harness floor rows are not in the candidate files."])
  let header := [
    "# A/B Comparison",
    "",
    renderFilesLine "Baseline" report.baselineFiles,
    renderFilesLine "Candidate" report.candidateFiles,
    "- Preset: `" ++ report.preset ++ "`",
    s!"- Threshold: ±{report.options.thresholdPercent}% on the ratio of medians, plus strict " ++
      "separation (every candidate run beats every baseline run, or vice versa); " ++
      s!"separation alone is met by chance 1 in {report.separationDenominator}.",
    driftLine
  ] ++ warnings ++ [
    s!"- Rows: {judged} judged — " ++
      String.intercalate ", " [
        tally "same" (· == Verdict.same),
        tally "faster" (· == Verdict.faster),
        tally "slower" (· == Verdict.slower)] ++ "; " ++
      String.intercalate ", " [
        tally "mismatch" (fun v ↦ match v with | Verdict.mismatch _ => true | _ => false),
        tally "missing" (fun v ↦ match v with | Verdict.missing _ => true | _ => false),
        tally "unjudged" (fun v ↦ match v with | Verdict.unjudged _ => true | _ => false)] ++
      s!"; {suspects} suspect",
    ""
  ]
  let withPerUnit := rows.any fun row ↦ row.workUnits > 1
  String.intercalate "\n"
    (header ++ renderMarkdownTable (compareColumns withPerUnit) rows.toList) ++ "\n"

#guard renderRatio 954 == "0.954"
#guard renderRatio 1000 == "1.000"
#guard renderRatio 12500 == "12.500"
#guard renderRatio 7 == "0.007"

end CompPolyBench
