/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PartialLinearization
import CompPoly.LinearAlgebra.PolynomialMatrix.RowSelection

/-!
# Diagonal Modular Equations

GS-independent solution-basis interface for systems
`p * matrix = 0 mod diag(moduli)`.

The production solver follows the degree-first pattern: it solves chunked
exact-nullspace X-adic problems whose partial-linearization windows are grown
adaptively per principal coordinate, doubling only the windows of coordinates
whose shifted pivot degree has not been discovered yet.  Because a window stops
growing once its coordinate's pivot is found, the total window mass stays
within a constant factor of the true pivot-degree mass, which is at most the
modulus degree mass `sigma`.  Every round is therefore an X-adic problem with
`O(m)` chunk rows and total order `O(sigma)`, and the number of rounds is
logarithmic, preserving the `~O(m^(omega-1) * sigma)` solver target.

The chunked X-adic problems are relaxations: their orders certify exactness
only for rows whose chunk coefficients stay below the chunk size, and the
relaxed kernel module also contains uncertified rows that can crowd exact
solutions out of the adaptive rounds.  The solver therefore backs the adaptive
loop with a certified verification solve (`windowedSolutionBasisViaPMBasis`):
solutions at or above the adaptive best are dominated by the adaptive rows,
and solutions below it lie inside the certified window, whose orders rule out
uncertified rows.

Callers that only need a witness under a known degree bound pass it as
`degreeBound?`; when the adaptive best already meets the bound the certified
solve is skipped entirely, and when it does not the certified window is shrunk
to the bound.  Passing `none` requests a degree-minimal answer and always runs
the verification solve over the best-degree-shrunk window.

## References

* [Giorgi, P., Jeannerod, C.-P., and Villard, G., *On the complexity of
    polynomial matrix computations*][GJV03]
* [Storjohann, A., *Notes on computing minimal approximant bases*][Sto06]
* [Chowdhury, M. F. I., Jeannerod, C.-P., Neiger, V., Schost, E., and
    Villard, G., *Faster algorithms for multivariate interpolation with
    multiplicities and simultaneous polynomial approximations*][CJNSV15]
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Diagonal modular-equation data.  Rows of `matrix` are solution coordinates;
columns are reduced independently by `moduli`. -/
structure ModularEquation (F : Type*) [Zero F] where
  moduli : Array (CPolynomial F)
  matrix : PolynomialMatrix F

/-- Number of principal solution coordinates. -/
def ModularEquation.solutionWidth [Zero F] (equation : ModularEquation F) : Nat :=
  equation.matrix.size

/-- Number of modular columns. -/
def ModularEquation.modularWidth [Zero F] (equation : ModularEquation F) : Nat :=
  equation.moduli.size

/-- Diagonal rows `-diag(moduli)` for the exact-nullspace lift. -/
def negativeDiagonalRows (moduli : Array (CPolynomial F)) : PolynomialMatrix F :=
  ofFn moduli.size moduli.size fun i j ↦
    if i == j then -moduli.getD i 0 else 0

/-- Exact-nullspace lift `[F; -diag(M)]`. -/
def exactNullspaceLift (equation : ModularEquation F) : PolynomialMatrix F :=
  equation.matrix ++ negativeDiagonalRows equation.moduli

/-- Principal solution rows: keep the first `solutionWidth` entries of each
expanded nullspace row. -/
def principalSolutionRows (solutionWidth : Nat) (basis : PolynomialMatrix F) :
    PolynomialMatrix F :=
  basis.map fun row ↦
    (List.range solutionWidth).map (fun j ↦ rowGet row j) |>.toArray

/-- Build the X-adic exact-nullspace problem used by the modular-equation
solver. -/
def exactNullspaceProblem (equation : ModularEquation F) : XAdicProblem F :=
  { orders := linearizedOrders equation.solutionWidth equation.moduli
    matrix := exactNullspaceLift equation }

/-- Entry-aware X-adic orders for a chunked exact-nullspace lift.  A balanced
in-window solution has chunk coefficients of degree below `delta`, and the
chunked principal entries of column `b` are reduced below `deg M_b`, so
`delta + maxEntryDeg + 1` low coefficients certify that its principal product
vanishes exactly.  This is never larger than the generic
`deg M_b + delta + 1` order and is much smaller when the relation entries have
low degree. -/
def chunkedLiftOrders (delta modularWidth : Nat)
    (chunkedPrincipal : PolynomialMatrix F) : Array Nat :=
  (List.range modularWidth).map
    (fun b ↦
      let maxEntryDegree := chunkedPrincipal.foldl
        (fun acc row ↦
          let entry := rowGet row b
          if entry == 0 then acc else max acc entry.natDegree)
        0
      delta + maxEntryDegree + 1) |>.toArray

/-- Principal rows for the chunked exact-nullspace lift.  Chunk row
`(coord, offset)` stores `X^offset` times the corresponding original relation
row, reduced columnwise by the diagonal moduli.  Reducing keeps every entry of
column `b` below `deg M_b`, matching the `E * F mod M` expansion from the
design notes and keeping chunked entry degrees independent of the offsets. -/
def chunkedPrincipalRows (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F)
    (plan : PartialLinearizationPlan) : PolynomialMatrix F :=
  ofFn plan.chunks.size (MatrixWidth equation.matrix) fun i j ↦
    let chunk := plan.chunks.getD i { coord := 0, offset := 0 }
    modByMonicWith modCtx
      (shiftPolynomialX chunk.offset
        (rowGet (equation.matrix.getD chunk.coord #[]) j))
      (equation.moduli.getD j 0)

/-- Chunked exact-nullspace lift for a partial-linearization plan. -/
def chunkedExactNullspaceLift (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F)
    (plan : PartialLinearizationPlan) : PolynomialMatrix F :=
  chunkedPrincipalRows modCtx equation plan ++ negativeDiagonalRows equation.moduli

/-- Build the X-adic exact-nullspace problem after principal-coordinate chunk
expansion, with generic partial-linearization orders. -/
def chunkedExactNullspaceProblem (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F)
    (plan : PartialLinearizationPlan) : XAdicProblem F :=
  { orders := linearizedOrders equation.solutionWidth equation.moduli
    matrix := chunkedExactNullspaceLift modCtx equation plan }

/-- Build the chunked X-adic exact-nullspace problem with entry-aware orders.
The `shift` argument is kept for call-site symmetry; orders depend only on the
chunked entry degrees and the chunk size. -/
def chunkedExactNullspaceProblemForShift (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F)
    (plan : PartialLinearizationPlan) (_shift : Array Nat) : XAdicProblem F :=
  let principal := chunkedPrincipalRows modCtx equation plan
  { orders := chunkedLiftOrders plan.delta equation.modularWidth principal
    matrix := principal ++ negativeDiagonalRows equation.moduli }

/-- Shifted pivot-degree profile discovered for the principal solution
coordinates.  `none` means that the discovery pass did not see a row pivoting in
that coordinate, so partial linearization uses its conservative fallback. -/
structure PivotDegreeProfile where
  degrees : Array (Option Nat)
deriving Repr, BEq

/-- Empty shifted pivot-degree profile for a fixed principal width. -/
def emptyPivotDegreeProfile (solutionWidth : Nat) : PivotDegreeProfile :=
  { degrees := Array.replicate solutionWidth none }

/-- Insert a discovered pivot degree, keeping the smallest degree for each
principal leading position. -/
def PivotDegreeProfile.insert (profile : PivotDegreeProfile)
    (position degree : Nat) : PivotDegreeProfile :=
  let current := profile.degrees.getD position none
  let next :=
    match current with
    | none => degree
    | some old => min old degree
  { degrees := profile.degrees.setIfInBounds position (some next) }

/-- Whether the profile has discovered a pivot degree for every coordinate. -/
def PivotDegreeProfile.coversAll (profile : PivotDegreeProfile) : Bool :=
  profile.degrees.all fun degree ↦ degree.isSome

/-- Whether the profile has discovered a pivot degree for any coordinate. -/
def PivotDegreeProfile.discoveredAny (profile : PivotDegreeProfile) : Bool :=
  profile.degrees.any fun degree ↦ degree.isSome

/-- Merge the principal pivot degrees observed in `rows` into a profile. -/
def pivotDegreeProfileMergeRows (profile : PivotDegreeProfile)
    (solutionWidth : Nat) (rows : PolynomialMatrix F) (shift : Array Nat) :
    PivotDegreeProfile :=
  (List.range rows.size).foldl
    (fun profile i ↦
      let row := rows.getD i #[]
      match rowShiftedLeadingPosition? row shift, rowShiftedDegree? row shift with
      | some position, some degree =>
          if position < solutionWidth then
            profile.insert position degree
          else
            profile
      | _, _ => profile)
    profile

/-- Discover principal pivot degrees from compressed candidate rows. -/
def pivotDegreeProfileFromRows (solutionWidth : Nat)
    (rows : PolynomialMatrix F) (shift : Array Nat) :
    PivotDegreeProfile :=
  pivotDegreeProfileMergeRows (emptyPivotDegreeProfile solutionWidth)
    solutionWidth rows shift

/-- Solve a diagonal modular equation with a supplied partial-linearization plan. -/
def solutionBasisWithPlanViaPMBasis (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F)
    (equation : ModularEquation F) (shift : Array Nat)
    (plan : PartialLinearizationPlan) : PolynomialMatrix F :=
  let xadic := chunkedExactNullspaceProblemForShift modCtx equation plan shift
  let expandedShift := chunkedExactNullspaceShift plan shift
  compactNonzeroRows (compressChunkedPrincipalRows plan (pmCtx.basis xadic expandedShift))

/-- Solve once with the conservative shift-spread window.  This is a debug
entry point only: its chunk count can grow quadratically in the module width
for spread-out shifts, so the production solver uses the adaptive
window-escalation loop instead. -/
def solutionBasisViaPMBasis (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F)
    (equation : ModularEquation F) (shift : Array Nat) : PolynomialMatrix F :=
  let plan := partialLinearizationPlan equation.solutionWidth equation.modularWidth
    equation.moduli shift
  solutionBasisWithPlanViaPMBasis modCtx pmCtx equation shift plan

/-- Known-degree reconstruction pass: build the partial-linearization plan from
the discovered pivot degrees and solve the X-adic problem directly for that
profile. -/
def knownDegreeSolutionBasisViaPMBasis (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F)
    (equation : ModularEquation F) (shift : Array Nat)
    (profile : PivotDegreeProfile) : PolynomialMatrix F :=
  let plan := partialLinearizationPlanFromPivotDegrees equation.solutionWidth
    equation.modularWidth equation.moduli shift profile.degrees
  solutionBasisWithPlanViaPMBasis modCtx pmCtx equation shift plan

/-- Solve once without principal-coordinate chunking.  This is an explicit
tiny-leaf/debug entry point; the default modular-equation context does not use
it as a production fallback. -/
def unchunkedSolutionBasisViaPMBasis (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F)
    (equation : ModularEquation F) (shift : Array Nat) : PolynomialMatrix F :=
  let plan := unchunkedPartialLinearizationPlan equation.solutionWidth
    equation.modularWidth equation.moduli
  solutionBasisWithPlanViaPMBasis modCtx pmCtx equation shift plan

/-- Keep only rows that satisfy the original diagonal modular equation after
compression from the exact-nullspace / X-adic bridge. -/
def filterModularSolutionRows
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F) (rows : PolynomialMatrix F) :
    PolynomialMatrix F :=
  rows.filter fun row ↦
    if rowIsZero row then
      false
    else
      rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli

/-- Residual rows `B * F mod diag(M)` for candidate solution rows `B`. -/
def modularResidualRows
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F) (rows : PolynomialMatrix F) :
    PolynomialMatrix F :=
  modDiagonalWith modCtx equation.moduli
    (mulWith mulCtx rows equation.matrix)

/-- Shift used for polynomial combinations of compressed candidate rows.  The
degree of a coefficient multiplying row `i` is measured relative to the shifted
degree already carried by that candidate row. -/
def candidateRowShift (rows : PolynomialMatrix F) (shift : Array Nat) : Array Nat :=
  updateShiftByRows rows shift

/-- Upper bound for the adaptive search window above each coordinate's shift.
The row `e_j * lcm(moduli)` is always a solution and `deg lcm(moduli)` is at
most the modulus degree mass, so every coordinate's minimal shifted pivot
degree is within this window. -/
def pivotWindowCap [Zero F] (equation : ModularEquation F) : Nat :=
  modulusDegreeMass equation.moduli

/-- Coefficient-degree bound for the full-window fallback problem.  Any row of
the lifted module whose shifted degree does not exceed the shifted degree of an
in-window solution has plain coefficient degrees at most
`pivotWindowCap + maxShiftDegree shift`: comparing two principal coordinates
costs at most the shift spread, and `pivotWindowCap` bounds every minimal
pivot degree. -/
def fullWindowDegreeBound [Zero F] (equation : ModularEquation F)
    (shift : Array Nat) : Nat :=
  pivotWindowCap equation + maxShiftDegree shift

/-- Exact-nullspace lift with the relation entries reduced columnwise by the
moduli, so every principal entry of column `b` has degree below `deg M_b` and
the quotient coefficients of exact solutions stay below the solution degree. -/
def reducedExactNullspaceLift (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F) : PolynomialMatrix F :=
  ofFn equation.solutionWidth equation.modularWidth
    (fun i j ↦
      modByMonicWith modCtx (rowGet (equation.matrix.getD i #[]) j)
        (equation.moduli.getD j 0)) ++
    negativeDiagonalRows equation.moduli

/-- Unchunked exact-nullspace problem with orders certifying exactness across
the whole pivot window: a lifted row with principal coefficient degrees at most
`bound` and quotient coefficient degrees at most `bound + 1` produces column-`b`
products of degree below `deg M_b + bound + 2`, so vanishing to that X-adic
order forces the product to vanish exactly.  Unlike the chunked relaxation,
this problem admits no uncertified rows below the in-window solution degrees,
at the cost of an order mass larger by a factor of the module width. -/
def fullWindowExactNullspaceProblem (modCtx : CPolynomial.ModContext F)
    (equation : ModularEquation F) (bound : Nat) : XAdicProblem F :=
  { orders := equation.moduli.map fun modulus ↦ modulus.natDegree + bound + 2
    matrix := reducedExactNullspaceLift modCtx equation }

/-- Certified full-window solve: compute a minimal basis of the unchunked
exact-nullspace problem whose orders cover the entire pivot window, and keep
the principal columns.  Every returned row that pivots at or below an in-window
solution degree is an exact modular solution, so this entry point cannot lose
the solution basis to uncertified low-degree rows.  It is used as the fallback
when the chunked adaptive solver discovers nothing. -/
def fullWindowSolutionBasisViaPMBasis (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) : PolynomialMatrix F :=
  let bound := fullWindowDegreeBound equation shift
  let problem := fullWindowExactNullspaceProblem modCtx equation bound
  let expandedShift := exactNullspaceShift shift equation.modularWidth bound
  compactNonzeroRows
    (principalSolutionRows equation.solutionWidth
      (pmCtx.basis problem expandedShift))

/-- Certified verification window sized by the best exact degree already in
hand.  Solutions at or above the best adaptive degree are dominated by the
adaptive result itself, so the certified window only has to cover the degrees
strictly below it; when the adaptive loop found nothing it falls back to the
full pivot window. -/
def verificationWindowBound [Zero F] (equation : ModularEquation F)
    (shift : Array Nat) (bestDegree? : Option Nat) : Nat :=
  match bestDegree? with
  | none => fullWindowDegreeBound equation shift
  | some best => min best (pivotWindowCap equation) + maxShiftDegree shift

/-- Certified solve over an explicit coefficient-degree window: an unchunked
exact-nullspace problem whose orders certify exactness for every row dominated
by an in-window solution.  Its order mass is `sigma + s * bound` instead of
the full window's `(s + 1) * sigma`, so when the window is shrunk to a
near-minimal degree this costs about one extra cheap round. -/
def windowedSolutionBasisViaPMBasis (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (bound : Nat) : PolynomialMatrix F :=
  compactNonzeroRows
    (principalSolutionRows equation.solutionWidth
      (pmCtx.basis (fullWindowExactNullspaceProblem modCtx equation bound)
        (exactNullspaceShift shift equation.modularWidth bound)))

/-- Certified verification solve over the best-degree-shrunk window sized by
`verificationWindowBound`. -/
def verificationSolutionBasisViaPMBasis (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (bestDegree? : Option Nat) : PolynomialMatrix F :=
  windowedSolutionBasisViaPMBasis modCtx pmCtx equation shift
    (verificationWindowBound equation shift bestDegree?)

/-- Whether a caller-supplied degree bound certifies the adaptive result: the
gate passes when the best exact degree already found does not exceed the
bound, in which case any solution within the bound is dominated by the
adaptive rows up to the bound itself and the certified verification solve is
unnecessary. -/
def degreeGatePassed (degreeBound? bestDegree? : Option Nat) : Bool :=
  match degreeBound?, bestDegree? with
  | some bound, some best => best ≤ bound
  | _, _ => false

/-- Verification window for a gated solve.  With a caller-supplied degree
bound the window only has to cover solutions within the bound, so it is
`min(bound, cap) + maxShift`; without one it falls back to the best-degree
window of `verificationWindowBound`. -/
def gatedWindowBound [Zero F] (equation : ModularEquation F)
    (shift : Array Nat) (degreeBound? bestDegree? : Option Nat) : Nat :=
  match degreeBound? with
  | some bound => min bound (pivotWindowCap equation) + maxShiftDegree shift
  | none => verificationWindowBound equation shift bestDegree?

/-- The degree gate passes exactly for a bound certified by an adaptive best. -/
theorem degreeGatePassed_eq_true_iff {degreeBound? bestDegree? : Option Nat} :
    degreeGatePassed degreeBound? bestDegree? = true ↔
      ∃ bound best, degreeBound? = some bound ∧ bestDegree? = some best ∧
        best ≤ bound := by
  cases degreeBound? with
  | none => simp [degreeGatePassed]
  | some bound =>
      cases bestDegree? with
      | none => simp [degreeGatePassed]
      | some best => simp [degreeGatePassed]

/-- Pivot-degree assignment for one adaptive round: discovered coordinates use
their observed pivot degrees, undiscovered coordinates use the current
escalation window above their shift entry. -/
def adaptiveProfileDegrees (shift : Array Nat) (profile : PivotDegreeProfile)
    (budgets : Array Nat) (solutionWidth : Nat) : Array (Option Nat) :=
  (List.range solutionWidth).map
    (fun j ↦
      match profile.degrees.getD j none with
      | some degree => some degree
      | none => some (shift.getD j 0 + budgets.getD j 0)) |>.toArray

/-- Least shifted degree among accumulated solution rows. -/
def leastSolutionRowDegree? (rows : PolynomialMatrix F) (shift : Array Nat) :
    Option Nat :=
  (leastShiftedDegreeChoice? rows shift).map fun choice ↦ choice.degree

/-- A coordinate needs no wider search window once its pivot degree is
discovered, its window has reached the cap, or its window already covers every
degree below the best solution row found so far.  The last rule is what keeps
the loop from growing windows for coordinates that cannot improve the answer:
a row pivoting at `j` with shifted degree below the current best would lie
inside the already-searched window.  Improving on `best` needs a row of degree
at most `best - 1`, so the window `shift[j] + budget[j]` suffices once
`best <= shift[j] + budget[j] + 1`. -/
def coordinateSettled (profile : PivotDegreeProfile) (budgets : Array Nat)
    (cap : Nat) (bestDegree? : Option Nat) (shift : Array Nat) (j : Nat) : Bool :=
  (profile.degrees.getD j none).isSome ||
    cap ≤ budgets.getD j 0 ||
    (match bestDegree? with
      | some best => best ≤ shift.getD j 0 + budgets.getD j 0 + 1
      | none => false)

/-- Whether every principal coordinate is settled for the current windows. -/
def allCoordinatesSettled (profile : PivotDegreeProfile) (budgets : Array Nat)
    (cap : Nat) (bestDegree? : Option Nat) (shift : Array Nat)
    (solutionWidth : Nat) : Bool :=
  (List.range solutionWidth).all fun j ↦
    coordinateSettled profile budgets cap bestDegree? shift j

/-- Double the escalation windows of coordinates that are not settled, clamped
at the window cap.  Settled coordinates keep their window so the total window
mass stays within a constant factor of the useful pivot-degree mass. -/
def escalateUnsettledBudgets (profile : PivotDegreeProfile)
    (budgets : Array Nat) (cap : Nat) (bestDegree? : Option Nat)
    (shift : Array Nat) : Array Nat :=
  (List.range budgets.size).map
    (fun j ↦
      let budget := budgets.getD j 0
      if coordinateSettled profile budgets cap bestDegree? shift j then
        budget
      else
        min cap (2 * max 1 budget)) |>.toArray

/-- State carried between adaptive solution-basis rounds.  `filtered`
accumulates the exact solution rows found across all rounds. -/
structure AdaptiveSolveState (F : Type*) [Zero F] where
  profile : PivotDegreeProfile
  budgets : Array Nat
  filtered : PolynomialMatrix F
  raw : PolynomialMatrix F

/-- One adaptive round: solve the chunked exact-nullspace problem for the
current window assignment, keep the rows that satisfy the original diagonal
congruences, and merge the observed shifted pivot degrees into the profile. -/
def adaptiveSolutionRound
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (state : AdaptiveSolveState F) : AdaptiveSolveState F :=
  let degrees := adaptiveProfileDegrees shift state.profile state.budgets
    equation.solutionWidth
  let plan := partialLinearizationPlanFromPivotDegrees equation.solutionWidth
    equation.modularWidth equation.moduli shift degrees
  let rows := solutionBasisWithPlanViaPMBasis modCtx pmCtx equation shift plan
  let filtered := filterModularSolutionRows mulCtx modCtx equation rows
  { profile := pivotDegreeProfileMergeRows state.profile equation.solutionWidth
      filtered shift
    budgets := state.budgets
    filtered := state.filtered ++ filtered
    raw := rows }

/-- Fuel-bounded adaptive window-escalation loop.  Rounds stop as soon as the
caller's degree bound is already met by the best exact row found, or every
principal coordinate is settled: discovered, saturated, or unable to beat the
best solution row already in hand. -/
def adaptiveSolutionLoop
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (degreeBound? : Option Nat) (cap : Nat) :
    Nat → AdaptiveSolveState F → AdaptiveSolveState F
  | 0, state => state
  | fuel + 1, state =>
      let next := adaptiveSolutionRound mulCtx modCtx pmCtx equation shift state
      let bestDegree? := leastSolutionRowDegree? next.filtered shift
      if next.filtered.size == 0 && !next.profile.discoveredAny then
        -- Zero discovery means the chunked relaxation is dominated by
        -- uncertified rows below the solution degrees; growing the windows
        -- multiplies the round cost without producing new pivot information,
        -- so stop here and let the caller run the certified full-window
        -- fallback instead.
        next
      else if degreeGatePassed degreeBound? bestDegree? then
        -- The best exact row already meets the caller's degree bound, so the
        -- gated solver returns the accumulated candidate set as-is; further
        -- escalation rounds cannot change anything the caller observes.
        next
      else if allCoordinatesSettled next.profile next.budgets cap bestDegree? shift
          equation.solutionWidth then
        next
      else
        let escalated := escalateUnsettledBudgets next.profile next.budgets cap
          bestDegree? shift
        if escalated == next.budgets then
          next
        else
          adaptiveSolutionLoop mulCtx modCtx pmCtx equation shift degreeBound? cap
            fuel { next with budgets := escalated }

/-- Run the adaptive degree-first solver: discover the shifted pivot-degree
profile with geometrically growing per-coordinate windows, where the final
round doubles as the known-degree reconstruction for all discovered
coordinates.  The initial window is one chunk per coordinate.  A caller with
a degree bound stops the escalation as soon as the bound is met. -/
def adaptiveSolutionBasis
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (degreeBound? : Option Nat) : AdaptiveSolveState F :=
  let delta := chunkDelta equation.solutionWidth equation.moduli
  let cap := max delta (pivotWindowCap equation)
  let fuel := Nat.log2 (max 1 cap) + 2
  adaptiveSolutionLoop mulCtx modCtx pmCtx equation shift degreeBound? cap fuel
    { profile := emptyPivotDegreeProfile equation.solutionWidth
      budgets := Array.replicate equation.solutionWidth (max 1 (delta - 1))
      filtered := #[]
      raw := #[] }

/-- Discover the shifted pivot-degree profile through the adaptive solver. -/
def discoverPivotDegreeProfileViaPMBasis
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) : PivotDegreeProfile :=
  (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift none).profile

/-- One residual reconstruction pass.  If compressed rows `B` are not themselves
exact modular solutions, solve for polynomial combinations `C` such that
`C * (B * F mod M) = 0 mod M`, then return `C * B`.  The residual equation is
solved with the same adaptive solver, without a further repair recursion.

The candidate rows are first reduced to one representative per shifted leading
position.  The reduction steps are unimodular, so the generated row module is
unchanged, while the residual equation's solution width stays bounded by the
principal width instead of the raw candidate count; without this bound the
repair solve can be quadratically wider than the original equation. -/
def repairSolutionRowsViaPMBasis
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (rows : PolynomialMatrix F) : PolynomialMatrix F :=
  let reduced := compactNonzeroRows (reduceKernelLeafRowsByPivots rows shift)
  let residualEquation : ModularEquation F :=
    { moduli := equation.moduli
      matrix := modularResidualRows mulCtx modCtx equation reduced }
  let repairState := adaptiveSolutionBasis mulCtx modCtx pmCtx residualEquation
    (candidateRowShift reduced shift) none
  PolynomialMatrix.mulStrassenWith pmCtx.runtime.lowMulContext
    pmCtx.runtime.leafCutoff repairState.filtered reduced

/-- Debug helper for tiny problems that intentionally disables
principal-coordinate chunking, keeping an unchunked solve available for
inspection without letting the production context bypass partial
linearization. -/
def debugUnchunkedFilteredSolutionBasisViaPMBasis
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) : PolynomialMatrix F :=
  filterModularSolutionRows mulCtx modCtx equation
    (unchunkedSolutionBasisViaPMBasis modCtx pmCtx equation shift)

/-- Known-degree reconstruction followed by the original diagonal-equation
guard.  The reconstruction plan is built from discovered shifted pivot degrees,
solved as a chunked exact-nullspace PM-basis problem, and compressed back to the
principal solution coordinates. -/
def knownDegreeFilteredSolutionBasisViaPMBasis
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (profile : PivotDegreeProfile) : PolynomialMatrix F :=
  let rows := knownDegreeSolutionBasisViaPMBasis modCtx pmCtx equation shift profile
  let filtered := filterModularSolutionRows mulCtx modCtx equation rows
  if filtered.size == 0 then
    filterModularSolutionRows mulCtx modCtx equation
      (repairSolutionRowsViaPMBasis mulCtx modCtx pmCtx equation shift rows)
  else
    filtered

/-- Solver exposed through the modular-equation context: run the adaptive
degree-first window-escalation loop, whose final round is the known-degree
reconstruction for every discovered coordinate, then back it with a certified
verification solve.  When the caller supplies a degree bound and the best
exact degree already found meets it, the adaptive candidate set is returned
as-is: any solution within the bound is then matched by an adaptive row up to
the bound, so the certified solve adds nothing the caller can observe.
Otherwise a certified verification solve runs over the gated window —
`min(bound, cap) + maxShift` with a bound, the best-degree-shrunk window
without one — and the union of both filtered candidate sets is returned:
solutions at or above the adaptive best are dominated by the adaptive rows;
solutions strictly below it lie inside the certified window, whose orders rule
out uncertified relaxed rows — so the union always contains an exact row of
minimal shifted degree, including in the partial-masking regime where
uncertified chunked-kernel rows crowd lower exact solutions out of every
adaptive round.  The adaptive rows come first, so ties keep the adaptive
choice.  The residual repair pass remains as a guard when both candidate sets
are empty.  The filter, verification, and repair are semantic guards around
the exact-nullspace bridge; they do not call any alternate interpolation
backend. -/
def filteredSolutionBasisViaPMBasis
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (degreeBound? : Option Nat) : PolynomialMatrix F :=
  let final := adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?
  let best? := leastSolutionRowDegree? final.filtered shift
  if degreeGatePassed degreeBound? best? then
    final.filtered
  else
    let verification := filterModularSolutionRows mulCtx modCtx equation
      (windowedSolutionBasisViaPMBasis modCtx pmCtx equation shift
        (gatedWindowBound equation shift degreeBound? best?))
    let combined := final.filtered ++ verification
    if combined.size == 0 then
      filterModularSolutionRows mulCtx modCtx equation
        (repairSolutionRowsViaPMBasis mulCtx modCtx pmCtx equation shift final.raw)
    else
      combined

/-- Rows kept by the modular solution filter satisfy the modular predicate. -/
theorem rowSatisfiesModularBool_of_mem_filterModularSolutionRows
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {equation : ModularEquation F} {rows : PolynomialMatrix F}
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (filterModularSolutionRows mulCtx modCtx equation rows)) :
    rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
  rw [MatrixRows, filterModularSolutionRows] at hrow
  have hmem : row ∈ rows ∧ rowIsZero row = false ∧
      rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
    simpa using hrow
  exact hmem.2.2

/-- One adaptive round preserves modular soundness of the accumulated filtered
rows. -/
theorem adaptiveSolutionRound_filtered_sound
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F}
    {shift : Array Nat} {state : AdaptiveSolveState F}
    (hstate : ∀ row ∈ MatrixRows state.filtered,
      rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true) :
    ∀ row ∈ MatrixRows
        (adaptiveSolutionRound mulCtx modCtx pmCtx equation shift state).filtered,
      rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
  intro row hrow
  simp only [adaptiveSolutionRound, MatrixRows, Array.toList_append,
    List.mem_append] at hrow
  rcases hrow with hold | hnew
  · exact hstate row hold
  · exact rowSatisfiesModularBool_of_mem_filterModularSolutionRows hnew

/-- The adaptive escalation loop preserves modular soundness of the accumulated
filtered rows. -/
theorem adaptiveSolutionLoop_filtered_sound
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F}
    {shift : Array Nat} {degreeBound? : Option Nat} {cap : Nat} :
    ∀ (fuel : Nat) (state : AdaptiveSolveState F),
      (∀ row ∈ MatrixRows state.filtered,
        rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true) →
      ∀ row ∈ MatrixRows
          (adaptiveSolutionLoop mulCtx modCtx pmCtx equation shift degreeBound? cap
            fuel state).filtered,
        rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro state hstate row hrow
      exact hstate row hrow
  | succ fuel ih =>
      intro state hstate row hrow
      rw [adaptiveSolutionLoop] at hrow
      have hnext := adaptiveSolutionRound_filtered_sound
        (pmCtx := pmCtx) (shift := shift) (state := state) hstate
      split at hrow
      · exact hnext row hrow
      · split at hrow
        · exact hnext row hrow
        · split at hrow
          · exact hnext row hrow
          · dsimp only [] at hrow
            split at hrow
            · exact hnext row hrow
            · refine ih _ ?_ row hrow
              intro r hr
              exact hnext r hr

/-- Rows accumulated by the adaptive solver satisfy the modular predicate. -/
theorem adaptiveSolutionBasis_filtered_sound
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F}
    {shift : Array Nat} {degreeBound? : Option Nat} :
    ∀ row ∈ MatrixRows
        (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift
          degreeBound?).filtered,
      rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
  rw [adaptiveSolutionBasis]
  exact adaptiveSolutionLoop_filtered_sound _ _
    (by intro r hr; simp [MatrixRows] at hr)

/-- Every row returned by the filtered PM-basis modular solver satisfies the
original diagonal modular equation. -/
theorem filteredSolutionBasisViaPMBasis_sound
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F}
    {shift : Array Nat} {degreeBound? : Option Nat} {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows
      (filteredSolutionBasisViaPMBasis mulCtx modCtx pmCtx equation shift
        degreeBound?)) :
    rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
  simp only [filteredSolutionBasisViaPMBasis] at hrow
  split at hrow
  · exact adaptiveSolutionBasis_filtered_sound row hrow
  · split at hrow
    · exact rowSatisfiesModularBool_of_mem_filterModularSolutionRows hrow
    · rw [MatrixRows, Array.toList_append, List.mem_append] at hrow
      rcases hrow with hmem | hmem
      · exact adaptiveSolutionBasis_filtered_sound row hmem
      · exact rowSatisfiesModularBool_of_mem_filterModularSolutionRows hmem

/-- Modular-equation solution-basis context with theorem fields.

The solver takes an optional caller-supplied degree bound.  The
completeness/minimality contract is bound-relative: for any nonzero in-width
solution row of the diagonal modular equation whose shifted degree fits the
bound (vacuous for `none`), the returned basis stays inside the principal
width and contains a row whose shifted degree does not exceed the bound — the
given solution's own degree when no bound is supplied.  The contract assumes
monic moduli, a relation matrix wide enough to expose every modular column to
the executable row predicate, and a shift aligned with the principal solution
width. -/
structure ModularSolutionBasisContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  mulContext : CPolynomial.MulContext F
  modContext : CPolynomial.ModContext F
  solutionBasis : ModularEquation F → Array Nat → Option Nat → PolynomialMatrix F
  sound :
    ∀ equation shift degreeBound? row,
      row ∈ MatrixRows (solutionBasis equation shift degreeBound?) →
        rowSatisfiesModularBool mulContext modContext row equation.matrix equation.moduli = true
  complete_minimal :
    ∀ equation shift degreeBound? row rowDegree,
      (∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic) →
      equation.moduli.size ≤ MatrixWidth equation.matrix →
      shift.size = equation.solutionWidth →
      rowSatisfiesModularBool mulContext modContext row equation.matrix
          equation.moduli = true →
      rowIsZero row = false →
      row.size ≤ equation.solutionWidth →
      rowShiftedDegree? row shift = some rowDegree →
      (∀ bound, degreeBound? = some bound → rowDegree ≤ bound) →
        (∀ basisRow,
          basisRow ∈ MatrixRows (solutionBasis equation shift degreeBound?) →
            basisRow.size ≤ equation.solutionWidth) ∧
        ∃ basisRow degree,
          basisRow ∈ MatrixRows (solutionBasis equation shift degreeBound?) ∧
          rowShiftedDegree? basisRow shift = some degree ∧
          degree ≤ degreeBound?.getD rowDegree

end Approximant

end PolynomialMatrix

end CompPoly
