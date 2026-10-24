# EFMW–Rule30

[![Verify](https://github.com/enuminous/EFMW-Rule30/actions/workflows/verify.yml/badge.svg)](https://github.com/enuminous/EFMW-Rule30/actions/workflows/verify.yml)

Reproducible EFMW-inspired Rule 30 proof research: exact residual identities,
a verified obstruction to one local-score proof method, finite searches, and
explicitly unresolved uniform proof obligations.

**This repository does not contain a solution to Rule 30 Prize Problem 1.**
The green verification badge, when present, certifies the checks below; it does
not certify a prize solution. The full-goal checker is required to reject this
partial attempt.

## Build and check

Install Python 3 and Lean/Lake using the pinned `lean-toolchain`, then run:

```sh
python3 -m pip install -r requirements.txt
python3 verify.py
lake build
python3 check_formal.py --kit .lake/packages/rule30prize --output-dir run-results
```

`lake-manifest.json` pins the official Rule 30 definitions to the same commit
used for the recorded attempt. The dependency is the kit's lightweight core;
Mathlib is not required. CI reruns the Python controls, builds the Lean modules,
replays their theorems through the official checker, and verifies that a claim
of a complete Problem 1 solution is rejected. New CI evidence is uploaded as a
workflow artifact. The root JSON and log files preserve the October 24 run.

The longer solver campaigns are available through **Actions → Verify → Run
workflow → run_search**, or through the commands in the reproduction section.
Timeouts must be reported as unknown.

## Research record: proof attempt 3

**October 24, 2026. Prepared for Matthew Chenoweth Wright.**

**Outcome: the period-two theorem and Prize Problem 1 remain unresolved.**
This attempt produced a checked obstruction to one proposed proof method, exact
residual identities, and finite constraint-solver exclusions. It produced no
proof that every finite configuration escapes alternation, no counterexample
to that conjecture, and no demonstrated EFMW advantage over established methods.

## 1. Frozen targets and evidence levels

Rule 30 is the infinite-line binary evolution

`x(t+1,i) = x(t,i-1) XOR (x(t,i) OR x(t,i+1))`.

The main attempted subproblem was:

> Every finitely supported initial configuration eventually differs at the
> center from the black-first sequence `101010...`.

Write `Supported(R,x)` for `x(i)=0` outside `[-R,R]`. The statement is
`forall R,x, Supported(R,x) -> exists t, x(t,0) != (t even)`.
It suffices to consider the black-first phase of a nonconstant period-two tail.
A finite-support theorem would apply to any restart time of the single-cell
orbit, because each restart row is finite. It would still leave other periods
of Prize Problem 1 open.

The quantitative candidate carried forward unchanged from v2 was:

> `LinearEscape`: the first mismatch occurs by time `2R+2`.

No physical EFMW premise, residual-decay assumption, or aperiodicity assumption
was used. `LinearEscape` and `UniformEscape` are definitions of OPEN propositions
in the Lean source, not axioms or established theorems.

| Claim | Evidence | Status |
|---|---|---|
| Exact Boolean residual dynamics and masking | Lean compilation and kernel replay | Demonstrated algebraic identities; novelty not claimed |
| A nonnegative local block-count score need not strictly decrease through an alternating two-step | Explicit finite row, independent simulation, Lean kernel replay | Demonstrated obstruction to that specific proof method |
| Radius-40 configurations all break black-first alternation by time 82 | Z3 UNSAT, encoding cross-checks | Solver-supported finite exclusion; not a Lean certificate |
| Linear escape for every radius | Selected finite cases only | Unresolved conjecture |
| Escape for every finitely supported row | No uniform argument | Unresolved |
| Single-cell center never eventually repeats | No full proof | Unresolved |

## 2. Exact residual derivation and the gap

For a positive lag `p`, define

`d_p(t,i) = x(t+p,i) XOR x(t,i)`.

At a fixed time, write `a=x(i-1)`, `b=x(i)`, `c=x(i+1)` and corresponding
differences `da,db,dc`. Direct Boolean algebra gives:

```
new difference = da XOR ((NOT c) AND db)
                    XOR ((NOT b) AND dc)
                    XOR (db AND dc).
```

`local_difference` verifies this identity in Lean. If the center matches across
the lag, `db=0`, then

`d_p(t+1,i) = d_p(t,i-1) XOR ((NOT x(t,i)) AND d_p(t,i+1))`.

If the center also matches at the next time, the exact balance is

`d_p(t,i-1) = (NOT x(t,i)) AND d_p(t,i+1)`.

Thus a black center forces the left residual to zero but places no constraint
on the right residual in this equation. A white center equates the two
neighboring residuals. This is the masking gap; the identity alone does not
propagate equality to both neighbors or force a mismatch at the center.

For the actual single-cell orbit, `seed_residual_edge` proves the uniform fact
`d_p(t,-(t+p))=1` for every `p>0` and `t`. The expanding left edge supplies a
global residual forever. The required prize statement concerns position zero;
this moving-edge fact does not supply it.

The conditional theorems `uniform_of_linear`,
`no_black_first_alternating_tail_of_uniform`, and
`no_black_first_alternating_tail_of_linear` expose the missing premise rather
than concealing it. They do NOT prove either escape proposition.

## 3. A proof strategy that fails: nonnegative local block scores

I tested whether a score built from counts of short spatial patterns could
strictly decrease at every two-step transition with center trace `101`.
Such a score, if nonnegative and strictly decreasing forever, would provide a
termination argument. The proposed score family was defined before its
counterexample search:

`E_k(x) = sum over nonzero k-bit patterns p of w_p * count_p(x)`, with `w_p>=0`.

Counts include every window intersecting the finite support, with the true
infinite white background. The all-zero pattern is omitted because it has
infinitely many occurrences. Weights are translation invariant and fixed.

**Counterexample:** start with black cells exactly at positions `{-1,0,2,3}`.
Its packed row is `108` in coordinates `[-3,3]`. Two exact Rule 30 steps give
packed row `1772` in coordinates `[-5,5]`.

* The center is `1,0,1` at times `0,1,2`.
* For every block length `1 <= k <= 6`, every nonzero pattern occurs at least
  as often after the two steps as before them.
* Consequently **no fixed nonnegative weighting of those pattern counts can
  strictly decrease on this transition**. This also applies to nonnegative
  sums mixing the six lengths.

Lean proves the actual orbit transition, the center trace, all count
inequalities, monotonicity of finite weighted sums, and the obstruction for
arbitrary natural-number weights. The elementary extension of the count
inequalities to arbitrary nonnegative real weights is mathematical reasoning
in this report; it is not an additional Lean theorem over the reals.

This is a counterexample to a ranking-function proposal, NOT a finite row
whose center alternates forever. It does not exclude signed weights with a
separate nonnegativity proof, time-dependent scores, amortized decreases,
longer blocks, nonlocal invariants, or other proof methods. It is not a
refutation of EFMW as a whole. Mathematical novelty is not established.

## 4. Constraint-solver attack on the linear bound

`search.py` encodes the complete backward light cone for times `0..H`.
Only initial sites `[-R,R]` are variables; other initial sites are false.
Every included space-time cell obeys the exact Rule 30 rule. There is no
periodic wraparound, forced future white boundary, or numerical approximation.
The cone shrinks toward the queried center because cells outside it cannot
affect the requested prefix.

An UNSAT result means no initial assignment has the target prefix through
time `H`, inclusive. An UNKNOWN result means no conclusion. Any SAT result
would be checked by both expanding-integer and coordinate-set simulation.

| Radius R | Tested inclusive horizon 2R+2 | Solver result |
|---:|---:|---|
| 11 | 24 | UNSAT |
| 12 | 26 | UNSAT |
| 13 | 28 | UNSAT |
| 14 | 30 | UNSAT |
| 15 | 32 | UNSAT |
| 16 | 34 | UNSAT |
| 20 | 42 | UNSAT |
| 24 | 50 | UNSAT |
| 32 | 66 | UNSAT |
| 33 | 68 | UNSAT |
| 40 | 82 | UNSAT |
| 48 | 98 | UNKNOWN: timeout |
| 56 | 114 | UNKNOWN: timeout |
| 64 | 130 | UNKNOWN: timeout |
| 96 | 194 | UNKNOWN: timeout |

The radius-40 class contains `2^81` initial configurations. The solver reasons
symbolically over that class; it did not enumerate all those rows individually.
Its UNSAT output was not exported as a kernel-checked proof certificate. The
successful radius-40 test also excludes an alternating prefix through time 82
for all smaller supported rows, but does not imply their sharper `2R+2` bounds
at radii not separately tested.

An additional left-half solver attempted the known stronger Q01 formulation:
the wall at depth zero is white, and the first cell is required to be black at
every even time. Widths 40,48,52,56,64,80,96 all timed out at ten seconds of
solver time each. These failures are recorded in `left-results.json` and are
not mathematical evidence against Q01.

## 5. Verification and anti-circularity audit

| Operation | Inputs and transformation | Pass/fail criterion | Result |
|---|---|---|---|
| Exact recurrence derivation | Boolean Rule 30 and XOR differences | Identity for every Boolean assignment | Lean checked |
| Support-preserving SMT search | Frozen radius/horizon; exact finite cone | SAT refutes that bound, UNSAT excludes that finite case, timeout unresolved | Eleven exclusions; four unknowns |
| Local-score falsification | Fixed nonnegative block-count score family | One alternating transition weakly increases every feature | Concrete witness for lengths 1..6 |
| Independent encoding check | Direct row enumeration and coordinate evolution | Agree with SAT/UNSAT at exact maximum prefix boundaries | Passed radii 0..6 |
| Boundary regression | Radius-21 finite truncation of the known ether | Must survive through 21 and fail at 22 | Passed |
| Formal audit | Pinned official definitions and own Lean modules | Compile; kernel-replay every headline; standard axioms only | Passed |
| Full-goal check | Attempt module against official Problem1 type | Must reject without a full proof | Rejected, as expected |

No ad hoc Zoo animal was invented. These are explicit mathematical and
computational operations, with the Zoo evidence-separation and anti-circularity
rules applied to their conclusions.

`verify.py` freshly enumerated all rows at radii 0..6 and recovered maximum
first-failure times `1,3,6,6,6,7,8`. Both sides of each maximum were checked
against SMT (SAT just before, UNSAT at the maximum). Fourteen control records
passed, including the ether and six local-score count comparisons.

Lean 4.35.0 compiled and replayed 18 theorem headlines in `Rule30AttemptV3`.
The 20 inherited v2 headlines in `Rule30SearchV2` were separately compiled and
replayed against the current pinned kit. These are not 38 new discoveries.
The official checker rejected the v3 module as a complete Problem 1 proof.
The SMT exclusions are separate from the Lean-verified algebra and witness.

The same assistant wrote the search and checking code. Separate implementations
help catch encoding mistakes but do not constitute independent external
replication. Nested support classes are not independent statistical samples.
No p-values, probabilities of truth, or empirical-physics conclusions are drawn.

## 6. Comparison with established work

The official catalog already has the Q01/CQ01 period-two reductions, the exact
sideways reconstruction, and barriers to several local ranking methods. In
particular, its width-52 module proves escape of the zero-wall left half by
even time 96. That theorem is stronger in support coverage than this attempt's
two-sided radius-40 exclusion. I read that source but did not rebuild its large
certificate modules during this run.

The catalog also identifies even the empty-right-half milestone, `CQ01Empty`,
as open. Re-expressing the target as a residual or a forced initial row does
not itself resolve it. This attempt's algebra overlaps standard Boolean
derivative and cellular-automaton reasoning; no new physical law or proven
EFMW-specific mechanism follows.

Pinned official kit commit: `3eca23c0a9fa6b153313655e6d51835406c2d06e`.

* [Official problem and rules](https://www.rule30prize.org/)
* [Official agent guidance](https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md)
* [Catalog status](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/README.md)
* [Period-two coupling](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30PeriodTwoCoupled.lean)
* [Sideways reconstruction and empty-right-half target](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30PeriodTwoSideways.lean)
* [Known ranking barriers](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryBarriers.lean)
* [Existing width-52 certificate](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryWidth52.lean)

## 7. What would advance the proof

The missing object is an argument that handles arbitrary finite support and
the phase-dependent masking. A practical narrower mathematical target is:
prove that the uniquely reconstructed left half for an empty right half has
black cells at arbitrarily large depths (`CQ01Empty`). This is an established
open subproblem, not a promised easy step.

Success for a future iteration means a complete uniform derivation, translated
to the official definitions and kernel checked. A finite counterexample would
reject the conjecture. More finite prefixes, solver timeouts, or another
conditional implication do not count as success.

The immediate result here is a falsified proof strategy and an explicit
remaining obligation. The research attempt has stopped; no continuing search
is scheduled. No prize submission was made. This repository publishes the
attempt and its evidence for inspection and reproduction.

## 8. Reproduction

Python 3 with `z3-solver==5.3.1.0`:

```sh
python3 -m pip install -r requirements.txt
python3 search.py
python3 search.py --radii 33,40,48,56,64,96 --timeout-ms 12000 --output sat-large.json
python3 left_search.py
python3 verify.py
```

Solver timeouts are hardware dependent. They are not reproducible claims of
unsatisfiability. The finite UNSAT instances and exact witness are the substantive
computational outputs to recheck.

For Lean, install Lean 4.35.0, clone the official kit, and check out the exact
commit above. No Mathlib download is needed for the core modules used here.

```sh
python3 check_formal.py --kit /absolute/path/to/Rule30PrizeKit
```

Inspect `formal-status.json`, especially its explicit false values for
`problem1_solved`, `uniform_escape_proved`, and `linear_escape_proved`.
The successful exit of the checker means the partial work was correctly checked.

This host required the inherited `self_exe_compat.c` adapter because its process
filesystem permits `/proc/self/exe` but not the equivalent own-PID path. It only
aliases that executable lookup. It does not alter Lean's proof checker. It is
included for provenance and is unnecessary on normal Linux systems.
