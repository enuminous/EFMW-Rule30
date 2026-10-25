# EFMW Rule 30 Attempt 4 — CQ01Empty

**October 25, 2026. Outcome: the target remains unresolved.**

This bounded attempt investigated the surviving empty-right-half reconstruction
route. It produced exact coupling identities, a verified fast representation of
the driven right half, and a kernel-checked counterexample to an apparent early
period. It did not prove `CQ01Empty`, the general period-two conjecture, or Rule
30 Prize Problem 1. No EFMW-specific advantage was demonstrated.

## Frozen target and sources

The target is exactly

`Rule30PeriodTwoSideways.CQ01Empty = ¬ FinSupp (Psi empty)`.

Equivalently, for every depth bound W, there must be a black cell of the
reconstructed left row Psi(empty) at some depth d > W. The required argument is
uniform in W. A long finite prefix does not satisfy that requirement.

* [Official definitions and reconstruction](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30PeriodTwoSideways.lean)
* [Official zero-boundary dynamics](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean)
* [Existing method barriers](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryBarriers.lean)
* [Base Monolithic attempt](https://github.com/enuminous/EFMW-Rule30/tree/3c674f845be6fe6cbcc29ca07c03fa3c7ee670f4)

The official kit is pinned to `3eca23c0a9fa6b153313655e6d51835406c2d06e`;
the base attempt is `3c674f845be6fe6cbcc29ca07c03fa3c7ee670f4`.
`PLAN.md` was written before executing the bounded search. Source and output
hashes are included in `SHA256SUMS`.

## Exact recurrence used

The center is prescribed to alternate black, white, black, white. Let

`u_R(s) = drv altCol R (2s+1) 1`.

The corresponding column immediately to its left is

`a(2s) = 1`, `a(2s+1) = NOT u_R(s)`.

The official sideways reconstruction obeys

```
C_0(t) = 0
C_1(t) = a(t)
C_(k+2)(t) = C_(k+1)(t+1) XOR (C_(k+1)(t) OR C_k(t))
Psi(R)(k) = C_k(0).
```

The Python search computes these exact Boolean operations with integer-packed
time columns. Each deeper column loses one time sample, so no artificial
future boundary can influence the recorded initial-row prefix. Its driven
right-half evolution expands freely into the initial white background.

## Findings and evidence levels

| Operation and purpose | Inputs and criterion | Result and status |
|---|---|---|
| Exact reconstruction | Empty right half; compute depths 1..16384 from the official recurrence | 8,189 black cells; the last is at depth 16,383. **Demonstrated finite computation**, not infinite support. |
| Separate encoding check | Ordinary arrays using arithmetic modulo 2; compare first 256 depths and first 128 driven samples | Exact agreement. Helps detect encoding errors; not external replication. |
| Truncation check | Cut the reconstructed row at W=0..127; evolve ordinary two-sided Rule 30 | All 128 first-failure times equal the first reconstructed black depth beyond W. This confirms the implementation against the catalog's existing exact-death relation. |
| Periodic absorption search | Periods 1..64, transients 0..256, first 1,024 samples of u | None of the 16,448 candidates fits the training prefix. Eventual periodicity with other parameters remains **unresolved**. |
| Binary-scale affine search | For each phase b=0,1, all 32 XOR combinations of 1, Psi(n−1), Psi(n), Psi(n+1), and n mod 2; fit Psi(2n+b) at target depths ≤1024, n≥2 | All 64 candidates have explicit counterexamples. This precisely specified family is **rejected**. No model reached held-out validation. |
| Symbolic two-step coupling | Arbitrary R and arbitrary n; prove equality in official definitions | **Demonstrated in Lean**, described below. It does not supply the missing support argument. |
| Right-support induction test | Prove the exact location of the advancing right edge | **Demonstrated in Lean**: support expands, so restarting does not reduce support width. |
| Formal audit | Compile with Lean 4.35.0 and replay new declarations through the official checker | All 10 theorem headlines passed; only `propext` and `Quot.sound` occur in their axiom dependencies. A complete Problem 1 claim was rejected as expected. |

The finite prefix's longest internal white run is 11, at depths 5,896..5,906.
No universal gap bound is inferred. `results.json` preserves all 128 truncation
checks and all 64 affine counterexamples, rather than retaining only selected
examples.

## What the uniform lemmas establish

With `R2 R` denoting the driven right half after two steps, Lean verifies

```
zrow (Psi R) 2 = Psi (R2 R)
zrow (Psi R) (2*n) = Psi (advanceRight R n).
```

These are exact transport identities for every right half and every n. They are
direct consequences of the catalog's two-step shift and right-trace shift
identities. They are useful formalization, not a claim of mathematical novelty.

For the empty initial right half, Lean also proves

```
drv altCol empty t p = false        whenever t < p
drv altCol empty (t+1) (t+1) = true.
```

Thus the rightmost black cell at positive time t is exactly at position t.
After n two-step restarts the driven right support reaches position 2n. The
transport relation does not turn the empty-right problem into a smaller-support
base case. An induction that requires this size to decrease is unavailable.
This does not rule out different induction measures or other global arguments.

## A false shortcut caught exactly

The initial driven trace is visually close to a seven-sample repeating pattern.
Direct computation shows `u(s+7)=u(s)` for s=1..145, but

```
u_empty(146) = 1
u_empty(153) = 0.
```

The inequality and the rejection of a period-seven tail starting at sample 1
are independently kernel-checked in `period_seven_counterexample` and
`not_period_seven_from_one`. The first 145 agreements are a Python observation.
This candidate was identified by inspecting the computed prefix and then
falsified; it is not a preregistered successful prediction. It does not exclude
a later period-seven tail, larger periods, or eventual periodicity in general.

The catalog already proves that eventual periodicity of u_R would imply
infinite support of Psi(R). This attempt did not establish that premise for
the empty right half.

## What remains missing

The required implication is still: for arbitrary W, derive a black depth beyond
W without assuming that such depths continue. Neither the two-step transport
identity nor any successful finite computation supplies this implication.

The new code contains no assertion of `CQ01Empty`, no new axiom, no `sorry`, and
no physical EFMW hypothesis. The 16,384-cell reconstruction is not exported as
a Lean certificate; distinguish it from the formally verified integer model,
transport identities, edge statements, and specific period counterexample.
The official checker replays this attempt's declarations, while trusting the
ordinary Lean/import boundary documented by that checker.

The same assistant developed and checked the two Python implementations. No
external replication, probability of truth, empirical-physics conclusion, or
claim that all possible EFMW approaches have been exhausted is made.

The bounded attempt is complete. It found no new uniform mechanism that closes
the target. Further work needs an additional mathematical idea beyond the
rejected finite-fit families and the already-known conditional absorption route.

## Reproduce

The repository's root `lake build` includes this module, and its verification
workflow reruns this search, compares all three finite output files byte for
byte, and replays the ten theorem headlines. See the [root instructions](../README.md#build-and-check)
to use the shared pinned dependency and write fresh results under `run-results/`.

For a standalone run from this directory:

Python needs only the standard library:

```sh
python3 search_cq01.py
```

Install Lean 4.35.0. Fetch the official kit and use the pinned commit:

```sh
git clone https://github.com/WolframInstitute/Rule30PrizeKit.git
git -C Rule30PrizeKit checkout 3eca23c0a9fa6b153313655e6d51835406c2d06e
python3 check_attempt.py --kit ./Rule30PrizeKit
```

The checker supports `--lean-bin /absolute/path/to/lean/bin` when Lean is not on
PATH. It writes `formal-status.json` and logs in `verification/`. The full-prize
negative control must exit 1; that expected rejection is not a refutation of
Problem 1. Both scripts accept `--output-dir /path/to/results` to preserve the
recorded evidence while reproducing it.

On this execution host only, the inherited `self_exe_compat.c` adapter was needed
to map a denied `/proc/<own-pid>/exe` lookup to `/proc/self/exe`. It changes no
proof-checking behavior. It is unnecessary on normal Linux hosts. Lean's
release archive extracted its files but reported ownership-metadata errors;
the installed binary subsequently reported the correct pinned version and the
build and kernel replay succeeded.

Contents: source, exact finite prefixes, results, frozen plan, verification
logs, dependency pins, and checksums. No search remains running and no prize
submission was made. This directory publishes the completed bounded attempt
for reproduction.
