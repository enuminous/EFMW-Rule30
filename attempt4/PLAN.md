# CQ01Empty bounded attempt, 2026-10-25

Target: `Rule30PeriodTwoSideways.CQ01Empty`, exactly `¬ FinSupp (Psi empty)`
at Rule30PrizeKit commit 3eca23c0a9fa6b153313655e6d51835406c2d06e.
Base attempt: enuminous/EFMW-Rule30 3c674f845be6fe6cbcc29ca07c03fa3c7ee670f4.

Success: an unconditional argument for arbitrarily large depths, checked against
the official definitions in Lean. A theorem exposing an additional assumption,
or a finite prefix, is not target success. Preserve every rejected candidate.

Initial work budget: one exact reconstruction through depth 16384; cross-check
the first 256 depths with a separate array algorithm and check 128 finite
truncation death times using ordinary forward Rule 30 evolution. Search for
short periodic absorption in the driven-right trace on training samples through
2048 steps; validate any candidates on the remaining sample. Search for simple
binary-scale identities of Psi using training depths 1..1024 and held-out depths
1025..16384. Finite fits are conjectures, never proof.

Symbolic routes: derive the exact reconstruction and two-step coupling; test
whether a support argument or a genuine smaller-scale recurrence closes the
target. Read existing barriers before proposing a local ranking. Do not assume
decay, aperiodicity, finite support of the desired reconstruction, or a physical
EFMW law. No additional Zoo animal definitions are introduced.

Stop: after this bounded pass and attempts to prove surviving exact identities.
If no uniform mechanism is obtained, report unresolved, with reusable code,
counterexamples, formal status, and the remaining proof obligation.
