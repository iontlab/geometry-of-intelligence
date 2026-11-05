LA-P004: Holstein §1.5, printed20–25/PDF22–27, before §1.6.
Typed Set α identities and finite powerset cardinality, not a formalization of ZF/ZFC.
Russell: abstract relation specification is impossible; no contradictory set is postulated.
Set identities use existing iLab logical laws, matching the actual original proof.
Nat induction, strong induction, smallest counterexample/descent, factorial recursion,
odd sum over range n (includes n=0), prime factor existence for n>1 and explicit 1/0 cases.
primeFactorizationByMinimalCounterexample follows the original minimality argument,
with factors 1<a,b<n. A second declaration uses Mathlib's actual primeFactorsList.
No uniqueness claim. The original unrestricted wording including zero is not proved.
Constructive Russell argument and set laws are distinct from classical counterexample
selection. Per-declaration axioms are in compiled.json. No project-added axiom or sorry.
Lean4.34.0; Mathlib remains pinned5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
All project sources are rebuilt before extraction; no browser algorithm is formally verified.
