LA-P006 — chapter 2 prologue and §2.1 Gruppen, printed31–36/PDF33–38.
Lean4.34.0, unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Actual fresh rebuild: tools/verify-linear-algebra.py. compiled.json contains
types, values, direct constant dependencies and recursive axiom audit.
No sorry/admit/native_decide, no new project axioms.
Allowed foundational axioms: propext, Classical.choice, Quot.sound.

All four parts of theorem2.1.5, inverse/neutral uniqueness, typed group laws;
ZMod representative independence including m0=Int; permutations and the
original noncommutative witness; Cayley left-regular representation;
subgroup closure/inheritance and integer powers; full right-coset framework
and Lagrange for finite groups. Detailed per-unit scope: coverage.json.

Holstein uses Ha and a~b iff a*b^-1 in H. groupRightRelationLibrary proves
equality with Mathlib rightRel, whose displayed formula reverses a,b;
subgroup closure under inversion proves their equivalence. right/left
quotient equivalence transfers cardinalities without assuming normality.
The graph shows actual compiler dependencies only. The separate class
partition theorem genuinely uses the earlier relationClassesEqualOrDisjoint.
The final cardinal factorization uses the existing Mathlib quotient/product
bijection, not a fabricated dependency on that separate partition theorem.

Finite simulations are tested JavaScript, not verified Lean programs.
No complete certificate is claimed for every example or the one-sided
axiom-redundancy remark. Incorrect original references are preserved in
Mathematics and discussed separately, never marked as verified propositions.
NeZero m is explicit for finite ZMod cardinality; m0 is infinite Int.
Permutations also allow an empty type, explicitly broader than the source.
Null-based Fin3 labels 0,1,2 correspond to original vertices1,2,3.

Reproduce: lake env python tools/verify-linear-algebra.py
No upgrades, fresh local mathematical oleans, exact pinned Mathlib cache.
