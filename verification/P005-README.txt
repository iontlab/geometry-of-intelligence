LA-P005 — Holstein §1.6 Relationen und Abbildungen, printed25–30/PDF27–32.
Lean 4.34.0; unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
39 authored declarations:36 theorems,3 definitions; no new compiler auxiliaries.

Typed products, Setoid equivalence classes (including all three source conditions) and quotient projection; function
graphs, image/preimage; composition/identities/restriction; bijectivity,
finite endomap equivalences; existence and uniqueness of a two-sided inverse;
finite cardinality and empty bijection; full curry/uncurry equivalence.
General source statements are not replaced by finite examples.

The three definitions are relationClass, graphOfFunction, curryEquivalence.
The inverse proof uses Equiv.ofBijective and reports its foundational axioms.
No sorry/admit, no additional project axioms, no native_decide.
Allowed audited axioms: propext, Classical.choice, Quot.sound.

Lean types encode domains/codomains explicitly. This is not an untyped ZF
universe. Setoid quotients represent the source equivalence-class structure;
quotientEquality identifies the underlying relation exactly.
Finite cardinality uses Fintype; no finite result is claimed for infinite types.
The particular ℕ↔ℤ enumeration, rational-number construction and countability
of ℚ/noncountability of ℝ are explained but have no new formal certificate here.
Modulo0 and the printed fraction/sphere anomalies are editorial, not silently
corrected original propositions that are then claimed to be verified.
JavaScript routines and diagram rendering are tested, not formally verified.

Reproduction in the pinned project:
  lake env python tools/verify-linear-algebra.py
The script freshly rebuilds every local mathematical module, extracts direct
constants from compiled types and values and audits axioms. compiled.json,
audit.json and clean-compilation.log contain the actual result and hashes.
Earlier package sources are unchanged and rebuilt as regression verification.
