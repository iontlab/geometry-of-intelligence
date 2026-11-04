LA-P003: Holstein §1.4, printed pp.14–19 / PDF pp.16–21.
Lean 4.34.0, unchanged Mathlib revision 5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
Freshly compiles every project module and extracts direct constants from types/values.
No sorry, admit, native_decide or additional project axioms. Axiom sets per declaration
are in compiled.json. Standard Lean foundations propext, Classical.choice and Quot.sound
are permitted and transparently listed; their occurrence is not a new iLab assumption.
Arbitrary Prop double-negation elimination, excluded middle, not-forall, full contraposition,
and conjunction De Morgan use classical logic. Forward contraposition, disjunction De Morgan,
not-exists, quantifier swaps/distributions and empty-domain arguments are constructive.
Finite Bool truth tables use decidable computation, not arbitrary-Prop decidability.
The source 1.4.6 formula is false: the corrected biconditional and a counterexample to the
printed formula are separate verified declarations. The original text is not corrected.
1.4.13: the general logical negation of unique intersections is verified for an abstract
membership predicate, plus two concrete R² countermodels. This is not a new proof of every
syntactic parameterization step in the faulty original display or verification of JavaScript.
The graph includes selected Lean core logical foundations with Lean-source provenance,
as well as existing pinned Mathlib foundations. All edges are direct compiled references.
Unselected references remain recorded as externalDependencies. No didactic edges.
