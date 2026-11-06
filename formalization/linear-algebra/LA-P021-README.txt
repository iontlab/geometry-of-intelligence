LA-P021: full unsectioned Holstein chapter6, printed97–98/PDF99–100.
Lean4.34.0; unchanged pinned Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
21 authored declarations:20 theorems and one definition.
General fields, arbitrary vector spaces; no finite-dimensionality assumption.
Own derivation of basisSetBetween/indexedBasisBetween via actual Mathlib
zorn_subset applied to admissibleIndependentSets M E. Nonempty chains use
their union and linearIndepOn_sUnion_of_directed; the empty chain uses M.
Maximality implies spanning, and Basis.mk converts the set to a basis family
indexed by the subtype B. b(x)=x and range(b)=B are explicitly proved.
All three corollaries follow from the own general theorem.
The imported Zorn theorem and its existing classical choice dependencies
are foundations, not a new proof of Zorn or an added iLab axiom. The original
only refers to the axiom of choice and an exercise sheet; no complete
ZF equivalence proof is supplied or claimed. Lean's Classical.choice is
not itself a formalization of the entire ZF metatheoretic equivalence.
Polynomial examples use existing Mathlib basisMonomials, explicitly as
supplementary examples. Browser posets/basis algorithms and SVGs are
separately tested illustrations, not formally verified JavaScript programs.
No sorry, new axioms, native_decide, or silently weakened general statements.
