LA-P020: Holstein section5.5, printed92–96/PDF94–98, before chapter6.
Lean4.34.0; Mathlib5ed2965256430c3649e86755f9576b54eca72435 unchanged.
Reproduce: lake env python tools/verify-linear-algebra.py

51 authored declarations (44 theorems,7 definitions), with generated helpers
counted separately. General fields and Fin m/Fin n include dimension zero.
Equivalence is Y=SXT^-1 with independent matrix units; similarity uses T
on both sides. Both are equivalence relations, with the original identity
counterexample and similarity implies equivalence proved generally.
Both directions of the common-linear-map/common-endomorphism coordinate
characterization are proved, reusing CoordinateChanges.lean. A basis with
coordinate reader T has synthesis T^-1; the convention is proved explicitly.

columnRank/rowRank are finrank of the spans of columns/rows. For both there
is an independent selection attaining this number and an upper bound for
every independent selection. This verifies the source's maximum definition.
Both rank invariances, rank of every representing matrix, transposition,
inverse transposition, and equality of row and column ranks are general.
Column addition is the transpose of the existing elementary-row theorem.

EXPLICIT LIMITS:
squareRankNormalForm proves existence of the rank block form for SQUARE
matrices with an explicit index equivalence. It does not assert the full
rectangular existence statement of5.5.4 or its original basis-extension proof.
equivalenceViaCommonForm is a general rectangular certificate-composition
theorem given actual invertible reductions to a common form. It is not the
unconditional converse equal rank implies equivalent. This converse is
present in the mathematical exposition and exact tested browser construction,
but not claimed fully Lean-formalized here. Units5.5.4 and5.5.9 report this.
The source proof of row-rank=column-rank uses rank normal form; the compiled
Mathlib proof takes the transpose/duality route. No fictional formal edge
is added to reproduce an uncompiled didactic proof sequence.

The false original5.5.7 relation gives (0,40) over Q, proved exactly; the
separate corrected relation (10,-7,-4) gives zero. The false equality is
preserved only as source text, never as a verified theorem.

No assertion that the JavaScript/Gauss implementation, rational parser,
UI, SVG or source transcription is verified by Lean. These are separately
tested. Existing quotient results and echelon results remain linked rather
than duplicated for5.5.5 and5.5.13. Standard Lean axioms are audited; no new
project axioms, sorry, native_decide, or weakened statements presented as full.
