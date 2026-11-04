LA-P002 — exact formal scope and reproducible verification, 4 November 2026

Source: Julian Holstein, Lineare Algebra 2023/24, edition 10 August 2024.
Section 1.3, printed pages 10–14 / PDF 12–16, ending before section 1.4.

Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b).
Mathlib v4.34.0 (5ed2965256430c3649e86755f9576b54eca72435).
No toolchain or dependency upgrade.

Reproduce in the source project:
  lake exe cache get
  lake env python tools/verify-linear-algebra.py

The verifier compiles all seven LA sources into fresh verification/rebuild
oleans, then extracts direct constant references and recursive axiom
dependencies from that compiled environment. Source hashes, exit codes and
the full compiler log are published. Completed proofs contain no sorry,
admit, native_decide or additional project axioms. The only allowed standard
axioms are propext, Classical.choice and Quot.sound, where actually used.

Formal content:
* linearSystemSolutions A b is the exact set {x | A.mulVec x = b}.
* Every homogeneous system admits the zero solution.
* An all-zero coefficient row with nonzero right side makes the solution set
  empty. This argument needs no echelon assumption, a documented slight
  generalization of Remark 1.3.5.
* Row interchange, scaling by a nonzero real scalar, and addition of a
  multiple of a different source row each preserve the whole solution set.
  Both the matrix coefficients and right side are transformed.
* EquationRowOperation contains the necessary side conditions as proof
  fields. rowSequenceSolutions proves preservation for every finite list
  of permitted operations, exactly the scope of Theorem 1.3.6.
* zeroScalingNotEquivalent proves the concrete loss of information when
  x=1 is scaled by zero, yielding 0=0.
* Example 1.3.4 is proved as the complete parametrization
  {(-16-2t,t,5) | t in R}.
* Example 1.3.9 uses the original A and b and proves the entire solution set
  is the singleton {(5,0,1)}, not merely membership of that point.

Representation differences / boundaries:
* Mathlib matrices are functions on row/column index types. The column type
  is finite. Real systems with Fin m / Fin n reproduce Holstein's finite
  matrices. General row-operation proofs also allow arbitrary row types
  with decidable equality. Fin indices begin at 0 rather than 1.
* The swap operation permits identical indices as an identity; the browser
  workshop asks for distinct rows to make the requested action meaningful.
* The source and target indices for addition must differ. Scaling must have
  a nonzero factor. Adding a zero multiple is allowed.
* The original typo in 1.3.9 says 'second row divided by 2' while its matrix
  scales the third row. The source layer preserves both; the browser's
  original sequence follows the displayed matrices, with an editorial note.
* The original first entry a_mn in the last row of the generic augmented
  matrix is preserved in the original layer; indexed Lean coefficients are
  positionally correct.
* Echelon recognition, Gaussian elimination, history navigation, rational
  parsing, plots and back-substitution in JavaScript are tested educational
  software, not proved correct by these Lean theorems. No complete formal
  verification of the Gaussian algorithm is claimed. Definition 1.3.2 and
  Remarks/recipe 1.3.3, 1.3.7, 1.3.8 have no separate verified mapping.

Graph edges are actual direct references in compiled types and values.
Existing declarations preserve their own pinned source commits. Additional
selected Mathlib foundations expose a bounded relevant formal excerpt;
omitted dependencies remain documented. No didactic/transitive edges.

Preparation, Dimensions, BasisMaps, MatrixAlgebra, Rotations, HCT and RQ-001
source declarations are unchanged.
