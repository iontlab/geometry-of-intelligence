LA-P024: Holstein §7.4, printed110–112/PDF112–114, all10 original items.
Lean4.34.0, unchanged pinned Mathlib5ed2965256430c3649e86755f9576b54eca72435.
27 authored declarations:24 theorems,3 definitions.39 project declarations including
compiler-generated helpers. Entire project freshly compiled and axiom-audited.
Use lake env python tools/verify-linear-algebra.py in the pinned project.

All finite square dimensions and arbitrary fields, including characteristic2.
Classical adjugate is explicitly the transposed cofactor matrix, NOT conjugate
transpose. Equality with Mathlib Matrix.adjugate is proved. Both product identities,
conditional inverse formula, general2×2 formula and Cramer coordinates checked.
Endomorphism determinant is actually basis-independent; the finite-dimensional
automorphism criterion retains its hypotheses. Rotation reuses the old rotation
definition; reflectionAxis matches Holstein's doubled-axis-angle matrix exactly.

Existing Mathlib theorems are used, explicitly documented in per-item mappings.
This does not reproduce Holstein's full elementary-factor proof as an identical
new Lean proof. Cramer's source proof is only the exercise14.3 reference; the
optional didactic proof is iLab-authored, and the Lean proof uses Mathlib Cramer.
Fin indices start0 instead1; corresponding signs agree. Empty minor det=1 is a
separate software/Mathlib convention; source examples use positive matrix size.
The inverse of Matrix is total in Mathlib; only det≠0 cases are presented as
actual inverses. IsUnit on End(V) means an invertible linear map; Kˣ is the group
of nonzero field elements. Classical.choice is foundational, no new project axiom.

Browser exact scalar model supports Q, Q(sqrt2,i) and F2,F3,F5,F7, size1–4.
Trigonometrical display uses controlled floating-point approximations.
JavaScript engines, numerical rendering and SVG orientation are NOT formally verified.
