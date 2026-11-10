LA-P040 – Holstein §12.4: exact formal scope and reproduction

Lean 4.34.0. Unchanged Mathlib revision 5ed2965256430c3649e86755f9576b54eca72435.
Sources: ILab/LinearAlgebra/QuadraticForms.lean, root import and the existing extraction/verification tools.
Run from the pinned project:
  lake env python tools/verify-linear-algebra.py
The audit lists every actual fresh compiler command, source hash, exit code, type/value dependency and axiom dependency. No sorry, no new project axioms, no native_decide.

CONVENTIONS
Holstein defines β_q(v,w)=q(v+w)−q(v)−q(w). This is Mathlib polarBilin, not associated. Mathlib associated is HALF that form. quadraticAssociatedFactor proves the exact factor of two. The inverse in Holstein's linear equivalence is β↦(1/2)β(x,x), including actual linearity and both inverse laws.
Holstein's QF1 and QF2 are explicitly defined as quadraticAxioms and proved equivalent, over arbitrary fields including characteristic2, to the existence of a Mathlib QuadraticForm with the same underlying function.
Holstein calls q nondegenerate when its UNHALVED POLAR form is nondegenerate. This is quadraticNondegenerate. Mathlib's general quadratic-map Nondegenerate/radical convention is not identical in characteristic2 and is not silently substituted. The exact agreement with the polar kernel/radical is proved under invertibility of2.

GENERAL RESULTS
Quadratic homogeneity; unhalved polar bilinearity/symmetry/self-evaluation; scalar-square examples and exact nondegeneracy2c≠0; symmetric bilinear/quadratic LINEAR equivalence under2≠0; actual ZMod2 lost-information and missing-polar-form counterexamples.
General orthogonal-basis existence for symmetric bilinear forms over any field with2≠0 in finite dimension, including dimension0. This is an actual compiled existence theorem, not a numerical example.
Nullspace as the bilinear map kernel. In any finite diagonalizing basis, membership is exactly the coefficient equations v_i β(b_i,b_i)=0. Over a field these are equivalent to Holstein's span of the zero-diagonal basis vectors. General radical-dimension invariance and zero-weight count under true quadratic isometry.
General complex0/1 and real−1/0/1 normal forms by actual linear isometric equivalences. quadraticBilinearCoordinates, quadraticComplexBilinearNormal and quadraticRealBilinearNormal additionally prove the complete bilinear coordinate formula, with correct factor conventions and no complex conjugation. The finite permutation that sorts weights into contiguous blocks is not a separately authored Lean declaration; the browser performs and checks this permutation.
General Sylvester existence and uniqueness: quadraticSylvester combines normal form, equivalence and the precise positive/negative/zero counts. quadraticSignatureInvariant proves invariance under any true equivalence. Positive/negative indices are characterized as greatest dimensions of definite subspaces; the nonpositive-subspace dimension inequality supplies the mathematical core of Holstein's dimension-intersection proof. These are not finite-matrix-only specializations.

TRANSPARENT LIMITS
12.4.11 is PARTIALLY formalized: the two directions of positive definiteness and positive semidefiniteness for general finite weighted real quadratic forms, and general isometry-invariance of positive definiteness, are compiled. All five sign categories and their complete signature criteria are correctly explained and independently tested in the browser, but are not all packaged as general Lean equivalences here.
The ellipse/hyperbola geometric classification is illustrated and independently checked algebraically, not presented as a full analytic Lean formalization of plane curves.
Minkowski evaluation/polarization, signature(3,1,0), indefiniteness for c≠0 and a nonzero isotropic vector are compiled. The physical interpretation and the original informal word “distance” are not formalized.
Classical.choice, propext and Quot.sound remain visible where genuinely required. No additional project axioms. The JavaScript algorithms, UI, parser, numerical square roots, SVG graphics and history are TESTED SOFTWARE, not Lean-verified implementations. All earlier package limitations remain unchanged, notably the partial general symplectic-basis theorem in12.3.6.

COMPUTATION
Exact rational/finite-field diagonalization follows Holstein's kernel induction, not an eigenvalue solver. Complex exact operations use the existing supported algebraic scalar field. General square-root normalization may leave that field and is therefore explicitly approximate, with full independent matrix-product residual checks and scale-dependent tolerances. Rational inertia uses exact diagonal signs; independent references use characteristic polynomials and Sturm root counts with multiplicity.

ORIGINAL SOURCE
All12 original units12.4.1–12.4.12, all proofs and all unnumbered passages are retained. Printed177–182 / PDF179–184, stopping before12.5. The proof of12.4.9 follows Definition12.4.10 in the original and remains there. Errors/oddities (missingx in the hyperbola coordinate, “aufK”, off-diagonal i/j in normalization formulas, duplicated words/punctuation, Minkowski z₂ coordinate and informal “distance”) are separately documented. Native text and mathematical formulas; no original illustrations occur in this section. Protected source SVGs are unchanged.
