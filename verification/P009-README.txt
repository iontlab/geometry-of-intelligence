LA-P009 — Holstein §2.5 Ringe, printed44–47/PDF46–49.
Eight numbered source units and complete original arguments. Chapter3 excluded.
Lean4.34.0, unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
Fresh oleans in verification/rebuild; types, values and axioms extracted.
No sorry/admit/native_decide or additional project axioms. Permitted standard
axioms: propext,Classical.choice,Quot.sound, enumerated per declaration.

NonUnitalRing models the initial definition; Ring models the unital convention
adopted immediately afterwards in the source. General target rings need not be
commutative. A field-to-ring homomorphism is injective under Nontrivial target;
the proof uses f(a⁻¹), not an assumed inverse operation on the target.
Ring axioms, a concrete noncommutative matrix example, function-ring operations,
a noninvertible function, residue rings and representative-independent products
are compiled. The prime-field equivalence is stated explicitly for m≥2 and
proved via Mathlib characteristic theory, not represented as a Lean replay of
Holstein's Lagrange proof. The original Lagrange argument is preserved in the
text and interactive navigator. m=0:2 not invertible; m=1:0=1 separately checked.
Characteristic of ZMod m, ℚ and ℝ is checked. Canonical quotient and conjugation
ring homomorphisms are represented; smallest representatives fail addition in
the concrete m=4 example. No certificate for every individual source sentence.

Polynomials use Mathlib Polynomial, with degree(0)=bottom corresponding to−∞.
Coefficient addition, convolution, evaluation homomorphism, difference of
squares, noninvertibility of X and the F₂ polynomial X+X² are checked. This
polynomial is nonzero while its evaluations at every F₂ point are zero.
The extra a₀ term and extra parenthesis in the original remain in Mathematics;
only the separately explained correct convolution law is compiled.
Browser programs, exact rational engine and SVG graphics are tested programs,
not formally verified implementations. All graph edges are direct constants
from compiled types and values; no didactic shortcut edges.
