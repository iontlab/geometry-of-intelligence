LA-P011 — Holstein §3.3, printed53–58/PDF55–60;14 numbered units.
Lean4.34.0 and unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
Fresh project oleans; actual compiled type/value references and transitive axiom
audit. No sorry/admit/native_decide or additional project axioms. Standard axioms
propext,Classical.choice,Quot.sound are listed per declaration, not treated as errors.

LinearMap over Field K represents the exact two linearity conditions. Combined
condition is equivalent to both laws. Finite combinations, zero and differences
are checked. Scalar endomorphisms, nonzero scalar bijectivity and all linear K→K
maps are represented. Rotation identities are reused from the earlier verified
module rather than counted again. Not every example is separately formalized.
Images/preimages use Submodule.map/comap, membership agrees with the original
set definition. Kernel/range, composition and the linear inverse of an explicitly
bijective map are checked. Basis-image uniqueness reuses the existing basis proof.
LinearEquiv witnesses isomorphy in explicit universes; no set of all vector spaces.
Hom is a literal Submodule of the full function space with proved closure, linearly
equivalent to LinearMap; pointwise operations are checked.

The canonical summation U×Z→U⊔Z is surjective without a full ambient-sum premise.
Trivial intersection yields injectivity using the existing P010 difference proof.
Thus external pairs and the inner summation subspace are linearly equivalent.
Original prime/minus/type inconsistencies remain in Mathematics only. Concrete
compatibility with linear maps is checked; no full categorical naturality claim.
DirectSum families have finite support; arbitrary products carry Module structure.
Finite indexed sums are equivalent to coordinate functions. Polynomial coefficients
give a LinearEquiv with Finsupp, then with the actual constant-family DirectSum;
both component formulas are proved. Constant one over N has infinite support.
This is linear representation, not polynomial evaluation or a convergence theorem.
Browser programs/SVGs are tested illustrations, not formally verified software.
Section3.4 belongs to P012 and is excluded.
