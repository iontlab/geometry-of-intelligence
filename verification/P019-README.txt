LA-P019: Holstein section5.4, printed87–92/PDF89–94.
Lean4.34.0; Mathlib5ed2965256430c3649e86755f9576b54eca72435 unchanged.
Reproduce: lake env python tools/verify-linear-algebra.py
General field K, explicit finite bases indexed by Fin n, Fin m, Fin k;
dimension0 and unequal source/target dimensions are allowed.
coordinateSynthesis a = a.equivFun.symm represents Holstein Phi_A.
coordinateChange a a' = toMatrix a a' id maps old a to new a' coordinates;
coordinateChangeConvention proves it equals a'.toMatrix a, not the reverse.
Both inverse products, vector coordinates, the commuting triangle,
composition, an explicit bridge for mismatched middle bases and the full
source/target change formula are compiled. Nonsingular inverse is used only
for matrices whose two inverse products have already been proved.
The real reflection example checks both basis-vector images, explicit
matrix inverses, the original triple product and all vector paths.
It does not formalize a separate Euclidean geometric reflection predicate.
The 1D scalar identity assumes the nonzero basis scalar explicitly.
Original formulas and typographic/editorial issues remain in the source;
formal statements use consistent typed source/target basis roles.
No claim that the JavaScript engine or SVG renderer is formally verified.
All dependencies are extracted from compiled types/values; no didactic edges.
