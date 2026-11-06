LA-P012 — Holstein §3.4, printed58–61/PDF60–63;7 numbered units.
Lean4.34.0 / unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
All project sources freshly compiled; actual compiled type/value constants and
transitive axiom audit. No sorry/admit/native_decide or new project axioms.
Standard axioms propext,Classical.choice,Quot.sound are reported per declaration.

All quotient and universal/isomorphism statements use arbitrary Field K and
arbitrary additive modules, without finite-dimensional restrictions. The actual
Submodule quotient Setoid agrees with x-y membership. Its equivalence and affine
class description are proved. Actual Module structure, linear projection, scalar
and addition representative independence, surjectivity and exact kernel are checked.
Induced linear maps satisfy factorization and uniqueness. Necessary and sufficient
condition is expressed as exists-unique iff U≤ker(f); both inverse constructions
are verified. The earlier quotientKernelEquivImage is actually reused for the
first isomorphism theorem and its existence-uniqueness/factorization equations.

The projection example is literally Fin3→R with index2 last; kernel membership,
surjectivity, quotient equivalence, values and inverse [(0,0,x)] are checked.
The external direct sum is the binary product V×W; its embedded first summand
is exactly the kernel of the second projection. General quotient equivalence,
value and inverse formulas match the original with its embedding made explicit.

Example3.4.7 uses all convergent real sequences N→R, represented by a Submodule
with existential filter convergence. The limit is chosen from actual convergence;
uniqueness in R proves additivity/scalar compatibility, independent of that choice.
The null-sequence submodule is its kernel; membership is iff convergence to zero.
The limit map is surjective by constant sequences. Equality of quotient classes
is iff equality of limits. The full quotient is linearly equivalent to R and the
representative evaluation formula is proved. No finite-window replacement.

Intro has no artificial theorem. The general opening cokernel observation is
explained didactically, not counted as a separately formalized source unit.
Original notation errors remain in Mathematics and are recorded separately.
Browser calculations/SVGs are tested illustrations, not formally verified software.
