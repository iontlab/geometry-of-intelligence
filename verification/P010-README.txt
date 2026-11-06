LA-P010 — Holstein §3.1–3.2, printed48–53/PDF50–55.13 numbered units.
Source ends immediately before §3.3. Lean4.34.0, unchanged Mathlib
5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
Fresh project oleans; direct type/value references and axiom audit extracted.
No sorry/admit/native_decide or additional project axioms. Standard foundational
axioms propext,Classical.choice,Quot.sound are enumerated per declaration.

The vector-space formalism is AddCommGroup V + Module K V over Field K.
Zero scalar, scalar zero, scalar-zero criterion and minus-one action have source-
aligned proofs. Coordinate/self/zero spaces, complex over real, real over rational,
functions, sequences and outer binary products use actual typeclass structures.
No claim to formalize the analysis exercise about null sequences in this package.
Submodule UV1 nonemptiness is used to derive zero membership; inherited subspace
operations agree after coercion. Real/imaginary complex axes are real submodules;
the real axis is not closed under multiplication by I. The union counterexample
is compiled. Indexed intersections have no finiteness restriction and include the
empty index type. The finite internal sum is explicitly constructed from tuples,
proved closed, inclusive, minimal and equal to iSup; it also works for r=0 as a
stronger explicitly recorded extension of the source's positive-r assumption.

The full-sum premise is retained in the equivalence between trivial intersection
and existence of a unique pair decomposition. Injectivity of summation is proved
equivalent to trivial intersection without assuming surjectivity. With both
conditions, a LinearEquiv connects the external product and internal ambient space;
the objects are not asserted literally equal. Finite indexed DirectSum is linked
to its function representation by the pinned Mathlib equivalence, without replacing
infinite direct sums by products. Complex axes form an internal real direct sum;
the repeated imaginary axis does not.

Original indexing/parenthesis errors remain in Mathematics and are separately
explained; they are not asserted as Lean identities. Finite browser axiom checkers,
SVG projections and rounded numerics are tested, not formally verified programs.
