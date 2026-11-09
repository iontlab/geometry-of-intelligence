LA-P032 / Holstein §9.6 – Minimal polynomial and Cayley–Hamilton
Source: printed145–147 / PDF147–149. Eight numbered units and the original
unnumbered Cayley–Hamilton proof in source order. No Chapter10 content.

Pinned compiler: Lean4.34.0. Pinned Mathlib revision:
5ed2965256430c3649e86755f9576b54eca72435 (unchanged).
Reproduce from the source archive with the matching Mathlib package cache:
  lake env python tools/verify-linear-algebra.py
This rebuilds every project module, then extracts compiled types, values,
direct constants and axiom dependencies using tools/ExtractLinearGraph.lean.
Only propext, Classical.choice and Quot.sound may occur. No sorry, admit,
new axiom, or native_decide is accepted by the verifier.

41 new authored mathematical declarations in MinimalPolynomial.lean.
General Cayley–Hamilton is proved via Matrix.aeval_self_charpoly and the
endomorphism counterpart. This uses Mathlib's general algebraic proof;
it is NOT a claim that Holstein's entire special triangular proof was
formalized verbatim. The corrected next-column induction step is proved
separately; the complete original proof and its corrected didactic navigator
are retained in Mathematics/Proof Steps. The source's word 'rows' is retained
and separately identified as incorrect for the displayed factor order.

The general minimal-polynomial characterization, monicity, annihilation,
divisibility, minimal degree, normalized uniqueness, division remainder,
basis independence, eigenvector evaluation, equality of roots in the ground
field and root multiplicity bound are formalized without assumptions of
diagonalizability or a split characteristic polynomial.

Positive degree requires a nontrivial carrier: Fin0 matrices have minpoly1.
The source's positive-degree formulation is not silently imposed on them.
The two non-scalar original examples are formalized exactly over Q, with
actual minimal degree certified by independence of smaller powers. The
characteristic7 version of the4×4 example is zero and has minpolyX.
The7-prime instance is proved by Lean's kernel using decide.
Null and identity minimal-polynomial formulas are general for nonempty
finite index sets. Additional preset computations and all JavaScript
algorithms, parsers, UI, SVG geometry and factorization search are tested
implementations; they are NOT formally verified programs.

The formal minpoly uses Mathlib's definition for integral elements, rather
than reproducing Holstein's prose definition as a new axiom or fake type.
The all-fields result does not pretend that the algebraic closure discussion
in9.6.3 supplies an original fully written general proof.
Every new declaration is mapped to its actual source unit in coverage.json;
the graph's edges are exclusively references from compiled types/values.
External dependencies omitted from the selected graph remain listed on each
node. Existing project signatures, types, values, axiom sets and graph edges
are checked unchanged. Source hashes and the immutable Git commit permit
reproduction. No independent human review is claimed.
