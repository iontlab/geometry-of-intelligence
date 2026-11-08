LA-P026: Holstein §§7.6 Orientierungen, 7.7 Minoren, 7.8 Spur.
Lean 4.34.0; unchanged pinned Mathlib 5ed2965256430c3649e86755f9576b54eca72435.
Reproduce from source archive: lake env python tools/verify-linear-algebra.py
This compiles all project modules freshly, extracts declaration type/value references and audits axioms.

28 authored declarations in OrientationsMinorsTrace.lean; generated compiler declarations are counted separately.
The orientation construction uses the actual quotient of ordered bases, not merely the sign set. The quotient is equivalent to Bool and has cardinality two under positive dimension and an existing finite basis. Fin n uses zero-based indices. The zero-dimensional quotient is not claimed to have two elements.
The orientation-preserving automorphisms are an actual Subgroup with the requisite closure proofs.
Minor results are genuinely general over a field, but only the nonzero-minor rank bound and vanishing above rank are formalized. The converse existence direction in 7.7.3 is not formally proved here. Browser enumeration is separate evidence and never replaces that general theorem.
Trace results are general: linearity, matching rectangular cyclic products, similarity, transpose and finite-basis independence. The source errors in 7.8.2/3 are preserved in Mathematics and separately explained; the Lean statements use the correct mathematics.
No claim that JavaScript, SVG interaction, all source examples or the entire source proof text has been formally verified. No sorry and no additional axioms. Existing standard classical axioms are listed per declaration in the audit.
Graph edges are extracted direct type/value references; source/didactic correspondences are separate metadata.
