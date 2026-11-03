Linear Algebra verification record – Holstein pp. 71–77

Toolchain: Lean 4.34.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b
Mathlib: 5ed2965256430c3649e86755f9576b54eca72435
The existing iLab toolchain and dependency lockfile are retained.

Reproduction in the source repository at the published source commit:
  lake exe cache get
  lake build ILab.LinearAlgebra
  lake env python tools/verify-linear-algebra.py

The second command builds the isolated ILab.LinearAlgebra namespace.
The third command creates fresh project oleans in verification/rebuild,
prioritizes them on LEAN_PATH, recompiles every LA source module, then runs
tools/ExtractLinearGraph.lean against those freshly compiled declarations.
The existing pinned Mathlib oleans are reused, not claimed as a fresh rebuild
of all Mathlib. Python 3 and the same git checkout of Mathlib are required.

The resulting verification/compiled.json records actual Lean-environment
types, direct type/value constant references and recursive axiom dependencies.
The extractor rejects project axioms, admitted expressions, and axioms other
than propext, Classical.choice and Quot.sound. These three standard foundations
are reported per declaration; they are not new assumptions introduced by iLab.

75 local compiled declarations include 60 authored definitions/theorems and
15 compiler-generated declarations. 61 explicitly selected library declarations
are extracted as a mathematically relevant bounded Mathlib excerpt.

Viewer edges are exactly the direct type/value references whose endpoints
are included. No transitive bridges or didactic prerequisite edges are added.
Source-unit mappings and graph grouping are authored presentation metadata.
The complete omitted direct references remain in externalDependencies.

Compilation validates the Lean statements under their explicit assumptions.
Their correspondence with Holstein is a separate source audit, not a
compiler-certified translation of German prose. The original mathematical
text is preserved. Definitions, proved general theorems and proved concrete
examples are distinguished in the source-unit coverage record.

The geometric JavaScript models use rounded coordinates and are not themselves
formally verified by these Lean declarations.
