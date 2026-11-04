LA-P001 — reproducible verification, 4 November 2026

Source: Julian Holstein, Lineare Algebra 2023/24, edition 10 August 2024,
printed pages 2–10 / PDF pages 4–12, ending before section 1.3.

Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b).
Mathlib v4.34.0 (5ed2965256430c3649e86755f9576b54eca72435).
Neither toolchain nor dependency versions were upgraded.

From the checked-out project containing lakefile.toml and lake-manifest.json:
  lake exe cache get
  lake env python tools/verify-linear-algebra.py

The checker writes fresh project oleans to verification/rebuild and prepends
that directory to LEAN_PATH. It compiles all six LA source files, then runs
tools/ExtractLinearGraph.lean against those compiled declarations.
The extraction reads direct constant references in the type and value of
each declaration and recursively checks axiom dependencies. Completed
declarations contain no sorry, no new project axioms, and use only the
audited standard axioms propext, Classical.choice, Quot.sound as applicable.
The audit and complete compilation log record source hashes and exit codes.

Preparation.lean adds genuine definitions and mathematical results for
parameter lines, equivalent parametrizations (1.2.6), lines through distinct
points (1.2.7), both coefficient cases of a linear equation (1.2.8), midpoint
identities (1.2.9), parallelograms (1.2.10), common diagonal midpoint (1.2.11),
and concurrence and uniqueness of the triangle centroid (1.2.13).
Addition commutativity and scalar distributivity are checked foundations
for the elementary calculations (1.2.2).

Scope / representation differences:
* The ambient space V may be any real vector space where the proof does
  not use coordinates. This includes every R^n in the original.
* parametricLine p v is defined even at v=0; zeroDirection proves that it
  is a singleton. Theorems about actual lines require nonzero directions.
* The midpoint agrees with Mathlib's affine midpoint. The common diagonal
  midpoint is proved without a nondegeneracy assumption; uniqueness is
  deliberately not claimed for degenerate parallelograms.
* For the centroid, LinearIndependent R ![b-a,c-a] expresses non-collinearity
  of the three vertices. Existence of the mean and membership in the three
  parameter sets are proved without this assumption; uniqueness explicitly
  requires it. In R^2 this is exactly the nondegenerate-triangle condition.
  The formal uniqueness proof compares the two coefficients in this
  independent pair; the original proof instead uses uniqueness of a line
  through two points. Both prove the same statement, with the difference
  in proof method documented here rather than conflated.
* Holstein's misprints b-a=2m (1.2.9) and the final sign in 1.2.8 are
  preserved in the original-text layer but corrected in the formal results.
* Lean Fin n indices start at 0, whereas the printed coordinates start at 1.

Formal graph edges are extracted direct references only. Selected Mathlib
nodes expose a bounded relevant library excerpt; omitted direct references
remain documented. There are no invented/transitive/didactic graph edges.
The browser's finite floating-point geometry is not verified by these
mathematical Lean results. No claim of formal verification of all prose,
all 13 numbered units, or the entire lecture script is made.

The existing Dimensions, BasisMaps, MatrixAlgebra and Rotations sources
remain unchanged. RQ-001 and HCT source modules remain unchanged.
