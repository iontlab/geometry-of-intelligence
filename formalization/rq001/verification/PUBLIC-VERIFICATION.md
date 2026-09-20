# Public-project verification — 2026-09-21

PASS. All four unchanged final modules compiled together in a fresh clone using the public Git dependency configuration. No mathematical content or verified source bytes changed during publication preparation.

- Lean 4.34.0, x86_64-w64-windows-gnu, Release; commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib v4.34.0; Git HEAD `5ed2965256430c3649e86755f9576b54eca72435`.
- Build command: `lake build`; exit 0; **Build completed successfully (8928 jobs).**
- [Complete final output](clean-build.log), including cosmetic linter warnings retained to preserve source bytes.

The project had newly resolved public Git dependencies and no copied project compilation artifacts. Official Mathlib cache archives supplied library artifacts; unavailable artifacts were built locally. Windows archive extraction initially encountered file-lock conflicts while setup processes overlapped. Those processes ended before the successful final ordinary Lake build. No `--old` option, proof-check bypass, local path dependency, or source workaround was used for this public-project build.

## Combined compiler audit and graph extraction

Command: `lake env lean tools/ExtractGraph.lean` (exit 0).

```text
PASS: extracted and audited 202 project declarations from compiled Lean types and values.
```

Command: `node tools/build-graph.mjs` (exit 0).

```text
PASS: 202 compiled declarations; 79 authored nodes; 627 direct project-local edges; all source hashes and axiom dependencies checked.
```

Every compiled declaration under `ILab.RQ001`, including compiler-generated declarations, was audited. See [exact per-declaration axiom dependencies](all-declaration-axioms.txt). The extractor rejects project axiom declarations, `hasSorry` in types or values, and any transitive axiom dependency other than `propext`, `Classical.choice`, or `Quot.sound`. A separate source-token scan and exact SHA-256 comparison passed for all four files.

Confirmed zero: `sorry`, `admit`, `sorryAx`, project-added axioms, `native_decide` auxiliary axioms, and hidden admitted propositions in the audited namespace. Foundational Lean axioms are reported as dependencies, not project-added assumptions. The graph dataset uses the same compiler audit results; historical named-declaration audits are retained alongside this report.

The final universal property compiles with existence, uniqueness, naturality, pointwise surjectivity, and probe-factorization assumptions intact:

```lean
∃! h : Z ⟶ transformationQuotientFunctor X Probe Obs eval,
  a ≫ h = transformationQuotientNatTrans X Probe Obs eval
```

The historical reports describe earlier compilation-only repairs. This publication made no further edits to any of the four verified Lean source files. The graph extractor is new tooling and is separate from the mathematical modules.
