# RQ-001 Phase I — Lean Formalization

Selected mathematical results from “Frame-Relative Structure in the Search for an Intelligence Criterion.”

Selected mathematical results from RQ-001 Phase I are Lean-verified. This is a partial formalization of the mathematical core, not a formalization of RQ-001 as a whole.

RQ-001 remains open. The [research note](https://iontlab.org/doku.php?id=research:rq001_phase_i) remains [Draft]. No intelligence predicate is proved. The categorical theorem concerns coherent abstraction under stated assumptions, not a categorical definition of intelligence.

## Verified modules

| Module | Scope and authored paper mapping |
| --- | --- |
| [FourStateQuotient](../../ILab/RQ001/FourStateQuotient.lean) | M3.1: task equivalence, enriched separation and strict refinement; M3.2: failure of update descent. The state type has four elements. Exact quotient cardinality equations are not separate named Lean theorems. |
| [CapabilityOrder](../../ILab/RQ001/CapabilityOrder.lean) | M1.1: capability preorder, quotient partial order, and realized profiles. Part of M1.2: capability monotonicity implies extensionality, conditionally; intelligence monotonicity is not assumed or proved. |
| [SymmetryObstruction](../../ILab/RQ001/SymmetryObstruction.lean) | M5.1: a transitive action permits only empty or universal invariant subsets. |
| [TransformationSufficientQuotient](../../ILab/RQ001/TransformationSufficientQuotient.lean) | M4.1: transformation-sufficient quotient functor, natural quotient map, probe factorization, and the full unique-factorization universal property. |

The modules are formally independent: each imports Mathlib, not another RQ-001 module. M5.2, M1.3, generic M2.1/M2.2, M6, M7 and M8.1 are not claimed Lean-verified. No novelty or Higher Category Theory claim is made.

## Reproduce the build

Install Elan/Lean from the official Lean distribution, then run from the repository root:

```sh
lake update
lake exe cache get
lake build
lake env lean tools/ExtractGraph.lean
node tools/build-graph.mjs
```

The toolchain is Lean **4.34.0**, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. Mathlib is **v4.34.0**, exact Git revision `5ed2965256430c3649e86755f9576b54eca72435`. The public Git dependency and generated manifest pin the dependency graph; no local Mathlib checkout path is required. Node.js 18 or later is used only to enrich graph metadata; it is not part of Lean proof checking.

A fresh public-project configuration compiled all four source modules with ordinary `lake build` (exit 0). The verified source bytes were unchanged. [Complete final build output](verification/clean-build.log), [public verification report](verification/PUBLIC-VERIFICATION.md), [source hashes](verification/source-hashes.json), and [all 202 declaration axiom dependencies](verification/all-declaration-axioms.txt) are included. Earlier final module reports and audits are retained as labelled historical evidence in [verification](verification/).

The compiler audit rejects namespace axiom declarations, admitted expressions, and any dependency outside `propext`, `Classical.choice`, and `Quot.sound`. There are zero `sorry`, `admit`, `sorryAx`, project-added axioms, or `native_decide` auxiliary axioms. These three permitted foundational axioms are not project-added assumptions.

## Interactive declaration graph

[Open the interactive formalization graph](https://iontlab.org/formalization/rq001/).

The [extractor](../../tools/ExtractGraph.lean) imports the compiled modules and records direct constant references from declaration types and values. It also collects transitive axiom dependencies for every namespace declaration. The [metadata builder](../../tools/build-graph.mjs) verifies the original source hashes and adds source locations and explicitly human-authored module-level paper mappings. [compiled.json](../../docs/formalization/rq001/compiled.json) is raw compiler output; [data.json](../../docs/formalization/rq001/data.json) is the display dataset.

The graph has 202 compiled declarations and 627 direct local edges. Its default view shows the 79 explicitly named source declarations; compiler-generated helpers are available by toggle. Mathlib references are excluded. Hiding nodes does not invent replacement edges. Grouping, source-line matching, and paper mappings are authored metadata, not additional formal proofs.

The graph displays formal declaration dependencies and verification metadata. Graph position or centrality does not indicate mathematical importance, novelty, or intelligence relevance.

The static HTML/CSS/JavaScript/SVG implementation is repository-local, with no third-party website code, CDN, analytics or trackers. Serve `docs/formalization/rq001/` over HTTP(S); loading `index.html` directly as a file may block its JSON request.
