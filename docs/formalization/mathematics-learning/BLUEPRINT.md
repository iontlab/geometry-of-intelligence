# Mathematics Learning graph provenance

This is the existing RQ-001 static graph implementation, with only dataset location, namespace prefix, group names, explanatory labels and lesson links adapted. `style.css` retains the original style rules; new artifact text uses LF line endings. The rendering, layout, filtering, search, zoom, inspector tabs, keyboard behavior and compiler-edge selection are unchanged. `mathematics-view.js` permits each curated result to link to its canonical DokuWiki lesson.

The two original graph modes remain distinct:

- Mathematical Blueprint: 15 curated declaration mappings and 7 direct visible compiler edges. `mathematics.json` is independently authored educational prose with AI assistance; it is not compiler output.
- Full Lean Graph: 20 authored declarations and 34 visible edges initially. The generated-declaration toggle exposes all 73 compiled declarations and 237 raw local edges. The existing renderer does not draw self edges (0 in the raw data).

Every edge is a direct constant reference from a compiled type or value. Hiding nodes does not invent replacement paths. External Mathlib references are excluded from the visualization; their transitive axiom dependencies are audited. A sparse graph is not missing a conceptual arrow: mathematical relationships are not automatically direct Lean dependencies.

The sibling `tools/ExtractLearningGraph.lean` retains every original compiler check. `tools/build-learning-graph.mjs` retains source-hash and metadata checks and adds exact-commit and curated-ID validation. Original RQ-001 tools and data are untouched. New declarations live only in `ILab.MathematicsLearning` in the same Lake project.

Serve this directory via HTTP for local inspection. Production deployment is the existing authenticated Hetzner WebFTP procedure into `public_html/formalization/mathematics-learning/`. Committing `docs/` is not a deployment. No PDFs, private source extracts, hosting credentials, wiki configuration, RQ-001 files or new server code are included.
