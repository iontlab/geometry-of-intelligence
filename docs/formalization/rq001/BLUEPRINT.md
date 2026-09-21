# Graph modes

The main URL defaults to **Mathematical Blueprint**. `?view=lean` opens **Full Lean Graph**. Switching modes is local and resets graph filters and zoom; the declaration inspector remains available.

- `mathematics.json` is human-authored mathematical presentation mapped to Lean declarations. Its statements and proofs are not extracted from Lean.
- `data.json` contains the compiler-derived declaration graph and existing audit/source metadata. Neither graph mode changes this data.
- Blueprint visibility is exactly the keys of `mathematics.json.declarations` (24 declarations at introduction). The four display group names in `blueprint-view.js` are curated presentation metadata. Layout uses the existing rank algorithm on the visible direct dependencies.
- Blueprint edges are exactly `data.edges` whose source and target are both visible after mode, module and search filtering (25 edges with no filters). There is no transitive closure, contraction through hidden helpers, or conceptual edge generation.
- Full Lean Graph preserves the existing graph layout, controls, authored/generated filtering, search, inspector and counts. Generated declarations remain hidden initially. Its 627-edge full-data count includes one self-reference, which the existing renderer does not draw.
- Selecting an unmapped dependency from the inspector opens Full Lean Graph so its declaration remains accessible. No Mathematics view is invented.

No additional mathematics metadata or duplicate statements are introduced. Grouping and graph position do not imply mathematical importance, novelty or intelligence relevance.
