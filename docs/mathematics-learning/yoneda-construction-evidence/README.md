# Yoneda 2.1: author-supplied construction data

The original 13-page Moser–Walde manuscript, page 9, supplies the forward map alpha -> alpha_c(id_c) and candidate inverse components (alpha_u)_x(f) = F(f)(u). Lean checks these two functions in the existing set-universe representation and their two defining equations. The candidate is deliberately not packaged as a natural transformation.

The first assigned check (well-defined natural transformation / naturality) and the second assigned check (mutual inverseness and naturality in c and F) remain open. No complete Yoneda equivalence or theorem is exported. The existing representable functor is a reused prerequisite, not a newly solved exercise.

Release r12 passed the clean compiler audit (8961 jobs), source-fidelity and exercise-boundary checks, graph/release integrity and 28 navigation tests. Live tests passed: 235 wiki layer checks, 195 graph layer checks, 116 source narrative checks, all four new declaration scope checks, 45 asset hashes and eight unchanged chapter bindings. All 781 earlier declarations, the existing 96 narratives (including corrected inverse story), original manuscript, shared plugin, dependency pins and RQ-001 remain unchanged.

See publication.json for exact commits and counts, release-checks.log for offline checks, live-integrity.json for deployed hashes, and the panel/graph JSON and screenshot for browser evidence. The previous release evidence remains historical and unchanged.
