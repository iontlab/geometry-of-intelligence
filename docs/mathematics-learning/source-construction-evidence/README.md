# G1–G10 source-record repairs

The preserved implementation adds 31 raw-data declarations and definitional formula readbacks at Lean source commit `ebde0f04b46bc3cfa906d06b749e4954549f545c`. It reuses existing representations and corrects the Section 3 introduction link. No assigned category, functor, naturality, inverse or triangle check is solved. G8 deliberately exposes only the reversed-composition formula; its missing opposite-isomorphism premise remains assigned. The complete Yoneda lemma and representable adjunction theorem are not source-verified.

`source-repairs.json` lists each repair, exact declaration mapping, scope and withheld obligations. `new-declarations.json` contains all 31 compiler-derived signatures and dependencies. All 785 prior declarations and 97 prior narrative contents remain unchanged, including PR #14's four Yoneda declarations. The primary manuscript, eight chapter sources, dependency pins, RQ-001 and shared plugin entry point are preserved.

The clean build passed 8962 jobs; compiler extraction records 816 declarations, 427 authored declarations, 4030 direct edges and 34 modules. Source coverage remains 29 fully verified numbered items, 15 exercise-affected items and zero eligible pending items. Local validation passed 290 source-panel checks, 225 graph-panel checks, 235 inline-panel checks, 28 navigation checks, 41 PHP binding/isolation checks and 17 capacity checks. Publication/live evidence will be recorded separately after deployment.

The serialized registry is 503551 bytes, including all signatures, bindings and scope metadata. The shared `capacity.json` starts at 5000000 UTF-8 bytes and 5000 records; headroom is 4496449 bytes. Its digest is bound to the release. Browser streaming and PHP bounded reads reject oversized payloads; schema depth, per-record limits, source freshness, ACL and hash checks remain enforced. No mathematics or existing narrative was shortened for capacity.

Capacity is configured once for the learning registry rather than edited separately in browser, server and build tools. Ordinary additions within this headroom need no limit adjustment. At sustained growth near 70% of the budget, measure transfer/parse time and memory on target devices; propose chapter-indexed, hash-bound on-demand records before further large increases. Such a loading change requires separate approval and is not implemented here. The existing architecture is retained. The synthetic 5 MB / 750-record Node V8 parse-and-validation measurement is recorded in `capacity-tests.json`; it is not a browser or network timing claim.


Publication is complete. See [the final live publication report](PUBLICATION-REPORT.md) and `publication.json` for merge provenance and complete verification results.
