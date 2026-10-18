# Mathematics Learning — verification record

The two new modules compile in the existing iLab Lake project. Only the named ordinary-category results and constructions below are checked. The full lecture notes, Synthetic Category Theory, infinity-category theory, HoTT, and set-universe existence are not formalized here. The general Yoneda lemma, adjunction correspondence and equivalence criterion are outside this formalization.

## Reproduction

Pinned Lean 4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`); Mathlib v4.34.0 (`5ed2965256430c3649e86755f9576b54eca72435`); Lake 5.0.0-src. Use the existing `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`; no dependency update is required.

From a checkout with the pinned dependencies and cache available:

```sh
lake clean rq001
lake build
lake env lean tools/ExtractLearningGraph.lean
SOURCE_REF=5f45eee29afa3c7507eb9a56bb132ccb92260e68 node tools/build-learning-graph.mjs
```

`rq001` is the existing root Lake package name. Cleaning it removes its build products while retaining the pinned dependency cache. All six source modules are then rebuilt; the four original RQ-001 modules are unchanged. The clean build completed with exit 0 (8930 jobs); existing RQ-001 stylistic linter suggestions were emitted, with no errors. No warning suppression or proof-checking bypass was added. For PowerShell, set `$env:SOURCE_REF='5f45eee29afa3c7507eb9a56bb132ccb92260e68'` before running Node.

The learning extractor is the original compiler auditor with only its imports, namespace prefix and output path changed. It rejects namespace axiom declarations, admitted expressions in types or values, and any transitive axiom dependency outside `propext`, `Classical.choice`, `Quot.sound`. The metadata builder retains the original source-hash, prohibited-token, dependency-resolution and authored-declaration completeness checks. It additionally requires an exact source commit and validates every curated graph mapping. No existing extractor or RQ-001 evidence was overwritten. Scoped LF Git attributes keep new verified source bytes reproducible across platforms.

## Audit results

73 compiled declarations, including 20 authored declarations, passed. All declarations (including generated constructors, recursors, instances and helpers) were checked. The raw dependency dataset has 237 direct local edges. External Mathlib references are excluded from the graph, but their transitive axioms are included in the axiom audit. Definitions with proof fields are compiler checked; an object-type definition is not described as a new mathematical theorem.

See [clean-build.log](clean-build.log), [declaration-audit.log](declaration-audit.log), [all-declaration-axioms.txt](all-declaration-axioms.txt), [source-hashes.json](source-hashes.json), [declaration-mapping.json](declaration-mapping.json), and the raw [compiled declarations](../../../docs/formalization/mathematics-learning/compiled.json). The full signatures and direct dependencies are available in the interactive inspector.

## Authored declaration mappings

All names below have prefix `ILab.MathematicsLearning.`. Each row compiled and passed the complete axiom audit.

| Declaration | Primary item | Exact checked scope | Source |
| --- | --- | --- | --- |
| `identity_padded_composite` | 1.5 | A composable pair is unchanged after inserting identities | [BasicCategoryTheory.lean:22](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L22) |
| `inverse_unique` | 1.11 | A right inverse and a left inverse of the same arrow agree | [BasicCategoryTheory.lean:27](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L27) |
| `mapped_inverse_left` | 1.14 | A functor preserves the first inverse equation | [BasicCategoryTheory.lean:36](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L36) |
| `mapped_inverse_right` | 1.14 | A functor preserves the second inverse equation | [BasicCategoryTheory.lean:42](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L42) |
| `mappedIso` | 1.14 | Package the two mapped arrows as an isomorphism | [BasicCategoryTheory.lean:48](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L48) |
| `mappedIso_eq_mapIso` | 1.14 | The construction equals Mathlib Functor.mapIso | [BasicCategoryTheory.lean:55](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L55) |
| `composite_naturality` | 1.20 / 1.23 | Vertical composition satisfies naturality | [BasicCategoryTheory.lean:61](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L61) |
| `vertical_composite_component` | 1.23 | Functor-category composition has the stated components | [BasicCategoryTheory.lean:73](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L73) |
| `Room` | 3.8 | Inductive object type with north and south constructors | [WalkingIsomorphism.lean:16](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L16) |
| `roomFintype` | 3.8 | Complete finite enumeration of the two objects | [WalkingIsomorphism.lean:21](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L21) |
| `OneRoom` | 1.25 | Inductive object type with one constructor | [WalkingIsomorphism.lean:25](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L25) |
| `roomCategory` | 3.8 | Small category with singleton hom types on Room | [WalkingIsomorphism.lean:29](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L29) |
| `oneRoomCategory` | 1.25 | Small category with singleton hom types on OneRoom | [WalkingIsomorphism.lean:34](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L34) |
| `roomIso` | 3.8 | Explicit isomorphism between each ordered pair of rooms | [WalkingIsomorphism.lean:40](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L40) |
| `includeRoom` | 3.9 | Functor selecting north from the one-object category | [WalkingIsomorphism.lean:45](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L45) |
| `collapseRoom` | 3.9 | Functor collapsing both rooms to the sole object | [WalkingIsomorphism.lean:50](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L50) |
| `walkingEquivalence` | 3.4 / 3.9 | Explicit bundled adjoint equivalence, including a triangle law | [WalkingIsomorphism.lean:55](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L55) |
| `inclusion_not_surjective` | 3.6 / 3.9 | The inclusion is not literally surjective on objects | [WalkingIsomorphism.lean:65](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L65) |
| `inclusion_essentially_surjective` | 3.6 / 3.9 | Every room is isomorphic to the selected image object | [WalkingIsomorphism.lean:72](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L72) |
| `room_cardinality` | 3.8 | The object type Room has exactly two elements | [WalkingIsomorphism.lean:76](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L76) |

## Mathematical and foundational boundaries

- The primary uses `g ∘ f`; Lean uses `f ≫ g` for that composite. Object and hom universes are independent in `BasicCategoryTheory`. Lean universes are not the primary's assumed set universes.
- The inverse-uniqueness lemma names the right and left inverses in the opposite order to the wiki proof; both statements are explicitly typed and imply uniqueness of a two-sided inverse.
- `mappedIso` is an educational construction whose equality with Mathlib's existing `Functor.mapIso` is checked. It does not claim novelty.
- `walkingEquivalence` satisfies Mathlib's additional triangle requirement. Primary Definition 3.4 requires only a quasi-inverse and natural isomorphisms. The finite example uses singleton hom types and explicit witnesses, not the general choice-based equivalence criterion.
- `room_cardinality` uses ordinary `decide` with a proved finite enumeration. No native evaluation shortcut is used.
- The source's 3.7 proof is deferred. The wiki's independently supplied classical proof sketch is not a Lean proof.

The mathematical exposition was reviewed by the authoring assistant against the three supplied sources. Independent human peer review is not claimed. Source PDFs and full extracted texts remain private and are excluded from GitHub and deployment.
