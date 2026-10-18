# Learning graph and explanation provenance

The existing RQ-001 viewer and its actual deployed five-layer renderer were inspected before adaptation; the live assets differ from the older repository copy. The learning viewer reuses that behavior, with learning-only source bindings and a scoped extension of the existing `ilabexplain` plugin approved by the user. RQ-001 handlers and live assets are preserved.

- Mathematical Blueprint: 109 mapped declarations and 70 direct visible compiler edges.
- Full Lean Graph: 116 authored declarations and 80 visible edges initially; 225 compiled declarations and 428 edges with generated declarations enabled.
- Five-layer graph explanations: 37 principal results. Supporting declarations link explicitly to their main result. Technical helpers receive only meaningful layers.
- Source inspector: all 58 source items, including assigned statements with their solutions withheld. These records are not invented graph nodes.
- Wiki: 47 inline controls across the existing eight lessons, bound to actual headings and exact source revisions.

Every graph edge is a direct constant reference extracted from a compiled Lean type or value. Hidden nodes are not bridged by fictional edges. External references are retained in the downloadable data and audited transitively for foundational axioms, but are not drawn as project-local nodes.

`mathematics.json` and the explanation registry are independently authored teaching metadata. The graph adapter matches exact signatures, source hashes, commit IDs and dataset hashes. The wiki adapter requires server attestation of the exact page fragment and the current raw-source digest. Publication authorization does not claim independent human editorial review. Stale or inconsistent bindings fail closed.

Local preview uses only public-source fixtures. Production freshness uses the approved learning status handler. Deployment uses WebFTP; `docs/` is not an automatic publication service. No private PDFs, full extracted source texts, credentials or unrelated hosting configuration are included.
