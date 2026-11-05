LA-P008 — Holstein §2.3 Körper AND §2.4 Die komplexen Zahlen

The binding package plan includes both sections: printed40–44/PDF42–46,
9 numbered units. This explicitly differs from the suggested §2.3-only scope
in the task. The plan has precedence as requested; §2.5 is excluded.

Lean4.34.0; unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduction: lake env python tools/verify-linear-algebra.py
No lake update or new toolchain is required. Fresh local oleans are built into
verification/rebuild and used by ExtractLinearGraph.lean. Types, proof values,
direct constants and axiom dependencies are recorded in compiled.json/audit.json.
No sorry, admit, native_decide or additional project axioms are accepted.
Standard foundational axioms propext, Classical.choice and Quot.sound are
allowed and enumerated per declaration. No didactic dependency edges.

34 authored declarations:29 theorems and5 definitions. Compiler-generated
helpers are counted separately in the actual compiler audit.
K is an arbitrary Field with no characteristic-zero restriction.
Own proofs of zero multiplication, no zero divisors, multiplication by minus
one and cancellation explicitly use the relevant group/distributive arguments.
Full Field structures for ZMod2,ZMod3 and Complex reuse pinned Mathlib instances.
The concrete integer/rational and composite-modulus counterexamples compile.
Complex numbers use their re/im coordinate representation. The inverse is
expressed via conjugation/normSq and is checked as a true inverse only for z≠0.
Conjugation, norm-square, product norm and triangle inequality are certified.
The coordinatewise real-pair multiplication counterexample is separate from
complex multiplication.

Holstein uses arg in[0,2π), whereas Complex.arg uses(-π,π]. The own function
complexArgumentPositive adds2π for a negative Mathlib angle. Range and polar
reconstruction are proved. Its formal total value at0 is a convention; the
geometric UI correctly displays argument(0) as undefined. No global continuity
or certificate for the JavaScript atan2 implementation is claimed. The complete
uniqueness theorem for the polar angle is not separately formalized here.

Original anomalies remain visible: additive wording for multiplicative groups;
extra open parenthesis in2.4.1; a^1+b^2 and missing left grouping in2.4.2;
unusual source reference in2.4.4. Only explicitly explained, well-formed
interpretations are compiled. As in the source, associativity/distributivity
in the complex-field proof are marked as exercises; their iLab elaborations
and existing Mathlib verification are identified separately.

The finite axiom checker and SVG diagrams are tested browser programs, not
formally verified implementations. No complete formalization of every sentence
or every numerical experiment is claimed. Exact per-source mapping is provided
by coverage.json and the Lean/Verification views.
