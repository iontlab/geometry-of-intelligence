LA-P022: complete original §§7.1–7.2, printed99–105/PDF101–107.
Lean4.34.0; unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduce: lake env python tools/verify-linear-algebra.py
40 authored declarations. No sorry, added axioms or native_decide.
Full 7.1 algebraic symmetry, bilinearity, cross-product convention, cyclic
triple product, alternation and normalization. Euclidean L2 representation
WithLp.toLp2 explicitly corresponds to coordinate inner product and norm;
never use the Pi sup norm. Basis parallelotopes are sets, not pictures.
Cross-norm angle identity uses the actual Mathlib Euclidean theorem.
Mathlib has a total angle at zero; the browser deliberately displays no
geometric angle when a factor is zero.
Geometric area/volume measure, signed height interpretation, handedness,
perspective SVGs and browser algorithms are not formally verified programs.
7.1.8 proves only an explicitly delimited algebraic base-height identity.
D1–D3 are stated for arbitrary unbundled functions on n×n matrices over any
field. Their conversion to AlternatingMap and uniqueness use the standard
basis in arbitrary finite dimension. All five rules in7.2.3 then hold for
any function satisfying the original axioms. This proof route differs from
the separately preserved original elementary-row-operation proof.
The existing canonical Mathlib determinant is a library foundation, not a
new presentation of the original §7.3 existence proof. That section remains
reserved for LA-P023. Three models1D/2D/3D and exact complex result3i checked.
2×2 nonadditivity is proved over all fields, including characteristic2;
the original I₂+I₂ example needs a separate editorial restriction.
Own graph edges come only from actual compiled type/value constant references.
Detailed per-unit scope: coverage.json and the five Explain layers.
