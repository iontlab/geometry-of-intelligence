LA-P042 — Holstein §12.6 Adjungierte Abbildungen
Original: printed188–190 / PDF190–192, nine numbered units12.6.1–9.
Only this section; §12.7 remains unpublished except the requested brief outlook.

Lean4.34.0, unchanged pinned Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduce from linear-algebra-lean-source.zip:
lake env python tools/verify-linear-algebra.py
Fresh project oleans are compiled into verification/rebuild. The extractor reads
actual compiled declaration types, values, direct constant references and axioms.
Only propext, Classical.choice and Quot.sound are allowed. No sorry, admit,
native_decide, project axioms or fabricated verification.

Conventions and scope:
Holstein: linear FIRST, conjugate-linear SECOND.
Mathlib: conjugate-linear first, linear second.
holsteinInner x y := inner K y x is imported unchanged from LA-P041.
holsteinAdjointIdentity proves exactly h_W(w,f(v))=h_V(f†(w),v).
The general existence/uniqueness, involution, composition, sum and conjugate
scalar laws concern arbitrary finite-dimensional real/complex inner product
spaces. Matrix representation is proved for arbitrary rectangular ONB indices,
including empty indices, not merely 2×2 examples.

The ordinary algebraic dual map and its transpose matrix are separate from
the matrix star and the inner-product-dependent adjoint. The algebraic antidual
is represented by semilinear functionals E→ₗ⋆K. J sends a linear functional to
its pointwise conjugate. Its conjugate scalar law records the conjugated dual
action; this is not a claim that an ordinary complex linear form is antilinear.
Lean does not introduce another named type alias for the conjugated dual.
The ONB statement identifies entire functionals through J.

The original real diagram is generalized explicitly to the complex antidual.
It is proved as equality of linear maps and as the resulting factorization.
The annihilator theorem is a genuine set-image equality for arbitrary sets;
the kernel/range statements are genuine submodule equalities, not dimension
checks. Both orthogonal direct decompositions and rank equality are proved.

Weighted-coordinate extension: with Holstein h(x,y)=xᵀH conjugate(y),
BᵀH_V=H_W conjugate(A), equivalently H_VᵀB=A*H_Wᵀ.
The invertible source transpose G is passed explicitly as a matrix unit;
G B=A*H_Wᵀ and uniqueness of B=G⁻¹A*H_Wᵀ are algebraically proved.
This is not a fresh Lean positivity-decision algorithm for entered Gram
matrices. The browser checks their positive hermitian structure using the
existing exact engine; 160 independent exact Fraction complex-pair reference
cases solve the defining equations separately. The concrete complex matrix,
its adjoint and inequality to its transpose are also Lean-proved.

Original errors remain in Mathematics and are separately documented. In
particular the ill-typed membership sign in the existence proof, wrong basis
names, wrong composition test-vector spaces and missing inverse on tau in
the annihilator proof are not silently edited. The printed proof order is kept.

No claim of formal verification of the JavaScript engine, parser, SVG diagrams,
browser UI or numerical pictures. Mathematical verification and software tests
are distinct. All previous package boundaries and formal limitations remain.
