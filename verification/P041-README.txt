LA-P041 / Holstein §12.5 / printed183–188 / PDF185–190
Lean4.34.0; unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduce in the pinned source project:
  lake env python tools/verify-linear-algebra.py
This freshly compiles every local LA source and audits actual constant references and axioms.
No sorry, admit, native_decide, additional project axioms or simulated compiler checks.

CONVENTION
Holstein: linear FIRST, antilinear SECOND. Mathlib: opposite. holsteinInner x y = inner K y x.
For H_ij=h(b_i,b_j) and new basis columnsS: Hnew=S^T H conjugate(S).
Antilinear functionals E→ₗ⋆K represent the algebraic dual of the conjugate scalar module.
The finite antidual equivalence is proved using Riesz and continuity of every finite algebraic linear form.
No assertion about all algebraic functionals in infinite dimension is made.

Original12.5.18 lacks a needed hypothesis: the direct-sum theorem here explicitly assumes finite dimension.
The printed original is preserved separately, with a genuine polynomial-space counterexample.
Original proofs remain German native text. They need not use the identical proof strategy as Mathlib.
Browser parsers, diagrams, programs, floating-point normalization and numerical stability are NOT Lean-verified software.
General Gram–Schmidt, nonzero residuals, orthogonality, span preservation and orthonormalization ARE formal mathematical theorems for arbitrary finite families, not merely numerical examples.

EXACT SCOPE BY SOURCE UNIT

12.5.1
Inneres Produkt über RCLike (insbesondere R/C), ausdrücklich durch Vertauschen der Mathlib-Argumente an Holsteins linear-erste Konvention angepasst. Selbstwert gleich Normquadrat und Definitheit. Mathlib bündelt die verträgliche Normstruktur in InnerProductSpace; keine Verifikation der JavaScript-Software.
holsteinInner, holsteinInnerSelf, holsteinInnerDefinite

12.5.2 PARTIAL
Allgemeine Koordinatenformel des reellen Standardskalarprodukts in jeder endlichen Dimension einschließlich0. Der gesamte stetige Funktionenraum mit Integralskalarprodukt wird mathematisch erklärt; dessen allgemeine positive Definitheit ist hier nicht als eigene Lean-Konstruktion verpackt. Das konkrete Sinus-Kosinus-Integral wird bei12.5.11 formal geprüft.
holsteinStandardReal, holsteinStandardRealFormula

12.5.3
Allgemeine Additivität, Linearität im ersten und Antilinearität im zweiten Argument sowie hermitesche Symmetrie. Die Konvention ist ausdrücklich bewiesen; kein stillschweigender Tausch der Projektionskoeffizienten.
holsteinInnerAddFirst, holsteinInnerAddSecond, holsteinInnerLinearFirst, holsteinInnerAntilinearSecond, holsteinInnerHermitian

12.5.4 PARTIAL
Allgemeine komplexe Standardproduktformel Σvᵢkonjugiert(wᵢ), dazu i²=−1 als Gegenbeispiel gegen positive komplexe Bilinearität. Der volle komplexe stetige Funktionenraum ist keine eigene Lean-Instanz dieses Pakets.
holsteinStandardComplex, holsteinStandardComplexFormula, innerComplexBilinearNotPositive

12.5.5 PARTIAL
Allgemeine komplexe Matrixkoordinatenformel h(v,w)=vᵀHkonjugiert(w), kongruenter Basiswechsel H′=SᵀHkonjugiert(S) und Erhaltung hermitescher Symmetrie. Die Koordinatenidentität gilt sogar ohne Invertierbarkeit; für einen Basiswechsel prüft der Browser S⁻¹ tatsächlich. Die vollständige hermitesche Diagonalisierungsinduktion ist im Browser exakt geprüft, hier nicht als eigener allgemeiner Lean-Existenzsatz angelegt. Die gedruckte S*MS-Formel bleibt getrennt dokumentiert.
holsteinMatrixProduct, holsteinMatrixChange, holsteinMatrixCoordinates, holsteinMatrixHermitianChange

12.5.6
Kanonische lineare Abbildung auf den algebraischen Antidual E→ₗ⋆K (antilineare Funktionale aufE, äquivalent zu linearen Funktionalen auf dem konjugierten Skalarmodul). Allgemeine Injektivität und endlichdimensionale Surjektivität, daher LinearEquiv. Der Beweis nutzt Riesz plus automatische Stetigkeit aller endlichen algebraischen Linearformen; keine Gleichsetzung des unendlichen algebraischen Duals mit dem stetigen Dual. Die basisabhängige Koordinatenkonjugation wird separat erklärt und exakt getestet.
holsteinAntidualFunctional, holsteinAntidualMap, holsteinAntidualInjective, holsteinAntidualSurjective, holsteinAntidualEquiv

12.5.7
Allgemeine Nichtausgeartetheit aus positiver Definitheit für innere Produkte über R/C, ohne Endlichdimensionalität. Die terminologische Zusammenfassung euklidisch/unitär ist keine zusätzliche Strukturbehauptung.
holsteinInnerNondegenerate

12.5.8
Allgemeine Cauchy–Schwarz-Ungleichung sowie beide Gleichheitsfassungen: y=0 oder x ist ein skalares Vielfaches vony. Dies ist genau die lineare Abhängigkeit zweier Vektoren, einschließlich aller Nullfälle. Keine Beschränkung auf konkrete Matrizen oder endliche Dimension.
holsteinCauchySchwarz, holsteinCauchySchwarzSquared, holsteinCauchySchwarzEquality, holsteinCauchySchwarzSquaredEquality

12.5.9
Allgemeine absolute Homogenität, Definitheit und Dreiecksungleichung der von InnerProductSpace kompatibel getragenen Norm. Die komplexe Realteilkorrektur der gedruckten Rechnung wird separat erklärt; der Beweisstatus bezieht sich auf die korrekte Normaussage.
holsteinNormHomogeneous, holsteinNormTriangle, holsteinNormZero

12.5.10 PARTIAL
Orthogonalität als verschwindendes Holstein-Produkt. Winkel werden im Browser nur für reelle Nichtnullvektoren definiert. Eine allgemeine Winkeltheorie ist hier nicht separat formalisiert.
holsteinOrthogonal

12.5.11
Genaues Originalintegral ∫₀^π sin(t)cos(t)dt=0, mit dem vorhandenen Mathlib-Integralsatz und exakten Randwerten. Keine numerische Quadratur als Beweis.
holsteinSinCosIntegral

12.5.12
Allgemeine Existenz einer Orthonormalbasis jedes endlichdimensionalen reellen/komplexen inneren Produktraums, einschließlich Nullraum. Der Originalbeweis über Sylvester beziehungsweise hermitesche Diagonalisierung bleibt vollständig erhalten; Mathlibs allgemeine ONB-Konstruktion ist der formale Existenznachweis.
holsteinOrthonormalBasis

12.5.13
Orthonormale Familie wird exakt durch Mathlibs Orthonormal repräsentiert. Ein System muss keine Basis sein; die Erzeugung ist eine zusätzliche Eigenschaft.
holsteinOrthonormalFamily

12.5.14
Jede beliebig indizierte orthonormale Familie ist linear unabhängig, nicht nur die kleinen numerischen Browserfamilien.
holsteinOrthonormalIndependent

12.5.15
Allgemeine Rekonstruktion aus einer endlichen Orthonormalbasis mit den richtigen Holstein-Koeffizienten h(v,bᵢ). Keine versehentliche komplexe Konjugation.
holsteinOrthonormalCoordinates

12.5.16
Orthogonales Komplement sowohl eines Unterraums als auch einer beliebigen Teilmenge als tatsächlicher Submodule konstruiert. Null, Addition und auch die konjugierte Skalarmultiplikation sind bewiesen; keine Annahme, dass die beliebige Ausgangsmenge ein Unterraum ist.
holsteinComplement, holsteinComplementMem, holsteinSetComplement, holsteinSetComplementMem

12.5.17
Allgemeine Symmetrie der Orthogonalität im inneren Produkt. Für beliebige nicht symmetrische Bilinearformen wird diese Aussage nicht behauptet; dafür bleibt§12.3 maßgeblich.
holsteinOrthogonalSymm

12.5.18
Trivialer Schnitt allgemein; direkte Komplementarität und Dimensionssumme unter expliziter Endlichdimensionalität. Das Original lässt diese Voraussetzung in der Aussage aus, benutzt sie aber im Beweis. Die unbegrenzt allgemeine Druckaussage wird ausdrücklich nicht als bewiesen ausgegeben.
holsteinComplementDisjoint, holsteinComplementSum, holsteinComplementDimension

12.5.19
Orthogonale lineare Projektion in jedem endlichdimensionalen inneren Produktraum, Fixpunkte genauU, Rest inU⊥, beste Approximation und Formel für eine normierte Einzelrichtung. Die tatsächliche Matrix wird im Browser mit exakter Arithmetik berechnet; keine Softwareverifikation behauptet.
holsteinProjection, holsteinProjectionFixed, holsteinProjectionResidual, holsteinProjectionBest, holsteinProjectionUnit

12.5.20
Allgemeine endliche ONB-Projektionssumme mit h(v,bᵢ), Idempotenz, komplementäre Zerlegung und Selbstadjungiertheit. Das Komplement ist damit id−P; die Browsermatrix prüft beide Idempotenzprodukte und P(I−P)=0 separat exakt.
holsteinProjectionDecomposition, holsteinProjectionIdempotent, holsteinProjectionFormula, holsteinProjectionSelfAdjoint

12.5.21
Allgemeiner Gram–Schmidt-Prozess für beliebige endliche Familien in reellen/komplexen inneren Produkträumen: exakte Rekursionsformel in Holstein-Konvention, Nichtnullreste bei linearer Unabhängigkeit, Orthogonalität, Erhaltung des Spanns, normierte orthonormale Familie und gleicher Spann. Keine bloße Verifikation eines numerischen Beispiels. Die Browserimplementierung sowie Gleitkomma-Stabilität klassischer/modifizierter Verfahren sind unabhängig getestet, nicht Lean-verifizierte Software.
holsteinGramSchmidt, holsteinGramSchmidtNonzero, holsteinGramSchmidtOrthogonal, holsteinGramSchmidtSpan, holsteinGramSchmidtFormula, holsteinGramSchmidtNormed, holsteinGramSchmidtOrthonormal, holsteinGramSchmidtNormedSpan

12.5.22
Konkrete exakte rationale Restvektoren des Originals und diagonale Gram-Matrix mit Werten3,2/3,1/2. Die dritte Restkomponente korrigiert ausdrücklich den separat erhaltenen Druckfehler. Normierung durch √3/√6/√2 und die umgekehrte Reihenfolge werden exakt beziehungsweise mit kontrollierter numerischer Gram-Prüfung getestet; der allgemeine normierte Prozess ist bereits bei12.5.21 formal bewiesen.
innerOriginalVectors, innerOriginalRests, innerOriginalGram, innerOriginalSecondResidual, innerOriginalThirdResidual
