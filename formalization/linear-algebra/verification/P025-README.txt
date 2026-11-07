LA-P025 – Holstein §7.5, Permutationen und Determinanten

27 neue eigene Deklarationen:24 Theoreme,3 Definitionen. Lean4.34.0;
unverändertes gepinntes Mathlib5ed2965256430c3649e86755f9576b54eca72435.
Reproduktion: lake env python tools/verify-linear-algebra.py.
Der Prüfer kompiliert sämtliche lokalen Quellen in verification/rebuild neu
und extrahiert tatsächliche Typ-, Wert- und Axiomreferenzen. Keine sorry,
admit, native_decide oder unbegründeten zusätzlichen Projektaxiome.

Wesentliche Konvention: holsteinPermutationEntry beweist
Eσ[i,j]=if i=σ(j) then1 else0. Mathlibs direkte permMatrix hat die inverse
Orientierung. holsteinPermutationMatrix verwendet Matrix.permMatrixHom,
das ausdrücklich σ⁻¹ in permMatrix einsetzt. Matrixprodukt entspricht
σ∘τ mit zuerst τ. IntegerPermutationSign hat Ziel Zˣ, keine Signumdefinition
allein im Körper. signCollapseCharacteristicTwo prüft den Kollaps in ZMod2.

Kardinalität und Komposition verwenden die bestehenden Deklarationen
permutationCard und permutationComposition aus LA-P006; keine Doppelung.
Neu formalisiert sind inverse
Transpositionen und Produktzerlegung, Permutationsmatrixkonvention und
Homomorphie, Determinante der Permutationsmatrix, abstraktes Signum und
Multiplikativität, Faktorparität und Unabhängigkeit der Zerlegung,
alternierende Gruppe als Kern samt korrekten Kardinalitäten, eine alternative
Vorzeichenproduktformel über geordnete Paare, zeilenorientierte Leibnizformel
und2×2/3×3-Fälle sowie Blockdeterminante/Blockpermutationssignum.

Die Kardinalitätsformel A_n=n!/2 setzt Nontrivial(Fin n), äquivalent n≥2,
explizit voraus. A1 hat separat nachgewiesen ein Element. Die allgemeine
Nichtkommutativität von S_n/A_n wird nicht neu formalisiert; konkrete
Gegenbeispiele werden unabhängig im Browser geprüft. Die rationale Formel
aus7.5.6 ist nicht vollständig neu formalisiert: Die Lean-Aussage dort ist
ausdrücklich die alternative Produktformel aus±1-Faktoren nach Paarordnung.
Die interaktive rationale Quotientenformel arbeitet exakt in Q; keine
unzulässige Division durch j−i in beliebigen endlichen Körpern.

Leibniz: Das allgemeine Resultat ist in Holsteins Reihenfolge A[i,σ(i)]
bewiesen, verwendet aber Mathlibs Determinantendefinition mit Transposition.
Dies ist keine eigene formale Kopie sämtlicher ursprünglicher D1-/D2-
Zwischenrechnungen. Originaltext, didaktischer Navigator, Lean-Identität
und separat getestetes JavaScript sind getrennte Nachweise.

Blockdeterminante: Nullblock exakt Teil der Aussage. Blockindexmenge
Fin n₁ ⊕ Fin n₂; kanonische Blockindizierung statt Fin(n₁+n₂). Mathlibs
allgemeiner Satz gilt auch für leere Blöcke, Holsteins n_i≥1 sind enthalten.

Keine formale asymptotische Software-Komplexitätsanalyse.7.5.9 hat keine
künstliche neue Lean-Deklaration. Holsteins Kostenmodell, BigInt-Modellwerte
und instrumentierte Kennzahlen des Browsers werden getrennt angezeigt.
Keine Behauptung, JavaScript, SVG oder sämtliche Originalargumente seien
formal verifiziert. Kein zusätzliches unbegründetes Axiom.
