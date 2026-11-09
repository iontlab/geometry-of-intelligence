LA-P033 – Reproduction and exact formal scope

Lean4.34.0, Mathlib5ed2965256430c3649e86755f9576b54eca72435. No upgrades.
Run lake env python tools/verify-linear-algebra.py from the source project.
This builds every local source anew, then extracts actual type/value references and axioms.
Only propext, Classical.choice and Quot.sound are allowed; no sorry or project axioms.

Original source: Holstein §§10.1–10.2, printed148–152/PDF150–154, stop before10.3.
Original diagram reconstructed as a transparent SVG with original arrow directions.
Ten numbered units and two introductions, all original proofs and exercise references.

Exact formal scope per mapped unit:

10.1.1: Allgemeine Jordanblockdefinition mit oberer Nebendiagonale über beliebigem Körper, obere Dreiecksgestalt und charakteristisches Polynom(X−λ)^r. Der exakte Minimalgrad eines allgemeinen Blocks und die vollständige Jordan-Normalform-Klassifikation sind keine neuen Lean-Sätze dieses Pakets. Konkrete Ketten und Minimalpolynome werden im Browser exakt geprüft.

10.2.1: Holsteins Hauptraum ist über beliebigem Körper bei endlicher Dimension exakt ker((f−λid)^dimV); die Gleichheit mit Mathlibs endlichem und maximalem verallgemeinertem Eigenraum und f-Invarianz sind bewiesen. Die Formel gilt formal auch für Skalare, die keine Eigenwerte sind; dort ist der Raum null.

10.2.2: Nilpotenz ist Existenz einer verschwindenden Potenz. X^d annulliert dann den Endomorphismus und wird vom Minimalpolynom geteilt. Die verschobene Einschränkung auf einen endlichen verallgemeinerten Eigenraum ist nilpotent. Kein behaupteter Nachweis der JavaScript-Potenzberechnung.

10.2.3: Allgemein über jedem Körper bei endlicher Dimension: monotone Kerne, antitone Bilder, Existenz einer stabilen Stelle≤dimV, kleinster Kernstabilisierungsindex mit Minimalitätsgesetz, spätere Kern-/Bildstabilität, Invarianz beider Räume, Rang-Nullität und echte direkte Summe ker g^d⊕Im g^d für jede stabile Stelle einschließlich d=0. Nicht als vollständig formalisiert ausgewiesen: Isomorphismus der konkreten Einschränkung auf W, exakter Minimalpolynomexponent der Einschränkung auf U, Ungleichung dimU≥d und vollständiger sechsteiliger Originalbeweis. Die allgemeine Hauptraumdimensionsformel ist separat bei10.2.5 bewiesen; Browserexperimente prüfen alle sechs Eigenschaften konkret.

10.2.4: Allgemeines charakteristisches Produkt für externe direkte Summen endlichdimensionaler Räume über beliebigem Körper. Der Transport einer beliebigen invarianten inneren direkten Summe zu dieser externen Darstellung ist hier keine zusätzliche eigene Lean-Deklaration. Das Original enthält nur den Übungsverweis; der vollständige zusätzliche Blockdeterminantenbeweis ist als iLab-Ergänzung gekennzeichnet.

10.2.5: Allgemeine Hauptraumdimension=algebraische Vielfachheit, Disjunktheit und Unabhängigkeit über jedem Körper. Die formale Erzeugendenaussage verwendet ausdrücklich die stärkere Voraussetzung IsAlgClosed; sie ist nicht als vollständiger Nachweis unter Holsteins bloßer Zerfallsvoraussetzung ausgewiesen. Verwandte Jordan-Chevalley-Existenz über PerfectField liefert kommutierende semisimple/nilpotente Anteile; semisimpel wird nicht mit diagonalisierbar über beliebigem K gleichgesetzt. Das zusätzliche3×3-iLab-Beispiel über Q hat formal geprüfte Summe, Kommutation und Nilpotenz. Keine vollständige formale Jordan-Klassifikation oder vollständiger induktiver Originalbeweis wird behauptet.

10.2.6: Verwandter allgemeiner Eindeutigkeitssatz über PerfectField für semisimple/nilpotente kommutierende Anteile. Dies ist nicht als identischer Nachweis der diagonalisierbaren Originalfassung unter bloßer Zerfallsvoraussetzung ausgewiesen. Die Originalbemerkung enthält keinen Beweis; Existenz, Eindeutigkeit und vollständige Jordanklassifikation bleiben getrennte Behauptungen.

10.2.7: Über beliebigem Körper ist die r-te Potenz jeder oberen r×r-Dreiecksmatrix mit Nulldiagonale null; Beweis mit dem bereits vorhandenen charakteristischen Dreiecksprodukt und Cayley-Hamilton. Die allgemeine Existenz der gesamten Primärblock-Basis unter Holsteins Zerfallsvoraussetzung ist nicht als neuer vollständiger Lean-Beweis ausgewiesen. Das Rechenmodul verwendet die vorhandene Trigonalisierung und prüft die berechneten Basiswechsel und strikt oberen Blöcke konkret.

Unmapped introductions10.1/10.2, announcement10.1.2 and original block example10.1.3 retain transparent unformalized status. The announced full Jordan existence/uniqueness proof is reserved for10.3.
Browser programs, parsing, SVG and exhaustive finite experiments are tested, not formally verified code.
