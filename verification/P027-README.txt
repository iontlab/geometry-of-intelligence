LA-P027 – Holstein Kapitel8, gedruckt120–122 / PDF122–124.
Lean4.34.0; unverändertes Mathlib5ed2965256430c3649e86755f9576b54eca72435.

Reproduktion im vorhandenen gepinnten Projekt:
lake env python tools/verify-linear-algebra.py
Der Prüfer baut jede lokale LA-Datei in verification/rebuild frisch, extrahiert
Deklarationstypen, direkte Referenzen in Typen und Werten und die Axiomabhängigkeiten.
Keine sorry/admit/native_decide, keine zusätzlichen Projektaxiome.
Erlaubte Standardaxiome: propext, Classical.choice, Quot.sound.
Konkrete endliche Prüfungen benutzen kernelgeprüftes decide, kein native_decide.

CodingTheory.lean: 45 selbst geschriebene Deklarationen.
Allgemein: Hamming-Abstand auf F2^n, alle vier Abstandseigenschaften,
Korrigierbarkeitsbedingung, Eindeutigkeit naher Kodewörter, lineare Kodes,
Kardinalität2^dim, Kontrollabbildung mit KernC und Ziel F2^(n−dimC),
Eindeutigkeit kleiner Fehler mit gleichem Syndrom, Dekodierung unter tatsächlich
eingehaltenem Fehlerbudget. n0, Nullkode und Gesamtraum sind eingeschlossen.
Die Existenz der Koordinatenkontrolle wird über den Quotienten und gleiche
Dimension bewiesen; nicht der konkrete Basisergänzungsalgorithmus formalisiert.

Konkret: exakt gedruckte Generator-/Kontrollmatrix des(7,4)-Kodes überZMod2;
HG^T0, systematische Kodierung, Injektivität, Kern=Bild, Dimension4,
Mindestabstand3 durch alle Paare und konkreten Gleichheitszeugen,
acht Syndromfälle einschließlich Null und sichere Dekodierung bis Fehlergewicht1.
Die allgemeine Hamming-Familie für beliebigesr, asymptotische Datenrate und
Hardwareaussagen sind nicht formalisiert. Die anwendungsbezogene Betrachtung
8.0.5 erhält keine künstliche Deklaration.

Originalfehler bleiben ausschließlich in der unveränderten Originalansicht;
Lean beweist die getrennt erläuterten korrekten Aussagen, insbesondere keine
Dekodiergarantie aus bloßer Zulässigkeit des Syndroms und kein Gewicht3 für
sämtliche Generatorzeilen oder Linearkombinationen.
Die JavaScript-Matrix-, Gauß-, Distanz- und Decoderimplementation ist nicht durch
diese mathematischen Lean-Beweise formal verifiziert. Eigenständige vollständige
endliche Tests und unabhängige Paritäts-/Distanzorakel prüfen die Browserrechnung.
