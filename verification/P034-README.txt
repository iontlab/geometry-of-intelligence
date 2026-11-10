LA-P034 — Holstein §10.3, printed152–154 / PDF154–156.

Reproduce with Lean4.34.0 and unchanged Mathlib5ed2965256430c3649e86755f9576b54eca72435:
  lake env python tools/verify-linear-algebra.py
All project declarations are freshly compiled; direct references in types/values and axioms are extracted. No sorry or additional project axioms.

10.3
Allgemein über jedem Körper: Die r-te Potenz des nilpotenten r×r-Jordanblocks mit oberer Nebendiagonale ist null. Verwendet die bereits vorhandene Jordanblockdefinition und den Satz für strikt obere Dreiecksmatrizen; kein neues oder dupliziertes Blockmodell.
Declarations: nilpotentBlockPowerZero

10.3.1
Kleinster verschwindender Exponent eines nilpotenten Endomorphismus über beliebigem Körper und seine Minimalität; zusätzlich ein konkretes nicht bereits in Jordanform gegebenes3×3-Beispiel über Q mit N³=0 und N²≠0. Nicht vollständig in Lean formalisiert: allgemeine Existenz einer kompatiblen Komplementfamilie, daraus einer Jordanbasis und vollständige nilpotente Jordan-Klassifikation. Der vollständige Originalbeweis und seine22 interaktiven Schritte bleiben erhalten; die Browserkonstruktion wird unabhängig getestet.
Declarations: nilpotentIndex, nilpotentIndexPower, nilpotentIndexMinimal, nilpotentExampleThree, nilpotentExampleCube, nilpotentExampleSquareNonzero

10.3.1.filtration
Über jedem Körper: U₀=0, U_d=V für den kleinsten verschwindenden Exponenten, Monotonie, echte Inklusion für i<d, g⁻¹(U_i)=U_(i+1) und g(U_(i+1))⊆U_i. Die Aussagen sind allgemein, keine endlichdimensionale Spezialfassung. Die Originaldruckfehler werden getrennt erläutert.
Declarations: nilpotentKernel, nilpotentKernelZero, nilpotentKernelTop, nilpotentKernelMonotone, nilpotentKernelPreimage, nilpotentKernelImage, nilpotentKernelStrict

10.3.1.komplemente
Allgemeine Zutaten: Existenz eines Komplements zu jedem Potenzkern, Injektivität von g auf W bei W∩U_i=0 und i>0 sowie Disjunktheit von g(W) und U_i aus W∩U_(i+1)=0. Die Existenz einer gleichzeitig rückwärts kompatiblen gesamten Familie W_i ist kein neuer vollständiger Lean-Satz. Insbesondere bedeutet die Existenz einzelner Komplemente noch nicht die Existenz einer Jordanbasis.
Declarations: nilpotentComplementExists, nilpotentInjectiveOnComplement, nilpotentImageDisjointLower

10.3.1.ketten
Allgemeine Potenzketten: Schrittgesetz, Zugehörigkeit zu den passenden Potenzkernen, Nichtverschwinden aller früheren Glieder aus einem nichtverschwindenden letzten Glied und Invarianz des von einer abbrechenden Kette erzeugten Raums. Keine behauptete formale gemeinsame Basiskonstruktion mehrerer Ketten. Ihre Unabhängigkeit, Erzeugung und konkreten Restriktionsmatrizen werden im Browser exakt geprüft.
Declarations: nilpotentChainStep, nilpotentChainInKernel, nilpotentChainFirstNonzero, nilpotentChainInvariant

10.3.1.eindeutigkeit
Signed second differences über Z: Differenzformel, Nichtnegativität unter ausdrücklich vorausgesetzter abnehmender Zuwachsfolge, Eindeutigkeit der daraus definierten Zahlen und gewichtete Teleskopsumme. Zusätzlich ist die gewichtete Summe der zweiten Differenzen der tatsächlichen Potenzkerndimensionen eines nilpotenten Endomorphismus gleich dim V formal bewiesen. Nicht behauptet: vollständige formale Herleitung der Nichtnegativität dieser tatsächlichen zweiten Differenzen oder ihre Identifikation mit existierenden Jordanblöcken ohne den noch nicht formalisierten kompatiblen Basissatz. Die vollständige Originalargumentation zur Blockeindeutigkeit bleibt in Mathematics und Proof Steps.
Declarations: kernelProfileMultiplicity, kernelProfileDifference, kernelProfileNonnegative, kernelProfileUnique, kernelProfileWeightedSum, kernelProfileTotalDimension, nilpotentKernelDimensions, nilpotentKernelProfileWeightedDimension

10.1.2.beweis
Allgemein über jedem Körper: T(λI+N)S=λI+TNS unter der expliziten Voraussetzung TS=I. Damit ist das skalare Verschiebungsargument des Originalbeweises formal geprüft. Dies ist keine vollständige Formalisierung der Existenz und Eindeutigkeit der allgemeinen Jordan-Normalform unter der Zerfallsvoraussetzung. Die Hauptraumzerlegung wird mit den bestehenden Formalisierungen verknüpft; deren zusätzliche IsAlgClosed-/PerfectField-Voraussetzungen werden nicht versteckt. Die zweite Originalfundstelle wird derselben Aussage10.1.2 zugeordnet und nicht als neuer Satz gezählt.
Declarations: jordanShiftConjugation

10.3.2
Allgemeines Matrixzertifikat über jedem Körper: Aus SB=I und AB=BJ folgt SAB=J. Dies ist eine konditionale Basiswechselprüfung, kein Existenzsatz für B, S oder J und keine vollständige formale Jordan-Klassifikation. Das Browsermodul konstruiert eine Basis und prüft die Inverse und die gesamte Ähnlichkeitsgleichung konkret; es wird dadurch nicht zu einem formal verifizierten Programm.
Declarations: jordanBasisCertificate

The full original proof and browser construction do not imply full formal Jordan classification. The browser algorithm and all JavaScript are tested separately and are not formally verified programs. The pinned source archive preserves all preceding package notes.
