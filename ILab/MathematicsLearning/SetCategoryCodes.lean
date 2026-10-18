import ILab.MathematicsLearning.SetIndexedFamilies
import ILab.MathematicsLearning.SetCategoryModels

/-! Injective set codes for the complete data of a strict category. The
object set, hom family, identities and composition are all retained. The
universe estimates use precisely the source's four closure properties. -/
namespace ILab.MathematicsLearning.SetCategory
universe u
open SetIndexedFamily

noncomputable def allHoms {U : ZFSet.{u}} (C : SetCategory U) : ZFSet.{u} :=
  ZFSet.iUnion (fun x : C.objects => ZFSet.iUnion (fun y : C.objects => C.hom x y))

theorem hom_subset_allHoms {U : ZFSet.{u}} (C : SetCategory U) (x y : C.objects) :
    C.hom x y ⊆ allHoms C := by
  intro f hf
  exact ZFSet.mem_iUnion.mpr ⟨x, ZFSet.mem_iUnion.mpr ⟨y, hf⟩⟩

theorem allHoms_mem {U : ZFSet.{u}} (hU : SetUniverse U) (C : SetCategory U) : allHoms C ∈ U :=
  hU.unions _ C.objects_mem _ (fun x =>
    hU.unions _ C.objects_mem _ (fun y => C.hom_mem x y))

noncomputable def homCode {U : ZFSet.{u}} (C : SetCategory U) : ZFSet.{u} :=
  graph C.objects (fun x => graph C.objects (C.hom x))

noncomputable def identityCode {U : ZFSet.{u}} (C : SetCategory U) : ZFSet.{u} :=
  graph C.objects (fun x => (C.identity x).val)

noncomputable def compositionCode {U : ZFSet.{u}} (C : SetCategory U) : ZFSet.{u} :=
  graph C.objects (fun x => graph C.objects (fun y => graph C.objects (fun z =>
    graph (C.hom x y) (fun f => graph (C.hom y z) (fun g => (C.compose f g).val)))))

noncomputable def code {U : ZFSet.{u}} (C : SetCategory U) : ZFSet.{u} :=
  ZFSet.pair C.objects (ZFSet.pair (homCode C) (ZFSet.pair (identityCode C) (compositionCode C)))

theorem code_injective (U : ZFSet.{u}) : Function.Injective (@code U) := by
  rintro ⟨O, hO, hom, hhom, id, comp, hi, hc, ha⟩
    ⟨P, hP, hom', hhom', id', comp', hi', hc', ha'⟩ h
  obtain ⟨hOP, hrest⟩ := ZFSet.pair_inj.mp h
  cases hOP
  obtain ⟨hhomcode, hrest⟩ := ZFSet.pair_inj.mp hrest
  have hehom : hom = hom' := by
    funext x
    exact graph_injective O (congrFun (graph_injective O hhomcode) x)
  cases hehom
  obtain ⟨hidcode, hcompcode⟩ := ZFSet.pair_inj.mp hrest
  have heid : id = id' := by
    funext x
    exact Subtype.ext (congrFun (graph_injective O hidcode) x)
  cases heid
  have hecomp : @comp = @comp' := by
    funext x y z f g
    apply Subtype.ext
    have h₁ := congrFun (graph_injective O hcompcode) x
    have h₂ := congrFun (graph_injective O h₁) y
    have h₃ := congrFun (graph_injective O h₂) z
    have h₄ := congrFun (graph_injective (hom x y) h₃) f
    exact congrFun (graph_injective (hom y z) h₄) g
  cases hecomp
  rfl

theorem code_mem {U : ZFSet.{u}} (hU : SetUniverse U) (C : SetCategory U) : code C ∈ U := by
  apply hU.orderedPair_mem C.objects_mem
  apply hU.orderedPair_mem
  · exact graph_mem hU C.objects_mem _ (fun x =>
      graph_mem hU C.objects_mem _ (fun y => C.hom_mem x y))
  · apply hU.orderedPair_mem
    · exact graph_mem_of_values hU C.objects_mem (allHoms_mem hU C) _
        (fun x => hom_subset_allHoms C x x (C.identity x).property)
    · exact graph_mem hU C.objects_mem _ (fun x =>
        graph_mem hU C.objects_mem _ (fun y =>
          graph_mem hU C.objects_mem _ (fun z =>
            graph_mem hU (C.hom_mem x y) _ (fun f =>
              graph_mem_of_values hU (C.hom_mem y z) (C.hom_mem x z) _
                (fun g => (C.compose f g).property)))))

theorem smallOfUniverse {U : ZFSet.{u}} (hU : SetUniverse U) : Small.{u} (SetCategory U) :=
  small_of_injective (f := fun C : SetCategory U => (⟨code C, code_mem hU C⟩ : U)) (by
    intro C D h
    exact code_injective U (congrArg (fun x : U => x.val) h))

noncomputable def codes {U : ZFSet.{u}} (hU : SetUniverse U) : ZFSet.{u} :=
  letI := smallOfUniverse hU
  ZFSet.range (@code U)

noncomputable def codeEquiv {U : ZFSet.{u}} (hU : SetUniverse U) : SetCategory U ≃ codes hU := by
  letI := smallOfUniverse hU
  exact Equiv.ofBijective (fun C => ⟨code C, ZFSet.mem_range_self C⟩)
    ⟨by
      intro C D h
      exact code_injective U (congrArg (fun x : codes hU => x.val) h), by
      intro x
      obtain ⟨C, hC⟩ := ZFSet.mem_range.mp x.property
      exact ⟨C, Subtype.ext hC⟩⟩

theorem codes_subset {U : ZFSet.{u}} (hU : SetUniverse U) : codes hU ⊆ U := by
  let := smallOfUniverse hU
  intro x hx
  obtain ⟨C, rfl⟩ := ZFSet.mem_range.mp hx
  exact code_mem hU C

theorem codes_mem {U V : ZFSet.{u}} (hU : SetUniverse U) (hV : SetUniverse V)
    (hUV : U ∈ V) : codes hU ∈ V := hV.subsets U hUV _ (codes_subset hU)

/-- Every U-bounded category is literally small when viewed in V. -/
def enlarge {U V : ZFSet.{u}} (hUV : U ⊆ V) (C : SetCategory U) : SetCategory V where
  objects := C.objects
  objects_mem := hUV C.objects_mem
  hom := C.hom
  hom_mem x y := hUV (C.hom_mem x y)
  identity := C.identity
  compose := C.compose
  identity_comp := C.identity_comp
  comp_identity := C.comp_identity
  associative := C.associative

/-- Conversely, a source-small category retains all its data in U. -/
def restrict {U V : ZFSet.{u}} (C : SetCategory V) (hC : C.IsSmall U) : SetCategory U where
  objects := C.objects
  objects_mem := hC.1
  hom := C.hom
  hom_mem := hC.2
  identity := C.identity
  compose := C.compose
  identity_comp := C.identity_comp
  comp_identity := C.comp_identity
  associative := C.associative

theorem enlarge_restrict {U V : ZFSet.{u}} (hUV : U ⊆ V)
    (C : SetCategory V) (hC : C.IsSmall U) : enlarge hUV (restrict C hC) = C := by
  cases C
  rfl

theorem enlarge_small {U V : ZFSet.{u}} (hUV : U ⊆ V) (C : SetCategory U) :
    (enlarge hUV C).IsSmall U := ⟨C.objects_mem, C.hom_mem⟩

end ILab.MathematicsLearning.SetCategory
