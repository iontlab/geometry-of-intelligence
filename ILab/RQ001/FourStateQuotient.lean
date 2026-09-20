import Mathlib

/-!
# RQ-001 Phase I — Four-State Quotient Model

A Lean 4 / Mathlib formalization of the finite model used in
"Frame-Relative Structure in the Search for an Intelligence Criterion".

The file formalizes the mathematical core of Proposition 2
(strict refinement by update probes) and Proposition 3
(failure of descent of the update operation to the coarse task quotient).

The representation is deliberately elementary: the coarse task quotient is
represented by the observable response-mode bit `q : Bool`. This avoids
introducing quotient-type machinery before it is needed, while proving the
same descent obstruction exactly.
-/

namespace ILab.RQ001

/-- Microstate `x_{q,p}`.  `q` is the current response mode and `p` is the
latent update-sensitivity bit. -/
structure State where
  q : Bool
  p : Bool
  deriving DecidableEq, Repr, Fintype

/-- Ordinary task output.  When `q = false`, the system returns the input;
when `q = true`, it returns the Boolean complement. -/
def taskOut : Bool → Bool → Bool
  | false, u => u
  | true,  u => !u

@[simp] theorem taskOut_false (q : Bool) : taskOut q false = q := by
  cases q <;> rfl

/-- The mode after the designated update signal. -/
def updatedQ : Bool → Bool → Bool
  | q, false => q
  | q, true  => !q

/-- The designated update operation `U_ℓ(x_{q,p}) = x_{q⊕p,p}`. -/
def update (s : State) : State :=
  ⟨updatedQ s.q s.p, s.p⟩

@[simp] theorem update_q (s : State) : (update s).q = updatedQ s.q s.p := rfl
@[simp] theorem update_p (s : State) : (update s).p = s.p := rfl

/-- Task-only output word.  Ordinary task inputs do not change the state. -/
def taskOutputs (s : State) (w : List Bool) : List Bool :=
  w.map (taskOut s.q)

/-- Equality under every finite task-only probe word. -/
def TaskEq (s t : State) : Prop :=
  ∀ w : List Bool, taskOutputs s w = taskOutputs t w

/-- Task equivalence remembers exactly the response-mode bit `q`. -/
theorem taskEq_iff_q_eq (s t : State) : TaskEq s t ↔ s.q = t.q := by
  constructor
  · intro h
    have h0 := h [false]
    simpa [taskOutputs] using h0
  · intro hq w
    simpa [taskOutputs, hq]

/-- Full input language: ordinary task inputs plus the designated update. -/
inductive Input where
  | task (u : Bool)
  | update
  deriving DecidableEq, Repr

/-- Observable outputs.  The update emits one common acknowledgment symbol. -/
inductive Output where
  | bit (b : Bool)
  | updateAck
  deriving DecidableEq, Repr

/-- State transition for one full-language input. -/
def stepState : State → Input → State
  | s, .task _ => s
  | s, .update => update s

/-- Observable output for one full-language input. -/
def emit : State → Input → Output
  | s, .task u => .bit (taskOut s.q u)
  | _, .update => .updateAck

/-- Observable output word produced by a finite full-language input word. -/
def outputs : State → List Input → List Output
  | _, [] => []
  | s, i :: is => emit s i :: outputs (stepState s i) is

/-- Equality under every finite word in the enriched language. -/
def FullEq (s t : State) : Prop :=
  ∀ w : List Input, outputs s w = outputs t w

/-- For fixed `q`, the pair consisting of current `q` and post-update `q`
uniquely determines the latent bit `p`. -/
theorem updatedQ_injective_in_p (q p₁ p₂ : Bool)
    (h : updatedQ q p₁ = updatedQ q p₂) : p₁ = p₂ := by
  cases q <;> cases p₁ <;> cases p₂ <;> simp [updatedQ] at h ⊢

/-- The observable pair `(current q, post-update q)` uniquely determines a
microstate. -/
theorem state_eq_of_q_and_updated_q_eq {s t : State}
    (hq : s.q = t.q)
    (hu : (update s).q = (update t).q) : s = t := by
  cases s with
  | mk sq sp =>
      cases t with
      | mk tq tp =>
          simp only at hq
          subst tq
          have hp : sp = tp := by
            apply updatedQ_injective_in_p sq sp tp
            simpa [update] using hu
          subst tp
          rfl

/-- The enriched probe language distinguishes all four microstates. -/
theorem fullEq_iff_eq (s t : State) : FullEq s t ↔ s = t := by
  constructor
  · intro h
    have hqObs := h [Input.task false]
    have hq : s.q = t.q := by
      simpa [outputs, emit, stepState] using hqObs

    have huObs := h [Input.update, Input.task false]
    have hu : (update s).q = (update t).q := by
      simpa [outputs, emit, stepState] using huObs

    exact state_eq_of_q_and_updated_q_eq hq hu
  · intro h
    subst t
    intro w
    rfl

/-- Enriched equivalence always implies task-only equivalence. -/
theorem fullEq_implies_taskEq {s t : State} (h : FullEq s t) : TaskEq s t := by
  have hst : s = t := (fullEq_iff_eq s t).mp h
  subst t
  intro w
  rfl

/-- Two concrete states with identical task behavior but different latent
update sensitivity. -/
def x00 : State := ⟨false, false⟩
def x01 : State := ⟨false, true⟩
def x10 : State := ⟨true, false⟩
def x11 : State := ⟨true, true⟩

/-- `x00` and `x01` are indistinguishable under task-only probes. -/
theorem x00_taskEq_x01 : TaskEq x00 x01 := by
  rw [taskEq_iff_q_eq]
  rfl

/-- `x00` and `x01` are distinguished by the enriched probe language. -/
theorem x00_not_fullEq_x01 : ¬ FullEq x00 x01 := by
  intro h
  have hEq : x00 = x01 := (fullEq_iff_eq x00 x01).mp h
  have hp : x00.p = x01.p := congrArg State.p hEq
  simp [x00, x01] at hp

/-- Proposition 2, relational form:
`FullEq` is a strict refinement of `TaskEq`. -/
theorem strict_refinement :
    (∀ {s t : State}, FullEq s t → TaskEq s t) ∧
    (∃ s t : State, TaskEq s t ∧ ¬ FullEq s t) := by
  constructor
  · intro s t h
    exact fullEq_implies_taskEq h
  · exact ⟨x00, x01, x00_taskEq_x01, x00_not_fullEq_x01⟩

/-- The coarse task quotient is represented canonically by the observable
response-mode bit. -/
def taskClass (s : State) : Bool := s.q

/-- The task-class map identifies exactly the task-equivalent states. -/
theorem taskClass_eq_iff_taskEq (s t : State) :
    taskClass s = taskClass t ↔ TaskEq s t := by
  simpa [taskClass] using (taskEq_iff_q_eq s t).symm

/-- Proposition 3 — Failure of descent.

There is no function on coarse task classes whose value agrees with applying
`update` at the microstate level and then projecting back to the task class.
Equivalently, the update operation is not well-defined on the task quotient.
-/
theorem no_update_descends :
    ¬ ∃ f : Bool → Bool, ∀ s : State, f (taskClass s) = taskClass (update s) := by
  rintro ⟨f, hf⟩

  have h00 : f false = false := by
    simpa [x00, taskClass, update, updatedQ] using hf x00

  have h01 : f false = true := by
    simpa [x01, taskClass, update, updatedQ] using hf x01

  have hfalse_true : false = true := h00.symm.trans h01
  cases hfalse_true

/-- The four concrete microstates exhaust `State`. -/
theorem state_cases (s : State) : s = x00 ∨ s = x01 ∨ s = x10 ∨ s = x11 := by
  cases s with
  | mk q p =>
      cases q <;> cases p <;> simp [x00, x01, x10, x11]

/-- There are exactly four microstates. -/
theorem card_state : Fintype.card State = 4 := by
  decide

end ILab.RQ001
