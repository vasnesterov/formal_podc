import Papers.PODC2019.ComposableCRN.Basic

-- CSLib candidate: Cslib/Computability/ChemicalReactionNetworks/Automaton.lean
/-!
# Leader-automaton CRNs

The constructions of Theorem 3.1 and Lemma 6.1 share one pattern: a single leader moves through
finitely many auxiliary states `L_q`; it reacts with one input molecule at a time,
`L_q + X_i → δ(q, i) Y + L_{q'}`, and outputs the finite difference of the target function. We
prove this pattern correct once.

Given `Φ : ℕ^ι → ℕ` nondecreasing in each coordinate and an abstraction `h : ℕ^ι → Q` into a
finite set of states such that `h c` determines both the finite differences
`Φ (c + eᵢ) - Φ c` and the next state `h (c + eᵢ)`, the CRN

* `L → Φ(0) Y + A_{h 0}`,
* `A_q + X_i → δ(q, i) Y + A_{next(q, i)}`

is output-oblivious and stably computes `Φ` (`obliviouslyComputable_of_automaton`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ComposableCRN

namespace Automaton

/-- Species of the leader-automaton CRN. -/
inductive Sp (ι Q : Type) where
  | X (i : ι)
  | Y
  | L
  | A (q : Q)
  deriving DecidableEq

/-- `Sp ι Q ≃ ι ⊕ Bool ⊕ Q`, for the `Fintype` instance. -/
def Sp.equiv (ι Q : Type) : Sp ι Q ≃ ι ⊕ Bool ⊕ Q where
  toFun
    | .X i => .inl i
    | .Y => .inr (.inl true)
    | .L => .inr (.inl false)
    | .A q => .inr (.inr q)
  invFun
    | .inl i => .X i
    | .inr (.inl true) => .Y
    | .inr (.inl false) => .L
    | .inr (.inr q) => .A q
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with i | (_ | _) | q <;> rfl

instance (ι Q : Type) [Fintype ι] [Fintype Q] : Fintype (Sp ι Q) :=
  Fintype.ofEquiv _ (Sp.equiv ι Q).symm

variable {ι Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Q] [DecidableEq Q]
  (Φ : (ι → ℕ) → ℕ) (h : (ι → ℕ) → Q)

/-- The unit vector `eᵢ`. -/
abbrev e (i : ι) : ι → ℕ := Pi.single i 1

open Classical in
/-- A representative input vector of a state (any, if the state is not reachable). -/
noncomputable def rep (q : Q) : ι → ℕ := if hq : ∃ c, h c = q then hq.choose else 0

/-- Output of the transition from state `q` on input `i`. -/
noncomputable def out (q : Q) (i : ι) : ℕ := Φ (rep h q + e i) - Φ (rep h q)

/-- Next state. -/
noncomputable def nxt (q : Q) (i : ι) : Q := h (rep h q + e i)

theorem h_rep (c : ι → ℕ) : h (rep h (h c)) = h c := by
  have hq : ∃ c', h c' = h c := ⟨c, rfl⟩
  simp only [rep, hq, dite_true]
  exact hq.choose_spec

/-- The initial reaction `L → Φ(0) Y + A_{h 0}`. -/
def initR : Reaction (Sp ι Q) where
  reactants := Pi.single .L 1
  products := Pi.single .Y (Φ 0) + Pi.single (.A (h 0)) 1

/-- The transition reaction `A_q + X_i → δ(q,i) Y + A_{next(q,i)}`. -/
noncomputable def stepR (q : Q) (i : ι) : Reaction (Sp ι Q) where
  reactants := Pi.single (.A q) 1 + Pi.single (.X i) 1
  products := Pi.single .Y (out Φ h q i) + Pi.single (.A (nxt h q i)) 1

/-- The leader-automaton CRN. -/
noncomputable def crn : FunCRN (Sp ι Q) ι where
  reactions := {initR Φ h} ∪ Set.range (fun p : Q × ι => stepR Φ h p.1 p.2)
  finite := (Set.finite_singleton _).union (Set.finite_range _)
  X := .X
  Y := .Y
  L := some .L
  X_injective _ _ h := by cases h; rfl
  Y_ne_X _ := by simp
  L_ne_X := by simp
  L_ne_Y := by simp

/-- The configuration after the leader has consumed the inputs `c ≤ x`. -/
def good (x c : ι → ℕ) : Config (Sp ι Q) := fun s =>
  match s with
  | .X i => x i - c i
  | .Y => Φ c
  | .L => 0
  | .A q => if q = h c then 1 else 0

theorem init_eq (x : ι → ℕ) :
    (crn Φ h).init x = fun s => match s with
      | .X i => x i
      | .L => 1
      | _ => 0 := by
  funext s
  cases s with
  | X i =>
    have := (crn Φ h).inputConf_X x i
    rw [show (crn Φ h).X i = Sp.X i from rfl] at this
    rw [FunCRN.init, Pi.add_apply, this]
    simp [FunCRN.leaderConf, crn]
  | Y => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, crn]
  | L => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, crn]
  | A q => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, crn]

variable {Φ h}

theorem terminal_good (x : ι → ℕ) : (crn Φ h).Terminal (good Φ h x x) := by
  rintro ρ (rfl | ⟨⟨q, i⟩, rfl⟩) hle
  · have := hle .L
    simp [initR, good] at this
  · have := hle (.X i)
    simp [stepR, good] at this

section

variable (hmono : ∀ c i, Φ c ≤ Φ (c + e i))
  (hdiff : ∀ c c', h c = h c' → ∀ i,
    Φ (c + e i) - Φ c = Φ (c' + e i) - Φ c' ∧ h (c + e i) = h (c' + e i))
include hmono hdiff

theorem good_step {x c : ι → ℕ} {i : ι} (hi : c i < x i) :
    good Φ h x c - (stepR Φ h (h c) i).reactants + (stepR Φ h (h c) i).products =
      good Φ h x (c + e i) := by
  have hout : out Φ h (h c) i = Φ (c + e i) - Φ c := by
    rw [out, (hdiff _ _ (h_rep h c) i).1]
  have hnxt : nxt h (h c) i = h (c + e i) := by
    rw [nxt, (hdiff _ _ (h_rep h c) i).2]
  have hm := hmono c i
  funext s
  cases s with
  | X j =>
    by_cases hj : j = i
    · subst hj; simp [good, stepR, e]; omega
    · simp [good, stepR, e, hj]
  | Y => simp [good, stepR, hout]; omega
  | L => simp [good, stepR]
  | A q' =>
    simp only [good, stepR, hnxt, Pi.add_apply, Pi.sub_apply, Pi.single_apply, Sp.A.injEq]
    by_cases h1 : q' = h c <;> by_cases h2 : q' = h (c + e i) <;> simp [h1, h2]

theorem step_good {x c : ι → ℕ} {D : Config (Sp ι Q)} (hs : (crn Φ h).Step (good Φ h x c) D) :
    ∃ i, c i < x i ∧ D = good Φ h x (c + e i) := by
  obtain ⟨ρ, hρ, hle, rfl⟩ := hs
  rcases hρ with rfl | ⟨⟨q, i⟩, rfl⟩
  · have := hle .L
    simp [initR, good] at this
  · dsimp only at hle ⊢
    have hA := hle (.A q)
    have hX := hle (.X i)
    simp only [stepR, good, Pi.add_apply, Pi.single_eq_same, ne_eq, reduceCtorEq,
      not_false_eq_true, Pi.single_eq_of_ne, add_zero, zero_add] at hA hX
    have hq : q = h c := by by_contra hne; simp [hne] at hA
    subst hq
    exact ⟨i, by omega, good_step hmono hdiff (by omega)⟩

theorem reach_init {x : ι → ℕ} {D : Config (Sp ι Q)} (hD : (crn Φ h).Reach ((crn Φ h).init x) D) :
    D = (crn Φ h).init x ∨ ∃ c ≤ x, D = good Φ h x c := by
  induction hD with
  | refl => exact .inl rfl
  | tail _ hs ih =>
    rcases ih with rfl | ⟨c, hcx, rfl⟩
    · right
      obtain ⟨ρ, hρ, hle, rfl⟩ := hs
      rcases hρ with rfl | ⟨⟨q, i⟩, rfl⟩
      · refine ⟨0, fun _ => Nat.zero_le _, ?_⟩
        rw [init_eq]
        funext s
        cases s <;> simp [good, initR, Pi.single_apply]
      · have := hle (.A q)
        rw [init_eq] at this
        simp [stepR] at this
    · obtain ⟨i, hi, rfl⟩ := step_good hmono hdiff hs
      refine .inr ⟨c + e i, fun j => ?_, rfl⟩
      by_cases hj : j = i
      · subst hj; simp [e]; omega
      · simp [e, hj]; exact hcx j

theorem reach_good_x {x c : ι → ℕ} (hcx : c ≤ x) :
    (crn Φ h).Reach (good Φ h x c) (good Φ h x x) := by
  induction hk : ∑ i, (x i - c i) generalizing c with
  | zero =>
    have : c = x := by
      funext i
      have := (Finset.sum_eq_zero_iff.mp hk) i (Finset.mem_univ _)
      have : c i ≤ x i := hcx i
      omega
    subst this; exact CRN.Reach.refl _
  | succ k ih =>
    have : ∃ i, c i < x i := by
      by_contra hne
      push Not at hne
      have : ∑ i, (x i - c i) = 0 :=
        Finset.sum_eq_zero fun i _ => by have := hne i; omega
      omega
    obtain ⟨i, hi⟩ := this
    have hle' : c + e i ≤ x := fun j => by
      by_cases hj : j = i
      · subst hj; simp [e]; omega
      · simp [e, hj]; exact hcx j
    have hstep : (crn Φ h).Step (good Φ h x c) (good Φ h x (c + e i)) := by
      refine ⟨stepR Φ h (h c) i, .inr ⟨⟨h c, i⟩, rfl⟩, fun s => ?_, ?_⟩
      · cases s with
        | X j =>
          by_cases hj : j = i
          · subst hj; simp [stepR, good]; omega
          · simp [stepR, good, hj]
        | Y => simp [stepR, good]
        | L => simp [stepR, good]
        | A q => by_cases hq : q = h c <;> simp [stepR, good, hq]
      · exact (good_step hmono hdiff hi).symm
    refine CRN.Reach.head hstep (ih hle' ?_)
    have hterm : ∀ j, x j - c j = (x j - (c + e i) j) + if j = i then 1 else 0 := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [e]; omega
      · simp [e, hj]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
      Finset.sum_ite_eq'] at hk
    simp at hk
    omega

theorem stablyComputes : (crn Φ h).StablyComputes Φ := by
  intro x D hD
  have hgood : ∀ c ≤ x, ∃ O, (crn Φ h).Reach (good Φ h x c) O ∧ O (crn Φ h).Y = Φ x ∧
      (crn Φ h).Stable O := fun c hc =>
    ⟨good Φ h x x, reach_good_x hmono hdiff hc, rfl, fun D hD => by
      rw [(terminal_good x).reach_eq hD]⟩
  rcases reach_init hmono hdiff hD with rfl | ⟨c, hc, rfl⟩
  · obtain ⟨O, hO1, hO2⟩ := hgood 0 (fun _ => Nat.zero_le _)
    refine ⟨O, CRN.Reach.head ?_ hO1, hO2⟩
    refine ⟨initR Φ h, .inl rfl, fun s => ?_, ?_⟩
    · rw [init_eq]; cases s <;> simp [initR]
    · rw [init_eq]; funext s; cases s <;> simp [good, initR, Pi.single_apply]
  · exact hgood c hc

end

theorem outputOblivious : (crn Φ h).OutputOblivious := by
  rintro ρ (rfl | ⟨⟨q, i⟩, rfl⟩) <;> simp [crn, initR, stepR]

end Automaton

open Automaton in
/-- **Leader-automaton construction.** If `Φ` is nondecreasing in each coordinate and the finite
abstraction `h` determines the finite differences of `Φ` and its own next value, then `Φ` is
obliviously-computable. -/
theorem obliviouslyComputable_of_automaton {ι Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Q]
    [DecidableEq Q] (Φ : (ι → ℕ) → ℕ) (h : (ι → ℕ) → Q)
    (hmono : ∀ c i, Φ c ≤ Φ (c + Pi.single i 1))
    (hdiff : ∀ c c', h c = h c' → ∀ i,
      Φ (c + Pi.single i 1) - Φ c = Φ (c' + Pi.single i 1) - Φ c' ∧
        h (c + Pi.single i 1) = h (c' + Pi.single i 1)) :
    ObliviouslyComputable Φ :=
  ⟨Sp ι Q, inferInstance, inferInstance, crn Φ h, rfl, outputOblivious,
    stablyComputes hmono hdiff⟩

end Podc.ComposableCRN
