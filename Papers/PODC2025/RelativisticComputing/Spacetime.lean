import Papers.PODC2025.RelativisticComputing.Model

/-!
# Relativistic physics and relativistic executions (Jayanti, PODC 2025, §3.2, Definition 4.4)

We abstract the relativistic postulates into an order-theoretic structure `Spacetime`:

* RP1: spacetime events are partially ordered by an irreflexive transitive *causal order* `≺`;
  every reference frame `F` has a real time coordinate `time F`, and its chronological order
  refines `≺` (`e ≺ e' → time F e < time F e'`);
* RP2: world lines are chains of `≺`;
* the physical fact used in the proof of Lemma 6.6: there is a body at rest in some frame `F`
  whose world line is parametrised by the time of `F` (`γ : ℝ → Pt`, `time F (γ τ) = τ`,
  `τ < τ' → γ τ ≺ γ τ'`).

RP3 (transmissions are physically permissible iff sent at `e` and received at `e'` with `e ≺ e'`)
enters the definition of a relativistic physical execution (`IsRelPhys`).

Non-vacuity: `minkowski d` is the Minkowski spacetime `ℝ × ℝᵈ` (with `c = 1`), with the
inertial frames of velocity `v`, `‖v‖ < 1`; frame time is `t - ⟪v, x⟫`, which is the Lorentz time
`γ_v (t - ⟪v, x⟫)` up to the positive factor `γ_v` (and the order is all that matters).
We also check the relativity of simultaneity (§3.2) and the spacetime geometry behind
Observation 1 (§7).
-/

namespace RelativisticComputing

/-- Abstract relativistic spacetime: postulates RP1, RP2 and the existence of a body at rest in some
reference frame. -/
structure Spacetime where
  /-- Spacetime events. -/
  Pt : Type
  /-- The relativistic causal order `≺`. -/
  prec : Pt → Pt → Prop
  prec_irrefl : ∀ e, ¬ prec e e
  prec_trans : ∀ e₁ e₂ e₃, prec e₁ e₂ → prec e₂ e₃ → prec e₁ e₃
  /-- Reference frames (observers). -/
  Frame : Type
  /-- The temporal coordinate of an event in a reference frame. -/
  time : Frame → Pt → ℝ
  /-- RP1: every frame's chronological order refines `≺`. -/
  time_mono : ∀ F e e', prec e e' → time F e < time F e'
  /-- World lines of pointlike bodies. -/
  IsWorldLine : Set Pt → Prop
  /-- RP2: events on a world line are totally ordered by `≺`. -/
  worldLine_chain : ∀ L, IsWorldLine L → IsChain prec L
  /-- A body at rest in some frame: its world line is parametrised by that frame's time. -/
  rest : ∃ (F : Frame) (γ : ℝ → Pt), IsWorldLine (Set.range γ) ∧ (∀ τ, time F (γ τ) = τ) ∧
    ∀ τ τ', τ < τ' → prec (γ τ) (γ τ')

variable {Proc Msg : Type} {A : Algorithm Proc Msg}

/-- **Definition 4.3** (relativistic physical execution `𝒴 = (S, ε)`): `ε` maps the steps to
distinct spacetime events (RP1); each processor is a pointlike body tracing a world line
containing the events of its steps (Φ1, RP2); the steps of each processor, ordered by `≺`, form a
rooted consecutively permissible sequence (Φ2); messages are valid and received at most once (Φ3)
and every transmission goes from `e` to `e'` with `e ≺ e'` (RP3). -/
structure IsRelPhys (X : Spacetime) (A : Algorithm Proc Msg) (S : Set (Step A)) (ε : S → X.Pt) :
    Prop where
  inj : Function.Injective ε
  worldLines : ∃ L : Proc → Set X.Pt, (∀ π, X.IsWorldLine (L π)) ∧ ∀ s : S, ε s ∈ L s.1.proc
  procSeq : ProcSeq S (fun a b => X.prec (ε a) (ε b))
  msgValid : MsgValid S
  msgForward : MsgForward S (fun a b => X.prec (ε a) (ε b))

/-- **Definition 4.4** (relativistic execution): `(S, ≺_S)` extracted from a relativistic physical
execution `(S, ε)`: `s ≺_S s' ↔ ε s ≺ ε s'`. -/
def IsRelativistic (X : Spacetime) (A : Algorithm Proc Msg) (S : Set (Step A))
    (prec : S → S → Prop) : Prop :=
  ∃ ε : S → X.Pt, IsRelPhys X A S ε ∧ ∀ a b, prec a b ↔ X.prec (ε a) (ε b)

/-! ### Minkowski spacetime -/

section Minkowski

open RealInnerProductSpace

variable (d : ℕ)

/-- Points of `(1+d)`-dimensional Minkowski spacetime: `(t, x)`. -/
abbrev MinkPt := ℝ × EuclideanSpace ℝ (Fin d)

/-- The causal order of Minkowski spacetime (`c = 1`): `e ≺ e'` iff `e ≠ e'` and a light pulse
emitted at `e` can reach `e'`, i.e. `‖x' - x‖ ≤ t' - t`. -/
def minkPrec (e e' : MinkPt d) : Prop := e ≠ e' ∧ ‖e'.2 - e.2‖ ≤ e'.1 - e.1

/-- Chronological time of the inertial frame with velocity `v` (up to the factor `γ_v > 0`). -/
noncomputable def minkTime (v : EuclideanSpace ℝ (Fin d)) (e : MinkPt d) : ℝ := e.1 - ⟪v, e.2⟫

lemma minkPrec_trans {e₁ e₂ e₃ : MinkPt d} (h₁ : minkPrec d e₁ e₂) (h₂ : minkPrec d e₂ e₃) :
    minkPrec d e₁ e₃ := by
  obtain ⟨hne₁, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  have htri : ‖e₃.2 - e₁.2‖ ≤ ‖e₃.2 - e₂.2‖ + ‖e₂.2 - e₁.2‖ := by
    have := norm_add_le (e₃.2 - e₂.2) (e₂.2 - e₁.2)
    simpa using this
  refine ⟨?_, by linarith⟩
  rintro rfl
  have h0 := norm_nonneg (e₂.2 - e₁.2)
  have h0' := norm_nonneg (e₁.2 - e₂.2)
  have ht : e₂.1 = e₁.1 := by linarith
  have hx : ‖e₂.2 - e₁.2‖ = 0 := by linarith
  rw [norm_eq_zero, sub_eq_zero] at hx
  exact hne₁ (Prod.ext ht.symm hx.symm)

lemma minkTime_mono {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ < 1) {e e' : MinkPt d}
    (h : minkPrec d e e') : minkTime d v e < minkTime d v e' := by
  obtain ⟨hne, h⟩ := h
  unfold minkTime
  have hin : ⟪v, e'.2 - e.2⟫ ≤ ‖v‖ * ‖e'.2 - e.2‖ := real_inner_le_norm _ _
  rw [inner_sub_right] at hin
  by_cases hx : e'.2 - e.2 = 0
  · have hx' : e'.2 = e.2 := sub_eq_zero.mp hx
    have ht : e.1 ≠ e'.1 := fun ht => hne (Prod.ext ht hx'.symm)
    rw [hx, norm_zero] at h
    rw [hx']
    have : e.1 < e'.1 := lt_of_le_of_ne (by linarith) ht
    linarith
  · have hpos : 0 < ‖e'.2 - e.2‖ := norm_pos_iff.mpr hx
    have : ‖v‖ * ‖e'.2 - e.2‖ < ‖e'.2 - e.2‖ := by nlinarith
    linarith

/-- Minkowski spacetime of dimension `1 + d` with its inertial frames. -/
noncomputable def minkowski : Spacetime where
  Pt := MinkPt d
  prec := minkPrec d
  prec_irrefl e h := h.1 rfl
  prec_trans _ _ _ := minkPrec_trans d
  Frame := {v : EuclideanSpace ℝ (Fin d) // ‖v‖ < 1}
  time v := minkTime d v.1
  time_mono v _ _ := minkTime_mono d v.2
  IsWorldLine L := IsChain (minkPrec d) L
  worldLine_chain _ h := h
  rest := by
    refine ⟨⟨0, by simp⟩, fun τ => (τ, 0), ?_, fun τ => by simp [minkTime], ?_⟩
    · rintro _ ⟨τ, rfl⟩ _ ⟨τ', rfl⟩ hne
      have hne' : τ ≠ τ' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hne' with h | h
      · exact Or.inl ⟨hne, by simp; linarith⟩
      · exact Or.inr ⟨Ne.symm hne, by simp; linarith⟩
    · intro τ τ' h
      refine ⟨fun h' => h.ne (by simpa using congrArg Prod.fst h'), by simp; linarith⟩

/-- **Relativity of simultaneity** (§3.2): in `1+1`-dimensional Minkowski spacetime there are two
events `e, e'` and three frames `F, F*, F**` with `e =_F e'`, `e <_{F*} e'` and `e >_{F**} e'`.
(Here `e = (0, 1)`, `e' = (0, -1)`, and the frames have velocities `0`, `1/2` and `-1/2`.) -/
theorem relativity_of_simultaneity :
    ∃ (e e' : (minkowski 1).Pt) (F F₁ F₂ : (minkowski 1).Frame),
      (minkowski 1).time F e = (minkowski 1).time F e' ∧
      (minkowski 1).time F₁ e < (minkowski 1).time F₁ e' ∧
      (minkowski 1).time F₂ e' < (minkowski 1).time F₂ e := by
  set u : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have hu : ‖u‖ = 1 := by simp [u]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  refine ⟨((0 : ℝ), u), ((0 : ℝ), -u), ⟨0, by simp⟩, ⟨(1/2 : ℝ) • u, ?_⟩, ⟨(-1/2 : ℝ) • u, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [norm_smul, hu]; norm_num
  · rw [norm_smul, hu]; norm_num
  · simp [minkowski, minkTime]
  · simp only [minkowski, minkTime, inner_smul_left, inner_neg_right, huu]; norm_num
  · simp only [minkowski, minkTime, inner_smul_left, inner_neg_right, huu]; norm_num

/-- **The geometry behind Observation 1** (§7). Two "almost instantaneous" operations happen
in the `ε`-neighbourhoods `E₁` of `e₁ = (0, -u)` and `E₂` of `e₂ = (0, u)` (`‖u‖ = 1`), which are
simultaneous for the observer at rest. If `ε < 1/3` then for the observer moving with velocity
`u/2` every event of `E₂` precedes every event of `E₁`, and for the observer moving with velocity
`-u/2` every event of `E₁` precedes every event of `E₂`. Hence in the first frame the operation
at `E₂` happens before the operation at `E₁`, and in the second frame the other way round, so the
two observers must linearize the two operations in opposite orders. -/
theorem observation1_geometry {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    {ε : ℝ} (hε : ε < 1 / 3) (e₁' e₂' : MinkPt d)
    (h₁ : |e₁'.1| < ε ∧ ‖e₁'.2 + u‖ < ε) (h₂ : |e₂'.1| < ε ∧ ‖e₂'.2 - u‖ < ε) :
    minkTime d ((1/2 : ℝ) • u) e₂' < minkTime d ((1/2 : ℝ) • u) e₁' ∧
    minkTime d ((-1/2 : ℝ) • u) e₁' < minkTime d ((-1/2 : ℝ) • u) e₂' := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  -- `⟪u, x⟫` is within `ε` of `-1` resp. `1`
  have b₁ : |⟪u, e₁'.2⟫ + 1| < ε := by
    have : ⟪u, e₁'.2⟫ + 1 = ⟪u, e₁'.2 + u⟫ := by rw [inner_add_right, huu]
    rw [this]
    calc |⟪u, e₁'.2 + u⟫| ≤ ‖u‖ * ‖e₁'.2 + u‖ := abs_real_inner_le_norm _ _
      _ < ε := by rw [hu, one_mul]; exact h₁.2
  have b₂ : |⟪u, e₂'.2⟫ - 1| < ε := by
    have : ⟪u, e₂'.2⟫ - 1 = ⟪u, e₂'.2 - u⟫ := by rw [inner_sub_right, huu]
    rw [this]
    calc |⟪u, e₂'.2 - u⟫| ≤ ‖u‖ * ‖e₂'.2 - u‖ := abs_real_inner_le_norm _ _
      _ < ε := by rw [hu, one_mul]; exact h₂.2
  rw [abs_lt] at b₁ b₂
  have t₁ := abs_lt.mp h₁.1
  have t₂ := abs_lt.mp h₂.1
  simp only [minkTime, inner_smul_left]
  simp only [RCLike.conj_to_real]
  constructor <;> nlinarith [b₁.1, b₁.2, b₂.1, b₂.2, t₁.1, t₁.2, t₂.1, t₂.2]

end Minkowski

end RelativisticComputing
