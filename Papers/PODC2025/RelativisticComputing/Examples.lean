import Papers.PODC2025.RelativisticComputing.Counterexample

/-!
# Examples: non-vacuity and the order-type gap in the proof of Lemma 6.3

* `ping_classical`, `ping_computational`, `ping_relativistic` — a two-processor algorithm in which
  processor `false` sends a message that processor `true` receives; its two-step execution is a
  classical, a computational and a relativistic execution (in Minkowski spacetime).
* `spacelike_relativistic` — two steps at spacelike-separated events form a relativistic execution
  in which the steps are causally unrelated, and two observers perceive them in opposite orders.
* `omegaPlusOne_classical`, `omegaPlusOne_not_seq` — a classical execution with two processors
  whose chronological order has order type `ω + 1`: processor `false` takes infinitely many steps
  (at times `1 - 1/(n+1)`), processor `true` one step at time `1`. Its steps cannot be listed as a
  sequence `s₁, s₂, …` in chronological order, so the time map `t(sᵢ) = i` used in the proof of
  Lemma 6.3 does not exist. (The statement of Lemma 6.3 is still true for countably many
  processors: `lemma_6_3_of_countable`.)
-/

namespace RelativisticComputing

open RealInnerProductSpace

/-! ### Ping -/

/-- Events of the ping algorithm. -/
inductive PingEv
  | send
  | recv
  deriving DecidableEq

/-- Processor `false` sends one message to processor `true`, which receives it. -/
def pingAlg : Algorithm Bool Unit where
  State := Bool
  Event := PingEv
  init _ := {false}
  δ π σ e σ' := σ = false ∧ σ' = true ∧ e = (if π then .recv else .send)
  sendTo e := match e with
    | .send => some ((), true)
    | .recv => none
  recv e := match e with
    | .send => none
    | .recv => some ()

/-- The send step. -/
def sSend : Step pingAlg := ⟨false, false, .send, true, ⟨rfl, rfl, rfl⟩⟩
/-- The receive step. -/
def sRecv : Step pingAlg := ⟨true, false, .recv, true, ⟨rfl, rfl, rfl⟩⟩

/-- The execution: both steps. -/
def Sping : Set (Step pingAlg) := {sSend, sRecv}

lemma ping_cases (a : Sping) : a.1 = sSend ∨ a.1 = sRecv := a.2

lemma ping_eq_of_proc {a b : Sping} (h : a.1.proc = b.1.proc) : a = b := by
  apply Subtype.ext
  rcases ping_cases a with ha | ha <;> rcases ping_cases b with hb | hb <;>
    simp_all [sSend, sRecv]

lemma ping_msgEdge {a b : Sping} (h : MsgEdge a b) : a.1 = sSend ∧ b.1 = sRecv := by
  obtain ⟨m, ⟨π', hs⟩, hr⟩ := h
  rcases ping_cases a with ha | ha <;> rcases ping_cases b with hb | hb <;>
    simp_all [sSend, sRecv, pingAlg, Receives]

lemma ping_msgValid : MsgValid Sping where
  valid a b m π' hs hr := by
    rcases ping_cases a with ha | ha <;> rcases ping_cases b with hb | hb <;>
      simp_all [sSend, sRecv, pingAlg, Receives]
  atMostOnce a b m ha hb := by
    apply Subtype.ext
    rcases ping_cases a with h1 | h1 <;> rcases ping_cases b with h2 | h2 <;>
      simp_all [sSend, sRecv, pingAlg, Receives]

/-- Every relation that is irreflexive and orders the send step first gives `ProcSeq`. -/
lemma ping_procSeq {r : Sping → Sping → Prop} (hr : ∀ a, ¬ r a a) : ProcSeq Sping r where
  irrefl := hr
  trans a b c hab hbc h1 _ := by
    rw [ping_eq_of_proc hab] at h1; exact absurd h1 (hr b)
  total a b hab hne := (hne (ping_eq_of_proc hab)).elim
  finite_pred a := by
    refine Set.Finite.subset (Set.finite_singleton a) fun b ⟨hb, _⟩ => ?_
    exact ping_eq_of_proc hb
  rooted a _ := by
    rcases ping_cases a with h | h <;> rw [h] <;> rfl
  consec a b hab h _ := by
    rw [ping_eq_of_proc hab] at h; exact absurd h (hr b)

/-- The ping execution with the send step at time `0` and the receive step at time `1` is a
classical execution. -/
theorem ping_classical :
    IsClassical pingAlg Sping (fun a b => (if a.1.proc then (1 : ℝ) else 0) <
      if b.1.proc then 1 else 0) := by
  refine ⟨fun a => if a.1.proc then 1 else 0, ⟨?_, ping_procSeq fun a => lt_irrefl _,
    ping_msgValid, fun a b h => ?_⟩, fun _ _ => Iff.rfl⟩
  · intro a b hab
    apply ping_eq_of_proc
    cases ha : a.1.proc <;> cases hb : b.1.proc <;> simp_all
  · obtain ⟨ha, hb⟩ := ping_msgEdge h
    simp [ha, hb, sSend, sRecv]

/-- The happens-before order of the ping execution (send ◁ receive) is a computational
execution. -/
theorem ping_computational :
    ∃ R, IsComputational pingAlg Sping R ∧ ∃ a b, R a b := by
  obtain ⟨R, hR, hlt⟩ := lemma_6_4_forward ping_classical
  refine ⟨R, hR, ⟨sSend, Or.inl rfl⟩, ⟨sRecv, Or.inr rfl⟩, ?_⟩
  exact hR.msgForward _ _ ⟨(), ⟨true, rfl⟩, rfl⟩

/-- The ping execution placed in Minkowski spacetime: send at `(0, 0)`, receive at `(2, 1)`. -/
theorem ping_relativistic :
    ∃ ε : Sping → (minkowski 1).Pt, IsRelPhys (minkowski 1) pingAlg Sping ε := by
  set u : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have hu : ‖u‖ = 1 := by simp [u]
  let ε : Sping → (minkowski 1).Pt := fun a => if a.1.proc then (2, u) else (0, 0)
  have hne : ((2 : ℝ), u) ≠ ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin 1))) := by
    intro h; have := congrArg Prod.fst h; norm_num at this
  refine ⟨ε, ⟨?_, ?_, ping_procSeq fun a => (minkowski 1).prec_irrefl _, ping_msgValid, ?_⟩⟩
  · intro a b hab
    apply ping_eq_of_proc
    have h1 := congrArg Prod.fst hab
    simp only [ε] at h1
    cases ha : a.1.proc <;> cases hb : b.1.proc <;> simp [ha, hb] at h1 ⊢
  · refine ⟨fun p => {ε ⟨sSend, Or.inl rfl⟩, ε ⟨sRecv, Or.inr rfl⟩}, fun p => ?_, fun s => ?_⟩
    · refine IsChain.pair ⟨?_, ?_⟩
      · simp [ε, sSend, sRecv, hne.symm]
      · simp [ε, sSend, sRecv, hu]
    · rcases ping_cases s with h | h
      · exact Or.inl (by congr 1; exact Subtype.ext h)
      · exact Or.inr (by rw [Set.mem_singleton_iff]; congr 1; exact Subtype.ext h)
  · intro a b h
    obtain ⟨ha, hb⟩ := ping_msgEdge h
    refine ⟨?_, ?_⟩
    · simp [ε, ha, hb, sSend, sRecv, hne.symm]
    · simp [ε, ha, hb, sSend, sRecv, hu]

/-! ### Two spacelike-separated steps -/

/-- Two processors each take one step, at the spacelike-separated events `(0, -u)` and `(0, u)`.
This is a relativistic execution in which the two steps are causally unrelated, and the
observers with velocities `u/2` and `-u/2` perceive them in opposite orders. -/
theorem spacelike_relativistic :
    ∃ ε : S₀ Bool → (minkowski 1).Pt, IsRelPhys (minkowski 1) (trivAlg Bool) (S₀ Bool) ε ∧
      (∀ a b, ¬ (minkowski 1).prec (ε a) (ε b)) ∧
      ∃ F₁ F₂ : (minkowski 1).Frame, ∃ a b : S₀ Bool,
        (minkowski 1).time F₁ (ε a) < (minkowski 1).time F₁ (ε b) ∧
        (minkowski 1).time F₂ (ε b) < (minkowski 1).time F₂ (ε a) := by
  set u : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have hu : ‖u‖ = 1 := by simp [u]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; norm_num at hu
  let ε : S₀ Bool → (minkowski 1).Pt := fun a => ((0 : ℝ), if a.1.proc then u else -u)
  have hneg : -u ≠ u := by
    intro h
    have : (2 : ℝ) • u = 0 := by rw [two_smul]; nth_rw 1 [← h]; simp
    exact hu0 ((smul_eq_zero.1 this).resolve_left (by norm_num))
  have hinj : Function.Injective ε := by
    intro a b hab
    apply S₀_ext
    have h := congrArg Prod.snd hab
    simp only [ε] at h
    cases ha : a.1.proc <;> cases hb : b.1.proc <;> simp_all [hneg.symm]
  have h2 : ‖u + u‖ = 2 := by rw [← two_smul ℝ u, norm_smul, hu]; norm_num
  have h2' : ‖-u - u‖ = 2 := by
    rw [show -u - u = (-2 : ℝ) • u by rw [neg_smul, two_smul]; abel, norm_smul, hu]; norm_num
  have hsep : ∀ a b, ¬ (minkowski 1).prec (ε a) (ε b) := by
    intro a b ⟨hne, h⟩
    simp only [ε, sub_self] at h hne
    cases ha : a.1.proc <;> cases hb : b.1.proc <;> simp_all [sub_neg_eq_add] <;>
      norm_num [h2, h2'] at h
  refine ⟨ε, isRelPhys_trivAlg _ ε hinj fun _ => Set.subsingleton_singleton.isChain, hsep,
    ⟨(1/2 : ℝ) • u, ?_⟩, ⟨(-1/2 : ℝ) • u, ?_⟩, ⟨tstep true, Set.mem_univ _⟩,
    ⟨tstep false, Set.mem_univ _⟩, ?_, ?_⟩
  · rw [norm_smul, hu]; norm_num
  · rw [norm_smul, hu]; norm_num
  · simp only [minkowski, minkTime, ε, tstep, ite_true, Bool.false_eq_true, ite_false,
      inner_smul_left, inner_neg_right, huu]; norm_num
  · simp only [minkowski, minkTime, ε, tstep, ite_true, Bool.false_eq_true, ite_false,
      inner_smul_left, inner_neg_right, huu]; norm_num

/-! ### A classical execution of order type `ω + 1` -/

/-- A counter: every step increments the state; no messages. -/
abbrev countAlg : Algorithm Bool Empty where
  State := ℕ
  Event := Unit
  init _ := {0}
  δ _ σ _ σ' := σ' = σ + 1
  sendTo _ := none
  recv _ := none

lemma countAlg_ext {a b : Step countAlg} (h1 : a.proc = b.proc) (h2 : a.pre = b.pre) : a = b := by
  obtain ⟨p, σ, e, σ', h⟩ := a
  obtain ⟨q, τ, f, τ', h'⟩ := b
  have e1 : σ' = σ + 1 := h
  have e2 : τ' = τ + 1 := h'
  cases e; cases f
  simp only at h1 h2
  subst h1 h2 e1 e2
  rfl

/-- The step of processor `π` starting at state `n`. -/
def cstep (π : Bool) (n : ℕ) : Step countAlg := ⟨π, n, (), n + 1, rfl⟩

/-- Processor `false` takes all its steps `0, 1, 2, …`; processor `true` takes its first step. -/
def Sω : Set (Step countAlg) := {s | s.proc = false ∨ s.pre = 0}

/-- Times: the `n`-th step of `false` at `1 - 1/(n+1)`, the step of `true` at time `1`. -/
noncomputable def tω (a : Sω) : ℝ := if a.1.proc then 1 else 1 - 1 / ((a.1.pre : ℝ) + 1)

lemma tω_false {a : Sω} (h : a.1.proc = false) : tω a = 1 - 1 / ((a.1.pre : ℝ) + 1) := by
  simp [tω, h]

lemma tω_true {a : Sω} (h : a.1.proc = true) : tω a = 1 := by simp [tω, h]

lemma tω_lt_one {a : Sω} (h : a.1.proc = false) : tω a < 1 := by
  rw [tω_false h]; have : (0 : ℝ) < 1 / ((a.1.pre : ℝ) + 1) := by positivity
  linarith

lemma tω_false_lt_iff {a b : Sω} (ha : a.1.proc = false) (hb : b.1.proc = false) :
    tω a < tω b ↔ a.1.pre < b.1.pre := by
  rw [tω_false ha, tω_false hb, sub_lt_sub_iff_left,
    one_div_lt_one_div (by positivity) (by positivity)]
  constructor
  · intro h; exact_mod_cast (by linarith : (a.1.pre : ℝ) < b.1.pre)
  · intro h; have : (a.1.pre : ℝ) < b.1.pre := by exact_mod_cast h
    linarith

lemma Sω_true {a : Sω} (h : a.1.proc = true) : a.1.pre = 0 := by
  rcases a.2 with h' | h'
  · rw [h] at h'; cases h'
  · exact h'

lemma Sω_ext {a b : Sω} (h1 : a.1.proc = b.1.proc) (h2 : a.1.pre = b.1.pre) : a = b :=
  Subtype.ext (countAlg_ext h1 h2)

lemma tω_injective : Function.Injective tω := by
  intro a b hab
  cases ha : a.1.proc <;> cases hb : b.1.proc
  · apply Sω_ext (ha.trans hb.symm)
    rcases lt_trichotomy a.1.pre b.1.pre with h | h | h
    · exact absurd hab ((tω_false_lt_iff ha hb).2 h).ne
    · exact h
    · exact absurd hab ((tω_false_lt_iff hb ha).2 h).ne'
  · exact absurd hab ((tω_lt_one ha).trans_eq (tω_true hb).symm).ne
  · exact absurd hab ((tω_lt_one hb).trans_eq (tω_true ha).symm).ne'
  · exact Sω_ext (ha.trans hb.symm) ((Sω_true ha).trans (Sω_true hb).symm)

/-- The `ω + 1` execution is a classical execution. -/
theorem omegaPlusOne_classical : IsClassical countAlg Sω (fun a b => tω a < tω b) := by
  refine ⟨tω, ⟨tω_injective, ?_, ⟨fun _ _ m => m.elim, fun _ _ m => m.elim⟩,
    fun _ _ ⟨m, _⟩ => m.elim⟩, fun _ _ => Iff.rfl⟩
  have mem : ∀ n, cstep false n ∈ Sω := fun n => Or.inl rfl
  refine
    { irrefl := fun a => lt_irrefl _
      trans := fun _ _ _ _ _ => lt_trans
      total := fun a b _ hne => lt_or_gt_of_ne fun h => hne (tω_injective h)
      finite_pred := fun a => ?_
      rooted := fun a ha => ?_
      consec := fun a b hab h hc => ?_ }
  · cases ha : a.1.proc
    · refine Set.Finite.of_finite_image (f := fun b : Sω => b.1.pre) ?_ ?_
      · refine (Set.finite_Iio a.1.pre).subset ?_
        rintro _ ⟨b, ⟨hb, hlt⟩, rfl⟩
        exact (tω_false_lt_iff hb ha).1 hlt
      · intro b ⟨hb, _⟩ c ⟨hc, _⟩ h
        exact Sω_ext (hb.trans hc.symm) h
    · refine Set.Finite.subset (Set.finite_empty) fun b ⟨hb, hlt⟩ => ?_
      rw [Sω_ext (hb.trans ha.symm) ((Sω_true hb).trans (Sω_true ha).symm)] at hlt
      exact lt_irrefl _ hlt
  · show a.1.pre = 0
    cases hp : a.1.proc
    · by_contra hne
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
      apply ha ⟨cstep false n, mem n⟩ hp.symm
      rw [tω_false_lt_iff rfl hp]
      simp [cstep, hn]
    · exact Sω_true hp
  · have hv : a.1.post = a.1.pre + 1 := a.1.valid
    rw [hv]
    cases hp : a.1.proc
    · have hbp : b.1.proc = false := hab ▸ hp
      have hlt := (tω_false_lt_iff hp hbp).1 h
      by_contra hne
      apply hc ⟨cstep false (a.1.pre + 1), mem _⟩ hp.symm
      rw [tω_false_lt_iff hp rfl, tω_false_lt_iff rfl hbp]
      simp only [cstep]
      obtain ⟨m, hm⟩ : ∃ m : ℕ, a.1.pre = m := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, b.1.pre = k := ⟨_, rfl⟩
      rw [hm, hk] at hlt hne ⊢
      exact ⟨Nat.lt_succ_self m, lt_of_le_of_ne (Nat.succ_le_of_lt hlt) (fun h => hne h.symm)⟩
    · have hbp : b.1.proc = true := hab ▸ hp
      rw [Sω_ext (hp.trans hbp.symm) ((Sω_true hp).trans (Sω_true hbp).symm)] at h
      exact absurd h (lt_irrefl _)

/-- The chronological order of the `ω + 1` execution cannot be listed as a sequence
`s₁, s₂, …`: there is no order embedding into `ℕ` (the step of processor `true` has infinitely
many predecessors). Hence the map `t(sᵢ) = i` of the proof of Lemma 6.3 does not exist. -/
theorem omegaPlusOne_not_seq : ¬ ∃ idx : Sω → ℕ, ∀ a b, tω a < tω b ↔ idx a < idx b := by
  rintro ⟨idx, hidx⟩
  let top : Sω := ⟨cstep true 0, Or.inr rfl⟩
  let f : ℕ → Sω := fun n => ⟨cstep false n, Or.inl rfl⟩
  have hf : Function.Injective f := fun m n h => by
    have := congrArg (fun a : Sω => a.1.pre) h
    simpa [f, cstep] using this
  have hlt : ∀ n, idx (f n) < idx top := fun n =>
    (hidx _ _).1 ((tω_lt_one (a := f n) rfl).trans_eq (tω_true (a := top) rfl).symm)
  have idx_inj : Function.Injective idx := by
    intro a b h
    by_contra hne
    rcases lt_or_gt_of_ne (tω_injective.ne hne) with h' | h'
    · exact ((hidx _ _).1 h').ne h
    · exact ((hidx _ _).1 h').ne' h
  have hinj : Function.Injective (idx ∘ f) := idx_inj.comp hf
  have : Set.range (idx ∘ f) ⊆ Set.Iio (idx top) := by
    rintro _ ⟨n, rfl⟩; exact hlt n
  exact Set.infinite_range_of_injective hinj ((Set.finite_Iio _).subset this)

end RelativisticComputing
