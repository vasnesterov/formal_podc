import Papers.PODC2015.ABADetection.CasDefs

/-!
# Lemma 2: hiding the steps of a process (Section 2.2)

`lemma2`: let `β` be a successful schedule for `C` (not containing `q`), and let `q` take at
most `t` more steps before returning. Then there is a schedule `σ` (steps of `q` and of `β` only,
no invocations) such that `Conf(C, β)` and `Conf(C, σ)` agree on all processes but `q`, and in
`Conf(C, σ)` either (a) `q` is idle, or (b) `q` is poised to `Write` an object `R` with
`|WCov(C,R) ∩ β| < t`, or (c) `q` is poised to execute a `CAS(x,y)`, `x ≠ y`, on `R` whose value
is `x`, with `|WCov(C,R) ∩ β| + |CCov(C,R) ∩ β| < t`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}
  {I : Impl A (fun _ : ι => wcasObj V v₀) P L}

local notation "Cf" => Config A (fun _ : ι => wcasObj V v₀) P L

/-! ### Helper lemmas -/

omit [DecidableEq P] in
lemma exists_first_split {α : Type} (f : α → Prop) (l : List α) :
    (∀ a ∈ l, ¬ f a) ∨ ∃ pre z post, l = pre ++ z :: post ∧ f z ∧ ∀ a ∈ pre, ¬ f a := by
  induction l with
  | nil => exact Or.inl (by simp)
  | cons b l ih =>
    by_cases hb : f b
    · exact Or.inr ⟨[], b, l, rfl, hb, by simp⟩
    · rcases ih with h | ⟨pre, z, post, rfl, hz, hpre⟩
      · exact Or.inl fun a ha => by
          rcases List.mem_cons.1 ha with rfl | ha
          exacts [hb, h a ha]
      · exact Or.inr ⟨b :: pre, z, post, rfl, hz, fun a ha => by
          rcases List.mem_cons.1 ha with rfl | ha
          exacts [hb, hpre a ha]⟩

lemma budget_step_self {C C' : Cf} {q : P} {t : ℕ} (h : Budget I C q (t + 1))
    (hs : I.step C (.tau q) = some C') : Budget I C' q t := by
  intro δ C'' hδ hq
  have := h (.tau q :: δ) C'' (by simp [hs, hδ]) (by
    intro ℓ hℓ hp
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · rfl
    · exact hq ℓ hℓ hp)
  simp only [List.countP_cons, Label.isTauOf_tau, decide_true, ite_true] at this
  omega

lemma budget_step_other {C C' : Cf} {q : P} {t : ℕ} (h : Budget I C q t) {ℓ : Label P A}
    (hℓ : ℓ.proc ≠ q) (hs : I.step C ℓ = some C') : Budget I C' q t := by
  intro δ C'' hδ hq
  have := h (ℓ :: δ) C'' (by simp [hs, hδ]) (by
    intro ℓ' hℓ' hp
    rcases List.mem_cons.1 hℓ' with rfl | hℓ'
    · exact absurd hp hℓ
    · exact hq ℓ' hℓ' hp)
  have hf : ℓ.isTauOf q = false := by
    cases ℓ with
    | tau p => simpa [Label.proc] using hℓ
    | _ => rfl
  simpa [List.countP_cons, hf] using this

lemma budget_zero {C C' : Cf} {q : P} (h : Budget I C q 0) (hs : I.step C (.tau q) = some C') :
    False := by
  have := h [.tau q] C' (by simp [hs]) (by simp)
  simp at this

/-- A step of `q` that does not change the accessed object only changes `q`. -/
lemma agreeOn_step_nonmod {C C' : Cf} {q : P} {i : ι} {o : WCasOp V} {k : Option V → L}
    (hact : I.act q (C.loc q) = .access i o k)
    (hmod : ((wcasObj V v₀).δ (C.mem i) o).1 = C.mem i)
    (h : I.step C (.tau q) = some C') : Impl.AgreeOn {p | p ≠ q} C C' := by
  have hp := (Impl.step_tau h).1
  rw [step_tau_eq hp hact] at h
  cases h
  refine ⟨?_, fun p hp => by simp [Function.update_of_ne hp], fun _ _ => rfl⟩
  show C.mem = Function.update C.mem i ((wcasObj V v₀).δ (C.mem i) o).1
  rw [hmod, Function.update_eq_self]

/-- A `Write` of `z` to `i` right after a step of `q` on `i` hides that step from everybody
but `q`. -/
lemma agreeOn_absorb {C C₁ C' Cz : Cf} {q z : P} (hzq : z ≠ q) {i : ι} {o : WCasOp V}
    {k : Option V → L} {w : V} {kz : Option V → L}
    (hactq : I.act q (C.loc q) = .access i o k) (hactz : I.act z (C.loc z) = .access i (.write w) kz)
    (h₁ : I.step C (.tau q) = some C₁) (h₂ : I.step C₁ (.tau z) = some C')
    (hz : I.step C (.tau z) = some Cz) : Impl.AgreeOn {p | p ≠ q} C' Cz := by
  have hpq := (Impl.step_tau h₁).1
  have hpz := (Impl.step_tau hz).1
  rw [step_tau_eq hpq hactq] at h₁
  cases h₁
  rw [step_tau_eq hpz hactz] at hz
  cases hz
  rw [step_tau_eq (I := I) (by simpa using hpz) (by simpa [Function.update_of_ne hzq] using hactz)]
    at h₂
  cases h₂
  refine ⟨by simp, fun p hp => ?_, fun _ _ => rfl⟩
  by_cases hpz : p = z
  · subst hpz; simp
  · simp [Function.update_of_ne hpz, Function.update_of_ne (show p ≠ q from hp)]


/-- Processes not poised on `R` do not change `R` in a block of single steps. -/
lemma mem_runFrom_blockWrite_of_not_on {R : ι} : ∀ {C D : Cf} {β : List P}, β.Nodup →
    (∀ p ∈ β, ∀ o, poisedAcc I C p ≠ some (R, o)) →
    I.runFrom C (Impl.blockWrite β) = some D → D.mem R = C.mem R
  | C, D, [], _, _, h => by simp at h; rw [h]
  | C, D, p :: β, hnd, hnot, h => by
    simp only [Impl.blockWrite_cons, Impl.runFrom_cons] at h
    cases hs : I.step C (.tau p) with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨-, -, i, o, k, hact, hm, -⟩ := Impl.step_tau hs
      have hiR : i ≠ R := by
        rintro rfl
        exact hnot p List.mem_cons_self o (poisedAcc_eq_of_act hact)
      have hpnot := (List.nodup_cons.1 hnd).1
      rw [mem_runFrom_blockWrite_of_not_on (List.nodup_cons.1 hnd).2 (fun p' hp' o' => by
        have hp'p : p' ≠ p := fun e => hpnot (e ▸ hp')
        rw [← poisedAcc_congr (Impl.step_other hs (q := p') (Ne.symm hp'p)).1.symm]
        exact hnot p' (List.mem_cons_of_mem _ hp') o') h, hm,
        Function.update_of_ne (Ne.symm hiR)]

/-- **Bubbling** the first process `z` accessing `R` to the front of a successful schedule:
the processes before it access other objects, so their steps commute with `z`'s step. -/
lemma succ_bubble {z : P} {R : ι} {oz : WCasOp V} : ∀ {C : Cf} (pre post : List P),
    (pre ++ z :: post).Nodup → poisedAcc I C z = some (R, oz) →
    (∀ a ∈ pre, ∀ o, poisedAcc I C a ≠ some (R, o)) → Succ I C (pre ++ z :: post) →
    Succ I C (z :: (pre ++ post)) ∧
      I.runFrom C (Impl.blockWrite (pre ++ z :: post)) =
        I.runFrom C (Impl.blockWrite (z :: (pre ++ post)))
  | C, [], post, _, _, _, h => ⟨h, rfl⟩
  | C, a :: pre, post, hnd, hz, hpre, ⟨ha, i, o, k, Ca, hact, hso, hs, hβ⟩ => by
    have hnd' := List.nodup_cons.1 hnd
    have haz : a ≠ z := fun e => hnd'.1 (by simp [e])
    have hiR : i ≠ R := by
      rintro rfl
      exact hpre a List.mem_cons_self o (poisedAcc_eq_of_act hact)
    have hza := Impl.step_other hs (q := z) haz
    obtain ⟨h1, h2⟩ := succ_bubble (C := Ca) pre post hnd'.2
      (by rw [← poisedAcc_congr hza.1.symm]; exact hz)
      (fun b hb o' => by
        have hba : b ≠ a := fun e => hnd'.1 (by simp [← e, hb])
        rw [← poisedAcc_congr (Impl.step_other hs (q := b) (Ne.symm hba)).1.symm]
        exact hpre b (List.mem_cons_of_mem _ hb) o') hβ
    obtain ⟨hzp, j, oz', kz, Caz, hactz, hsoz, hsz, hβ'⟩ := h1
    have hjR : j = R := by
      have := poisedAcc_eq_of_act hactz
      rw [← poisedAcc_congr hza.1.symm, hz] at this
      exact (Prod.mk.inj (Option.some.inj this)).1.symm
    subst hjR
    rw [hza.1] at hactz
    obtain ⟨Cz, hCz, hCza⟩ := Impl.step_comm (I := I) haz rfl rfl hs hsz
      (fun i₁ o₁ k₁ j₁ o₂ k₂ _ h₁ _ h₂ => by
        rw [hact] at h₁; rw [hactz] at h₂
        simp only [Action.access.injEq] at h₁ h₂
        exact Or.inl (h₁.1 ▸ h₂.1 ▸ hiR))
    have hCa_mem : Ca.mem j = C.mem j := by
      obtain ⟨-, -, i', o', k', hact', hm, -⟩ := Impl.step_tau hs
      rw [hact] at hact'
      simp only [Action.access.injEq] at hact'
      rw [hm, ← hact'.1, Function.update_of_ne (Ne.symm hiR)]
    have hzC := Impl.step_other hCz (q := a) (Ne.symm haz)
    have hCz_mem : Cz.mem i = C.mem i := by
      obtain ⟨-, -, i', o', k', hact', hm, -⟩ := Impl.step_tau hCz
      rw [hactz] at hact'
      simp only [Action.access.injEq] at hact'
      rw [hm, ← hact'.1, Function.update_of_ne hiR]
    refine ⟨⟨by rw [← hza.2]; exact hzp, j, oz', kz, Cz, hactz, by rw [← hCa_mem]; exact hsoz,
      hCz, by rw [hzC.2]; exact ha, i, o, k, Caz, by rw [hzC.1]; exact hact,
      by rw [hCz_mem]; exact hso, hCza, hβ'⟩, ?_⟩
    simp only [List.cons_append, Impl.blockWrite_cons, Impl.runFrom_cons, hs, hCz, hCza,
      Option.bind_some] at h2 ⊢
    rw [h2]
    simp [hsz]

open Classical in
lemma wcov_congr {C C' : Cf} {S : Finset P} (h : ∀ p ∈ S, poisedAcc I C p = poisedAcc I C' p)
    (R : ι) : WCov I C R S = WCov I C' R S :=
  Finset.filter_congr fun p hp => by rw [h p hp]

open Classical in
lemma ccov_congr {C C' : Cf} {S : Finset P} (h : ∀ p ∈ S, poisedAcc I C p = poisedAcc I C' p)
    (R : ι) : CCov I C R S = CCov I C' R S :=
  Finset.filter_congr fun p hp => by rw [h p hp]

open Classical in
/-- Removing one process from the schedule decreases the covering counts by at most one. -/
lemma cov_insert_le {C C' : Cf} {S : Finset P} {z : P} (hz : z ∉ S)
    (h : ∀ p ∈ S, poisedAcc I C p = poisedAcc I C' p) (R : ι) :
    (WCov I C R (insert z S)).card ≤ (WCov I C' R S).card + 1 ∧
    (WCov I C R (insert z S)).card + (CCov I C R (insert z S)).card ≤
      (WCov I C' R S).card + (CCov I C' R S).card + 1 := by
  rw [← wcov_congr h, ← ccov_congr h]
  have hzW : z ∉ WCov I C R S := fun hm => hz (Finset.mem_filter.1 hm).1
  have hzC : z ∉ CCov I C R S := fun hm => hz (Finset.mem_filter.1 hm).1
  unfold WCov CCov at *
  rw [Finset.filter_insert, Finset.filter_insert]
  split_ifs with h1 h2 h2
  · obtain ⟨v, hv⟩ := h1; obtain ⟨x, y, hxy⟩ := h2
    rw [hv] at hxy; simp at hxy
  · rw [Finset.card_insert_of_notMem hzW]; omega
  · rw [Finset.card_insert_of_notMem hzC]; omega
  · omega

open Classical in
/-- A process poised to `CAS` does not count in `WCov`. -/
lemma wcov_insert_of_cas {C : Cf} {S : Finset P} {z : P} {R' : ι} {a b : V}
    (hz : poisedAcc I C z = some (R', .cas a b)) (R : ι) :
    WCov I C R (insert z S) = WCov I C R S := by
  unfold WCov
  rw [Finset.filter_insert, ite_eq_right]
  rintro ⟨v, hv⟩; rw [hz] at hv; simp at hv

open Classical in
/-- A process poised on `R'` does not count in `CCov(_, R)` for `R ≠ R'`. -/
lemma ccov_insert_of_ne {C : Cf} {S : Finset P} {z : P} {R R' : ι} {oz : WCasOp V}
    (hz : poisedAcc I C z = some (R', oz)) (hR : R ≠ R') :
    CCov I C R (insert z S) = CCov I C R S := by
  unfold CCov
  rw [Finset.filter_insert, ite_eq_right]
  rintro ⟨x, y, hv⟩; rw [hz] at hv; simp only [Option.some.injEq, Prod.mk.injEq] at hv
  exact hR hv.1.symm

/-- The conclusion of Lemma 2. -/
def L2Concl (I : Impl A (fun _ : ι => wcasObj V v₀) P L) (q : P) (t : ℕ) (C : Cf) (β : List P) :
    Prop :=
  ∃ D σ D', I.runFrom C (Impl.blockWrite β) = some D ∧ I.runFrom C σ = some D' ∧
    (∀ ℓ ∈ σ, ℓ.proc ∈ q :: β) ∧ (∀ p, opsOf σ p = []) ∧ Impl.AgreeOn {p | p ≠ q} D D' ∧
    (D'.pend q = none ∨
      (D'.pend q ≠ none ∧ ∃ R v, poisedAcc I D' q = some (R, .write v) ∧
        (WCov I C R β.toFinset).card < t) ∨
      (D'.pend q ≠ none ∧ ∃ R x y, poisedAcc I D' q = some (R, .cas x y) ∧ x ≠ y ∧
        D'.mem R = x ∧ (WCov I C R β.toFinset).card + (CCov I C R β.toFinset).card < t))

/-- Prepending a schedule `γ` to the schedule obtained for `(C', β')`. -/
lemma L2Concl.transfer {q : P} {t t' : ℕ} {C C' D D₁ : Cf} {β β' : List P}
    {γ : List (Label P A)} (hγ : I.runFrom C γ = some C') (hγp : ∀ ℓ ∈ γ, ℓ.proc ∈ q :: β)
    (hγo : ∀ p, opsOf γ p = []) (hβ' : ∀ p ∈ β', p ∈ β)
    (hD : I.runFrom C (Impl.blockWrite β) = some D)
    (hD₁ : I.runFrom C' (Impl.blockWrite β') = some D₁) (hag : Impl.AgreeOn {p | p ≠ q} D D₁)
    (hb : ∀ R, (WCov I C' R β'.toFinset).card < t' → (WCov I C R β.toFinset).card < t)
    (hc : ∀ R, (WCov I C' R β'.toFinset).card + (CCov I C' R β'.toFinset).card < t' →
      (WCov I C R β.toFinset).card + (CCov I C R β.toFinset).card < t)
    (ih : L2Concl I q t' C' β') : L2Concl I q t C β := by
  obtain ⟨D₂, σ', D', h1, h2, h3, h4, h5, h6⟩ := ih
  rw [hD₁] at h1; cases h1
  refine ⟨D, γ ++ σ', D', hD, by rw [Impl.runFrom_append_of_eq I hγ, h2], ?_, ?_,
    hag.trans h5, ?_⟩
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with h | h
    · exact hγp ℓ h
    · rcases List.mem_cons.1 (h3 ℓ h) with e | e
      · rw [e]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hβ' _ e)
  · intro p; rw [opsOf_append, hγo, h4]; rfl
  · rcases h6 with h | ⟨hp, R, v, hv, hcard⟩ | ⟨hp, R, x, y, hv, hxy, hm, hcard⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hp, R, v, hv, hb R hcard⟩)
    · exact Or.inr (Or.inr ⟨hp, R, x, y, hv, hxy, hm, hc R hcard⟩)

omit [DecidableEq P] in
lemma toFinset_split [DecidableEq P] (pre post : List P) (z : P) :
    (pre ++ z :: post).toFinset = insert z (pre ++ post).toFinset := by
  ext p; simp only [List.mem_toFinset, List.mem_append, List.mem_cons, Finset.mem_insert]; tauto

/-- The common step of the cases where `q` and the first process `z` of `β` on `q`'s object
both take a step (schedule `γ`), and the result agrees with `Conf(C, z)` on all `p ≠ q`. -/
lemma L2Concl.zcase {q z : P} {t' : ℕ} {C Cz C' D : Cf} {pre post : List P}
    {γ : List (Label P A)} (hnd : (pre ++ z :: post).Nodup) (hq : q ∉ pre ++ z :: post)
    (hD : I.runFrom C (Impl.blockWrite (pre ++ z :: post)) = some D)
    (hD' : I.runFrom Cz (Impl.blockWrite (pre ++ post)) = some D)
    (hβ' : Succ I Cz (pre ++ post)) (hγ : I.runFrom C γ = some C')
    (hγp : ∀ ℓ ∈ γ, ℓ.proc = q ∨ ℓ.proc = z) (hγo : ∀ p, opsOf γ p = [])
    (hag : Impl.AgreeOn {p | p ≠ q} Cz C')
    (ih : Succ I C' (pre ++ post) → L2Concl I q t' C' (pre ++ post)) :
    L2Concl I q (t' + 1) C (pre ++ z :: post) := by
  have hβq : ∀ p ∈ pre ++ post, p ∈ {p | p ≠ q} := fun p hp e => hq (by
    subst e; simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto)
  obtain ⟨hs', D₂, D₁, h1, h2, h3⟩ := Succ.agreeOn hag hβq hβ'
  rw [hD'] at h1; cases h1
  have hz : z ∉ pre ++ post := by
    have := List.nodup_middle.1 hnd
    exact (List.nodup_cons.1 this).1
  have hsub : ∀ p ∈ pre ++ post, p ∈ pre ++ z :: post := fun p hp => by
    simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto
  have hpa : ∀ p ∈ (pre ++ post).toFinset, poisedAcc I C p = poisedAcc I C' p := by
    intro p hp
    have hp := List.mem_toFinset.1 hp
    have hpz : p ≠ z := fun e => hz (e ▸ hp)
    have hpq : p ≠ q := hβq p hp
    refine poisedAcc_congr (I.runFrom_other hγ fun ℓ hℓ e => ?_).1.symm
    rcases hγp ℓ hℓ with h | h
    · exact hpq (e ▸ h)
    · exact hpz (e ▸ h)
  have hzS : z ∉ (pre ++ post).toFinset := fun h => hz (List.mem_toFinset.1 h)
  refine L2Concl.transfer hγ (fun ℓ hℓ => ?_) hγo hsub hD h2 h3 (fun R h => ?_) (fun R h => ?_)
    (ih hs')
  · rcases hγp ℓ hℓ with h | h
    · rw [h]; exact List.mem_cons_self
    · rw [h]; exact List.mem_cons_of_mem _ (by simp)
  · rw [toFinset_split]; have := (cov_insert_le hzS hpa R).1; omega
  · rw [toFinset_split]; have := (cov_insert_le hzS hpa R).2; omega

open Classical in
/-- Lemma 2, by strong induction on `t + |β|`. -/
lemma lemma2_aux (q : P) (n : ℕ) : ∀ (t : ℕ) (C : Cf) (β : List P), t + β.length = n →
    q ∉ β → β.Nodup → Succ I C β → Budget I C q t → L2Concl I q t C β := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t C β hn hq hnd hs hb
  obtain ⟨D, hD⟩ := Succ.run hs
  have hDq := I.runFrom_blockWrite_other hD hq
  have hbw : ∀ ℓ ∈ (Impl.blockWrite β : List (Label P A)), ℓ.proc ∈ q :: β :=
    fun ℓ hℓ => List.mem_cons_of_mem _ (Impl.mem_blockWrite hℓ)
  have hβq : ∀ p ∈ β, p ∈ {p | p ≠ q} := fun p hp e => hq (e ▸ hp)
  by_cases hp : C.pend q = none
  · exact ⟨D, _, D, hD, hD, hbw, fun p => Impl.opsOf_blockWrite β p, Impl.AgreeOn.refl _ _,
      Or.inl (hDq.2.trans hp)⟩
  cases hact : I.act q (C.loc q) with
  | ret r l =>
    have hDs := Impl.step_ret_eq_some (I := I) (C := D) (by rw [hDq.2]; exact hp)
      (by rw [hDq.1]; exact hact)
    refine ⟨D, Impl.blockWrite β ++ [.ret q r], _, hD,
      by rw [Impl.runFrom_append_of_eq I hD, Impl.runFrom_singleton, hDs], ?_, ?_, ?_,
      Or.inl (by simp)⟩
    · intro ℓ hℓ
      rcases List.mem_append.1 hℓ with h | h
      · exact hbw ℓ h
      · rw [List.mem_singleton.1 h]; exact List.mem_cons_self
    · intro p; simp
    · exact ⟨rfl, fun p hp => by simp [Function.update_of_ne (show p ≠ q from hp)],
        fun p hp => by simp [Function.update_of_ne (show p ≠ q from hp)]⟩
  | access X o k =>
    have hsq0 := step_tau_eq (I := I) hp hact
    obtain ⟨Cq, hsq⟩ : ∃ Cq, I.step C (.tau q) = some Cq := ⟨_, hsq0⟩
    clear hsq0
    cases t with
    | zero => exact (budget_zero hb hsq).elim
    | succ t' =>
    by_cases hmod : SOp (C.mem X) o
    swap
    · -- `q`'s step does not change the memory: let `q` take it
      have hnm : ((wcasObj V v₀).δ (C.mem X) o).1 = C.mem X := by
        cases o with
        | read => rfl
        | write v => exact (hmod trivial).elim
        | cas x y =>
          show (if C.mem X = x then y else C.mem X) = C.mem X
          split_ifs with h
          · by_cases hxy : x = y
            · rw [← hxy, h]
            · exact (hmod ⟨hxy, h⟩).elim
          · rfl
      have hag := agreeOn_step_nonmod hact hnm hsq
      obtain ⟨hs', D₂, D₁, h1, h2, h3⟩ := Succ.agreeOn hag hβq hs
      rw [hD] at h1; cases h1
      have hpa : ∀ p ∈ β.toFinset, poisedAcc I C p = poisedAcc I Cq p := fun p hp =>
        poisedAcc_congr (hag.loc p (hβq p (List.mem_toFinset.1 hp)))
      refine L2Concl.transfer (γ := [.tau q]) (by simp [hsq]) (by simp [Label.proc]) (fun p => rfl)
        (fun p hp => hp) hD h2 h3 (fun R h => ?_) (fun R h => ?_)
        (ih (t' + β.length) (by omega) t' Cq β rfl hq hnd hs' (budget_step_self hb hsq))
      · rw [wcov_congr hpa]; omega
      · rw [wcov_congr hpa, ccov_congr hpa]; omega
    have hpaD : poisedAcc I D q = some (X, o) := by
      rw [poisedAcc_congr hDq.1, poisedAcc_eq_of_act hact]
    have hpD : D.pend q ≠ none := by rw [hDq.2]; exact hp
    rcases exists_first_split (fun p => ∃ o', poisedAcc I C p = some (X, o')) β with
      hnone | ⟨pre, z, post, rfl, ⟨oz, hz⟩, hpre⟩
    · -- no process of `β` accesses `q`'s object
      have hDX : D.mem X = C.mem X :=
        mem_runFrom_blockWrite_of_not_on hnd (fun p hp o' h => hnone p hp ⟨o', h⟩) hD
      have hW0 : WCov I C X β.toFinset = ∅ := Finset.filter_eq_empty_iff.2
        fun p hp ⟨v, hv⟩ => hnone p (List.mem_toFinset.1 hp) ⟨_, hv⟩
      have hC0 : CCov I C X β.toFinset = ∅ := Finset.filter_eq_empty_iff.2
        fun p hp ⟨x, y, hv⟩ => hnone p (List.mem_toFinset.1 hp) ⟨_, hv⟩
      cases o with
      | read => exact hmod.elim
      | write v =>
        exact ⟨D, _, D, hD, hD, hbw, fun p => Impl.opsOf_blockWrite β p, Impl.AgreeOn.refl _ _,
          Or.inr (Or.inl ⟨hpD, X, v, hpaD, by simp [hW0]⟩)⟩
      | cas x y =>
        exact ⟨D, _, D, hD, hD, hbw, fun p => Impl.opsOf_blockWrite β p, Impl.AgreeOn.refl _ _,
          Or.inr (Or.inr ⟨hpD, X, x, y, hpaD, hmod.1, by rw [hDX]; exact hmod.2,
            by simp [hW0, hC0]⟩)⟩
    · -- `z` is the first process of `β` accessing `q`'s object
      have hzq : z ≠ q := fun e => hq (by simp [e])
      obtain ⟨hsucc', hrun'⟩ := succ_bubble pre post hnd hz (fun a ha o' h => hpre a ha ⟨o', h⟩) hs
      obtain ⟨hzp, j, oz', kz, Cz, hactz, hsoz, hsz, hβ'⟩ := hsucc'
      have hjo : j = X ∧ oz' = oz := by
        have := poisedAcc_eq_of_act hactz
        rw [hz] at this
        simp only [Option.some.injEq, Prod.mk.injEq] at this
        exact ⟨this.1.symm, this.2.symm⟩
      obtain ⟨hjX, hoo⟩ := hjo
      subst j oz'
      have hD' : I.runFrom Cz (Impl.blockWrite (pre ++ post)) = some D := by
        rw [← hD, hrun']; simp [hsz]
      have hnd' : (pre ++ post).Nodup := (List.nodup_cons.1 (List.nodup_middle.1 hnd)).2
      have hq' : q ∉ pre ++ post := fun h => hq (by
        simp only [List.mem_append, List.mem_cons] at h ⊢; tauto)
      have hlen : (pre ++ z :: post).length = (pre ++ post).length + 1 := by simp; omega
      have hCz := Impl.step_other hsz (q := q) (by simpa [Label.proc] using hzq)
      cases oz with
      | read => exact hsoz.elim
      | write w =>
        -- `q` takes its step, then `z` overwrites it
        obtain ⟨C', hsz'⟩ : ∃ C', I.step Cq (.tau z) = some C' := by
          have hCq := Impl.step_other hsq (q := z) (by simpa [Label.proc] using hzq.symm)
          exact ⟨_, step_tau_eq (I := I) (by rw [hCq.2]; exact hzp) (by rw [hCq.1]; exact hactz)⟩
        exact L2Concl.zcase hnd hq hD hD' hβ' (γ := [.tau q, .tau z]) (by simp [hsq, hsz'])
          (by simp [Label.proc]) (fun p => rfl) (agreeOn_absorb hzq hact hactz hsq hsz' hsz).symm
          (fun hs' => ih _ (by omega) t' C' _ rfl hq' hnd' hs'
            (budget_step_other (budget_step_self hb hsq) (by simpa [Label.proc] using hzq) hsz'))
      | cas a b =>
        cases o with
        | read => exact hmod.elim
        | cas x y =>
          -- `z`'s CAS succeeds, then `q`'s CAS fails
          have hCzX : Cz.mem X = b := by
            have h := hsz
            rw [step_tau_eq hzp hactz] at h; cases h; simp [hsoz.2]
          obtain ⟨C', hsq'⟩ : ∃ C', I.step Cz (.tau q) = some C' :=
            ⟨_, step_tau_eq (I := I) (by rw [hCz.2]; exact hp) (by rw [hCz.1]; exact hact)⟩
          have hag := agreeOn_step_nonmod (I := I) (by rw [hCz.1]; exact hact) (by
            show (if Cz.mem X = x then y else Cz.mem X) = Cz.mem X
            rw [ite_eq_right]; rw [hCzX]; intro e
            exact hsoz.1 (hsoz.2.symm.trans (hmod.2.trans e.symm))) hsq'
          exact L2Concl.zcase hnd hq hD hD' hβ' (γ := [.tau z, .tau q]) (by simp [hsz, hsq'])
            (by simp [Label.proc]) (fun p => rfl) hag
            (fun hs' => ih _ (by omega) t' C' _ rfl hq' hnd' hs'
              (budget_step_self (budget_step_other hb (by simpa [Label.proc] using hzq) hsz)
                hsq'))
        | write v =>
          by_cases hlt : (WCov I C X (pre ++ z :: post).toFinset).card < t' + 1
          · exact ⟨D, _, D, hD, hD, hbw, fun p => Impl.opsOf_blockWrite _ p,
              Impl.AgreeOn.refl _ _, Or.inr (Or.inl ⟨hpD, X, v, hpaD, hlt⟩)⟩
          · -- only `z` takes a step; the bound on `WCov(C, X)` excludes cases (b), (c) on `X`
            have hpa' : ∀ p ∈ (pre ++ post).toFinset, poisedAcc I C p = poisedAcc I Cz p := by
              intro p hp
              have hp := List.mem_toFinset.1 hp
              have hpz : p ≠ z := fun e => (List.nodup_cons.1 (List.nodup_middle.1 hnd)).1 (e ▸ hp)
              exact poisedAcc_congr (Impl.step_other hsz (q := p)
                (by simpa [Label.proc] using hpz.symm)).1.symm
            refine L2Concl.transfer (γ := [.tau z]) (by simp [hsz]) (by simp [Label.proc]) (fun p => rfl)
              (fun p hp => by simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto)
              hD hD' (Impl.AgreeOn.refl _ _) (fun R h => ?_) (fun R h => ?_)
              (ih _ (by omega) (t' + 1) Cz _ rfl hq' hnd' hβ'
                (budget_step_other hb (by simpa [Label.proc] using hzq) hsz))
            · rw [toFinset_split, wcov_insert_of_cas hz, wcov_congr hpa']; exact h
            · rw [toFinset_split, wcov_insert_of_cas hz, wcov_congr hpa']
              by_cases hRX : R = X
              · subst hRX
                exfalso; apply hlt
                rw [toFinset_split, wcov_insert_of_cas hz, wcov_congr hpa']; omega
              · rw [ccov_insert_of_ne hz hRX, ccov_congr hpa']; exact h

/-- **Lemma 2** of [Aghazadeh–Woelfel, PODC 2015]. -/
theorem lemma2 (q : P) : ∀ (t : ℕ) (C : Config A (fun _ : ι => wcasObj V v₀) P L) (β : List P),
    q ∉ β → β.Nodup → Succ I C β → Budget I C q t →
    ∃ D σ D', I.runFrom C (Impl.blockWrite β) = some D ∧ I.runFrom C σ = some D' ∧
      (∀ ℓ ∈ σ, ℓ.proc ∈ q :: β) ∧ (∀ p, opsOf σ p = []) ∧ Impl.AgreeOn {p | p ≠ q} D D' ∧
      (D'.pend q = none ∨
        (D'.pend q ≠ none ∧ ∃ R v, poisedAcc I D' q = some (R, .write v) ∧
          (WCov I C R β.toFinset).card < t) ∨
        (D'.pend q ≠ none ∧ ∃ R x y, poisedAcc I D' q = some (R, .cas x y) ∧ x ≠ y ∧
          D'.mem R = x ∧ (WCov I C R β.toFinset).card + (CCov I C R β.toFinset).card < t)) :=
  fun t C β hq hnd hs hb => lemma2_aux q _ t C β rfl hq hnd hs hb

end Cslib.SharedMemory.ABADetection
