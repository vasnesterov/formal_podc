import Papers.PODC2016.RWLockRMRTradeoff.Regions

/-!
# Awareness and familiarity sets: basic facts

Observation 1 (awareness sets only grow), Observation 2 / the bound `|F(v)| ≤ max_p |AW(p)|`,
Fact 1 (an expanding step is a reading step and only the stepping process's awareness set
grows).
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq ι] [DecidableEq V] [DecidableEq P] {v₀ : V}
variable {I : Impl A (Regs ι V v₀) P L} {cm : CacheModel P ι}

section KStep

variable (I)

lemma kstep_read {C : Config A (Regs ι V v₀) P L} {K : Know P ι} {p : P} {i : ι}
    {k : (rwcas V v₀).Resp → L} (hact : I.act p (C.loc p) = .access i (CASOp.read : CASOp V) k) :
    kstep I C K (.tau p) = { K with aw := Function.update K.aw p (K.aw p ∪ K.fam i) } := by
  simp [kstep, hact]

lemma kstep_write {C : Config A (Regs ι V v₀) P L} {K : Know P ι} {p : P} {i : ι} {v : V}
    {k : (rwcas V v₀).Resp → L} (hact : I.act p (C.loc p) = .access i (CASOp.write v) k) :
    kstep I C K (.tau p) =
      if C.mem i = v then K else { K with fam := Function.update K.fam i (K.aw p) } := by
  simp [kstep, hact]

lemma kstep_cas {C : Config A (Regs ι V v₀) P L} {K : Know P ι} {p : P} {i : ι} {a b : V}
    {k : (rwcas V v₀).Resp → L} (hact : I.act p (C.loc p) = .access i (CASOp.cas a b) k) :
    kstep I C K (.tau p) =
      { aw := Function.update K.aw p (K.aw p ∪ K.fam i)
        fam := if C.mem i = a ∧ b ≠ a then Function.update K.fam i (K.aw p ∪ K.fam i)
          else K.fam } := by
  simp [kstep, hact]

lemma kstep_of_not_tau {C : Config A (Regs ι V v₀) P L} {K : Know P ι} {ℓ : Label P A}
    (h : ∀ p, ℓ ≠ .tau p) : kstep I C K ℓ = K := by
  cases ℓ with
  | tau p => exact absurd rfl (h p)
  | _ => rfl

lemma kstep_tau_ret {C : Config A (Regs ι V v₀) P L} {K : Know P ι} {p : P} {r : A.Resp} {l : L}
    (hact : I.act p (C.loc p) = .ret r l) : kstep I C K (.tau p) = K := by
  simp [kstep, hact]

/-- **Observation 1** (one step): awareness sets only grow, and only the stepping process's. -/
lemma kstep_aw (C : Config A (Regs ι V v₀) P L) (K : Know P ι) (ℓ : Label P A) (q : P) :
    K.aw q ⊆ (kstep I C K ℓ).aw q ∧ (ℓ.proc ≠ q → (kstep I C K ℓ).aw q = K.aw q) := by
  cases ℓ with
  | inv p o => simp [kstep]
  | ret p r => simp [kstep]
  | tau p =>
    simp only [Label.proc]
    cases hact : I.act p (C.loc p) with
    | ret r l => simp [kstep_tau_ret I hact]
    | access i o k =>
      cases o with
      | read =>
        rw [kstep_read I hact]
        by_cases hq : p = q
        · subst hq; simp
        · simp [Function.update_of_ne (Ne.symm hq), hq]
      | write v => rw [kstep_write I hact]; split_ifs <;> simp
      | cas a b =>
        rw [kstep_cas I hact]
        by_cases hq : p = q
        · subst hq; simp
        · simp [Function.update_of_ne (Ne.symm hq), hq]

/-- Familiarity sets change only at the variable accessed by the label. -/
lemma kstep_fam_of_ne (C : Config A (Regs ι V v₀) P L) (K : Know P ι) (ℓ : Label P A) (j : ι)
    (h : ∀ p i o k, ℓ = .tau p → I.act p (C.loc p) = .access i o k → i ≠ j) :
    (kstep I C K ℓ).fam j = K.fam j := by
  cases ℓ with
  | inv p o => rfl
  | ret p r => rfl
  | tau p =>
    cases hact : I.act p (C.loc p) with
    | ret r l => simp [kstep_tau_ret I hact]
    | access i o k =>
      have hij := h p i o k rfl hact
      cases o with
      | read => rw [kstep_read I hact]
      | write v => rw [kstep_write I hact]; split_ifs <;> simp [Function.update_of_ne (Ne.symm hij)]
      | cas a b => rw [kstep_cas I hact]; split_ifs <;> simp [Function.update_of_ne (Ne.symm hij)]

end KStep

/-! ### Invariants of knowledge along a fragment -/

/-- Invariants of the knowledge along a fragment: every process is aware of itself, and every
familiarity set is contained in some awareness set (Observations 1 and 2). -/
structure KInv (K : Know P ι) : Prop where
  self_mem : ∀ p, p ∈ K.aw p
  fam_sub : ∀ i, K.fam i = ∅ ∨ ∃ q, K.fam i ⊆ K.aw q

lemma KInv.init : KInv (Know.init : Know P ι) :=
  ⟨fun p => by simp [Know.init], fun i => Or.inl rfl⟩

lemma KInv.step {K : Know P ι} (hK : KInv K) (C : Config A (Regs ι V v₀) P L)
    (ℓ : Label P A) : KInv (kstep I C K ℓ) := by
  have haw := kstep_aw I C K ℓ
  refine ⟨fun q => (haw q).1 (hK.self_mem q), fun j => ?_⟩
  -- old familiarity sets stay below the (grown) awareness sets
  have hold : ∀ j, K.fam j = ∅ ∨ ∃ q, K.fam j ⊆ (kstep I C K ℓ).aw q := fun j =>
    (hK.fam_sub j).imp_right fun ⟨q, hq⟩ => ⟨q, hq.trans (haw q).1⟩
  cases ℓ with
  | inv p o => exact hK.fam_sub j
  | ret p r => exact hK.fam_sub j
  | tau p =>
    cases hact : I.act p (C.loc p) with
    | ret r l => rw [kstep_tau_ret I hact]; exact hK.fam_sub j
    | access i o k =>
      cases o with
      | read => rw [kstep_read I hact] at hold ⊢; exact hold j
      | write v =>
        rw [kstep_write I hact] at hold ⊢
        split_ifs at hold ⊢ with h1
        · exact hK.fam_sub j
        · by_cases hj : j = i
          · subst hj; exact Or.inr ⟨p, by simp⟩
          · simp only [Function.update_of_ne hj]; exact hold j
      | cas a b =>
        rw [kstep_cas I hact] at hold ⊢
        split_ifs with h1
        · by_cases hj : j = i
          · subst hj; exact Or.inr ⟨p, by simp⟩
          · simp only [Function.update_of_ne hj]; exact hold j
        · exact hold j

/-- `|F(v)| ≤ max_p |AW(p)|`. -/
lemma KInv.card_fam_le {K : Know P ι} (hK : KInv K) (i : ι) {B : ℕ}
    (hB : ∀ q, (K.aw q).card ≤ B) : (K.fam i).card ≤ B := by
  rcases hK.fam_sub i with h | ⟨q, hq⟩
  · simp [h]
  · exact (Finset.card_le_card hq).trans (hB q)

/-! ### Fact 1 -/

/-- **Fact 1.** An expanding step is a reading step (read or CAS) of some process `p` on some
variable `v` with `F(v) ⊄ AW(p)`; it only enlarges `AW(p)`, by `F(v)`. -/
lemma expanding_iff {X : Ext I cm} {ℓ : Label P A} :
    Expanding X ℓ ↔ ∃ p i o k, ℓ = .tau p ∧ I.act p (X.cfg.loc p) = .access i o k ∧
      (o = CASOp.read ∨ ∃ a b, o = CASOp.cas a b) ∧ ¬ X.kn.fam i ⊆ X.kn.aw p := by
  constructor
  · rintro ⟨q, hq⟩
    have haw := kstep_aw I X.cfg X.kn ℓ q
    have hpq : ℓ.proc = q := by
      by_contra h; rw [haw.2 h] at hq; exact lt_irrefl _ hq
    cases ℓ with
    | inv p o => simp [kstep] at hq
    | ret p r => simp [kstep] at hq
    | tau p =>
      simp only [Label.proc] at hpq; subst hpq
      cases hact : I.act p (X.cfg.loc p) with
      | ret r l => rw [kstep_tau_ret I hact] at hq; exact absurd hq (lt_irrefl _)
      | access i o k =>
        refine ⟨p, i, o, k, rfl, hact, ?_, ?_⟩
        · cases o with
          | read => exact Or.inl rfl
          | write v =>
            rw [kstep_write I hact] at hq; split_ifs at hq <;> simp at hq
          | cas a b => exact Or.inr ⟨a, b, rfl⟩
        · intro hsub
          cases o with
          | read =>
            rw [kstep_read I hact] at hq
            simp [Finset.union_eq_left.2 hsub] at hq
          | write v =>
            rw [kstep_write I hact] at hq; split_ifs at hq <;> simp at hq
          | cas a b =>
            rw [kstep_cas I hact] at hq
            simp [Finset.union_eq_left.2 hsub] at hq
  · rintro ⟨p, i, o, k, rfl, hact, ho, hsub⟩
    refine ⟨p, ?_⟩
    have : (kstep I X.cfg X.kn (.tau p)).aw p = X.kn.aw p ∪ X.kn.fam i := by
      rcases ho with rfl | ⟨a, b, rfl⟩
      · rw [kstep_read I hact]; simp
      · rw [kstep_cas I hact]; simp
    rw [this]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, fun h => hsub ?_⟩
    rw [h]; exact Finset.subset_union_right

/-! ### Runs -/

lemma xrun_aw_mono {X Y : Ext I cm} {α : List (Label P A)} (h : xrun X α = some Y) (q : P) :
    X.kn.aw q ⊆ Y.kn.aw q := by
  induction α generalizing X with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; exact subset_rfl
  | cons ℓ α ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      have := (xstep_eq_some.1 hs).2.1
      exact (this ▸ (kstep_aw I X.cfg X.kn ℓ q).1).trans (ih h)

lemma xrun_aw_of_not_mem {X Y : Ext I cm} {α : List (Label P A)} (h : xrun X α = some Y) (q : P)
    (hq : ∀ ℓ ∈ α, ℓ.proc ≠ q) : Y.kn.aw q = X.kn.aw q := by
  induction α generalizing X with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      have := (xstep_eq_some.1 hs).2.1
      rw [ih h (fun ℓ' h' => hq ℓ' (List.mem_cons_of_mem _ h')), this]
      exact (kstep_aw I X.cfg X.kn ℓ q).2 (hq ℓ List.mem_cons_self)

lemma xrun_kinv {X Y : Ext I cm} {α : List (Label P A)} (h : xrun X α = some Y) (hK : KInv X.kn) :
    KInv Y.kn := by
  induction α generalizing X with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; exact hK
  | cons ℓ α ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      exact ih h ((xstep_eq_some.1 hs).2.1 ▸ hK.step X.cfg ℓ)

end Podc.RWLockRMRTradeoff
