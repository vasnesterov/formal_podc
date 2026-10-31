import Papers.PODC2011.CCvsDSMSeparation.Advance

/-!
# Rolling a process forward (roll-forward case of the proof of Lemma 6.10)

A process `r` that is not active any more completes its current call running solo. Whenever it is
about to see or touch an active process, that process is erased first. Rather than erasing on the
fly, we let `r` run solo in the history where *all* active processes are erased (where its call
completes because the algorithm is terminating), collect the set `E` of active processes whose
module or last writes `r` accesses, erase exactly `E`, and replay `r`'s run. Each process of `E`
costs `r` a distinct RMR, so `|E|` is bounded by the RMRs of a history with few participants.
-/

namespace Podc.CCvsDSMSeparation

variable {N : ℕ} {V Val S : Type*}

namespace Algorithm

variable (A : Algorithm N V Val S)

/-- The supposition of the proof (towards a contradiction): every execution with at most one call
to `Signal()` and at most `K` participants incurs at most `c` RMRs per participant. -/
def AmortBound (c K : ℕ) : Prop :=
  ∀ τ : List (Ev N V Val), A.Valid τ → signals τ ≤ 1 → (par τ).card ≤ K →
    A.rmr τ ≤ c * (par τ).card

/-- Distinct variables accessed remotely by `σ` give distinct RMRs. -/
lemma card_le_rmr_of_injOn {ι : Type*} {E : Finset ι} {σ : List (Ev N V Val)} (f : ι → V)
    (hf : Set.InjOn f E)
    (hacc : ∀ q ∈ E, ∃ e ∈ σ, e.op.var = some (f q) ∧ e.remote A.home = true) :
    E.card ≤ A.rmr σ := by
  classical
  set X : Finset V := ((σ.filter fun e => e.remote A.home).filterMap fun e => e.op.var).toFinset
  have h1 : E.card ≤ X.card := by
    refine Finset.card_le_card_of_injOn f (fun q hq => ?_) hf
    obtain ⟨e, he, hv, hr⟩ := hacc q hq
    simp only [X]
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_filterMap]
    exact ⟨e, List.mem_filter.2 ⟨he, by simp [hr]⟩, hv⟩
  have h2 : X.card ≤ A.rmr σ := by
    refine (List.toFinset_card_le _).trans ?_
    refine (List.length_filterMap_le _ _).trans ?_
    simp [rmr, List.countP_eq_length_filter]
  omega

lemma idle_erase_of_settled {B : Finset (Fin N)} {τ : List (Ev N V Val)} {r : Fin N}
    (h : A.Settled (insert r B) τ) : ∀ q, q ≠ r → A.Idle (erase B τ) q := by
  intro q hqr
  by_cases hqB : q ∈ B
  · refine A.idle_of_not_par ?_
    rw [par_erase]; simp [hqB]
  · refine A.idle_of_proj_eq ?_ (proj_erase_of_not_mem τ hqB)
    by_cases hq : q ∈ par τ
    · exact h q hq (by simp [hqr, hqB])
    · exact A.idle_of_not_par hq

/-- **Roll-forward.** -/
lemma roll_forward {c K : ℕ} (hT : A.SoloTerminating) (hb : A.AmortBound c K)
    {τ : List (Ev N V Val)} {B : Finset (Fin N)} {r : Fin N} {o : Proc}
    (hv : A.Valid τ) (hsig : signals τ = 0) (hreg : A.Regular B τ)
    (hnt : A.NoTouch (insert r B) τ) (hset : A.Settled (insert r B) τ) (hr : r ∉ B)
    (hbusy : A.Busy τ r o) (hK : ((par τ \ B) ∪ {r}).card ≤ K) :
    ∃ E ⊆ B, E.card ≤ c * ((par τ \ B) ∪ {r}).card ∧ ∃ σ : List (Ev N V Val),
      (∀ e ∈ σ, e.p = r) ∧ A.Valid (erase E τ ++ σ) ∧ signals (erase E τ ++ σ) = 0 ∧
      A.Regular (B \ E) (erase E τ ++ σ) ∧ A.Settled (B \ E) (erase E τ ++ σ) ∧
      par (erase E τ ++ σ) \ (B \ E) ⊆ (par τ \ B) ∪ {r} := by
  classical
  set G := erase B τ with hG
  have hvG : A.Valid G := hreg.valid_erase A hv subset_rfl
  have hsigG : signals G = 0 := Nat.le_zero.1 (hsig ▸ signals_erase_le B τ)
  obtain ⟨σ₀, b, hσ₀, hvGσ⟩ := hT G r o hvG (by omega) (A.idle_erase_of_settled hset)
    (A.busy_of_proj_eq hbusy (proj_erase_of_not_mem τ hr))
  set σ := σ₀ ++ [⟨r, .ret b⟩] with hσ
  have hσr : ∀ e ∈ σ, e.p = r := by
    intro e he; rcases List.mem_append.1 he with he | he
    · exact (hσ₀ e he).1
    · simp at he; subst he; rfl
  have hσsig : signals σ = 0 := by
    refine signals_eq_zero fun e he => ?_
    rcases List.mem_append.1 he with he | he
    · exact Op.isSigInv_eq_false_of_isAccess (hσ₀ e he).2
    · simp at he; subst he; rfl
  have hvGσ' : A.Valid (G ++ σ) := by rw [hσ, ← List.append_assoc]; exact hvGσ
  -- the bound on `r`'s RMRs
  have hparGσ : par (G ++ σ) ⊆ (par τ \ B) ∪ {r} := by
    rw [par_append, hG, par_erase]
    exact Finset.union_subset_union subset_rfl (par_subset_of_forall (fun e he => by
      simp [hσr e he]))
  have hrmr : A.rmr σ ≤ c * ((par τ \ B) ∪ {r}).card := by
    calc A.rmr σ ≤ A.rmr (G ++ σ) := A.rmr_le_rmr_append_left _ _
      _ ≤ c * (par (G ++ σ)).card :=
          hb _ hvGσ' (by rw [signals_append, hsigG, hσsig]; omega)
            ((Finset.card_le_card hparGσ).trans hK)
      _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card hparGσ)
  -- the processes to erase
  set D : Fin N → V → Prop := fun q v => A.home v = q ∨ writer v τ = some q with hD
  set E := B.filter fun q => ∃ e ∈ σ, ∃ v, e.op.var = some v ∧ D q v with hE
  have hEB : E ⊆ B := Finset.filter_subset _ _
  have hDdisj : ∀ q₁ ∈ B, ∀ q₂ ∈ B, ∀ v, D q₁ v → D q₂ v → q₁ = q₂ := by
    have key : ∀ q₁ ∈ B, ∀ q₂ v, A.home v = q₁ → writer v τ = some q₂ → q₁ = q₂ := by
      intro q₁ hq₁ q₂ v hh hw
      obtain ⟨e, he, rfl, hwe⟩ := writer_mem hw
      exact hnt e he v hwe.var q₁ (by rw [hh]) (Finset.mem_insert_of_mem hq₁)
    intro q₁ hq₁ q₂ hq₂ v h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact h1.symm.trans h2
    · exact key q₁ hq₁ q₂ v h1 h2
    · exact (key q₂ hq₂ q₁ v h2 h1).symm
    · rw [h1] at h2; cases h2; rfl
  have hEcard : E.card ≤ c * ((par τ \ B) ∪ {r}).card := by
    refine le_trans ?_ hrmr
    have hch : ∀ q ∈ E, ∃ v, (∃ e ∈ σ, e.op.var = some v) ∧ D q v := by
      intro q hq
      obtain ⟨-, e, he, v, hv, hd⟩ := Finset.mem_filter.1 hq
      exact ⟨v, ⟨e, he, hv⟩, hd⟩
    rcases E.eq_empty_or_nonempty with h0 | ⟨q0, hq0⟩
    · simp [h0]
    have : Nonempty V := ⟨(hch q0 hq0).choose⟩
    choose! f hf using hch
    refine A.card_le_rmr_of_injOn f ?_ ?_
    · intro q₁ hq₁ q₂ hq₂ heq
      exact hDdisj q₁ (hEB hq₁) q₂ (hEB hq₂) (f q₁) (hf q₁ hq₁).2
        (by rw [heq]; exact (hf q₂ hq₂).2)
    · intro q hq
      obtain ⟨⟨e, he, hv⟩, hd⟩ := hf q hq
      refine ⟨e, he, hv, A.remote_of_var hv ?_⟩
      rw [hσr e he]
      have hqB := hEB hq
      have hqr : q ≠ r := fun h' => hr (h' ▸ hqB)
      rcases hd with hd | hd
      · rw [hd]; exact hqr
      · intro hh
        obtain ⟨e', he', rfl, hwe⟩ := writer_mem hd
        exact hqr (hnt e' he' (f e'.p) hwe.var r (by rw [hh]) (Finset.mem_insert_self _ _)).symm
  -- variables accessed by `r` have no active last writer after erasing `E`
  have hacc : ∀ e ∈ σ, ∀ v, e.op.var = some v →
      A.home v ∉ B \ E ∧ ∀ q ∈ B \ E, writer v (erase E τ) ≠ some q := by
    intro e he v hv
    constructor
    · intro hh
      rw [Finset.mem_sdiff] at hh
      exact hh.2 (Finset.mem_filter.2 ⟨hh.1, e, he, v, hv, Or.inl rfl⟩)
    · intro q hq hw
      rw [Finset.mem_sdiff] at hq
      have := (hreg.sole v).writer_of_erase hEB hw hq.1
      exact hq.2 (Finset.mem_filter.2 ⟨hq.1, e, he, v, hv, Or.inr this⟩)
  have hGE : G = erase (B \ E) (erase E τ) := by
    rw [hG, erase_erase, Finset.sdiff_union_of_subset hEB]
  have hvE : A.Valid (erase E τ) := hreg.valid_erase A hv hEB
  have hvEσ : A.Valid (erase E τ ++ σ) := by
    refine A.valid_transport (τ := G) hvGσ' hvE ?_ ?_
    · intro e he
      rw [hσr e he, hGE, proj_erase_of_not_mem _ (fun h' => hr (Finset.sdiff_subset h'))]
    · intro e he v hv
      rw [hGE, A.memVal_erase (τ := erase E τ) (E := B \ E)]
      intro q hq hqBE
      exact (hacc e he v hv).2 q hqBE hq
  refine ⟨E, hEB, hEcard, σ, hσr, hvEσ, ?_, ?_, ?_, ?_⟩
  · rw [signals_append, hσsig]
    exact Nat.le_zero.1 ((signals_erase_le E τ).trans (by omega))
  · refine Regular.append_outsider A (hreg.erase A hEB) ?_ hacc
    intro e he h'; rw [hσr e he] at h'; exact hr (Finset.sdiff_subset h')
  · intro q hq hqBE
    by_cases hqr : q = r
    · subst hqr
      rw [hσ, ← List.append_assoc]
      refine A.idle_snoc_ret ?_
      rw [List.append_assoc]; exact hvEσ
    · rw [par_append, Finset.mem_union] at hq
      rcases hq with hq | hq
      · rw [par_erase, Finset.mem_sdiff] at hq
        have hqB : q ∉ B := fun h' => hqBE (Finset.mem_sdiff.2 ⟨h', hq.2⟩)
        refine A.idle_of_proj_eq (hset q hq.1 (by simp [hqr, hqB])) ?_
        rw [proj_append_of_forall _ _ _ (fun e he heq => hqr (heq.symm.trans (hσr e he))),
          proj_erase_of_not_mem _ hq.2]
      · obtain ⟨e, he, rfl⟩ := mem_par.1 hq; exact absurd (hσr e he) hqr
  · intro q hq
    rw [Finset.mem_sdiff, par_append, Finset.mem_union, par_erase] at hq
    rw [Finset.mem_union, Finset.mem_singleton]
    rcases hq.1 with h1 | h1
    · rw [Finset.mem_sdiff] at h1
      left; refine Finset.mem_sdiff.2 ⟨h1.1, fun hqB => hq.2 (Finset.mem_sdiff.2 ⟨hqB, h1.2⟩)⟩
    · obtain ⟨e, he, rfl⟩ := mem_par.1 h1; right; exact hσr e he

end Algorithm

end Podc.CCvsDSMSeparation
