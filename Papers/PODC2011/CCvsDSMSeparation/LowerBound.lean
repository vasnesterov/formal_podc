import Papers.PODC2011.CCvsDSMSeparation.Round

/-!
# The lower bound for the DSM model (Section 6: Lemmas 6.10–6.13, Theorem 6.2)

* `lemma_6_10`: under the supposition `AmortBound c K` (at most `c` RMRs per participant in every
  execution with at most `K` participants), for `i ≤ c` there is a regular history satisfying the
  invariant `S(i)` with at least `keep^[i](N)` active processes.
* `final_unstable` (Lemma 6.11): `S(c)` cannot have `5(c²+1)` unstable active processes.
* `final_stable` (Lemmas 6.12, 6.13): `S(c)` cannot have `c(c+1)+1` stable active processes if
  `N` is large: a process `s` that took no step and whose module was not written by them calls
  `Signal()`; it must access the module or a last write of each stable process.
* `theorem_6_2`.
-/

namespace Podc.CCvsDSMSeparation

open Cslib (exists_indep_of_outdeg)

variable {N : ℕ} {V Val S : Type*}

lemma signals_pos {τ : List (Ev N V Val)} {e : Ev N V Val} (he : e ∈ τ)
    (hs : e.op.isSigInv = true) : 0 < signals τ :=
  List.countP_pos_iff.2 ⟨e, he, hs⟩

namespace Algorithm

variable (A : Algorithm N V Val S)

lemma inv_zero : A.Inv 0 [] Finset.univ := by
  refine ⟨A.valid_nil, rfl, ⟨steps_nil, by simp [NoTouch], fun v => ?_⟩, by simp [Settled],
    by simp, fun _ _ => Or.inr (Nat.zero_le _)⟩
  exact SoleW.of_writer_not_mem (by simp [writer])

/-- **Lemma 6.10**: the statements `S(i)` for `i ≤ c`. -/
lemma lemma_6_10 {c K : ℕ} (hT : A.SoloTerminating) (hb : A.AmortBound c K) (hcK : c ≤ K) :
    ∀ i ≤ c, ∃ τ B, A.Inv i τ B ∧ (keep c)^[i] N ≤ B.card
  | 0, _ => ⟨[], Finset.univ, A.inv_zero, by simp⟩
  | i + 1, hi => by
    obtain ⟨τ, B, hI, hB⟩ := lemma_6_10 hT hb hcK i (by omega)
    obtain ⟨τ', B', hI', hB'⟩ := A.round hT hb hcK (by omega) hI
    exact ⟨τ', B', hI', by
      rw [Function.iterate_succ_apply']; exact (keep_mono c hB).trans hB'⟩

/-- Keeping only `T ⊆ B`: basic facts. -/
lemma erase_keep {i : ℕ} {τ : List (Ev N V Val)} {B T : Finset (Fin N)} (hI : A.Inv i τ B)
    (hTB : T ⊆ B) :
    A.Valid (erase (B \ T) τ) ∧ A.Regular T (erase (B \ T) τ) ∧
      A.Settled T (erase (B \ T) τ) ∧ par (erase (B \ T) τ) \ T ⊆ par τ \ B ∧
      signals (erase (B \ T) τ) = 0 ∧
      (∀ q ∈ T, proj (erase (B \ T) τ) q = proj τ q) ∧
      (∀ q ∈ T, ∀ v, A.home v = q → A.memVal (erase (B \ T) τ) v = A.memVal τ v) := by
  have hBT : B \ (B \ T) = T := Finset.sdiff_sdiff_eq_self hTB
  have hsub : B \ T ⊆ B := Finset.sdiff_subset
  have hnotin : ∀ q ∈ T, q ∉ B \ T := fun q hq h' => (Finset.mem_sdiff.1 h').2 hq
  refine ⟨hI.reg.valid_erase A hI.valid hsub, by have := hI.reg.erase A hsub; rwa [hBT] at this,
    by have := Settled.erase A hI.settled (E := B \ T); rwa [hBT] at this, ?_, ?_,
    fun q hq => proj_erase_of_not_mem τ (hnotin q hq), ?_⟩
  · intro q hq
    rw [Finset.mem_sdiff, par_erase, Finset.mem_sdiff] at hq
    exact Finset.mem_sdiff.2 ⟨hq.1.1, fun hqB => hq.1.2 (Finset.mem_sdiff.2 ⟨hqB, hq.2⟩)⟩
  · exact Nat.le_zero.1 ((signals_erase_le _ τ).trans (by rw [hI.nosig]))
  · intro q hq v hv
    refine A.memVal_erase fun w hw hwBT => ?_
    have := A.okW_writer_of_home hI.reg.noTouch (hTB hq) hv w hw (hsub hwBT)
    subst this; exact hnotin w hq hwBT

open Classical in
/-- **Lemma 6.11**: at the end of the construction there are few unstable processes. -/
lemma final_unstable {c : ℕ} (hb : A.AmortBound c (c * c + c + 1)) {τ : List (Ev N V Val)}
    {B : Finset (Fin N)} (hI : A.Inv c τ B)
    (hU : 5 * (c * c + 1) ≤ (B.filter fun p => ¬ A.Stable τ p).card) : False := by
  classical
  set U := B.filter fun p => ¬ A.Stable τ p with hUdef
  have hUB : U ⊆ B := Finset.filter_subset _ _
  obtain ⟨p0, hp0⟩ : U.Nonempty := Finset.card_pos.1 (by omega)
  have : Nonempty (Ev N V Val) := ⟨⟨p0, .inv .poll⟩⟩
  have hex : ∀ p ∈ U, ∃ (α : List (Ev N V Val)) (e : Ev N V Val), SoloPoll p (α ++ [e]) ∧
      A.Valid (τ ++ α ++ [e]) ∧ A.rmr α = 0 ∧ e.remote A.home = true :=
    fun p hp => A.exists_next_rmr (Finset.mem_filter.1 hp).2
  choose! α e hαe using hex
  have hd : A.NextData τ U α e := ⟨fun p hp => (hαe p hp).1, fun p hp => (hαe p hp).2.1,
    fun p hp => (hαe p hp).2.2.1, fun p hp => (hαe p hp).2.2.2⟩
  obtain ⟨T, hTU, hcard, hindep⟩ := exists_indep_of_outdeg (A.conflicts τ e) 2 U
    (fun x _ => A.card_conflicts_le τ e x)
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq (s := T) (n := c * c + 1)
    (by omega)
  have hT'U := hT'T.trans hTU
  have hd' := NextData.mono A hd hT'U
  have hind : ∀ p ∈ T', ∀ v, (e p).op.var = some v → A.home v ∉ T' := by
    intro p hp v hv hvT
    obtain ⟨u, hu, hne⟩ := hd.var_e (hT'U hp)
    rw [hv] at hu; cases hu
    exact hne (hindep p (hT'T hp) _ (hT'T hvT) (by simp [conflicts, hv]))
  obtain ⟨k1, -, -, k4, k5, k6, k7⟩ := A.erase_keep hI (hT'U.trans hUB)
  obtain ⟨s1, ⟨σ, hσ, hshape⟩, s3⟩ := A.advance_spec hd' hind T'.toList _
    (Finset.nodup_toList _) (fun p hp => Finset.mem_toList.1 hp) k1
    (fun q hq => k6 q (Finset.mem_toList.1 hq)) (fun q hq => k7 q (Finset.mem_toList.1 hq))
  set ρ := A.advance α e (erase (B \ T') τ) T'.toList
  have hpar : par ρ ⊆ (par τ \ B) ∪ T' := by
    intro q hq
    rw [hσ, par_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · by_cases hqT : q ∈ T'
      · exact Finset.mem_union_right _ hqT
      · exact Finset.mem_union_left _ (k4 (Finset.mem_sdiff.2 ⟨hq, hqT⟩))
    · obtain ⟨e', he', rfl⟩ := mem_par.1 hq
      exact Finset.mem_union_right _ (Finset.mem_toList.1 (hshape e' he').1)
  have hparc : (par ρ).card ≤ c + (c * c + 1) :=
    (Finset.card_le_card hpar).trans ((Finset.card_union_le _ _).trans (by
      rw [hT'card]; exact Nat.add_le_add_right hI.fin _))
  have hsig : signals ρ = 0 := by
    rw [hσ, signals_append, k5, signals_eq_zero (fun e' he' => (hshape e' he').2.1)]
  have hrmr : (c * c + 1) * (c + 1) ≤ A.rmr ρ := by
    calc (c * c + 1) * (c + 1) = ∑ p ∈ T', (c + 1) := by simp [hT'card]
      _ ≤ ∑ p ∈ T', A.rmrOf ρ p := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [s3 p (Finset.mem_toList.2 hp), A.rmrOf_eq_of_proj (k6 p hp)]
          have := (hI.prog p (hUB (hT'U hp))).resolve_left (Finset.mem_filter.1 (hT'U hp)).2
          omega
      _ ≤ A.rmr ρ := A.sum_rmrOf_le ρ T'
  have := hb ρ s1 (by omega) (by nlinarith)
  have : A.rmr ρ ≤ c * (c + (c * c + 1)) := this.trans (Nat.mul_le_mul_left _ hparc)
  nlinarith

open Classical in
/-- **Lemmas 6.12 and 6.13**: at the end of the construction there are few stable processes,
provided `N` is large. -/
lemma final_stable {c : ℕ} (hT : A.SoloTerminating) (hS : A.Solves)
    (hb : A.AmortBound c (c * c + c + 1)) {τ : List (Ev N V Val)}
    {B : Finset (Fin N)} (hI : A.Inv c τ B)
    (hSb : c * (c + 1) + 1 ≤ (B.filter fun p => A.Stable τ p).card)
    (hN : c + 2 * (c * (c + 1) + 1) + (c * (c + 1) + 1) * (c * (c + 1)) < N) : False := by
  classical
  set M := c * (c + 1) + 1 with hM
  obtain ⟨S₀, hS₀, hS₀card⟩ := Finset.exists_subset_card_eq (s := B.filter fun p => A.Stable τ p)
    (n := M) hSb
  have hS₀B : S₀ ⊆ B := hS₀.trans (Finset.filter_subset _ _)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := A.erase_keep hI hS₀B
  set τ₁ := erase (B \ S₀) τ with hτ₁
  have hstab : ∀ p ∈ S₀, A.Stable τ₁ p := fun p hp =>
    A.stable_congr hI.valid (k6 p hp) (k7 p hp) (Finset.mem_filter.1 (hS₀ hp)).2
  -- every stable process makes at most `c(c+1)` RMRs
  have hrmrS : ∀ p ∈ S₀, A.rmrOf τ₁ p ≤ c * (c + 1) := by
    intro p hp
    have hsub : S₀.erase p ⊆ S₀ := Finset.erase_subset _ _
    have hv := k2.valid_erase A k1 hsub
    have hpar : par (erase (S₀.erase p) τ₁) ⊆ (par τ \ B) ∪ {p} := by
      intro q hq
      rw [par_erase, Finset.mem_sdiff] at hq
      by_cases hqp : q = p
      · simp [hqp]
      · have hqS : q ∉ S₀ := fun h' => hq.2 (Finset.mem_erase.2 ⟨hqp, h'⟩)
        exact Finset.mem_union_left _ (k4 (Finset.mem_sdiff.2 ⟨hq.1, hqS⟩))
    have hparc : (par (erase (S₀.erase p) τ₁)).card ≤ c + 1 :=
      (Finset.card_le_card hpar).trans ((Finset.card_union_le _ _).trans (by
        simp only [Finset.card_singleton]; exact Nat.add_le_add_right hI.fin 1))
    have h1 := hb _ hv (by rw [Nat.le_zero.1 ((signals_erase_le _ _).trans k5.le)]; omega)
      (by nlinarith)
    have h2 : A.rmrOf (erase (S₀.erase p) τ₁) p ≤ A.rmr (erase (S₀.erase p) τ₁) := by
      have := A.sum_rmrOf_le (erase (S₀.erase p) τ₁) {p}; simpa using this
    rw [A.rmrOf_eq_of_proj (proj_erase_of_not_mem τ₁ (by simp))] at h2
    exact h2.trans (h1.trans (Nat.mul_le_mul_left _ hparc))
  -- the modules written remotely by the stable processes
  set O : Finset (Fin N) := ((τ₁.filter fun e => decide (e.p ∈ S₀) && e.remote A.home).filterMap
    fun e => e.op.var.map A.home).toFinset with hO
  have hOcard : O.card ≤ M * (c * (c + 1)) := by
    refine (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans ?_)
    rw [← List.countP_eq_length_filter, A.countP_mem_remote_eq_sum]
    calc ∑ p ∈ S₀, A.rmrOf τ₁ p ≤ ∑ p ∈ S₀, c * (c + 1) := Finset.sum_le_sum hrmrS
      _ = M * (c * (c + 1)) := by simp [hS₀card]
  have hpar₁ : par τ₁ ⊆ (par τ \ B) ∪ S₀ := by
    intro q hq
    by_cases hqS : q ∈ S₀
    · exact Finset.mem_union_right _ hqS
    · exact Finset.mem_union_left _ (k4 (Finset.mem_sdiff.2 ⟨hq, hqS⟩))
  -- the signaler
  obtain ⟨s, hs⟩ : ∃ s, s ∉ par τ₁ ∪ S₀ ∪ O := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin N)) ⊆ par τ₁ ∪ S₀ ∪ O := fun q _ => h q
    have := Finset.card_le_card this
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have h1 := Finset.card_le_card hpar₁
    have h2 := (Finset.card_union_le (par τ \ B) S₀)
    have h3 := Finset.card_union_le (par τ₁ ∪ S₀) O
    have h4 := Finset.card_union_le (par τ₁) S₀
    have := hI.fin
    omega
  simp only [Finset.mem_union, not_or] at hs
  obtain ⟨⟨hsτ₁, hsS⟩, hsO⟩ := hs
  set τ₀ := erase S₀ τ₁ with hτ₀
  have hv₀ : A.Valid τ₀ := k2.valid_erase A k1 subset_rfl
  have hsig₀ : signals τ₀ = 0 := Nat.le_zero.1 ((signals_erase_le _ _).trans k5.le)
  have hset' : A.Settled (insert s S₀) τ₁ := fun q hq hqS =>
    k3 q hq (fun h' => hqS (Finset.mem_insert_of_mem h'))
  have hidle₀ : ∀ q, q ≠ s → A.Idle τ₀ q := A.idle_erase_of_settled hset'
  have hsτ₀ : s ∉ par τ₀ := fun h' => hsτ₁ (by rw [hτ₀, par_erase] at h'; exact (Finset.mem_sdiff.1 h').1)
  set X₀ := τ₀ ++ [⟨s, .inv .signal⟩] with hX₀
  have hvX₀ : A.Valid X₀ :=
    (A.valid_snoc _ _).2 ⟨hv₀, A.stepOK_inv (A.idle_of_not_par hsτ₀) _⟩
  have hsigX₀ : signals X₀ = 1 := by
    rw [hX₀, signals_append, hsig₀]; rfl
  obtain ⟨σ₀, bs, hσ₀, hvs⟩ := hT X₀ s .signal hvX₀ (by omega)
    (fun q hq => A.idle_of_proj_eq (hidle₀ q hq) (proj_snoc_ne _ _ (Ne.symm hq)))
    (A.busy_snoc_inv hvX₀)
  set ρs : List (Ev N V Val) := [⟨s, .inv .signal⟩] ++ σ₀ ++ [⟨s, .ret bs⟩] with hρs
  have hρs_s : ∀ e ∈ ρs, e.p = s := by
    intro e he; simp only [hρs, List.mem_append, List.mem_singleton] at he
    rcases he with (rfl | he) | rfl
    · rfl
    · exact (hσ₀ e he).1
    · rfl
  have hvρs : A.Valid (τ₀ ++ ρs) := by
    rw [hρs, ← List.append_assoc, ← List.append_assoc]; exact hvs
  have hsigρs : signals ρs = 1 := by
    simp only [hρs, signals_append]
    rw [signals_eq_zero (σ := σ₀) (fun e he => Op.isSigInv_eq_false_of_isAccess (hσ₀ e he).2)]
    rfl
  -- the signaler accesses the module or a last write of every stable process
  have hclaim : ∀ p ∈ S₀, ∃ e ∈ ρs, ∃ v, e.op.var = some v ∧
      (A.home v = p ∨ writer v τ₁ = some p) := by
    intro p hp
    by_contra hno
    push Not at hno
    set τp := erase (S₀.erase p) τ₁ with hτp
    have hsubp : S₀.erase p ⊆ S₀ := Finset.erase_subset _ _
    have hvp : A.Valid τp := k2.valid_erase A k1 hsubp
    have hτ0p : τ₀ = erase {p} τp := by
      rw [hτp, erase_erase, hτ₀]; congr 1; ext q; by_cases hq : q = p <;> simp [hq, hp]
    have hsp : s ≠ p := fun h' => hsS (h' ▸ hp)
    -- replay the signaler after `τp`
    have hX : A.Valid (τp ++ ρs) := by
      refine A.valid_transport (τ := τ₀) hvρs hvp ?_ ?_
      · intro e he
        rw [hρs_s e he, hτ0p, proj_erase_of_not_mem τp (E := {p}) (by simpa using hsp)]
      · intro e he v hv
        rw [hτ0p, A.memVal_erase (τ := τp) (E := {p})]
        intro q hq hqp
        rw [Finset.mem_singleton] at hqp; subst hqp
        have := ((k2.sole v).okW_erase hsubp q hq).2 hp
        exact (hno e he v hv).2 this
    set X := τp ++ ρs with hXdef
    have hsigX : signals X = 1 := by
      rw [hXdef, signals_append, hsigρs, hτp,
        Nat.le_zero.1 ((signals_erase_le _ _).trans k5.le)]
    have hpjX : proj X p = proj τp p := proj_append_of_forall _ _ _ (fun e he heq =>
      hsp ((hρs_s e he).symm.trans heq))
    have hstab_p : A.Stable τp p :=
      A.stable_congr k1 (proj_erase_of_not_mem τ₁ (by simp)) (fun v hv => by
        refine A.memVal_erase fun w hw hwS => ?_
        have := A.okW_writer_of_home k2.noTouch hp hv w hw (hsubp hwS)
        subst this; simp at hwS) (hstab p hp)
    have hmemX : ∀ v, A.home v = p → A.memVal X v = A.memVal τp v := by
      intro v hv
      refine A.memVal_append_of_not_writes _ _ v fun e he hw => ?_
      exact (hno e he v hw.var).1 hv
    have hstabX : A.Stable X p := A.stable_congr hvp hpjX hmemX hstab_p
    -- every process other than `p` is idle
    have hothers : ∀ Y : List (Ev N V Val), (∀ e ∈ Y, e.p = p) → ∀ q, q ≠ p →
        A.Idle (X ++ Y) q := by
      intro Y hY q hqp
      refine A.idle_of_proj_eq ?_ (proj_append_of_forall _ _ _ fun e he heq =>
        hqp (heq ▸ hY e he))
      by_cases hqs : q = s
      · rw [hqs]
        have hXeq : X = (τp ++ [⟨s, .inv .signal⟩] ++ σ₀) ++ [⟨s, .ret bs⟩] := by
          rw [hXdef, hρs]; simp
        rw [hXeq]; exact A.idle_snoc_ret (hXeq ▸ hX)
      · refine A.idle_of_proj_eq ?_ (proj_append_of_forall _ _ _ fun e he heq =>
          hqs ((heq.symm.trans (hρs_s e he))))
        by_cases hqS : q ∈ S₀
        · refine A.idle_of_not_par ?_
          rw [hτp, par_erase]; simp [hqS, hqp]
        · refine A.idle_of_proj_eq ?_ (proj_erase_of_not_mem τ₁ (by simp [hqS]))
          by_cases hq1 : q ∈ par τ₁
          · exact k3 q hq1 hqS
          · exact A.idle_of_not_par hq1
    -- `p` completes its pending call, if any
    obtain ⟨γ, hγp, hγsig, hvγ, hidleγ⟩ : ∃ γ : List (Ev N V Val), (∀ e ∈ γ, e.p = p) ∧
        (∀ e ∈ γ, e.op.isInv = false) ∧ A.Valid (X ++ γ) ∧ A.Idle (X ++ γ) p := by
      rcases A.idle_or_busy hX p with hid | ⟨o, hbu⟩
      · exact ⟨[], by simp, by simp, by simpa using hX, by simpa using hid⟩
      · obtain ⟨β₁, b₁, hβ₁, hvβ₁⟩ := hT X p o hX (by omega)
          (fun q hq => by simpa using hothers [] (by simp) q hq) hbu
        refine ⟨β₁ ++ [⟨p, .ret b₁⟩], ?_, ?_, by rw [← List.append_assoc]; exact hvβ₁,
          by rw [← List.append_assoc]; exact A.idle_snoc_ret hvβ₁⟩
        · intro e he; simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact (hβ₁ e he).1
          · rfl
        · intro e he; simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact Op.isInv_eq_false_of_isAccess (hβ₁ e he).2
          · rfl
    -- `p` calls `Poll()` once more
    set Y := X ++ γ ++ [⟨p, .inv .poll⟩] with hY
    have hvY : A.Valid Y := (A.valid_snoc _ _).2 ⟨hvγ, A.stepOK_inv hidleγ _⟩
    have hbusyY : A.Busy Y p .poll := A.busy_snoc_inv hvY
    have hsigγ : signals γ = 0 := signals_eq_zero fun e he => by
      exact Op.isSigInv_eq_false_of_isInv (hγsig e he)
    have hsigY : signals Y = 1 := by
      rw [hY, signals_append, signals_append, hsigX, hsigγ]; rfl
    obtain ⟨β₂, b, hβ₂, hvβ₂⟩ := hT Y p .poll hvY (by omega)
      (fun q hq => by
        have := hothers (γ ++ [⟨p, .inv .poll⟩]) (by
          intro e he; simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hγp e he
          · rfl) q hq
        simpa [hY, List.append_assoc] using this) hbusyY
    set γ' := γ ++ [⟨p, .inv .poll⟩] ++ β₂ with hγ'
    have hγ'p : ∀ e ∈ γ', e.p = p := by
      intro e he; simp only [hγ', List.mem_append, List.mem_singleton] at he
      rcases he with (he | rfl) | he
      · exact hγp e he
      · rfl
      · exact (hβ₂ e he).1
    have hvXγ' : A.Valid (X ++ γ' ++ [⟨p, .ret b⟩]) := by
      simpa [hγ', hY, List.append_assoc] using hvβ₂
    have hbusyXγ' : A.Busy (X ++ γ') p .poll := by
      have := A.busy_append_access hbusyY (σ := β₂) (Valid.of_append A hvβ₂) hβ₂
      simpa [hγ', hY, List.append_assoc] using this
    have hsigγ' : signals γ' = 0 := by
      simp only [hγ', signals_append, hsigγ]
      rw [signals_eq_zero (σ := β₂) (fun e he => Op.isSigInv_eq_false_of_isAccess (hβ₂ e he).2)]
      rfl
    -- by Specification 4.1, the poll returns `true` (the signal completed before it began)
    have hbt : b = true := by
      by_contra hbf
      have hbf : b = false := by simpa using hbf
      subst hbf
      refine (hS (X ++ γ') p false hvXγ' (by rw [signals_append, hsigX, hsigγ']) hbusyXγ').2 rfl
        ⟨τp ++ [⟨s, .inv .signal⟩] ++ σ₀, s, bs, γ, β₂, ?_, ?_, ?_⟩
      · rw [hXdef, hρs, hγ']; simp
      · have h1 : A.Valid (τp ++ [⟨s, .inv .signal⟩] ++ σ₀) :=
          Valid.of_prefix A hX ⟨[⟨s, .ret bs⟩], by rw [hXdef, hρs]; simp⟩
        exact A.busy_append_access (A.busy_snoc_inv (Valid.of_append A h1)) h1 hσ₀
      · intro e he _
        exact Op.isInv_eq_false_of_isAccess (hβ₂ e he).2
    subst hbt
    -- the same run of `p` without the signaler: the poll returns `true` without any signal
    have hrmr0 : A.rmr γ' = 0 := hstabX γ' (fun e he => ⟨hγ'p e he, by
      simp only [hγ', List.mem_append, List.mem_singleton] at he
      rcases he with (he | rfl) | he
      · exact Op.isSigInv_eq_false_of_isInv (hγsig e he)
      · rfl
      · exact Op.isSigInv_eq_false_of_isAccess (hβ₂ e he).2⟩)
      (Valid.of_append A hvXγ')
    have hvp' : A.Valid (τp ++ (γ' ++ [⟨p, .ret true⟩])) := by
      refine A.valid_transport (τ := X) (by simpa [List.append_assoc] using hvXγ') hvp ?_ ?_
      · intro e he
        have : e.p = p := by
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hγ'p e he
          · rfl
        rw [this, hpjX]
      · intro e he v hv
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · have hloc := A.home_eq_of_not_remote ((A.rmr_eq_zero_iff).1 hrmr0 e he) hv
          rw [hγ'p e he] at hloc
          exact (hmemX v hloc).symm
        · simp [Op.var] at hv
    have hbusyp : A.Busy (τp ++ γ') p .poll :=
      A.busy_of_proj_eq hbusyXγ' (by rw [proj_append τp γ', proj_append X γ', hpjX])
    have hsigp : signals (τp ++ γ') = 0 := by
      rw [signals_append, hsigγ', hτp, Nat.le_zero.1 ((signals_erase_le _ _).trans k5.le)]
    obtain ⟨e', he', hsig'⟩ := (hS (τp ++ γ') p true (by simpa using hvp') (by omega)
      hbusyp).1 rfl
    have := signals_pos he' hsig'
    omega
  -- count the RMRs of the signaler
  have hρsrmr : M ≤ A.rmr ρs := by
    have hch : ∀ p ∈ S₀, ∃ v, (∃ e ∈ ρs, e.op.var = some v) ∧
        (A.home v = p ∨ writer v τ₁ = some p) := by
      intro p hp
      obtain ⟨e, he, v, hv, hd⟩ := hclaim p hp
      exact ⟨v, ⟨e, he, hv⟩, hd⟩
    rcases S₀.eq_empty_or_nonempty with h0 | ⟨q0, hq0⟩
    · rw [h0] at hS₀card; simp at hS₀card
    have : Nonempty V := ⟨(hch q0 hq0).choose⟩
    choose! f hf using hch
    rw [← hS₀card]
    refine A.card_le_rmr_of_injOn f ?_ ?_
    · have key : ∀ q₁ ∈ S₀, ∀ q₂ v, A.home v = q₁ → writer v τ₁ = some q₂ → q₁ = q₂ := by
        intro q₁ hq₁ q₂ v hh hw
        obtain ⟨e, he, rfl, hwe⟩ := writer_mem hw
        exact k2.noTouch e he v hwe.var q₁ (by rw [hh]) hq₁
      intro q₁ hq₁ q₂ hq₂ heq
      have h1 := (hf q₁ hq₁).2; have h2 := (hf q₂ hq₂).2
      rw [heq] at h1
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact h1.symm.trans h2
      · exact key q₁ hq₁ q₂ _ h1 h2
      · exact (key q₂ hq₂ q₁ _ h2 h1).symm
      · rw [h1] at h2; cases h2; rfl
    · intro q hq
      obtain ⟨⟨e, he, hv⟩, hd⟩ := hf q hq
      refine ⟨e, he, hv, A.remote_of_var hv ?_⟩
      rw [hρs_s e he]
      rcases hd with hd | hd
      · rw [hd]; exact fun h' => hsS (h' ▸ hq)
      · intro hh
        obtain ⟨e', he', hq', hwe⟩ := writer_mem hd
        apply hsO
        rw [hO, List.mem_toFinset, List.mem_filterMap]
        refine ⟨e', List.mem_filter.2 ⟨he', ?_⟩, by simp [hwe.var, hh]⟩
        have : e'.remote A.home = true := A.remote_of_var hwe.var (by
          rw [hh, hq']; exact fun h' => hsS (h' ▸ hq))
        simp [hq', hq, this]
  -- the execution `τ₀ ++ ρs` has at most `c + 1` participants
  have hparW : par (τ₀ ++ ρs) ⊆ (par τ \ B) ∪ {s} := by
    intro q hq
    rw [par_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · rw [hτ₀, par_erase, Finset.mem_sdiff] at hq
      exact Finset.mem_union_left _ (k4 (Finset.mem_sdiff.2 hq))
    · obtain ⟨e, he, rfl⟩ := mem_par.1 hq; simp [hρs_s e he]
  have hparWc : (par (τ₀ ++ ρs)).card ≤ c + 1 :=
    (Finset.card_le_card hparW).trans ((Finset.card_union_le _ _).trans (by
      simp only [Finset.card_singleton]; exact Nat.add_le_add_right hI.fin 1))
  have h1 := hb _ hvρs (by rw [signals_append, hsig₀, hsigρs]) (by nlinarith)
  have h2 := A.rmr_le_rmr_append_left τ₀ ρs
  have h3 : c * (par (τ₀ ++ ρs)).card ≤ c * (c + 1) := Nat.mul_le_mul_left _ hparWc
  omega

end Algorithm

/-! ### Theorem 6.2 -/

lemma keep_unbounded (c T : ℕ) : ∃ n₀, ∀ n ≥ n₀, T ≤ Algorithm.keep c n := by
  refine ⟨3 * (5 * (T + c * c + 3)) ^ 2, fun n hn => ?_⟩
  unfold Algorithm.keep
  have h1 : (5 * (T + c * c + 3)) ^ 2 ≤ n / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; linarith
  have h2 : 5 * (T + c * c + 3) ≤ Nat.sqrt (n / 3) := by
    rw [Nat.le_sqrt']; exact h1
  have h3 : T + c * c + 3 ≤ Nat.sqrt (n / 3) / 5 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; linarith
  omega

lemma iterate_keep_unbounded (c : ℕ) : ∀ k T, ∃ n₀, ∀ n ≥ n₀, T ≤ (Algorithm.keep c)^[k] n
  | 0, T => ⟨T, fun n hn => by simpa using hn⟩
  | k + 1, T => by
    obtain ⟨m₀, hm₀⟩ := iterate_keep_unbounded c k T
    obtain ⟨n₀, hn₀⟩ := keep_unbounded c m₀
    exact ⟨n₀, fun n hn => by rw [Function.iterate_succ_apply]; exact hm₀ _ (hn₀ n hn)⟩

/-- **Theorem 6.2.** For every constant `c` there is `N₀` such that for every `N ≥ N₀`, every
deterministic terminating algorithm for `N` processes that solves the signaling problem (polling
semantics, one signaler, waiters not fixed in advance) using atomic reads and writes has an
execution (with at most one call to `Signal()`) in which `k ≤ c² + c + 1` processes participate
and incur more than `c·k` RMRs in total in the DSM model. In other words, the signaling problem
has no solution with `O(1)` amortized RMR complexity in the DSM model. -/
theorem theorem_6_2 (c : ℕ) : ∃ N₀, ∀ N ≥ N₀, ∀ {V Val S : Type*} (A : Algorithm N V Val S),
    A.SoloTerminating → A.Solves →
    ∃ τ : List (Ev N V Val), A.Valid τ ∧ signals τ ≤ 1 ∧ (par τ).card ≤ c * c + c + 1 ∧
      c * (par τ).card < A.rmr τ := by
  obtain ⟨n₀, hn₀⟩ := iterate_keep_unbounded c c (5 * (c * c + 1) + (c * (c + 1) + 1))
  refine ⟨max n₀ (c + 2 * (c * (c + 1) + 1) + (c * (c + 1) + 1) * (c * (c + 1)) + 1),
    fun N hN V Val S A hT hS => ?_⟩
  classical
  by_contra hcon
  have hb : A.AmortBound c (c * c + c + 1) := by
    intro τ hv hs hk
    by_contra h
    exact hcon ⟨τ, hv, hs, hk, by omega⟩
  obtain ⟨τ, B, hI, hB⟩ := A.lemma_6_10 hT hb (by nlinarith) c le_rfl
  have hB' := (hn₀ N (le_of_max_le_left hN)).trans hB
  have hsplit := Finset.card_filter_add_card_filter_not (s := B) (fun p => A.Stable τ p)
  by_cases hU : 5 * (c * c + 1) ≤ (B.filter fun p => ¬ A.Stable τ p).card
  · exact A.final_unstable hb hI hU
  · exact A.final_stable hT hS hb hI (by omega) (by have := le_of_max_le_right hN; omega)

end Podc.CCvsDSMSeparation
