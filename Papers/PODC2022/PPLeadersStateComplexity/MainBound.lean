import Papers.PODC2022.PPLeadersStateComplexity.Section8

/-!
# Proof of Theorem 4.3 (Section 8 of Leroux), main case `|P| ≥ 2`

Notation follows the paper: `d = |P|`, `‖T‖∞ = M`, `B` is (an upper bound of) the constant `b`
of Theorem 6.1 for the `d − 1` places `P' = P \ {i}`, `h = d (1 + M) B`; we use
`a = h^(2d+3)`, `ℓ = h^(2^d+2d+4)`, `k = d h^(2^d+1)` (the exponents of `ℓ` and `k` differ from
the paper because Lemma 7.3 is used with the weak Pottier bound), and prove
`n ≤ h^(2d+5) ℓ`.
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

namespace Sec8

variable {P : Type*} [Fintype P] [DecidableEq P]

open Arith

set_option maxHeartbeats 1000000 in
/-- The bound of Section 8 for a protocol given by a Petri net `T`, with `|P| ≥ 2`. -/
theorem main_bound (Pr : Protocol P) (T : Finset (Trans P))
    (hR : ∀ α β, Pr.R α β ↔ Reach T α β) {i : P} {n : ℕ} (hc : Pr.StablyComputesGe i n)
    (hd : 2 ≤ Fintype.card P) :
    n ≤ (Fintype.card P * (1 + netNorm T) *
        (4 + 4 * netNorm T + 2 * supNorm Pr.leaders) ^ E1 (Fintype.card P)) ^ (2 * Fintype.card P + 5) *
      (Fintype.card P * (1 + netNorm T) *
        (4 + 4 * netNorm T + 2 * supNorm Pr.leaders) ^ E1 (Fintype.card P)) ^
          (2 ^ Fintype.card P + 2 * Fintype.card P + 4) := by
  classical
  set d := Fintype.card P with hddef
  set M := netNorm T with hMdef
  set L := supNorm Pr.leaders with hLdef
  set B := (4 + 4 * M + 2 * L) ^ E1 d with hBdef
  set h := d * (1 + M) * B with hhdef
  set a := h ^ (2 * d + 3) with hadef
  set ℓ := h ^ (2 ^ d + 2 * d + 4) with hℓdef
  set k := d * h ^ (2 ^ d + 1) with hkdef
  set F := Finset.univ.filter fun p => Pr.γ p = Out.zero with hFdef
  -- basic arithmetic facts
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hBh : 2 * B * (1 + M) ≤ h := by
    rw [hhdef]; nlinarith [Nat.mul_le_mul_right (B * (1 + M)) hd]
  have hdh : d ≤ h := by
    rw [hhdef]
    have : 1 ≤ (1 + M) * B := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have h2 : 2 ≤ h := hd.trans hdh
  have hBleh := B_le hd hB1 hBh hdh h2
  have hMleh := M_le hd hB1 hBh hdh h2
  have ha1 : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_pow _ _ (by omega)
  have hBM : B * M ≤ h := by nlinarith
  have hh : M * (1 + M) ^ (d ^ d) ≤ h := lemma_5_4_hyp d M L hd
  have hBMh : B + B * M ≤ h := by nlinarith
  clear_value k ℓ a h B
  by_contra hlt
  push_neg at hlt
  have hI := hc.1
  -- the places `P' = P \ {i}`
  set P' := Finset.univ.erase i with hP'def
  have hiP' : i ∉ P' := by simp [hP'def]
  have hcardP' : P'.card = d - 1 := by rw [hP'def, Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl
  have hmemP' : ∀ p, p ≠ i → p ∈ P' := fun p hp => by simp [hP'def, hp]
  -- Theorem 6.1 on `T|_P'` and `ρ_L|_P'`
  obtain ⟨σ₀, w₀, Q, α, β, hQP', hσ₀, hw₀, hrσ₀, hrw₀, hαβQ, hαβ, hbot, hcardS, hσ₀len, hw₀len,
    hdα, hdβ⟩ := theorem_6_1_rel (netOn_resNet P' T) (ρ := res P' Pr.leaders)
      (fun p hp => res_apply_of_not_mem hp _)
  set b₀ := (4 + 4 * netNorm (resNet P' T) + 2 * supNorm (res P' Pr.leaders)) ^
    (P'.card ^ P'.card * (1 + (2 + P'.card ^ P'.card) ^ (P'.card + 1))) with hb₀
  have hb₀B : b₀ ≤ B := by
    rw [hb₀, hBdef, hcardP', show d - 1 + 1 = d by omega]
    apply Nat.pow_le_pow_left
    have := netNorm_resNet_le P' T
    have := supNorm_res_le P' Pr.leaders
    omega
  have hiQ : i ∉ Q := fun h => hiP' (hQP' h)
  rw [resNet_resNet_of_subset hQP'] at hbot hcardS
  -- lift the words to `T`
  obtain ⟨σ, hσ, rfl⟩ := hσ₀.exists_of_resNet
  obtain ⟨w, hw, rfl⟩ := hw₀.exists_of_resNet
  rw [List.length_map] at hσ₀len hw₀len
  have hσlen : σ.length ≤ B := hσ₀len.trans hb₀B
  have hwlen : w.length ≤ B := hw₀len.trans hb₀B
  have hdαB : (d - 1) * supNorm α ≤ B := hcardP' ▸ hdα.trans hb₀B
  have hαnorm : supNorm α ≤ B := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hdαB
  have hαvan : ∀ p ∉ P', α p = 0 := Run.vanish (netOn_resNet P' T) (hσ.res P') hrσ₀
    (fun p hp => res_apply_of_not_mem hp _)
  have hβvan : ∀ p ∉ P', β p = 0 := Run.vanish (netOn_resNet P' T) (hw.res P') hrw₀ hαvan
  have hαleβ : ∀ p, α p ≤ β p := by
    intro p
    by_cases hpQ : p ∈ Q
    · have := congrFun hαβQ p; simp only [res_apply_of_mem hpQ] at this; omega
    by_cases hpP' : p ∈ P'
    · exact (hαβ p (Finset.mem_sdiff.2 ⟨hpP', hpQ⟩)).le
    · rw [hαvan p hpP', hβvan p hpP']
  -- the Petri net with control-states
  set S := hbot.1.toFinset with hSdef
  set E := edges T Q S with hEdef
  have hS := closed_component hbot
  have hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S := edges_sub hS
  have hSC : StronglyConnected E S := stronglyConnected_component hbot
  set x₀ := res Q α with hx₀def
  have hx₀ : x₀ ∈ S := mem_component_self hbot
  have hScard : S.card ≤ B := by
    rw [hSdef, ← Set.ncard_eq_toFinset_card _ hbot.1]; exact hcardS.trans hb₀B
  have hEcard : E.card ≤ B * (M + 1) ^ (2 * d) :=
    card_edges_le.trans (Nat.mul_le_mul hScard card_le_box)
  have hδE : ∀ e ∈ E, ∀ p, |Trans.delta e.2.1 p| ≤ ((1 + M : ℕ) : ℤ) := by
    intro e he p
    have := (mem_edges.1 he).2.1
    calc |Trans.delta e.2.1 p| ≤ e.2.1.supNorm := Trans.abs_delta_le _ _
      _ ≤ ((1 + M : ℕ) : ℤ) := by have := le_netNorm this; push_cast; omega
  -- Lemma 7.2: a total cycle on `α|_Q`
  obtain ⟨θE, hθE, hθEtot, hθElen⟩ := lemma_7_2 hE hSC hx₀
  set σE := θE.map fun e => e.2.1 with hσEdef
  obtain ⟨hσE, hrσE⟩ := run_of_path hθE
  have hσElen : σE.length ≤ B * B * (M + 1) ^ (2 * d) := by
    rw [hσEdef, List.length_map]
    calc θE.length ≤ E.card * S.card := hθElen
      _ ≤ B * (M + 1) ^ (2 * d) * B := Nat.mul_le_mul hEcard hScard
      _ = B * B * (M + 1) ^ (2 * d) := by ring
  have hMσE : M * σE.length ≤ a :=
    (Nat.mul_le_mul_left _ hσElen).trans ((f3 hd hB1 hBh hdh h2).trans_eq hadef.symm)
  -- the runs in `P'`
  set wpow := List.flatten (List.replicate (a * ℓ) w) with hwpow
  set σEpow := List.flatten (List.replicate ℓ σE) with hσEpow
  set η := α + (a * ℓ) • (β - α) with hηdef
  have hβeq : β = α + (β - α) := by
    funext p; have := hαleβ p; simp only [Pi.add_apply, Pi.sub_apply]; omega
  have hrwpow : Run (wpow.map (Trans.res P')) α η := by
    rw [hwpow, map_flatten_replicate]; exact (hβeq ▸ hrw₀).pow _
  have hηQ : res Q η = x₀ := by
    funext p
    by_cases hpQ : p ∈ Q
    · have h1 : α p = β p := by
        have := congrFun hαβQ p; rw [hx₀def] at this; simpa [res_apply_of_mem hpQ] using this
      simp only [hηdef, hx₀def, res_apply_of_mem hpQ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, h1, Nat.sub_self, mul_zero, add_zero]
    · simp [hx₀def, res_apply_of_not_mem hpQ]
  have hηbig : ∀ p ∈ P' \ Q, a * ℓ ≤ η p := by
    intro p hp
    have := hαβ p hp
    simp only [hηdef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have h1 : 1 ≤ β p - α p := by omega
    have h3 : a * ℓ * 1 ≤ a * ℓ * (β p - α p) := Nat.mul_le_mul_left _ h1
    omega
  have hσEpowlen : σEpow.length = ℓ * σE.length := length_flatten_replicate _ _
  obtain ⟨δ, hrδ, hδQ, -⟩ := run_lift (σ := σEpow.map (Trans.res P')) (Q := Q) (α := η)
    (M := fun p => if p ∈ P' then M else 0)
    (fun t ht p _ => by
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
      by_cases hp : p ∈ P'
      · simp only [hp, if_true, Trans.res, res_apply_of_mem hp]
        exact (t'.fst_le_supNorm p).trans (le_netNorm (IsWord.flatten_replicate hσE ℓ t' ht'))
      · simp [hp, Trans.res])
    (by
      rw [List.map_map, show Trans.res Q ∘ Trans.res P' = Trans.res Q from
        funext (trans_res_res hQP'), hηQ, hσEpow, map_flatten_replicate]
      have h0 : Run (σE.map (Trans.res Q)) x₀ (x₀ + 0) := by rw [add_zero]; exact hrσE
      have := h0.pow ℓ
      simpa using this)
    (fun p hpQ => by
      by_cases hp : p ∈ P'
      · simp only [hp, if_true, List.length_map, hσEpowlen]
        calc ℓ * σE.length * M = ℓ * (M * σE.length) := by ring
          _ ≤ ℓ * a := Nat.mul_le_mul_left _ hMσE
          _ = a * ℓ := by ring
          _ ≤ η p := hηbig p (Finset.mem_sdiff.2 ⟨hp, hpQ⟩)
      · simp [hp])
  -- lift to `P` (Lemma 5.2 with the place `i`)
  set ρ' := Pr.leaders + Pi.single i (n - 1) with hρ'def
  have hρ'P' : res P' ρ' = res P' Pr.leaders := by
    rw [hρ'def, res_add, res_single_of_not_mem hiP', add_zero]
  set W1 := σ ++ (wpow ++ σEpow) with hW1
  have hW1len : W1.length * M + ℓ ≤ h ^ (2 * d + 5) * ℓ := by
    have e1 : W1.length = σ.length + a * ℓ * w.length + ℓ * σE.length := by
      rw [hW1, List.length_append, List.length_append, hσEpowlen, hwpow,
        length_flatten_replicate]; ring
    have e2 := f4 hd hB1 hBh hdh h2 ha1 hℓ1
    have e3 : h ^ (2 * d + 5) * ℓ = h ^ 2 * a * ℓ := by rw [hadef]; ring
    rw [e1, e3]
    calc (σ.length + a * ℓ * w.length + ℓ * σE.length) * M + ℓ
        = σ.length * M + a * ℓ * (w.length * M) + ℓ * (M * σE.length) + ℓ := by ring
      _ ≤ B * M + a * ℓ * (B * M) + ℓ * a + ℓ := by gcongr
      _ = (B + a * ℓ * B) * M + ℓ * a + ℓ := by ring
      _ ≤ h ^ 2 * a * ℓ := e2
  have hW1P' : Run (W1.map (Trans.res P')) (res P' ρ') δ := by
    rw [hρ'P', hW1, List.map_append, List.map_append]
    exact hrσ₀.append (hrwpow.append hrδ)
  have hW1word : IsWord T W1 := hσ.append ((IsWord.flatten_replicate hw _).append
    (IsWord.flatten_replicate hσE _))
  obtain ⟨δ', hrδ', hδ'P', -⟩ := lemma_5_2 hW1word hW1P' (fun p hp => by
    have hpi : p = i := by by_contra hne; exact hp (hmemP' p hne)
    subst hpi
    simp only [hρ'def, Pi.add_apply, Pi.single_eq_same, ← hMdef]
    omega)
  obtain ⟨α', hrα', hr2⟩ := run_append.1 (hW1 ▸ hrδ')
  obtain ⟨η', hrη', hrδ''⟩ := run_append.1 hr2
  have hα'P' : res P' α' = α := by
    have := hrα'.res P'; rw [hρ'P'] at this; exact this.det hrσ₀
  have hη'P' : res P' η' = η := by
    have := hrη'.res P'; rw [hα'P'] at this; exact this.det hrwpow
  have hα'eq : ∀ p, p ≠ i → α' p = α p := fun p hp => by
    rw [← hα'P', res_apply_of_mem (hmemP' p hp)]
  have hη'eq : ∀ p, p ≠ i → η' p = η p := fun p hp => by
    rw [← hη'P', res_apply_of_mem (hmemP' p hp)]
  have hresQ : ∀ x : Config P, res Q (res P' x) = res Q x := fun x => by
    rw [res_res, Finset.inter_eq_left.2 hQP']
  have hn1 : 1 ≤ n := by omega
  -- stable computation for the input `n - 1`
  have hreachδ' : Reach T ρ' δ' := ⟨W1, hW1word, hrδ'⟩
  obtain ⟨μ, hδμ, hμS0⟩ := hc.2 _ (isInput_single Pr hI (n - 1)) δ' ((hR _ _).2 hreachδ')
  have hcp : countingPred i n (Pi.single i (n - 1)) = false := by
    simp only [countingPred, Pi.single_eq_same, decide_eq_false_iff_not]; omega
  rw [hcp] at hμS0
  have hμstab : Stabilized T F μ := (lemma_5_1 Pr T hR μ).2 (by simpa [Protocol.stable] using hμS0)
  obtain ⟨σ', hσ', hrσ'⟩ := (hR _ _).1 hδμ
  -- the path of `(S, T, E)` labelled by `w^(aℓ) σ_E^ℓ σ'`
  have hα'Q : res Q α' = x₀ := by rw [← hresQ α', hα'P']
  have hη'Q : res Q η' = x₀ := by rw [← hresQ η', hη'P', hηQ]
  have hδ'Q : res Q δ' = x₀ := by rw [← hresQ δ', hδ'P', hδQ]
  obtain ⟨π1, hπ1, hπ1l⟩ := path_of_run hS (IsWord.flatten_replicate hw _) hx₀
    (by have := hrη'.res Q; rwa [hα'Q, hη'Q] at this)
  obtain ⟨π3, hπ3, hπ3l⟩ := path_of_run hS hσ' hx₀
    (by have := hrσ'.res Q; rwa [hδ'Q] at this)
  set θEpow := List.flatten (List.replicate ℓ θE) with hθEpow
  set π := π1 ++ (θEpow ++ π3) with hπdef
  have hπ : IsPath E x₀ π (res Q μ) :=
    isPath_append.2 ⟨x₀, hπ1, isPath_append.2 ⟨x₀, isPath_flatten_replicate hθE ℓ, hπ3⟩⟩
  have hπl : π.map (fun e => e.2.1) = wpow ++ (σEpow ++ σ') := by
    simp only [hπdef, List.map_append, hπ1l, hπ3l, hθEpow, map_flatten_replicate, hσEpow, hσEdef,
      hwpow]
  have hdispπ : ∀ p, disp Trans.delta π p = (μ p : ℤ) - α' p := by
    intro p
    rw [disp_eq_wordDelta, hπl, (hrη'.append (hrδ''.append hrσ')).apply_eq p]; ring
  obtain ⟨π₀, Θ, hπ₀, hπ₀len, hΘ, hπeq⟩ := exists_decomp hE hx₀ hπ
  have hδE' : ∀ e ∈ E, ∀ p, |Trans.delta e.2.1 p| ≤ (M : ℤ) := by
    intro e he p
    have := le_netNorm (mem_edges.1 he).2.1
    calc |Trans.delta e.2.1 p| ≤ e.2.1.supNorm := Trans.abs_delta_le _ _
      _ ≤ (M : ℤ) := by exact_mod_cast this
  have hdispπ₀ : ∀ p, |disp Trans.delta π₀ p| ≤ ((B * M : ℕ) : ℤ) := by
    intro p
    calc |disp Trans.delta π₀ p| ≤ π₀.length * M := abs_disp_le _ hδE' hπ₀.mem_E p
      _ ≤ ((B * M : ℕ) : ℤ) := by
        have : π₀.length * M ≤ B * M := Nat.mul_le_mul_right _ (by omega)
        exact_mod_cast this
  have hΘval : ∀ p, mdisp Trans.delta Θ p = (μ p : ℤ) - α' p - disp Trans.delta π₀ p := by
    intro p
    have := hdispπ p
    rw [disp_eq_coe, hπeq, Multiset.map_add, Multiset.sum_add, ← disp_eq_coe,
      ← mdisp_eq_parikh] at this
    linarith
  have hcount : ∀ e ∈ E, k ≤ (parikh Θ).count e := by
    intro e he
    have h1 : ℓ ≤ π.count e := by
      simp only [hπdef, List.count_append, hθEpow, count_flatten_replicate]
      have : 1 ≤ θE.count e := List.count_pos_iff.2 (hθEtot e he)
      nlinarith
    have h2' : π.count e = π₀.count e + (parikh Θ).count e := by
      rw [← Multiset.coe_count, hπeq, Multiset.count_add, Multiset.coe_count]
    have h3 : π₀.count e ≤ π₀.length := List.count_le_length
    have h4 := f6 hd hB1 hBh hdh h2
    omega
  -- the set `R` of small places of `μ`
  set R := Finset.univ.filter fun p => μ p < h with hRdef
  have hh0 : 0 < h := by omega
  have hiR : i ∈ R := by
    by_contra hiR
    have hst : Stabilized T F (μ + Pi.single i 1) := lemma_5_4 hμstab hh0 hh (fun p => by
      by_cases hpR : p ∈ R
      · have : p ≠ i := fun h => hiR (h ▸ hpR)
        rw [res_add, Pi.add_apply, res_apply_of_mem hpR (Pi.single i 1),
          Pi.single_eq_of_ne this, add_zero]
      · rw [res_apply_of_not_mem hpR, res_apply_of_not_mem hpR])
    have hr : Reach T (Pr.leaders + Pi.single i n) (μ + Pi.single i 1) := by
      have : Pr.leaders + Pi.single i n = ρ' + Pi.single i 1 := by
        rw [hρ'def, add_assoc, single_add_single, Nat.sub_add_cancel hn1]
      rw [this]; exact (hreachδ'.trans ⟨σ', hσ', hrσ'⟩).add _
    exact false_of_reach_stabilized Pr hR hc le_rfl hr hst
  set R' := R.erase i with hR'def
  have hR'card : R'.card ≤ d - 1 := by
    rw [← hcardP']
    exact Finset.card_le_card fun q hq => hmemP' q (Finset.ne_of_mem_erase hq)
  have hR'sum : ∑ q ∈ R', |mdisp Trans.delta Θ q| ≤ ((d * h : ℕ) : ℤ) := by
    have hterm : ∀ q ∈ R', |mdisp Trans.delta Θ q| ≤ ((h + B * M : ℕ) : ℤ) + (α q : ℤ) := by
      intro q hq
      have hqi := Finset.ne_of_mem_erase hq
      have hqR : μ q < h := by simpa [hRdef] using Finset.mem_of_mem_erase hq
      rw [hΘval q, hα'eq q hqi]
      have := hdispπ₀ q
      rw [abs_le] at this ⊢
      push_cast at this ⊢
      constructor <;> linarith
    have hα : ∑ q ∈ R', (α q : ℤ) ≤ ((d - 1) * supNorm α : ℕ) := by
      have : ∑ q ∈ R', α q ≤ R'.card * supNorm α :=
        Finset.sum_le_card_nsmul _ _ _ (fun q _ => le_supNorm α q)
      have h' : R'.card * supNorm α ≤ (d - 1) * supNorm α := Nat.mul_le_mul_right _ hR'card
      exact_mod_cast this.trans h'
    calc ∑ q ∈ R', |mdisp Trans.delta Θ q|
        ≤ ∑ q ∈ R', (((h + B * M : ℕ) : ℤ) + (α q : ℤ)) := Finset.sum_le_sum hterm
      _ = R'.card * ((h + B * M : ℕ) : ℤ) + ∑ q ∈ R', (α q : ℤ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((d - 1) * (h + B * M) + B : ℕ) := by
        have e1 : R'.card * (h + B * M) ≤ (d - 1) * (h + B * M) := Nat.mul_le_mul_right _ hR'card
        have e2 : ((R'.card * (h + B * M) : ℕ) : ℤ) ≤ (((d - 1) * (h + B * M) : ℕ) : ℤ) := by
          exact_mod_cast e1
        push_cast at e2 ⊢
        have e3 : (((d - 1) * supNorm α : ℕ) : ℤ) ≤ B := by exact_mod_cast hdαB
        push_cast at hα e3
        linarith
      _ ≤ ((d * h : ℕ) : ℤ) := by
        have : (d - 1) * (h + B * M) + B ≤ d * h := by
          obtain ⟨D, hD⟩ : ∃ D, D = d - 1 := ⟨_, rfl⟩
          have hdD : d = D + 1 := by omega
          rw [← hD]
          have hh' : h = (D + 1) * (1 + M) * B := by rw [hhdef, hdD]
          rw [hdD, hh']
          nlinarith
        exact_mod_cast this
  -- Lemma 7.3
  set X := (∑ q ∈ R', |mdisp Trans.delta Θ q|).toNat with hXdef
  have hX : (X : ℤ) = ∑ q ∈ R', |mdisp Trans.delta Θ q| :=
    Int.toNat_of_nonneg (Finset.sum_nonneg fun q _ => abs_nonneg _)
  have hXle : X ≤ d * h := by have := hR'sum; rw [← hX] at this; exact_mod_cast this
  have hk := f8 hd hB1 hBh hdh h2 hXle hScard
  obtain ⟨Θ', hΘ'cyc, hsign, hzero, hedge, hlen⟩ := lemma_7_3 hE Trans.delta (M := 1 + M)
    (by omega) hδE (fun θ hθ => (hΘ θ hθ).1) R' k (by rw [← hX, hkdef]; exact_mod_cast hk)
  -- `m = −Δ(Θ')(i) > 0`
  have hf7 : 3 * h + k ≤ h ^ (2 * d + 5) * ℓ := by
    rw [hkdef, hℓdef]; exact f7 hd hB1 hBh hdh h2
  have hΘi : mdisp Trans.delta Θ i ≤ -(k : ℤ) := by
    have e1 := hΘval i
    have e2 : μ i < h := by simpa [hRdef] using hiR
    have e3 : ρ' i ≤ α' i + σ.length * M := hrα'.ge_sub (IsWord.supNorm_le hσ) i
    have e4 : n - 1 ≤ ρ' i := by simp [hρ'def]
    have e5 := hdispπ₀ i
    have e6 : σ.length * M ≤ B * M := Nat.mul_le_mul_right _ hσlen
    rw [abs_le] at e5
    have e7 : ((n - 1 : ℕ) : ℤ) = n - 1 := by push_cast [Nat.cast_sub hn1]; ring
    have e8 : (ρ' i : ℤ) ≤ α' i + σ.length * M := by exact_mod_cast e3
    have e9 : ((n - 1 : ℕ) : ℤ) ≤ ρ' i := by exact_mod_cast e4
    have e10 : ((σ.length * M : ℕ) : ℤ) ≤ ((B * M : ℕ) : ℤ) := by exact_mod_cast e6
    have e11 : ((3 * h + k : ℕ) : ℤ) + 1 ≤ n := by exact_mod_cast (by omega : 3 * h + k + 1 ≤ n)
    have e12 : ((B * M : ℕ) : ℤ) ≤ h := by exact_mod_cast hBM
    push_cast at e1 e5 e10 e11 e12 e8 e9 ⊢
    linarith
  have hΘ'i : mdisp Trans.delta Θ' i < 0 := (hsign i).2.1 hΘi
  set m₀ := (-mdisp Trans.delta Θ' i).toNat with hm₀def
  have hm₀ : (m₀ : ℤ) = -mdisp Trans.delta Θ' i := Int.toNat_of_nonneg (by linarith)
  have hm₀1 : 1 ≤ m₀ := by omega
  have hΘ'nn : ∀ p, p ≠ i → 0 ≤ mdisp Trans.delta Θ' p := by
    intro p hp
    by_cases hpR : p ∈ R
    · rw [hzero p (Finset.mem_erase.2 ⟨hp, hpR⟩)]
    · apply (hsign p).2.2.1
      have e1 := hΘval p
      have e2 : h ≤ μ p := by simpa [hRdef] using hpR
      have e3 : α' p ≤ B := (hα'eq p hp) ▸ (le_supNorm α p).trans hαnorm
      have e5 := hdispπ₀ p
      rw [abs_le] at e5
      have e2' : (h : ℤ) ≤ μ p := by exact_mod_cast e2
      have e3' : (α' p : ℤ) ≤ B := by exact_mod_cast e3
      have e4' : ((B + B * M : ℕ) : ℤ) ≤ h := by exact_mod_cast hBMh
      push_cast at e1 e5 e4' ⊢
      linarith
  -- `η = m·i + Δ(Θ')` as a configuration
  set ηc : Config P := fun p => if p = i then 0 else (mdisp Trans.delta Θ' p).toNat with hηcdef
  have hηc : ∀ p, (ηc p : ℤ) = (if p = i then (m₀ : ℤ) else 0) + mdisp Trans.delta Θ' p := by
    intro p
    by_cases hp : p = i
    · subst hp; simp [hηcdef, hm₀]
    · simp only [hηcdef, hp, if_false, zero_add]
      exact Int.toNat_of_nonneg (hΘ'nn p hp)
  -- Lemma 7.1: one cycle `u` on `α|_Q` with Parikh image `#Θ'`
  have htot : ∀ e ∈ E, e ∈ parikh Θ' := fun e he => hedge e (hcount e he)
  obtain ⟨u, hu, hueq⟩ := lemma_7_1 hE hSC hx₀ hΘ'cyc htot
  set U := u.map fun e => e.2.1 with hUdef
  obtain ⟨hU, hrU⟩ := run_of_path hu
  have hUdelta : ∀ p, wordDelta U p = mdisp Trans.delta Θ' p := by
    intro p; rw [hUdef, ← disp_eq_wordDelta, disp_eq_coe, hueq, mdisp_eq_parikh]
  have hUlen : U.length = mlength Θ' := by
    rw [hUdef, List.length_map, ← card_parikh, ← hueq, Multiset.coe_card]
  have hUM : U.length * M ≤ ℓ := by
    rw [hUlen]
    have e1 : (2 * S.card * (1 + M)) ^ (2 ^ d - 1) ≤ h ^ (2 ^ d - 1) :=
      Nat.pow_le_pow_left (le_trans (by gcongr) hBh) _
    have e2 : (E.card + d) * S.card * (2 * S.card * (1 + M)) ^ (2 ^ d - 1) ≤
        (B * (M + 1) ^ (2 * d) + d) * B * h ^ (2 ^ d - 1) := by gcongr
    have e3 := f5 hd hB1 hBh hdh h2
    rw [← hℓdef] at e3
    calc mlength Θ' * M ≤ (E.card + d) * S.card * (2 * S.card * (1 + M)) ^ (2 ^ d - 1) * M :=
          Nat.mul_le_mul_right _ hlen
      _ ≤ (B * (M + 1) ^ (2 * d) + d) * B * h ^ (2 ^ d - 1) * M := Nat.mul_le_mul_right _ e2
      _ = M * ((B * (M + 1) ^ (2 * d) + d) * B * h ^ (2 ^ d - 1)) := by ring
      _ ≤ ℓ := e3
  -- lift `u` (Lemma 5.2)
  set X₀ := η' + Pi.single i m₀ with hX₀def
  have hX₀Q : res Q X₀ = x₀ := by rw [hX₀def, res_add, res_single_of_not_mem hiQ, add_zero, hη'Q]
  have hη'i : ℓ ≤ η' i := by
    have e1 := (hrα'.append hrη').ge_sub (IsWord.supNorm_le (hσ.append
      (IsWord.flatten_replicate hw _))) i
    rw [← hMdef] at e1
    have e2 : n - 1 ≤ ρ' i := by simp [hρ'def]
    have e3 : (σ ++ wpow).length ≤ W1.length := by simp [hW1]
    have e4 : (σ ++ wpow).length * M ≤ W1.length * M := Nat.mul_le_mul_right _ e3
    omega
  obtain ⟨Y, hrY, -, -⟩ := lemma_5_2 hU (by rw [hX₀Q]; exact hrU) (fun p hpQ => by
    rw [← hMdef, ← hUdef]
    by_cases hp : p = i
    · subst hp
      have : η' p ≤ X₀ p := by simp [hX₀def]
      omega
    · have e1 : X₀ p = η p := by simp [hX₀def, Pi.single_eq_of_ne hp, hη'eq p hp]
      have e2 := hηbig p (Finset.mem_sdiff.2 ⟨hmemP' p hp, hpQ⟩)
      have e3 : ℓ ≤ a * ℓ := Nat.le_mul_of_pos_left _ ha1
      rw [e1]; omega)
  have hY : Y = η' + ηc := by
    funext p
    have e1 := hrY.apply_eq p
    rw [hUdelta p] at e1
    have e2 := hηc p
    have e3 : ((Pi.single i m₀ : Config P) p : ℤ) = if p = i then (m₀ : ℤ) else 0 := by
      by_cases hp : p = i
      · subst hp; simp
      · simp [hp]
    simp only [hX₀def, Pi.add_apply, Nat.cast_add] at e1
    have : (Y p : ℤ) = η' p + ηc p := by rw [e1, e2, e3]; ring
    simp only [Pi.add_apply]
    exact_mod_cast this
  -- the final run reaches a stabilized configuration with input `n − 1 + m ≥ n`
  have hfinal : Reach T (Pr.leaders + Pi.single i (n - 1 + m₀)) (μ + ηc) := by
    have e : Pr.leaders + Pi.single i (n - 1 + m₀) = ρ' + Pi.single i m₀ := by
      rw [hρ'def, add_assoc, single_add_single]
    rw [e]
    refine ⟨(σ ++ wpow) ++ (U ++ (σEpow ++ σ')), ?_, ?_⟩
    · exact (hσ.append (IsWord.flatten_replicate hw _)).append
        (hU.append ((IsWord.flatten_replicate hσE _).append hσ'))
    · refine ((hrα'.append hrη').add (Pi.single i m₀)).append ?_
      refine (hY ▸ hrY).append ?_
      have h1 := hrδ''.add ηc
      have h2 := hrσ'.add ηc
      exact h1.append h2
  have hstab : Stabilized T F (μ + ηc) := lemma_5_4 hμstab hh0 hh (fun p => by
    by_cases hpR : p ∈ R
    · have : ηc p = 0 := by
        by_cases hp : p = i
        · simp [hηcdef, hp]
        · simp [hηcdef, hp, hzero p (Finset.mem_erase.2 ⟨hp, hpR⟩)]
      rw [res_add, Pi.add_apply, res_apply_of_mem hpR ηc, this, add_zero]
    · rw [res_apply_of_not_mem hpR, res_apply_of_not_mem hpR])
  exact false_of_reach_stabilized Pr hR hc (by omega) hfinal hstab

end Sec8

end Podc.PPLeadersStateComplexity
