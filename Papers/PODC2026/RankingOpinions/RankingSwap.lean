import Papers.PODC2026.RankingOpinions.RankingRank

/-!
# The Ranking protocol: reachability, part 2 (Lemma 6.12)

From a stable consistent configuration whose ranking `σ` is not yet correct, rules (6) and (7)
fix the ranking of the most popular color `u` whose ranking is wrong (exchanging it with the
color `v` that currently holds `u`'s correct ranking). The number of colors with a wrong ranking
strictly decreases.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Ranking

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Finset

variable {k : ℕ} [NeZero k] {A : Type*} [DecidableEq A] [Fintype A]

/-- Number of colors with a wrong ranking. -/
def wrong (x : Fin k → ℕ) (σ : Fin k → Fin k) : ℕ := (univ.filter fun c => σ c ≠ rnk x c).card

lemma wrong_swap_lt {x : Fin k → ℕ} {σ : Fin k → Fin k} {u v : Fin k} (hv : σ v = rnk x u)
    (hu : σ u ≠ rnk x u) (hv' : σ v ≠ rnk x v) :
    wrong x (σ ∘ Equiv.swap u v) < wrong x σ := by
  have huv : u ≠ v := by rintro rfl; exact hu hv
  apply card_lt_card
  refine ⟨fun c hc => ?_, fun hs => ?_⟩
  · simp only [mem_filter, mem_univ, true_and, Function.comp] at hc ⊢
    by_cases h1 : c = u
    · subst h1; rw [Equiv.swap_apply_left, hv] at hc; exact absurd rfl hc
    by_cases h2 : c = v
    · subst h2; exact hv'
    · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at hc
  · have := hs (show u ∈ univ.filter fun c => σ c ≠ rnk x c by simpa using hu)
    simp [Equiv.swap_apply_left, hv] at this

/-- After exchanging the rankings of the tokens of `u` and `v`. -/
lemma tr_swap {C : Config A (RState k)} {σ : Fin k → Fin k} (h1 : OneTok C) (h2 : TR σ C)
    {H V : A} (hHV : H ≠ V) {u v : Fin k} (hH : (C H).tok) (hHu : (C H).kc = u)
    (hV : (C V).tok) (hVv : (C V).kc = v) {s t : RState k} (hr : rδ (C H) (C V) = (s, t))
    (hs : s.tok ∧ s.kc = u ∧ s.kr = σ v) (ht : t.tok ∧ t.kc = v ∧ t.kr = σ u) :
    OneTok ((ranking k).interact C H V) ∧ TR (σ ∘ Equiv.swap u v) ((ranking k).interact C H V) := by
  have hI := interact_eq hr
  constructor
  · apply h1.of_eq; intro x; rw [hI]; dsimp only
    split_ifs with h3 h4
    · subst h3; rw [hs.1, hs.2.1, hH, hHu]; exact ⟨rfl, rfl⟩
    · subst h4; rw [ht.1, ht.2.1, hV, hVv]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · intro x hx; rw [hI] at hx ⊢; dsimp only at hx ⊢
    split_ifs at hx ⊢ with h3 h4
    · rw [hs.2.2, hs.2.1]; simp
    · rw [ht.2.2, ht.2.1]; simp
    · have hu : (C x).kc ≠ u := fun e => h3 (h1 x H hx hH (e.trans hHu.symm))
      have hv : (C x).kc ≠ v := fun e => h4 (h1 x V hx hV (e.trans hVv.symm))
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hu hv]; exact h2 x hx

/-- Moving a token with rule (6) keeps a stable consistent configuration stable and consistent. -/
lemma move_token {input : A → Fin k} {σ : Fin k → Fin k} {C : Config A (RState k)}
    (hC : Inv input C) (h1 : OneTok C) (h2 : Cons σ C) (hs : Stable (brk C)) {t h : A}
    (hth : t ≠ h) (hr : rδ (C t) (C h) = ({C t with tok := true}, {C h with tok := false}))
    (htt : (C t).tok = false) (hht : (C h).tok) (hkc : (C t).kc = (C h).kc) :
    ∃ C1, (ranking k).Reachable C C1 ∧ Inv input C1 ∧ OneTok C1 ∧ Cons σ C1 ∧
      Stable (brk C1) ∧ (C1 t).tok ∧ (C1 t).kc = (C t).kc ∧ (C1 t).bc = (C t).bc ∧
      (C1 t).br = (C t).br := by
  have hI := interact_eq hr
  have hb : brk ((ranking k).interact C t h) = brk C := by
    funext x; rw [hI]; simp only [brk]; split_ifs with h3 h4
    · subst h3; rfl
    · subst h4; rfl
    · rfl
  refine ⟨_, step_of hth, hC.step ⟨t, h, hth, rfl⟩, ?_, ?_, by rw [hb]; exact hs, ?_⟩
  · apply h1.of_swap (a := t) (b := h); intro x; rw [hI]; dsimp only
    split_ifs with h3 h4
    · subst h3; simp [hht, hkc]
    · subst h4; simp [htt, hkc]
    · simp [Equiv.swap_apply_of_ne_of_ne h3 h4]
  · intro x; rw [hI]; dsimp only; split_ifs with h3 h4
    · exact h2 t
    · exact h2 h
    · exact h2 x
  · rw [hI]; simp

/-- The token of a color in strict relative majority can be put on a diagonal braket. -/
lemma top_on_diag {input : A → Fin k} {σ : Fin k → Fin k} (hσ : Function.Injective σ)
    {C : Config A (RState k)} (hC : Inv input C) (h1 : OneTok C) (h2 : Cons σ C)
    (hs : Stable (brk C)) {u : Fin k} (hu : ∀ c, c ≠ u → inputCount input c < inputCount input u) :
    ∃ C1, (ranking k).Reachable C C1 ∧ Inv input C1 ∧ OneTok C1 ∧ Cons σ C1 ∧
      Stable (brk C1) ∧ ∃ H, (C1 H).tok ∧ (C1 H).kc = u ∧ (C1 H).bc = u := by
  obtain ⟨H, hH, hHu⟩ := hC.holder u
  by_cases hd : (C H).bc = u
  · exact ⟨C, Relation.ReflTransGen.refl, hC, h1, h2, hs, H, hH, hHu, hd⟩
  -- a diagonal braket `⟨σ u|σ u⟩` exists
  have hsurj := Finite.surjective_of_injective hσ
  have hmem : (σ u, σ u) ∈ layers (ycount input σ) := by
    rw [diag_mem_layers_iff, ycount_apply input hσ]
    refine ⟨?_, fun m hm => ?_⟩
    · obtain ⟨a, ha⟩ := hC.tok u
      have : 0 < (univ.val.map input).count u := by
        rw [← hC.kc, Multiset.count_pos]
        exact Multiset.mem_map.2 ⟨a, mem_univ_val a, ha.2⟩
      rwa [count_map_input] at this
    · obtain ⟨c, rfl⟩ := hsurj m
      rw [ycount_apply input hσ]
      exact hu c (fun e => hm (by rw [e]))
  obtain ⟨D, hDb, hDk⟩ := exists_of_mem_layers hC h2 hs hmem
  have hDbc : (C D).bc = u := hσ (by rw [← (h2 D).1, hDb])
  have hDkc : (C D).kc = u := hσ (by rw [← (h2 D).2, hDk])
  have hDH : D ≠ H := by rintro rfl; exact hd hDbc
  have hDt : (C D).tok = false := tok_false (fun ht => hDH (h1 D H ht hH (hDkc.trans hHu.symm)))
  have hr := rδ_r6a (t := C D) (h := C H) hDt (hDbc.trans hDkc.symm) (by rw [hDb, hDk]) hH
    (hHu.trans hDkc.symm) (by rw [(h2 H).2, hHu, hDk])
  obtain ⟨C1, r1, i1, o1, c1, s1, t1, k1, b1, -⟩ :=
    move_token hC h1 h2 hs hDH hr hDt hH (hDkc.trans hHu.symm)
  exact ⟨C1, r1, i1, o1, c1, s1, D, t1, k1.trans hDkc, b1.trans hDbc⟩

lemma inputCount_pos {input : A → Fin k} (hall : ∀ c, ∃ a, input a = c) (c : Fin k) :
    0 < inputCount input c := by
  obtain ⟨a, ha⟩ := hall c
  exact card_pos.2 ⟨a, by simp [ha]⟩

/-- **Lemma 6.12** (one step): if the ranking `σ` of a stable consistent configuration is wrong,
rules (6) and (7) strictly decrease the number of colors with a wrong ranking. -/
lemma phase5 {input : A → Fin k} (hall : ∀ c, ∃ a, input a = c)
    (hx : Function.Injective (inputCount input)) {σ : Fin k → Fin k}
    (hσ : Function.Injective σ) {C : Config A (RState k)} (hC : Inv input C) (h1 : OneTok C)
    (h2 : Cons σ C) (hs : Stable (brk C)) (hw : ∃ c, σ c ≠ rnk (inputCount input) c) :
    ∃ C' σ', (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ TR σ' C' ∧
      Function.Injective σ' ∧ wrong (inputCount input) σ' < wrong (inputCount input) σ := by
  set x := inputCount input with hxdef
  have hsurj := Finite.surjective_of_injective hσ
  have hy : ∀ c, ycount input σ (σ c) = x c := ycount_apply input hσ
  -- the most popular color `u` with a wrong ranking
  obtain ⟨u, hu, hmin⟩ := (univ.filter fun c => σ c ≠ rnk x c).exists_min_image (rnk x)
    (by obtain ⟨c, hc⟩ := hw; exact ⟨c, by simpa using hc⟩)
  simp only [mem_filter, mem_univ, true_and] at hu hmin
  have pre : ∀ c, rnk x c < rnk x u → σ c = rnk x c := by
    intro c hc; by_contra h; exact absurd (hmin c h) (not_le.2 hc)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, rnk x u = ℓ := ⟨_, rfl⟩
  rw [hℓ] at hu pre
  obtain ⟨v, hv⟩ := hsurj ℓ
  have hvu : v ≠ u := by rintro rfl; exact hu hv
  have hσu : ℓ < σ u := by
    rcases lt_trichotomy (σ u) ℓ with h | h | h
    · obtain ⟨c, hc⟩ := rnk_surjective hx (σ u)
      have := pre c (hc ▸ h)
      rw [hc] at this
      have hcu := hσ this
      rw [hcu, hℓ] at hc; rw [hc] at h; exact absurd h (lt_irrefl _)
    · exact absurd h hu
    · exact h
  have hrv : ℓ < rnk x v := by
    rcases lt_trichotomy (rnk x v) ℓ with h | h | h
    · have := pre v h; rw [hv] at this; rw [this] at h; exact absurd h (lt_irrefl _)
    · exact absurd (rnk_injective hx (h.trans hℓ.symm)) hvu
    · exact h
  have hxv : x v < x u := lt_of_rnk_lt hx (hℓ ▸ hrv)
  -- colors other than `u` whose ranking is at least `ℓ` are less popular than `u`
  have below : ∀ c, c ≠ u → ℓ ≤ σ c → x c < x u := by
    intro c hcu hc
    rcases lt_trichotomy (rnk x c) ℓ with h | h | h
    · rw [pre c h] at hc; exact absurd hc (not_le.2 h)
    · exact absurd (rnk_injective hx (h.trans hℓ.symm)) hcu
    · exact lt_of_rnk_lt hx (hℓ ▸ h)
  have hσv : σ v ≠ rnk x v := by rw [hv]; exact hrv.ne
  have hσ' : Function.Injective (σ ∘ Equiv.swap u v) := hσ.comp (Equiv.injective _)
  by_cases hℓ0 : (ℓ : ℕ) = 0
  · ---- `u` is the majority color: rule (7), first bullet
    have htop : ∀ c, c ≠ u → x c < x u := rnk_eq_zero hx (hℓ ▸ hℓ0)
    obtain ⟨C1, r1, i1, o1, c1, s1, H, hH, hHu, hHb⟩ := top_on_diag hσ hC h1 h2 hs htop
    obtain ⟨V, hV, hVv⟩ := i1.holder v
    have hHV : H ≠ V := by rintro rfl; exact hvu (hVv.symm.trans hHu)
    have hℓz : ℓ = 0 := Fin.ext hℓ0
    have hr := rδ_r7a (a := C1 H) (b := C1 V) hH hV (hHb.trans hHu.symm)
      (by rw [(c1 H).1, (c1 H).2, hHb, hHu]) (by rw [(c1 V).2, hVv, hv, hℓz])
      (by rw [hVv, hHb]; exact hvu) (by rw [(c1 H).1, hHb, ← hℓz]; exact hσu.ne')
      (fun e => by rw [(c1 V).1, (c1 H).2, e])
      (s1 H V hHV) (s1 V H hHV.symm)
    obtain ⟨o2, t2⟩ := tr_swap o1 c1.tr hHV hH hHu hV hVv hr
      ⟨hH, hHu, by rw [hv, hℓz]⟩
      ⟨by rw [norm_tok]; exact hV, by rw [norm_kc]; exact hVv,
        by rw [norm_kr]; simp only; rw [(c1 H).1, hHb]⟩
    exact ⟨_, _, r1.trans (step_of hHV), i1.step ⟨H, V, hHV, rfl⟩, o2, t2, hσ',
      wrong_swap_lt (hv.trans hℓ.symm) (hℓ ▸ hu) hσv⟩
  · ---- `ℓ ≥ 1`: rule (6) then rule (7), second bullet
    obtain ⟨g, hgv⟩ : ∃ g : Fin k, (g : ℕ) = ℓ - 1 := ⟨⟨(ℓ : ℕ) - 1, by omega⟩, rfl⟩
    have hgℓ : (g : ℕ) < ℓ := by omega
    obtain ⟨cg, hcg⟩ := rnk_surjective hx g
    have hσcg : σ cg = g := by rw [pre cg (by rw [hcg]; exact hgℓ), hcg]
    have hxcg : x u < x cg := lt_of_rnk_lt hx (by rw [hcg, hℓ]; exact hgℓ)
    have hcgu : cg ≠ u := by rintro rfl; rw [hcg] at hℓ; rw [hℓ] at hgℓ; exact absurd hgℓ (lt_irrefl _)
    have hcgv : cg ≠ v := by rintro rfl; rw [hσcg] at hv; rw [hv] at hgℓ; omega
    have hσuv : (g : ℕ) < σ u := lt_trans hgℓ hσu
    -- the braket `⟨g|σ u⟩` exists
    have hmem : (g, σ u) ∈ layers (ycount input σ) := by
      apply mem_layers_of_gap hσuv
      · rw [hy]; exact inputCount_pos hall u
      · rw [hy, ← hσcg, hy]; exact hxcg
      · intro m hm1 hm2
        obtain ⟨c, rfl⟩ := hsurj m
        rw [hy, hy]
        apply below c (fun e => by rw [e] at hm2; omega)
        show (ℓ : ℕ) ≤ σ c; omega
    obtain ⟨T, hTb, hTk⟩ := exists_of_mem_layers hC h2 hs hmem
    have hTkc : (C T).kc = u := hσ (by rw [← (h2 T).2, hTk])
    have hTbc : (C T).bc = cg := hσ (by rw [← (h2 T).1, hTb, hσcg])
    -- put the token of `u` on a braket with bra ranking `g`
    obtain ⟨C1, r1, i1, o1, c1, s1, H, hH, hHu, hHg⟩ : ∃ C1, (ranking k).Reachable C C1 ∧
        Inv input C1 ∧ OneTok C1 ∧ Cons σ C1 ∧ Stable (brk C1) ∧
        ∃ H, (C1 H).tok ∧ (C1 H).kc = u ∧ (C1 H).br = g := by
      obtain ⟨H, hH, hHu⟩ := hC.holder u
      have hbd : (g : ℕ) ≤ (C H).br ∧ ((C H).br : ℕ) < (C H).kr :=
        bra_bound_layers (brk_mem_layers hC h2 hs H)
        (g := g) (by simp only; rw [(h2 H).2, hHu]; exact hσuv)
        (by simp only; rw [(h2 H).2, hHu, hy, ← hσcg, hy]; exact hxcg)
      by_cases hHg : (C H).br = g
      · exact ⟨C, Relation.ReflTransGen.refl, hC, h1, h2, hs, H, hH, hHu, hHg⟩
      have hTH : T ≠ H := by rintro rfl; exact hHg hTb
      have hTt : (C T).tok = false :=
        tok_false (fun ht => hTH (h1 T H ht hH (hTkc.trans hHu.symm)))
      have hHd : (C H).bc ≠ (C H).kc := by
        intro e
        have := (h2 H).1; rw [e, ← (h2 H).2] at this
        rw [this] at hbd; exact lt_irrefl _ hbd.2
      have hr := rδ_r6b (t := C T) (h := C H) hTt hH (hTkc.trans hHu.symm)
        (by rw [hTk, (h2 H).2, hHu]) (by rw [hTbc, hTkc]; exact hcgu) hHd
        (by rw [hTb]; show g < (C H).br; rw [Fin.lt_def]
            have : (g : ℕ) ≠ (C H).br := fun e => hHg (Fin.ext e).symm
            omega)
      obtain ⟨C1, r1, i1, o1, c1, s1, t1, k1, -, b1⟩ :=
        move_token hC h1 h2 hs hTH hr hTt hH (hTkc.trans hHu.symm)
      exact ⟨C1, r1, i1, o1, c1, s1, T, t1, k1.trans hTkc, b1.trans hTb⟩
    have hHbc : (C1 H).bc = cg := hσ (by rw [← (c1 H).1, hHg, hσcg])
    -- the token of `v` sits on a braket with bra ranking `g`
    obtain ⟨V, hV, hVv⟩ := i1.holder v
    have hHV : H ≠ V := by rintro rfl; exact hvu (hVv.symm.trans hHu)
    have hVg : (C1 V).br = g := by
      have hbd : (g : ℕ) ≤ (C1 V).br ∧ ((C1 V).br : ℕ) < (C1 V).kr :=
        bra_bound_layers (brk_mem_layers i1 c1 s1 V) (g := g)
        (by simp only; rw [(c1 V).2, hVv, hv]; exact hgℓ)
        (by simp only; rw [(c1 V).2, hVv, hy, ← hσcg, hy]; omega)
      rw [(c1 V).2, hVv, hv] at hbd
      exact Fin.ext (by omega)
    have hVbc : (C1 V).bc = cg := hσ (by rw [← (c1 V).1, hVg, hσcg])
    have hr := rδ_r7b (a := C1 H) (b := C1 V) hH hV (hHbc.trans hVbc.symm) (hHg.trans hVg.symm)
      (by rw [hHu, hHbc]; exact hcgu.symm) (by rw [hVv, hVbc]; exact hcgv.symm)
      (by rw [hHu, hVv]; exact hvu.symm)
      (by rw [(c1 H).2, (c1 V).2, hHu, hVv]; exact fun e => hvu (hσ e).symm)
      (s1 H V hHV) (s1 V H hHV.symm)
    obtain ⟨o2, t2⟩ := tr_swap o1 c1.tr hHV hH hHu hV hVv hr
      ⟨hH, hHu, by simp only; rw [(c1 V).2, hVv]⟩
      ⟨hV, hVv, by simp only; rw [(c1 H).2, hHu]⟩
    exact ⟨_, _, r1.trans (step_of hHV), i1.step ⟨H, V, hHV, rfl⟩, o2, t2, hσ',
      wrong_swap_lt (hv.trans hℓ.symm) (hℓ ▸ hu) hσv⟩

end RankingOpinions.Ranking
