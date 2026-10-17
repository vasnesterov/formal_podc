import Papers.PODC2013.CongestedCliqueRouting.SortDefs

/-!
# Correctness of the sorting algorithm, rounds 0–22
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

namespace SortSetup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [LinearOrder M] [Nonempty V] {s : ℕ}
  [NeZero s] {τ : SortSetup I V M s}

/-! ### Round 0: samples -/

lemma card_smp_le (hG : τ.Good) (d : I) (v : V) : (τ.smp d v).card ≤ s := by
  unfold smp
  rw [card_samples _ (Nat.pos_of_ne_zero (NeZero.ne s))]
  exact Nat.div_le_of_le_mul (hG.card_le d v)

lemma smpAt_eq_some_iff {d : I} {v : V} {i : Fin s} {x : M} :
    τ.smpAt d v i = some x ↔ x ∈ τ.smp d v ∧ rk (τ.smp d v) x = i := by
  constructor
  · intro h
    have := pick_mem h
    simpa using this
  · rintro ⟨hx, hj⟩
    apply pick_eq_some_of_card_le_one _ (by simp [hx, hj])
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    exact rk_injOn _ ha.1 hb.1 (ha.2.trans hb.2.symm)

lemma smp_sub {d : I} {v : V} {x : M} (h : x ∈ τ.smp d v) : x ∈ τ.inp d v :=
  (mem_filter.1 h).1

lemma len_P0 (d : I) (v w : V) :
    (((τ.smpAt d v (mem τ.e w)).toList.map Item.msg).length ≤ SB) := by
  rcases τ.smpAt d v (mem τ.e w) with _ | x <;> simp [SB]

lemma mem_A1 (hG : τ.Good) {d : I} {w : V} {x : M} :
    x ∈ τ.A1 d w ↔ grp τ.e w = 0 ∧ ∃ v, x ∈ τ.smp d v ∧ rk (τ.smp d v) x = mem τ.e w := by
  unfold A1
  rw [mem_rcvd]
  constructor
  · rintro ⟨v, hv⟩
    unfold P0 at hv
    split_ifs at hv with h0
    · rw [mem_msgsOf_ofList (len_P0 d v w)] at hv
      rcases h : τ.smpAt d v (mem τ.e w) with _ | y
      · simp [h] at hv
      · simp only [h, Option.toList_some, List.map_cons, List.map_nil, List.mem_cons,
          Item.msg.injEq, List.mem_nil_iff, or_false] at hv
        subst hv
        exact ⟨h0, v, smpAt_eq_some_iff.1 h⟩
    · rw [msgsOf_ofList_nil] at hv; simp at hv
  · rintro ⟨h0, v, hx, hr⟩
    refine ⟨v, ?_⟩
    unfold P0
    rw [if_pos h0, mem_msgsOf_ofList (len_P0 d v w),
      smpAt_eq_some_iff.2 ⟨hx, hr⟩]
    simp

lemma card_A1_le (d : I) (w : V) : (τ.A1 d w).card ≤ s * s := by
  rw [← card_V τ.e]
  refine card_rcvd_le fun v => ?_
  have hsub : msgsOf (τ.P0 d v w) ⊆ (τ.smpAt d v (mem τ.e w)).toFinset := by
    intro x hx
    unfold P0 at hx
    split_ifs at hx
    · have := msgsOf_ofList_sub hx; simpa using this
    · rw [msgsOf_ofList_nil] at hx; simp at hx
  exact le_trans (card_le_card hsub) (by cases τ.smpAt d v (mem τ.e w) <;> simp)

lemma hyp1 (hG : τ.Good) : Alg3.Hyp s τ.A1 where
  card_le d v := le_trans (card_A1_le d v) (by nlinarith)
  disj d u w huw := by
    rw [disjoint_left]
    intro x hu hw
    obtain ⟨hu0, v, hv, hvr⟩ := (mem_A1 hG).1 hu
    obtain ⟨hw0, v', hv', hvr'⟩ := (mem_A1 hG).1 hw
    have hvv : v = v' := by
      by_contra hne
      exact disjoint_left.1 (hG.disj d v v' hne) (smp_sub hv) (smp_sub hv')
    subst hvv
    apply huw
    apply τ.e.injective
    exact Prod.ext (hu0.trans hw0.symm) (Fin.ext (hvr.symm.trans hvr'))

lemma GA1 (hG : τ.Good) (d : I) (a : Fin s) :
    Alg3.GA τ.e τ.A1 d a = if a = 0 then τ.Sig d else ∅ := by
  ext x
  simp only [Alg3.GA, mem_biUnion, mem_univ, true_and, mem_A1 hG, grp_node, mem_node]
  split_ifs with ha
  · subst ha
    simp only [Sig, mem_biUnion, mem_univ, true_and, true_and]
    constructor
    · rintro ⟨b, v, hv, -⟩; exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨⟨_, lt_of_lt_of_le (rk_lt_card hv) (card_smp_le hG d v)⟩, v, hv, rfl⟩
  · simp [ha]

lemma A1_known (v : V) : Determined τ.inp τ.run 1 v fun d => τ.A1 d v :=
  (determined_received (r := 0) (by norm_num) v).congr fun d => by
    show rcvd (τ.P0 d) v = rcvd (τ.run d 0) v
    rw [run_0]

lemma A1_holds {d : I} {v : V} {x : M} (h : x ∈ τ.A1 d v) : HoldsS τ.inp τ.run d 1 v x :=
  holdsS_of_mem_received (r := 0) (by show x ∈ rcvd (τ.run d 0) v; rw [run_0]; exact h)
    (by norm_num)

lemma hS1 (d : I) (k : ℕ) (hk : k < 6) : τ.run d (1 + k) = Alg3.pkt τ.e τ.A1 d k :=
  run_alg1 τ d k hk

/-! ### Round 7: delimiters -/

lemma mem_B1 (hG : τ.Good) {d : I} {v : V} {x : M} :
    x ∈ τ.B1 d v ↔ grp τ.e v = 0 ∧ x ∈ τ.Sig d ∧ Alg3.bk τ.e τ.A1 d 0 x = mem τ.e v := by
  unfold B1
  rw [Alg3.mem_Bk' τ.e (hyp1 hG), GA1 hG]
  split_ifs with h
  · rw [h]; simp [h]
  · simp [h]

lemma loc7_eq (hG : τ.Good) (d : I) (v : V) :
    loc7 (τ.B1 d v) (Alg3.Cm τ.e τ.A1 d (grp τ.e v)) (mem τ.e v) =
      (τ.G d).filter fun x => x ∈ τ.B1 d v := by
  unfold B1
  ext x
  simp only [loc7, mem_filter]
  constructor
  · rintro ⟨hx, h1, h2⟩
    refine ⟨?_, hx⟩
    have hr := Alg3.rk_GA τ.e (hyp1 hG) hx
    obtain ⟨h0, hxS, -⟩ := (mem_B1 hG).1 hx
    rw [GA1 hG, if_pos h0] at hr
    simp only [G, delims, mem_filter]
    exact ⟨hxS, by rw [hr]; exact h1, by rw [hr]; exact h2⟩
  · rintro ⟨hxG, hx⟩
    have hr := Alg3.rk_GA τ.e (hyp1 hG) hx
    obtain ⟨h0, hxS, -⟩ := (mem_B1 hG).1 hx
    rw [GA1 hG, if_pos h0] at hr
    simp only [G, delims, mem_filter] at hxG
    exact ⟨hx, by rw [← hr]; exact hxG.2.1, by rw [← hr]; exact hxG.2.2⟩

lemma card_loc7_le (hG : τ.Good) (d : I) (v : V) :
    ((τ.G d).filter fun x => x ∈ τ.B1 d v).card ≤ 6 := by
  by_cases h0 : grp τ.e v = 0
  · have hsub : (τ.G d).filter (fun x => x ∈ τ.B1 d v) ⊆
        (delims (τ.Sig d) (s * s) s).filter fun x => Alg3.bk τ.e τ.A1 d 0 x = mem τ.e v := by
      intro x hx
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, ((mem_B1 hG).1 hx.2).2.2⟩
    refine le_trans (card_le_card hsub) (le_trans (card_delims_filter_le (SortSetup.hNpos (s := s))
      (Alg3.bk_mono τ.e (A := τ.A1) d 0) _) ?_)
    have hB : (τ.Sig d).filter (fun x => Alg3.bk τ.e τ.A1 d 0 x = mem τ.e v) = τ.B1 d v := by
      ext x; rw [mem_filter, mem_B1 hG]; simp [h0]
    rw [hB]
    have hlt := Alg3.card_Bk_lt τ.e (hyp1 hG) d v
    have : (τ.B1 d v).card / (s * s) < 6 := by
      rw [Nat.div_lt_iff_lt_mul (SortSetup.hNpos (s := s))]; unfold B1; linarith
    omega
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    · rw [filter_eq_empty_iff]
      intro x _ hx
      exact h0 ((mem_B1 hG).1 hx).1

lemma len_P7 (hG : τ.Good) (d : I) (v : V) :
    ((loc7 (τ.B1 d v) (Alg3.Cm τ.e τ.A1 d (grp τ.e v)) (mem τ.e v)).toList.map
      Item.msg).length ≤ SB := by
  rw [List.length_map, length_toList, loc7_eq hG]
  have := card_loc7_le hG d v
  simp only [SB]; omega

lemma G_sub_Sig (d : I) : τ.G d ⊆ τ.Sig d := filter_subset _ _

lemma rcvd_P7 (hG : τ.Good) (d : I) (w : V) : rcvd (τ.P7 d) w = τ.G d := by
  ext x
  rw [mem_rcvd]
  constructor
  · rintro ⟨v, hv⟩
    unfold P7 at hv
    rw [mem_msgsOf_ofList (len_P7 hG d v)] at hv
    simp only [List.mem_map, mem_toList, Item.msg.injEq, exists_eq_right] at hv
    rw [loc7_eq hG] at hv
    exact (mem_filter.1 hv).1
  · intro hx
    have hxS := G_sub_Sig d hx
    set y : Fin s := ⟨Alg3.bk τ.e τ.A1 d 0 x, Alg3.bk_lt τ.e _ d 0 x⟩
    refine ⟨node τ.e 0 y, ?_⟩
    unfold P7
    rw [mem_msgsOf_ofList (len_P7 hG d _)]
    simp only [List.mem_map, mem_toList, Item.msg.injEq, exists_eq_right]
    rw [loc7_eq hG, mem_filter, mem_B1 hG]
    exact ⟨hx, by simp, hxS, by simp [y]⟩

lemma G_known (hG : τ.Good) (v : V) : Determined τ.inp τ.run 8 v fun d => τ.G d :=
  (determined_received (r := 7) (by norm_num) v).congr fun d => by
    show τ.G d = rcvd (τ.run d 7) v
    rw [run_7, rcvd_P7 hG]

/-! ### Rounds 8–22: the routing subroutine -/

lemma tgt_eq_iff {d : I} {v w : V} {x : M} :
    τ.tgt d v x = w ↔ τ.gam d x = grp τ.e w ∧ rk (τ.K d v (τ.gam d x)) x % s = mem τ.e w := by
  unfold tgt
  rw [node_eq_iff]
  simp [Fin.ext_iff, eq_comm]

/-- Lemma 4.3 for Algorithm 4: bucket `j` holds fewer than `2 n^{3/2}` keys. -/
lemma sum_K (hG : τ.Good) (d : I) (j : ℕ) :
    ∑ v, (τ.K d v j).card + s * s ≤ 2 * s * (s * s) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have h1 := sum_bucket_le (ι := V) (H := τ.inp d) (hG.disj d) (p := s) hs
    (f := τ.gam d) (fun x y h => bucketOf_mono _ h) j
  have hSig : (τ.Sig d).card ≤ s * s * s := by
    calc (τ.Sig d).card ≤ ∑ v, (τ.smp d v).card := card_biUnion_le
      _ ≤ ∑ _v : V, s := sum_le_sum fun v _ => card_smp_le hG d v
      _ = s * s * s := by simp [card_V τ.e]
  have h2 : ((τ.Sig d).filter fun x => τ.gam d x = j).card ≤ s * s :=
    card_fiber_bucketOf_delims (SortSetup.hNpos (s := s)) hSig j
  rw [card_V τ.e] at h1
  calc ∑ v, (τ.K d v j).card + s * s ≤ s * (((univ.biUnion fun v => samples (τ.inp d v) s).filter
        fun x => τ.gam d x = j).card + s * s) := h1
    _ ≤ s * (s * s + s * s) := Nat.mul_le_mul_left _ (by
        have : (univ.biUnion fun v => samples (τ.inp d v) s) = τ.Sig d := rfl
        rw [this]; omega)
    _ = 2 * s * (s * s) := by ring

/-- Every node receives fewer than `3 n` keys in Step 6. -/
lemma load_tgt (hG : τ.Good) (d : I) (w : V) :
    ∑ v, ((τ.inp d v).filter fun x => τ.tgt d v x = w).card ≤ 3 * (s * s) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have h1 : ∀ v, ((τ.inp d v).filter fun x => τ.tgt d v x = w).card ≤
      ((τ.K d v (grp τ.e w)).card + s - 1) / s := by
    intro v
    refine le_trans (card_le_card fun x hx => ?_) (card_rk_mod_le _ hs (mem τ.e w))
    rw [mem_filter, tgt_eq_iff] at hx
    obtain ⟨hx, h1, h2⟩ := hx
    rw [h1] at h2
    rw [mem_filter]
    refine ⟨?_, h2⟩
    unfold K
    rw [mem_filter]
    exact ⟨hx, h1⟩
  have h2 := sum_K hG d (grp τ.e w)
  have h3 : s * ∑ v, ((τ.K d v (grp τ.e w)).card + s - 1) / s ≤
      ∑ v, ((τ.K d v (grp τ.e w)).card + s - 1) := by
    rw [mul_sum]
    exact sum_le_sum fun v _ => Nat.mul_div_le _ _
  have h4 : ∑ v, ((τ.K d v (grp τ.e w)).card + s - 1) = ∑ v, (τ.K d v (grp τ.e w)).card +
      s * s * (s - 1) := by
    rw [show (fun v => (τ.K d v (grp τ.e w)).card + s - 1) =
      fun v => (τ.K d v (grp τ.e w)).card + (s - 1) by funext v; omega, sum_add_distrib]
    simp [card_V τ.e]
  have h5 : s * ∑ v, ((τ.inp d v).filter fun x => τ.tgt d v x = w).card ≤
      s * (3 * (s * s)) := by
    calc _ ≤ s * ∑ v, ((τ.K d v (grp τ.e w)).card + s - 1) / s :=
          Nat.mul_le_mul_left _ (sum_le_sum fun v _ => h1 v)
      _ ≤ _ := h3
      _ = _ := h4
      _ ≤ s * (3 * (s * s)) := by
          have : s * s * (s - 1) + s * s = s * (s * s) := by
            rcases s with _ | s
            · omega
            · simp only [Nat.add_sub_cancel]; ring
          nlinarith
  exact Nat.le_of_mul_le_mul_left h5 hs

lemma box_hcard (hG : τ.Good) (d : I) (v : V) : (τ.inp d v).card ≤ 2 * s * (2 * s) :=
  le_trans (hG.card_le d v) (by nlinarith)

lemma box_hload (hG : τ.Good) (d : I) (w : V) :
    ∑ v, ((τ.inp d v).filter fun x => τ.tgt d v x = w).card ≤ 2 * s * (2 * s) :=
  le_trans (load_tgt hG d w) (by nlinarith)

lemma pairsIn_known (hG : τ.Good) (v : V) :
    Determined τ.inp τ.run 8 v fun d => pairsIn τ.inp τ.tgt d v := by
  intro d d' hv
  have h1 : τ.inp d v = τ.inp d' v := hv.1
  have h2 := G_known hG v d d' hv
  simp only at h2
  simp only [pairsIn, tgt, K, gam, h1, h2]
  rfl

lemma hSbox (d : I) (r : ℕ) (hr : r < 15) : τ.run d (8 + r) = τ.box d r := run_box τ d r hr

lemma box_isLocal' (hG : τ.Good) : IsLocal (pairsIn τ.inp τ.tgt) τ.box :=
  box_isLocal τ.eV hNpos hNle hFle (box_hcard hG) (box_hload hG)

lemma isLocal_box_seg (hG : τ.Good) {r : ℕ} (hr : r < 15) (v : V) :
    Determined τ.inp τ.run (8 + r) v fun d => τ.run d (8 + r) v :=
  determined_segment (box_isLocal' hG) (hSbox) (pairsIn_known hG) hr v

lemma holds_box_seg (hG : τ.Good) {d : I} {r : ℕ} (hr : r ≤ 15) {v : V} {x : M}
    (h : HoldsS τ.inp τ.box d r v x) : HoldsS τ.inp τ.run d (8 + r) v x :=
  HoldsS.of_segment hSbox (fun _ _ _ hm => Or.inl hm) hr h

lemma valid_box_seg (hG : τ.Good) {d : I} {r : ℕ} (hr : r < 15) {u v : V} {i : Fin SB} {x : M}
    (h : τ.run d (8 + r) u v i = some (Item.msg x)) : HoldsS τ.inp τ.run d (8 + r) u x := by
  rw [hSbox d r hr] at h
  exact holds_box_seg hG hr.le (box_valid τ.eV hNpos hNle hFle (box_hcard hG) (box_hload hG) hr h)

lemma nums_box_seg (hG : τ.Good) {d : I} {r : ℕ} (hr : r < 15) {u v : V} {i : Fin SB} {k : ℕ}
    (h : τ.run d (8 + r) u v i = some (Item.num k)) : k ≤ 2 * s * (2 * s) * (2 * s) := by
  rw [hSbox d r hr] at h
  exact box_num_le τ.eV hNpos hNle hFle (box_hcard hG) (box_hload hG) hr h

/-! ### The holdings after the routing -/

lemma A2_known (hG : τ.Good) (w : V) : Determined τ.inp τ.run 23 w fun d => τ.A2 d w :=
  Determined.of_segment (len := 15) hSbox (pairsIn_known hG) le_rfl
    (box_known τ.eV hNpos hNle hFle (box_hcard hG) (box_hload hG) w)

lemma mem_A2 {d : I} {w : V} {x : M} : x ∈ τ.A2 d w ↔ ∃ v, x ∈ τ.inp d v ∧ τ.tgt d v x = w := by
  simp [A2, Recv]

lemma A2_holds (hG : τ.Good) {d : I} {w : V} {x : M} (h : x ∈ τ.A2 d w) :
    HoldsS τ.inp τ.run d 23 w x := by
  obtain ⟨v, hv, rfl⟩ := mem_A2.1 h
  exact holds_box_seg hG le_rfl
    (box_deliver τ.eV hNpos hNle hFle (box_hcard hG) (box_hload hG) d v hv)

lemma hyp2 (hG : τ.Good) : Alg3.Hyp s τ.A2 where
  card_le d w := by
    refine le_trans ?_ (load_tgt hG d w)
    unfold A2 Recv
    exact card_biUnion_le
  disj d u w huw := by
    rw [disjoint_left]
    intro x hu hw
    obtain ⟨v, hv, rfl⟩ := mem_A2.1 hu
    obtain ⟨v', hv', hvw⟩ := mem_A2.1 hw
    have : v = v' := by
      by_contra hne
      exact disjoint_left.1 (hG.disj d v v' hne) hv hv'
    subst this
    exact huw hvw

lemma hS2 (d : I) (k : ℕ) (hk : k < 6) : τ.run d (23 + k) = Alg3.pkt τ.e τ.A2 d k :=
  run_alg2 τ d k hk

end SortSetup

end CongestedCliqueRouting
