import Papers.PODC2013.CongestedCliqueRouting.SortSpec1

/-!
# Correctness of the sorting algorithm, rounds 23–31, and the square case of Theorem 4.5
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

namespace SortSetup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [LinearOrder M] [Nonempty V] {s : ℕ}
  [NeZero s] {τ : SortSetup I V M s}

lemma enc_node (a b : Fin s) : enc τ.e (node τ.e a b) = b + s * a := by
  simp [enc, node, finProdFinEquiv_apply_val]

lemma GA2_eq (d : I) (a : Fin s) :
    Alg3.GA τ.e τ.A2 d a = (τ.U d).filter fun x => τ.gam d x = a := by
  ext x
  simp only [Alg3.GA, mem_biUnion, mem_univ, true_and, mem_A2, mem_filter, U]
  constructor
  · rintro ⟨b, v, hv, ht⟩
    rw [tgt_eq_iff] at ht
    exact ⟨⟨v, hv⟩, by simpa using ht.1⟩
  · rintro ⟨⟨v, hv⟩, hg⟩
    refine ⟨⟨rk (τ.K d v (τ.gam d x)) x % s, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne s))⟩,
      v, hv, ?_⟩
    rw [tgt_eq_iff]
    simp [hg]

/-- The node holding `x` after the second Algorithm 3. -/
def hold (d : I) (x : M) : V :=
  node τ.e ⟨τ.gam d x, τ.gam_lt d x⟩
    ⟨Alg3.bk τ.e τ.A2 d ⟨τ.gam d x, τ.gam_lt d x⟩ x, Alg3.bk_lt τ.e _ d _ x⟩

lemma mem_B2 (hG : τ.Good) {d : I} {w : V} {x : M} :
    x ∈ τ.B2 d w ↔ x ∈ τ.U d ∧ τ.hold d x = w := by
  unfold B2
  rw [Alg3.mem_Bk' τ.e (hyp2 hG), GA2_eq, mem_filter, hold, node_eq_iff]
  constructor
  · rintro ⟨⟨hU, hg⟩, hb⟩
    have ha : grp τ.e w = ⟨τ.gam d x, τ.gam_lt d x⟩ := Fin.ext hg.symm
    refine ⟨hU, ha, ?_⟩
    rw [Fin.ext_iff]
    simp only
    rw [← ha]
    exact hb.symm
  · rintro ⟨hU, hg, hb⟩
    refine ⟨⟨hU, by rw [hg]⟩, ?_⟩
    rw [hg]
    rw [Fin.ext_iff] at hb
    exact hb.symm

lemma blk_mono (d : I) : Monotone fun x => enc τ.e (τ.hold d x) := by
  intro x y hxy
  simp only [hold, enc_node, Fin.val_mk]
  have hg : τ.gam d x ≤ τ.gam d y := bucketOf_mono _ hxy
  have h1 := Alg3.bk_lt τ.e τ.A2 d ⟨τ.gam d x, τ.gam_lt d x⟩ x
  rcases lt_or_eq_of_le hg with h | h
  · have : s * (τ.gam d x + 1) ≤ s * τ.gam d y := Nat.mul_le_mul_left _ h
    nlinarith
  · have hfin : (⟨τ.gam d x, τ.gam_lt d x⟩ : Fin s) = ⟨τ.gam d y, τ.gam_lt d y⟩ := Fin.ext h
    have := Alg3.bk_mono τ.e (A := τ.A2) d ⟨τ.gam d y, τ.gam_lt d y⟩ hxy
    rw [hfin, h]
    omega

lemma B2_disj (hG : τ.Good) (d : I) {v w : V} (h : v ≠ w) : Disjoint (τ.B2 d v) (τ.B2 d w) := by
  rw [disjoint_left]
  intro x hv hw
  exact h (((mem_B2 hG).1 hv).2.symm.trans ((mem_B2 hG).1 hw).2)

/-- The global rank of a key held by `w` at the end of Step 7. -/
lemma rank_U (hG : τ.Good) {d : I} {w : V} {x : M} (hx : x ∈ τ.B2 d w) :
    rk (τ.U d) x = τ.offOf (τ.L d) w + rk (τ.B2 d w) x := by
  obtain ⟨hU, hh⟩ := (mem_B2 hG).1 hx
  rw [rk_eq_add (blk_mono (τ := τ) d) hU]
  congr 1
  · rw [offOf, card_eq_sum_card_fiberwise (f := τ.hold d) (t := univ.filter
      fun w' => enc τ.e w' < enc τ.e w)]
    · refine sum_congr rfl fun w' hw' => ?_
      unfold L
      congr 1
      ext y
      rw [mem_filter, mem_filter, mem_B2 hG]
      simp only [mem_filter, mem_univ, true_and] at hw'
      constructor
      · rintro ⟨⟨hy, -⟩, h⟩; exact ⟨hy, h⟩
      · rintro ⟨hy, h⟩; exact ⟨⟨hy, by rw [h, hh]; exact hw'⟩, h⟩
    · intro y hy
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hy ⊢
      rw [hh] at hy; exact hy.2
  · congr 1
    ext y
    rw [mem_filter, mem_B2 hG, hh]
    constructor
    · rintro ⟨hy, h⟩; exact ⟨hy, enc_inj τ.e h⟩
    · rintro ⟨hy, h⟩; exact ⟨hy, by rw [h]⟩

lemma fR_eq (d : I) (v w : V) :
    τ.fROf (τ.L d) v w = ((τ.B2 d v).filter fun x => τ.tgF d v x = w).card := by
  unfold fROf tgF
  rw [card_filter_rk (τ.B2 d v) (fun r => τ.out (τ.offOf (τ.L d) v + r) = w)]
  have : Ico (τ.offOf (τ.L d) v) (τ.offOf (τ.L d) v + τ.L d v) =
      (range (τ.L d v)).map (addLeftEmbedding (τ.offOf (τ.L d) v)) := by
    rw [range_eq_Ico, map_add_left_Ico, add_zero]
  rw [this, filter_map, card_map]
  rfl

lemma fR_row (d : I) (v : V) : ∑ w, τ.fROf (τ.L d) v w = τ.L d v := by
  unfold fROf
  rw [← card_eq_sum_card_fiberwise (f := τ.out) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  simp

lemma fR_col (hG : τ.Good) (d : I) (w : V) : ∑ v, τ.fROf (τ.L d) v w ≤ s * s := by
  simp only [fR_eq]
  have h1 : ∀ v, ((τ.B2 d v).filter fun x => τ.tgF d v x = w) =
      (τ.B2 d v).filter fun x => τ.out (rk (τ.U d) x) = w := by
    intro v
    refine filter_congr fun x hx => ?_
    rw [tgF, rank_U hG hx]
  simp only [h1]
  have h2 : (τ.U d).filter (fun x => τ.out (rk (τ.U d) x) = w) =
      univ.biUnion fun v => (τ.B2 d v).filter fun x => τ.out (rk (τ.U d) x) = w := by
    ext x
    simp only [mem_filter, mem_biUnion, mem_univ, true_and, mem_B2 hG]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨_, ⟨hx, rfl⟩, h⟩
    · rintro ⟨v, ⟨hx, -⟩, h⟩; exact ⟨hx, h⟩
  rw [← card_biUnion (fun v _ v' _ h => disjoint_filter_filter (B2_disj hG d h)), ← h2,
    card_filter_rk (τ.U d) (fun r => τ.out r = w)]
  exact hG.out_le d w

lemma fRp_spec (hG : τ.Good) (d : I) :
    (∀ v w, ∑ c, τ.fRp d c v w = τ.fROf (τ.L d) v w) ∧ (∀ c v, ∑ w, τ.fRp d c v w ≤ 6) ∧
      (∀ c w, ∑ v, τ.fRp d c v w ≤ 6) := by
  refine splitParts_spec (ι := V) (fun v => ?_) (fun w => ?_)
  · rw [fR_row, card_V τ.e]
    have := Alg3.card_Bk_lt τ.e (hyp2 hG) d v
    unfold L B2; omega
  · rw [card_V τ.e]
    have := fR_col hG d w
    omega

lemma viaF_cap (hG : τ.Good) (d : I) (v : V) (w : V) :
    ((τ.B2 d v).filter fun x => τ.tgF d v x = w).card ≤ ∑ c, τ.fRp d c v w := by
  rw [(fRp_spec hG d).1, fR_eq]

lemma card_viaF_le (hG : τ.Good) (d : I) (v c : V) :
    ((τ.B2 d v).filter fun x => τ.viaF d v x = c).card ≤ 6 := by
  rw [card_filter_eq_sum_fiber _ (τ.viaF d v) (τ.tgF d v) c]
  refine le_trans (sum_le_sum fun w _ => ?_) ((fRp_spec hG d).2.1 c v)
  have := assign_le (viaF_cap hG d v) w c
  refine le_trans (le_of_eq (congrArg card (filter_congr fun x _ => ?_))) this
  simp only [viaF]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma len_P30 (hG : τ.Good) (d : I) (v c : V) :
    2 * ((τ.B2 d v).filter fun x => τ.viaF d v x = c).card ≤ SB := by
  have := card_viaF_le hG d v c
  simp only [SB]; omega

lemma mem_fwd_P30 (hG : τ.Good) {d : I} {c w : V} {x : M} :
    x ∈ fwd (enc τ.e) (fun u => τ.P30 d u c) w ↔
      ∃ u, x ∈ τ.B2 d u ∧ τ.viaF d u x = c ∧ τ.tgF d u x = w :=
  mem_fwd_rr1 (enc_inj τ.e) (fun u => len_P30 hG d u c)

lemma card_fwd_P30 (hG : τ.Good) (d : I) (c w : V) :
    (fwd (enc τ.e) (fun u => τ.P30 d u c) w).card ≤ 6 := by
  have hsub : fwd (enc τ.e) (fun u => τ.P30 d u c) w ⊆ univ.biUnion fun u =>
      (τ.B2 d u).filter fun x => τ.tgF d u x = w ∧ τ.viaF d u x = c := by
    intro x hx
    obtain ⟨u, hu, hc, ht⟩ := (mem_fwd_P30 hG).1 hx
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    exact ⟨u, hu, ht, hc⟩
  refine le_trans (card_le_card hsub) (le_trans card_biUnion_le ?_)
  refine le_trans (sum_le_sum fun u _ => ?_) ((fRp_spec hG d).2.2 c w)
  exact assign_le (viaF_cap hG d u) w c

lemma mem_HF (hG : τ.Good) {d : I} {w : V} {x : M} :
    x ∈ τ.HF d w ↔ ∃ u, x ∈ τ.B2 d u ∧ τ.tgF d u x = w := by
  unfold HF
  rw [mem_rcvd]
  constructor
  · rintro ⟨c, hc⟩
    rw [P31, msgsOf_rr2 (by simp only [SB]; have := card_fwd_P30 hG d c w; omega),
      mem_fwd_P30 hG] at hc
    obtain ⟨u, hu, -, ht⟩ := hc
    exact ⟨u, hu, ht⟩
  · rintro ⟨u, hu, ht⟩
    refine ⟨τ.viaF d u x, ?_⟩
    rw [P31, msgsOf_rr2 (by simp only [SB]; have := card_fwd_P30 hG d (τ.viaF d u x) w; omega),
      mem_fwd_P30 hG]
    exact ⟨u, hu, rfl, ht⟩

/-- Every key ends at the output node of its global rank. -/
lemma final (hG : τ.Good) {d : I} {x : M} (hx : x ∈ τ.U d) :
    x ∈ τ.HF d (τ.out (rk (τ.U d) x)) := by
  have hB : x ∈ τ.B2 d (τ.hold d x) := (mem_B2 hG).2 ⟨hx, rfl⟩
  rw [mem_HF hG]
  exact ⟨_, hB, by rw [tgF, rank_U hG hB]⟩

/-! ### Locality -/

lemma loc_0 (v : V) : Determined τ.inp τ.run 0 v fun d => τ.run d 0 v :=
  ((determined_inp 0 v).map fun H => fun w =>
    if grp τ.e w = 0 then (ofList ((pick ((samples H s).filter fun x =>
      rk (samples H s) x = mem τ.e w)).toList.map Item.msg) : Packet M SB) else ofList []).congr
    fun d => by rw [run_0]; rfl

lemma hS1' (d : I) (k : ℕ) (hk : k < 6) : τ.run d (1 + k) = Alg3.pkt τ.e τ.A1 d k := hS1 d k hk

lemma loc_alg1 (hG : τ.Good) (k : ℕ) (hk : k < 6) (v : V) :
    Determined τ.inp τ.run (k + 1) v fun d => τ.run d (k + 1) v := by
  have := Alg3.isLocal_alg3 τ.e (t0 := 1) (A := τ.A1) hS1' A1_known (hyp1 hG) hk v
  rwa [Nat.add_comm] at this

lemma loc_7 (hG : τ.Good) (v : V) : Determined τ.inp τ.run 7 v fun d => τ.run d 7 v := by
  have h1 : Determined τ.inp τ.run 7 v fun d => τ.B1 d v :=
    Alg3.Bk_known τ.e (t0 := 1) (A := τ.A1) hS1' v
  have h2 : Determined τ.inp τ.run 7 v fun d => Alg3.Cm τ.e τ.A1 d (grp τ.e v) :=
    (Alg3.Cm_known τ.e (t0 := 1) (A := τ.A1) hS1' v).mono (by norm_num)
  refine ((h1.pair h2).map fun p => fun _ =>
    (ofList ((loc7 p.1 p.2 (mem τ.e v)).toList.map Item.msg) : Packet M SB)).congr fun d => ?_
  rw [run_7]; rfl

lemma loc_box (hG : τ.Good) (r : ℕ) (hr : r < 15) (v : V) :
    Determined τ.inp τ.run (r + 8) v fun d => τ.run d (r + 8) v := by
  have := isLocal_box_seg hG hr v
  rwa [Nat.add_comm] at this

lemma loc_alg2 (hG : τ.Good) (k : ℕ) (hk : k < 6) (v : V) :
    Determined τ.inp τ.run (k + 23) v fun d => τ.run d (k + 23) v := by
  have := Alg3.isLocal_alg3 τ.e (t0 := 23) (A := τ.A2) hS2 (A2_known hG) (hyp2 hG) hk v
  rwa [Nat.add_comm] at this

lemma B2_known (v : V) : Determined τ.inp τ.run 29 v fun d => τ.B2 d v :=
  Alg3.Bk_known τ.e (t0 := 23) (A := τ.A2) hS2 v

lemma loc_29 (v : V) : Determined τ.inp τ.run 29 v fun d => τ.run d 29 v :=
  ((B2_known v).map fun H => fun _ => (ofList [Item.num H.card] : Packet M SB)).congr
    fun d => by rw [run_29]; rfl

lemma L_known (w : V) : Determined τ.inp τ.run 30 w fun d => τ.L d :=
  ((determined_recv (r := 29) (by norm_num) w).map fun f => fun v => numOfL (f v)).congr
    fun d => by
      funext v
      show τ.L d v = numOfL (τ.run d 29 v w)
      rw [run_29, P29, numOfL_num (by simp [SB])]
      rfl

lemma loc_30 (v : V) : Determined τ.inp τ.run 30 v fun d => τ.run d 30 v := by
  intro d d' hv
  have h1 := ((B2_known v).mono (by norm_num)) d d' hv
  have h2 := (L_known v) d d' hv
  simp only at h1 h2
  show τ.run d 30 v = τ.run d' 30 v
  rw [run_30, run_30]
  have h3 : τ.tgF d v = τ.tgF d' v := by
    funext x; unfold tgF; rw [h1, h2]
  funext c
  unfold P30 viaF fRp
  rw [h1, h2, h3]

lemma loc_31 (v : V) : Determined τ.inp τ.run 31 v fun d => τ.run d 31 v :=
  ((determined_recv (r := 30) (by norm_num) v).map
    fun f => fun w => (rr2 (enc τ.e) f w : Packet M SB)).congr fun d => by
      rw [run_31]
      funext w
      show τ.P31 d v w = rr2 (enc τ.e) (fun u => τ.run d 30 u v) w
      rw [run_30]
      rfl

lemma t_cases {t : ℕ} (ht : t < 32) :
    t = 0 ∨ (∃ k, k < 6 ∧ t = k + 1) ∨ t = 7 ∨ (∃ r, r < 15 ∧ t = r + 8) ∨
      (∃ k, k < 6 ∧ t = k + 23) ∨ t = 29 ∨ t = 30 ∨ t = 31 := by
  rcases Nat.lt_or_ge t 1 with h | h
  · left; omega
  rcases Nat.lt_or_ge t 7 with h' | h'
  · exact Or.inr (Or.inl ⟨t - 1, by omega, by omega⟩)
  rcases Nat.lt_or_ge t 8 with h'' | h''
  · right; right; left; omega
  rcases Nat.lt_or_ge t 23 with h3 | h3
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t - 8, by omega, by omega⟩)))
  rcases Nat.lt_or_ge t 29 with h4 | h4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t - 23, by omega, by omega⟩))))
  right; right; right; right; right; omega

theorem run_isLocal (hG : τ.Good) : IsLocal τ.inp τ.run := by
  intro t v
  rcases Nat.lt_or_ge t 32 with ht | ht
  · rcases t_cases ht with rfl | ⟨k, hk, rfl⟩ | rfl | ⟨r, hr, rfl⟩ | ⟨k, hk, rfl⟩ | rfl | rfl | rfl
    · exact loc_0 v
    · exact loc_alg1 hG k hk v
    · exact loc_7 hG v
    · exact loc_box hG r hr v
    · exact loc_alg2 hG k hk v
    · exact loc_29 v
    · exact loc_30 v
    · exact loc_31 v
  · refine (determined_const t v (fun _ => (ofList [] : Packet M SB))).congr fun d => ?_
    simp only [run]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ### Validity and numbers -/

lemma valid_alg1 (hG : τ.Good) {d : I} (k : ℕ) (hk : k < 6) {u v : V} {i : Fin SB} {x : M}
    (h : τ.run d (k + 1) u v i = some (Item.msg x)) : HoldsS τ.inp τ.run d (k + 1) u x := by
  rw [Nat.add_comm] at h ⊢
  exact Alg3.valid_alg3 τ.e hS1' (hyp1 hG) (fun d v x hx => A1_holds hx) hk h

lemma valid_alg2 (hG : τ.Good) {d : I} (k : ℕ) (hk : k < 6) {u v : V} {i : Fin SB} {x : M}
    (h : τ.run d (k + 23) u v i = some (Item.msg x)) : HoldsS τ.inp τ.run d (k + 23) u x := by
  rw [Nat.add_comm] at h ⊢
  exact Alg3.valid_alg3 τ.e hS2 (hyp2 hG) (fun d v x hx => A2_holds hG hx) hk h

lemma valid_boxL (hG : τ.Good) {d : I} (r : ℕ) (hr : r < 15) {u v : V} {i : Fin SB} {x : M}
    (h : τ.run d (r + 8) u v i = some (Item.msg x)) : HoldsS τ.inp τ.run d (r + 8) u x := by
  rw [Nat.add_comm] at h ⊢
  exact valid_box_seg hG hr h

theorem run_valid (hG : τ.Good) (d : I) (t : ℕ) (ht : t < 32) (u v : V) (i : Fin SB) (x : M)
    (h : τ.run d t u v i = some (Item.msg x)) : HoldsS τ.inp τ.run d t u x := by
  have hm : x ∈ msgsOf (τ.run d t u v) := mem_msgsOf.2 ⟨i, h⟩
  rcases t_cases ht with rfl | ⟨k, hk, rfl⟩ | rfl | ⟨r, hr, rfl⟩ | ⟨k, hk, rfl⟩ | rfl | rfl | rfl
  · rw [run_0, P0] at hm
    split_ifs at hm
    · have := msgsOf_ofList_sub hm
      simp only [List.mem_map, Option.mem_toList, Item.msg.injEq, exists_eq_right] at this
      exact Or.inl (smp_sub (smpAt_eq_some_iff.1 this).1)
    · rw [msgsOf_ofList_nil] at hm; simp at hm
  · exact valid_alg1 hG k hk h
  · rw [run_7, P7] at hm
    have := msgsOf_ofList_sub hm
    simp only [List.mem_map, mem_toList, Item.msg.injEq, exists_eq_right] at this
    exact Alg3.holds_Bk τ.e (t0 := 1) (A := τ.A1) hS1' (mem_filter.1 this).1
  · exact valid_boxL hG r hr h
  · exact valid_alg2 hG k hk h
  · rw [run_29] at hm
    have h0 : msgsOf (τ.P29 d u v) = ∅ := msgsOf_ofList_num _
    rw [h0] at hm
    exact absurd hm (notMem_empty x)
  · rw [run_30, P30] at hm
    exact (Alg3.holds_Bk τ.e (t0 := 23) (A := τ.A2) hS2 (msgsOf_rr1_sub hm)).mono (by norm_num)
  · rw [run_31, P31] at hm
    obtain ⟨u', hu'⟩ := fwd_sub (msgsOf_rr2_sub hm)
    refine holdsS_of_mem_received (r := 30) ?_ (by norm_num)
    show x ∈ rcvd (τ.run d 30) u
    rw [run_30]
    exact mem_rcvd.2 ⟨u', hu'⟩

lemma s_cube_bound (k : ℕ) (hk : k ≤ 6 * (s * s)) : k ≤ 8 * (s * s * s) := by
  have := one_le_s (s := s)
  nlinarith

theorem run_num_le (hG : τ.Good) (d : I) (t : ℕ) (ht : t < 32) (u v : V) (i : Fin SB) (k : ℕ)
    (h : τ.run d t u v i = some (Item.num k)) : k ≤ 8 * (s * s * s) := by
  have hs := one_le_s (s := s)
  rcases t_cases ht with rfl | ⟨k', hk, rfl⟩ | rfl | ⟨r, hr, rfl⟩ | ⟨k', hk, rfl⟩ | rfl | rfl | rfl
  · rw [run_0, P0] at h
    split_ifs at h
    · have := ofList_eq_some h; simp at this
    · have := ofList_eq_some h; simp at this
  · rw [Nat.add_comm] at h
    exact s_cube_bound _ (le_trans (Alg3.nums_alg3 τ.e (t0 := 1) (A := τ.A1) hS1' (hyp1 hG)
      hk h) (by nlinarith))
  · rw [run_7, P7] at h
    have := ofList_eq_some h; simp at this
  · rw [Nat.add_comm] at h
    exact le_trans (nums_box_seg hG hr h) (by nlinarith)
  · rw [Nat.add_comm] at h
    exact s_cube_bound _ (le_trans (Alg3.nums_alg3 τ.e (t0 := 23) (A := τ.A2) hS2 (hyp2 hG)
      hk h) (by nlinarith))
  · rw [run_29, P29] at h
    have := ofList_eq_some h
    simp only [List.mem_cons, Item.num.injEq, List.mem_nil_iff, or_false] at this
    subst this
    exact s_cube_bound _ (le_of_lt (Alg3.card_Bk_lt τ.e (hyp2 hG) d u))
  · rw [run_30, P30] at h
    obtain ⟨x, rfl⟩ := nums_rr1 h
    exact s_cube_bound _ (le_trans (enc_lt τ.e _).le (by nlinarith))
  · rw [run_31, P31] at h
    exact (nums_rr2 h).elim

/-- **Theorem 4.5, square case** (with the fixes in `differencies.md`): on `s²` nodes holding at
most `s²` distinct keys each, the 32-round run is implementable, uses packets of `SB` slots and
numbers `≤ 8 s³`, forwards only held keys, and delivers every key to `out` of its global rank. -/
theorem sort_correct (hG : τ.Good) :
    IsLocal τ.inp τ.run ∧
      Routes τ.inp (fun d x => τ.out (rk (τ.U d) x)) τ.run 32 (8 * (s * s * s)) :=
  ⟨run_isLocal hG, ⟨fun d t ht u v i k h => run_num_le hG d t ht u v i k h,
    fun d t ht u v i x h => run_valid hG d t ht u v i x h,
    fun d v x hx => holdsS_of_mem_received (r := 31) (by
      show x ∈ rcvd (τ.run d 31) _
      rw [run_31]
      exact final hG (mem_biUnion.2 ⟨v, mem_univ _, hx⟩)) (by norm_num)⟩⟩

end SortSetup

end CongestedCliqueRouting
