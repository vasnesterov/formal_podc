import Papers.PODC2013.CongestedCliqueRouting.SquarePhaseA

/-!
# Correctness of Phases B, C, D (Steps 3–5 of Algorithm 1: Corollary 3.5, the inter-group
round, Corollary 3.4)
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

section C33rcvd

variable {V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] {s : ℕ}

/-- Messages received in round 2 of Corollary 3.3. -/
lemma mem_rcvd_c33 (e : V ≃ Fin s × Fin s) {rel : V → V → Option (M × ℕ × ℕ)}
    (hu : C33Unique e rel) {w : V} {m : M} :
    m ∈ rcvd (fun c w' => c33b e (fun u => c33a (rel u c)) w') w ↔
      ∃ u c k, grp e u = grp e w ∧ rel u c = some (m, (mem e w : ℕ), k) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := mem_rcvd.1 h
    rcases c33b_cases e (fun u => c33a (rel u c)) w with h0 | ⟨m', k, hmk, h1⟩
    · rw [h0] at hc; simp at hc
    · rw [h1, msgsOf_pMsgNum, mem_singleton] at hc
      subst hc
      simp only [cand, mem_biUnion, mem_filter, mem_univ, true_and, mem_parse3_c33a] at hmk
      obtain ⟨u, hu1, hu2⟩ := hmk
      exact ⟨u, c, k, hu1, hu2⟩
  · rintro ⟨u, c, k, hg, hr⟩
    refine mem_rcvd.2 ⟨c, ?_⟩
    rw [c33b_c33a_eq e hu hg hr]
    simp

end C33rcvd

namespace Setup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] [Nonempty V] {s : ℕ}
  [NeZero s] {σ : Setup I V M s}

/-! ### Phase B -/

lemma F_row (d : I) (a b : Fin s) : ∑ j, σ.F d a b j ≤ s * s := by
  unfold F c1
  rw [sum_cnt]
  exact card_HB_le d _

lemma F_col (hG : σ.Good) (d : I) (a j : Fin s) : ∑ b, σ.F d a b j ≤ s * s :=
  HB_col hG d a j

lemma Fp_spec (hG : σ.Good) (d : I) (a : Fin s) :
    (∀ b j, ∑ y, σ.Fp d a y b j = σ.F d a b j) ∧ (∀ y b, ∑ j, σ.Fp d a y b j ≤ s) ∧
      (∀ y j, ∑ b, σ.Fp d a y b j ≤ s) :=
  splitParts_spec (ι := Fin s) (by simpa using F_row d a) (by simpa using F_col hG d a)

lemma yB_le (hG : σ.Good) (d : I) (v : V) (j y : Fin s) :
    ((σ.HB d v).filter fun m => σ.dg m = j ∧ σ.yB d v m = y).card ≤
      σ.Fp d (grp σ.e v) y (mem σ.e v) j := by
  unfold yB
  refine assign_le (fun j => ?_) j y
  rw [(Fp_spec hG d _).1]
  simp [F, c1, cnt]

lemma R1_row (hG : σ.Good) (d : I) (a b : Fin s) : ∑ y, σ.R1 d a b y ≤ s * s := by
  unfold R1
  rw [sum_comm]
  simp only [(Fp_spec hG d a).1]
  exact F_row d a b

lemma R1_col (hG : σ.Good) (d : I) (a y : Fin s) : ∑ b, σ.R1 d a b y ≤ s * s := by
  unfold R1
  rw [sum_comm]
  calc ∑ j, ∑ b, σ.Fp d a y b j ≤ ∑ _j : Fin s, s := sum_le_sum fun j _ => (Fp_spec hG d a).2.2 y j
    _ = s * s := by simp

lemma R1p_spec (hG : σ.Good) (d : I) (a : Fin s) :
    (∀ b y, ∑ c, σ.R1p d a c b y = σ.R1 d a b y) ∧ (∀ c b, ∑ y, σ.R1p d a c b y ≤ 1) ∧
      (∀ c y, ∑ b, σ.R1p d a c b y ≤ 1) :=
  splitParts_spec (ι := V) (by simpa [card_V σ.e] using R1_row hG d a)
    (by simpa [card_V σ.e] using R1_col hG d a)

lemma yB_cap (hG : σ.Good) (d : I) (v : V) (y : Fin s) :
    ((σ.HB d v).filter fun m => σ.yB d v m = y).card ≤
      ∑ c, σ.R1p d (grp σ.e v) c (mem σ.e v) y := by
  rw [(R1p_spec hG d _).1, card_filter_eq_sum_fiber _ (σ.yB d v) σ.dg y]
  unfold R1
  refine sum_le_sum fun j _ => le_trans (le_of_eq ?_) (yB_le hG d v j y)
  congr 1
  exact filter_congr fun m _ => and_comm

lemma relB_some (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.HB d v) :
    ∃ c, σ.relB d v c = some (m, (σ.yB d v m : ℕ), 0) :=
  ⟨_, relayOf_some (yB_cap hG d v) (fun c => (R1p_spec hG d _).2.1 c _) hm⟩

lemma relB_spec (hG : σ.Good) (d : I) {v c : V} {m : M} {y k : ℕ}
    (h : σ.relB d v c = some (m, y, k)) :
    m ∈ σ.HB d v ∧ y = (σ.yB d v m : ℕ) ∧ k = 0 ∧
      1 ≤ σ.R1p d (grp σ.e v) c (mem σ.e v) (σ.yB d v m) :=
  relayOf_spec (yB_cap hG d v) h

lemma relB_unique (hG : σ.Good) (d : I) : C33Unique σ.e (σ.relB d) := by
  intro c u u' m m' y k k' hg h h'
  obtain ⟨-, hy, -, h1⟩ := relB_spec hG d h
  obtain ⟨-, hy', -, h1'⟩ := relB_spec hG d h'
  have hyy : σ.yB d u m = σ.yB d u' m' := Fin.ext (hy.symm.trans hy')
  rw [hyy, hg] at h1
  have := unique_of_sum_le_one ((R1p_spec hG d (grp σ.e u')).2.2 c _) h1 h1'
  rw [← node_grp_mem σ.e u, ← node_grp_mem σ.e u', hg, this]

lemma mem_HC (hG : σ.Good) (d : I) {w : V} {m : M} :
    m ∈ σ.HC d w ↔ ∃ u c k, grp σ.e u = grp σ.e w ∧
      σ.relB d u c = some (m, (mem σ.e w : ℕ), k) :=
  mem_rcvd_c33 σ.e (relB_unique hG d)

lemma HC_of_HB (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.HB d v) :
    m ∈ σ.HC d (node σ.e (grp σ.e v) (σ.yB d v m)) := by
  obtain ⟨c, hc⟩ := relB_some hG d hm
  rw [mem_HC hG]
  exact ⟨v, c, 0, by simp, by simpa using hc⟩

lemma HC_sub (hG : σ.Good) (d : I) {w : V} {m : M} (h : m ∈ σ.HC d w) :
    ∃ u, m ∈ σ.HB d u ∧ node σ.e (grp σ.e u) (σ.yB d u m) = w := by
  rw [mem_HC hG] at h
  obtain ⟨u, c, k, hg, hc⟩ := h
  obtain ⟨hm, hy, -, -⟩ := relB_spec hG d hc
  refine ⟨u, hm, ?_⟩
  rw [node_eq_iff]
  exact ⟨hg.symm, Fin.ext hy⟩

/-! ### Phase C -/

lemma HC_cap (hG : σ.Good) (d : I) (w : V) (k : ℕ) :
    ((σ.HC d w).filter fun m => (σ.dg m : ℕ) = k).card ≤ s := by
  have hsub : (σ.HC d w).filter (fun m => (σ.dg m : ℕ) = k) ⊆
      (univ.filter fun u => grp σ.e u = grp σ.e w).biUnion fun u =>
        (σ.HB d u).filter fun m => (σ.dg m : ℕ) = k ∧ σ.yB d u m = mem σ.e w := by
    intro m hm
    rw [mem_filter] at hm
    obtain ⟨u, hu, hw⟩ := HC_sub hG d hm.1
    rw [node_eq_iff] at hw
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨u, hw.1.symm, hu, hm.2, hw.2.symm⟩
  refine le_trans (card_le_card hsub) (le_trans card_biUnion_le ?_)
  rw [sum_group σ.e (fun u => ((σ.HB d u).filter fun m => (σ.dg m : ℕ) = k ∧
    σ.yB d u m = mem σ.e w).card)]
  by_cases hk : k < s
  · calc ∑ b, ((σ.HB d (node σ.e (grp σ.e w) b)).filter fun m => (σ.dg m : ℕ) = k ∧
            σ.yB d (node σ.e (grp σ.e w) b) m = mem σ.e w).card
        ≤ ∑ b, σ.Fp d (grp σ.e w) (mem σ.e w) b ⟨k, hk⟩ := by
          refine sum_le_sum fun b _ => ?_
          have := yB_le hG d (node σ.e (grp σ.e w) b) ⟨k, hk⟩ (mem σ.e w)
          simp only [grp_node, mem_node] at this
          refine le_trans (le_of_eq (congrArg card (filter_congr fun m _ => ?_))) this
          simp [Fin.ext_iff]
      _ ≤ s := (Fp_spec hG d _).2.2 _ _
  · refine le_trans (le_of_eq ?_) (Nat.zero_le s)
    refine sum_eq_zero fun b _ => ?_
    rw [card_eq_zero, filter_eq_empty_iff]
    intro m _ h
    have := (σ.dg m).isLt
    omega

lemma mem_HD (hG : σ.Good) (d : I) {z : V} {m : M} :
    m ∈ σ.HD d z ↔ ∃ w, m ∈ σ.HC d w ∧ σ.dg m = grp σ.e z ∧
      slot (σ.HC d w) (fun m => (σ.dg m : ℕ)) m = mem σ.e z := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := mem_rcvd.1 h
    obtain ⟨m', hp, rfl, hk, hs⟩ := msgsOf_scatter σ.e hw
    exact ⟨w, hp, Fin.ext hk, hs⟩
  · rintro ⟨w, hp, hk, hs⟩
    refine mem_rcvd.2 ⟨w, ?_⟩
    have hlt : (σ.dg m : ℕ) < s := (σ.dg m).isLt
    have := scatter_eq σ.e (toM := id) (HC_cap hG d w) hp hlt
    have hz : node σ.e ⟨(σ.dg m : ℕ), hlt⟩ (slot (σ.HC d w) (fun m => (σ.dg m : ℕ)) m) = z := by
      rw [node_eq_iff]
      exact ⟨Fin.ext (by simp [hk]), hs.symm⟩
    rw [hz] at this
    show m ∈ msgsOf (σ.P10 d w z)
    unfold P10
    rw [this]
    simp

lemma HD_of_HC (hG : σ.Good) (d : I) {w : V} {m : M} (hm : m ∈ σ.HC d w) :
    m ∈ σ.HD d (node σ.e (σ.dg m) (slot (σ.HC d w) (fun m => (σ.dg m : ℕ)) m)) := by
  rw [mem_HD hG]
  exact ⟨w, hm, by simp, by simp⟩

lemma HD_sub (hG : σ.Good) (d : I) {z : V} {m : M} (h : m ∈ σ.HD d z) :
    ∃ w, m ∈ σ.HC d w ∧ node σ.e (σ.dg m) (slot (σ.HC d w) (fun m => (σ.dg m : ℕ)) m) = z := by
  rw [mem_HD hG] at h
  obtain ⟨w, hp, hk, hs⟩ := h
  exact ⟨w, hp, by rw [node_eq_iff]; exact ⟨hk.symm, hs.symm⟩⟩

lemma HD_dg (hG : σ.Good) (d : I) {z : V} {m : M} (h : m ∈ σ.HD d z) :
    σ.dg m = grp σ.e z := by
  rw [mem_HD hG] at h
  obtain ⟨w, -, hk, -⟩ := h
  exact hk

/-! ### Phase D -/

lemma card_HD_le (d : I) (z : V) : (σ.HD d z).card ≤ s * s := by
  rw [← card_V σ.e]
  exact card_rcvd_le fun w => card_msgsOf_scatter_le σ.e _ _ _ _

lemma card_HC_le (d : I) (z : V) : (σ.HC d z).card ≤ s * s := by
  rw [← card_V σ.e]
  exact card_rcvd_le fun w => card_msgsOf_c33b_le σ.e _ _

lemma HD_load (hG : σ.Good) (d : I) (w0 : V) :
    ∑ z, ((σ.HD d z).filter fun m => σ.dst m = w0).card ≤ s * s := by
  calc ∑ z, ((σ.HD d z).filter fun m => σ.dst m = w0).card
      ≤ ∑ w, ((σ.HC d w).filter fun m => σ.dst m = w0).card :=
        sum_move (H := σ.HC d) (f := fun w m => node σ.e (σ.dg m)
          (slot (σ.HC d w) (fun m => (σ.dg m : ℕ)) m)) (fun _ m => σ.dst m = w0)
          (fun z m hm => HD_sub hG d hm)
    _ ≤ ∑ u, ((σ.HB d u).filter fun m => σ.dst m = w0).card :=
        sum_move (H := σ.HB d) (f := fun u m => node σ.e (grp σ.e u) (σ.yB d u m))
          (fun _ m => σ.dst m = w0) (fun z m hm => HC_sub hG d hm)
    _ ≤ ∑ v, ((σ.inp d v).filter fun m => σ.dst m = w0).card :=
        sum_move (H := σ.inp d) (f := σ.fA d) (fun _ m => σ.dst m = w0)
          (fun z m hm => HB_sub hG d hm)
    _ ≤ s * s := hG.load_le d w0

lemma G3_row (d : I) (a b : Fin s) : ∑ y, σ.G3 d a b y ≤ s * s := by
  unfold G3 c3
  rw [sum_cnt]
  exact card_HD_le d _

lemma G3_col (hG : σ.Good) (d : I) (a y : Fin s) : ∑ b, σ.G3 d a b y ≤ s * s := by
  have h1 : ∀ b, σ.G3 d a b y ≤
      ((σ.HD d (node σ.e a b)).filter fun m => σ.dst m = node σ.e a y).card := by
    intro b
    unfold G3 c3 cnt
    refine card_le_card fun m hm => ?_
    rw [mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    rw [eq_node_iff]
    have := HD_dg hG d hm.1
    simp only [grp_node] at this
    exact ⟨this, hm.2⟩
  refine le_trans (sum_le_sum fun b _ => h1 b) (le_trans ?_ (HD_load hG d (node σ.e a y)))
  rw [sum_V σ.e (fun z => ((σ.HD d z).filter fun m => σ.dst m = node σ.e a y).card)]
  exact single_le_sum (f := fun a' => ∑ b, ((σ.HD d (node σ.e a' b)).filter
    fun m => σ.dst m = node σ.e a y).card) (fun _ _ => Nat.zero_le _) (mem_univ a)

lemma G3p_spec (hG : σ.Good) (d : I) (a : Fin s) :
    (∀ b y, ∑ c, σ.G3p d a c b y = σ.G3 d a b y) ∧ (∀ c b, ∑ y, σ.G3p d a c b y ≤ 1) ∧
      (∀ c y, ∑ b, σ.G3p d a c b y ≤ 1) :=
  splitParts_spec (ι := V) (by simpa [card_V σ.e] using G3_row d a)
    (by simpa [card_V σ.e] using G3_col hG d a)

lemma dm_cap (hG : σ.Good) (d : I) (v : V) (y : Fin s) :
    ((σ.HD d v).filter fun m => σ.dm m = y).card ≤
      ∑ c, σ.G3p d (grp σ.e v) c (mem σ.e v) y := by
  rw [(G3p_spec hG d _).1]
  simp [G3, c3, cnt]

lemma relD_some (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.HD d v) :
    ∃ c, σ.relD d v c = some (m, (σ.dm m : ℕ), 0) :=
  ⟨_, relayOf_some (dm_cap hG d v) (fun c => (G3p_spec hG d _).2.1 c _) hm⟩

lemma relD_spec (hG : σ.Good) (d : I) {v c : V} {m : M} {y k : ℕ}
    (h : σ.relD d v c = some (m, y, k)) :
    m ∈ σ.HD d v ∧ y = (σ.dm m : ℕ) ∧ k = 0 ∧
      1 ≤ σ.G3p d (grp σ.e v) c (mem σ.e v) (σ.dm m) :=
  relayOf_spec (dm_cap hG d v) h

lemma relD_unique (hG : σ.Good) (d : I) : C33Unique σ.e (σ.relD d) := by
  intro c u u' m m' y k k' hg h h'
  obtain ⟨-, hy, -, h1⟩ := relD_spec hG d h
  obtain ⟨-, hy', -, h1'⟩ := relD_spec hG d h'
  have hyy : σ.dm m = σ.dm m' := Fin.ext (hy.symm.trans hy')
  rw [hyy, hg] at h1
  have := unique_of_sum_le_one ((G3p_spec hG d (grp σ.e u')).2.2 c _) h1 h1'
  rw [← node_grp_mem σ.e u, ← node_grp_mem σ.e u', hg, this]

lemma mem_HE (hG : σ.Good) (d : I) {w : V} {m : M} :
    m ∈ σ.HE d w ↔ ∃ u c k, grp σ.e u = grp σ.e w ∧
      σ.relD d u c = some (m, (mem σ.e w : ℕ), k) :=
  mem_rcvd_c33 σ.e (relD_unique hG d)

lemma HE_of_HD (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.HD d v) :
    m ∈ σ.HE d (σ.dst m) := by
  obtain ⟨c, hc⟩ := relD_some hG d hm
  rw [mem_HE hG]
  have hdg := HD_dg hG d hm
  refine ⟨v, c, 0, hdg.symm, ?_⟩
  simpa [dm] using hc

/-- Every message reaches its destination after the 15 rounds. -/
lemma HE_of_inp (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.inp d v) :
    m ∈ σ.HE d (σ.dst m) :=
  HE_of_HD hG d (HD_of_HC hG d (HC_of_HB hG d (HB_of_inp hG d hm)))

end Setup

end CongestedCliqueRouting
