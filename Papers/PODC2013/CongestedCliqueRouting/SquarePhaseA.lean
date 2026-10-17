import Papers.PODC2013.CongestedCliqueRouting.SquareDefs

/-!
# Correctness of Phase A (Step 2 of Algorithm 1, i.e. Algorithm 2 / Lemma 3.6)
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V] {s : ℕ}

lemma node_eq_iff (e : V ≃ Fin s × Fin s) {v : V} {a b : Fin s} :
    node e a b = v ↔ grp e v = a ∧ mem e v = b := by
  rw [eq_comm, eq_node_iff]

lemma unique_of_sum_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ}
    (h : ∑ i, f i ≤ 1) {i i' : ι} (hi : 1 ≤ f i) (hi' : 1 ≤ f i') : i = i' := by
  by_contra hne
  have : f i + f i' ≤ ∑ x, f x := by
    rw [← sum_pair hne]
    exact sum_le_sum_of_subset (subset_univ _)
  omega

lemma sum_group (e : V ≃ Fin s × Fin s) (f : V → ℕ) (a : Fin s) :
    ∑ u ∈ univ.filter (fun u => grp e u = a), f u = ∑ b, f (node e a b) := by
  rw [sum_filter, sum_V e]
  simp only [grp_node]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma sum_cnt {M κ : Type*} [Fintype κ] [DecidableEq κ] (H : Finset M) (f : M → κ) :
    ∑ j, cnt H f j = H.card := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  rfl

/-- Messages move from holders `H u` to new holders `H' z`, `u` sending `m` to `f u m`. Then
counts over the new holders are bounded by counts over the old holders. -/
lemma sum_move {α : Type*} [DecidableEq α] {H H' : V → Finset α} {f : V → α → V}
    (P : V → α → Prop) [∀ z m, Decidable (P z m)]
    (hsub : ∀ z m, m ∈ H' z → ∃ u, m ∈ H u ∧ f u m = z) :
    ∑ z, ((H' z).filter (P z)).card ≤ ∑ u, ((H u).filter fun m => P (f u m) m).card := by
  calc ∑ z, ((H' z).filter (P z)).card
      ≤ ∑ z, ∑ u, ((H u).filter fun m => P (f u m) m ∧ f u m = z).card := by
        refine sum_le_sum fun z _ => ?_
        refine le_trans (card_le_card ?_) card_biUnion_le
        intro m hm
        rw [mem_filter] at hm
        obtain ⟨u, hu, rfl⟩ := hsub z m hm.1
        simp only [mem_biUnion, mem_univ, true_and, mem_filter]
        exact ⟨u, hu, hm.2, rfl⟩
    _ = ∑ u, ∑ z, ((H u).filter fun m => P (f u m) m ∧ f u m = z).card := sum_comm
    _ = ∑ u, ((H u).filter fun m => P (f u m) m).card := by
        refine sum_congr rfl fun u _ => ?_
        rw [eq_comm, card_eq_sum_card_fiberwise (f := f u) (t := univ)
          (fun _ _ => mem_coe.2 (mem_univ _))]
        refine sum_congr rfl fun z _ => ?_
        rw [filter_filter]

end Helpers

namespace Setup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] [Nonempty V] {s : ℕ}
  [NeZero s] (σ : Setup I V M s)

lemma card_fin_mul (D : ℕ) : Fintype.card (Fin s) * D = s * D := by simp

lemma cnt_dg_eq (H : Finset M) (j : Fin s) :
    cnt H σ.dg j = ∑ y, (H.filter fun m => σ.dst m = node σ.e j y).card := by
  unfold cnt
  rw [card_filter_eq_sum_fiber H σ.dg σ.dm j]
  refine sum_congr rfl fun y _ => ?_
  congr 1
  refine filter_congr fun m _ => ?_
  rw [eq_node_iff]
  rfl

lemma sum_c0 (d : I) (v : V) : ∑ j, σ.c0 d v j = (σ.inp d v).card := sum_cnt _ _

variable {σ}

lemma T_row (hG : σ.Good) (d : I) (a : Fin s) : ∑ j, σ.T d a j ≤ s * (s * s) := by
  unfold T C
  rw [sum_comm]
  calc ∑ b, ∑ j, σ.c0 d (node σ.e a b) j = ∑ b, (σ.inp d (node σ.e a b)).card := by
        simp [sum_c0]
    _ ≤ ∑ _b : Fin s, s * s := sum_le_sum fun b _ => hG.card_le d _
    _ = s * (s * s) := by simp

lemma T_col (hG : σ.Good) (d : I) (j : Fin s) : ∑ a, σ.T d a j ≤ s * (s * s) := by
  unfold T C
  rw [← sum_V σ.e (fun v => σ.c0 d v j)]
  unfold c0
  simp only [cnt_dg_eq]
  rw [sum_comm]
  calc ∑ y, ∑ v, ((σ.inp d v).filter fun m => σ.dst m = node σ.e j y).card
      ≤ ∑ _y : Fin s, s * s := sum_le_sum fun y _ => hG.load_le d _
    _ = s * (s * s) := by simp

lemma Tp_spec (hG : σ.Good) (d : I) :
    (∀ a j, ∑ x, σ.Tp d x a j = σ.T d a j) ∧ (∀ x a, ∑ j, σ.Tp d x a j ≤ s * s) ∧
      (∀ x j, ∑ a, σ.Tp d x a j ≤ s * s) :=
  splitParts_spec (ι := Fin s) (by simpa using T_row hG d) (by simpa using T_col hG d)

lemma q_spec (hG : σ.Good) (d : I) (a j : Fin s) :
    (∀ b, ∑ x, σ.q d a j b x = σ.C d a b j) ∧ (∀ x, ∑ b, σ.q d a j b x = σ.Tp d x a j) :=
  transportOf_spec (by rw [(Tp_spec hG d).1 a j]; rfl)

lemma xA_count (hG : σ.Good) (d : I) (v : V) (j x : Fin s) :
    ((σ.inp d v).filter fun m => σ.dg m = j ∧ σ.xA d v m = x).card =
      σ.q d (grp σ.e v) j (mem σ.e v) x := by
  unfold xA
  refine assign_eq (fun j => ?_) j x
  rw [(q_spec hG d _ j).1]
  simp [C, c0, cnt]

lemma E_eq (hG : σ.Good) (d : I) (v : V) (x : Fin s) :
    σ.E d (grp σ.e v) (mem σ.e v) x = ((σ.inp d v).filter fun m => σ.xA d v m = x).card := by
  rw [card_filter_eq_sum_fiber _ (σ.xA d v) σ.dg x]
  unfold E
  refine sum_congr rfl fun j _ => ?_
  rw [← xA_count hG d v j x]
  congr 1
  exact filter_congr fun m _ => and_comm

lemma E_row (hG : σ.Good) (d : I) (a b : Fin s) : ∑ x, σ.E d a b x ≤ s * s := by
  unfold E
  rw [sum_comm]
  simp only [(q_spec hG d a _).1]
  have := sum_c0 σ d (node σ.e a b)
  unfold C
  rw [this]
  exact hG.card_le d _

lemma E_col (hG : σ.Good) (d : I) (a x : Fin s) : ∑ b, σ.E d a b x ≤ s * s := by
  unfold E
  rw [sum_comm]
  simp only [(q_spec hG d a _).2]
  exact (Tp_spec hG d).2.1 x a

lemma Ep_spec (hG : σ.Good) (d : I) (a : Fin s) :
    (∀ b x, ∑ y, σ.Ep d a y b x = σ.E d a b x) ∧ (∀ y b, ∑ x, σ.Ep d a y b x ≤ s) ∧
      (∀ y x, ∑ b, σ.Ep d a y b x ≤ s) :=
  splitParts_spec (ι := Fin s) (by simpa using E_row hG d a) (by simpa using E_col hG d a)

lemma yA_le (hG : σ.Good) (d : I) (v : V) (x y : Fin s) :
    ((σ.inp d v).filter fun m => σ.xA d v m = x ∧ σ.yA d v m = y).card ≤
      σ.Ep d (grp σ.e v) y (mem σ.e v) x := by
  unfold yA
  refine assign_le (fun x => ?_) x y
  rw [(Ep_spec hG d _).1, E_eq hG]

lemma R_row (hG : σ.Good) (d : I) (a b : Fin s) : ∑ y, σ.R d a b y ≤ s * s := by
  unfold R
  rw [sum_comm]
  simp only [(Ep_spec hG d a).1]
  exact E_row hG d a b

lemma R_col (hG : σ.Good) (d : I) (a y : Fin s) : ∑ b, σ.R d a b y ≤ s * s := by
  unfold R
  rw [sum_comm]
  calc ∑ x, ∑ b, σ.Ep d a y b x ≤ ∑ _x : Fin s, s := sum_le_sum fun x _ => (Ep_spec hG d a).2.2 y x
    _ = s * s := by simp

lemma Rp_spec (hG : σ.Good) (d : I) (a : Fin s) :
    (∀ b y, ∑ c, σ.Rp d a c b y = σ.R d a b y) ∧ (∀ c b, ∑ y, σ.Rp d a c b y ≤ 1) ∧
      (∀ c y, ∑ b, σ.Rp d a c b y ≤ 1) :=
  splitParts_spec (ι := V) (by simpa [card_V σ.e] using R_row hG d a)
    (by simpa [card_V σ.e] using R_col hG d a)

lemma yA_cap (hG : σ.Good) (d : I) (v : V) (y : Fin s) :
    ((σ.inp d v).filter fun m => σ.yA d v m = y).card ≤
      ∑ c, σ.Rp d (grp σ.e v) c (mem σ.e v) y := by
  rw [(Rp_spec hG d _).1, card_filter_eq_sum_fiber _ (σ.yA d v) (σ.xA d v) y]
  unfold R
  refine sum_le_sum fun x _ => le_trans (le_of_eq ?_) (yA_le hG d v x y)
  congr 1
  exact filter_congr fun m _ => and_comm

lemma relA_some (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.inp d v) :
    ∃ c, σ.relA d v c = some (m, (σ.yA d v m : ℕ), (σ.xA d v m : ℕ)) :=
  ⟨_, relayOf_some (yA_cap hG d v) (fun c => (Rp_spec hG d _).2.1 c _) hm⟩

lemma relA_spec (hG : σ.Good) (d : I) {v c : V} {m : M} {y k : ℕ}
    (h : σ.relA d v c = some (m, y, k)) :
    m ∈ σ.inp d v ∧ y = (σ.yA d v m : ℕ) ∧ k = (σ.xA d v m : ℕ) ∧
      1 ≤ σ.Rp d (grp σ.e v) c (mem σ.e v) (σ.yA d v m) :=
  relayOf_spec (yA_cap hG d v) h

lemma relA_unique (hG : σ.Good) (d : I) : C33Unique σ.e (σ.relA d) := by
  intro c u u' m m' y k k' hg h h'
  obtain ⟨-, hy, -, h1⟩ := relA_spec hG d h
  obtain ⟨-, hy', -, h1'⟩ := relA_spec hG d h'
  have hyy : σ.yA d u m = σ.yA d u' m' := Fin.ext (hy.symm.trans hy')
  rw [hyy, hg] at h1
  have := unique_of_sum_le_one ((Rp_spec hG d (grp σ.e u')).2.2 c _) h1 h1'
  rw [← node_grp_mem σ.e u, ← node_grp_mem σ.e u', hg, this]

lemma mem_TA (hG : σ.Good) (d : I) {w : V} {m : M} {k : ℕ} :
    (m, k) ∈ σ.TA d w ↔ ∃ u c, grp σ.e u = grp σ.e w ∧ σ.relA d u c = some (m, (mem σ.e w : ℕ), k) :=
  mem_tagged_c33 σ.e (relA_unique hG d)

lemma TA_of_inp (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.inp d v) :
    (m, (σ.xA d v m : ℕ)) ∈ σ.TA d (node σ.e (grp σ.e v) (σ.yA d v m)) := by
  obtain ⟨c, hc⟩ := relA_some hG d hm
  rw [mem_TA hG]
  exact ⟨v, c, by simp, by simpa using hc⟩

lemma inp_of_TA (hG : σ.Good) (d : I) {w : V} {m : M} {k : ℕ} (h : (m, k) ∈ σ.TA d w) :
    ∃ u, grp σ.e u = grp σ.e w ∧ m ∈ σ.inp d u ∧ σ.yA d u m = mem σ.e w ∧
      k = (σ.xA d u m : ℕ) := by
  rw [mem_TA hG] at h
  obtain ⟨u, c, hg, hc⟩ := h
  obtain ⟨hm, hy, hk, -⟩ := relA_spec hG d hc
  exact ⟨u, hg, hm, Fin.ext hy.symm, hk⟩

lemma TA_cap (hG : σ.Good) (d : I) (w : V) (k : ℕ) :
    ((σ.TA d w).filter fun p => p.2 = k).card ≤ s := by
  have hsub : (σ.TA d w).filter (fun p => p.2 = k) ⊆
      (univ.filter fun u => grp σ.e u = grp σ.e w).biUnion fun u =>
        ((σ.inp d u).filter fun m => (σ.xA d u m : ℕ) = k ∧ σ.yA d u m = mem σ.e w).image
          fun m => (m, k) := by
    rintro ⟨m, k'⟩ hp
    rw [mem_filter] at hp
    obtain ⟨hp, rfl⟩ := hp
    obtain ⟨u, hg, hm, hy, hk⟩ := inp_of_TA hG d hp
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
    refine ⟨u, hg, m, ⟨hm, hk.symm, hy⟩, ?_⟩
    simp
  refine le_trans (card_le_card hsub) (le_trans card_biUnion_le ?_)
  rw [sum_group σ.e (fun u => (((σ.inp d u).filter fun m => (σ.xA d u m : ℕ) = k ∧
    σ.yA d u m = mem σ.e w).image fun m => (m, k)).card)]
  by_cases hk : k < s
  · calc ∑ b, (((σ.inp d (node σ.e (grp σ.e w) b)).filter fun m =>
            (σ.xA d (node σ.e (grp σ.e w) b) m : ℕ) = k ∧
              σ.yA d (node σ.e (grp σ.e w) b) m = mem σ.e w).image fun m => (m, k)).card
        ≤ ∑ b, σ.Ep d (grp σ.e w) (mem σ.e w) b ⟨k, hk⟩ := by
          refine sum_le_sum fun b _ => le_trans card_image_le ?_
          have := yA_le hG d (node σ.e (grp σ.e w) b) ⟨k, hk⟩ (mem σ.e w)
          simp only [grp_node, mem_node] at this
          refine le_trans (le_of_eq (congrArg card (filter_congr fun m _ => ?_))) this
          simp [Fin.ext_iff]
      _ ≤ s := (Ep_spec hG d _).2.2 _ _
  · refine le_trans (le_of_eq ?_) (Nat.zero_le s)
    refine sum_eq_zero fun b _ => ?_
    rw [card_eq_zero, image_eq_empty, filter_eq_empty_iff]
    intro m _ h
    have := (σ.xA d (node σ.e (grp σ.e w) b) m).isLt
    omega

/-- Where a message of `v` is after Phase A. -/
noncomputable def fA (d : I) (v : V) (m : M) : V :=
  node σ.e (σ.xA d v m)
    (slot (σ.TA d (node σ.e (grp σ.e v) (σ.yA d v m))) Prod.snd (m, (σ.xA d v m : ℕ)))

lemma mem_HB (hG : σ.Good) (d : I) {z : V} {m : M} :
    m ∈ σ.HB d z ↔ ∃ w k, (m, k) ∈ σ.TA d w ∧ k = (grp σ.e z : ℕ) ∧
      slot (σ.TA d w) Prod.snd (m, k) = mem σ.e z := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := mem_rcvd.1 h
    obtain ⟨⟨m', k⟩, hp, rfl, hk, hs⟩ := msgsOf_scatter σ.e hw
    exact ⟨w, k, hp, hk, hs⟩
  · rintro ⟨w, k, hp, hk, hs⟩
    refine mem_rcvd.2 ⟨w, ?_⟩
    have hlt : (m, k).2 < s := by rw [hk]; exact (grp σ.e z).isLt
    have := scatter_eq σ.e (toM := Prod.fst) (TA_cap hG d w) hp hlt
    have hz : node σ.e ⟨(m, k).2, hlt⟩ (slot (σ.TA d w) Prod.snd (m, k)) = z := by
      rw [node_eq_iff]
      exact ⟨Fin.ext hk.symm, hs.symm⟩
    rw [hz] at this
    show m ∈ msgsOf (σ.P5 d w z)
    unfold P5
    rw [this]
    simp

lemma HB_of_inp (hG : σ.Good) (d : I) {v : V} {m : M} (hm : m ∈ σ.inp d v) :
    m ∈ σ.HB d (σ.fA d v m) := by
  rw [mem_HB hG]
  exact ⟨_, _, TA_of_inp hG d hm, by simp [fA], by simp [fA]⟩

lemma HB_sub (hG : σ.Good) (d : I) {z : V} {m : M} (h : m ∈ σ.HB d z) :
    ∃ v, m ∈ σ.inp d v ∧ σ.fA d v m = z := by
  rw [mem_HB hG] at h
  obtain ⟨w, k, hp, hk, hs⟩ := h
  obtain ⟨u, hg, hm, hy, rfl⟩ := inp_of_TA hG d hp
  refine ⟨u, hm, ?_⟩
  have hw : node σ.e (grp σ.e u) (σ.yA d u m) = w := by
    rw [node_eq_iff]; exact ⟨hg.symm, hy.symm⟩
  unfold fA
  rw [hw, node_eq_iff]
  exact ⟨Fin.ext hk.symm, hs.symm⟩

lemma card_HB_le (d : I) (z : V) : (σ.HB d z).card ≤ s * s := by
  rw [← card_V σ.e]
  exact card_rcvd_le fun w => card_msgsOf_scatter_le σ.e _ _ _ _

/-- Column sums for Phase B: group `x` holds at most `s²` messages for group `j`. -/
lemma HB_col (hG : σ.Good) (d : I) (x j : Fin s) :
    ∑ b, ((σ.HB d (node σ.e x b)).filter fun m => σ.dg m = j).card ≤ s * s := by
  have h1 : ∑ b, ((σ.HB d (node σ.e x b)).filter fun m => σ.dg m = j).card =
      ∑ z, ((σ.HB d z).filter fun m => grp σ.e z = x ∧ σ.dg m = j).card := by
    rw [sum_V σ.e]
    simp only [grp_node]
    rw [Finset.sum_eq_single (f := fun a => ∑ b,
      ((σ.HB d (node σ.e a b)).filter fun m => a = x ∧ σ.dg m = j).card) x]
    · simp
    · intro a _ hax; simp [hax]
    · simp
  rw [h1]
  refine le_trans (sum_move (H := σ.inp d) (f := σ.fA d)
    (fun z m => grp σ.e z = x ∧ σ.dg m = j) fun z m hm => HB_sub hG d hm) ?_
  have h2 : ∀ u, ((σ.inp d u).filter fun m => grp σ.e (σ.fA d u m) = x ∧ σ.dg m = j).card =
      σ.q d (grp σ.e u) j (mem σ.e u) x := by
    intro u
    rw [← xA_count hG d u j x]
    congr 1
    refine filter_congr fun m _ => ?_
    simp [fA, and_comm]
  refine le_trans (le_of_eq (sum_congr rfl fun u _ => h2 u)) ?_
  rw [sum_V σ.e]
  simp only [grp_node, mem_node]
  refine le_trans (le_of_eq (sum_congr rfl fun a _ => (q_spec hG d a j).2 x)) ?_
  exact (Tp_spec hG d).2.2 x j

end Setup

end CongestedCliqueRouting
