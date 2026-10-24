import Papers.PODC2020.DynamicPartitioningLB.Model

/-!
# The adversary of Theorem 2.1 (lower bound `Ω(k ℓ)`)

Pacut, Parham, Schmid, PODC 2020, Section 2.1.

We work with `ℓ = L + 2` clusters and capacity `k = K + 3`; the nodes are
`Node L K = Fin ℓ × Fin k` (cluster of origin, index) and the initial configuration is `Prod.fst`.

**The ground sets** (the communication pattern revealed by the adversary) are, at every time:
* `B` = the `k - 1` nodes `(0, j)`, `j ≠ 0`, of cluster `0` (never requested unless the algorithm
  separates them);
* the pair `{z, y₀}` with `z = (0,0)` and `y₀ = (1,0)`;
* for every origin `c`, the set of nodes of `J` with origin `c` (empty or of size `≥ 2`);
* singletons (the *isolated* nodes).
`SameGS J u v` says that `u` and `v` are in the same ground set.

**The adversary** (`next`, `run`). If the algorithm's current configuration separates two nodes
of the same ground set, the adversary requests such a pair (a *repair* request; it costs the
algorithm `≥ 1`). Otherwise (all ground sets collocated) and while at least `ℓ + 2` nodes are
isolated, it joins the *pivot* — the unique node collocated with `B` outside `B`, which is
isolated — to the ground set of its origin (or to a fresh isolated node of its origin when that
ground set is empty), and requests a pair of the new ground set. This is the pivot-eviction
adversary of the paper; the differences (repair requests, `{z, y₀}` fixed in advance, the choice of
the ground set to join) are discussed in `differencies.md`.

**Accounting.** Between two consecutive configurations in which all ground sets are collocated
(`Q` and the next one) the algorithm migrates at least two nodes (`two_le_dist`); the invariant
`Inv` keeps track of `2α (s - 1) + α · dist Q P ≤ ALG`, where `s` counts the phases.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DynamicPartitioningLB.LB

open Finset Classical

noncomputable section

variable {L K : ℕ}

/-- Nodes: `(cluster of origin, index)`; `ℓ = L + 2`, `k = K + 3`. -/
abbrev Node (L K : ℕ) := Fin (L + 2) × Fin (K + 3)

/-- Configurations of `Node L K`. -/
abbrev Cfg (L K : ℕ) := Config (Node L K) (L + 2)

/-- The initial configuration: every node in its cluster of origin. -/
abbrev init : Cfg L K := Prod.fst

/-- The node of cluster `0` outside `B`. -/
def z : Node L K := (0, 0)
/-- The partner of `z` in the first non-trivial ground set. -/
def y0 : Node L K := (1, 0)
/-- A fixed node of `B`. -/
def b0 : Node L K := (0, 1)
/-- A second node of `B` (`k ≥ 3`). -/
def b1 : Node L K := (0, 2)

/-- The ground set `B` of size `k - 1`. -/
def B : Finset (Node L K) := univ.filter (fun v => v.1 = 0 ∧ v.2 ≠ 0)

/-- Nodes that are neither in `B` nor in `{z, y₀}`. -/
def Free : Finset (Node L K) := univ.filter (fun v => v ∉ B ∧ v ≠ z ∧ v ≠ y0)

/-- Same ground set. -/
def SameGS (J : Finset (Node L K)) (u v : Node L K) : Prop :=
  u = v ∨ (u ∈ B ∧ v ∈ B) ∨ ((u = z ∨ u = y0) ∧ (v = z ∨ v = y0)) ∨
    (u ∈ J ∧ v ∈ J ∧ u.1 = v.1)

/-- `P` collocates every ground set. -/
def Collocates (J : Finset (Node L K)) (P : Cfg L K) : Prop :=
  ∀ u v, SameGS J u v → P u = P v

/-- Number of isolated nodes. -/
def isoCount (J : Finset (Node L K)) : ℕ := (Free \ J).card

/-- The pivot: a node collocated with `B` outside `B`. -/
def pivot (P : Cfg L K) : Node L K :=
  if h : ∃ x, P x = P b0 ∧ x ∉ B then h.choose else z

/-- A node of the same origin as `x`, different from `x` and from `y₀`. -/
def fresh (x : Node L K) : Node L K := (x.1, if x.2 = 1 then 2 else 1)

/-- The adversary's merge step: join the pivot to the ground set of its origin. -/
def grow (J : Finset (Node L K)) (P : Cfg L K) : Finset (Node L K) :=
  if ∃ w ∈ J, w.1 = (pivot P).1 then insert (pivot P) J
  else insert (pivot P) (insert (fresh (pivot P)) J)

/-- A request inside a ground set that `P` separates, if any. -/
def splitPair (J : Finset (Node L K)) (P : Cfg L K) : Option (Req (Node L K)) :=
  if h : ∃ r : Req (Node L K), SameGS J r.1 r.2 ∧ P r.1 ≠ P r.2 then some h.choose else none

/-- State of the adversary: requests so far, the structure `J`, the configuration `Q` at the
beginning of the current phase, and the number `s` of phases. -/
structure St (L K : ℕ) where
  σ : List (Req (Node L K))
  J : Finset (Node L K)
  Q : Cfg L K
  s : ℕ

variable (A : OnlineAlg (Node L K) (L + 2) (K + 3) init)

/-- One move of the adversary (`none` = the adversary stops). -/
def next (st : St L K) : Option (St L K) :=
  match splitPair st.J (A.conf st.σ) with
  | some r => some ⟨st.σ ++ [r], st.J, st.Q, st.s⟩
  | none =>
    if L + 4 ≤ isoCount st.J then
      match splitPair (grow st.J (A.conf st.σ)) (A.conf st.σ) with
      | some r => some ⟨st.σ ++ [r], grow st.J (A.conf st.σ), A.conf st.σ, st.s + 1⟩
      | none => none
    else none

/-- The interaction of the adversary with `A`, for `n` moves. -/
def run : ℕ → St L K
  | 0 => ⟨[], ∅, init, 1⟩
  | n + 1 => (next A (run n)).getD (run n)

/-! ### Elementary facts about the fixed nodes -/

lemma fin_two_val : (2 : Fin (K + 3)).val = 2 := by simp
lemma fin_one_val : (1 : Fin (K + 3)).val = 1 := by simp

lemma mem_B {v : Node L K} : v ∈ B ↔ v.1 = 0 ∧ v.2 ≠ 0 := by simp [B]

lemma z_notMem_B : (z : Node L K) ∉ B := by simp [B, z]
lemma y0_notMem_B : (y0 : Node L K) ∉ B := by
  simp only [mem_B, y0, not_and, not_not]; intro h; exact absurd h.symm zero_ne_one
lemma b0_mem_B : (b0 : Node L K) ∈ B := by
  simp only [mem_B, b0, true_and, ne_eq, Fin.ext_iff, fin_one_val]; simp
lemma b1_mem_B : (b1 : Node L K) ∈ B := by
  simp only [mem_B, b1, true_and, ne_eq, Fin.ext_iff, fin_two_val]; simp
lemma b0_ne_b1 : (b0 : Node L K) ≠ b1 := by
  intro h
  have := congrArg (fun v : Node L K => (v.2 : ℕ)) h
  simp only [b0, b1, fin_one_val, fin_two_val] at this
  omega
lemma z_ne_y0 : (z : Node L K) ≠ y0 := by
  simp only [z, y0, ne_eq, Prod.mk.injEq, and_true]; exact zero_ne_one

lemma mem_Free {v : Node L K} : v ∈ Free ↔ v ∉ B ∧ v ≠ z ∧ v ≠ y0 := by simp [Free]

lemma fst_ne_zero_of_mem_Free {v : Node L K} (h : v ∈ Free) : v.1 ≠ 0 := by
  rw [mem_Free] at h
  intro h0
  by_cases h2 : v.2 = 0
  · exact h.2.1 (Prod.ext h0 h2)
  · exact h.1 (mem_B.2 ⟨h0, h2⟩)

lemma card_B : (B : Finset (Node L K)).card = K + 2 := by
  have : (B : Finset (Node L K)) = ({0} : Finset (Fin (L + 2))) ×ˢ (univ.erase 0) := by
    ext ⟨a, b⟩; simp [B, eq_comm]; tauto
  rw [this, card_product, card_erase_of_mem (mem_univ _)]; simp

lemma card_Free : (Free : Finset (Node L K)).card + K + 4 = (L + 2) * (K + 3) := by
  have h1 : (Free : Finset (Node L K)) = ((univ \ B).erase z).erase y0 := by
    ext v; simp only [Free, mem_filter, mem_univ, true_and, mem_erase, mem_sdiff]; tauto
  have hz : z ∈ (univ \ (B : Finset (Node L K))) := by simp [z_notMem_B]
  have hy : y0 ∈ (univ \ (B : Finset (Node L K))).erase z := by
    simp [y0_notMem_B, z_ne_y0.symm]
  rw [h1, card_erase_of_mem hy, card_erase_of_mem hz, card_sdiff_of_subset (subset_univ _),
    card_B, card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have : K + 2 + 2 ≤ (L + 2) * (K + 3) := by nlinarith
  omega

lemma card_node : Fintype.card (Node L K) = (L + 2) * (K + 3) := by simp

lemma card_fst_fiber (s : Fin (L + 2)) :
    (univ.filter (fun v : Node L K => v.1 = s)).card = K + 3 := by
  have : (univ.filter (fun v : Node L K => v.1 = s)) = ({s} : Finset _) ×ˢ univ := by
    ext ⟨a, b⟩; simp [eq_comm]
  rw [this, card_product]; simp

lemma init_balanced : Balanced (K + 3) (init : Cfg L K) := fun s => (card_fst_fiber s).le

lemma sameGS_mono {J J' : Finset (Node L K)} (h : J ⊆ J') {u v : Node L K} :
    SameGS J u v → SameGS J' u v := by
  rintro (h1 | h1 | h1 | ⟨hu, hv, he⟩)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr ⟨h hu, h hv, he⟩))

lemma Collocates.B {J : Finset (Node L K)} {P : Cfg L K} (h : Collocates J P) :
    ∀ v ∈ B, P v = P b0 := fun v hv => h v b0 (Or.inr (Or.inl ⟨hv, b0_mem_B⟩))

lemma splitPair_eq_none {J : Finset (Node L K)} {P : Cfg L K} :
    splitPair J P = none ↔ Collocates J P := by
  unfold splitPair Collocates
  split_ifs with h
  · simp only [false_iff]
    intro hc; obtain ⟨r, h1, h2⟩ := h; exact h2 (hc _ _ h1)
  · simp only [true_iff]
    intro u v huv; by_contra hne; exact h ⟨(u, v), huv, hne⟩

lemma splitPair_spec {J : Finset (Node L K)} {P : Cfg L K} {r : Req (Node L K)}
    (h : splitPair J P = some r) : SameGS J r.1 r.2 ∧ P r.1 ≠ P r.2 := by
  unfold splitPair at h
  split_ifs at h with h'
  · cases h; exact h'.choose_spec

/-! ### The key counting lemmas -/

/-- A cluster holding `B` holds at most one more node. -/
lemma no_two_extra {P : Cfg L K} (hP : Balanced (K + 3) P) (hB : ∀ v ∈ B, P v = P b0)
    {a b : Node L K} (ha : P a = P b0) (hb : P b = P b0) (haB : a ∉ B) (hbB : b ∉ B)
    (hab : a ≠ b) : False := by
  have hsub : insert a (insert b B) ⊆ univ.filter (fun v => P v = P b0) := by
    intro v hv
    simp only [mem_insert] at hv
    simp only [mem_filter, mem_univ, true_and]
    rcases hv with rfl | rfl | hv
    · exact ha
    · exact hb
    · exact hB v hv
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, haB]), card_insert_of_notMem hbB, card_B] at this
  have := hP (P b0)
  omega

/-- **Every phase costs two migrations.** If `P` has `B ∪ {x}` in one cluster and `P'` collocates
`B` and collocates `x` with some `w ∉ B`, then `P'` differs from `P` on at least two nodes. -/
lemma two_le_dist {P P' : Cfg L K} (hP : Balanced (K + 3) P) (hP' : Balanced (K + 3) P')
    (hB : ∀ v ∈ B, P v = P b0) {x w : Node L K} (hx : P x = P b0) (hxB : x ∉ B)
    (hB' : ∀ v ∈ B, P' v = P' b0) (hxw : P' x = P' w) (hwB : w ∉ B) (hwx : w ≠ x) :
    2 ≤ dist P P' := by
  have hx' : P' x ≠ P' b0 := fun h =>
    no_two_extra hP' hB' h (hxw ▸ h) hxB hwB hwx.symm
  by_cases he : P' b0 = P b0
  · -- `x` leaves the cluster of `B`, and some node `w'` enters it.
    have hcard := card_fiber_eq (by simp) hP' (P' b0)
    have hlt : (B : Finset (Node L K)).card < (univ.filter (fun v => P' v = P' b0)).card := by
      rw [hcard, card_B]; omega
    obtain ⟨w', hw'F, hw'B⟩ := exists_mem_notMem_of_card_lt_card hlt
    simp only [mem_filter, mem_univ, true_and] at hw'F
    have hw'x : w' ≠ x := by rintro rfl; exact hx' hw'F
    have hPw' : P w' ≠ P' w' := by
      intro h
      exact no_two_extra hP hB hx (h.trans (hw'F.trans he)) hxB hw'B hw'x.symm
    have hsub : ({x, w'} : Finset (Node L K)) ⊆ univ.filter (fun v => P v ≠ P' v) := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      simp only [mem_filter, mem_univ, true_and]
      rcases hv with rfl | rfl
      · rw [hx, ← he]; exact fun h => hx' h.symm
      · exact hPw'
    have := card_le_card hsub
    rwa [card_pair hw'x.symm] at this
  · -- `B` itself moves: `b0` and `b1` migrate.
    have hsub : ({b0, b1} : Finset (Node L K)) ⊆ univ.filter (fun v => P v ≠ P' v) := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      simp only [mem_filter, mem_univ, true_and]
      have hvB : v ∈ B := by rcases hv with rfl | rfl; exacts [b0_mem_B, b1_mem_B]
      rw [hB v hvB, hB' v hvB]; exact fun h => he h.symm
    have := card_le_card hsub
    rwa [card_pair b0_ne_b1] at this

/-- Facts about the pivot of a configuration collocating all ground sets. -/
lemma pivot_spec {J : Finset (Node L K)} {P : Cfg L K} (hP : Balanced (K + 3) P)
    (hc : Collocates J P) (hJ : J ⊆ Free) (hJ1 : ∀ c, (J.filter (fun v => v.1 = c)).card ≠ 1) :
    P (pivot P) = P b0 ∧ pivot P ∉ B ∧ pivot P ∈ Free ∧ pivot P ∉ J := by
  have hB := hc.B
  have hex : ∃ x, P x = P b0 ∧ x ∉ B := by
    have hcard := card_fiber_eq (by simp) hP (P b0)
    have hlt : (B : Finset (Node L K)).card < (univ.filter (fun v => P v = P b0)).card := by
      rw [hcard, card_B]; omega
    obtain ⟨x, hxF, hxB⟩ := exists_mem_notMem_of_card_lt_card hlt
    exact ⟨x, by simpa using hxF, hxB⟩
  have hpiv : P (pivot P) = P b0 ∧ pivot P ∉ B := by
    unfold pivot; rw [dite_eq_left hex]; exact hex.choose_spec
  set x := pivot P
  refine ⟨hpiv.1, hpiv.2, ?_, ?_⟩
  · rw [mem_Free]
    refine ⟨hpiv.2, ?_, ?_⟩
    · rintro hxz
      have : P y0 = P b0 := (hc y0 x (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, Or.inl hxz⟩)))).trans
        hpiv.1
      exact no_two_extra hP hB hpiv.1 this hpiv.2 y0_notMem_B (hxz ▸ z_ne_y0)
    · rintro hxy
      have : P z = P b0 := (hc z x (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, Or.inr hxy⟩)))).trans
        hpiv.1
      exact no_two_extra hP hB hpiv.1 this hpiv.2 z_notMem_B (hxy ▸ z_ne_y0.symm)
  · intro hxJ
    have h1 := hJ1 x.1
    have hpos : 0 < (J.filter (fun v => v.1 = x.1)).card := card_pos.2 ⟨x, by simp [hxJ]⟩
    have h2 : 1 < (J.filter (fun v => v.1 = x.1)).card := by omega
    obtain ⟨w, hw, hwx⟩ := exists_mem_ne h2 x
    simp only [mem_filter] at hw
    have : P w = P b0 := (hc w x (Or.inr (Or.inr (Or.inr ⟨hw.1, hxJ, hw.2⟩)))).trans hpiv.1
    exact no_two_extra hP hB hpiv.1 this hpiv.2 (mem_Free.1 (hJ hw.1)).1 hwx.symm

lemma fresh_spec (x : Node L K) (hx : x ∈ Free) :
    (fresh x).1 = x.1 ∧ fresh x ≠ x ∧ fresh x ∈ Free := by
  have h0 := fst_ne_zero_of_mem_Free hx
  refine ⟨rfl, ?_, ?_⟩
  · unfold fresh
    split_ifs with h
    · intro he; have := congrArg (fun v => v.2) he; simp only at this
      rw [h] at this; exact absurd (congrArg Fin.val this) (by rw [fin_two_val, fin_one_val]; omega)
    · intro he; exact h (congrArg (fun v => v.2) he).symm
  · rw [mem_Free]
    refine ⟨fun h => h0 (mem_B.1 h).1, fun h => h0 (congrArg Prod.fst h), fun h => ?_⟩
    have := congrArg (fun v => v.2) h
    simp only [fresh, y0] at this
    split_ifs at this
    · exact absurd (congrArg Fin.val this) (by rw [fin_two_val]; simp)
    · exact absurd (congrArg Fin.val this) (by rw [fin_one_val]; simp)

/-! ### The invariant -/

/-- Invariant of the interaction. -/
structure Inv (α : ℕ) (st : St L K) : Prop where
  sub : st.J ⊆ Free
  blob : ∀ c, (st.J.filter (fun v => v.1 = c)).card ≠ 1
  reqs : ∀ r ∈ st.σ, SameGS st.J r.1 r.2
  len : st.σ.length ≤ algCost α A st.σ
  s_pos : 1 ≤ st.s
  cost : 2 * α * (st.s - 1) + α * dist st.Q (A.conf st.σ) ≤ algCost α A st.σ
  good : ∀ P', Balanced (K + 3) P' → Collocates st.J P' → 2 ≤ dist st.Q P'
  count : st.J.card + 1 = st.s + (st.J.image Prod.fst).card
  iso : L + 2 ≤ isoCount st.J

lemma isoCount_add {J : Finset (Node L K)} (h : J ⊆ Free) :
    isoCount J + J.card = (Free : Finset (Node L K)).card :=
  card_sdiff_add_card_eq_card h

lemma image_card_le {J : Finset (Node L K)} (h : J ⊆ Free) : (J.image Prod.fst).card ≤ L + 1 := by
  have : J.image Prod.fst ⊆ univ.erase 0 := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
    exact mem_erase.2 ⟨fst_ne_zero_of_mem_Free (h hv), mem_univ _⟩
  have := card_le_card this
  rw [card_erase_of_mem (mem_univ _)] at this
  simpa using this

variable {A}

@[simp] lemma run_zero : run A 0 = ⟨[], ∅, init, 1⟩ := rfl

lemma inv_init {α : ℕ} : Inv A α (run A 0) where
  sub := empty_subset _
  blob := by simp
  reqs := by simp
  len := by simp [run]
  s_pos := le_rfl
  cost := by simp [run, A.conf_nil, dist_self, algCost_nil]
  good := by
    intro P' hP' hc
    show 2 ≤ dist init P'
    exact two_le_dist init_balanced hP' (fun v hv => by simp [init, (mem_B.1 hv).1, b0])
      (x := z) (w := y0) (by simp [init, z, b0]) z_notMem_B hc.B
      (hc z y0 (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, Or.inr rfl⟩)))) y0_notMem_B z_ne_y0.symm
  count := by simp [run]
  iso := by
    have := card_Free (L := L) (K := K)
    simp only [run, isoCount, sdiff_empty]
    nlinarith

/-- Adding a request inside a ground set that the current configuration separates. -/
lemma inv_req {α : ℕ} (hα : 1 ≤ α) {st : St L K} (h : Inv A α st) {r : Req (Node L K)}
    (hr : SameGS st.J r.1 r.2) (hsep : A.conf st.σ r.1 ≠ A.conf st.σ r.2) :
    Inv A α ⟨st.σ ++ [r], st.J, st.Q, st.s⟩ where
  sub := h.sub
  blob := h.blob
  reqs := by
    intro r' hr'
    rcases List.mem_append.1 hr' with h' | h'
    · exact h.reqs r' h'
    · rw [List.mem_singleton.1 h']; exact hr
  len := by
    have := one_le_stepCost hα (Q := A.conf (st.σ ++ [r])) hsep
    simp only [algCost_append, List.length_append, List.length_singleton]
    have := h.len; omega
  s_pos := h.s_pos
  cost := by
    simp only [algCost_append]
    have h1 := h.cost
    have h2 := dist_triangle st.Q (A.conf st.σ) (A.conf (st.σ ++ [r]))
    have h3 : α * dist st.Q (A.conf (st.σ ++ [r])) ≤
        α * dist st.Q (A.conf st.σ) + α * dist (A.conf st.σ) (A.conf (st.σ ++ [r])) := by
      rw [← mul_add]; exact Nat.mul_le_mul_left _ h2
    omega
  good := h.good
  count := h.count
  iso := h.iso

/-- The shape of the merge step, for a given isolated pivot `x`. -/
lemma grow_shape {J : Finset (Node L K)} {x : Node L K} (hxF : x ∈ Free) (hxJ : x ∉ J)
    (hJ : J ⊆ Free) (hblob : ∀ c, (J.filter (fun v => v.1 = c)).card ≠ 1) :
    let G := if ∃ w ∈ J, w.1 = x.1 then insert x J else insert x (insert (fresh x) J)
    (∃ w ∈ G, w ≠ x ∧ w ∉ B ∧ w.1 = x.1) ∧ x ∈ G ∧ J ⊆ G ∧ G ⊆ Free ∧
      (∀ c, (G.filter (fun v => v.1 = c)).card ≠ 1) ∧
      G.card + (J.image Prod.fst).card = J.card + 1 + (G.image Prod.fst).card ∧
      G.card ≤ J.card + 2 := by
  intro G
  by_cases hex : ∃ w ∈ J, w.1 = x.1
  · have hG : G = insert x J := ite_eq_left hex
    rw [hG]
    obtain ⟨w, hwJ, hwx⟩ := hex
    refine ⟨⟨w, mem_insert_of_mem hwJ, fun h => hxJ (h ▸ hwJ), (mem_Free.1 (hJ hwJ)).1, hwx⟩,
      mem_insert_self _ _, subset_insert _ _, insert_subset hxF hJ, ?_, ?_, ?_⟩
    · intro c
      rw [filter_insert]
      split_ifs with hc
      · have hpos : 0 < (J.filter (fun v => v.1 = c)).card :=
          card_pos.2 ⟨w, by simp [hwJ, hwx, hc]⟩
        rw [card_insert_of_notMem (by simp [hxJ])]
        have := hblob c; omega
      · exact hblob c
    · rw [card_insert_of_notMem hxJ, image_insert,
        insert_eq_of_mem (mem_image.2 ⟨w, hwJ, hwx⟩)]
    · rw [card_insert_of_notMem hxJ]; omega
  · have hG : G = insert x (insert (fresh x) J) := ite_eq_right hex
    rw [hG]
    obtain ⟨hy1, hyx, hyF⟩ := fresh_spec x hxF
    have hyJ : fresh x ∉ J := fun h => hex ⟨_, h, hy1⟩
    have hxyJ : x ∉ insert (fresh x) J := by simp [hxJ, hyx.symm]
    refine ⟨⟨fresh x, mem_insert_of_mem (mem_insert_self _ _), hyx, (mem_Free.1 hyF).1, hy1⟩,
      mem_insert_self _ _, (subset_insert _ _).trans (subset_insert _ _),
      insert_subset hxF (insert_subset hyF hJ), ?_, ?_, ?_⟩
    · intro c
      rw [filter_insert, filter_insert, hy1]
      split_ifs with hc
      · have : J.filter (fun v => v.1 = c) = ∅ := by
          rw [filter_eq_empty_iff]; intro v hv hvc; exact hex ⟨v, hv, hvc.trans hc.symm⟩
        rw [this, card_insert_of_notMem (by simp [hyx.symm]), insert_empty, card_singleton]
        omega
      · exact hblob c
    · have hx1 : x.1 ∉ J.image Prod.fst := by
        intro h; obtain ⟨v, hv, hv1⟩ := mem_image.1 h; exact hex ⟨v, hv, hv1⟩
      rw [card_insert_of_notMem hxyJ, card_insert_of_notMem hyJ, image_insert, image_insert, hy1,
        insert_idem, card_insert_of_notMem hx1]; ring
    · rw [card_insert_of_notMem hxyJ, card_insert_of_notMem hyJ]

/-- The merge step preserves the invariant (with the new phase starting at the current
configuration). -/
lemma inv_grow {α : ℕ} {st : St L K} (h : Inv A α st) (hc : Collocates st.J (A.conf st.σ))
    (hiso : L + 4 ≤ isoCount st.J) :
    Inv A α ⟨st.σ, grow st.J (A.conf st.σ), A.conf st.σ, st.s + 1⟩ := by
  have hP := A.balanced st.σ
  obtain ⟨hxb, hxB, hxF, hxJ⟩ := pivot_spec hP hc h.sub h.blob
  obtain ⟨⟨w, hwG, hwx, hwB, hw1⟩, hxG, hJG, hGF, hGblob, hGcount, hGcard⟩ :=
    grow_shape hxF hxJ h.sub h.blob
  have hgrow : grow st.J (A.conf st.σ) = (if ∃ w ∈ st.J, w.1 = (pivot (A.conf st.σ)).1 then
      insert (pivot (A.conf st.σ)) st.J else
      insert (pivot (A.conf st.σ)) (insert (fresh (pivot (A.conf st.σ))) st.J)) := rfl
  rw [← hgrow] at hwG hxG hJG hGF hGblob hGcount hGcard
  set G := grow st.J (A.conf st.σ)
  set x := pivot (A.conf st.σ)
  have hdQ : 2 ≤ dist st.Q (A.conf st.σ) := h.good _ hP hc
  exact
  { sub := hGF
    blob := hGblob
    reqs := fun r hr => sameGS_mono hJG (h.reqs r hr)
    len := h.len
    s_pos := Nat.le_add_left 1 st.s
    cost := by
      show 2 * α * (st.s + 1 - 1) + α * dist (A.conf st.σ) (A.conf st.σ) ≤ algCost α A st.σ
      have := h.cost; have := h.s_pos
      simp only [dist_self, mul_zero, add_zero, Nat.add_sub_cancel]
      have h2 : 2 * α * st.s = 2 * α * (st.s - 1) + 2 * α := by
        rw [← Nat.mul_add_one]; congr 1; omega
      have h3 : 2 * α ≤ α * dist st.Q (A.conf st.σ) := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ hdQ
      omega
    good := by
      intro P' hP' hc'
      exact two_le_dist hP hP' hc.B hxb hxB hc'.B
        (hc' x w (Or.inr (Or.inr (Or.inr ⟨hxG, hwG, hw1.symm⟩)))) hwB hwx
    count := by
      show G.card + 1 = (st.s + 1) + (G.image Prod.fst).card
      have := h.count; omega
    iso := by
      show L + 2 ≤ isoCount G
      have h1 := isoCount_add h.sub
      have h2 := isoCount_add hGF
      omega }

/-- What happens when the adversary stops. -/
lemma next_eq_none {α : ℕ} {st : St L K} (h : Inv A α st) (hn : next A st = none) :
    Collocates st.J (A.conf st.σ) ∧ isoCount st.J < L + 4 := by
  unfold next at hn
  cases hs : splitPair st.J (A.conf st.σ) with
  | some r => rw [hs] at hn; simp at hn
  | none =>
    rw [hs] at hn
    have hc := splitPair_eq_none.1 hs
    refine ⟨hc, ?_⟩
    by_contra hlt
    push Not at hlt
    rw [ite_eq_left hlt] at hn
    cases hs' : splitPair (grow st.J (A.conf st.σ)) (A.conf st.σ) with
    | some r => rw [hs'] at hn; simp at hn
    | none =>
      have hi := inv_grow h hc hlt
      have := hi.good _ (A.balanced st.σ) (splitPair_eq_none.1 hs')
      simp [dist_self] at this

/-- One move of the adversary preserves the invariant and appends one request. -/
lemma next_eq_some {α : ℕ} (hα : 1 ≤ α) {st st' : St L K} (h : Inv A α st)
    (hn : next A st = some st') : Inv A α st' ∧ ∃ r, st'.σ = st.σ ++ [r] := by
  unfold next at hn
  cases hs : splitPair st.J (A.conf st.σ) with
  | some r =>
    rw [hs] at hn
    cases hn
    obtain ⟨h1, h2⟩ := splitPair_spec hs
    exact ⟨inv_req hα h h1 h2, r, rfl⟩
  | none =>
    rw [hs] at hn
    have hc := splitPair_eq_none.1 hs
    split_ifs at hn with hlt
    cases hs' : splitPair (grow st.J (A.conf st.σ)) (A.conf st.σ) with
    | none => rw [hs'] at hn; simp at hn
    | some r =>
      rw [hs'] at hn
      cases hn
      have hi := inv_grow h hc hlt
      obtain ⟨h1, h2⟩ := splitPair_spec hs'
      exact ⟨inv_req hα hi h1 h2, r, rfl⟩

lemma inv_run {α : ℕ} (hα : 1 ≤ α) : ∀ n, Inv A α (run A n)
  | 0 => inv_init
  | n + 1 => by
    have ih := inv_run hα n
    show Inv A α ((next A (run A n)).getD (run A n))
    cases hn : next A (run A n) with
    | none => exact ih
    | some st' => exact (next_eq_some hα ih hn).1

lemma run_succ_prefix (n : ℕ) : (run A n).σ <+: (run A (n + 1)).σ := by
  show (run A n).σ <+: ((next A (run A n)).getD (run A n)).σ
  cases hn : next A (run A n) with
  | none => exact List.prefix_refl _
  | some st' =>
    -- the invariant is not needed for the shape of `next`
    unfold next at hn
    split at hn
    · cases hn; exact List.prefix_append _ _
    · split_ifs at hn
      split at hn
      · cases hn; exact List.prefix_append _ _
      · simp at hn

lemma run_prefix {m n : ℕ} (h : m ≤ n) : (run A m).σ <+: (run A n).σ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (run_succ_prefix _)

lemma run_length_or_stop {α : ℕ} (hα : 1 ≤ α) :
    ∀ n, (run A n).σ.length = n ∨ next A (run A n) = none
  | 0 => Or.inl rfl
  | n + 1 => by
    rcases run_length_or_stop hα n with hl | hs
    · show ((next A (run A n)).getD (run A n)).σ.length = n + 1 ∨
        next A ((next A (run A n)).getD (run A n)) = none
      cases hn : next A (run A n) with
      | none => exact Or.inr (by simpa using hn)
      | some st' =>
        obtain ⟨-, r, hr⟩ := next_eq_some hα (inv_run hα n) hn
        left; simp [hr, hl]
    · right
      show next A ((next A (run A n)).getD (run A n)) = none
      rw [hs]; exact hs

/-- The first request is `(z, y₀)`-like: external in the initial configuration. -/
lemma run_one : ∃ r : Req (Node L K), (run A 1).σ = [r] ∧ init r.1 ≠ init r.2 := by
  have hsp : ∃ r : Req (Node L K), SameGS (∅ : Finset (Node L K)) r.1 r.2 ∧
      init r.1 ≠ init r.2 :=
    ⟨(z, y0), Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, Or.inr rfl⟩)), by
      simp only [init, z, y0]; exact zero_ne_one⟩
  have hs : splitPair (∅ : Finset (Node L K)) (A.conf []) = some hsp.choose := by
    unfold splitPair; rw [A.conf_nil, dite_eq_left hsp]
  refine ⟨hsp.choose, ?_, hsp.choose_spec.2⟩
  show ((next A (run A 0)).getD (run A 0)).σ = _
  simp only [next, run_zero, hs, Option.getD_some, List.nil_append]

/-- **The perfect partition `P*`.** While at least `ℓ` nodes are isolated, two isolated nodes
`x*, y*` have the same origin; swapping `z, y₀` with `x*, y*` in the initial partition collocates
every ground set, at migration cost `≤ 4`. -/
lemma exists_perfect {α : ℕ} {st : St L K} (h : Inv A α st) :
    ∃ P : Cfg L K, Balanced (K + 3) P ∧ Collocates st.J P ∧ dist init P ≤ 4 := by
  have hlt : (univ.erase (0 : Fin (L + 2))).card < (Free \ st.J).card := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have := h.iso; unfold isoCount at this; omega
  obtain ⟨xs, hxs, ys, hys, hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (f := Prod.fst) (fun v hv => by
      simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
        true_and]
      exact fst_ne_zero_of_mem_Free (mem_sdiff.1 hv).1)
  rw [mem_sdiff] at hxs hys
  obtain ⟨hxsB, hxsz, hxsy⟩ := mem_Free.1 hxs.1
  obtain ⟨hysB, hysz, hysy⟩ := mem_Free.1 hys.1
  set τ : Equiv.Perm (Node L K) := Equiv.swap z xs * Equiv.swap y0 ys
  have hfix : ∀ v, v ≠ z → v ≠ y0 → v ≠ xs → v ≠ ys → τ v = v := by
    intro v h1 h2 h3 h4
    simp only [τ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h2 h4, Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hz : τ z = xs := by
    simp only [τ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne z_ne_y0 (Ne.symm hysz), Equiv.swap_apply_left]
  have hy : τ y0 = ys := by
    simp only [τ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hysz hne.symm]
  refine ⟨fun v => (τ v).1, ?_, ?_, ?_⟩
  · intro s
    rw [card_equiv τ (t := univ.filter (fun v : Node L K => v.1 = s)) (fun i => by simp)]
    exact (card_fst_fiber s).le
  · rintro u v (rfl | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv, he⟩)
    · rfl
    · have hfu : ∀ w ∈ (B : Finset (Node L K)), τ w = w := fun w hw =>
        hfix w (fun h => z_notMem_B (h ▸ hw)) (fun h => y0_notMem_B (h ▸ hw))
          (fun h => hxsB (h ▸ hw)) (fun h => hysB (h ▸ hw))
      simp only [hfu u hu, hfu v hv, (mem_B.1 hu).1, (mem_B.1 hv).1]
    · have hval : ∀ w, (w = z ∨ w = y0) → (τ w).1 = xs.1 := by
        rintro w (rfl | rfl)
        · rw [hz]
        · rw [hy, heq]
      simp only [hval u hu, hval v hv]
    · have hfu : ∀ w ∈ st.J, τ w = w := fun w hw => by
        obtain ⟨-, h2, h3⟩ := mem_Free.1 (h.sub hw)
        exact hfix w h2 h3 (fun h' => hxs.2 (h' ▸ hw)) (fun h' => hys.2 (h' ▸ hw))
      simp only [hfu u hu, hfu v hv, he]
  · refine (dist_le_of_subset (S := {z, y0, xs, ys}) fun v hv => ?_).trans card_le_four
    by_contra hS
    simp only [mem_insert, mem_singleton, not_or] at hS
    exact hv (by simp only [init, hfix v hS.1 hS.2.1 hS.2.2.1 hS.2.2.2])

/-- **Theorem 2.1, core.** Against every deterministic online algorithm the adversary produces a
request sequence `σ` together with a perfect partition `P*` of it at distance `≤ 4` from the
initial partition, whose first request is external initially, and on which
`ALG ≥ 2α · ((k - 2)(ℓ - 1) - 2)` (`k = K + 3`, `ℓ = L + 2`). -/
theorem lower_bound_core {α : ℕ} (hα : 1 ≤ α) :
    ∃ (σ : List (Req (Node L K))) (P : Cfg L K), Balanced (K + 3) P ∧
      (∀ r ∈ σ, P r.1 = P r.2) ∧ dist init P ≤ 4 ∧
      (∃ r τ, σ = r :: τ ∧ init r.1 ≠ init r.2) ∧
      2 * α * ((K + 1) * (L + 1) - 2) ≤ algCost α A σ := by
  set S := (K + 1) * (L + 1) - 2 with hS
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * α * S + 1 := ⟨_, rfl⟩
  have h := inv_run (A := A) hα N
  obtain ⟨P, hPb, hPc, hPd⟩ := exists_perfect h
  refine ⟨(run A N).σ, P, hPb, fun r hr => hPc _ _ (h.reqs r hr), hPd, ?_, ?_⟩
  · obtain ⟨r, hr1, hr⟩ := run_one (A := A)
    obtain ⟨τ, hτ⟩ := run_prefix (A := A) (show 1 ≤ N by omega)
    exact ⟨r, τ, by rw [← hτ, hr1, List.singleton_append], hr⟩
  · rcases run_length_or_stop (A := A) hα N with hl | hs
    · have := h.len; omega
    · obtain ⟨hc, hiso⟩ := next_eq_none h hs
      have hd := h.good _ (A.balanced _) hc
      have hcost := h.cost
      have hspos := h.s_pos
      have hcount := h.count
      have him := image_card_le h.sub
      have hiso' := isoCount_add h.sub
      have hF := card_Free (L := L) (K := K)
      have e1 : (K + 1) * (L + 1) = K * L + K + L + 1 := by ring
      have e2 : (L + 2) * (K + 3) = K * L + 2 * K + 3 * L + 6 := by ring
      have hsS : S ≤ (run A N).s := by omega
      have h3 : 2 * α ≤ α * dist (run A N).Q (A.conf (run A N).σ) := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ hd
      have h4 : 2 * α * (run A N).s = 2 * α * ((run A N).s - 1) + 2 * α := by
        rw [← Nat.mul_add_one]; congr 1; omega
      have h5 : 2 * α * S ≤ 2 * α * (run A N).s := Nat.mul_le_mul_left _ hsS
      omega

/-- **Theorem 2.1, specialised form.** Against every deterministic online algorithm the adversary
produces a learning-model input on which `1 ≤ OPT ≤ 4α` and
`ALG ≥ 2α · ((k - 2)(ℓ - 1) - 2)` (`k = K + 3`, `ℓ = L + 2`). -/
theorem lower_bound {α : ℕ} (hα : 1 ≤ α) :
    ∃ σ : List (Req (Node L K)), IsLearningInput (L + 2) (K + 3) σ ∧
      1 ≤ optCost (K + 3) α init σ ∧ optCost (K + 3) α init σ ≤ 4 * α ∧
      2 * α * ((K + 1) * (L + 1) - 2) ≤ algCost α A σ := by
  obtain ⟨σ, P, hPb, hPc, hPd, ⟨r, τ, rfl, hr⟩, hcost⟩ := lower_bound_core (A := A) hα
  refine ⟨r :: τ, ⟨P, hPb, hPc⟩, one_le_optCost hα init_balanced hr, ?_, hcost⟩
  refine (optCost_le (O := fun t => if t = 0 then init else P) ⟨ite_eq_left rfl, fun t => ?_⟩).trans
    ((schedCost_switch_le α init P _ hPc).trans ?_)
  · by_cases ht : t = 0
    · simp only [ht, ite_eq_left]; exact init_balanced
    · simp only [ht, ite_false]; exact hPb
  · rw [mul_comm 4]; exact Nat.mul_le_mul_left _ hPd

end

end Papers.PODC2020.DynamicPartitioningLB.LB
