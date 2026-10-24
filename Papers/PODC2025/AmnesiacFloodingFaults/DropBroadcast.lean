import Papers.PODC2025.AmnesiacFloodingFaults.Faults
import Papers.PODC2019.FloodingTermination.Model

/-!
# Theorem 5.6, broadcast part

Single-source amnesiac flooding from `s` on a connected finite graph loses the message `(u, v)`
of round `k + 1` (`dropRun`). It *fails to broadcast* (some node never receives the message) iff
* no message travelled along `uv` (in either direction) before that round,
* `uv` is a bridge, and
* the side of the cut containing `u` (the component of `u` in `G - uv`) has no odd cycle.

The proof compares the faulty run with flooding on `G - uv` (`dropRun_eq_srcRun_delete`), whose
round sets are the parity distances of Hussak–Trehan (`FloodingTermination.mem_roundSet_iff`).
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-! ### Bridge to `FloodingTermination` -/

lemma mem_srcRun_iff_sends {s : V} (t : ℕ) (u v : V) :
    (u, v) ∈ srcRun G s t ↔ FloodingTermination.sends G s (t + 1) u v := by
  induction t generalizing u v with
  | zero =>
    simp only [srcRun, Function.iterate_zero, id, mem_step, Set.mem_empty_iff_false,
      not_false_eq_true, true_and, Set.mem_singleton_iff, Active, exists_false, or_false,
      zero_add, FloodingTermination.sends_one]
    tauto
  | succ t ih =>
    rw [FloodingTermination.sends_add_two, srcRun, Function.iterate_succ_apply', ← srcRun]
    simp only [mem_step, Set.mem_empty_iff_false, false_or, Active, ih]
    tauto

/-- `x` is in the round set `R_j` of single-source flooding iff it initiates (`j = 0`) or is
active in round `j`. -/
lemma mem_roundSet_iff_active {s x : V} (j : ℕ) :
    x ∈ FloodingTermination.roundSet G s (j + 1) ↔ Active (srcRun G s j) x := by
  rw [FloodingTermination.mem_roundSet_succ]
  simp only [Active, mem_srcRun_iff_sends]

lemma reachable_of_active_srcRun {s x : V} {j : ℕ} (h : Active (srcRun G s j) x) :
    G.Reachable s x := by
  rw [← mem_roundSet_iff_active, FloodingTermination.mem_roundSet_iff] at h
  exact reachable_of_mem_walkSet h.1

/-! ### Odd closed walks contain odd cycles -/

lemma exists_odd_cycle {H : SimpleGraph V} :
    ∀ (n : ℕ) {x : V} (Z : H.Walk x x), Z.length = n → Odd n →
      ∃ (y : V) (C : H.Walk y y), C.IsCycle ∧ Odd C.length ∧ C.support ⊆ Z.support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x Z hZ hodd
    rcases WalkAlgebra.closed_cases Z with hc | h0 | h2 | ⟨y, A, B, A', rfl, hB, hA⟩
    · exact ⟨x, Z, hc, hZ ▸ hodd, fun _ h => h⟩
    · rw [h0] at hZ; subst hZ; exact absurd hodd (by decide)
    · rw [h2] at hZ; subst hZ; exact absurd hodd (by decide)
    · simp only [Walk.length_append] at hZ
      rcases Nat.even_or_odd B.length with hBe | hBo
      · obtain ⟨z, C, hC, hCo, hCs⟩ := ih (A.length + A'.length) (by omega) (A.append A')
          (by simp) (by obtain ⟨r, hr⟩ := hodd; obtain ⟨q, hq⟩ := hBe; exact ⟨r - q, by omega⟩)
        refine ⟨z, C, hC, hCo, fun w hw => ?_⟩
        have := hCs hw
        simp only [Walk.mem_support_append_iff] at this ⊢
        tauto
      · obtain ⟨z, C, hC, hCo, hCs⟩ := ih B.length (by omega) B rfl hBo
        refine ⟨z, C, hC, hCo, fun w hw => ?_⟩
        have := hCs hw
        simp only [Walk.mem_support_append_iff]
        tauto

/-! ### The faulty run -/

variable (G) in
/-- Single-source amnesiac flooding from `s` in which the message `m` of round `k + 1` is lost:
`dropRun G s k m t` is the set of messages delivered in round `t + 1`. -/
def dropRun (s : V) (k : ℕ) (m : V × V) : ℕ → Config V
  | 0 => step G {s} ∅ \ (if k = 0 then {m} else ∅)
  | t + 1 => af G (dropRun s k m t) \ (if t + 1 = k then {m} else ∅)

lemma dropRun_of_lt {s : V} {k : ℕ} {m : V × V} {t : ℕ} (ht : t < k) :
    dropRun G s k m t = srcRun G s t := by
  induction t with
  | zero => simp [dropRun, srcRun, show k ≠ 0 by omega]
  | succ t ih =>
    rw [dropRun, ih (by omega), ite_eq_right (by omega), Set.sdiff_empty, srcRun, srcRun,
      Function.iterate_succ_apply']

lemma dropRun_self {s : V} {k : ℕ} {m : V × V} :
    dropRun G s k m k = srcRun G s k \ {m} := by
  cases k with
  | zero => simp [dropRun, srcRun]
  | succ k =>
    rw [dropRun, dropRun_of_lt (by omega), ite_eq_left rfl, srcRun, srcRun,
      Function.iterate_succ_apply']

lemma dropRun_add {s : V} {k : ℕ} {m : V × V} (t : ℕ) :
    dropRun G s k m (k + t) = (af G)^[t] (srcRun G s k \ {m}) := by
  induction t with
  | zero => exact dropRun_self
  | succ t ih =>
    rw [← add_assoc, dropRun, ite_eq_right (by omega), Set.sdiff_empty, ih,
      Function.iterate_succ_apply']

/-- A node sends in round `j + 1` of the faulty run: it initiates (`j = 0`) or was active. -/
def DropSends (s : V) (k : ℕ) (m : V × V) (j : ℕ) (x : V) : Prop :=
  (j = 0 ∧ x = s) ∨ ∃ j', j = j' + 1 ∧ Active (dropRun G s k m j') x

lemma head_dropSends {s : V} {k : ℕ} {m : V × V} {j : ℕ} {x y : V}
    (h : (x, y) ∈ dropRun G s k m j) : DropSends (G := G) s k m j x := by
  cases j with
  | zero =>
    left; refine ⟨rfl, ?_⟩
    have := h.1.2.2
    simpa [Active] using this
  | succ j =>
    right; refine ⟨j, rfl, ?_⟩
    exact h.1.2.2.resolve_left (Set.notMem_empty _)

lemma mem_dropRun_of_sends {s : V} {k : ℕ} {m : V × V} {j : ℕ} {x y : V}
    (hs : DropSends (G := G) s k m j x) (hxy : G.Adj x y) (hm : ¬ (j = k ∧ (x, y) = m)) :
    (x, y) ∈ dropRun G s k m j ∨ ∃ j', j = j' + 1 ∧ (y, x) ∈ dropRun G s k m j' := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨j', rfl, hact⟩
  · left
    refine ⟨⟨hxy, by simp, Or.inl rfl⟩, ?_⟩
    split_ifs with hk
    · simp only [Set.mem_singleton_iff]; exact fun h => hm ⟨hk.symm, h⟩
    · simp
  · by_cases hyx : (y, x) ∈ dropRun G s k m j'
    · exact Or.inr ⟨j', rfl, hyx⟩
    · left
      refine ⟨⟨hxy, hyx, Or.inr hact⟩, ?_⟩
      split_ifs with hk
      · simp only [Set.mem_singleton_iff]; exact fun h => hm ⟨hk, h⟩
      · simp

/-- Comparison with flooding on `G - uv` while no message uses `uv`. -/
lemma dropRun_eq_srcRun_delete {s u v : V} {k T : ℕ}
    (hno : ∀ t ≤ T, (u, v) ∉ dropRun G s k (u, v) t ∧ (v, u) ∉ dropRun G s k (u, v) t) :
    ∀ t ≤ T, dropRun G s k (u, v) t = srcRun (G.deleteEdges {s(u, v)}) s t := by
  have key : ∀ (S S' : Config V) (D : Set (V × V)) (I : Set V), S = S' → D ⊆ {(u, v)} →
      (u, v) ∉ step G I S \ D → (v, u) ∉ step G I S \ D →
      step G I S \ D = step (G.deleteEdges {s(u, v)}) I S' := by
    intro S S' D I hSS hD h1 h2
    subst hSS
    ext ⟨x, y⟩
    simp only [Set.mem_sdiff, mem_step, deleteEdges_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hxy, h3, h4⟩, h5⟩
      refine ⟨⟨hxy, fun he => ?_⟩, h3, h4⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1 ⟨⟨hxy, h3, h4⟩, h5⟩
      · exact h2 ⟨⟨hxy, h3, h4⟩, h5⟩
    · rintro ⟨⟨hxy, hne⟩, h3, h4⟩
      refine ⟨⟨hxy, h3, h4⟩, fun hD' => hne ?_⟩
      have := hD hD'
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this; rfl
  intro t ht
  induction t with
  | zero =>
    have := hno 0 ht
    rw [dropRun] at this ⊢
    rw [srcRun, Function.iterate_zero, id]
    exact key _ _ _ _ rfl (by split_ifs <;> simp) this.1 this.2
  | succ t ih =>
    have := hno (t + 1) ht
    rw [dropRun] at this ⊢
    rw [srcRun, Function.iterate_succ_apply', ← srcRun]
    exact key _ _ _ _ (ih (by omega)) (by split_ifs <;> simp) this.1 this.2

/-- Some node never receives the message in the faulty run. -/
def DropFailsBroadcast (s : V) (k : ℕ) (m : V × V) : Prop :=
  ∃ x, x ≠ s ∧ ∀ t, ¬ Active (dropRun G s k m t) x

/-- The side of the cut at `uv` containing `u` has an odd cycle. -/
def SideHasOddCycle (u v : V) : Prop :=
  ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length ∧
    ∀ y ∈ c.support, (G.deleteEdges {s(u, v)}).Reachable u y

lemma reachable_delete_of_reachable {u v a b : V}
    (huv : (G.deleteEdges {s(u, v)}).Reachable u v) (h : G.Reachable a b) :
    (G.deleteEdges {s(u, v)}).Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons x y z hxy q ih =>
    refine Reachable.trans ?_ ih
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    · exact Adj.reachable (deleteEdges_adj.2 ⟨hxy, by simpa using he⟩)

lemma reachable_delete_cover {u v a b : V} (h : G.Reachable a b)
    (ha : (G.deleteEdges {s(u, v)}).Reachable u a ∨ (G.deleteEdges {s(u, v)}).Reachable v a) :
    (G.deleteEdges {s(u, v)}).Reachable u b ∨ (G.deleteEdges {s(u, v)}).Reachable v b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | @cons x y z hxy q ih =>
    apply ih
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; rfl
      · left; rfl
    · have hadj : (G.deleteEdges {s(u, v)}).Adj x y := deleteEdges_adj.2 ⟨hxy, by simpa using he⟩
      rcases ha with ha | ha
      · exact Or.inl (ha.trans hadj.reachable)
      · exact Or.inr (ha.trans hadj.reachable)

/-- **Theorem 5.6** (single message failure, broadcast part). On a connected graph, single-source
amnesiac flooding that loses the message `(u, v)` of round `k + 1` fails to broadcast iff no message
used the edge `uv` before that round, `uv` is a bridge, and the side of the cut containing `u` has
no odd cycle. -/
theorem theorem_5_6_broadcast (hG : G.Connected) {s u v : V} {k : ℕ}
    (hm : (u, v) ∈ srcRun G s k) :
    DropFailsBroadcast (G := G) s k (u, v) ↔
      (∀ t < k, (u, v) ∉ srcRun G s t ∧ (v, u) ∉ srcRun G s t) ∧ G.IsBridge s(u, v) ∧
        ¬ SideHasOddCycle (G := G) u v := by
  classical
  set G' := G.deleteEdges {s(u, v)} with hG'
  have hadj : G.Adj u v := (srcRun_reachable (G := G) s k).isConfig u v hm
  -- `u` sends in round `k + 1`
  have hu_k : DropSends (G := G) s k (u, v) k u := by
    cases k with
    | zero => left; exact ⟨rfl, by simpa [Active] using hm.2.2⟩
    | succ k =>
      right; refine ⟨k, rfl, ?_⟩
      rw [dropRun_of_lt (by omega)]
      have := hm; rw [srcRun, Function.iterate_succ_apply'] at this
      exact this.2.2.resolve_left (Set.notMem_empty _)
  -- parity distances in `G'` are round sets of the comparison run
  have hroundG' : ∀ j x, (j = 0 ∧ x = s ∨ ∃ j', j = j' + 1 ∧ Active (srcRun G' s j') x) →
      G'.IsParityDist s x j := by
    rintro j x (⟨rfl, rfl⟩ | ⟨j', rfl, h⟩)
    · simp
    · rw [← FloodingTermination.mem_roundSet_iff, mem_roundSet_iff_active]; exact h
  constructor
  · rintro ⟨x, hxs, hx⟩
    -- the set of informed nodes
    set Inf : V → Prop := fun y => y = s ∨ ∃ t, Active ((dropRun G s k (u, v)) t) y
    have hInf_of_sends : ∀ j y, DropSends (G := G) s k (u, v) j y → Inf y := by
      rintro j y (⟨-, rfl⟩ | ⟨j', -, h⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨j', h⟩
    have hclosed : ∀ a b, Inf a → G.Adj a b → s(a, b) ≠ s(u, v) → Inf b := by
      intro a b ha hab hne
      obtain ⟨j, hj⟩ : ∃ j, DropSends (G := G) s k (u, v) j a := by
        rcases ha with rfl | ⟨t, ht⟩
        · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨t + 1, Or.inr ⟨t, rfl, ht⟩⟩
      rcases mem_dropRun_of_sends hj hab (fun h => hne (by obtain ⟨-, h2⟩ := h; simp only [Prod.mk.injEq] at h2; rw [h2.1, h2.2])) with h | ⟨j', -, h⟩
      · exact Or.inr ⟨j, a, h⟩
      · exact hInf_of_sends _ _ (head_dropSends h)
    have hInf_reach : ∀ a b, Inf a → G'.Reachable a b → Inf b := by
      intro a b ha ⟨p⟩
      induction p with
      | nil => exact ha
      | @cons y z w hyz q ih =>
        rw [deleteEdges_adj] at hyz
        exact ih (hclosed _ _ ha hyz.1 (by simpa using hyz.2))
    have hxInf : ¬ Inf x := by
      rintro (h | ⟨t, ht⟩)
      · exact hxs h
      · exact hx t ht
    have huInf : Inf u := hInf_of_sends _ _ hu_k
    have hsInf : Inf s := Or.inl rfl
    have hvInf : ¬ Inf v := by
      intro hv
      rcases reachable_delete_cover (G := G) (hG.preconnected u x) (Or.inl (Reachable.refl _)) with h | h
      · exact hxInf (hInf_reach _ _ huInf h)
      · exact hxInf (hInf_reach _ _ hv h)
    have hbridge : G.IsBridge s(u, v) := by
      rw [isBridge_iff]
      intro huv
      exact hxInf (hInf_reach _ _ hsInf (reachable_delete_of_reachable huv (hG.preconnected s x)))
    -- no message ever uses `uv`
    have hnoF : ∀ t, (u, v) ∉ (dropRun G s k (u, v)) t ∧ (v, u) ∉ (dropRun G s k (u, v)) t := by
      intro t
      exact ⟨fun h => hvInf (Or.inr ⟨t, u, h⟩),
        fun h => hvInf (hInf_of_sends _ _ (head_dropSends h))⟩
    refine ⟨fun t ht => ?_, hbridge, ?_⟩
    · rw [← dropRun_of_lt (m := (u, v)) ht]; exact hnoF t
    · rintro ⟨c0, C, hC, hCo, hCs⟩
      have hFeq := fun t => dropRun_eq_srcRun_delete (fun t' _ => hnoF t') t le_rfl
      -- the cycle avoids the bridge, so it lives in `G'`
      have hCG' : ∀ e ∈ C.edges, e ∈ G'.edgeSet := by
        intro e he
        rw [hG', edgeSet_deleteEdges]
        exact ⟨C.edges_subset_edgeSet he, fun h => hbridge.notMem_edges_of_isCycle hC
          (by rw [Set.mem_singleton_iff] at h; exact h ▸ he)⟩
      let C' := C.transfer G' hCG'
      have hsu : G'.Reachable s u := by
        by_contra hsu
        rcases reachable_delete_cover (G := G) (hG.preconnected u s) (Or.inl (Reachable.refl _)) with h | h
        · exact hsu h.symm
        · exact hvInf (hInf_reach _ _ hsInf h.symm)
      obtain ⟨p⟩ := hsu.trans (hCs c0 C.start_mem_support)
      obtain ⟨q⟩ := (hCs c0 C.start_mem_support).symm
      have h1 : u ∈ G'.walkSet s (p.length + q.length) :=
        mem_walkSet_iff.2 ⟨p.append q, by simp⟩
      have h2 : u ∈ G'.walkSet s (p.length + C.length + q.length) :=
        mem_walkSet_iff.2 ⟨p.append (C'.append q), by simp [C']; ring⟩
      obtain ⟨t1, -, ht1, hd1⟩ := exists_isParityDist h1
      obtain ⟨t2, -, ht2, hd2⟩ := exists_isParityDist h2
      have hne12 : t1 ≠ t2 := by
        intro he; subst he
        obtain ⟨r, hr⟩ := hCo
        omega
      -- `u` sends in rounds `t1` and `t2`; one of them is not the faulty round
      have hsend : ∀ j, G'.IsParityDist s u j → j ≠ k → Inf v := by
        intro j hj hjk
        have hs : DropSends (G := G) s k (u, v) j u := by
          rw [← FloodingTermination.mem_roundSet_iff] at hj
          cases j with
          | zero => left; simpa using hj
          | succ j =>
            right; refine ⟨j, rfl, ?_⟩
            rw [mem_roundSet_iff_active] at hj
            rwa [show (dropRun G s k (u, v)) j = srcRun G' s j from hFeq j]
        rcases mem_dropRun_of_sends hs hadj (fun h => hjk h.1) with h | ⟨j', -, h⟩
        · exact Or.inr ⟨j, u, h⟩
        · exact absurd h (hnoF j').2
      by_cases hk1 : t1 = k
      · exact hvInf (hsend t2 hd2 (by omega))
      · exact hvInf (hsend t1 hd1 hk1)
  · rintro ⟨hfirst, hbridge, hnoodd⟩
    have hR : ∀ t < k, (dropRun G s k (u, v)) t = srcRun G' s t := by
      intro t ht
      exact dropRun_eq_srcRun_delete (T := t) (fun t' ht' => by
        rw [dropRun_of_lt (by omega)]; exact hfirst t' (by omega)) t le_rfl
    -- `u` is reachable from `s` in `G'`, `v` is not
    have hsu : G'.Reachable s u := by
      rcases hu_k with ⟨-, rfl⟩ | ⟨j, rfl, hj⟩
      · rfl
      · rw [hR j (by omega)] at hj; exact reachable_of_active_srcRun hj
    have hsv : ¬ G'.Reachable s v := fun h => hbridge (hsu.symm.trans h)
    have hvact : ∀ j, ¬ Active (srcRun G' s j) v := fun j h => hsv (reachable_of_active_srcRun h)
    -- all walks from `s` to `u` in `G'` have the same parity
    have hpar : ∀ (p q : G'.Walk s u), p.length % 2 = q.length % 2 := by
      intro p q
      by_contra hne
      obtain ⟨y, C, hC, hCo, hCs⟩ := exists_odd_cycle _ (p.append q.reverse) rfl
        (by simp only [Walk.length_append, Walk.length_reverse]; exact Nat.odd_iff.2 (by omega))
      apply hnoodd
      refine ⟨y, C.transfer G (fun e he => ?_), hC.transfer _, by simpa using hCo, ?_⟩
      · exact edgeSet_mono (deleteEdges_le _) (C.edges_subset_edgeSet he)
      · intro z hz
        rw [Walk.support_transfer] at hz
        have hz' := hCs hz
        simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hz'
        rcases hz' with hz' | hz'
        · exact hsu.symm.trans ⟨p.takeUntil z hz'⟩
        · exact hsu.symm.trans ⟨q.takeUntil z hz'⟩
    have hunique : ∀ j, G'.IsParityDist s u j → j = k := by
      have hk : G'.IsParityDist s u k := by
        apply hroundG'
        rcases hu_k with ⟨rfl, rfl⟩ | ⟨j, rfl, hj⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨j, rfl, by rwa [← hR j (by omega)]⟩
      intro j hj
      obtain ⟨p, hp⟩ := mem_walkSet_iff.1 hj.1
      obtain ⟨q, hq⟩ := mem_walkSet_iff.1 hk.1
      exact hj.eq_of_mod_two_eq hk (by rw [← hp, ← hq]; exact hpar p q)
    -- no message ever uses `uv`
    have hno : ∀ T, ∀ t ≤ T, (u, v) ∉ (dropRun G s k (u, v)) t ∧ (v, u) ∉ (dropRun G s k (u, v)) t := by
      intro T
      induction T with
      | zero =>
        intro t ht
        obtain rfl : t = 0 := by omega
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          refine ⟨by simp [dropRun], fun h => ?_⟩
          have : v = s := by simpa [Active] using h.1.2.2
          exact hsv (this ▸ Reachable.refl _)
        · rw [show (dropRun G s k (u, v)) 0 = srcRun G s 0 from dropRun_of_lt hk0]; exact hfirst 0 hk0
      | succ T ih =>
        intro t ht
        rcases Nat.lt_or_ge t (T + 1) with h | h
        · exact ih t (by omega)
        obtain rfl : t = T + 1 := by omega
        have hFT := dropRun_eq_srcRun_delete (fun t' ht' => ih t' ht') T le_rfl
        constructor
        · intro h1
          by_cases hk : T + 1 = k
          · have : (u, v) ∉ (dropRun G s k (u, v)) (T + 1) := by
              rw [dropRun, ite_eq_left hk]; exact fun h => h.2 rfl
            exact this h1
          · -- `u` would send in round `T + 2 ≠ k + 1`
            have hact : Active (srcRun G' s T) u := by
              rw [← hFT]; exact h1.1.2.2.resolve_left (Set.notMem_empty _)
            exact hk (hunique (T + 1) (hroundG' _ _ (Or.inr ⟨T, rfl, hact⟩)))
        · intro h1
          have hact : Active (srcRun G' s T) v := by
            rw [← hFT]; exact h1.1.2.2.resolve_left (Set.notMem_empty _)
          exact hvact T hact
    have hFeq := fun t => dropRun_eq_srcRun_delete (fun t' ht' => hno t t' ht') t le_rfl
    refine ⟨v, fun h => hsv (h ▸ Reachable.refl _), fun t ht => ?_⟩
    rw [show (dropRun G s k (u, v)) t = srcRun G' s t from hFeq t] at ht
    exact hvact t ht

end AmnesiacFloodingFaults
