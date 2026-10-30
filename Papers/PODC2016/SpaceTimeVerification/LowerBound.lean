import Papers.PODC2016.SpaceTimeVerification.Basic
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
import Cslib.Foundations.Combinatorics.SimpleGraph.Arboricity

/-!
# Theorem 7: every `t`-PLS for acyclicity needs labels of size `Ω(log n / t)`

The paper (Section 4.1) derives Theorem 7 from its general crossing tool (Theorem 5). That tool is
false in the identifier-based model the paper claims for it (`Crossing.lean`), so we prove
Theorem 7 directly, following the same construction.

* `G` is the path `0 — 1 — ⋯ — (n-1)` (`pathGraph n`), labelled by an accepted labelling `ℓ`.
  The edges `e_i = (q·i, q·i+1)`, `q = 2t+2`, `1 ≤ i ≤ r = ⌊n/q⌋ - 1`, have pairwise disjoint
  `t`-neighbourhoods `[q·i - t, q·i + t + 1]` of `q` nodes. If the labels come from a set of size
  `< r^{1/q}`, two of these windows carry the same labels (pigeonhole).
* `crossGraph n A B` is the edge crossing `C(e_i, e_j, G)` with `A = q·i < B = q·j`: the edges
  `(A, A+1)` and `(B, B+1)` are replaced by `(A, B+1)` and `(B, A+1)`. It is the path
  `0..A, B+1..n-1` plus the cycle `A+1..B`.
* Every node of the crossed graph sees the same labelled `t`-ball as some node of the path, so it
  accepts (`crossGraph_accepts`). Far from the crossing the ball is unchanged; near it we compare
  with the path relabelled by a *block swap* `bswap` (exchange `[P, P+w)` with `[P+D, P+D+w)`,
  `D = B - A`), which leaves `ℓ` unchanged because the two windows carry the same labels, and
  which agrees with the crossed graph around the node (`key_high`, `key_low`; the width `w` of
  the swapped block depends on the node).
* The cycle `A+1..B` is a connected component, it is a connected graph with a cycle, and all of its
  nodes accept: this contradicts soundness. Hence `⌊n/(2t+2)⌋ - 1 ≤ |labels|^(2t+2)`
  (`lowerBound_card`), i.e. labels of length `≤ L` need `log₂(⌊n/(2t+2)⌋ - 1) < (2t+2)(L+1)`
  (`theorem_7`).
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph

/-! ### Arithmetic of the crossing -/

/-- Adjacency of the crossed path on node indices: the path edges except `(A, A+1)` and
`(B, B+1)`, plus the crossing edges `(A, B+1)` and `(B, A+1)`. -/
def crossAdj (A B u v : ℕ) : Prop :=
  ((u + 1 = v ∨ v + 1 = u) ∧ ¬ (u = A ∧ v = A + 1) ∧ ¬ (v = A ∧ u = A + 1) ∧
      ¬ (u = B ∧ v = B + 1) ∧ ¬ (v = B ∧ u = B + 1)) ∨ (u = A ∧ v = B + 1) ∨
    (v = A ∧ u = B + 1) ∨ (u = B ∧ v = A + 1) ∨ (v = B ∧ u = A + 1)

/-- Exchange the blocks `[P, P+w)` and `[P+D, P+D+w)` of node indices (for `w ≤ D`). -/
def bswap (P D w u : ℕ) : ℕ :=
  if P ≤ u ∧ u < P + w then u + D else if P + D ≤ u ∧ u < P + D + w then u - D else u

lemma bswap_bswap {P D w : ℕ} (h : w ≤ D) (u : ℕ) : bswap P D w (bswap P D w u) = u := by
  unfold bswap; split_ifs <;> omega

@[simp] lemma bswap_zero (P D u : ℕ) : bswap P D 0 u = u := by
  unfold bswap; split_ifs <;> omega

lemma bswap_lt {P D w n u : ℕ} (hn : P + D + w ≤ n) (hu : u < n) : bswap P D w u < n := by
  unfold bswap; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- Near the crossing edge `(A, B+1)` on the path side (`x ∈ (A-t, A]`), the crossed graph agrees
with the path relabelled by swapping `[A+1, A+w]` and `[B+1, B+w]`, `w = x + t - A`. -/
lemma key_high_A (A D t w x a b : ℕ) (hAB : 2 * t + 2 ≤ D) (hx : x ≤ A) (hw : w + A = x + t)
    (hd1 : bswap (A + 1) D w a < x + t) (hd2 : x < bswap (A + 1) D w a + t) :
    (bswap (A + 1) D w a + 1 = bswap (A + 1) D w b ∨
      bswap (A + 1) D w b + 1 = bswap (A + 1) D w a) ↔ crossAdj A (A + D) a b := by
  unfold crossAdj bswap at *
  split_ifs at * <;> constructor <;> intro h <;> omega

set_option maxHeartbeats 2000000 in
/-- Near the crossing edge `(B, A+1)` on the cycle side (`x ∈ (B-t, B]`): swap `[A+1, A+w]`
and `[B+1, B+w]`, `w = x + t - B`. -/
lemma key_high_B (A D t w x a b : ℕ) (hAB : 2 * t + 2 ≤ D) (hx : x ≤ A + D)
    (hw : w + A + D = x + t)
    (hd1 : bswap (A + 1) D w a < x + t) (hd2 : x < bswap (A + 1) D w a + t) :
    (bswap (A + 1) D w a + 1 = bswap (A + 1) D w b ∨
      bswap (A + 1) D w b + 1 = bswap (A + 1) D w a) ↔ crossAdj A (A + D) a b := by
  unfold crossAdj bswap at *
  split_ifs at * <;> constructor <;> intro h <;> omega

set_option maxHeartbeats 2000000 in
/-- Near the crossing edge `(B, A+1)` on the cycle side (`x ∈ [A+1, A+t]`): swap
`[A+1-w, A]` and `[B+1-w, B]`, `w = A + 1 + t - x`. -/
lemma key_low_A (A D t w x a b : ℕ) (hAB : 2 * t + 2 ≤ D) (htA : t ≤ A) (hx : A + 1 ≤ x)
    (hw : w + x = A + 1 + t)
    (hd1 : bswap (A + 1 - w) D w a < x + t) (hd2 : x < bswap (A + 1 - w) D w a + t) :
    (bswap (A + 1 - w) D w a + 1 = bswap (A + 1 - w) D w b ∨
      bswap (A + 1 - w) D w b + 1 = bswap (A + 1 - w) D w a) ↔ crossAdj A (A + D) a b := by
  unfold crossAdj bswap at *
  split_ifs at * <;> constructor <;> intro h <;> omega

set_option maxHeartbeats 2000000 in
/-- Near the crossing edge `(A, B+1)` on the path side (`x ∈ [B+1, B+t]`): swap `[A+1-w, A]` and
`[B+1-w, B]`, `w = B + 1 + t - x`. -/
lemma key_low_B (A D t w x a b : ℕ) (hAB : 2 * t + 2 ≤ D) (htA : t ≤ A) (hx : A + D + 1 ≤ x)
    (hw : w + x = A + D + 1 + t)
    (hd1 : bswap (A + 1 - w) D w a < x + t) (hd2 : x < bswap (A + 1 - w) D w a + t) :
    (bswap (A + 1 - w) D w a + 1 = bswap (A + 1 - w) D w b ∨
      bswap (A + 1 - w) D w b + 1 = bswap (A + 1 - w) D w a) ↔ crossAdj A (A + D) a b := by
  unfold crossAdj bswap at *
  split_ifs at * <;> constructor <;> intro h <;> omega

/-- Far from the four endpoints of the crossing, the crossed graph agrees with the path. -/
lemma key_far (A D t x a b : ℕ)
    (hfar : (x + t ≤ A ∨ A + 1 + t ≤ x) ∧ (x + t ≤ A + 1 ∨ A + t ≤ x) ∧
      (x + t ≤ A + D ∨ A + D + 1 + t ≤ x) ∧ (x + t ≤ A + D + 1 ∨ A + D + t ≤ x))
    (hd1 : a < x + t) (hd2 : x < a + t) :
    (a + 1 = b ∨ b + 1 = a) ↔ crossAdj A (A + D) a b := by
  unfold crossAdj
  constructor <;> intro h <;> omega

/-! ### The crossed graph and block swaps on `Fin n` -/

lemma crossAdj_symm {A B u v : ℕ} (h : crossAdj A B u v) : crossAdj A B v u := by
  unfold crossAdj at *
  rcases h with ⟨h1, h2, h3, h4, h5⟩ | h | h | h | h
  · exact Or.inl ⟨h1.symm, h3, h2, h5, h4⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- The edge crossing `C((A, A+1), (B, B+1), P_n)` of the path on `Fin n` (Definition 2). -/
def crossGraph (n A B : ℕ) : SimpleGraph (Fin n) where
  Adj u v := crossAdj A B u.val v.val ∧ u ≠ v
  symm := ⟨fun _ _ h => ⟨crossAdj_symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

lemma crossGraph_adj {n A B : ℕ} {u v : Fin n} :
    (crossGraph n A B).Adj u v ↔ crossAdj A B u.val v.val ∧ u ≠ v := Iff.rfl

/-- The block swap `bswap P D w` as a permutation of `Fin n`. -/
def swapPerm (n P D w : ℕ) (hw : w ≤ D) (hn : P + D + w ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun u => ⟨bswap P D w u.val, bswap_lt hn u.2⟩)
    (fun u => Fin.ext (bswap_bswap hw u.val))

@[simp] lemma swapPerm_val {n P D w : ℕ} (hw : w ≤ D) (hn : P + D + w ≤ n) (u : Fin n) :
    (swapPerm n P D w hw hn u).val = bswap P D w u.val := rfl

@[simp] lemma swapPerm_symm {n P D w : ℕ} (hw : w ≤ D) (hn : P + D + w ≤ n) :
    (swapPerm n P D w hw hn).symm = swapPerm n P D w hw hn :=
  Function.Involutive.toPerm_symm _

/-- Distances bound differences of a potential that changes by at most one along edges. -/
lemma lt_of_edist_lt {V : Type*} {G : SimpleGraph V} (f : V → ℕ)
    (hf : ∀ y z, G.Adj y z → f z ≤ f y + 1 ∧ f y ≤ f z + 1) {x a : V} {t : ℕ}
    (h : G.edist x a < t) : f a < f x + t ∧ f x < f a + t := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt h)
  have hkt : k < t := by rw [← hk] at h; exact_mod_cast h
  have h1 := SimpleGraph.le_add_edist_of_lipschitz (G := G) (f := f) (fun y z h => (hf y z h).1) x a
  have h2 := SimpleGraph.le_add_edist_of_lipschitz (G := G) (f := f) (fun y z h => (hf y z h).1) a x
  rw [← hk] at h1
  rw [edist_comm, ← hk] at h2
  have h1' : f a ≤ f x + k := by exact_mod_cast h1
  have h2' : f x ≤ f a + k := by exact_mod_cast h2
  omega

/-- The labelled crossed graph agrees around `x` with the path relabelled by the block swap, as
soon as the arithmetic key lemma holds around `x`. -/
lemma gAgree_of_key {n A B P D w t : ℕ} (hw : w ≤ D) (hn : P + D + w ≤ n) {x : Fin n}
    (hx : bswap P D w x.val = x.val)
    (hkey : ∀ a b : ℕ, bswap P D w a < x.val + t → x.val < bswap P D w a + t →
      ((bswap P D w a + 1 = bswap P D w b ∨ bswap P D w b + 1 = bswap P D w a) ↔
        crossAdj A B a b)) :
    Cslib.Local.GAgree ((pathGraph n).comap (swapPerm n P D w hw hn)) (crossGraph n A B) x t := by
  intro a ha b
  have hd := lt_of_edist_lt (fun u => (swapPerm n P D w hw hn u).val) (fun y z h => by
    simp only [comap_adj, pathGraph_adj] at h; omega) ha
  simp only [swapPerm_val, hx] at hd
  simp only [comap_adj, pathGraph_adj, swapPerm_val, crossGraph_adj]
  rw [← hkey a.val b.val hd.1 hd.2]
  constructor
  · intro h
    refine ⟨h, fun hab => ?_⟩
    subst hab; omega
  · exact fun h => h.1

/-! ### Every node of the crossed graph accepts -/

section Accept

variable {Λ : Type} {F P : CProp Unit} {t : ℕ} (S : TPLS Unit Λ F P t) {n : ℕ}

/-- A node `x` of a graph `G'` on `Fin n` accepts if its ball agrees with the ball of `x` in the
accepted path relabelled by a permutation `τ` that preserves the labels. -/
lemma accept_of_perm {ℓ : Fin n → Λ} (hacc : ∀ v, S.verify (pathGraph n) (fun _ => ()) ℓ v)
    (τ : Equiv.Perm (Fin n)) (hτ : ∀ u, ℓ (τ u) = ℓ u) {G' : SimpleGraph (Fin n)} {x : Fin n}
    (hag : Cslib.Local.GAgree ((pathGraph n).comap τ) G' x t) :
    S.verify G' (fun _ => ()) ℓ x := by
  have h1 : S.verify ((pathGraph n).comap τ) (fun _ => ()) ℓ x := by
    have hb := ballIso_comap (t := t) τ.symm (pathGraph n) (fun u => (((), ℓ u) : Unit × Λ))
      (τ x)
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at hb
    refine S.isLocal _ _ _ (τ x) _ _ _ x ?_ (hacc _)
    convert hb using 2
    simp [hτ]
  exact S.isLocal _ _ _ x _ _ _ x (ballIso_of_gAgree hag fun _ _ => rfl) h1

/-- Block swaps between the two windows `[A-t, A+t+1]` and `[A+D-t, A+D+t+1]` preserve labels
that agree on the two windows. -/
lemma swap_label {ℓ : Fin n → Λ} {A D P w : ℕ}
    (hℓ : ∀ u v : Fin n, A ≤ u.val + t → u.val ≤ A + t + 1 → v.val = u.val + D → ℓ u = ℓ v)
    (hw : w ≤ D) (hn : P + D + w ≤ n) (hP : A ≤ P + t) (hPw : P + w ≤ A + t + 2) (u : Fin n) :
    ℓ (swapPerm n P D w hw hn u) = ℓ u := by
  by_cases h1 : P ≤ u.val ∧ u.val < P + w
  · exact (hℓ u _ (by omega) (by omega) (by simp [bswap, h1])).symm
  · by_cases h2 : P + D ≤ u.val ∧ u.val < P + D + w
    · exact hℓ _ u (by simp [bswap, h1, h2]; omega) (by simp [bswap, h1, h2]; omega)
        (by simp [bswap, h1, h2]; omega)
    · congr 1; ext; simp [bswap, h1, h2]

/-- All nodes of the crossed graph `C((A, A+1), (A+D, A+D+1), P_n)` accept the labelling `ℓ`
of the path, provided `ℓ` is accepted on the path and agrees on the two `t`-neighbourhoods
`[A-t, A+t+1]` and `[A+D-t, A+D+t+1]` of the crossed edges. -/
theorem crossGraph_accepts {ℓ : Fin n → Λ} (hacc : ∀ v, S.verify (pathGraph n) (fun _ => ()) ℓ v)
    {A D : ℕ} (htA : t ≤ A) (hD : 2 * t + 2 ≤ D) (hn : A + D + t + 2 ≤ n)
    (hℓ : ∀ u v : Fin n, A ≤ u.val + t → u.val ≤ A + t + 1 → v.val = u.val + D → ℓ u = ℓ v)
    (x : Fin n) : S.verify (crossGraph n A (A + D)) (fun _ => ()) ℓ x := by
  have hx := x.2
  by_cases c1 : x.val ≤ A ∧ A < x.val + t
  · -- path side, near `A`: swap `[A+1, A+w]` with `[A+D+1, A+D+w]`
    obtain ⟨w, hw⟩ : ∃ w, w + A = x.val + t := ⟨x.val + t - A, by omega⟩
    refine accept_of_perm S hacc _ (swap_label hℓ (P := A + 1) (w := w) (by omega) (by omega)
      (by omega) (by omega)) (gAgree_of_key (by omega) (by omega) (by unfold bswap; split_ifs <;> omega)
      fun a b h1 h2 => key_high_A A D t w x.val a b hD c1.1 hw h1 h2)
  by_cases c2 : A + 1 ≤ x.val ∧ x.val ≤ A + t
  · -- cycle side, near `A+1`: swap `[A+1-w, A]` with `[A+D+1-w, A+D]`
    obtain ⟨w, hw⟩ : ∃ w, w + x.val = A + 1 + t := ⟨A + 1 + t - x.val, by omega⟩
    refine accept_of_perm S hacc _ (swap_label hℓ (P := A + 1 - w) (w := w) (by omega)
      (by omega) (by omega) (by omega)) (gAgree_of_key (by omega) (by omega)
      (by unfold bswap; split_ifs <;> omega) fun a b h1 h2 => key_low_A A D t w x.val a b hD htA c2.1 hw h1 h2)
  by_cases c3 : x.val ≤ A + D ∧ A + D < x.val + t
  · -- cycle side, near `A+D`
    obtain ⟨w, hw⟩ : ∃ w, w + A + D = x.val + t := ⟨x.val + t - A - D, by omega⟩
    refine accept_of_perm S hacc _ (swap_label hℓ (P := A + 1) (w := w) (by omega) (by omega)
      (by omega) (by omega)) (gAgree_of_key (by omega) (by omega) (by unfold bswap; split_ifs <;> omega)
      fun a b h1 h2 => key_high_B A D t w x.val a b hD c3.1 hw h1 h2)
  by_cases c4 : A + D + 1 ≤ x.val ∧ x.val ≤ A + D + t
  · -- path side, near `A+D+1`
    obtain ⟨w, hw⟩ : ∃ w, w + x.val = A + D + 1 + t := ⟨A + D + 1 + t - x.val, by omega⟩
    refine accept_of_perm S hacc _ (swap_label hℓ (P := A + 1 - w) (w := w) (by omega)
      (by omega) (by omega) (by omega)) (gAgree_of_key (by omega) (by omega)
      (by unfold bswap; split_ifs <;> omega) fun a b h1 h2 => key_low_B A D t w x.val a b hD htA c4.1 hw h1 h2)
  · -- far from the crossing: the identity (a swap of width `0`)
    refine accept_of_perm S hacc _ (swap_label hℓ (P := A) (w := 0) (by omega) (by omega)
      (by omega) (by omega)) (gAgree_of_key (by omega) (by omega) (bswap_zero ..)
      fun a b h1 h2 => ?_)
    simp only [bswap_zero] at h1 h2 ⊢
    exact key_far A D t x.val a b (by omega) h1 h2

end Accept

/-! ### The cycle component -/

/-- The connected-graph family of Definition 6 (states are empty). -/
def ConnF : CProp Unit := fun _ G _ => G.Connected

/-- The predicate `acyclic` of Definition 6. -/
def AcycP : CProp Unit := fun _ G _ => G.IsAcyclic

section Cycle

variable {n A D : ℕ}

/-- The node set `[A+1, A+D]` of the cycle component of the crossed graph. -/
def cycSet (n A D : ℕ) : Set (Fin n) := {x | A + 1 ≤ x.val ∧ x.val ≤ A + D}

lemma cycSet_closed (a : Fin n) (ha : a ∈ cycSet n A D) (b : Fin n)
    (hab : (crossGraph n A (A + D)).Adj a b) : b ∈ cycSet n A D := by
  simp only [cycSet, Set.mem_ofPred_eq, crossGraph_adj, crossAdj] at *
  omega

/-- In a graph on `[A+1, A+D]` containing the edges between consecutive indices, every node is
reachable from `A+1`. -/
lemma reachable_of_consecutive {K : SimpleGraph (cycSet n A D)}
    (hK : ∀ u v : cycSet n A D, u.1.val + 1 = v.1.val → K.Adj u v) (a0 : cycSet n A D)
    (ha0 : a0.1.val = A + 1) : ∀ k (v : cycSet n A D), v.1.val = A + 1 + k → K.Reachable a0 v
  | 0, v, hv => by
    obtain rfl : a0 = v := Subtype.ext (Fin.ext (by omega))
    rfl
  | k + 1, v, hv => by
    have hlt : A + 1 + k < n := by have := v.1.2; omega
    let u : cycSet n A D := ⟨⟨A + 1 + k, hlt⟩, by have := v.2; simp [cycSet] at this ⊢; omega⟩
    exact (reachable_of_consecutive hK a0 ha0 k u rfl).trans (hK u v (by simp [u]; omega)).reachable

lemma cyc_adj_consecutive (u v : cycSet n A D) (h : u.1.val + 1 = v.1.val) :
    ((crossGraph n A (A + D)).induce (cycSet n A D)).Adj u v := by
  have hu := u.2; have hv := v.2
  simp only [cycSet, Set.mem_ofPred_eq] at hu hv
  simp only [comap_adj, Function.Embedding.subtype_apply, crossGraph_adj, crossAdj]
  refine ⟨Or.inl ⟨Or.inl h, ?_, ?_, ?_, ?_⟩, fun e => ?_⟩ <;> try omega

/-- The cycle component is connected. -/
lemma cyc_connected (hD : 2 ≤ D) (hn : A + D < n) :
    ((crossGraph n A (A + D)).induce (cycSet n A D)).Connected := by
  let a0 : cycSet n A D := ⟨⟨A + 1, by omega⟩, by simp [cycSet]; omega⟩
  have hr := reachable_of_consecutive (cyc_adj_consecutive) a0 rfl
  have : Nonempty (cycSet n A D) := ⟨a0⟩
  refine ⟨fun u v => (hr (u.1.val - A - 1) u ?_).symm.trans (hr (v.1.val - A - 1) v ?_)⟩
  · have := u.2; simp [cycSet] at this; omega
  · have := v.2; simp [cycSet] at this; omega

/-- The cycle component contains a cycle: the crossing edge `(A+D, A+1)` is not a bridge. -/
lemma cyc_not_acyclic (hD : 3 ≤ D) (hn : A + D < n) :
    ¬ ((crossGraph n A (A + D)).induce (cycSet n A D)).IsAcyclic := by
  intro hac
  let a0 : cycSet n A D := ⟨⟨A + 1, by omega⟩, by simp [cycSet]; omega⟩
  let b0 : cycSet n A D := ⟨⟨A + D, by omega⟩, by simp [cycSet]; omega⟩
  have hadj : ((crossGraph n A (A + D)).induce (cycSet n A D)).Adj a0 b0 := by
    simp only [comap_adj, Function.Embedding.subtype_apply, crossGraph_adj, crossAdj, a0, b0]
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, trivial⟩))), fun e => ?_⟩
    have := congrArg Fin.val e; simp at this; omega
  have hb := isAcyclic_iff_forall_adj_isBridge.1 hac hadj
  rw [isBridge_iff] at hb
  refine hb (reachable_of_consecutive (fun u v h => ?_) a0 rfl (D - 1) b0 (by simp [b0]; omega))
  refine ⟨cyc_adj_consecutive u v h, ?_⟩
  simp only [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, not_and]
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [a0, b0] at h <;> omega

end Cycle

/-- If an accepted labelling of the path carries the same labels on the `t`-neighbourhoods
`[A-t, A+t+1]` and `[A+D-t, A+D+t+1]` of two edges at distance `≥ 2t+1`, the scheme accepts the
cycle component of the crossed graph, contradicting soundness (the proof of Theorem 7). -/
theorem false_of_equal_windows {Λ : Type} {t : ℕ} (S : TPLS Unit Λ ConnF AcycP t) {n : ℕ}
    {ℓ : Fin n → Λ} (hacc : ∀ v, S.verify (pathGraph n) (fun _ => ()) ℓ v)
    {A D : ℕ} (htA : t ≤ A) (hD : 2 * t + 2 ≤ D) (hn : A + D + t + 2 ≤ n)
    (hℓ : ∀ u v : Fin n, A ≤ u.val + t → u.val ≤ A + t + 1 → v.val = u.val + D → ℓ u = ℓ v)
    (ht : 1 ≤ t) : False := by
  have hacc' := crossGraph_accepts S hacc htA hD hn hℓ
  have hcyc : ∀ w : cycSet n A D, S.verify ((crossGraph n A (A + D)).induce (cycSet n A D))
      (fun _ => ()) (ℓ ∘ Subtype.val) w := fun w =>
    S.isLocal _ _ _ w.1 _ _ _ w (ballIso_induce cycSet_closed _ w) (hacc' w.1)
  exact cyc_not_acyclic (by omega) (by omega)
    (S.sound _ _ (cyc_connected (by omega) (by omega)) _ hcyc)

/-! ### Theorem 7 -/

/-- Theorem 7 of [OPR], exact form: if a `t`-PLS for `acyclic` on connected graphs (`t ≥ 1`)
accepts a labelling of the `n`-node path with labels from a finite set `L`, then
`⌊n/(2t+2)⌋ - 1 ≤ |L|^(2t+2)`. (Pigeonhole over the `r = ⌊n/(2t+2)⌋ - 1` windows
`[q·i - t, q·i + t + 1]`, `q = 2t+2`, then `false_of_equal_windows`.) -/
theorem lowerBound_card {Λ : Type} {t : ℕ} (ht : 1 ≤ t) (S : TPLS Unit Λ ConnF AcycP t) {n : ℕ}
    (ℓ : Fin n → Λ) (hacc : ∀ v, S.verify (pathGraph n) (fun _ => ()) ℓ v) (L : Finset Λ)
    (hL : ∀ v, ℓ v ∈ L) : n / (2 * t + 2) - 1 ≤ L.card ^ (2 * t + 2) := by
  by_contra hlt
  rw [not_le] at hlt
  set q := 2 * t + 2 with hq
  set r := n / q - 1 with hr
  have hqn : q * (n / q) ≤ n := Nat.mul_div_le n q
  have hwin : ∀ i : Fin r, q * (i.val + 1) + q ≤ q * (n / q) := by
    intro i
    rw [← Nat.mul_add_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have hqi : ∀ i : Fin r, q ≤ q * (i.val + 1) := fun i => Nat.le_mul_of_pos_right _ (by omega)
  have hpos : ∀ (i : Fin r) (k : Fin q), q * (i.val + 1) - t + k.val < n := by
    intro i k
    have := hwin i; have := hqi i; have := k.2
    omega
  let f : Fin r → (Fin q → L) := fun i k => ⟨ℓ ⟨_, hpos i k⟩, hL _⟩
  have hcard : Fintype.card (Fin q → L) < Fintype.card (Fin r) := by
    simpa [Fintype.card_fun] using hlt
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have key : ∀ i j : Fin r, i.val < j.val → f i = f j → False := by
    intro i j hij hf
    have hij' : q * (i.val + 1) + q ≤ q * (j.val + 1) := by
      rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)
    have hj := hwin j
    have hi := hqi i
    have hlab : ∀ k : Fin q, ℓ ⟨_, hpos i k⟩ = ℓ ⟨_, hpos j k⟩ := fun k =>
      congrArg Subtype.val (congrFun hf k)
    refine false_of_equal_windows S hacc (A := q * (i.val + 1))
      (D := q * (j.val + 1) - q * (i.val + 1)) (by omega) (by omega) (by omega) ?_ ht
    intro u v h1 h2 h3
    have := hlab ⟨u.val + t - q * (i.val + 1), by omega⟩
    convert this using 2 <;> ext <;> simp only <;> omega
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h hf
  · exact key j i h hf.symm

/-- The bit strings of length at most `m`. -/
def bitStrings (m : ℕ) : Finset (List Bool) :=
  (Finset.range (m + 1)).biUnion fun k => Finset.univ.image fun v : Fin k → Bool => List.ofFn v

lemma mem_bitStrings {m : ℕ} {l : List Bool} (hl : l.length ≤ m) : l ∈ bitStrings m := by
  simp only [bitStrings, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨l.length, by omega, l.get, List.ofFn_get l⟩

lemma card_bitStrings (m : ℕ) : (bitStrings m).card ≤ 2 ^ (m + 1) - 1 := by
  have hsum : ∀ m, ∑ k ∈ Finset.range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      rw [pow_succ 2 (m + 1)]
      omega
  calc (bitStrings m).card ≤ ∑ k ∈ Finset.range (m + 1),
        (Finset.univ.image fun v : Fin k → Bool => List.ofFn v).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (m + 1), 2 ^ k := Finset.sum_le_sum fun k _ =>
        Finset.card_image_le.trans (by simp)
    _ = 2 ^ (m + 1) - 1 := hsum m

lemma pathGraph_isAcyclic (n : ℕ) : (pathGraph n).IsAcyclic :=
  isAcyclic_of_rank (fun u => u.val) (fun u v h => by rw [pathGraph_adj] at h; omega)
    (fun v u u' hu hu' h1 h2 => by
      rw [pathGraph_adj] at hu hu'; exact Fin.ext (by omega))

/-- **Theorem 7** of [OPR]: every `t`-round scheme (`t ≥ 1`) verifying `acyclic` on connected
graphs, whose honest labels on `n`-node graphs are bit strings of length `≤ L n`, satisfies
`⌊n/(2t+2)⌋ - 1 ≤ (2^(L n + 1) - 1)^(2t+2)`, hence
`log₂(⌊n/(2t+2)⌋ - 1) < (2t+2)(L n + 1)`, i.e. `L n = Ω(log n / t)`. -/
theorem theorem_7 {t : ℕ} (ht : 1 ≤ t) (S : TPLS Unit (List Bool) ConnF AcycP t) (L : ℕ → ℕ)
    (hS : S.CostLE List.length L) (n : ℕ) :
    n / (2 * t + 2) - 1 ≤ (2 ^ (L n + 1) - 1) ^ (2 * t + 2) ∧
      Nat.log 2 (n / (2 * t + 2) - 1) < (2 * t + 2) * (L n + 1) := by
  have h1 : n / (2 * t + 2) - 1 ≤ (2 ^ (L n + 1) - 1) ^ (2 * t + 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hconn : ConnF _ (pathGraph (m + 1)) (fun _ => ()) := pathGraph_connected m
    have hacyc : AcycP _ (pathGraph (m + 1)) (fun _ => ()) := pathGraph_isAcyclic _
    have hacc := S.complete _ _ hconn hacyc
    have hlen := hS (pathGraph (m + 1)) (fun _ => ()) hconn hacyc
    simp only [Fintype.card_fin] at hlen
    refine (lowerBound_card ht S _ hacc (bitStrings (L (m + 1)))
      fun v => mem_bitStrings (hlen v)).trans (Nat.pow_le_pow_left (card_bitStrings _) _)
  refine ⟨h1, ?_⟩
  rcases Nat.eq_zero_or_pos (n / (2 * t + 2) - 1) with h0 | hpos
  · rw [h0]; simp
  rw [Nat.log_lt_iff_lt_pow (by norm_num) (by omega)]
  calc n / (2 * t + 2) - 1 ≤ (2 ^ (L n + 1) - 1) ^ (2 * t + 2) := h1
    _ < (2 ^ (L n + 1)) ^ (2 * t + 2) :=
        Nat.pow_lt_pow_left (by have := Nat.one_le_two_pow (n := L n + 1); omega) (by omega)
    _ = 2 ^ ((2 * t + 2) * (L n + 1)) := by rw [← pow_mul, mul_comm]

end Podc.SpaceTimeVerification
