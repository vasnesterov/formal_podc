import Papers.PODC2026.SinklessOrientation.Basic

/-!
# Tightness of Theorem 2.1: a lower bound for sinksparse orientations

After Theorem 2.1 (a `k`-sinksparse orientation in `O(k)` rounds), Nolin remarks that this is
"obviously tight, even in LOCAL", by a standard indistinguishability argument. We formalize it:

* `sinkSparse_lower_bound`: every `T`-round LOCAL orientation algorithm with `2 * T + 2 ≤ k` fails
  to be `k`-sinksparse on some path with `k + 1` nodes (plus isolated nodes), provided there are at
  least `2 * T + 2 + 3 * k` node identifiers.
* `sinkSparse_rounds_ge`: hence an algorithm that is `k`-sinksparse on all graphs needs
  `T > (k - 2) / 2` rounds (`k < 2 * T + 2`).

## Proof

In a path on `k + 1` nodes all distances are `≤ k`, so a `k`-sinksparse orientation has at most one
sink; an interior *source* (both incident edges outgoing) would produce two sinks, one on each side.

Let `a₀, …, a_{2T+1}` be fixed identifiers. We consider the sequence of positions
`a₀ … a_{2T+1} | k fillers | a_{2T+1} … a₀ | k fillers | a₀ … a_{2T+1} | k fillers` (`seq`), and the
paths `win S k j` through the positions `j, …, j + k` (*windows*); repeated identifiers are more than
`k` positions apart, so every window is a genuine path. By locality the orientation of the edge
between positions `p` and `p + 1` is the same in all windows containing `[p - T, p + T]`; call it
`dirAt p` ("points right"). The absence of sources forces `dirAt` to be antitone. But the edge
`a_T a_{T+1}` is seen identically (radius `T` around `a_T`) in the three blocks, so it points right in
blocks 1 and 3 iff it points left in block 2 — contradicting antitonicity.
-/

namespace SinklessOrientation

open SimpleGraph

variable {V : Type*}

/-- The path along the list `l`: two nodes are adjacent iff they are consecutive in `l`; nodes not
in `l` are isolated. -/
def pathOn (l : List V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => ∃ i, ∃ h : i + 1 < l.length, x = l[i] ∧ y = l[i + 1]

lemma Orientation.out_iff_not_out {G : SimpleGraph V} (o : Orientation G) {u v : V}
    (h : G.Adj u v) : o.out u v ↔ ¬ o.out v u :=
  ⟨fun h' => o.not_out_of_out h', fun h' => (o.out_or_out h).resolve_right h'⟩

namespace LowerBound

/-! ### Windows of a sequence -/

/-- The path through the positions `j, j + 1, …, j + k` of the sequence `S`. -/
def win (S : ℕ → V) (k j : ℕ) : SimpleGraph V :=
  pathOn ((List.range (k + 1)).map fun i => S (j + i))

/-- `S` is injective on the positions `j, …, j + k`. -/
def WinInj (S : ℕ → V) (k j : ℕ) : Prop :=
  ∀ p q, j ≤ p → p ≤ j + k → j ≤ q → q ≤ j + k → S p = S q → p = q

variable {S : ℕ → V} {k j : ℕ}

lemma win_adj {x y : V} : (win S k j).Adj x y ↔ x ≠ y ∧ ∃ i, i < k ∧
    ((x = S (j + i) ∧ y = S (j + i + 1)) ∨ (y = S (j + i) ∧ x = S (j + i + 1))) := by
  simp only [win, pathOn, fromRel_adj, List.length_map, List.length_range, List.getElem_map,
    List.getElem_range]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (⟨i, hi, h1, h2⟩ | ⟨i, hi, h1, h2⟩)
    · exact ⟨i, by omega, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨i, by omega, Or.inr ⟨h1, h2⟩⟩
  · rintro ⟨i, hi, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨i, by omega, h1, h2⟩
    · exact Or.inr ⟨i, by omega, h1, h2⟩

/-- The neighbours of the node at position `q` of a window: the nodes at positions `q ± 1` inside
the window. -/
lemma adj_iff (hj : WinInj S k j) {q : ℕ} (h1 : j ≤ q) (h2 : q ≤ j + k) (y : V) :
    (win S k j).Adj (S q) y ↔ (q < j + k ∧ y = S (q + 1)) ∨ (j < q ∧ y = S (q - 1)) := by
  rw [win_adj]
  constructor
  · rintro ⟨-, i, hi, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩
    · have := hj _ _ h1 h2 (by omega) (by omega) e1
      subst this
      exact Or.inl ⟨by omega, e2⟩
    · have := hj _ _ h1 h2 (by omega) (by omega) e2
      subst this
      refine Or.inr ⟨by omega, ?_⟩
      rw [e1]; congr 1
  · rintro (⟨h3, rfl⟩ | ⟨h3, rfl⟩)
    · refine ⟨fun h => ?_, q - j, by omega, Or.inl ⟨by congr 1; omega, by congr 1; omega⟩⟩
      have := hj _ _ h1 h2 (by omega) (by omega) h
      omega
    · refine ⟨fun h => ?_, q - 1 - j, by omega, Or.inr ⟨by congr 1; omega, by congr 1; omega⟩⟩
      have := hj _ _ h1 h2 (by omega) (by omega) h
      omega

lemma adj_succ (hj : WinInj S k j) {q : ℕ} (h1 : j ≤ q) (h2 : q < j + k) :
    (win S k j).Adj (S q) (S (q + 1)) :=
  (adj_iff hj h1 h2.le _).2 (Or.inl ⟨h2, rfl⟩)

/-- A walk of length `ℓ` from position `p` of a window ends at a position at most `ℓ` away. -/
lemma walk_pos (hj : WinInj S k j) {u x : V} (w : (win S k j).Walk u x) :
    ∀ p, j ≤ p → p ≤ j + k → u = S p →
      ∃ q, j ≤ q ∧ q ≤ j + k ∧ x = S q ∧ q ≤ p + w.length ∧ p ≤ q + w.length := by
  induction w with
  | nil => intro p h1 h2 hu; exact ⟨p, h1, h2, hu, by simp, by simp⟩
  | cons h w ih =>
    intro p h1 h2 hu
    subst hu
    rw [adj_iff hj h1 h2] at h
    rcases h with ⟨h3, rfl⟩ | ⟨h3, rfl⟩
    · obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ := ih (p + 1) (by omega) (by omega) rfl
      exact ⟨q, hq1, hq2, hq3, by simp; omega, by simp; omega⟩
    · obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ := ih (p - 1) (by omega) (by omega) rfl
      exact ⟨q, hq1, hq2, hq3, by simp; omega, by simp; omega⟩

lemma exists_pos_of_edist_lt (hj : WinInj S k j) {p T : ℕ} (h1 : j ≤ p) (h2 : p ≤ j + k) {x : V}
    (hx : (win S k j).edist (S p) x < T) :
    ∃ q, j ≤ q ∧ q ≤ j + k ∧ x = S q ∧ q < p + T ∧ p < q + T := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hx)
  obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_coe hn.symm
  have hnT : n < T := by rw [← hn] at hx; exact_mod_cast hx
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ := walk_pos hj w p h1 h2 rfl
  exact ⟨q, hq1, hq2, hq3, by omega, by omega⟩

lemma edist_le (hj : WinInj S k j) : ∀ d p, j ≤ p → p + d ≤ j + k →
    (win S k j).edist (S p) (S (p + d)) ≤ d := by
  intro d
  induction d with
  | zero => intro p _ _; simp
  | succ d ih =>
    intro p h1 h2
    calc (win S k j).edist (S p) (S (p + (d + 1)))
        ≤ (win S k j).edist (S p) (S (p + d)) + 1 :=
          edist_le_add_one_of_adj (adj_succ hj (by omega) (by omega))
      _ ≤ d + 1 := by gcongr; exact ih p h1 (by omega)
      _ = ((d + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- Two windows look the same within radius `T` of the node at position `p` of the first one, if
every node `S q` at distance `< T` from it occurs in the second window (at an interior position
`q'`) with the same pair of neighbours. -/
lemma gagree_win {j' p T : ℕ} (hj : WinInj S k j) (hj' : WinInj S k j')
    (hp1 : j + T ≤ p) (hp2 : p + T ≤ j + k)
    (hc : ∀ q, p < q + T → q < p + T → ∃ q', j' < q' ∧ q' < j' + k ∧ S q' = S q ∧
      ((S (q' + 1) = S (q + 1) ∧ S (q' - 1) = S (q - 1)) ∨
        (S (q' + 1) = S (q - 1) ∧ S (q' - 1) = S (q + 1)))) :
    GAgree (win S k j) (win S k j') (S p) T := by
  intro x hx y
  obtain ⟨q, hq1, hq2, rfl, hq3, hq4⟩ := exists_pos_of_edist_lt hj (by omega) (by omega) hx
  obtain ⟨q', h1, h2, h3, h4⟩ := hc q hq4 hq3
  have e1 := adj_iff hj hq1 hq2 y
  have e2 := adj_iff hj' (q := q') (by omega) (by omega) y
  rw [e1, ← h3, e2]
  have a1 : q < j + k := by omega
  have a2 : j < q := by omega
  simp only [a1, a2, h1, h2, true_and]
  rcases h4 with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> rw [e3, e4]
  exact or_comm

/-! ### Sinks in a window -/

section Sinks

variable (hj : WinInj S k j) (o : Orientation (win S k j))
include hj

lemma step_left {c : ℕ} (h1 : j ≤ c) (h2 : c < j + k) (hout : o.out (S (c + 1)) (S c))
    (hns : ¬ o.IsSink (S c)) : j < c ∧ o.out (S c) (S (c - 1)) := by
  simp only [Orientation.IsSink, not_forall, not_not] at hns
  obtain ⟨u, hu⟩ := hns
  have := o.adj_of_out hu
  rw [adj_iff hj h1 h2.le] at this
  rcases this with ⟨-, rfl⟩ | ⟨h, rfl⟩
  · exact absurd hu (o.not_out_of_out hout)
  · exact ⟨h, hu⟩

lemma step_right {c : ℕ} (h1 : j ≤ c) (h2 : c + 1 ≤ j + k) (hout : o.out (S c) (S (c + 1)))
    (hns : ¬ o.IsSink (S (c + 1))) : c + 1 < j + k ∧ o.out (S (c + 1)) (S (c + 1 + 1)) := by
  simp only [Orientation.IsSink, not_forall, not_not] at hns
  obtain ⟨u, hu⟩ := hns
  have := o.adj_of_out hu
  rw [adj_iff hj (by omega) h2] at this
  rcases this with ⟨h, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨h, hu⟩
  · simp only [Nat.add_sub_cancel] at hu
    exact absurd hu (o.not_out_of_out hout)

/-- Following the edges to the left from an edge pointing left reaches a sink. -/
lemma exists_sink_left : ∀ c, j ≤ c → c < j + k → o.out (S (c + 1)) (S c) →
    ∃ r, j ≤ r ∧ r ≤ c ∧ o.IsSink (S r) := by
  intro c
  induction c with
  | zero =>
    intro h1 h2 hout
    by_cases hs : o.IsSink (S 0)
    · exact ⟨0, h1, le_rfl, hs⟩
    · have := step_left hj o h1 h2 hout hs; omega
  | succ c ih =>
    intro h1 h2 hout
    by_cases hs : o.IsSink (S (c + 1))
    · exact ⟨c + 1, h1, le_rfl, hs⟩
    · obtain ⟨h3, h4⟩ := step_left hj o h1 h2 hout hs
      simp only [Nat.add_sub_cancel] at h4
      obtain ⟨r, hr1, hr2, hr3⟩ := ih (by omega) (by omega) h4
      exact ⟨r, hr1, by omega, hr3⟩

/-- Following the edges to the right from an edge pointing right reaches a sink. -/
lemma exists_sink_right : ∀ d c, j ≤ c → c + 1 + d = j + k → o.out (S c) (S (c + 1)) →
    ∃ r, c + 1 ≤ r ∧ r ≤ j + k ∧ o.IsSink (S r) := by
  intro d
  induction d with
  | zero =>
    intro c h1 h2 hout
    by_cases hs : o.IsSink (S (c + 1))
    · exact ⟨c + 1, le_rfl, by omega, hs⟩
    · have := step_right hj o h1 (by omega) hout hs; omega
  | succ d ih =>
    intro c h1 h2 hout
    by_cases hs : o.IsSink (S (c + 1))
    · exact ⟨c + 1, le_rfl, by omega, hs⟩
    · obtain ⟨-, h4⟩ := step_right hj o h1 (by omega) hout hs
      obtain ⟨r, hr1, hr2, hr3⟩ := ih (c + 1) (by omega) (by omega) h4
      exact ⟨r, by omega, hr2, hr3⟩

/-- A `k`-sinksparse orientation of a window has no interior source. -/
lemma no_source (hsp : o.IsSinkSparse k) {c : ℕ} (h1 : j ≤ c) (h2 : c + 2 ≤ j + k)
    (hl : o.out (S (c + 1)) (S c)) (hr : o.out (S (c + 1)) (S (c + 1 + 1))) : False := by
  obtain ⟨r₁, hr₁, hr₁', hs₁⟩ := exists_sink_left hj o c h1 (by omega) hl
  obtain ⟨r₂, hr₂, hr₂', hs₂⟩ :=
    exists_sink_right hj o (j + k - (c + 1 + 1)) (c + 1) (by omega) (by omega) hr
  have hne : S r₁ ≠ S r₂ := fun h => by
    have := hj _ _ (by omega) (by omega) (by omega) (by omega) h; omega
  have hd := edist_le hj (r₂ - r₁) r₁ hr₁ (by omega)
  rw [show r₁ + (r₂ - r₁) = r₂ by omega] at hd
  have := hsp hs₁ hs₂ hne
  have : ((r₂ - r₁ : ℕ) : ℕ∞) ≤ k := by exact_mod_cast (by omega : r₂ - r₁ ≤ k)
  exact absurd (hd.trans this) (not_le.2 (by assumption))

end Sinks

/-! ### Direction of the edges along the sequence -/

/-- The edge between positions `p` and `p + 1` points right, in the window starting at `p - T`
(by locality, in every window containing positions `p - T, …, p + T`). -/
def dirAt (A : ∀ G : SimpleGraph V, Orientation G) (S : ℕ → V) (k T p : ℕ) : Prop :=
  (A (win S k (p - T))).out (S p) (S (p + 1))

section Dir

variable {A : ∀ G : SimpleGraph V, Orientation G} {T N : ℕ}

lemma out_win_iff (hA : IsLocal A T) {j' p : ℕ} (hj : WinInj S k j) (hj' : WinInj S k j')
    (h1 : j + T ≤ p) (h2 : p + T ≤ j + k) (h1' : j' + T ≤ p) (h2' : p + T ≤ j' + k) (v : V) :
    (A (win S k j)).out (S p) v ↔ (A (win S k j')).out (S p) v :=
  hA _ _ _ (gagree_win hj hj' h1 h2 fun q hq1 hq2 =>
    ⟨q, by omega, by omega, rfl, Or.inl ⟨rfl, rfl⟩⟩) v

variable (hA : IsLocal A T) (hk : 2 * T + 2 ≤ k) (hW : ∀ j, j + k < N → WinInj S k j)
  (H : ∀ j, j + k < N → (A (win S k j)).IsSinkSparse k)
include hA hk hW H

/-- No sources: `dirAt` is antitone (one step). -/
lemma dirAt_of_succ {q : ℕ} (hq : T ≤ q) (hqN : q + 1 - T + k < N)
    (hd : dirAt A S k T (q + 1)) : dirAt A S k T q := by
  have hj := hW (q - T) (by omega)
  have hj' := hW (q + 1 - T) hqN
  unfold dirAt at hd ⊢
  rw [out_win_iff hA hj' hj (by omega) (by omega) (by omega) (by omega)] at hd
  by_contra hnd
  have hadj := adj_succ hj (q := q) (by omega) (by omega)
  have hl := ((A _).out_or_out hadj).resolve_left hnd
  exact no_source hj (A _) (H _ (by omega)) (c := q) (by omega) (by omega) hl hd

lemma dirAt_anti : ∀ d p, T ≤ p → p + d - T + k < N → dirAt A S k T (p + d) → dirAt A S k T p := by
  intro d
  induction d with
  | zero => intro p _ _ h; exact h
  | succ d ih =>
    intro p h1 h2 h
    exact ih p h1 (by omega) (dirAt_of_succ hA hk hW H (q := p + d) (by omega) (by omega) h)

/-- The abstract contradiction: an edge pointing right at `P₁` and `P₃` but left at `P₂`, or
left at `P₁` and right at `P₂`, is impossible. -/
lemma false_of_dirAt {P₁ P₂ P₃ : ℕ} (h1 : T ≤ P₁) (h12 : P₁ ≤ P₂) (h23 : P₂ ≤ P₃)
    (hN : P₃ - T + k < N) (h13 : dirAt A S k T P₃ ↔ dirAt A S k T P₁)
    (h2 : dirAt A S k T P₂ ↔ ¬ dirAt A S k T P₁) : False := by
  by_cases d1 : dirAt A S k T P₁
  · have hd3 := h13.2 d1
    have := dirAt_anti hA hk hW H (P₃ - P₂) P₂ (by omega) (by omega)
      (by rw [show P₂ + (P₃ - P₂) = P₃ by omega]; exact hd3)
    exact h2.1 this d1
  · have := dirAt_anti hA hk hW H (P₂ - P₁) P₁ (by omega) (by omega)
      (by rw [show P₁ + (P₂ - P₁) = P₂ by omega]; exact h2.2 d1)
    exact d1 this

end Dir

/-! ### The three-copies sequence -/

/-- Index (into the identifiers `e`) of the node at position `p` of the sequence
`a₀ … a_{L-1} | fillers | a_{L-1} … a₀ | fillers | a₀ … a_{L-1} | fillers` with `L = 2 * T + 2`,
`a i = e i` and `k` fresh fillers in each filler block. -/
def idx (T k p : ℕ) : ℕ :=
  if p < 2 * T + 2 + k then p
  else if p < 2 * (2 * T + 2) + k then 2 * (2 * T + 2) + k - 1 - p
  else if p < 2 * (2 * T + 2) + 2 * k then p - (2 * T + 2)
  else if p < 3 * (2 * T + 2) + 2 * k then p - 2 * (2 * T + 2) - 2 * k
  else if p < 3 * (2 * T + 2) + 3 * k then p - 2 * (2 * T + 2)
  else 0

lemma idx_lt (T k p : ℕ) : idx T k p < 2 * T + 2 + 3 * k := by
  unfold idx; split_ifs <;> omega

lemma idx_inj {T k p q : ℕ} (h : idx T k p = idx T k q) (hpq : p ≤ q) (hqp : q ≤ p + k)
    (hq : q < 3 * (2 * T + 2) + 3 * k) : p = q := by
  unfold idx at h; split_ifs at h <;> omega

lemma idx_one {T k i : ℕ} (hi : i < 2 * T + 2 + k) : idx T k i = i := by
  unfold idx; rw [ite_eq_left_iff]; omega

lemma idx_two {T k p i : ℕ} (h : p + i = 4 * T + 3 + k) (hi : i < 2 * T + 2) : idx T k p = i := by
  unfold idx; split_ifs <;> omega

lemma idx_three {T k p i : ℕ} (h : p = i + (4 * T + 4 + 2 * k)) (hi : i < 2 * T + 2) :
    idx T k p = i := by
  unfold idx; split_ifs <;> omega

/-- The three-copies sequence of node identifiers. -/
def seq (T k : ℕ) (e : Fin (2 * T + 2 + 3 * k) → V) (p : ℕ) : V := e ⟨idx T k p, idx_lt T k p⟩

lemma seq_eq {T k : ℕ} (e : Fin (2 * T + 2 + 3 * k) → V) {a b : ℕ} (h : idx T k a = idx T k b) :
    seq T k e a = seq T k e b := by
  unfold seq; congr 1; exact Fin.ext h

lemma winInj_seq {T k : ℕ} {e : Fin (2 * T + 2 + 3 * k) → V} (he : Function.Injective e) {j : ℕ}
    (hj : j + k < 3 * (2 * T + 2) + 3 * k) : WinInj (seq T k e) k j := by
  intro p q h1 h2 h3 h4 h
  have h' := congrArg Fin.val (he h)
  simp only at h'
  rcases le_total p q with hpq | hpq
  · exact idx_inj h' hpq (by omega) (by omega)
  · exact (idx_inj h'.symm hpq (by omega) (by omega)).symm

end LowerBound

open LowerBound

/-- Tightness remark after Theorem 2.1 of [Nolin, PODC'26] ("this is obviously tight, even in
LOCAL"): if there are at least `2 * T + 2 + 3 * k` node identifiers and `2 * T + 2 ≤ k`, then every
`T`-round LOCAL orientation algorithm `A` produces, on some path with `k + 1` nodes (all other nodes
isolated), two distinct sinks at distance `≤ k`. Hence computing a `k`-sinksparse orientation
requires more than `(k - 2) / 2` rounds, matching the `O(k)` upper bound of Theorem 2.1 up to a
constant factor. -/
theorem sinkSparse_lower_bound (A : ∀ G : SimpleGraph V, Orientation G) {T k : ℕ}
    (hA : IsLocal A T) (hk : 2 * T + 2 ≤ k) (e : Fin (2 * T + 2 + 3 * k) → V)
    (he : Function.Injective e) :
    ∃ l : List V, l.Nodup ∧ l.length = k + 1 ∧ ¬ (A (pathOn l)).IsSinkSparse k := by
  by_contra hcon
  push Not at hcon
  have hW : ∀ j, j + k < 3 * (2 * T + 2) + 3 * k → WinInj (seq T k e) k j :=
    fun j hj => winInj_seq he hj
  have H : ∀ j, j + k < 3 * (2 * T + 2) + 3 * k → (A (win (seq T k e) k j)).IsSinkSparse k := by
    intro j hj
    refine hcon _ ?_ (by simp)
    refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    have := hW j hj _ _ (by omega) (by omega) (by omega) (by omega) hxy
    omega
  have hJ := hW (2 * T + k + 2) (by omega)
  refine false_of_dirAt hA hk hW H (P₁ := T) (P₂ := 3 * T + k + 2) (P₃ := 5 * T + 4 + 2 * k)
    le_rfl (by omega) (by omega) (by omega) ?_ ?_
  · -- the third copy of the edge `a_T a_{T+1}` is oriented like the first one
    unfold dirAt
    rw [show 5 * T + 4 + 2 * k - T = 4 * T + 4 + 2 * k by omega, Nat.sub_self,
      seq_eq e (a := 5 * T + 4 + 2 * k + 1) (b := T + 1)
        (by rw [idx_three (i := T + 1) (by omega) (by omega), idx_one (by omega)]),
      seq_eq e (a := 5 * T + 4 + 2 * k) (b := T)
        (by rw [idx_three (i := T) (by omega) (by omega), idx_one (by omega)])]
    refine (hA _ _ _ (gagree_win (hW 0 (by omega)) (hW _ (by omega)) (p := T) (by omega)
      (by omega) ?_) _).symm
    intro q hq1 hq2
    refine ⟨q + (4 * T + 4 + 2 * k), by omega, by omega, seq_eq e ?_, Or.inl ⟨seq_eq e ?_, seq_eq e ?_⟩⟩
    · rw [idx_three (i := q) (by omega) (by omega), idx_one (by omega)]
    · rw [idx_three (i := q + 1) (by omega) (by omega), idx_one (by omega)]
    · rw [idx_three (i := q - 1) (by omega) (by omega), idx_one (by omega)]
  · -- the second (reversed) copy is oriented the other way
    unfold dirAt
    have hadj := adj_succ hJ (q := 3 * T + k + 2) (by omega) (by omega)
    rw [show 3 * T + k + 2 - T = 2 * T + k + 2 by omega, Nat.sub_self,
      (A _).out_iff_not_out hadj,
      seq_eq e (a := 3 * T + k + 2 + 1) (b := T)
        (by rw [idx_two (i := T) (by omega) (by omega), idx_one (by omega)]),
      seq_eq e (a := 3 * T + k + 2) (b := T + 1)
        (by rw [idx_two (i := T + 1) (by omega) (by omega), idx_one (by omega)])]
    refine not_congr (hA _ _ _ (gagree_win (hW 0 (by omega)) hJ (p := T) (by omega)
      (by omega) ?_) _).symm
    intro q hq1 hq2
    refine ⟨4 * T + 3 + k - q, by omega, by omega, seq_eq e ?_, Or.inr ⟨seq_eq e ?_, seq_eq e ?_⟩⟩
    · rw [idx_two (i := q) (by omega) (by omega), idx_one (by omega)]
    · rw [idx_two (i := q - 1) (by omega) (by omega), idx_one (by omega)]
    · rw [idx_two (i := q + 1) (by omega) (by omega), idx_one (by omega)]

/-- Corollary: a `T`-round LOCAL algorithm that computes a `k`-sinksparse orientation on every
graph (with at least `2 * T + 2 + 3 * k` node identifiers available) satisfies `k < 2 * T + 2`,
i.e. `T > (k - 2) / 2`. -/
theorem sinkSparse_rounds_ge (A : ∀ G : SimpleGraph V, Orientation G) {T k : ℕ}
    (hsol : ∀ G, (A G).IsSinkSparse k) (hA : IsLocal A T) (e : Fin (2 * T + 2 + 3 * k) → V)
    (he : Function.Injective e) : k < 2 * T + 2 := by
  by_contra hk
  obtain ⟨l, -, -, hl⟩ := sinkSparse_lower_bound A hA (by omega) e he
  exact hl (hsol _)

/-- The same with infinitely many node identifiers. -/
theorem sinkSparse_rounds_ge' [Infinite V] (A : ∀ G : SimpleGraph V, Orientation G) {T k : ℕ}
    (hsol : ∀ G, (A G).IsSinkSparse k) (hA : IsLocal A T) : k < 2 * T + 2 :=
  sinkSparse_rounds_ge A hsol hA (fun i => Infinite.natEmbedding V i)
    ((Infinite.natEmbedding V).injective.comp Fin.val_injective)

end SinklessOrientation
