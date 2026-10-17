import Papers.PODC2020.TightBipartiteMatching.UpperBoundRun

/-!
# The upper bound of §5

Brandt–Olivetti, *Truly Tight-in-Δ Bounds for Bipartite Maximal Matching and Variants*, PODC 2020,
§5.

**Theorem** (`upper_bound`). For `1 ≤ y ≤ d`, `x ≤ Δ = d + 1`, the encoded bipartite `x`-maximal
`y`-matching problem `Φ^W_Δ(x, y)` can be solved by a white algorithm in `T_Δ(x, y)` rounds in the
port-numbering model, on every `Δ`-regular port-numbered (multi)graph with a given proper
2-colouring.

The algorithm is the proposal algorithm of `UpperBoundRun` (`k = ⌈(Δ - x)/y⌉`):

* if `⌈(Δ - x)/y⌉ < ⌈Δ/y⌉`: white nodes are active in rounds `0, 2, …`, and we run `2k` rounds;
* otherwise: black nodes are active in rounds `0, 2, …`, and we run `2k - 1` rounds (this solves
  the `x = 0` problem).

At the end, a white node outputs (`out`): `M` on its matched ports and `O` elsewhere; if it is
unmatched but has received proposals (in the last round) it accepts one of them (`M` there, `O`
elsewhere); otherwise it outputs `P` on the ports over which it proposed and `X` elsewhere (first
case), or `P` on all ports (second case: then all its neighbours are matched).
-/

namespace TightBipartiteMatching

namespace UpperBound

open Finset Cslib.PortNumbering Cslib.PortNumbering.Algorithm

/-- The output of a white node at the end of the algorithm. -/
def out (allP : Bool) (s : St) : ℕ → Lab := fun i =>
  if s.M ∪ s.acc = ∅ then (if allP then .P else if i ∈ s.S then .P else .X)
  else if i ∈ s.M ∪ s.acc then .M else .O

theorem out_M {allP : Bool} {s : St} {i : ℕ} : out allP s i = .M ↔ i ∈ s.M ∪ s.acc := by
  unfold out
  split_ifs with h1 h2 h3 <;> simp_all

theorem out_P {allP : Bool} {s : St} {i : ℕ} :
    out allP s i = .P ↔ s.M ∪ s.acc = ∅ ∧ (allP = true ∨ i ∈ s.S) := by
  unfold out
  split_ifs with h1 h2 h3 <;> simp_all

theorem out_X {allP : Bool} {s : St} {i : ℕ} (h : out allP s i = .X) : s.M ∪ s.acc = ∅ := by
  unfold out at h
  split_ifs at h with h1
  exact h1

theorem out_ne_Z {allP : Bool} {s : St} {i : ℕ} : out allP s i ≠ .Z := by
  unfold out
  split_ifs <;> simp

theorem out_ne_O {allP : Bool} {s : St} {i : ℕ} (h : s.M ∪ s.acc = ∅) : out allP s i ≠ .O := by
  unfold out
  split_ifs <;> simp_all

theorem count_map_range (τ : ℕ → Lab) (n : ℕ) (ℓ : Lab) :
    ((Multiset.range n).map τ).count ℓ = ((range n).filter fun i => τ i = ℓ).card := by
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val, Finset.range_val]
  congr 1
  exact Multiset.filter_congr fun _ _ => eq_comm

theorem count_map_range_eq_zero {τ : ℕ → Lab} {n : ℕ} {ℓ : Lab} (h : ∀ i < n, τ i ≠ ℓ) :
    ((Multiset.range n).map τ).count ℓ = 0 :=
  Multiset.count_eq_zero.2 fun hm => by
    obtain ⟨i, hi, he⟩ := Multiset.mem_map.1 hm
    exact h i (Multiset.mem_range.1 hi) he

theorem card_filter_mem {n : ℕ} {A : Finset ℕ} (hA : A ⊆ range n) :
    ((range n).filter (· ∈ A)).card = A.card := by
  rw [filter_mem_eq_inter, inter_eq_right.2 hA]

section Final

variable {V : Type} {G : PNGraph V} {d x y : ℕ} {a0 : Bool} {col : V → Bool}

/-- Correctness of the output, assuming that white is the colour active in round `T` and that
enough proposals have been made. -/
theorem final (hy1 : 1 ≤ y) (hyd : y ≤ d + 1) (hx : x ≤ d + 1) (hdeg : ∀ v, G.deg v = d + 1)
    (hcol : ∀ v i, i < d + 1 → col (G.nbr v i) = !col v) {T : ℕ} {c : V → St}
    (h : Inv G (d + 1) y a0 col T c) (hT : act a0 T = true) (allP : Bool)
    (hW : allP = false → d + 1 - x ≤ y * nact a0 true T)
    (hB : d + 1 - x ≤ y * nact a0 false T)
    (hAll : allP = true → d + 1 ≤ y * nact a0 false T) :
    (∀ v, col v = true → mset (fun k : Fin (d + 1) => out allP (c v) k) ∈ (Phi d x y).W) ∧
    (∀ u, col u = false →
      mset (fun k : Fin (d + 1) => out allP (c (G.nbr u k)) (G.rport u k)) ∈ (Phi d x y).B) := by
  have nn : ∀ v i, i < d + 1 → G.nbr (G.nbr v i) (G.rport v i) = v :=
    fun v i hi => G.nbr_nbr (by rw [hdeg]; exact hi)
  have rr : ∀ v i, i < d + 1 → G.rport (G.nbr v i) (G.rport v i) = i :=
    fun v i hi => G.rport_rport (by rw [hdeg]; exact hi)
  have rl : ∀ v i, i < d + 1 → G.rport v i < d + 1 := fun v i hi => by
    have := G.rport_lt (v := v) (i := i) (by rw [hdeg]; exact hi)
    rwa [hdeg] at this
  constructor
  · -- white nodes
    intro v hv
    rw [show mset (fun k : Fin (d + 1) => out allP (c v) k) =
      (Multiset.range (d + 1)).map (out allP (c v)) from mset_eq_map_range _]
    have hcard : Multiset.card ((Multiset.range (d + 1)).map (out allP (c v))) = d + 1 := by
      simp
    have hZ := count_map_range_eq_zero (τ := out allP (c v)) (n := d + 1) (ℓ := .Z)
      fun i _ => out_ne_Z
    by_cases hN : (c v).M ∪ (c v).acc = ∅
    · obtain ⟨hMv, hRv⟩ := St.union_acc_eq_empty.1 hN
      refine phiW_unmatched hx hcard
        (count_map_range_eq_zero fun i _ h' => by rw [out_M, hN] at h'; simp at h') hZ
        (count_map_range_eq_zero fun i _ => out_ne_O hN) ?_
      rw [count_map_range]
      cases allP
      · rw [filter_congr (q := (· ∈ (c v).S)) (fun i _ => by rw [out_P]; simp [hN]),
          card_filter_mem (h.S_sub v)]
        have := h.count v hMv hRv
        rw [hv] at this
        have := hW rfl
        omega
      · rw [filter_true_of_mem (fun i _ => out_P.2 ⟨hN, Or.inl rfl⟩), card_range]
        omega
    · have hNsub : (c v).M ∪ (c v).acc ⊆ range (d + 1) :=
        union_subset (h.M_sub v) ((St.acc_subset _).trans (h.R_sub v))
      have hNcard : ((c v).M ∪ (c v).acc).card ≤ y := by
        by_cases hM : (c v).M = ∅
        · rw [hM, empty_union, St.acc, ite_eq_left hM]
          exact (card_pick_le _).trans hy1
        · rw [St.acc, ite_eq_right hM, union_empty]; exact h.M_card v
      have hcM : ((Multiset.range (d + 1)).map (out allP (c v))).count .M =
          ((c v).M ∪ (c v).acc).card := by
        rw [count_map_range, filter_congr (q := (· ∈ (c v).M ∪ (c v).acc))
          (fun i _ => out_M), card_filter_mem hNsub]
      refine phiW_matched hy1 hyd hcard ?_ (hcM ▸ hNcard) hZ
        (count_map_range_eq_zero fun i _ h' => hN (out_P.1 h').1)
      rw [hcM]
      exact card_pos.2 (nonempty_iff_ne_empty.2 hN)
  · -- black nodes
    intro u hu
    set τ : ℕ → Lab := fun i => out allP (c (G.nbr u i)) (G.rport u i) with hτ
    rw [show mset (fun k : Fin (d + 1) => out allP (c (G.nbr u k)) (G.rport u k)) =
      (Multiset.range (d + 1)).map τ from mset_eq_map_range τ]
    have hcard : Multiset.card ((Multiset.range (d + 1)).map τ) = d + 1 := by simp
    have hu' : col u ≠ act a0 T := by rw [hT, hu]; decide
    have hw : ∀ i, i < d + 1 → col (G.nbr u i) = act a0 T := fun i hi => by
      rw [hcol u i hi, hu, hT]; rfl
    have hZ : ((Multiset.range (d + 1)).map τ).count .Z = 0 :=
      count_map_range_eq_zero fun i _ => out_ne_Z
    -- an `M` on the edge behind port `i` of `u`
    have hMcase : ∀ i, i < d + 1 → τ i = .M →
        i ∈ (c u).M ∨ ((c u).M = ∅ ∧ i ∈ (c u).B) := by
      intro i hi hM
      rw [hτ] at hM
      rcases mem_union.1 (out_M.1 hM) with hj | hj
      · have := (h.cons (G.nbr u i) (G.rport u i) (rl u i hi)).1 hj
        rw [nn u i hi, rr u i hi] at this
        exact Or.inl this
      · obtain ⟨hMw, hp⟩ := St.mem_acc.1 hj
        have := h.recv _ _ (hw i hi) hMw (pick_subset _ hp)
        rw [nn u i hi, rr u i hi] at this
        exact Or.inr this
    by_cases hMu : (c u).M = ∅
    · have hRu := h.passive u hu' hMu
      have hcnt := h.count u hMu hRu
      rw [hu] at hcnt
      have hcM : ((Multiset.range (d + 1)).map τ).count .M ≤ y := by
        rw [count_map_range]
        refine le_trans (card_le_card fun i hi => ?_) (h.B_card u)
        rw [mem_filter, mem_range] at hi
        rcases hMcase i hi.1 hi.2 with h1 | h1
        · rw [hMu] at h1; exact absurd h1 (notMem_empty _)
        · exact h1.2
      by_cases hM1 : 1 ≤ ((Multiset.range (d + 1)).map τ).count .M
      · exact phiB_matched hy1 hyd hcard hM1 hcM hZ
      · refine phiB_unmatched hx hcard (by omega) hZ ?_ ?_
        · -- no `P` next to an unmatched black node
          refine count_map_range_eq_zero fun i hi hP => ?_
          rw [hτ] at hP
          obtain ⟨hN, hor⟩ := out_P.1 hP
          obtain ⟨hMw, hRw⟩ := St.union_acc_eq_empty.1 hN
          rcases hor with hall | hjS
          · have := hAll hall
            have hS : (c u).S = range (d + 1) :=
              eq_of_subset_of_card_le (h.S_sub u) (by rw [card_range]; omega)
            have hiS : i ∈ (c u).S := by rw [hS]; exact mem_range.2 hi
            rcases h.sent u i hiS with h1 | h1
            · exact h1 hMw
            · rw [hRw] at h1; exact notMem_empty _ h1
          · rcases h.sent _ _ hjS with h1 | h1
            · rw [nn u i hi] at h1; exact h1 hMu
            · rw [nn u i hi, rr u i hi, hRu] at h1; exact notMem_empty _ h1
        · -- at most `x` labels `X`
          rw [count_map_range]
          have hsub : (range (d + 1)).filter (fun i => τ i = .X) ⊆ range (d + 1) \ (c u).S := by
            intro i hi
            rw [mem_filter] at hi
            refine mem_sdiff.2 ⟨hi.1, fun hiS => ?_⟩
            have hX := hi.2
            rw [hτ] at hX
            obtain ⟨hMw, hRw⟩ := St.union_acc_eq_empty.1 (out_X hX)
            rcases h.sent u i hiS with h1 | h1
            · exact h1 hMw
            · rw [hRw] at h1; exact notMem_empty _ h1
          have := card_le_card hsub
          rw [card_sdiff_of_subset (h.S_sub u), card_range] at this
          omega
    · have hcM : ((Multiset.range (d + 1)).map τ).count .M = (c u).M.card := by
        rw [count_map_range, ← card_filter_mem (h.M_sub u)]
        congr 1
        refine filter_congr fun i hi => ⟨fun hM => ?_, fun hiM => ?_⟩
        · rcases hMcase i (mem_range.1 hi) hM with h1 | h1
          · exact h1
          · exact absurd h1.1 hMu
        · rw [hτ]
          exact out_M.2 (mem_union_left _ ((h.cons u i (mem_range.1 hi)).1 hiM))
      refine phiB_matched hy1 hyd hcard ?_ (hcM ▸ h.M_card u) hZ
      rw [hcM]
      exact card_pos.2 (nonempty_iff_ne_empty.2 hMu)

end Final

/-- The algorithm: start from the initial states, run the local process `step` for `T` rounds,
and output with `out`. -/
def alg (d y : ℕ) (a0 allP : Bool) (T : ℕ) : Algorithm Bool (ℕ → Lab) :=
  ((ofFun fun (_ : ℕ) (c : Bool) => St.init c).seq 0 (ofLocal (step (d + 1) y a0))).seq T
    (ofFun fun (_ : ℕ) (s : St) => out allP s)

theorem eval_alg {V : Type} (G : PNGraph V) (col : V → Bool) (d y : ℕ) (a0 allP : Bool) (T : ℕ)
    (v : V) : (alg d y a0 allP T).eval G T col v = out allP (cfg G (d + 1) y a0 col T v) := by
  have h1 := eval_seq ((ofFun fun (_ : ℕ) (c : Bool) => St.init c).seq 0
    (ofLocal (step (d + 1) y a0))) T (ofFun fun (_ : ℕ) (s : St) => out allP s) G 0 col
  have h2 := eval_seq (ofFun fun (_ : ℕ) (c : Bool) => St.init c) 0
    (ofLocal (step (d + 1) y a0)) G T col
  rw [Nat.zero_add] at h2
  unfold alg
  show Algorithm.eval _ G (T + 0) col v = _
  rw [h1, eval_ofFun, h2, eval_ofLocal]
  rfl

theorem act_two_mul (a0 : Bool) (k : ℕ) : act a0 (2 * k) = a0 := by simp [act]

theorem act_two_mul_add_one (a0 : Bool) (k : ℕ) : act a0 (2 * k + 1) = !a0 := by
  rw [act_succ, act_two_mul]

theorem nact_two_mul (a0 c : Bool) (k : ℕ) : nact a0 c (2 * k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, nact, nact, ih, act_two_mul_add_one,
      act_two_mul]
    cases a0 <;> cases c <;> simp

theorem nact_two_mul_add_one (a0 : Bool) (k : ℕ) : nact a0 a0 (2 * k + 1) = k + 1 := by
  rw [nact, nact_two_mul, act_two_mul]; simp

theorem le_mul_cdiv (a y : ℕ) (hy : 1 ≤ y) : a ≤ y * cdiv a y := by
  unfold cdiv
  have h1 := Nat.div_add_mod (a + y - 1) y
  have h2 := Nat.mod_lt (a + y - 1) (show y > 0 by omega)
  omega

end UpperBound

open UpperBound Cslib.PortNumbering in
/-- Section 5 of [Brandt–Olivetti, PODC 2020]: upper bound. For `1 ≤ y < Δ = d + 1` and
`0 ≤ x ≤ Δ`, the (encoded) bipartite `x`-maximal `y`-matching problem `Φ^W_Δ(x, y)` is solved by a
white algorithm in `T_Δ(x, y)` rounds on every `Δ`-regular port-numbered graph with a proper
2-colouring given as input (`true` = white): the output of white node `v` on port `k` is the label
of the edge behind port `k`; the configuration of a white node satisfies the white constraint, and
the configuration of a black node `u` (the labels its white neighbours put on the connecting edges)
satisfies the black constraint. -/
theorem upper_bound {d x y : ℕ} (hy1 : 1 ≤ y) (hy : y ≤ d) (hx : x ≤ d + 1) :
    ∃ A : Algorithm Bool (ℕ → Lab), ∀ {V : Type} (G : PNGraph V) (col : V → Bool),
      (∀ v, G.deg v = d + 1) → (∀ v i, i < d + 1 → col (G.nbr v i) = !col v) →
      (∀ v, col v = true →
        mset (fun k : Fin (d + 1) => A.eval G (Tval (d + 1) x y) col v k) ∈ (Phi d x y).W) ∧
      (∀ u, col u = false →
        mset (fun k : Fin (d + 1) => A.eval G (Tval (d + 1) x y) col (G.nbr u k) (G.rport u k)) ∈
          (Phi d x y).B) := by
  obtain ⟨k, hk⟩ : ∃ k, k = cdiv (d + 1 - x) y := ⟨_, rfl⟩
  have hkx : d + 1 - x ≤ y * k := hk ▸ le_mul_cdiv _ _ hy1
  by_cases hcase : k < cdiv (d + 1) y
  · -- white starts; `2k` rounds
    have hT : Tval (d + 1) x y = 2 * k := by
      rw [Tval, ← hk, ite_eq_left hcase]
    refine ⟨alg d y true false (2 * k), fun G col hdeg hcol => ?_⟩
    rw [hT]
    simp only [eval_alg]
    refine final hy1 (by omega) hx hdeg hcol (inv_cfg G (d + 1) y true col hy1 hdeg hcol _)
      (act_two_mul _ _) false ?_ ?_ ?_
    · intro _; rw [nact_two_mul]; exact hkx
    · rw [nact_two_mul]; exact hkx
    · intro h; cases h
  · -- black starts; `2k - 1` rounds, solving the `x = 0` problem
    have hΔ : d + 1 ≤ y * k :=
      (le_mul_cdiv (d + 1) y hy1).trans (Nat.mul_le_mul_left y (not_lt.1 hcase))
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; simp at hΔ)
    have hT : Tval (d + 1) x y = 2 * (k - 1) + 1 := by
      rw [Tval, ← hk, ite_eq_right hcase]; omega
    refine ⟨alg d y false true (2 * (k - 1) + 1), fun G col hdeg hcol => ?_⟩
    rw [hT]
    simp only [eval_alg]
    have hn : nact false false (2 * (k - 1) + 1) = k := by
      rw [nact_two_mul_add_one]; omega
    refine final hy1 (by omega) hx hdeg hcol (inv_cfg G (d + 1) y false col hy1 hdeg hcol _)
      (by rw [act_two_mul_add_one]; rfl) true (fun h => by cases h) ?_ ?_
    · rw [hn]; omega
    · intro _; rw [hn]; exact hΔ

end TightBipartiteMatching
