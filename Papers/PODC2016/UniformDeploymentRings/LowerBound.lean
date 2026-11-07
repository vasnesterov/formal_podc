import Papers.PODC2016.UniformDeploymentRings.Defs

/-!
# Uniform deployment of mobile agents in asynchronous rings — the `Ω(kn)` lower bound

Theorem 1 of [Shibata et al., PODC 2016]: when `k ≤ p·n` for a constant `p < 1`, solving uniform
deployment requires `Ω(kn)` total moves.

In a unidirectional ring an agent going from node `h` to node `t` makes at least
`(t - h : ZMod n).val` moves (the forward distance). We consider the initial configuration in which
the `k` agents occupy the block of nodes `0, 1, …, k-1` (agent `a` has home `a`), and an arbitrary
assignment `f` of agents to final nodes that forms a uniform deployment. Every algorithm solving
the problem from this configuration therefore makes at least `∑ a, (f a - a).val` moves in total.

Main results (`T = ∑ a, (f a - a).val`, the final nodes `f a` forming a uniform deployment):

* `theorem_1` : for `2 ≤ k` and `4k ≤ n`, `k·n ≤ 6·T` (the paper proves `16`); the constant `6`
  is optimal (`theorem_1_tight`: `n = 9`, `k = 2`).
* `theorem_1_general` : for every `k ≥ 2`, `3·k·(n - k - 1)² ≤ 64·n·T`.
* `theorem_1_of_le_mul` : for `p < 1`, `2 ≤ k ≤ p·n` and `(1 - p)·n ≥ 2`,
  `T ≥ 3(1-p)²/256 · k·n`, i.e. the paper's `Ω(kn)` for every constant `p < 1`.

The condition `(1 - p)·n ≥ 2` cannot be dropped: for `k = n - 1` every set of `k` distinct nodes is
a uniform deployment, so `T = 0` is possible (e.g. `n = 3`, `k = 2`, `p = 2/3`).

Proof technique: in a uniform deployment every `g = ⌈n/k⌉` consecutive nodes contain an agent
(`exists_sub_mem`), so each of the `m` disjoint windows `[n - (j+1)g, n - jg)` contains a final
node, reached by an agent from the block `0, …, k-1` with at least `n - (j+1)g - (k-1)` moves
(`sum_window_le_total`); the windows are summed in closed form (`two_mul_sum_window`).
-/

namespace Podc.UniformDeploymentRings

variable {n k : ℕ}

/-- In a uniform deployment, every occupied node `v` has another occupied node at forward distance
`d` with `0 < d ≤ ⌈n/k⌉`. -/
theorem exists_gap_of_mem {P : Finset (ZMod n)} (hu : IsUniformSet n k P) {v : ZMod n}
    (hv : v ∈ P) : ∃ d : ℕ, 0 < d ∧ d ≤ (n + k - 1) / k ∧ v + (d : ZMod n) ∈ P := by
  obtain ⟨d, hd, hd0, hdP, -⟩ := hu.2 v (by simp [hv])
  refine ⟨d, hd0, ?_, by simpa using hdP⟩
  rcases hd with rfl | rfl
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hd0
    · exact Nat.div_le_div_right (by omega)
  · exact le_rfl

/-- Walking forward from an occupied node `p`: for every `r`, some occupied node `p + s` with
`s ≤ r` has its successor `p + (s + d)` beyond `p + r`, with `d ≤ ⌈n/k⌉`. -/
theorem exists_mem_le_lt {P : Finset (ZMod n)} (hu : IsUniformSet n k P) {p : ZMod n}
    (hp : p ∈ P) (r : ℕ) : ∃ s d : ℕ, s ≤ r ∧ r < s + d ∧ d ≤ (n + k - 1) / k ∧
      p + (s : ZMod n) ∈ P ∧ p + ((s + d : ℕ) : ZMod n) ∈ P := by
  induction r with
  | zero =>
    obtain ⟨d, hd0, hdg, hdP⟩ := exists_gap_of_mem hu hp
    exact ⟨0, d, le_rfl, by omega, hdg, by simpa using hp, by simpa using hdP⟩
  | succ r ih =>
    obtain ⟨s, d, hsr, hrd, hdg, hs, hsd⟩ := ih
    by_cases h : r + 1 < s + d
    · exact ⟨s, d, by omega, h, hdg, hs, hsd⟩
    · obtain ⟨d', hd0, hdg', hdP⟩ := exists_gap_of_mem hu hsd
      refine ⟨s + d, d', by omega, by omega, hdg', hsd, ?_⟩
      simpa [add_assoc] using hdP

/-- In a uniform deployment every `⌈n/k⌉` consecutive nodes `v - (⌈n/k⌉ - 1), …, v` contain an
occupied node. -/
theorem exists_sub_mem [NeZero n] {P : Finset (ZMod n)} (hu : IsUniformSet n k P)
    (hP : P.Nonempty) (v : ZMod n) : ∃ e < (n + k - 1) / k, v - (e : ZMod n) ∈ P := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨s, d, hsr, hrd, hdg, hs, -⟩ := exists_mem_le_lt hu hp (v - p).val
  refine ⟨(v - p).val - s, by omega, ?_⟩
  convert hs using 1
  rw [Nat.cast_sub hsr, ZMod.natCast_zmod_val]
  ring

/-- The `j`-th window: a target among the nodes `n - 1 - j·g - e` (`e < g`), where
`g = ⌈n/k⌉`, reached by some agent `a` starting in the block `0, …, k-1`, costs at least
`n - (j + 1)·g - (k - 1)` moves. -/
theorem exists_agent_window [NeZero n] {f : Fin k → ZMod n}
    (huni : IsUniformSet n k (Finset.univ.image f)) (hk : 0 < k) (j : ℕ)
    (hj : (j + 1) * ((n + k - 1) / k) + k ≤ n + 1) :
    ∃ a : Fin k, ∃ e < (n + k - 1) / k, (f a).val = n - 1 - j * ((n + k - 1) / k) - e ∧
      n - (j + 1) * ((n + k - 1) / k) - (k - 1) ≤ (f a - (a.val : ZMod n)).val := by
  set g := (n + k - 1) / k with hg
  have hne : (Finset.univ.image f).Nonempty := (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩).image f
  obtain ⟨e, he, hmem⟩ := exists_sub_mem huni hne ((n - 1 - j * g : ℕ) : ZMod n)
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
  have hjg : (j + 1) * g = j * g + g := by ring
  have hval : (f a).val = n - 1 - j * g - e := by
    rw [ha, ← Nat.cast_sub (by omega), ZMod.val_natCast_of_lt (by omega)]
  refine ⟨a, e, he, hval, ?_⟩
  have hak : a.val < k := a.isLt
  have hle : ((a.val : ℕ) : ZMod n).val ≤ (f a).val := by
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  rw [ZMod.val_sub hle, ZMod.val_natCast_of_lt (by omega)]
  omega

/-- Summing over `m` disjoint windows of `g = ⌈n/k⌉` nodes at the end of the ring: if the agents
start at the nodes `0, …, k-1` and end in a uniform deployment, they make at least
`∑_{j<m} (n - (j + 1)·g - (k - 1))` moves in total. -/
theorem sum_window_le_total [NeZero n] {f : Fin k → ZMod n}
    (huni : IsUniformSet n k (Finset.univ.image f)) (hk : 0 < k) (m : ℕ)
    (hm : m * ((n + k - 1) / k) + k ≤ n + 1) :
    ∑ j ∈ Finset.range m, (n - (j + 1) * ((n + k - 1) / k) - (k - 1)) ≤
      ∑ a, (f a - (a.val : ZMod n)).val := by
  set g := (n + k - 1) / k with hg
  have hw : ∀ j : Fin m, ∃ a : Fin k, ∃ e < g, (f a).val = n - 1 - j.val * g - e ∧
      n - (j.val + 1) * g - (k - 1) ≤ (f a - (a.val : ZMod n)).val := fun j =>
    exists_agent_window huni hk j.val
      (le_trans (by gcongr; exact j.isLt) hm)
  choose a e he hval hcost using hw
  have hinj : Function.Injective a := by
    intro i j hij
    have h1 := hval i
    have h2 := hval j
    rw [hij] at h1
    have hi := i.isLt
    have hj := j.isLt
    have hmg : ∀ x : Fin m, x.val * g + g ≤ m * g := fun x => by
      have := Nat.mul_le_mul_right g (Nat.succ_le_of_lt x.isLt); rw [Nat.succ_mul] at this
      exact this
    have hi' := hmg i
    have hj' := hmg j
    have hei := he i
    have hej := he j
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have := Nat.mul_le_mul_right g (Nat.succ_le_of_lt hlt); rw [Nat.succ_mul] at this
      omega
    · have := Nat.mul_le_mul_right g (Nat.succ_le_of_lt hlt); rw [Nat.succ_mul] at this
      omega
  calc ∑ j ∈ Finset.range m, (n - (j + 1) * g - (k - 1))
      = ∑ j : Fin m, (n - (j.val + 1) * g - (k - 1)) := (Fin.sum_univ_eq_sum_range _ m).symm
    _ ≤ ∑ j : Fin m, (f (a j) - ((a j).val : ZMod n)).val := Finset.sum_le_sum fun j _ => hcost j
    _ = ∑ b ∈ Finset.univ.image a, (f b - (b.val : ZMod n)).val :=
        (Finset.sum_image (f := fun b => (f b - (b.val : ZMod n)).val)
          fun x _ y _ h => hinj h).symm
    _ ≤ ∑ b, (f b - (b.val : ZMod n)).val :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The window sum in closed form: `2 · ∑_{j<m} (n - (j + 1)·g - (k - 1)) = 2m(n + 1 - k) - g·m(m+1)`
when no term is truncated. -/
theorem two_mul_sum_window (n g : ℕ) {k m : ℕ} (hk : 0 < k) (h : m * g + k ≤ n + 1) :
    2 * ∑ j ∈ Finset.range m, (n - (j + 1) * g - (k - 1)) + g * (m * (m + 1)) =
      2 * m * (n + 1 - k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : (m + 1) * g = m * g + g := by ring
    rw [e1] at h
    have ih' := ih (by omega)
    clear ih
    rw [Finset.sum_range_succ]
    generalize ∑ j ∈ Finset.range m, (n - (j + 1) * g - (k - 1)) = S at ih' ⊢
    rw [e1]
    have h1 : m * g + g ≤ n := by omega
    have h2 : k - 1 ≤ n - (m * g + g) := by omega
    have h3 : k ≤ n + 1 := by omega
    zify [h1, h2, h3, (by omega : 1 ≤ k)] at ih' ⊢
    linear_combination ih'

/-- Arithmetic for an even number `k = 2m` of agents (`m` windows). -/
theorem arith_even {n g m : ℤ} (hm : 1 ≤ m) (h4 : 8 * m ≤ n) (hg : 2 * m * g ≤ n + 2 * m - 1)
    (hgi : m = 1 → n = 8 → g ≤ 4) :
    2 * m * n ≤ 3 * (2 * m * (n + 1 - 2 * m) - g * (m * (m + 1))) := by
  rcases eq_or_lt_of_le hm with rfl | hm2
  · rcases eq_or_lt_of_le h4 with h8 | h9
    · have := hgi rfl h8.symm; subst h8; nlinarith
    · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℤ) ≤ m + 1),
      mul_nonneg (by linarith : (0 : ℤ) ≤ n - 8 * m) (by linarith : (0 : ℤ) ≤ 5 * m - 3)]

/-- Arithmetic for an odd number `k = 2m + 1` of agents (`m + 1` windows). -/
theorem arith_odd {n g m : ℤ} (hm : 1 ≤ m) (h4 : 4 * (2 * m + 1) ≤ n)
    (hg : (2 * m + 1) * g ≤ n + 2 * m) :
    (2 * m + 1) * n ≤ 3 * (2 * (m + 1) * (n - 2 * m) - g * ((m + 1) * (m + 2))) := by
  have h1 : 0 < 2 * m + 1 := by linarith
  refine le_of_mul_le_mul_left ?_ h1
  nlinarith [mul_le_mul_of_nonneg_left hg (by nlinarith : (0 : ℤ) ≤ 3 * ((m + 1) * (m + 2))),
    mul_nonneg (by linarith : (0 : ℤ) ≤ n - 4 * (2 * m + 1)) (by nlinarith : (0 : ℤ) ≤ 5 * m * m + 5 * m - 1),
    mul_nonneg (mul_nonneg (by linarith : (0 : ℤ) ≤ m - 1) (by linarith : (0 : ℤ) ≤ m - 1))
      (by linarith : (0 : ℤ) ≤ m)]

/-- **Theorem 1** of [Shibata et al., PODC 2016], for `p = 1/4`, with constant `6` (the paper
proves `16`): if `k ≥ 2` agents start at the nodes `0, 1, …, k-1` of a unidirectional ring of
`n ≥ 4k` nodes and agent `a` ends at node `f a`, the final nodes forming a uniform deployment, then
the agents make at least `k·n/6` moves in total (agent `a` makes at least `(f a - a).val` moves).
The constant `6` is optimal (`n = 9`, `k = 2`, see `theorem_1_tight`). -/
theorem theorem_1 (hk : 2 ≤ k) (h4 : 4 * k ≤ n) (f : Fin k → ZMod n)
    (huni : IsUniformSet n k (Finset.univ.image f)) :
    k * n ≤ 6 * ∑ a, (f a - (a.val : ZMod n)).val := by
  have : NeZero n := ⟨by omega⟩
  set T := ∑ a, (f a - (a.val : ZMod n)).val
  set g := (n + k - 1) / k with hgdef
  have hg1 : k * g ≤ n + k - 1 := Nat.mul_div_le _ _
  have hg2 : n ≤ k * g := by
    have := Nat.div_add_mod (n + k - 1) k
    have := Nat.mod_lt (n + k - 1) (by omega : 0 < k)
    rw [← hgdef] at *
    omega
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · -- `k = 2m`: `m` windows
    have hm : m * g + 2 * m ≤ n + 1 := by
      have : 2 * m * g = 2 * (m * g) := by ring
      omega
    have hW := two_mul_sum_window n g (by omega) hm
    have hWT := sum_window_le_total huni (by omega) m hm
    rw [← hgdef] at hWT
    generalize ∑ j ∈ Finset.range m, (n - (j + 1) * g - (2 * m - 1)) = W at hW hWT
    have key := arith_even (n := (n : ℤ)) (g := (g : ℤ)) (m := (m : ℤ)) (by omega) (by omega)
      (by have : 2 * m * g + 1 ≤ n + 2 * m := by omega
          have : ((2 * m * g + 1 : ℕ) : ℤ) ≤ ((n + 2 * m : ℕ) : ℤ) := by exact_mod_cast this
          push_cast at this; linarith)
      (fun h1 h2 => by
        have : m = 1 := by exact_mod_cast h1
        have : n = 8 := by exact_mod_cast h2
        subst_vars; omega)
    have hW' : (2 * W : ℤ) + g * (m * (m + 1)) = 2 * m * (n + 1 - 2 * m) := by
      have h' := congrArg (Nat.cast : ℕ → ℤ) hW
      push_cast [(by omega : 2 * m ≤ n + 1)] at h'
      linarith
    have hWT' : (W : ℤ) ≤ T := by exact_mod_cast hWT
    zify
    linarith
  · -- `k = 2m + 1`: `m + 1` windows
    have hm1 : 1 ≤ m := by omega
    have hm : (m + 1) * g + (2 * m + 1) ≤ n + 1 := by
      zify at hg1 h4 ⊢
      push_cast [(by omega : 1 ≤ n + (2 * m + 1))] at hg1
      nlinarith
    have hW := two_mul_sum_window n g (by omega) hm
    have hWT := sum_window_le_total huni (by omega) (m + 1) hm
    rw [← hgdef] at hWT
    generalize ∑ j ∈ Finset.range (m + 1), (n - (j + 1) * g - (2 * m + 1 - 1)) = W at hW hWT
    have key := arith_odd (n := (n : ℤ)) (g := (g : ℤ)) (m := (m : ℤ)) (by omega)
      (by omega)
      (by zify at hg1; push_cast [(by omega : 1 ≤ n + (2 * m + 1))] at hg1; linarith)
    have hW' : (2 * W : ℤ) + g * ((m + 1) * (m + 2)) = 2 * (m + 1) * (n - 2 * m) := by
      rw [(by omega : n + 1 - (2 * m + 1) = n - 2 * m)] at hW
      have h' := congrArg (Nat.cast : ℕ → ℤ) hW
      push_cast [(by omega : 2 * m ≤ n)] at h'
      linarith
    have hWT' : (W : ℤ) ≤ T := by exact_mod_cast hWT
    zify
    linarith

/-- Arithmetic for the general bound: with `x = n + 1 - k` and `m ≈ x / (2g)` windows,
`3k(x - 2)² ≤ 64·n·W`. -/
theorem arith_general {n k g m W : ℤ} (hk : 2 ≤ k) (hn : k + 1 ≤ n) (hg1 : k * g ≤ n + k - 1)
    (hg2 : n ≤ k * g) (hm1 : 2 * g * m ≤ n + 1 - k + g) (hm2 : n + 1 - k - g + 1 ≤ 2 * g * m)
    (hW : 2 * W + g * (m * (m + 1)) = 2 * m * (n + 1 - k)) :
    3 * k * (n - k - 1) ^ 2 ≤ 64 * n * W := by
  set x := n + 1 - k with hx
  have hg0 : 1 ≤ g := by nlinarith
  have hk1 : (0 : ℤ) ≤ (k - 1) * (n - k - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hk2 : (0 : ℤ) ≤ (k - 2) * (n - k - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hgx : g ≤ x := by nlinarith
  have hgx2 : 2 * g ≤ x + 2 := by nlinarith
  -- `8 g W ≥ 3 (x - g)²`
  have h1 : 3 * (x - g) ^ 2 ≤ 8 * g * W := by
    have e : 8 * g * W = 2 * (g * m) * (4 * x - 2 * (g * m) - 2 * g) := by linear_combination 4 * g * hW
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * (g * m) - (x - g))
      (by linarith : (0 : ℤ) ≤ x + g - 2 * (g * m)),
      mul_nonneg (by linarith : (0 : ℤ) ≤ x - g) (by linarith : (0 : ℤ) ≤ g),
      mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * (g * m) - (x - g)) (by linarith : (0 : ℤ) ≤ g)]
  have h2 : (n - k - 1) ^ 2 ≤ 4 * (x - g) ^ 2 := by nlinarith
  have hW0 : 0 ≤ W := by nlinarith
  have h3 : 3 * (n - k - 1) ^ 2 ≤ 32 * g * W := by nlinarith
  have h4 : 32 * (k * g) * W ≤ 32 * (2 * n) * W := by
    apply mul_le_mul_of_nonneg_right _ hW0; linarith
  nlinarith

/-- **Theorem 1** of [Shibata et al., PODC 2016], general form: if `k ≥ 2` agents start at the
nodes `0, 1, …, k-1` of a unidirectional ring of `n` nodes and agent `a` ends at node `f a`, the
final nodes forming a uniform deployment, then the total number of moves `T` satisfies
`3·k·(n - k - 1)² ≤ 64·n·T`. Hence for `k ≤ p·n` with a constant `p < 1` and `n ≥ 2/(1-p)`,
`T ≥ 3(1-p)²/256 · k·n = Ω(kn)` (see `theorem_1_of_le_mul`). -/
theorem theorem_1_general (hk : 2 ≤ k) (f : Fin k → ZMod n)
    (huni : IsUniformSet n k (Finset.univ.image f)) :
    3 * k * (n - k - 1) ^ 2 ≤ 64 * n * ∑ a, (f a - (a.val : ZMod n)).val := by
  rcases Nat.lt_or_ge n (k + 2) with hn | hn
  · rw [(by omega : n - k - 1 = 0)]; simp
  have : NeZero n := ⟨by omega⟩
  set T := ∑ a, (f a - (a.val : ZMod n)).val
  set g := (n + k - 1) / k with hgdef
  have hg1 : k * g ≤ n + k - 1 := Nat.mul_div_le _ _
  have hg2 : n ≤ k * g := by
    have := Nat.div_add_mod (n + k - 1) k
    have := Nat.mod_lt (n + k - 1) (by omega : 0 < k)
    rw [← hgdef] at *
    omega
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by rintro h; rw [h] at hg2; omega)
  set m := (n + 1 - k + g) / (2 * g) with hmdef
  have hm1 : 2 * g * m ≤ n + 1 - k + g := Nat.mul_div_le _ _
  have hm2 : n + 1 - k + g < 2 * g * (m + 1) := by
    have := Nat.div_add_mod (n + 1 - k + g) (2 * g)
    have := Nat.mod_lt (n + 1 - k + g) (by omega : 0 < 2 * g)
    rw [← hmdef] at *
    rw [mul_add]; omega
  have hgx : g ≤ n + 1 - k := by
    have h1 : ((k * g : ℕ) : ℤ) ≤ ((n + k - 1 : ℕ) : ℤ) := by exact_mod_cast hg1
    push_cast [(by omega : 1 ≤ n + k)] at h1
    have : (0 : ℤ) ≤ (k - 1) * (n - k - 1) := mul_nonneg (by omega) (by omega)
    have : (g : ℤ) ≤ n + 1 - k := by nlinarith
    omega
  have hm : m * g + k ≤ n + 1 := by
    have : 2 * g * m = 2 * (m * g) := by ring
    omega
  have hW := two_mul_sum_window n g (by omega) hm
  have hWT := sum_window_le_total huni (by omega) m hm
  rw [← hgdef] at hWT
  generalize ∑ j ∈ Finset.range m, (n - (j + 1) * g - (k - 1)) = W at hW hWT
  have h1 : ((k * g : ℕ) : ℤ) ≤ ((n + k - 1 : ℕ) : ℤ) := by exact_mod_cast hg1
  push_cast [(by omega : 1 ≤ n + k)] at h1
  have h2 : ((2 * g * m : ℕ) : ℤ) ≤ ((n + 1 - k + g : ℕ) : ℤ) := by exact_mod_cast hm1
  have h3 : ((n + 1 - k + g + 1 : ℕ) : ℤ) ≤ ((2 * g * (m + 1) : ℕ) : ℤ) := by exact_mod_cast hm2
  have h4 := congrArg (Nat.cast : ℕ → ℤ) hW
  push_cast [(by omega : k ≤ n + 1)] at h2 h3 h4
  have key := arith_general (n := (n : ℤ)) (k := (k : ℤ)) (g := (g : ℤ)) (m := (m : ℤ))
    (W := (W : ℤ)) (by omega) (by omega) h1 (by exact_mod_cast hg2) h2 (by linarith) h4
  have hWT' : (W : ℤ) ≤ T := by exact_mod_cast hWT
  have e : ((n - k - 1 : ℕ) : ℤ) = n - k - 1 := by omega
  zify
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hWT' (by positivity : (0 : ℤ) ≤ 64 * n)]

/-- **Theorem 1** of [Shibata et al., PODC 2016] in the paper's form: for a constant `p < 1`, if
`2 ≤ k ≤ p·n` (and `n ≥ 2/(1-p)`), then starting from the block configuration `0, …, k-1` every
uniform deployment costs at least `c(p)·k·n` moves, `c(p) = 3(1-p)²/256`. -/
theorem theorem_1_of_le_mul {p : ℝ} (hk : 2 ≤ k) (hkn : (k : ℝ) ≤ p * n)
    (hn : 2 ≤ (1 - p) * n) (f : Fin k → ZMod n)
    (huni : IsUniformSet n k (Finset.univ.image f)) :
    3 * (1 - p) ^ 2 / 256 * k * n ≤ ∑ a, ((f a - (a.val : ZMod n)).val : ℝ) := by
  have h := theorem_1_general hk f huni
  have hkn2 : k + 2 ≤ n := by
    have : (k : ℝ) + 2 ≤ n := by linarith
    exact_mod_cast this
  have h' : ((3 * k * (n - k - 1) ^ 2 : ℕ) : ℝ) ≤ ((64 * n * ∑ a, (f a - (a.val : ZMod n)).val : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.sub_sub] at h'
  push_cast [Nat.cast_sub (by omega : k + 1 ≤ n)] at h'
  set T := ∑ a, ((f a - (a.val : ZMod n)).val : ℝ)
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact this
  have hd : (1 - p) * n / 2 ≤ (n : ℝ) - k - 1 := by linarith
  have hd0 : (0 : ℝ) ≤ (1 - p) * n / 2 := by linarith
  have hsq : ((1 - p) * n / 2) ^ 2 ≤ ((n : ℝ) - k - 1) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have : 3 * k * ((1 - p) * n / 2) ^ 2 ≤ 64 * n * T := by nlinarith
  have e : 3 * (1 - p) ^ 2 / 256 * k * n * (64 * n) = 3 * k * ((1 - p) * n / 2) ^ 2 := by ring
  nlinarith

/-- The constant `6` of `theorem_1` is optimal: for `n = 9`, `k = 2`, the agents at nodes `0, 1`
reach the uniform deployment `{0, 4}` with `3` moves, and `2 · 9 = 6 · 3`. -/
theorem theorem_1_tight :
    IsUniformSet 9 2 (Finset.univ.image ![(0 : ZMod 9), 4]) ∧
      ∑ a : Fin 2, (![(0 : ZMod 9), 4] a - (a.val : ZMod 9)).val = 3 := by
  refine ⟨⟨fun v => by dsimp only; split_ifs <;> omega, fun v hv => ?_⟩, by decide⟩
  dsimp only at hv ⊢
  have hv' : v = 0 ∨ v = 4 := by
    by_contra h
    push Not at h
    apply hv
    rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro a ha
    fin_cases a <;> simp_all
  rcases hv' with rfl | rfl
  · refine ⟨4, Or.inl rfl, by norm_num, by decide, fun e he1 he2 => ?_⟩
    interval_cases e <;> decide
  · refine ⟨5, Or.inr rfl, by norm_num, by decide, fun e he1 he2 => ?_⟩
    interval_cases e <;> decide

end Podc.UniformDeploymentRings
