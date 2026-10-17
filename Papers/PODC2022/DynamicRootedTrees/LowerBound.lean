import Papers.PODC2022.DynamicRootedTrees.Defs
import Cslib.Computability.Distributed.DynamicNetworks.Journey

/-!
# The lower bound `t*(𝒯ₙ) ≥ ⌈(3n-1)/2⌉ - 2`

The explicit sequence of rooted trees of Zeiner, Schwarz and Schmid (Figure 5 of the full version
arXiv:2211.10151 of El-Hayek–Henzinger–Schmid), on processes `0, …, n-1` (paper labels `1, …, n`
shifted by one), with `h = ⌊n/2⌋`:

* rounds `t ≤ ⌊(n-1)/2⌋`: the path `0 → 1 → ⋯ → n-1` (root `0`);
* rounds `⌊(n-1)/2⌋ < t ≤ n-2`: the tree rooted at `n-1` with the two branches
  `n-1 → 0 → 1 → ⋯ → h-1` and `n-1 → n-2 → ⋯ → h`;
* rounds `t ≥ n-1`: the path `h-1 → h → ⋯ → n-1 → 0 → 1 → ⋯ → h-2` (root `h-1`).

In ℕ, `⌈(3n-1)/2⌉ - 2 = 3n/2 - 2`. We show that no process has broadcast after any round
`s < 3n/2 - 2` (`lbSeq_not_broadcasts`).

The proof tracks forward invariants for out-neighbourhoods `{y | prod G 1 t x y}`:
* for `x ≥ h`, the out-neighbourhood of `x` never contains `h-1` (`lbInvHigh`);
* for `x < h`, the out-neighbourhood of `x` after `t` rounds is contained in the cyclic interval
  `[x, x + r t]` with `r t = min t ⌊(n-1)/2⌋ + (t - (n-2))` (`lbInvLow`), which at
  `t ≤ 3n/2 - 3` misses the cyclic predecessor of `x`.
-/

namespace DynamicRootedTrees

open Cslib.DynNet

/-! ### The sequence -/

/-- The root (as a natural number) of the tree of round `t` in the lower-bound sequence. -/
def lbRoot (n t : ℕ) : ℕ :=
  if t ≤ (n - 1) / 2 then 0
  else if t ≤ n - 2 then n - 1
  else n / 2 - 1

/-- The parent (as a natural number) of the non-root vertex `y` in the tree of round `t`. -/
def lbParent (n t y : ℕ) : ℕ :=
  if t ≤ (n - 1) / 2 then y - 1                                   -- path `0 → ⋯ → n-1`
  else if t ≤ n - 2 then                                          -- two branches from `n-1`
    (if y = 0 then n - 1 else if y < n / 2 then y - 1 else y + 1)
  else (if y = 0 then n - 1 else y - 1)                           -- path `h-1 → ⋯ → n-1 → 0 → ⋯`

/-- The lower-bound sequence of Zeiner–Schwarz–Schmid: in round `t`, `x → y` iff `x = y` or `x` is
the parent of the non-root vertex `y` (see the module docstring for the three phases). -/
def lbSeq (n t : ℕ) (x y : Fin n) : Prop :=
  x = y ∨ (y.val ≠ lbRoot n t ∧ lbParent n t y.val = x.val)

/-! ### Every round is a rooted tree -/

/-- A rooted tree from a parent function that strictly decreases a rank away from the root. -/
def RootedTree.ofRank {n : ℕ} (root : Fin n) (parent : Fin n → Fin n) (d : Fin n → ℕ)
    (hd : ∀ v, v ≠ root → d (parent v) < d v) : RootedTree n where
  root := root
  parent := parent
  reach_root := by
    intro v
    induction hv : d v using Nat.strong_induction_on generalizing v with
    | _ m ih =>
      by_cases hr : v = root
      · exact ⟨0, hr⟩
      · obtain ⟨k, hk⟩ := ih _ (hv ▸ hd v hr) (parent v) rfl
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- Rank (distance to the root) in the tree of round `t`. -/
def lbRank (n t y : ℕ) : ℕ :=
  if t ≤ (n - 1) / 2 then y
  else if t ≤ n - 2 then (if y < n / 2 then y + 1 else n - 1 - y)
  else (if n / 2 - 1 ≤ y then y - (n / 2 - 1) else y + n - n / 2 + 1)

theorem lbRoot_lt {n : ℕ} (hn : 2 ≤ n) (t : ℕ) : lbRoot n t < n := by
  unfold lbRoot; split_ifs <;> omega

theorem lbParent_lt {n t y : ℕ} (hn : 2 ≤ n) (hy : y < n) (hr : y ≠ lbRoot n t) :
    lbParent n t y < n := by
  unfold lbParent lbRoot at *; split_ifs at * <;> omega

theorem lbRank_lt {n t y : ℕ} (hn : 2 ≤ n) (hy : y < n) (hr : y ≠ lbRoot n t) :
    lbRank n t (lbParent n t y) < lbRank n t y := by
  unfold lbRank lbParent lbRoot at *; split_ifs at * <;> omega

/-- The tree of round `t` (for `n ≥ 2`). -/
def lbTree (n : ℕ) (hn : 2 ≤ n) (t : ℕ) : RootedTree n :=
  RootedTree.ofRank ⟨lbRoot n t, lbRoot_lt hn t⟩
    (fun v => if h : lbParent n t v < n then ⟨_, h⟩ else v) (fun v => lbRank n t v) (by
      intro v hv
      have hv' : v.val ≠ lbRoot n t := fun h => hv (Fin.ext h)
      simp only [lbParent_lt hn v.2 hv', ↓reduceDIte]
      exact lbRank_lt hn v.2 hv')

theorem lbTree_adj (n : ℕ) (hn : 2 ≤ n) (t : ℕ) : (lbTree n hn t).adj = lbSeq n t := by
  funext x y
  simp only [RootedTree.adj, lbTree, RootedTree.ofRank, lbSeq]
  apply propext
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : y.val ≠ lbRoot n t := fun h => h1 (Fin.ext h)
    simp only [lbParent_lt hn y.2 h1', ↓reduceDIte] at h2
    exact ⟨h1', by rw [← h2]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 (by rw [h]), ?_⟩
    simp only [lbParent_lt hn y.2 h1, ↓reduceDIte]
    exact Fin.ext h2

theorem lbSeq_mem (n : ℕ) (hn : 2 ≤ n) (i : ℕ) : lbSeq n i ∈ treesWithLoops n :=
  ⟨lbTree n hn i, lbTree_adj n hn i⟩

/-! ### Invariants -/

/-- Invariant for senders `x ≥ n/2`: the root `n/2 - 1` of the last phase is never reached. -/
def lbInvHigh (n t y : ℕ) : Prop := n / 2 ≤ y ∨ (y + (n - 1) / 2 < t ∧ y + 1 < n / 2)

/-- Invariant for senders `x < n/2`: the cyclic interval `[x, x + r t]`. -/
def lbInvLow (n x t y : ℕ) : Prop :=
  let r := min t ((n - 1) / 2) + (t - (n - 2))
  (x ≤ y ∧ y ≤ x + r) ∨ (y < x ∧ y + n ≤ x + r)

theorem lbInvHigh_step {n t z y : ℕ} (hn : 2 ≤ n) (hy : y < n) (hz : z < n)
    (hS : lbInvHigh n t z) (hE : z = y ∨ (y ≠ lbRoot n (t + 1) ∧ lbParent n (t + 1) y = z)) :
    lbInvHigh n (t + 1) y := by
  unfold lbInvHigh at *
  rcases hE with rfl | ⟨hr, hp⟩
  · omega
  · subst hp
    unfold lbParent lbRoot at *
    split_ifs at * <;> omega

theorem lbInvLow_step {n x t z y : ℕ} (hn : 2 ≤ n) (hx : x < n / 2) (hy : y < n) (hz : z < n)
    (hS : lbInvLow n x t z) (hE : z = y ∨ (y ≠ lbRoot n (t + 1) ∧ lbParent n (t + 1) y = z)) :
    lbInvLow n x (t + 1) y := by
  unfold lbInvLow at *
  rcases hE with rfl | ⟨hr, hp⟩
  · omega
  · subst hp
    unfold lbParent lbRoot at *
    split_ifs at * <;> omega

/-! ### The lower bound -/

/-- Theorem 3.7 of El-Hayek–Henzinger–Schmid (construction of Zeiner–Schwarz–Schmid): in the
sequence `lbSeq n` of rooted trees, no process has broadcast after any round
`s < ⌈(3n-1)/2⌉ - 2 = 3n/2 - 2`. -/
theorem lbSeq_not_broadcasts (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hs : s < 3 * n / 2 - 2) :
    ¬ Cslib.DynNet.Broadcasts (lbSeq n) s := by
  rintro ⟨x, hx⟩
  by_cases hxh : n / 2 ≤ x.val
  · have key := Cslib.DynNet.prod_of_inv (E := lbSeq n) (a := 1)
      (fun t (y : Fin n) => lbInvHigh n t y.val) (x := x) (by unfold lbInvHigh; omega)
      (fun t z y hS hE => lbInvHigh_step hn y.2 z.2 hS
        (by rw [Nat.add_comm] at hE; rcases hE with rfl | h; exacts [Or.inl rfl, Or.inr h]))
      s ⟨n / 2 - 1, by omega⟩ (hx _)
    simp only [lbInvHigh] at key
    omega
  · have key := Cslib.DynNet.prod_of_inv (E := lbSeq n) (a := 1)
      (fun t (y : Fin n) => lbInvLow n x t y.val) (x := x) (by unfold lbInvLow; omega)
      (fun t z y hS hE => lbInvLow_step hn (by omega) y.2 z.2 hS
        (by rw [Nat.add_comm] at hE; rcases hE with rfl | h; exacts [Or.inl rfl, Or.inr h])) s
      ⟨if x.val = 0 then n - 1 else x.val - 1, by split_ifs <;> omega⟩ (hx _)
    simp only [lbInvLow] at key
    split_ifs at key <;> omega

/-! ### Sanity checks: the bound is attained for small `n` -/

instance (n t : ℕ) : DecidableRel (lbSeq n t) := fun _ _ => by unfold lbSeq; infer_instance

example : Cslib.DynNet.Broadcasts (lbSeq 4) (3 * 4 / 2 - 2) := by
  refine ⟨1, ?_⟩
  simp only [Cslib.DynNet.prod, Relation.Comp, Nat.reduceAdd]
  decide

example : Cslib.DynNet.Broadcasts (lbSeq 5) (3 * 5 / 2 - 2) := by
  refine ⟨1, ?_⟩
  simp only [Cslib.DynNet.prod, Relation.Comp, Nat.reduceAdd]
  decide

end DynamicRootedTrees
