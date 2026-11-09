import Papers.PODC2014.LinialLowerBoundEasy.LogStar

/-!
# 3-colouring directed cycles: Linial's bound (1)

Model of §2 of [Laurinharju–Suomela]: deterministic synchronous LOCAL algorithms on the directed
`n`-cycle. Nodes are `ZMod n`, with edges `v → v + 1`; the nodes carry unique identifiers from
`{1, …, n}` (`IdAssignment n`). After `T` rounds a node knows exactly the identifiers of the nodes
`v - T, …, v + T` (in this order: the cycle is directed), so a `T`-round algorithm is a function
`A` of the window `(id (v - T), …, id (v + T))` of `2T + 1` identifiers (`IdAssignment.window`).
The algorithm finds a proper 3-colouring if for every identifier assignment and every node the
colour is in `{1, 2, 3}` and differs from the colour of the successor (`Is3ColouringAlgorithm`).

We also give the more extensional version: an algorithm is a function `f` of the whole view
`j ↦ id (v + j)` (`j : ℤ`) that depends only on the offsets `|j| ≤ T` (`IsLocal T f`).

## Main statements

* `algorithm_mem`, `algorithm_ne`: §2, the algorithm satisfies `A (x₁, …, x_{2T+1}) ∈ {1, 2, 3}`
  and `A (x₁, …, x_{2T+1}) ≠ A (x₂, …, x_{2T+2})` whenever the `xᵢ` are distinct identifiers.
* `isColouringFunction_of_algorithm`: §3, it is a `(2T+1)`-ary 3-colouring function.
* `linial_bound`: equation (1), `T ≥ log*(n)/2 - 1`; `linial_bound_local` for local view functions.
-/

namespace Podc.LinialLowerBoundEasy

open Finset

/-- Unique identifiers from `{1, …, n}` on the nodes `ZMod n` of the directed `n`-cycle
(edges `v → v + 1`). -/
structure IdAssignment (n : ℕ) where
  /-- The identifier of each node. -/
  id : ZMod n → ℕ
  /-- Identifiers are unique. -/
  injective : Function.Injective id
  /-- Identifiers are taken from `{1, …, n}`. -/
  mem : ∀ v, id v ∈ Icc 1 n

/-- The radius-`T` window of node `v`: the identifiers of `v - T, v - T + 1, …, v + T`. -/
def IdAssignment.window {n : ℕ} (L : IdAssignment n) (T : ℕ) (v : ZMod n) : Fin (2 * T + 1) → ℕ :=
  fun i => L.id (v - T + (i : ℕ))

/-- §2 of [Laurinharju–Suomela]: the `T`-round algorithm `A` (a function of the radius-`T` window)
finds a proper 3-colouring of every directed `n`-cycle with identifiers from `{1, …, n}`. -/
def Is3ColouringAlgorithm (n T : ℕ) (A : (Fin (2 * T + 1) → ℕ) → ℕ) : Prop :=
  ∀ (L : IdAssignment n) (v : ZMod n),
    A (L.window T v) ∈ Icc 1 3 ∧ A (L.window T v) ≠ A (L.window T (v + 1))

/-- Any `m ≥ 1` distinct identifiers from `{1, …, n}` can be placed on consecutive nodes
`0, 1, …, m - 1` of the directed `n`-cycle. -/
theorem exists_idAssignment {n m : ℕ} (hm : 0 < m) (x : Fin m → ℕ) (hx : Function.Injective x)
    (hmem : ∀ i, x i ∈ Icc 1 n) :
    ∃ L : IdAssignment n, ∀ j : Fin m, L.id ((j : ℕ) : ZMod n) = x j := by
  classical
  have himg : univ.image x ⊆ Icc 1 n := by
    intro a ha; obtain ⟨i, -, rfl⟩ := mem_image.1 ha; exact hmem i
  have hcard : (univ.image x).card = m := by rw [card_image_of_injective _ hx]; simp
  have hmn : m ≤ n := by simpa [hcard] using card_le_card himg
  have : NeZero n := ⟨by omega⟩
  obtain ⟨l, hldef⟩ : ∃ l : List ℕ, l = List.ofFn x ++ (Icc 1 n \ univ.image x).sort (· ≤ ·) :=
    ⟨_, rfl⟩
  have hlen : l.length = n := by
    simp only [hldef, List.length_append, List.length_ofFn, Finset.length_sort,
      card_sdiff_of_subset himg, hcard, Nat.card_Icc]
    omega
  have hnodup : l.Nodup := by
    rw [hldef]
    refine List.nodup_append.2 ⟨List.nodup_ofFn.2 hx, Finset.sort_nodup _ _, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    rw [Finset.mem_sort, mem_sdiff] at hb
    exact hb.2 (mem_image_of_mem _ (mem_univ _))
  have hl : ∀ a ∈ l, a ∈ Icc 1 n := by
    intro a ha
    rw [hldef] at ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact hmem i
    · exact (mem_sdiff.1 ((Finset.mem_sort _).1 ha)).1
  have hfirst : ∀ j : Fin m, l[(j : ℕ)]'(by rw [hlen]; omega) = x j := by
    intro j
    subst hldef
    rw [List.getElem_append_left (by simp), List.getElem_ofFn]
  refine ⟨⟨fun v => l[v.val]'(by rw [hlen]; exact ZMod.val_lt v), ?_,
    fun v => hl _ (List.getElem_mem _)⟩, ?_⟩
  · intro v w hvw
    exact ZMod.val_injective n ((hnodup.getElem_inj_iff).1 hvw)
  · intro j
    have hj : ((j : ℕ) : ZMod n).val = j := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [hj]
    exact hfirst j

/-- §2 of [Laurinharju–Suomela]: `A (x₁, …, x_{2T+1}) ∈ {1, 2, 3}` for distinct identifiers. -/
theorem algorithm_mem {n T : ℕ} {A : (Fin (2 * T + 1) → ℕ) → ℕ} (hA : Is3ColouringAlgorithm n T A)
    (x : Fin (2 * T + 1) → ℕ) (hx : Function.Injective x) (hmem : ∀ i, x i ∈ Icc 1 n) :
    A x ∈ Icc 1 3 := by
  obtain ⟨L, hL⟩ := exists_idAssignment (by omega) x hx hmem
  have : L.window T (T : ZMod n) = x := by
    funext i
    simp only [IdAssignment.window, sub_self, zero_add]
    exact hL i
  simpa [this] using (hA L T).1

/-- §2 of [Laurinharju–Suomela]: `A (x₁, …, x_{2T+1}) ≠ A (x₂, …, x_{2T+2})` whenever
`x₁, …, x_{2T+2}` are distinct identifiers from `{1, …, n}` (they then occupy consecutive nodes
of some directed `n`-cycle; see Figure 1). -/
theorem algorithm_ne {n T : ℕ} {A : (Fin (2 * T + 1) → ℕ) → ℕ} (hA : Is3ColouringAlgorithm n T A)
    (x : Fin (2 * T + 2) → ℕ) (hx : Function.Injective x) (hmem : ∀ i, x i ∈ Icc 1 n) :
    A (Fin.init x) ≠ A (Fin.tail x) := by
  obtain ⟨L, hL⟩ := exists_idAssignment (by omega) x hx hmem
  have h0 : L.window T (T : ZMod n) = Fin.init x := by
    funext i
    simp only [IdAssignment.window, sub_self, zero_add, Fin.init]
    exact hL i.castSucc
  have h1 : L.window T ((T : ZMod n) + 1) = Fin.tail x := by
    funext i
    simp only [IdAssignment.window, Fin.tail]
    have := hL i.succ
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at this
    rw [← this]
    congr 1
    ring
  rw [← h0, ← h1]
  exact (hA L T).2

/-- §3 of [Laurinharju–Suomela]: a `T`-round 3-colouring algorithm for directed `n`-cycles is a
`(2T+1)`-ary 3-colouring function. -/
theorem isColouringFunction_of_algorithm {n T : ℕ} {A : (Fin (2 * T + 1) → ℕ) → ℕ}
    (hA : Is3ColouringAlgorithm n T A) : IsColouringFunction n (2 * T + 1) 3 A :=
  ⟨fun x hx hmem => algorithm_mem hA x hx.injective hmem,
    fun x hx hmem => algorithm_ne hA x hx.injective hmem⟩

/-- **Equation (1)** of [Laurinharju–Suomela] (Linial's lower bound): every deterministic
`T`-round algorithm that finds a proper 3-colouring of the directed `n`-cycle with identifiers
from `{1, …, n}` has `T ≥ log*(n)/2 - 1`. -/
theorem linial_bound {n T : ℕ} {A : (Fin (2 * T + 1) → ℕ) → ℕ}
    (hA : Is3ColouringAlgorithm n T A) : (logStar n : ℝ) / 2 - 1 ≤ T := by
  have := logStar_le_of_isColouringFunction (isColouringFunction_of_algorithm hA)
  have : (logStar n : ℝ) ≤ 2 * T + 1 + 1 := by exact_mod_cast this
  linarith

/-! ### Algorithms as local functions of the view -/

/-- The view of node `v`: offset `j : ℤ` carries the identifier of node `v + j`. -/
def IdAssignment.view {n : ℕ} (L : IdAssignment n) (v : ZMod n) : ℤ → ℕ :=
  fun j => L.id (v + j)

/-- `f` only depends on the offsets `-T, …, T` of a view (it runs in `T` rounds). -/
def IsLocal (T : ℕ) (f : (ℤ → ℕ) → ℕ) : Prop :=
  ∀ g h : ℤ → ℕ, (∀ j : ℤ, |j| ≤ T → g j = h j) → f g = f h

/-- A `T`-round algorithm, given as a local function of the view, that finds a proper
3-colouring of every directed `n`-cycle with identifiers from `{1, …, n}`. -/
def IsLocal3ColouringAlgorithm (n T : ℕ) (f : (ℤ → ℕ) → ℕ) : Prop :=
  IsLocal T f ∧ ∀ (L : IdAssignment n) (v : ZMod n),
    f (L.view v) ∈ Icc 1 3 ∧ f (L.view v) ≠ f (L.view (v + 1))

/-- The window function of a local view function: read offset `j` at window position `j + T`. -/
def windowFun (T : ℕ) (f : (ℤ → ℕ) → ℕ) (w : Fin (2 * T + 1) → ℕ) : ℕ :=
  f fun j => if h : |j| ≤ T then w ⟨(j + T).toNat, by rw [abs_le] at h; omega⟩ else 0

theorem windowFun_window {n T : ℕ} {f : (ℤ → ℕ) → ℕ} (hf : IsLocal T f) (L : IdAssignment n)
    (v : ZMod n) : windowFun T f (L.window T v) = f (L.view v) := by
  refine hf _ _ fun j hj => ?_
  simp only [hj, dite_true, IdAssignment.window, IdAssignment.view]
  congr 1
  have : (((j + T).toNat : ℕ) : ZMod n) = ((j + T : ℤ) : ZMod n) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by rw [abs_le] at hj; omega)]
  rw [this]
  push_cast
  ring

/-- **Equation (1)** for algorithms given as `T`-local functions of the view. -/
theorem linial_bound_local {n T : ℕ} {f : (ℤ → ℕ) → ℕ} (hf : IsLocal3ColouringAlgorithm n T f) :
    (logStar n : ℝ) / 2 - 1 ≤ T := by
  refine linial_bound (A := windowFun T f) fun L v => ?_
  rw [windowFun_window hf.1, windowFun_window hf.1]
  exact hf.2 L v

/-! ### Non-vacuity -/

/-- The hypotheses are satisfiable: on the directed 3-cycle, "colour = own identifier" is a
0-round 3-colouring algorithm. -/
theorem is3ColouringAlgorithm_three : Is3ColouringAlgorithm 3 0 (fun w => w 0) := by
  intro L v
  refine ⟨by simpa [IdAssignment.window] using L.mem v, fun h => ?_⟩
  have := L.injective (by simpa [IdAssignment.window] using h)
  have h' : (1 : ZMod 3) = 0 := by
    have := congrArg (· - v) this; simpa using this.symm
  exact absurd h' (by decide)
end Podc.LinialLowerBoundEasy
