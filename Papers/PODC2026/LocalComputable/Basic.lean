import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Computability.Partrec
import Mathlib.Data.ENat.Basic

/-!
# The ball-growing LOCAL model, abstractly

Cruciani, Das, Equi, Lievonen, Luong-Le, Modanese, Suomela,
*Is a LOCAL algorithm computable?* (PODC 2026 brief announcement; arXiv 2602.21022).

The paper's equivalence results (Section 5) use only the following features of the LOCAL model
(Definitions 3.1, 3.5): every node `v` of a network `G` has, for every radius `t`, a *view*
`view G v t` (its radius-`t` rooted neighbourhood up to isomorphism), and the radius-`t` view
determines all smaller views. A (deterministic) LOCAL algorithm in the *ball-growing formalism*
is a map `A : View → ℕ → Option Out`; node `v` outputs `A (view G v t) t` for the least `t` with
a non-`⊥` (here: non-`none`) value.

We therefore work with an abstract `Model Net View`: a type of networks, their sizes, and
their views, subject to the restriction property `Model.restrict`. The concrete port-numbered
networks with identifiers of Section 3 are an instance (`Concrete.lean`).

A *problem* is an arbitrary predicate on output labellings (LCLs are a special case; the paper
remarks that its equivalences hold "for LCLs and beyond"). The only property of LCLs that is
used is that the output alphabet is finite (Theorem 5.4) and that validity is decidable
(Theorem 5.3).

Knowledge of `n`: in the model with an upper bound, every node additionally receives a common
natural number `N`; an algorithm is then a family `A : ℕ → Alg View Out`, and the *promise*
`Adm N G` says which pairs `(N, G)` are legal inputs (`n ≤ N`, or `n ≤ N ≤ f(n)`).
-/

namespace LocalComputable

/-- An abstract family of networks for the ball-growing LOCAL model: networks have a size
(number of nodes, the nodes being `0, …, size G - 1`) and every node has a view of every
radius. The radius-`t` view determines all views of smaller radius. -/
structure Model (Net View : Type*) where
  /-- Number of nodes. -/
  size : Net → ℕ
  /-- `view G v t`: the radius-`t` view (rooted neighbourhood) of node `v` in `G`. -/
  view : Net → ℕ → ℕ → View
  /-- The radius-`t` view determines the radius-`s` view for `s ≤ t`. -/
  restrict : ∀ {G G' : Net} {v v' t s : ℕ}, s ≤ t → view G v t = view G' v' t →
    view G v s = view G' v' s

/-- A LOCAL algorithm in the ball-growing formalism (Definition 3.5): given the gathered view
and the current radius, output a label (`some a`) or keep exploring (`none`, the paper's `⊥`). -/
abbrev Alg (View Out : Type*) := View → ℕ → Option Out

namespace Model

variable {Net View Out : Type*} (M : Model Net View)

/-- The output of node `v` when the ball is grown up to radius at most `r`: the value at the
least radius `t ≤ r` at which the algorithm does not return `⊥` (`none` if there is none). -/
def out (A : Alg View Out) (G : Net) (v r : ℕ) : Option Out :=
  (List.range (r + 1)).findSome? fun t => A (M.view G v t) t

/-- A problem: a set of valid output labellings of every network. -/
def Problem (Out : Type*) := ∀ G : Net, (Fin (M.size G) → Out) → Prop

/-- `A` solves `P` on the network `G` with locality `T`: every node stops by radius
`T (size G)`, and the resulting labelling is valid. -/
def SolvesOn (P : M.Problem Out) (A : Alg View Out) (T : ℕ → ℕ) (G : Net) : Prop :=
  ∃ lab : Fin (M.size G) → Out,
    (∀ v : Fin (M.size G), M.out A G v (T (M.size G)) = some (lab v)) ∧ P G lab

/-- No auxiliary information on `n`: `A` solves `P` with locality `T` on every network. -/
def Solves (P : M.Problem Out) (A : Alg View Out) (T : ℕ → ℕ) : Prop :=
  ∀ G, M.SolvesOn P A T G

/-- With auxiliary information: every node receives the same number `N`, subject to the
promise `Adm N G`; the algorithm is a family `A N`. -/
def SolvesWith (Adm : ℕ → Net → Prop) (P : M.Problem Out) (A : ℕ → Alg View Out)
    (T : ℕ → ℕ) : Prop :=
  ∀ N G, Adm N G → M.SolvesOn P (A N) T G

/-- The promise `n ≤ N` (an upper bound on the network size). -/
def UpperBound (N : ℕ) (G : Net) : Prop := M.size G ≤ N

/-- The promise `n ≤ N ≤ f(n)` for a fixed function `f : ℕ → ℕ∞`. -/
def Sandwich (f : ℕ → ℕ∞) (N : ℕ) (G : Net) : Prop := M.size G ≤ N ∧ (N : ℕ∞) ≤ f (M.size G)

/-! ### Basic facts about outputs -/

variable {M}

theorem out_congr (A : Alg View Out) {G G' : Net} {v v' r : ℕ}
    (h : M.view G v r = M.view G' v' r) : M.out A G v r = M.out A G' v' r := by
  unfold out
  have key : ∀ l : List ℕ, (∀ t ∈ l, t ≤ r) →
      l.findSome? (fun t => A (M.view G v t) t) = l.findSome? (fun t => A (M.view G' v' t) t) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons t l ih =>
      simp only [List.findSome?_cons]
      rw [M.restrict (hl t (by simp)) h, ih (fun t ht => hl t (by simp [ht]))]
  exact key _ fun t ht => Nat.lt_succ_iff.mp (List.mem_range.mp ht)

theorem out_mono (A : Alg View Out) {G : Net} {v r r' : ℕ} {a : Out}
    (h : M.out A G v r = some a) (hr : r ≤ r') : M.out A G v r' = some a := by
  unfold out at *
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show r + k + 1 = (r + 1) + k by omega, List.range_add, List.findSome?_append, h]
  rfl

theorem out_eq_none_iff (A : Alg View Out) {G : Net} {v r : ℕ} :
    M.out A G v r = none ↔ ∀ t ≤ r, A (M.view G v t) t = none := by
  simp [out, List.findSome?_eq_none_iff, Nat.lt_succ_iff]

/-- If radius `t₀ ≤ r` is the first radius with a non-`⊥` value, the output is that value. -/
theorem out_eq_of_first (A : Alg View Out) {G : Net} {v r t₀ : ℕ} {a : Out}
    (ht₀ : t₀ ≤ r) (ha : A (M.view G v t₀) t₀ = some a)
    (hbefore : ∀ t < t₀, A (M.view G v t) t = none) : M.out A G v r = some a := by
  refine out_mono A ?_ ht₀
  unfold out
  rw [List.range_succ, List.findSome?_append]
  have : (List.range t₀).findSome? (fun t => A (M.view G v t) t) = none := by
    rw [List.findSome?_eq_none_iff]
    intro t ht
    exact hbefore t (List.mem_range.mp ht)
  rw [this]
  simp [ha]

/-! ### Critical views: the corrected "maximally safe" neighbourhoods -/

/-- A view `x` of radius `t` is *`T`-critical* if it occurs (as the radius-`t` view of some node)
in a network `G'` whose time bound `T (size G')` is at most `t`. A node that sees a critical view
must already have stopped in any algorithm of locality `T`, because it cannot distinguish its
network from `G'`.

This is the corrected form of the paper's "maximally `T`-safe neighbourhood" (Definition 5.1):
the paper's notion "`t` is safe but `t + 1` is not" depends on the radius-`(t+1)` view, which
a node does not know after `t` rounds (see `MaxSafe.lean`). -/
def Critical (T : ℕ → ℕ) (x : View) (t : ℕ) : Prop :=
  ∃ G v, v < M.size G ∧ M.view G v t = x ∧ T (M.size G) ≤ t

variable (M) in
/-- Every node has a critical radius `≤ T (size G)`: its own network witnesses it. -/
theorem critical_self (T : ℕ → ℕ) (G : Net) (v : Fin (M.size G)) :
    M.Critical T (M.view G v (T (M.size G))) (T (M.size G)) :=
  ⟨G, v, v.2, rfl, le_rfl⟩

/-- **Stopping lemma.** If `A` solves a problem with locality `T` on a network `G'` in which the
radius-`t` view `x` occurs with `T (size G') ≤ t`, then every node `v` (of any network) whose
radius-`t` view is `x` has stopped by radius `t`, with the same output as the witness node. -/
theorem out_of_critical {P : M.Problem Out} {A : Alg View Out} {T : ℕ → ℕ} {G G' : Net}
    {v v' t : ℕ} (hA : M.SolvesOn P A T G') (hv' : v' < M.size G') (hT : T (M.size G') ≤ t)
    (hx : M.view G v t = M.view G' v' t) :
    M.out A G v t = M.out A G' v' t ∧ (M.out A G' v' t).isSome := by
  refine ⟨out_congr A hx, ?_⟩
  obtain ⟨lab, hlab, -⟩ := hA
  rw [out_mono A (hlab ⟨v', hv'⟩) hT]
  rfl

/-! ### Theorem 5.4: in uncomputable-LOCAL, an upper bound on `n` does not help -/

/-- **Theorem 5.4** of [Cruciani et al., PODC 2026] (corrected and generalized).
Let `{A_N}` be a family of (arbitrary, possibly uncomputable) LOCAL algorithms such that `A_N`
solves the problem `P` with locality `T` on every network with at most `N` nodes. If the output
alphabet is finite, there is a single algorithm `B` without any information on `n` that solves
`P` with locality `T` on every network. Moreover, on every network `G`, the output of `B`
coincides with that of `A_N` for some `N ≥ |V(G)|`, and `B` stops exactly at the first critical
radius.

No assumption on `T` is needed (the paper assumes `T` computable). `P` is an arbitrary problem
(not necessarily locally checkable). -/
theorem exists_boundFree [Finite Out] (P : M.Problem Out) (T : ℕ → ℕ) (A : ℕ → Alg View Out)
    (hA : M.SolvesWith M.UpperBound P A T) :
    ∃ B : Alg View Out, M.Solves P B T ∧
      (∀ x t, (B x t).isSome ↔ M.Critical T x t) ∧
      ∀ G, ∃ N, M.size G ≤ N ∧
        ∀ v : Fin (M.size G), M.out B G v (T (M.size G)) = M.out (A N) G v (T (M.size G)) := by
  classical
  -- Sandboxed simulation of `A N` on (a witness network of) a critical view.
  let sb : ℕ → View → ℕ → Option Out := fun N x t =>
    if h : M.Critical T x t then M.out (A N) h.choose h.choose_spec.choose t else none
  -- Ultrafilter limit along `N`.
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hlim : ∀ x t, ∃ a : Option Out, ∀ᶠ N in (U : Filter ℕ), sb N x t = a := by
    intro x t
    obtain ⟨a, ha⟩ := Ultrafilter.eq_pure_of_finite (U.map fun N => sb N x t)
    refine ⟨a, ?_⟩
    have : ({a} : Set (Option Out)) ∈ U.map fun N => sb N x t := by rw [ha]; simp
    exact this
  choose lim hlim using hlim
  have hge : ∀ m : ℕ, ∀ᶠ N in (U : Filter ℕ), m ≤ N := fun m =>
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop m)
  -- The limit is not `⊥` on critical views.
  have hlim_some : ∀ x t, M.Critical T x t → (lim x t).isSome := by
    intro x t h
    obtain ⟨N, hN1, hN2⟩ := ((hlim x t).and (hge (M.size h.choose))).exists
    rw [← hN1]
    simp only [sb, h, ↓reduceDIte]
    exact (out_of_critical (hA N _ hN2) h.choose_spec.choose_spec.1
      h.choose_spec.choose_spec.2.2 rfl).2
  let B : Alg View Out := fun x t => if M.Critical T x t then lim x t else none
  have hB : ∀ x t, (B x t).isSome ↔ M.Critical T x t := by
    intro x t
    by_cases h : M.Critical T x t
    · simp [B, h, hlim_some x t h]
    · simp [B, h]
  -- On a network `G`, `B` agrees with `A N` for a suitable `N`.
  have key : ∀ G, ∃ N, M.size G ≤ N ∧
      ∀ v : Fin (M.size G), M.out B G v (T (M.size G)) = M.out (A N) G v (T (M.size G)) := by
    intro G
    have hex : ∀ v : Fin (M.size G), ∃ t, M.Critical T (M.view G v t) t :=
      fun v => ⟨_, M.critical_self T G v⟩
    let tv : Fin (M.size G) → ℕ := fun v => Nat.find (hex v)
    have hev : ∀ᶠ N in (U : Filter ℕ), M.size G ≤ N ∧
        ∀ v : Fin (M.size G), sb N (M.view G v (tv v)) (tv v) = lim (M.view G v (tv v)) (tv v) :=
      (hge _).and (Filter.eventually_all.mpr fun v => hlim _ _)
    obtain ⟨N, hNG, hNv⟩ := hev.exists
    refine ⟨N, hNG, fun v => ?_⟩
    have hcrit : M.Critical T (M.view G v (tv v)) (tv v) := Nat.find_spec (hex v)
    have htv : tv v ≤ T (M.size G) := Nat.find_min' (hex v) (M.critical_self T G v)
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hlim_some _ _ hcrit)
    -- output of `B`
    have hBout : M.out B G v (T (M.size G)) = some a := by
      refine out_eq_of_first B htv ?_ ?_
      · simp [B, hcrit, ha]
      · intro t ht
        have : ¬ M.Critical T (M.view G v t) t := Nat.find_min (hex v) ht
        simp [B, this]
    -- output of `A N`
    have hsb := hNv v
    simp only [sb, hcrit, ↓reduceDIte] at hsb
    have hw := hcrit.choose_spec.choose_spec
    have hAout : M.out (A N) G v (tv v) = some a := by
      rw [out_congr (A N) (hw.2.1.trans rfl).symm, hsb, ha]
    rw [hBout, out_mono (A N) hAout htv]
  refine ⟨B, fun G => ?_, hB, key⟩
  obtain ⟨N, hNG, hN⟩ := key G
  obtain ⟨lab, hlab, hP⟩ := hA N G hNG
  exact ⟨lab, fun v => (hN v).trans (hlab v), hP⟩

/-- **Corollary 5.6.** In uncomputable-LOCAL, an upper bound `N ≥ n` given to all nodes does
not help to solve problems with a finite output alphabet: solvability with locality `T` is the
same with and without the bound. -/
theorem solvable_upperBound_iff [Finite Out] (P : M.Problem Out) (T : ℕ → ℕ) :
    (∃ A : ℕ → Alg View Out, M.SolvesWith M.UpperBound P A T) ↔
      ∃ B : Alg View Out, M.Solves P B T := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨B, hB, -⟩ := M.exists_boundFree P T A hA
    exact ⟨B, hB⟩
  · rintro ⟨B, hB⟩
    exact ⟨fun _ => B, fun _ G _ => hB G⟩

end Model

end LocalComputable
