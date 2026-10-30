import Mathlib

/-!
# Approximate order fairness: the model

Cai, Goharshady. *Brief Announcement: Delay-Optimal Transaction Order Fairness.* PODC 2026, §2.

* `n` nodes (a finite type `Node`), an honest set `H`, the rest Byzantine.
* A *profile* `ts : Node → Tx → ℝ` gives the timestamp each node reports for each transaction.
* `Δ`-synchrony (`Synchronous H Δ ts`): honest receive times of a transaction differ by at most `Δ`.
  Byzantine timestamps are unconstrained.
* `supp ts θ tx tx' = I_θ(tx, tx') = {i | ts i tx + θ ≤ ts i tx'}` and
  `Prec ts θ φ tx tx'` (`tx ≺_{θ,φ} tx'`) iff `|I_θ(tx, tx')| ≥ φ n`.
* The `(θ, φ)`-AOF graph is the relation `Prec ts θ φ`; it has a directed cycle iff `HasCycle`.

We also prove the generic facts used by all theorems: a relation is respected by some strict total
order iff it is acyclic (§2, "AOF is implementable exactly when its constraint graph is acyclic"),
and two potential-function criteria for acyclicity.
-/

namespace Podc.DelayOptimalOrderFairness

open Finset Relation

variable {Node Tx : Type*}

/-- A timestamp profile: `ts i tx` is the time at which node `i` reports to have received `tx`. -/
abbrev Profile (Node Tx : Type*) := Node → Tx → ℝ

section Defs

variable [Fintype Node]

/-- `I_θ(tx, tx') = {i ∈ S : ts_i(tx) + θ ≤ ts_i(tx')}` (§2). -/
noncomputable def supp (ts : Profile Node Tx) (θ : ℝ) (tx tx' : Tx) : Finset Node := by
  classical exact univ.filter fun i => ts i tx + θ ≤ ts i tx'

theorem mem_supp {ts : Profile Node Tx} {θ : ℝ} {tx tx' : Tx} {i : Node} :
    i ∈ supp ts θ tx tx' ↔ ts i tx + θ ≤ ts i tx' := by
  classical simp [supp]

/-- `tx ≺_{θ,φ} tx'` iff `|I_θ(tx, tx')| ≥ φ n` (§2). This relation is the `(θ, φ)`-AOF graph. -/
def Prec (ts : Profile Node Tx) (θ φ : ℝ) (tx tx' : Tx) : Prop :=
  φ * Fintype.card Node ≤ (supp ts θ tx tx').card

/-- Pairwise vote ("receive-order") relation used in §3: at least a `φ` fraction of the nodes
received `tx` strictly before `tx'`. -/
noncomputable def VotePrec (ts : Profile Node Tx) (φ : ℝ) (tx tx' : Tx) : Prop := by
  classical exact φ * Fintype.card Node ≤ (univ.filter fun i => ts i tx < ts i tx').card

end Defs

/-- `Δ_sync`-synchrony (§2): if one honest node receives a transaction, every honest node receives
it within `Δ`. Byzantine (non-`H`) nodes may report arbitrary timestamps. -/
def Synchronous (H : Finset Node) (Δ : ℝ) (ts : Profile Node Tx) : Prop :=
  ∀ i ∈ H, ∀ j ∈ H, ∀ tx, ts i tx ≤ ts j tx + Δ

/-- The graph of a relation has a directed cycle. -/
def HasCycle (R : Tx → Tx → Prop) : Prop := ∃ x, TransGen R x x

/-! ### Implementability ⇔ acyclicity -/

-- CSLib candidate (generic order theory)
/-- §2: "AOF is implementable exactly when its constraint graph is acyclic": a set of ordering
constraints can be respected by a (strict, total) ledger order iff it has no directed cycle. -/
theorem exists_strictTotalOrder_iff_not_hasCycle (R : Tx → Tx → Prop) :
    (∃ r : Tx → Tx → Prop, IsStrictTotalOrder Tx r ∧ ∀ x y, R x y → r x y) ↔ ¬ HasCycle R := by
  constructor
  · rintro ⟨r, hr, hR⟩ ⟨x, hx⟩
    have : ∀ a b, TransGen R a b → r a b := fun a b h => by
      induction h with
      | single h => exact hR _ _ h
      | tail _ h ih => exact _root_.trans ih (hR _ _ h)
    exact irrefl x (this x x hx)
  · intro hac
    let p : Tx → Tx → Prop := fun x y => x = y ∨ TransGen R x y
    have : IsPartialOrder Tx p :=
      { refl := fun _ => Or.inl rfl
        trans := by
          rintro a b c (rfl | hab) (rfl | hbc)
          · exact Or.inl rfl
          · exact Or.inr hbc
          · exact Or.inr hab
          · exact Or.inr (hab.trans hbc)
        antisymm := by
          rintro a b (rfl | hab) (h | hba)
          · rfl
          · rfl
          · exact h.symm
          · exact absurd ⟨a, hab.trans hba⟩ hac }
    obtain ⟨s, hs, hps⟩ := extend_partialOrder p
    refine ⟨fun x y => s x y ∧ x ≠ y, ?_, fun x y hxy => ⟨hps _ _ (Or.inr (.single hxy)), ?_⟩⟩
    · refine { trichotomous := fun a b h1 h2 => ?_, irrefl := fun a h => h.2 rfl, trans := ?_ }
      · by_contra hab
        rcases total_of s a b with h | h
        · exact h1 ⟨h, hab⟩
        · exact h2 ⟨h, Ne.symm hab⟩
      · rintro a b c ⟨hab, hab'⟩ ⟨hbc, -⟩
        refine ⟨_root_.trans hab hbc, ?_⟩
        rintro rfl
        exact hab' (antisymm hab hbc)
    · rintro rfl
      exact hac ⟨x, .single hxy⟩

/-! ### Acyclicity criteria -/

-- CSLib candidate (generic order theory)
/-- A strictly increasing potential rules out cycles. -/
theorem not_hasCycle_of_lt {R : Tx → Tx → Prop} (s : Tx → ℝ) (h : ∀ x y, R x y → s x < s y) :
    ¬ HasCycle R := by
  rintro ⟨x, hx⟩
  have : ∀ a b, TransGen R a b → s a < s b := fun a b hab => by
    induction hab with
    | single h' => exact h _ _ h'
    | tail _ h' ih => exact ih.trans (h _ _ h')
  exact lt_irrefl _ (this x x hx)

-- CSLib candidate (generic order theory)
/-- A path of `n ≥ 1` steps as a sequence. -/
theorem TransGen.exists_seq {R : Tx → Tx → Prop} {x y : Tx} (h : TransGen R x y) :
    ∃ n, 0 < n ∧ ∃ f : ℕ → Tx, f 0 = x ∧ f n = y ∧ ∀ i < n, R (f i) (f (i + 1)) := by
  induction h with
  | @single b hb =>
    refine ⟨1, one_pos, fun i => if i = 0 then x else b, by simp, by simp, ?_⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    simpa using hb
  | @tail b c _ hbc ih =>
    obtain ⟨n, hn, f, h0, hn', hf⟩ := ih
    refine ⟨n + 1, by omega, fun i => if i = n + 1 then c else f i, by simp [h0], by simp, ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · simpa [show i ≠ n + 1 by omega, show i ≠ n by omega] using hf i hi
    · simpa [hn'] using hbc

-- CSLib candidate (generic order theory)
/-- A cycle unrolls into an infinite periodic walk. -/
theorem HasCycle.exists_periodic {R : Tx → Tx → Prop} (h : HasCycle R) :
    ∃ g : ℕ → Tx, (∀ i, R (g i) (g (i + 1))) ∧ ∃ n, 0 < n ∧ ∀ i, g (i + n) = g i := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨n, hn, f, h0, hn', hf⟩ := TransGen.exists_seq hx
  refine ⟨fun i => f (i % n), fun i => ?_, n, hn, fun i => by simp⟩
  have hlt := Nat.mod_lt i hn
  have hmod : (i + 1) % n = (i % n + 1) % n := (Nat.mod_add_mod i n 1).symm
  by_cases hlast : i % n + 1 = n
  · show R (f (i % n)) (f ((i + 1) % n))
    rw [hmod, hlast, Nat.mod_self]
    have := hf _ hlt
    rwa [hlast, hn', ← h0] at this
  · show R (f (i % n)) (f ((i + 1) % n))
    rw [hmod, Nat.mod_eq_of_lt (a := i % n + 1) (by omega)]
    exact hf _ hlt

-- CSLib candidate (generic order theory)
/-- If along every infinite walk the potential strictly increases over every block of `k ≥ 1`
consecutive steps, the relation is acyclic. (This is the "`s_j < s_{j+k}` and sum around the
cycle" argument of Theorem 5.1.) -/
theorem not_hasCycle_of_kstep {R : Tx → Tx → Prop} (s : Tx → ℝ) (k : ℕ)
    (h : ∀ g : ℕ → Tx, (∀ i, R (g i) (g (i + 1))) → ∀ j, s (g j) < s (g (j + k))) :
    ¬ HasCycle R := by
  intro hc
  obtain ⟨g, hg, n, hn, hper⟩ := hc.exists_periodic
  have hmul : ∀ m, g (m * n) = g 0 := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Nat.succ_mul, hper, ih]
  have hinc : ∀ m, 0 < m → s (g 0) < s (g (m * k)) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · simpa using h g hg 0
      · calc s (g 0) < s (g (m * k)) := ih hm'
          _ < s (g (m * k + k)) := h g hg _
          _ = s (g ((m + 1) * k)) := by rw [Nat.succ_mul]
  have := hinc n hn
  rw [mul_comm, hmul] at this
  exact lt_irrefl _ this

end Podc.DelayOptimalOrderFairness
