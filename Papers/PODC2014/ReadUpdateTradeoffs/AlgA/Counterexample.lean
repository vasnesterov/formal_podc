import Papers.PODC2014.ReadUpdateTradeoffs.AlgA.Defs

/-!
# Definition 9 leaves completed `WriteMax` operations without a linearization point

The paper linearizes a `WriteMax` operation `Φ` at the first event after which the root
*counts* `Φ` (Definition 9), where (Definition 8) a node `N` counts `Φ` after `E` if some
*visible* event `e` on `N.value` occurs in `E` and either `e` is issued in `Φ`, or `e` is issued by
a process `p` that earlier read a child `N'` of `N` at a time when `N'` already counted `Φ`.
An event is visible only if it changes the value of the object (Definition 1).

Invariant 1 (used to prove Lemma 9) claims that after the last write/CAS of `Φ` on a node `N`,
`N` counts `Φ`. This is false: below, with `N = 2` processes, process `0` performs
`WriteMax(3)` to completion, then process `1` performs `WriteMax(2)` to completion. All CASes of
process `1` succeed **trivially** (they install the value the node already holds), so no event
after the invocation of `WriteMax(2)` changes the root, and the root never counts `WriteMax(2)`.
Hence Definition 9 assigns no linearization point to this completed operation, Invariant 1 fails
for `N = root`, and the proof of Lemma 9 (which assumes that both CASes of a refresh can be
trivial only if *other* processes changed the node in between) breaks. The execution respects the
paper's assumptions (both operands are `≥ N`, each process writes once).

`Counts` below over-approximates Definition 8 (any value-changing event counts as visible, any
access of a child as a read), so `not_counts` is a statement about the paper's notion as well.
Theorem 5 itself is true (`AlgA/Lin.lean`, with different linearization points).
-/

namespace Podc.ReadUpdateTradeoffs.AlgA

open Cslib.SharedMemory

variable {N : ℕ} (lay : Layout N)

/-- The configuration after the first `j` labels of `α`. -/
noncomputable def cfgAt (α : List (Label (Fin N) maxRegObj)) (j : ℕ) : Option (Cfg N) :=
  (impl lay).run (α.take j)

/-- The `j`-th event of `α` changes the value of node `n` (a superset of the paper's visible
events on `n`). -/
def Visible (α : List (Label (Fin N) maxRegObj)) (n j : ℕ) : Prop :=
  ∃ C C', cfgAt lay α j = some C ∧ cfgAt lay α (j + 1) = some C' ∧ C'.mem n ≠ C.mem n

/-- The `j`-th event of `α` is a step of the operation instance `x`. -/
def IssuedIn (α : List (Label (Fin N) maxRegObj)) (x : OpId (Fin N)) (j : ℕ) : Prop :=
  α[j]? = some (.tau x.1) ∧ (respsOf (α.take j) x.1).length = x.2

/-- The `i`-th event of `α` is a step of `q` accessing node `n'`. -/
def Accesses (α : List (Label (Fin N) maxRegObj)) (q : Fin N) (n' i : ℕ) : Prop :=
  α[i]? = some (.tau q) ∧ ∃ C, cfgAt lay α i = some C ∧
    ∃ o k, (impl lay).act q (C.loc q) = .access n' o k

/-- **Definition 8** (over-approximated): node `n` counts the operation `x` after the first `t`
events of `α`. -/
inductive Counts (α : List (Label (Fin N) maxRegObj)) : ℕ → OpId (Fin N) → ℕ → Prop
  /-- A visible event on `n` issued in `x`. -/
  | own {n : ℕ} {x : OpId (Fin N)} {t j : ℕ} : j < t → Visible lay α n j → IssuedIn α x j →
      Counts α n x t
  /-- A visible event on `n` by a process that earlier read a child `n'` counting `x`. -/
  | prop {n n' : ℕ} {x : OpId (Fin N)} {t j i : ℕ} {q : Fin N} : j < t → Visible lay α n j →
      α[j]? = some (.tau q) → i < j → Accesses lay α q n' i → n' / 2 = n → Counts α n' x i →
      Counts α n x t

/-- A node counts `x` only through a visible event that follows a step of `x`'s process
(the argument of Lemma 7). -/
lemma Counts.exists_visible {α : List (Label (Fin N) maxRegObj)} {n : ℕ} {x : OpId (Fin N)}
    {t : ℕ} (h : Counts lay α n x t) :
    ∃ j j', j' ≤ j ∧ j < t ∧ α[j']? = some (.tau x.1) ∧ Visible lay α n j := by
  induction h with
  | own hj hv hi => exact ⟨_, _, le_rfl, hj, hi.1, hv⟩
  | prop hj hv _ hij _ _ _ ih =>
    obtain ⟨j₁, j', h1, h2, h3, -⟩ := ih
    exact ⟨_, j', by omega, hj, h3, hv⟩

/-! ### The concrete execution -/

/-- The tree of Figure 4 for `N = 2`: root `1`, `T_L` under `2` (leaves `4, 5`), `T_R` under `3`
(leaves `6, 7`). -/
def lay2 : Layout 2 where
  leaf
    | .inl v => 4 + v
    | .inr i => 6 + i
  two_le := by rintro (v | i) <;> dsimp only <;> omega
  inj := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) h <;> simp at h ⊢ <;> omega
  not_anc := by
    intro a b k hk
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hlt : ∀ c : Fin 2 ⊕ Fin 2, 4 ≤ (match c with | .inl v => 4 + (v : ℕ) | .inr i => 6 + i)
        ∧ (match c with | .inl v => 4 + (v : ℕ) | .inr i => 6 + i) < 8 := by
      rintro (⟨v, hv⟩ | ⟨v, hv⟩) <;> simp <;> omega
    obtain ⟨-, ha⟩ := hlt a
    obtain ⟨hb, -⟩ := hlt b
    intro h
    have : (match a with | .inl v => 4 + (v : ℕ) | .inr i => 6 + i) / 2 ^ k < 4 :=
      Nat.div_lt_of_lt_mul (by nlinarith)
    omega

instance (p : Fin 2) (o : MaxOp) : Decidable ((impl lay2).allowed p o) := isTrue trivial

/-- Process `0` runs `WriteMax(3)` solo to completion (18 accesses). -/
def exβ : List (Label (Fin 2) maxRegObj) :=
  [.inv 0 (.writeMax 3)] ++ List.replicate 18 (.tau 0) ++ [.ret 0 0]

/-- Then process `1` runs `WriteMax(2)` solo to completion (18 accesses). -/
def exγ : List (Label (Fin 2) maxRegObj) :=
  [.inv 1 (.writeMax 2)] ++ List.replicate 18 (.tau 1) ++ [.ret 1 0]

/-- The whole execution. -/
def exα : List (Label (Fin 2) maxRegObj) := exβ ++ exγ

lemma exα_crun : ((impl lay2).crun exα).isSome = true := by decide +kernel

/-- The execution is valid. -/
theorem exα_valid : (impl lay2).Valid exα := (impl lay2).valid_of_crun exα_crun

/-- `WriteMax(2)` of process `1` (instance `(1, 0)`) completes. -/
theorem exα_completed : Completed exα ((1 : Fin 2), 0) := by
  simp only [Completed]; decide

lemma exα_root_stable : ∀ j < 40, 20 ≤ j →
    ((impl lay2).crun (exα.take j)).map (fun C => C.mem 1) =
      ((impl lay2).crun (exα.take (j + 1))).map (fun C => C.mem 1) := by
  decide +kernel

/-- Is the label an internal step of process `1`? -/
def isTauOne : Label (Fin 2) maxRegObj → Bool
  | .tau q => q == 1
  | _ => false

lemma exα_tau_one' : ∀ j < 40, exα[j]?.map isTauOne = some true → 20 < j := by decide +kernel

lemma exα_tau_one (j : ℕ) (hj : j < 40) (h : exα[j]? = some (.tau 1)) : 20 < j :=
  exα_tau_one' j hj (by rw [h]; rfl)

lemma exα_length : exα.length = 40 := rfl

/-- **Counterexample to Invariant 1 / Definition 9 of [Hendler–Khait, PODC'14]**: in a valid
execution of Algorithm A, the operation `WriteMax(2)` of process `1` completes but the root never
counts it, so Definition 9 gives it no linearization point. -/
theorem not_counts : (impl lay2).Valid exα ∧ Completed exα ((1 : Fin 2), 0) ∧
    ∀ t, ¬ Counts lay2 exα 1 ((1 : Fin 2), 0) t := by
  refine ⟨exα_valid, exα_completed, fun t h => ?_⟩
  obtain ⟨j, j', hjj, -, hj', C, C', hC, hC', hne⟩ := h.exists_visible
  have hj'lt : j' < 40 := by
    have := (List.getElem?_eq_some_iff.1 hj').1
    simpa [exα_length] using this
  have h20 := exα_tau_one j' hj'lt hj'
  have hjlt : j < 40 := by
    by_contra hge
    have : exα.take (j + 1) = exα.take j := by
      rw [List.take_of_length_le (by rw [exα_length]; omega),
        List.take_of_length_le (by rw [exα_length]; omega)]
    simp only [cfgAt, this] at hC' hC
    rw [hC] at hC'
    cases hC'; exact hne rfl
  have hs := exα_root_stable j hjlt (by omega)
  simp only [cfgAt, Impl.run_eq_crun] at hC hC'
  rw [hC, hC'] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  exact hne hs.symm

end Podc.ReadUpdateTradeoffs.AlgA
