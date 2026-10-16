import Papers.PODC2021.ScannableBinaryObjects.Exec

/-!
# Lemma 5 of Ovens (PODC 2021), relativized to a stage

The paper proves Lemma 5 for an implementation `I` and then (Lemma 7) simulates a smaller
implementation `I'` with one component, `h` processes and `h` base objects fewer. We avoid
building `I'`: instead we prove Lemma 5 for a *stage* of `I` — a reachable configuration `X`
(reached by `ε`), a set `A` of *active* processes (containing the updater `p₀`), a set `F` of
*frozen* base objects and a number `k'` of *live* components such that

* all active processes are idle in `X`, the components `≥ k' - 1` are `0` in `X`, and
* no execution from `X` by active processes that only updates live components changes `F`.

The initial configuration with all processes active, no frozen object and `k' = k` is a stage.
The paper's executions of `I'` are exactly the restricted executions (`Lim A k'`) of `I` from
the stage, so Lemma 5 for stages is Lemma 5 for `I'`.

`vec k' t` (`t < 2^(k'-1)`) are distinct vectors with `1` in the top live component `k' - 1` and
`0` above it (paper: `V_{t+1}`); `Vset k' j = {vec k' t | t < j}` (paper: `𝒱_j`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

/-! ### The vectors `V_j` -/

/-- The `t`-th vector with `1` in component `k' - 1`, `0` above, and the binary digits of `t`
below. -/
def vec (k' t : ℕ) : Fin k → Bool := fun c =>
  if c.val + 1 < k' then t.testBit c.val else decide (c.val + 1 = k')

/-- Paper: `𝒱_j = {V_1, …, V_j}`. -/
def Vset (k' j : ℕ) : Set (Fin k → Bool) := {v | ∃ t < j, v = vec k' t}

lemma vec_top {k' t : ℕ} {top : Fin k} (htop : top.val + 1 = k') : vec k' t top = true := by
  simp [vec, htop]

lemma vec_high {k' t : ℕ} {c : Fin k} (hc : k' ≤ c.val) : vec k' t c = false := by
  simp only [vec]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; simp; omega

lemma vec_inj {k' t t' : ℕ} (hk : k' ≤ k) (ht : t < 2 ^ (k' - 1)) (ht' : t' < 2 ^ (k' - 1))
    (h : (vec k' t : Fin k → Bool) = vec k' t') : t = t' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i + 1 < k'
  · have := congrFun h ⟨i, by omega⟩
    simpa [vec, hi] using this
  · have h2 : 2 ^ (k' - 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

lemma Vset_top {k' j : ℕ} {top : Fin k} (htop : top.val + 1 = k') {v : Fin k → Bool}
    (hv : v ∈ Vset k' j) : v top = true := by
  obtain ⟨t, -, rfl⟩ := hv; exact vec_top htop

lemma Vset_mono {k' j j' : ℕ} (h : j ≤ j') : (Vset k' j : Set (Fin k → Bool)) ⊆ Vset k' j' := by
  rintro v ⟨t, ht, rfl⟩; exact ⟨t, by omega, rfl⟩

lemma vec_mem_Vset_succ (k' j : ℕ) : (vec k' j : Fin k → Bool) ∈ Vset k' (j + 1) :=
  ⟨j, by omega, rfl⟩

lemma vec_not_mem_Vset {k' j : ℕ} (hk : k' ≤ k) (hj : j < 2 ^ (k' - 1)) :
    (vec k' j : Fin k → Bool) ∉ Vset k' j := by
  rintro ⟨t, ht, he⟩
  have := vec_inj hk hj (by omega) he
  omega

/-! ### Stages -/

/-- Components `≥ k' - 1` of `v` are `0`. -/
def High (k' : ℕ) (v : Fin k → Bool) : Prop := ∀ c : Fin k, k' ≤ c.val + 1 → v c = false

variable {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}

/-- A stage of the implementation `I` (see the module docstring). -/
structure Stage (I : Impl (scannable O) B P L) (p₀ : P) (ε : List (Label P (scannable O)))
    (X : Config (scannable O) B P L) (A : Finset P) (F : Finset ι) (k' : ℕ) : Prop where
  run : I.run ε = some X
  su : SUExec p₀ ε
  p0A : p₀ ∈ A
  idle : ∀ p ∈ A, X.pend p = none
  k'pos : 1 ≤ k'
  k'le : k' ≤ k
  high : High k' (curVal p₀ ε)
  frozen : ∀ β G, Lim p₀ A k' β → I.runFrom X β = some G → ∀ i ∈ F, G.mem i = X.mem i

/-- The initial configuration is a stage: all processes active, nothing frozen, all components
live. -/
lemma stage_init [Fintype P] (I : Impl (scannable O) B P L) (p₀ : P) (hk : 1 ≤ k) :
    Stage I p₀ [] I.initCfg Finset.univ (∅ : Finset ι) k :=
  { run := rfl
    su := fun _ _ h => by simp at h
    p0A := Finset.mem_univ _
    idle := fun _ _ => rfl
    k'pos := hk
    k'le := le_rfl
    high := fun _ _ => by simp [curVal, valAt]; rfl
    frozen := fun _ _ _ _ i hi => by simp at hi }

/-- Fewer active processes: still a stage. -/
lemma Stage.shrink {I : Impl (scannable O) B P L} {p₀ : P} {ε X} {A A' : Finset P} {F : Finset ι}
    {k' : ℕ} (h : Stage I p₀ ε X A F k') (hA : A' ⊆ A) (hp : p₀ ∈ A') :
    Stage I p₀ ε X A' F k' :=
  { h with
    p0A := hp
    idle := fun p hp' => h.idle p (hA hp')
    frozen := fun β G hβ => h.frozen β G (hβ.mono hA le_rfl) }

/-- The conclusion of Lemma 5 for `j`: execution `α` from the stage configuration `X` to `Xj`,
remaining active processes `Aj` (`j` scanners fewer), and `j` base objects `Bj` (outside `F`)
that no restricted `𝒱_j`-absent execution of `Aj` from `Xj` changes. -/
structure L5Res (I : Impl (scannable O) B P L) (p₀ : P) (ε : List (Label P (scannable O)))
    (X : Config (scannable O) B P L) (A : Finset P) (F : Finset ι) (k' j : ℕ)
    (α : List (Label P (scannable O))) (Xj : Config (scannable O) B P L) (Aj : Finset P)
    (Bj : Finset ι) : Prop where
  run : I.runFrom X α = some Xj
  lim : Lim p₀ A k' α
  sub : Aj ⊆ A
  p0 : p₀ ∈ Aj
  card : Aj.card + j = A.card
  disj : Disjoint Bj F
  bcard : Bj.card = j
  /-- (a) -/
  idle : ∀ p ∈ Aj, Xj.pend p = none
  /-- (b) -/
  high : High k' (curVal p₀ (ε ++ α))
  /-- (c) -/
  fixed : ∀ β G, Lim p₀ Aj k' β → Absent p₀ (Vset k' j) (ε ++ α) β → I.runFrom Xj β = some G →
    ∀ i ∈ Bj, G.mem i = Xj.mem i

end Cslib.SharedMemory.Scannable
