import Papers.PODC2020.BezoutElection.Alg2Conc
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Algorithm 2: the global invariant

On *virtual configurations* (memory, local states, virtual program counters) and a ghost
counting, for every process, the competitions it won before (`wf`) and after (`wt`) setting
`finishing`:

* every register satisfies the per-register invariant (`abs`);
* `to_win` and the ghost counters (`g1`–`g4`): before `finishing`, `to_win + wf = W`; after it,
  `to_win + wt = 1`; `wf ≤ W`; once somebody set `finishing`, `Σ wf = W n`;
* the number of solved competitions (sum of the levels, plus pending writes of line N(11)) is the
  total number of wins (`g5`);
* the `leaders` fields contain exactly the processes that won with `finishing` set (`g6*`);
* a candidate flag is set only with `to_win ≥ 1` and for one register at a time (`g7`);
* a process about to return has seen all registers at level `U` and returns their leaders
  (`ret`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}

/-- Ghost counters of wins before / after setting `finishing`. -/
structure Ghost (P : Type) where
  wf : P → ℕ
  wt : P → ℕ

section Defs

variable (π : P → Equiv.Perm (Fin m))

/-- `q` has a pending write of `w` to the physical register `x`. -/
def PendAt (vpc : P → VPC Id) (q : P) (x : Fin m) (w : Reg Id) : Prop :=
  ∃ k : Fin m, vpc q = .pc (.write k.val w) ∧ π q k = x

/-- `q` has a pending write of line N(11). -/
def IsN11At (mem : Fin m → Reg Id) (vpc : P → VPC Id) (q : P) : Prop :=
  ∃ x w, PendAt π vpc q x w ∧ w.level = (mem x).level + 1

/-- The number of pending writes of line N(11). -/
noncomputable def n11Count (mem : Fin m → Reg Id) (vpc : P → VPC Id) : ℕ := by
  classical exact (univ.filter (IsN11At π mem vpc)).card

variable (pp : Params) (ids : P → Id)

/-- The global invariant. -/
structure GInv (mem : Fin m → Reg Id) (loc : P → St Id m) (vpc : P → VPC Id) (g : Ghost P) :
    Prop where
  abs : ∀ x, AInv pp.n pp.U ids (absAt π mem loc vpc x)
  me : ∀ q, (loc q).me = ids q
  g1 : ∀ q, (loc q).finishing = false → (loc q).toWin + g.wf q = pp.W ∧ g.wt q = 0
  g2 : ∀ q, (loc q).finishing = true → (loc q).toWin + g.wt q = 1
  g3 : ∀ q, g.wf q ≤ pp.W
  g4 : (∃ q, (loc q).finishing = true) → ∑ q, g.wf q = pp.W * pp.n
  g5 : ∑ x, (mem x).level + n11Count π mem vpc = ∑ q, (g.wf q + g.wt q)
  g6a : ∀ x a, a ∈ (mem x).leaders → ∃ q, ids q = a ∧ g.wt q = 1
  g6b : ∀ q, g.wt q = 1 → (∃ x, ids q ∈ (mem x).leaders) ∨
    (∃ x w, PendAt π vpc q x w ∧ w.level = (mem x).level + 1 ∧ ids q ∈ w.leaders)
  g6c : ∀ q x w, PendAt π vpc q x w → w.level = (mem x).level + 1 → ∀ a ∈ w.leaders,
    a ∈ (mem x).leaders ∨ (a = ids q ∧ g.wt q = 1)
  g7 : ∀ q k, (loc q).cand k = true → 1 ≤ (loc q).toWin ∧ ∀ k', k' ≠ k → (loc q).cand k' = false
  ret : ∀ q L, vpc q = .pc (.ret L) →
    (∀ x, (mem x).level = pp.U) ∧ L = univ.sup (fun x => (mem x).leaders)

end Defs

/-! ### Basic lemmas -/

section Lemmas

variable {π : P → Equiv.Perm (Fin m)}

lemma absAt_update (mem : Fin m → Reg Id) (loc : P → St Id m) (vpc : P → VPC Id) (q : P)
    (s : St Id m) (c : VPC Id) (x : Fin m) :
    absAt π mem (Function.update loc q s) (Function.update vpc q c) x =
      (absAt π mem loc vpc x).upd q (locX s ((π q).symm x) (vstatus c s ((π q).symm x))) := by
  unfold absAt AState.upd
  congr 1
  funext j
  by_cases hj : j = q
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma absAt_loc (mem : Fin m → Reg Id) (loc : P → St Id m) (vpc : P → VPC Id) (q : P)
    (x : Fin m) : (absAt π mem loc vpc x).loc q =
      locX (loc q) ((π q).symm x) (vstatus (vpc q) (loc q) ((π q).symm x)) := rfl

@[simp] lemma absAt_reg (mem : Fin m → Reg Id) (loc : P → St Id m) (vpc : P → VPC Id)
    (x : Fin m) : (absAt π mem loc vpc x).reg = mem x := rfl

/-- Counting a predicate that changes only at `q`. -/
lemma card_filter_change {A B : P → Prop} [DecidablePred A] [DecidablePred B] (q : P)
    (h : ∀ j, j ≠ q → (A j ↔ B j)) :
    (univ.filter B).card + (if A q then 1 else 0) = (univ.filter A).card + (if B q then 1 else 0) := by
  rw [card_filter, card_filter, ← add_sum_erase _ (fun j => if A j then 1 else 0) (mem_univ q),
    ← add_sum_erase _ (fun j => if B j then 1 else 0) (mem_univ q)]
  have : ∑ x ∈ univ.erase q, (if A x then 1 else 0) = ∑ x ∈ univ.erase q, (if B x then 1 else 0) :=
    sum_congr rfl (fun j hj => by rw [if_congr (h j (ne_of_mem_erase hj)) rfl rfl])
  rw [this]; omega

open Classical in
/-- `n11Count` when the N(11)-status changes only at `q`. -/
lemma n11Count_change (mem mem' : Fin m → Reg Id) (vpc vpc' : P → VPC Id) (q : P)
    (h : ∀ j, j ≠ q → (IsN11At π mem vpc j ↔ IsN11At π mem' vpc' j)) :
    n11Count π mem' vpc' + (if IsN11At π mem vpc q then 1 else 0) =
      n11Count π mem vpc + (if IsN11At π mem' vpc' q then 1 else 0) := by
  classical
  unfold n11Count
  convert card_filter_change q h

/-- A sum over `P` changing only at `q`. -/
lemma sum_update_eq (f : P → ℕ) (q : P) (a : ℕ) :
    ∑ j, Function.update f q a j + f q = ∑ j, f j + a := by
  rw [← add_sum_erase _ _ (mem_univ q), ← add_sum_erase _ f (mem_univ q)]
  have : ∑ x ∈ univ.erase q, Function.update f q a x = ∑ x ∈ univ.erase q, f x :=
    sum_congr rfl (fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)])
  rw [this]; simp; omega

end Lemmas

end BezoutElection.Alg2
