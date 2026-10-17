import Papers.PODC2015.CrashConsensusDigraph.MinMaxCore
import Papers.PODC2015.CrashConsensusDigraph.Necessity

/-!
# Algorithm Min-Max: Theorems 2 and 3

Algorithm Min-Max (Section 2.2) for binary inputs: `2f + 2` phases of `D` rounds each (the paper
uses `D = d`, the fault-tolerant diameter); in every round each node broadcasts its value `vᵢ`
to its out-neighbours and sets `vᵢ` to the maximum (odd phases `p = 1, 3, …`) or the minimum
(even phases) of the values received, including its own. After the last phase it outputs `vᵢ`.

* `minMax f D` — the algorithm (state: round counter and current value). Values are `Bool`
  (`false` = 0, `true` = 1); `recvd` is the set of received values, including the own one.
* **Theorem 3** (`theorem3`): Min-Max solves binary crash consensus in every graph with `f` CT
  node connectivity, for every phase length `D` bounding the fault-tolerant diameter (in
  particular `D = d` and `D = n − 1`, Section 3).
* **Theorem 2** (`theorem2`) and the tight characterization for binary consensus
  (`binary_consensus_iff`, with Theorem 1).
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V}

/-- The values received in a round together with one's own value `own`
(`{own} ∪ {m | some in-neighbour sent m}`; absent messages contribute nothing). -/
def recvd {α : Type*} [DecidableEq α] (own : α) (ib : V → Option α) : Finset α :=
  insert own (univ.image fun u => (ib u).getD own)

theorem recvd_nonempty {α : Type*} [DecidableEq α] (own : α) (ib : V → Option α) :
    (recvd own ib).Nonempty := insert_nonempty _ _

theorem mem_recvd {α : Type*} [DecidableEq α] {own b : α} {ib : V → Option α} :
    b ∈ recvd own ib ↔ b = own ∨ ∃ u, ib u = some b := by
  simp only [recvd, mem_insert, mem_image, mem_univ, true_and]
  constructor
  · rintro (h | ⟨u, hu⟩)
    · exact Or.inl h
    · cases h : ib u with
      | none => simp [h] at hu; exact Or.inl hu.symm
      | some m => simp [h] at hu; exact Or.inr ⟨u, by rw [h, hu]⟩
  · rintro (h | ⟨u, hu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, by simp [hu]⟩

theorem bool_max'_eq_true {s : Finset Bool} (h : s.Nonempty) : s.max' h = true ↔ true ∈ s := by
  constructor
  · intro h'; rw [← h']; exact max'_mem s h
  · intro h'; exact le_antisymm (by simp) (le_max' s true h')

theorem bool_min'_eq_false {s : Finset Bool} (h : s.Nonempty) : s.min' h = false ↔ false ∈ s := by
  constructor
  · intro h'; rw [← h']; exact min'_mem s h
  · intro h'; exact le_antisymm (min'_le s false h') (by simp)

/-- The Min/Max update of a binary value `own` with absorbing value `a`. -/
def mmUpdate (a own : Bool) (ib : V → Option Bool) : Bool :=
  if a then (recvd own ib).max' (recvd_nonempty _ _) else (recvd own ib).min' (recvd_nonempty _ _)

theorem mmUpdate_eq_iff {a own : Bool} {ib : V → Option Bool} :
    mmUpdate a own ib = a ↔ own = a ∨ ∃ u, ib u = some a := by
  cases a
  · simp only [mmUpdate, Bool.false_eq_true, ite_false, bool_min'_eq_false, mem_recvd]
    simp [eq_comm]
  · simp only [mmUpdate, ite_true, bool_max'_eq_true, mem_recvd]
    simp [eq_comm]

open Classical in
/-- A trajectory computed by `mmUpdate` from the delivered values follows the absorbing rule. -/
theorem absStep_of_mmUpdate {adv : Adversary V} {x : ℕ → V → Bool} {r : ℕ} {a : Bool}
    (h : ∀ w, x (r + 1) w = mmUpdate a (x r w)
      (fun u => if Delivers G adv r u w then some (x r u) else none)) :
    AbsStep G adv x r a := by
  classical
  intro w
  rw [h w, mmUpdate_eq_iff]
  apply or_congr_right
  constructor
  · rintro ⟨u, hu⟩
    split_ifs at hu with hd
    · exact ⟨u, hd, Option.some_injective _ hu⟩
  · rintro ⟨u, hd, hu⟩
    exact ⟨u, by simp [hd, hu]⟩

/-- **Algorithm Min-Max** with `2f + 2` phases of `D` rounds. State: (round counter, value). -/
def minMax (f D : ℕ) : Algorithm V Bool Bool (ℕ × Bool) Bool where
  init _ b := (0, b)
  send _ s _ := some s.2
  trans _ s ib := (s.1 + 1, mmUpdate (phaseVal D 0 s.1) s.2 ib)
  out _ s := if s.1 = (2 * f + 2) * D then some s.2 else none

theorem minMax_init {f D : ℕ} (u : V) (b : Bool) : (minMax f D).init u b = (0, b) := rfl

theorem minMax_out {f D : ℕ} (u : V) (s : ℕ × Bool) :
    (minMax f D).out u s = if s.1 = (2 * f + 2) * D then some s.2 else none := rfl

section Run

variable {f D : ℕ} {adv : Adversary V} {inp : V → Bool}

theorem minMax_counter (r : ℕ) (u : V) : (state G (minMax f D) adv inp r u).1 = r := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih =>
    show (state G (minMax f D) adv inp r u).1 + 1 = r + 1
    rw [ih]

open Classical in
theorem minMax_val_succ (r : ℕ) (w : V) :
    (state G (minMax f D) adv inp (r + 1) w).2 = mmUpdate (phaseVal D 0 r)
      (state G (minMax f D) adv inp r w).2 (fun u => if Delivers G adv r u w then
        some (state G (minMax f D) adv inp r u).2 else none) := by
  show mmUpdate (phaseVal D 0 (state G (minMax f D) adv inp r w).1) _ _ = _
  rw [minMax_counter]
  rfl

theorem minMax_absStep (r : ℕ) :
    AbsStep G adv (fun r u => (state G (minMax f D) adv inp r u).2) r (phaseVal D 0 r) :=
  absStep_of_mmUpdate fun w => minMax_val_succ r w

theorem minMax_decides_iff {u : V} {o : Bool} :
    Decides G (minMax f D) adv inp u o ↔ (state G (minMax f D) adv inp ((2 * f + 2) * D) u).2 = o := by
  constructor
  · rintro ⟨r, hr, -⟩
    rw [minMax_out, minMax_counter] at hr
    split_ifs at hr with h
    · subst h; exact Option.some_injective _ hr
  · intro h
    refine ⟨(2 * f + 2) * D, by simp only [minMax_out, minMax_counter, ↓reduceIte, h], fun r' hr' => ?_⟩
    simp only [minMax_out, minMax_counter, hr'.ne, ↓reduceIte]

end Run

/-- If all values are `c` before an absorbing-rule round, they are all `c` after it. -/
theorem AbsStep.const {adv : Adversary V} {x : ℕ → V → Bool} {r : ℕ} {a c : Bool}
    (h : AbsStep G adv x r a) (hc : ∀ w, x r w = c) (w : V) : x (r + 1) w = c := by
  have key := h w
  simp only [hc] at key
  by_cases hca : c = a
  · subst hca; exact key.mpr (Or.inl rfl)
  · have : x (r + 1) w ≠ a := fun h' => by
      rcases key.mp h' with h'' | ⟨_, _, h''⟩ <;> exact hca h''
    cases c <;> cases a
    · exact absurd rfl hca
    · simpa using this
    · simpa using this
    · exact absurd rfl hca

/-- **Theorem 3.** Algorithm Min-Max (with phases of `D ≥ d` rounds) solves binary crash
consensus in every graph satisfying `f` CT node connectivity. -/
theorem theorem3 {f D : ℕ} (hG : CTConn G f) (hD : FTDiamLE G f D) : Solves G f (minMax f D) := by
  intro adv hadm inp _
  set x : ℕ → V → Bool := fun r u => (state G (minMax f D) adv inp r u).2
  set T := (2 * f + 2) * D
  refine ⟨fun u _ => ⟨_, minMax_decides_iff.mpr rfl⟩, ?_, ?_⟩
  · -- agreement
    intro u w o o' hu hw ho ho'
    rw [minMax_decides_iff] at ho ho'
    obtain ⟨c, hc⟩ := minmax_core (x := x) hG hD hadm 0
      (fun r _ _ => by simpa using minMax_absStep (f := f) (D := D) (adv := adv) (inp := inp) r)
    rw [← ho, ← ho']
    simp only [Nat.zero_add] at hc
    exact (hc u (Adversary.alive_of_correct hu _)).trans (hc w (Adversary.alive_of_correct hw _)).symm
  · -- validity
    intro u o _ ho
    rw [minMax_decides_iff] at ho
    by_contra hno
    push Not at hno
    have hall : ∀ r w, x r w = !o := by
      intro r
      induction r with
      | zero =>
        intro w
        simp only [x, state_zero, minMax_init]
        have := hno w
        cases h : inp w <;> cases o <;> simp_all
      | succ r ih => exact (minMax_absStep r).const ih
    have := hall T u
    simp only [x] at this
    rw [ho] at this
    cases o <;> simp at this

/-- **Theorem 2.** If `G` satisfies `f` CT node connectivity, binary consensus is achievable in
`G` with at most `f` crash faults (by Min-Max with `D = d`). -/
theorem theorem2 {f : ℕ} (hG : CTConn G f) :
    ∃ alg : Algorithm V Bool Bool (ℕ × Bool) Bool, Solves G f alg :=
  ⟨minMax f (ftDiam G f), theorem3 hG (ftDiamLE_ftDiam f)⟩

/-- **Tight condition for binary consensus** (Theorems 1 and 2): binary crash consensus with at
most `f` crashes is solvable on `G` iff `G` satisfies `f` CT node connectivity. -/
theorem binary_consensus_iff {f : ℕ} :
    (∃ (M S : Type) (alg : Algorithm V Bool M S Bool), Solves G f alg) ↔ CTConn G f := by
  constructor
  · rintro ⟨M, S, alg, h⟩
    exact theorem1 (a := false) (b := true) (Set.mem_univ _) (Set.mem_univ _) (by simp) h
  · intro h
    exact ⟨Bool, ℕ × Bool, theorem2 h⟩

end CrashConsensusDigraph
