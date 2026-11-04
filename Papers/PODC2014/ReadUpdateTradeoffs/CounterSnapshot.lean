import Papers.PODC2014.ReadUpdateTradeoffs.UpdateLB
import Cslib.Computability.Distributed.SharedMemory.Objects.Snapshot

/-!
# Theorem 1 and Corollary 1 of Hendler–Khait (PODC'14): counters and snapshots

Instances of the generic tradeoff `update_lower_bound` for

* counters (`counterObj`: `inc` / `read`) — Theorem 1;
* single-writer snapshots (`snapObj n`: `update p 1` by process `p` / `scan`) — Corollary 1.

The paper derives Corollary 1 from Theorem 1 by a reduction (a counter built from a snapshot);
we instead apply the generic theorem directly to the snapshot, which avoids composing
implementations.

Each theorem is stated non-asymptotically: if the read completes within `R` solo steps, then
some update takes at least `s` steps for some `s` with `N ≤ R · 3^s + 1`, i.e.
`s ≥ log₃((N − 1)/R)`; the asymptotic statements `Ω(log (N / f(N)))` are in `Asymptotic.lean`.
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

/-- Operations of a counter. -/
inductive CtrOp where
  | inc
  | read
  deriving DecidableEq

/-- A counter over `ℕ` (initially `0`): `inc` increments (and returns `0`), `read` returns the
number of preceding increments. -/
abbrev counterObj : ObjSpec where
  State := ℕ
  Op := CtrOp
  Resp := ℕ
  init := 0
  δ q
    | .inc => (q + 1, 0)
    | .read => (q, q)

lemma counter_runOps {P : Type} (l : List P) (q : ℕ) :
    counterObj.runOps q (l.map (fun _ => (CtrOp.inc : counterObj.Op))) = q + l.length := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ObjSpec.runOps_cons]
    rw [ih]; simp only [List.length_cons]; omega

variable {P : Type} [Fintype P] [DecidableEq P]

lemma counter_reveals (r : P) :
    Reveals counterObj r (fun _ => (CtrOp.inc : counterObj.Op)) (CtrOp.read : counterObj.Op) := by
  intro q hqr l₁ l₂ hnd₁ hl₁ hnd₂ hl₂ heq
  unfold respAfter at heq
  rw [counter_runOps, counter_runOps] at heq
  change 0 + l₁.length = 0 + l₂.length at heq
  have h1 : l₁.toFinset = Finset.univ.erase r := by
    ext p; simp [hl₁ p]
  have h2 : l₂.toFinset ⊆ (Finset.univ.erase r).erase q := by
    intro p hp; simp only [List.mem_toFinset] at hp; simp [(hl₂ p hp).1, (hl₂ p hp).2]
  have c1 := List.toFinset_card_of_nodup hnd₁
  have c2 := List.toFinset_card_of_nodup hnd₂
  rw [h1] at c1
  have c3 := Finset.card_le_card h2
  have hq : q ∈ Finset.univ.erase r := by simp [hqr]
  rw [Finset.card_erase_of_mem hq] at c3
  have : 0 < (Finset.univ.erase r).card := Finset.card_pos.2 ⟨q, hq⟩
  omega

variable {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}

/-- **Theorem 1 of Hendler–Khait, PODC'14 (non-asymptotic form).** Let `I` be a linearizable
`N`-process implementation of a counter from read/write/CAS base objects, in which every process
may increment. If a `read` by `r` completes within `R` solo steps, then for every `k` with
`R · 3^k + 1 < N`, some execution has an increment that has already taken `k + 1` steps. -/
theorem counter_tradeoff {I : Impl counterObj (RWC ι V v₀) P L} (hlin : I.Linearizable) (r : P)
    (hall : ∀ p, p ≠ r → I.allowed p CtrOp.inc) {R : ℕ} (hR : SoloBound I r CtrOp.read R) (k : ℕ)
    (hk : R * 3 ^ k + 1 < Fintype.card P) :
    ∃ α, I.Valid α ∧ ∃ p, p ≠ r ∧ opsOf α p = [CtrOp.inc] ∧ respsOf α p = [] ∧
      k + 1 ≤ tauCount α p :=
  update_lower_bound (u := fun _ => (CtrOp.inc : counterObj.Op)) (rd := CtrOp.read) hlin
    (counter_reveals r) hall hR k hk

lemma snap_runOps {n : ℕ} (l : List (Fin n)) (s : Fin n → ℕ) :
    (snapObj n).runOps s (l.map (fun p => (SnapOp.update p 1 : (snapObj n).Op))) =
      fun j => if j ∈ l then 1 else s j := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ObjSpec.runOps_cons, snapObj_update]
    rw [ih]
    funext j
    by_cases hj : j ∈ l
    · simp [hj]
    · by_cases hja : j = a
      · subst hja; simp
      · simp [hj, hja, Function.update_of_ne hja]

lemma snap_reveals {n : ℕ} (r : Fin n) :
    Reveals (snapObj n) r (fun p => (SnapOp.update p 1 : (snapObj n).Op))
      (SnapOp.scan : (snapObj n).Op) := by
  intro q hqr l₁ l₂ _ hl₁ _ hl₂ heq
  unfold respAfter at heq
  rw [snap_runOps, snap_runOps, snapObj_scan, snapObj_scan] at heq
  have := congrFun heq q
  have h1 : q ∈ l₁ := (hl₁ q).2 hqr
  have h2 : q ∉ l₂ := fun h => (hl₂ q h).2 rfl
  simp [h1, h2] at this

/-- **Corollary 1 of Hendler–Khait, PODC'14 (non-asymptotic form).** Let `I` be a linearizable
`n`-process implementation of a single-writer snapshot from read/write/CAS base objects
(process `p` updates component `p`). If a `scan` by `r` completes within `R` solo steps, then
for every `k` with `R · 3^k + 1 < n`, some execution has an `update` that has already taken
`k + 1` steps. -/
theorem snapshot_tradeoff {n : ℕ} {I : Impl (snapObj n) (RWC ι V v₀) (Fin n) L}
    (hlin : I.Linearizable) (r : Fin n) (hall : ∀ p, p ≠ r → I.allowed p (SnapOp.update p 1))
    {R : ℕ} (hR : SoloBound I r SnapOp.scan R) (k : ℕ) (hk : R * 3 ^ k + 1 < n) :
    ∃ α, I.Valid α ∧ ∃ p, p ≠ r ∧ opsOf α p = [SnapOp.update p 1] ∧ respsOf α p = [] ∧
      k + 1 ≤ tauCount α p :=
  update_lower_bound (u := fun p => (SnapOp.update p 1 : (snapObj n).Op))
    (rd := SnapOp.scan) hlin (snap_reveals r) hall hR k (by simpa using hk)

end Podc.ReadUpdateTradeoffs
