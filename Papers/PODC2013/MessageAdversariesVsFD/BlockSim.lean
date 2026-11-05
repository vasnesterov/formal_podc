import Papers.PODC2013.MessageAdversariesVsFD.Model

/-!
# Block simulation of synchronous rounds

A generic simulation theorem used for Theorem 6 of Raynal–Stainer (Appendix A.3): every round `R`
of an algorithm `A` designed for a "target" adversary is simulated by a block of `k ≥ 1` rounds of
the "host" adversary (rounds `k R, …, k R + k - 1`, in our `0`-based numbering). During a block
the processes flood (full information) the states they had at the beginning of the block; at the
end of the block process `i` applies `A`'s transition to the states it knows of the processes `j`
allowed by a filter `allow R j i` known to everybody (`allow = ⊤`: plain flooding; the PAIRS
simulation of Part 4 discards the messages not exchanged by the pair of the round).

The simulated (induced) pattern is `blockPat k allow p`: `j → i` in simulated round `R` iff
`allow R j i` and there is a journey from `j` to `i` inside block `R`. The main result
`solvable_of_blockPat`: if the induced pattern of every host pattern is in the target adversary,
then every task solvable under the target adversary is solvable under the host adversary (with the
strong semantics `Solvable`: every process outputs).
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.HeardOf (Graph Hears StepFn conf next msgs)
open Cslib.DynNet (Journey)

variable {P X Y : Type}

/-- The pattern induced by blocks of `k` rounds of `p` with filter `allow`: in simulated round
`R` (`0`-based), `i` receives the message of `j` iff `allow R j i` and some journey of `p` leads
from `j` at time `k R` to `i` at time `k R + k`. -/
def blockPat (k : ℕ) (allow : ℕ → Graph P) (p : ℕ → Graph P) : ℕ → Graph P :=
  fun R j i => allow R j i ∧ Journey p (k * R) j (k * R + k) i

namespace BlockSim

variable {σ : Type}

/-- Local state of the simulating (host) algorithm: the current host round, the identity of the
process, and the simulated states (at the beginning of the current block) it knows. -/
structure St (P σ : Type) where
  /-- Number of host rounds executed so far. -/
  time : ℕ
  /-- The identity of the process. -/
  me : P
  /-- The known simulated states of the current block (`none`: unknown). -/
  known : P → Option σ

open Classical in
/-- Union of the knowledge carried by the received messages. -/
noncomputable def merge (M : P → Option (St P σ)) (j : P) : Option σ :=
  if h : ∃ v, ∃ l m, M l = some m ∧ m.known j = some v then some (Classical.choose h) else none

open Classical in
/-- One host round of process `i` receiving the host states `M` (`M i` is its own state): merge
the received knowledge; at the end of a block, apply `A`'s transition to the known states of the
allowed processes and start a new block knowing only the new own simulated state. -/
noncomputable def simStep (A : Alg P X Y σ) (k : ℕ) (allow : ℕ → Graph P) :
    StepFn P (St P σ) := fun i M =>
  let c := ((M i).map St.time).getD 0
  if (c + 1) % k = 0 then
    ⟨c + 1, i, fun j => if j = i then
      some (A.step i (fun l => if l = i ∨ allow (c / k) l i then merge M l else none))
      else none⟩
  else ⟨c + 1, i, merge M⟩

open Classical in
theorem simStep_eq (A : Alg P X Y σ) (k : ℕ) (allow : ℕ → Graph P) (i : P)
    (M : P → Option (St P σ)) (c : ℕ) (hc : ((M i).map St.time).getD 0 = c) :
    simStep A k allow i M =
      if (c + 1) % k = 0 then
        ⟨c + 1, i, fun j => if j = i then
          some (A.step i (fun l => if l = i ∨ allow (c / k) l i then merge M l else none))
          else none⟩
      else ⟨c + 1, i, merge M⟩ := by
  subst hc; rfl

open Classical in
/-- The host algorithm simulating `A` with blocks of `k` rounds and filter `allow`; its output
function is `A`'s output function applied to the own simulated state. -/
noncomputable def alg (A : Alg P X Y σ) (k : ℕ) (allow : ℕ → Graph P) : Alg P X Y (St P σ) where
  init i v := ⟨0, i, fun j => if j = i then some (A.init i v) else none⟩
  step := simStep A k allow
  out m := (m.known m.me).bind A.out

theorem div_mod_succ {k : ℕ} (hk : 0 < k) (t : ℕ) :
    ((t + 1) % k = 0 ∧ (t + 1) / k = t / k + 1 ∧ t + 1 = k * (t / k) + k) ∨
      ((t + 1) % k ≠ 0 ∧ (t + 1) / k = t / k) := by
  have h1 := Nat.div_add_mod t k
  have h2 := Nat.mod_lt t hk
  rcases Nat.lt_or_ge (t % k + 1) k with h | h
  · right
    have e : t + 1 = (t % k + 1) + k * (t / k) := by omega
    rw [e, Nat.add_mul_div_left _ _ hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h,
      Nat.div_eq_of_lt h]
    omega
  · left
    have e : t + 1 = k * (t / k + 1) := by rw [Nat.mul_add]; omega
    refine ⟨?_, ?_, by rw [e, Nat.mul_add, Nat.mul_one]⟩
    · rw [e]; exact Nat.mul_mod_right _ _
    · rw [e, Nat.mul_div_cancel_left _ hk]

variable (A : Alg P X Y σ) {k : ℕ} (allow : ℕ → Graph P) (x : P → X) (p : ℕ → Graph P)

open Classical in
/-- **Simulation invariant.** After `t` host rounds, process `i` knows exactly the simulated
states (of round `t / k` of `A` under the induced pattern) of the processes `j` having a journey
to `i` since the beginning of the current block. -/
theorem run_eq (hk : 0 < k) (t : ℕ) (i : P) :
    (alg A k allow).run x p t i =
      ⟨t, i, fun j => if Journey p (k * (t / k)) j t i
        then some (A.run x (blockPat k allow p) (t / k) j) else none⟩ := by
  induction t generalizing i with
  | zero =>
    simp only [Alg.run, Cslib.HeardOf.conf_zero, alg, Nat.zero_div, Nat.mul_zero]
    congr 1
    funext j
    simp only [Cslib.DynNet.journey_self_iff]
    split_ifs with h
    · subst h; rfl
    · rfl
  | succ t ih =>
    have hle : k * (t / k) ≤ t := Nat.mul_div_le t k
    -- the merged knowledge
    have hM : merge (msgs (p t) ((alg A k allow).run x p t) i) = fun j =>
        if Journey p (k * (t / k)) j (t + 1) i
        then some (A.run x (blockPat k allow p) (t / k) j) else none := by
      funext j
      unfold merge
      rw [Cslib.DynNet.journey_succ_iff hle]
      by_cases hj : ∃ y, Journey p (k * (t / k)) j t y ∧ (y = i ∨ p t y i)
      · obtain ⟨y, hy, hyi⟩ := hj
        have hex : ∃ v, ∃ l m, msgs (p t) ((alg A k allow).run x p t) i l = some m ∧
            m.known j = some v := by
          refine ⟨A.run x (blockPat k allow p) (t / k) j, y, (alg A k allow).run x p t y, ?_, ?_⟩
          · simp only [msgs]
            exact ite_eq_left (show Hears (p t) i y from hyi)
          · rw [ih y]; simp [hy]
        rw [dite_eq_left hex, ite_eq_left ⟨y, hy, hyi⟩]
        obtain ⟨l, m, hl, hm⟩ := Classical.choose_spec hex
        simp only [msgs] at hl
        split_ifs at hl with hh
        cases hl
        rw [ih l] at hm
        simp only at hm
        split_ifs at hm
        exact hm.symm
      · rw [ite_eq_right hj, dite_eq_right]
        rintro ⟨v, l, m, hl, hm⟩
        simp only [msgs] at hl
        split_ifs at hl with hh
        cases hl
        rw [ih l] at hm
        simp only at hm
        split_ifs at hm with hj'
        exact hj ⟨l, hj', hh⟩
    have hti : ((msgs (p t) ((alg A k allow).run x p t) i i).map St.time).getD 0 = t := by
      simp [msgs, Hears, ih i]
    show simStep A k allow i (msgs (p t) ((alg A k allow).run x p t) i) = _
    rw [simStep_eq A k allow i _ t hti, hM]
    rcases div_mod_succ hk t with ⟨h0, hdiv, he⟩ | ⟨h0, hdiv⟩
    · rw [ite_eq_left h0, hdiv]
      congr 1
      funext j
      rw [show k * (t / k + 1) = t + 1 by rw [Nat.mul_add, Nat.mul_one]; omega,
        Cslib.DynNet.journey_self_iff]
      by_cases hji : j = i
      · subst hji
        simp only [ite_true]
        show _ = some (next A.step (blockPat k allow p (t / k))
          (A.run x (blockPat k allow p) (t / k)) j)
        congr 1
        unfold next
        congr 1
        funext l
        simp only [msgs, Hears, blockPat]
        rw [he]
        by_cases hlj : l = j
        · subst hlj; simp [Cslib.DynNet.Journey.self (Nat.le_add_right _ _)]
        · simp only [hlj, false_or]
          by_cases ha : allow (t / k) l j <;> simp [ha]
      · simp [hji]
    · rw [ite_eq_right h0, hdiv]

/-- The host output function at time `t` is `A`'s output function on the simulated state of
simulated round `t / k`. -/
theorem out_run (hk : 0 < k) (t : ℕ) (i : P) :
    (alg A k allow).out ((alg A k allow).run x p t i) =
      A.out (A.run x (blockPat k allow p) (t / k) i) := by
  rw [run_eq A allow x p hk]
  simp [alg, Cslib.DynNet.Journey.self (Nat.mul_div_le t k)]

theorem decided_iff (hk : 0 < k) (i : P) :
    (alg A k allow).Decided x p i ↔ A.Decided x (blockPat k allow p) i := by
  constructor
  · rintro ⟨t, ht⟩
    rw [out_run A allow x p hk] at ht
    exact ⟨_, ht⟩
  · rintro ⟨R, hR⟩
    refine ⟨k * R, ?_⟩
    rwa [out_run A allow x p hk, Nat.mul_div_cancel_left _ hk]

/-- The simulation preserves the (first) outputs. -/
theorem output_eq (hk : 0 < k) (i : P) :
    (alg A k allow).output x p i = A.output x (blockPat k allow p) i := by
  by_cases hA : A.Decided x (blockPat k allow p) i
  · have hB := (decided_iff A allow x p hk i).2 hA
    rw [Alg.output, dite_eq_left hB, Alg.output, dite_eq_left hA, out_run A allow x p hk]
    congr 3
    apply le_antisymm
    · have : Nat.find hB ≤ k * Nat.find hA := Nat.find_min' hB (by
        rw [out_run A allow x p hk, Nat.mul_div_cancel_left _ hk]; exact Nat.find_spec hA)
      exact Nat.div_le_of_le_mul this
    · apply Nat.find_min' hA
      have := Nat.find_spec hB
      rwa [out_run A allow x p hk] at this
  · have hB : ¬ (alg A k allow).Decided x p i := fun h => hA ((decided_iff A allow x p hk i).1 h)
    rw [Alg.output, dite_eq_right hB, Alg.output, dite_eq_right hA]

end BlockSim

/-- **Block simulation theorem.** Simulating every round by a block of `k ≥ 1` rounds of flooding
(filtered by `allow`): if the induced pattern `blockPat k allow p` of every pattern `p` of the
host adversary belongs to the target adversary, then every task solvable under the target
adversary is solvable under the host adversary. -/
theorem solvable_of_blockPat {Host Target : Adversary P} {k : ℕ} (hk : 0 < k)
    (allow : ℕ → Graph P) (h : ∀ p ∈ Host, blockPat k allow p ∈ Target) {T : Task P X Y}
    (hs : Solvable Target T) : Solvable Host T := by
  obtain ⟨σ, A, hA⟩ := hs
  refine ⟨_, BlockSim.alg A k allow, fun x hx p hp => ?_⟩
  obtain ⟨hdec, hval⟩ := hA x hx _ (h p hp)
  refine ⟨fun i => (BlockSim.decided_iff A allow x p hk i).2 (hdec i), ?_⟩
  have : (BlockSim.alg A k allow).output x p = A.output x (blockPat k allow p) :=
    funext (BlockSim.output_eq A allow x p hk)
  rw [this]; exact hval

end Podc.MessageAdversariesVsFD
