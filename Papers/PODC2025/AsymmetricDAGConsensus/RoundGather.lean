import Podc.Computability.Distributed.Byzantine.AsyncBroadcast
import Podc.Computability.Distributed.AsymmetricQuorum

/-!
# Algorithm 2 (asymmetric gather by quorum replacement) and its `r`-round generalization

Amores-Sesar, Cachin, Villacis, Zanolini, *DAG-based Consensus with Asymmetric Trust*, PODC 2025
(arXiv:2505.17891).

Algorithm 2 replaces "`n − f` messages" in the three-round gather of Abraham et al. by "messages
from all members of one of my quorums". We model the natural `r`-round generalization (the paper
speaks of running the same pattern for more rounds, Section 3.2 and Appendix A):

* round `0`: arb-broadcast the input (`RMsg.val`); `acc ib 0` = the arb-delivered pairs;
* round `k + 1` (`k + 1 < r`): once a quorum `Q ∈ Qs p` is "complete at level `k`" (all members'
  level-`k` messages received), send `RMsg.dist (k+1) (acc ib k)` once; `acc ib (k+1)` = union
  of all received level-`k+1` sets;
* after `r` levels: once a quorum is complete at level `r - 1`, ag-deliver `acc ib (r-1)`.

Algorithm 2 is `protocol Qs 3` (`DISTRIBUTES` = level 1, `DISTRIBUTET` = level 2).

The model is the asynchronous interleaving model `Cslib.Byzantine.AsyncBroadcast`. The
asymmetric reliable broadcast of the inputs is represented by the `val` messages; in the
fault-free executions used here every delivery schedule of the reliable broadcast is possible,
so this is exact.

## Main results

* `reachable_run`: for a single-quorum system `q` and every `r ≥ 1`, the "everybody hears
  exactly its own quorum" schedule is a reachable execution in which every process
  ag-delivers the pairs of the processes in `R q (r-1) p` (`r`-fold quorum neighbourhood).
* `not_commonCore_of_run`: if no quorum is contained in all these neighbourhoods, the run has
  no common core.
-/

namespace Podc.AsymmetricDAGConsensus

open Cslib.Byzantine.AsyncBroadcast Cslib.AsymmetricQuorum

variable {P V : Type*}

/-! ### Generic batch lemmas for the `AsyncBroadcast` model -/

section Batch

variable {M I O : Type*} [DecidableEq P] {A : Protocol P M I O} {x : P → I} {k : FaultKind}
  {t : ℕ}

-- CSLib candidate (AsyncBroadcast): deliver a finite set of sent messages.
theorem reach_deliver_set (σ : State P M O) {X : Set (P × P × M)} (hX : X.Finite)
    (hs : ∀ e ∈ X, (e.2.1, e.2.2) ∈ σ.sent) :
    Reach A x k t σ { σ with rcv := σ.rcv ∪ X } := by
  induction X, hX using Set.Finite.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | @insert a X _ _ ih =>
    have ih := ih fun e he => hs e (Set.mem_insert_of_mem _ he)
    refine ih.tail ?_
    have := Step.deliver (A := A) (x := x) (k := k) (t := t)
      { σ with rcv := σ.rcv ∪ X } a.1 a.2.1 a.2.2 (hs a (Set.mem_insert _ _))
    convert this using 2
    ext e; simp

-- CSLib candidate (AsyncBroadcast): every process of `D` broadcasts one message allowed by
-- its guard in `σ`.
theorem reach_send_finset (σ : State P M O) (m : P → M) (D : Finset P)
    (hg : ∀ p ∈ D, p ∉ σ.bad ∧ A.send p (x p) (σ.inbox p) (σ.out p) (m p)) :
    Reach A x k t σ { σ with sent := σ.sent ∪ {e | ∃ p ∈ D, e = (p, m p)} } := by
  classical
  induction D using Finset.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | @insert a D ha ih =>
    have ih := ih fun p hp => hg p (Finset.mem_insert_of_mem hp)
    refine ih.tail ?_
    obtain ⟨hb, hga⟩ := hg a (Finset.mem_insert_self a D)
    have hout : ({ σ with sent := σ.sent ∪ {e | ∃ p ∈ D, e = (p, m p)} } : State P M O).out a =
        σ.out a := by
      ext m'
      simp only [State.mem_out, Set.mem_union, Set.mem_ofPred_eq, Prod.mk.injEq]
      constructor
      · rintro (h | ⟨p, hp, rfl, -⟩)
        · exact h
        · exact absurd hp ha
      · exact Or.inl
    have := Step.send (A := A) (x := x) (k := k) (t := t)
      { σ with sent := σ.sent ∪ {e | ∃ p ∈ D, e = (p, m p)} } a (m a) hb (by rw [hout]; exact hga)
    convert this using 2
    ext e
    simp only [Finset.mem_insert, exists_eq_or_imp, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_insert_iff]
    tauto

-- CSLib candidate (AsyncBroadcast): every process of `D` decides.
theorem reach_decide_finset (σ : State P M O) (o : P → O) (D : Finset P)
    (hdec : ∀ p, σ.dec p = none)
    (hg : ∀ p ∈ D, p ∉ σ.bad ∧ A.decide p (x p) (σ.inbox p) (σ.out p) (o p)) :
    Reach A x k t σ { σ with dec := fun p => if p ∈ D then some (o p) else none } := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    have : (fun _ : P => (none : Option O)) = σ.dec := funext fun p => (hdec p).symm
    simpa [this] using Relation.ReflTransGen.refl
  | @insert a D ha ih =>
    have ih := ih fun p hp => hg p (Finset.mem_insert_of_mem hp)
    refine ih.tail ?_
    obtain ⟨hb, hga⟩ := hg a (Finset.mem_insert_self a D)
    have := Step.decide (A := A) (x := x) (k := k) (t := t)
      { σ with dec := fun p => if p ∈ D then some (o p) else none } a (o a) hb
      (by simp [ha]) hga
    convert this using 2
    funext p
    by_cases hp : p = a
    · subst hp; simp
    · simp [hp]

end Batch

/-! ### The protocol -/

/-- Messages of the round-based gather: the arb-broadcast input, and the level-`k` sets
(`DISTRIBUTES` is level 1, `DISTRIBUTET` level 2). -/
inductive RMsg (P V : Type*)
  | val (v : V)
  | dist (k : ℕ) (S : Set (P × V))

namespace RoundGather

/-- The arb-delivered pairs. -/
def delivered (ib : P → Set (RMsg P V)) : Set (P × V) := {sv | RMsg.val sv.2 ∈ ib sv.1}

/-- The accumulated set of level `k`: the delivered pairs for `k = 0`, the union of all
received level-`k` sets otherwise (the variables `S`, `T`, `U` of Algorithm 2). -/
def acc (ib : P → Set (RMsg P V)) : ℕ → Set (P × V)
  | 0 => delivered ib
  | k + 1 => {sv | ∃ s S, RMsg.dist (k + 1) S ∈ ib s ∧ sv ∈ S}

/-- `s`'s level-`k` message has been received. -/
def Has (ib : P → Set (RMsg P V)) (s : P) : ℕ → Prop
  | 0 => ∃ v, RMsg.val v ∈ ib s
  | k + 1 => ∃ S, RMsg.dist (k + 1) S ∈ ib s

/-- The `r`-round quorum-replacement gather; `protocol Qs 3` is Algorithm 2. -/
def protocol (Qs : P → Set (Finset P)) (r : ℕ) : Protocol P (RMsg P V) V (Set (P × V)) where
  send p x ib out m := m = RMsg.val x ∨ ∃ k, k + 1 < r ∧ (∃ Q ∈ Qs p, ∀ q ∈ Q, Has ib q k) ∧
      m = RMsg.dist (k + 1) (acc ib k) ∧ ∀ S, RMsg.dist (k + 1) S ∉ out
  decide p _ ib _ U := (∃ Q ∈ Qs p, ∀ q ∈ Q, Has ib q (r - 1)) ∧ U = acc ib (r - 1)

end RoundGather

/-- The common-core property of Definition 3.1 for a family of ag-delivered sets: there is a
process `i` of the guild `G`, a quorum `Q` of `i`, and a set `S` of pairs containing a pair
`(s, v)` for every `s ∈ Q`, such that every guild member that ag-delivered `U` has `S ⊆ U`. -/
def CommonCore (Qs : P → Set (Finset P)) (G : Set P) (dec : P → Option (Set (P × V))) : Prop :=
  ∃ i ∈ G, ∃ Q ∈ Qs i, ∃ S : Set (P × V), (∀ s ∈ Q, ∃ v, (s, v) ∈ S) ∧
    ∀ k ∈ G, ∀ U, dec k = some U → S ⊆ U

namespace RoundGather

/-! ### The canonical run of a single-quorum system -/

variable [DecidableEq P] (q : P → Finset P) (x : P → V)

/-- `R q k i`: the processes whose inputs reach `i` after `k + 1` levels when every process
listens exactly to its quorum: `R q 0 i = q i`, `R q (k+1) i = ⋃_{s ∈ q i} R q k s`. -/
def R : ℕ → P → Finset P
  | 0, i => q i
  | k + 1, i => (q i).biUnion (R k)

/-- The pairs `(s, x s)` for `s ∈ A`. -/
def img (A : Finset P) : Set (P × V) := {sv | sv.1 ∈ A ∧ sv.2 = x sv.1}

/-- Messages broadcast by `p` up to level `k`. -/
def runMsg (k : ℕ) (p : P) (m : RMsg P V) : Prop :=
  m = RMsg.val (x p) ∨ ∃ j < k, m = RMsg.dist (j + 1) (img x (R q j p))

/-- The state after levels `0, …, k` have been sent and delivered along the quorums. -/
def st (k : ℕ) : State P (RMsg P V) (Set (P × V)) where
  sent := {e | runMsg q x k e.1 e.2}
  rcv := {e | e.2.1 ∈ q e.1 ∧ runMsg q x k e.2.1 e.2.2}
  dec := fun _ => none
  bad := ∅

theorem inbox_st (k : ℕ) (i s : P) (m : RMsg P V) :
    m ∈ (st q x k).inbox i s ↔ s ∈ q i ∧ runMsg q x k s m := Iff.rfl

theorem acc_st {k j : ℕ} (hj : j ≤ k) (i : P) :
    acc ((st q x k).inbox i) j = img x (R q j i) := by
  ext ⟨s, v⟩
  cases j with
  | zero =>
    simp only [acc, delivered, inbox_st, runMsg, Set.mem_ofPred_eq, img, R]
    constructor
    · rintro ⟨hs, h | ⟨j, -, h⟩⟩
      · exact ⟨hs, RMsg.val.inj h⟩
      · cases h
    · rintro ⟨hs, rfl⟩; exact ⟨hs, Or.inl rfl⟩
  | succ j =>
    simp only [acc, inbox_st, runMsg, Set.mem_ofPred_eq, img, R, Finset.mem_biUnion]
    constructor
    · rintro ⟨s', S, ⟨hs', h | ⟨j', -, h⟩⟩, hm⟩
      · cases h
      · obtain ⟨hj', rfl⟩ := RMsg.dist.inj h
        obtain rfl : j' = j := by omega
        exact ⟨⟨s', hs', hm.1⟩, hm.2⟩
    · rintro ⟨⟨s', hs', hm⟩, rfl⟩
      exact ⟨s', _, ⟨hs', Or.inr ⟨j, by omega, rfl⟩⟩, hm, rfl⟩

theorem has_st {k j : ℕ} (hj : j ≤ k) {i s : P} (hs : s ∈ q i) :
    Has ((st q x k).inbox i) s j := by
  cases j with
  | zero => exact ⟨x s, hs, Or.inl rfl⟩
  | succ j => exact ⟨img x (R q j s), hs, Or.inr ⟨j, by omega, rfl⟩⟩

variable {Qs : P → Set (Finset P)} (hq : ∀ p, q p ∈ Qs p)
include hq

/-- The canonical run reaches `st q x k` for every `k < r`. -/
theorem reachable_st [Fintype P] {r : ℕ} (fk : FaultKind) (t : ℕ) :
    ∀ k, k < r → Reachable (protocol Qs r) x fk t (st q x k) := by
  intro k hk
  induction k with
  | zero =>
    -- broadcast all inputs, then deliver them along the quorums
    have h1 := reach_send_finset (A := protocol Qs r) (x := x) (k := fk) (t := t)
      (State.init : State P (RMsg P V) (Set (P × V))) (fun p => RMsg.val (x p)) Finset.univ
      (fun p _ => ⟨Set.notMem_empty p, Or.inl rfl⟩)
    let σ1 : State P (RMsg P V) (Set (P × V)) :=
      { (State.init : State P (RMsg P V) (Set (P × V))) with
        sent := (State.init : State P (RMsg P V) (Set (P × V))).sent ∪
          {e | ∃ p ∈ (Finset.univ : Finset P), e = (p, RMsg.val (x p))} }
    let X : Set (P × P × RMsg P V) := {e | e.2.1 ∈ q e.1 ∧ e.2.2 = RMsg.val (x e.2.1)}
    have hX : X.Finite := by
      refine (Set.finite_range fun (ab : P × P) => (ab.1, ab.2, RMsg.val (x ab.2))).subset ?_
      rintro ⟨i, s, m⟩ ⟨-, hm⟩
      exact ⟨(i, s), by simp only at hm; simp [hm]⟩
    have h2 := reach_deliver_set (A := protocol Qs r) (x := x) (k := fk) (t := t) σ1 hX
      (by rintro ⟨i, s, m⟩ ⟨-, hm⟩; simp only at hm; subst hm; simp [σ1, State.init])
    have := h1.trans h2
    suffices heq : st q x 0 = ({ σ1 with rcv := σ1.rcv ∪ X }) by
      rw [heq]; exact this
    simp only [st, runMsg, State.init, σ1, X]
    congr 1
    · ext ⟨p, m⟩; simp
    · ext ⟨i, s, m⟩; simp
  | succ k ih =>
    have ih := ih (by omega)
    -- every process sends its level-`k+1` set
    have h1 := reach_send_finset (A := protocol Qs r) (x := x) (k := fk) (t := t)
      (st q x k) (fun p => RMsg.dist (k + 1) (img x (R q k p))) Finset.univ
      (fun p _ => ⟨Set.notMem_empty p, Or.inr ⟨k, hk, ⟨q p, hq p, fun s hs => has_st q x le_rfl hs⟩,
        by rw [acc_st q x le_rfl], fun S hS => by
          rcases hS with h | ⟨j, hj, h⟩
          · cases h
          · obtain ⟨h', -⟩ := RMsg.dist.inj h; omega⟩⟩)
    let σ1 : State P (RMsg P V) (Set (P × V)) :=
      { st q x k with sent := (st q x k).sent ∪
          {e | ∃ p ∈ (Finset.univ : Finset P), e = (p, RMsg.dist (k + 1) (img x (R q k p)))} }
    let X : Set (P × P × RMsg P V) :=
      {e | e.2.1 ∈ q e.1 ∧ e.2.2 = RMsg.dist (k + 1) (img x (R q k e.2.1))}
    have hX : X.Finite := by
      refine (Set.finite_range fun (ab : P × P) =>
        (ab.1, ab.2, RMsg.dist (k + 1) (img x (R q k ab.2)))).subset ?_
      rintro ⟨i, s, m⟩ ⟨-, hm⟩
      exact ⟨(i, s), by simp only at hm; simp [hm]⟩
    have h2 := reach_deliver_set (A := protocol Qs r) (x := x) (k := fk) (t := t) σ1 hX
      (by rintro ⟨i, s, m⟩ ⟨-, hm⟩; simp only at hm; subst hm; simp [σ1])
    have := ih.trans (h1.trans h2)
    suffices heq : st q x (k + 1) = ({ σ1 with rcv := σ1.rcv ∪ X }) by
      rw [heq]; exact this
    simp only [st, σ1, X]
    congr 1
    · ext ⟨p, m⟩
      simp only [runMsg, Set.mem_ofPred_eq, Set.mem_union, Finset.mem_univ, true_and,
        Prod.mk.injEq, exists_eq_left']
      constructor
      · rintro (h | ⟨j, hj, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact Or.inl (Or.inr ⟨j, hj, h⟩)
          · exact Or.inr h
      · rintro ((h | ⟨j, hj, h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, h⟩
        · exact Or.inr ⟨k, by omega, h⟩
    · ext ⟨i, s, m⟩
      simp only [runMsg, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨hs, h | ⟨j, hj, h⟩⟩
        · exact Or.inl ⟨hs, Or.inl h⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact Or.inl ⟨hs, Or.inr ⟨j, hj, h⟩⟩
          · exact Or.inr ⟨hs, h⟩
      · rintro (⟨hs, h | ⟨j, hj, h⟩⟩ | ⟨hs, h⟩)
        · exact ⟨hs, Or.inl h⟩
        · exact ⟨hs, Or.inr ⟨j, by omega, h⟩⟩
        · exact ⟨hs, Or.inr ⟨k, by omega, h⟩⟩

/-- The final state of the canonical run: every process has ag-delivered `img x (R q (r-1) p)`. -/
def fin (r : ℕ) : State P (RMsg P V) (Set (P × V)) :=
  { st q x (r - 1) with dec := fun p => some (img x (R q (r - 1) p)) }

/-- **The canonical run.** For every `r ≥ 1`, the fault-free schedule in which every process
hears exactly the members of its quorum is an execution of the `r`-round gather in which every
process ag-delivers the inputs of `R q (r - 1) p`. -/
theorem reachable_run [Fintype P] {r : ℕ} (hr : 1 ≤ r) (fk : FaultKind) (t : ℕ) :
    Reachable (protocol Qs r) x fk t (fin q x r) := by
  have h0 := reachable_st (r := r) q x hq fk t (r - 1) (by omega)
  have h1 := reach_decide_finset (A := protocol Qs r) (x := x) (k := fk) (t := t)
    (st q x (r - 1)) (fun p => img x (R q (r - 1) p)) Finset.univ (fun _ => rfl)
    (fun p _ => ⟨Set.notMem_empty p, ⟨q p, hq p, fun s hs => has_st q x le_rfl hs⟩,
      (acc_st q x le_rfl p).symm⟩)
  have heq : fin q x r = ({ st q x (r - 1) with
      dec := fun p => if p ∈ Finset.univ then some (img x (R q (r - 1) p)) else none }) := by
    simp [fin]
  rw [heq]; exact h0.trans h1

omit hq in
/-- If no quorum `q i` is contained in all neighbourhoods `R q (r-1) k`, the canonical run has
no common core (for any guild containing the witnesses `k`). -/
theorem not_commonCore_of_run {r : ℕ} (G : Set P)
    (h : ∀ i, ∃ k ∈ G, ¬ q i ⊆ R q (r - 1) k) :
    ¬ CommonCore (fun i => ({q i} : Set (Finset P))) G (fin q x r).dec := by
  rintro ⟨i, -, Q, hQ, S, hS, hcore⟩
  simp only [Set.mem_singleton_iff] at hQ
  subst hQ
  obtain ⟨k, hk, hnot⟩ := h i
  apply hnot
  intro s hs
  obtain ⟨v, hv⟩ := hS s hs
  exact (hcore k hk _ rfl hv).1

end RoundGather

end Podc.AsymmetricDAGConsensus
