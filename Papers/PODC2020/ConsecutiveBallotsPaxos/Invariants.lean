import Papers.PODC2020.ConsecutiveBallotsPaxos.Model

/-!
# Inductive invariant of (Consecutive) Paxos

The invariant `Inv` collects the facts about reachable states used in the safety proof:

* acceptor-local facts (`maxBal` dominates every accepted/promised ballot, `last` is the highest
  accepted proposal);
* a promise for ballot `b` reports exactly the highest proposal its sender accepted below `b`
  (`prom_none`, `prom_some`) — this is where "an acceptor never accepts below a promised ballot"
  is used;
* Definition 8 (Accept Implies Propose, `acc_prop`), one proposal per ballot (`prop_unique`),
  and every proposal is justified by the messages present (`prop_ok`).
-/

namespace Podc.ConsecutiveBallotsPaxos

open Msg

variable {A V : Type*} [DecidableEq A]

/-- The inductive invariant. -/
structure Inv (QS : QuorumSystem A) (cp : Bool) (s : State A V) : Prop where
  acc_maxBal : ∀ a k w, accept a k w ∈ s.msgs → (k : WithBot ℕ) ≤ s.maxBal a
  acc_last : ∀ a k w, accept a k w ∈ s.msgs → ∃ k₀ w₀, s.last a = some (k₀, w₀) ∧ k ≤ k₀
  last_acc : ∀ a k w, s.last a = some (k, w) → accept a k w ∈ s.msgs
  last_maxBal : ∀ a k w, s.last a = some (k, w) → (k : WithBot ℕ) ≤ s.maxBal a
  prom_maxBal : ∀ a b r, promise a b r ∈ s.msgs → (b : WithBot ℕ) ≤ s.maxBal a
  prom_none : ∀ a b k w, promise a b none ∈ s.msgs → accept a k w ∈ s.msgs → b ≤ k
  prom_some : ∀ a b k w, promise a b (some (k, w)) ∈ s.msgs →
    k < b ∧ accept a k w ∈ s.msgs ∧ ∀ k' w', accept a k' w' ∈ s.msgs → k' < b → k' ≤ k
  acc_prop : ∀ a b v, accept a b v ∈ s.msgs → propose b v ∈ s.msgs
  prop_unique : ∀ b v w, propose b v ∈ s.msgs → propose b w ∈ s.msgs → v = w
  prop_ok : ∀ b v, propose b v ∈ s.msgs → ProposalOK QS cp s.msgs b v

omit [DecidableEq A] in
lemma inv_init (QS : QuorumSystem A) (cp : Bool) : Inv QS cp (init : State A V) where
  acc_maxBal := by simp [init]
  acc_last := by simp [init]
  last_acc := by simp [init]
  last_maxBal := by simp [init]
  prom_maxBal := by simp [init]
  prom_none := by simp [init]
  prom_some := by simp [init]
  acc_prop := by simp [init]
  prop_unique := by simp [init]
  prop_ok := by simp [init]

omit [DecidableEq A] in
/-- Adding a message that is not a second promise (for the same ballot) of an acceptor that
already promised preserves the Normal criterion. -/
lemma NormalClause.insert_msg {QS : QuorumSystem A} {M : Set (Msg A V)} {b : ℕ} {v : V}
    (h : NormalClause QS M b v) (m : Msg A V)
    (hm : ∀ a r, m = promise a b r → ∀ r', promise a b r' ∉ M) :
    NormalClause QS (insert m M) b v := by
  obtain ⟨Q, hQ, hall, hcase⟩ := h
  have key : ∀ a ∈ Q, ∀ r, promise a b r ∈ insert m M → promise a b r ∈ M := by
    intro a ha r hr
    rcases hr with hr | hr
    · obtain ⟨r', hr'⟩ := hall a ha
      exact absurd hr' (hm a r hr.symm r')
    · exact hr
  refine ⟨Q, hQ, fun a ha => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hall a ha; exact ⟨r, Set.mem_insert_of_mem _ hr⟩
  rcases hcase with hnone | ⟨a, ha, k, hk, hmax⟩
  · exact Or.inl fun a ha k w hmem => hnone a ha k w (key a ha _ hmem)
  · exact Or.inr ⟨a, ha, k, Set.mem_insert_of_mem _ hk,
      fun a' ha' k' w' hmem => hmax a' ha' k' w' (key a' ha' _ hmem)⟩

omit [DecidableEq A] in
lemma ConsecClause.mono {M M' : Set (Msg A V)} (hM : M ⊆ M') {b : ℕ} {v : V}
    (h : ConsecClause M b v) : ConsecClause M' b v := by
  obtain ⟨c, hc, a, ha⟩ := h
  exact ⟨c, hc, a, ha.imp (fun h => hM h) (fun h => hM h)⟩

omit [DecidableEq A] in
lemma ProposalOK.insert_msg {QS : QuorumSystem A} {cp : Bool} {M : Set (Msg A V)} {b : ℕ} {v : V}
    (h : ProposalOK QS cp M b v) (m : Msg A V)
    (hm : ∀ a r, m = promise a b r → ∀ r', promise a b r' ∉ M) :
    ProposalOK QS cp (insert m M) b v :=
  h.imp (fun h => h.insert_msg m hm) (fun ⟨h1, h2⟩ => ⟨h1, h2.mono (Set.subset_insert _ _)⟩)

lemma WithBot.coe_lt_of_le_of_lt {k b : ℕ} {x : WithBot ℕ} (h1 : (k : WithBot ℕ) ≤ x)
    (h2 : x < b) : k < b := WithBot.coe_lt_coe.mp (lt_of_le_of_lt h1 h2)

lemma WithBot.coe_le_of_le_of_le {k b : ℕ} {x : WithBot ℕ} (h1 : (k : WithBot ℕ) ≤ x)
    (h2 : x ≤ b) : k ≤ b := WithBot.coe_le_coe.mp (le_trans h1 h2)

theorem Inv.step {QS : QuorumSystem A} {cp : Bool} {s s' : State A V} (hI : Inv QS cp s)
    (hs : Step QS cp s s') : Inv QS cp s' := by
  obtain ⟨act, hen, rfl⟩ := hs
  cases act with
  | prepare b₀ =>
    simp only [Action.apply]
    constructor <;> simp only [Set.mem_insert_iff, reduceCtorEq, false_or]
    · exact hI.acc_maxBal
    · exact hI.acc_last
    · exact hI.last_acc
    · exact hI.last_maxBal
    · exact hI.prom_maxBal
    · exact hI.prom_none
    · exact hI.prom_some
    · exact hI.acc_prop
    · exact hI.prop_unique
    · intro b v h
      exact (hI.prop_ok b v h).insert_msg _ (by intro a r hr; cases hr)
  | promise a₀ b₀ =>
    obtain ⟨-, hlt⟩ := hen
    simp only [Action.apply]
    -- the new maxBal dominates the old one
    have hmono : ∀ a, s.maxBal a ≤ Function.update s.maxBal a₀ (b₀ : WithBot ℕ) a := by
      intro a
      by_cases ha : a = a₀
      · subst ha; simp only [Function.update_self]; exact hlt.le
      · simp [Function.update_of_ne ha]
    constructor
    · intro a k w h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      exact le_trans (hI.acc_maxBal a k w h) (hmono a)
    · intro a k w h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      exact hI.acc_last a k w h
    · intro a k w h
      exact Set.mem_insert_of_mem _ (hI.last_acc a k w h)
    · intro a k w h
      exact le_trans (hI.last_maxBal a k w h) (hmono a)
    · intro a b r h
      rcases h with h | h
      · simp only [promise.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        simp
      · exact le_trans (hI.prom_maxBal a b r h) (hmono a)
    · intro a b k w h hacc
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at hacc
      rcases h with h | h
      · simp only [promise.injEq] at h
        obtain ⟨rfl, rfl, hnone⟩ := h
        obtain ⟨k₀, w₀, hl, -⟩ := hI.acc_last a k w hacc
        rw [hl] at hnone; cases hnone
      · exact hI.prom_none a b k w h hacc
    · intro a b k w h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or]
      rcases h with h | h
      · simp only [promise.injEq] at h
        obtain ⟨rfl, rfl, hl⟩ := h
        refine ⟨WithBot.coe_lt_of_le_of_lt (hI.last_maxBal a k w hl.symm) hlt,
          hI.last_acc a k w hl.symm, fun k' w' hacc _ => ?_⟩
        obtain ⟨k₀, w₀, hl', hle⟩ := hI.acc_last a k' w' hacc
        rw [← hl] at hl'
        simp only [Option.some.injEq, Prod.mk.injEq] at hl'
        omega
      · exact hI.prom_some a b k w h
    · intro a b v h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      exact Set.mem_insert_of_mem _ (hI.acc_prop a b v h)
    · intro b v w h1 h2
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h1 h2
      exact hI.prop_unique b v w h1 h2
    · intro b v h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      refine (hI.prop_ok b v h).insert_msg _ ?_
      intro a r hr r' hr'
      simp only [promise.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      exact lt_irrefl _ (lt_of_le_of_lt (hI.prom_maxBal a₀ b₀ r' hr') hlt)
  | propose b₀ v₀ =>
    obtain ⟨hfresh, hok⟩ := hen
    simp only [Action.apply]
    constructor <;> simp only [Set.mem_insert_iff, reduceCtorEq, false_or]
    · exact hI.acc_maxBal
    · exact hI.acc_last
    · exact hI.last_acc
    · exact hI.last_maxBal
    · exact hI.prom_maxBal
    · exact hI.prom_none
    · exact hI.prom_some
    · intro a b v h; exact Or.inr (hI.acc_prop a b v h)
    · intro b v w h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · simp only [propose.injEq] at h1 h2; rw [h1.2, h2.2]
      · simp only [propose.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1; exact absurd h2 (hfresh w)
      · simp only [propose.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2; exact absurd h1 (hfresh v)
      · exact hI.prop_unique b v w h1 h2
    · intro b v h
      rcases h with h | h
      · simp only [propose.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact hok.insert_msg _ (by intro a r hr; cases hr)
      · exact (hI.prop_ok b v h).insert_msg _ (by intro a r hr; cases hr)
  | accept a₀ b₀ v₀ =>
    obtain ⟨hprop, hle⟩ := hen
    simp only [Action.apply]
    constructor
    · intro a k w h
      by_cases ha : a = a₀
      · subst ha; simp only [Function.update_self]
        rcases h with h | h
        · simp only [accept.injEq] at h; obtain ⟨-, rfl, -⟩ := h; exact le_rfl
        · exact le_trans (hI.acc_maxBal a k w h) hle
      · simp only [Function.update_of_ne ha]
        rcases h with h | h
        · simp only [accept.injEq] at h; exact absurd h.1 ha
        · exact hI.acc_maxBal a k w h
    · intro a k w h
      by_cases ha : a = a₀
      · subst ha; simp only [Function.update_self]
        refine ⟨b₀, v₀, rfl, ?_⟩
        rcases h with h | h
        · simp only [accept.injEq] at h; obtain ⟨-, rfl, -⟩ := h; exact le_rfl
        · exact WithBot.coe_le_of_le_of_le (hI.acc_maxBal a k w h) hle
      · simp only [Function.update_of_ne ha]
        rcases h with h | h
        · simp only [accept.injEq] at h; exact absurd h.1 ha
        · exact hI.acc_last a k w h
    · intro a k w h
      by_cases ha : a = a₀
      · subst ha
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Set.mem_insert _ _
      · simp only [Function.update_of_ne ha] at h
        exact Set.mem_insert_of_mem _ (hI.last_acc a k w h)
    · intro a k w h
      by_cases ha : a = a₀
      · subst ha
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact le_rfl
      · simp only [Function.update_of_ne ha] at h ⊢
        exact hI.last_maxBal a k w h
    · intro a b r h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      by_cases ha : a = a₀
      · subst ha; simp only [Function.update_self]
        exact le_trans (hI.prom_maxBal a b r h) hle
      · simp only [Function.update_of_ne ha]
        exact hI.prom_maxBal a b r h
    · intro a b k w h hacc
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      rcases hacc with hacc | hacc
      · simp only [accept.injEq] at hacc
        obtain ⟨rfl, rfl, -⟩ := hacc
        exact WithBot.coe_le_of_le_of_le (hI.prom_maxBal a b none h) hle
      · exact hI.prom_none a b k w h hacc
    · intro a b k w h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      obtain ⟨h1, h2, h3⟩ := hI.prom_some a b k w h
      refine ⟨h1, Set.mem_insert_of_mem _ h2, fun k' w' hacc hk' => ?_⟩
      rcases hacc with hacc | hacc
      · simp only [accept.injEq] at hacc
        obtain ⟨rfl, rfl, -⟩ := hacc
        have := WithBot.coe_le_of_le_of_le (hI.prom_maxBal a b _ h) hle
        omega
      · exact h3 k' w' hacc hk'
    · intro a b v h
      rcases h with h | h
      · simp only [accept.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact Set.mem_insert_of_mem _ hprop
      · exact Set.mem_insert_of_mem _ (hI.acc_prop a b v h)
    · intro b v w h1 h2
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h1 h2
      exact hI.prop_unique b v w h1 h2
    · intro b v h
      simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at h
      exact (hI.prop_ok b v h).insert_msg _ (by intro a r hr; cases hr)

theorem Reachable.inv {QS : QuorumSystem A} {cp : Bool} {s : State A V}
    (h : Reachable QS cp s) : Inv QS cp s := by
  induction h with
  | refl => exact inv_init QS cp
  | tail _ hst ih => exact ih.step hst

/-- Messages are never removed. -/
lemma Step.msgs_subset {QS : QuorumSystem A} {cp : Bool} {s s' : State A V}
    (h : Step QS cp s s') : s.msgs ⊆ s'.msgs := by
  obtain ⟨act, -, rfl⟩ := h
  cases act <;> exact Set.subset_insert _ _

lemma msgs_subset_of_reflTransGen {QS : QuorumSystem A} {cp : Bool} {s s' : State A V}
    (h : Relation.ReflTransGen (Step QS cp) s s') : s.msgs ⊆ s'.msgs := by
  induction h with
  | refl => exact le_rfl
  | tail _ hst ih => exact ih.trans hst.msgs_subset

end Podc.ConsecutiveBallotsPaxos
