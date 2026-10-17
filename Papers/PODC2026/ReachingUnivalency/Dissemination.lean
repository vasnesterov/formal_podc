import Podc.PartialSync.Omission

/-!
# Reaching Univalency — Appendix A: the dissemination lower bound (Theorem 7)

Theorem 7 of [Lewis-Pye, *Reaching Univalency with Subquadratic Communication*, PODC 2026]:
in the synchronous model with omission faults, any deterministic protocol in which every correct
processor receives at least one message in every execution has message complexity `Ω(n + f²)`.

We use CSLib's synchronous omission executions `OmExec` (`Cslib.Byzantine.PartialSync`):
an execution is given by the inputs and by the set of delivered message batches; a set `F` of
omission-faulty processes is admissible (`E.Admits A F`) if every omitted non-empty batch has an
endpoint in `F`. Message complexity counts the messages that processes outside `F` send to other
processes (`E.msgsUpTo A F N`, messages sent at times `< N`). The protocol is an arbitrary
deterministic `Algorithm` (arbitrary state space): signatures play no role for omission faults,
so the result holds in the authenticated setting as well.

* `receives_lower_bound_sq` : some admissible execution has `≥ ⌈f/2⌉²` messages (the paper's
  `(f/2)²`).
* `receives_lower_bound_n` : the fault-free execution has `≥ n` messages.
* `theorem7` : both bounds.
-/

namespace ReachingUnivalency

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO : Type*} [Fintype P] [DecidableEq P]

/-- In `E`, process `p` receives at least one message from some *other* process. -/
def ReceivesMsg (A : Algorithm P M S VI VO) (E : OmExec P VI) (p : P) : Prop :=
  ∃ τ q, q ≠ p ∧ E.inbox A τ p q ≠ []

/-- The protocol guarantees that every correct processor receives at least one message, in every
execution with at most `f` omission-faulty processors. -/
def AlwaysReceives (A : Algorithm P M S VI VO) (f : ℕ) : Prop :=
  ∀ (E : OmExec P VI) (F : Finset P), E.Admits A F → F.card ≤ f → ∀ p ∉ F, ReceivesMsg A E p

/-- **Theorem 7, the `f²` part.** If every correct processor always receives a message, then some
execution with at most `f` omission faults has at least `⌈f/2⌉²` messages sent by correct
processors. (The paper assumes `f < n - 1`; `f ≤ n` suffices.) -/
theorem receives_lower_bound_sq (A : Algorithm P M S VI VO) {f : ℕ}
    (hf : f ≤ Fintype.card P) (hA : AlwaysReceives A f) (inp : P → VI) :
    ∃ (E : OmExec P VI) (F : Finset P) (N : ℕ), E.Admits A F ∧ F.card ≤ f ∧
      ((f + 1) / 2) * ((f + 1) / 2) ≤ E.msgsUpTo A F N := by
  set h := (f + 1) / 2 with hh
  obtain ⟨P₁, -, hP₁⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := h)
    (by rw [card_univ]; omega)
  -- the execution `E₁` of the proof: the processes of `P₁` receive no message from other
  -- processes ("they do not send or receive messages to or from each other, and ignore messages
  -- from processors in `P₂`")
  set E := OmExec.solo inp P₁
  have hE : E.Admits A P₁ := OmExec.solo_admits
  by_cases hall : ∀ p ∈ P₁, h ≤ (E.dropSenders A P₁ p).card
  · -- every isolated processor is sent messages by `≥ ⌈f/2⌉` correct processors
    obtain ⟨N, hN⟩ := OmExec.sum_card_dropSenders_le (E := E) (A := A) (subset_refl P₁)
    refine ⟨E, P₁, N, hE, by omega, ?_⟩
    calc h * h = ∑ _p ∈ P₁, h := by rw [sum_const, hP₁, smul_eq_mul]
      _ ≤ ∑ p ∈ P₁, (E.dropSenders A P₁ p).card := sum_le_sum hall
      _ ≤ _ := hN
  · -- some isolated `p` is sent messages by `< ⌈f/2⌉` processors: blame them instead of `p`
    exfalso
    push Not at hall
    obtain ⟨p, hp, hlt⟩ := hall
    have hsw : E.Admits A (P₁.erase p ∪ E.dropSenders A P₁ p) := by
      refine hE.swap (fun τ r hok _ => ?_)
      simp only [E, OmExec.solo_ok, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hok
      exact hok.1
    have hcard : (P₁.erase p ∪ E.dropSenders A P₁ p).card ≤ f := by
      have h1 := card_union_le (P₁.erase p) (E.dropSenders A P₁ p)
      have h2 := card_erase_of_mem hp
      omega
    have hpF : p ∉ P₁.erase p ∪ E.dropSenders A P₁ p := by
      simp only [mem_union, mem_erase, ne_eq, not_true_eq_false, false_and, false_or]
      exact OmExec.not_mem_dropSenders hp
    obtain ⟨τ, q, hqp, hne⟩ := hA E _ hsw hcard p hpF
    apply hne
    exact OmExec.solo_inbox_of_mem hp hqp τ

/-- **Theorem 7, the `n` part.** In the fault-free execution correct processors send at least `n`
messages. -/
theorem receives_lower_bound_n (A : Algorithm P M S VI VO) {f : ℕ} (hA : AlwaysReceives A f)
    (inp : P → VI) :
    ∃ (E : OmExec P VI) (N : ℕ), E.Admits A ∅ ∧ Fintype.card P ≤ E.msgsUpTo A ∅ N := by
  classical
  let E : OmExec P VI := ⟨inp, fun _ _ _ => true⟩
  have hE : E.Admits A ∅ := fun τ q p h _ => by simp [E] at h
  have hr : ∀ p, ReceivesMsg A E p := fun p => hA E ∅ hE (by simp) p (by simp)
  choose τ q hq hne using hr
  let N := (univ : Finset P).sup τ + 1
  refine ⟨E, N, hE, ?_⟩
  have key : ∀ p, 1 ≤ ∑ t ∈ range N, (A.send (q p) (E.st A t (q p)) p).length := by
    intro p
    have hlt : τ p < N := Nat.lt_succ_of_le (le_sup (f := τ) (mem_univ p))
    have h1 : 1 ≤ (A.send (q p) (E.st A (τ p) (q p)) p).length := by
      have := hne p
      simp only [OmExec.inbox, E, ite_true] at this
      exact List.length_pos_iff.mpr this
    exact h1.trans (single_le_sum (f := fun t => (A.send (q p) (E.st A t (q p)) p).length)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr hlt))
  calc Fintype.card P = ∑ _p : P, 1 := by simp
    _ ≤ ∑ p : P, ∑ t ∈ range N, (A.send (q p) (E.st A t (q p)) p).length :=
        sum_le_sum fun p _ => key p
    _ ≤ ∑ p : P, ∑ t ∈ range N, ∑ q' ∈ univ.filter (· ≠ p),
          (A.send q' (E.st A t q') p).length := by
        refine sum_le_sum fun p _ => sum_le_sum fun t _ => ?_
        exact single_le_sum (f := fun q' => (A.send q' (E.st A t q') p).length)
          (fun _ _ => Nat.zero_le _) (by simp [hq p])
    _ = E.msgsUpTo A ∅ N := by
        unfold OmExec.msgsUpTo
        rw [sum_comm]
        refine sum_congr rfl fun t _ => ?_
        rw [sum_comm' (t' := univ.filter (· ∉ (∅ : Finset P)))
          (s' := fun q' => univ.filter (· ≠ q'))]
        intro p q'
        simp [ne_comm]

/-- **Theorem 7** (Appendix A). With omission faults, any deterministic protocol in which every
correct processor receives at least one message in every execution has message complexity
`Ω(n + f²)`: there are admissible executions with at least `n` and at least `⌈f/2⌉²` messages sent by
correct processors. -/
theorem theorem7 (A : Algorithm P M S VI VO) {f : ℕ} (hf : f ≤ Fintype.card P)
    (hA : AlwaysReceives A f) (inp : P → VI) :
    (∃ (E : OmExec P VI) (N : ℕ), E.Admits A ∅ ∧ Fintype.card P ≤ E.msgsUpTo A ∅ N) ∧
    ∃ (E : OmExec P VI) (F : Finset P) (N : ℕ), E.Admits A F ∧ F.card ≤ f ∧
      ((f + 1) / 2) * ((f + 1) / 2) ≤ E.msgsUpTo A F N :=
  ⟨receives_lower_bound_n A hA inp, receives_lower_bound_sq A hf hA inp⟩

/-- Non-vacuity of Theorem 7: "everybody sends one message to everybody at time `0`" guarantees that
every correct processor receives a message, as soon as `f < n - 1` (two correct processors exist).
For `f ≥ n - 1` no protocol has this property, which is why the paper assumes `f < n - 1`. -/
def helloAlg (P VI : Type*) [DecidableEq P] : Algorithm P Unit Bool VI Unit where
  init _ _ := false
  step _ _ _ := true
  send p s q := if s = false ∧ q ≠ p then [()] else []
  decide _ _ := none

theorem helloAlg_alwaysReceives {f : ℕ} (hf : f + 1 < Fintype.card P) :
    AlwaysReceives (helloAlg P VI) f := by
  classical
  intro E F hE hF p hp
  obtain ⟨q, hq⟩ : ∃ q, q ∉ insert p F := by
    by_contra h
    push Not at h
    have : (insert p F).card = Fintype.card P := by
      rw [← card_univ]; congr 1; ext x; simp [h x]
    have := card_insert_le p F
    omega
  simp only [mem_insert, not_or] at hq
  refine ⟨0, q, hq.1, ?_⟩
  have hsend : (helloAlg P VI).send q (E.st (helloAlg P VI) 0 q) p = [()] := by
    simp [helloAlg, OmExec.st, Ne.symm hq.1]
  rw [OmExec.inbox_eq_send_of_correct hE hq.2 hp, hsend]
  simp

end ReachingUnivalency
