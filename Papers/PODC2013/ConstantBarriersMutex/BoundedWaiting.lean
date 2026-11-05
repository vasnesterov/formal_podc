import Papers.PODC2013.ConstantBarriersMutex.BoundedWaitingCore
import Papers.PODC2013.ConstantBarriersMutex.Invariant

/-!
# Bounded waiting (Lemmas 8 and 9 of the paper)

Hagit Attiya, Danny Hendler, Smadar Levy. *An O(1)-Barriers Optimal RMRs Mutual Exclusion
Algorithm.* PODC 2013.

A mutual exclusion algorithm provides *k-bounded waiting* if, in every execution, no process
enters the critical section more than `k` times while another process is waiting in its entry
section. The *waiting section* starts when the CAS of statement 23 has been performed
(Definition 1); in the model it consists of the program counters `PC.Waiting` (statements 24–27).

* `lemma8` — while `p` is in its waiting section during the time interval `[t₁, t₂]`, any other
  process `q` enters the critical section at most `log n + 2 = h + 2` times at steps in
  `[t₁, t₂)` (any run, no fairness needed).
* `lemma8_log_n_add_three` — the paper's statement, `(log n + 3)`-bounded waiting.
* `lemma9` — the key lemma, in the form used by the proof (see `BW.lemma9`).

The proof follows the paper. Its ingredients are in `BoundedWaitingBasic.lean` (steps, store
buffers, tree arithmetic, the doorway writes of `p`), `BoundedWaitingQueue.lean` (the promotion
order is FIFO; exit sections promote the applying processes they read) and
`BoundedWaitingCore.lean` (Lemma 9 by induction on the level, and the counting).
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- **Lemma 8 of [Attiya–Hendler–Levy, PODC 2013]**, with the sharper constant `log n + 2`.
While process `p` is in its waiting section (statements 24–27) at all times in `[t₁, t₂]`, every
other process `q` enters the critical section at most `h + 2 = log n + 2` times at steps
`t ∈ [t₁, t₂)` (`q`'s program counter is not `cs` at `t` and is `cs` at `t + 1`). -/
theorem lemma8 (r : Run h) {p q : Proc h} (hpq : p ≠ q) {t₁ t₂ : ℕ}
    (hW : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Waiting) :
    ((Finset.Ico t₁ t₂).filter
      (fun t => (r.s t).pc q ≠ .cs ∧ (r.s (t + 1)).pc q = .cs)).card ≤ h + 2 := by
  classical
  have := BW.bounded_waiting_core r r.inv hpq hW
  unfold BW.cnt BW.Enters at this
  convert this

/-- **Lemma 8 of [Attiya–Hendler–Levy, PODC 2013]**: the algorithm provides
`(log n + 3)`-bounded waiting (`n = 2 ^ h`, `log n = h`). -/
theorem lemma8_log_n_add_three (r : Run h) {p q : Proc h} (hpq : p ≠ q) {t₁ t₂ : ℕ}
    (hW : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Waiting) :
    ((Finset.Ico t₁ t₂).filter
      (fun t => (r.s t).pc q ≠ .cs ∧ (r.s (t + 1)).pc q = .cs)).card ≤ h + 3 :=
  (lemma8 r hpq hW).trans (Nat.le_succ _)

/-- **Lemma 9 of [Attiya–Hendler–Levy, PODC 2013]** (TSO version). Let `p` be in its waiting
section during `[t₁, t₂]` and let `q ≠ p` enter the critical section at step `e < t₂` after
having entered it at least `l + 1` times during `[t₁, e)` (so `e` is at least its `(l + 2)`-th
entry). Then `p` has been promoted (it is in the promotion order `BW.Q`) at some time in `[t₁, e]`,
or some process reads `n^l_p = anc p l` at statement 34 of its exit section at a step `τ < e`
that follows a time `a` at which `n^l_p` holds `p`, written by the doorway of the current passage
of `p` (`BW.Done` holds on `[a, t₂]`; in the paper's notation `a ≥ t_l(P)`). -/
theorem lemma9 (r : Run h) {p q : Proc h} (hpq : p ≠ q) {t₁ t₂ : ℕ}
    (hW : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Waiting) {l : ℕ} (hl : l ≤ h) {e : ℕ}
    (he : BW.Enters r q e) (het : e < t₂) (hc : l + 1 ≤ BW.cnt r q t₁ e) :
    (∃ π, t₁ ≤ π ∧ π ≤ e ∧ p ∈ BW.Q (r.s π)) ∨
    (∃ a τ, a ≤ τ ∧ τ < e ∧ (r.s a).mem.node (anc p l) = some p ∧
      (∀ u, a ≤ u → u ≤ t₂ → BW.Done (r.s u) p l) ∧ BW.ReadsAt r τ (anc p l)) :=
  BW.lemma9 r r.inv hpq hW l hl e he het hc

end Podc.ConstantBarriersMutex
