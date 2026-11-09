import Papers.PODC2015.StabilizingByzStorage.Cycle

/-!
# Lemma 9 (as stated) is false

Lemma 9 claims that when a `prac_at_write` invoked after `τ_no_tr` returns, at least `4t + 1`
*correct* servers store the same helping pair. If the test of line 03 fails because `4t + 1` acks
carry the same pair, up to `t` of them come from Byzantine servers, so only `3t + 1` correct servers
are guaranteed. The proof's Case 2 ("the writer found `4t + 1` same values") overlooks this.
`3t + 1` correct copies are what the later uses (Lemma 10, Case 2.2) need, so this is a slip.
-/

namespace Podc.StabilizingByzStorage.Atomic.Cex

open Podc.StabilizingByzStorage

/-- Initial configuration (arbitrary, as after transient failures): servers `0–3` have helping
pair `(0, 0)`, the other servers `⊥`. -/
def st9 : State N M ℕ :=
  ⟨fun s => if s.val < 4 then { srv0 0 with help := some (d 0) } else srv0 0,
    ⟨sq 0, .idle⟩, ⟨sq 0, 0, .idle⟩⟩

/-- One write: the Byzantine server acks `(0, 0)`, so `4t + 1 = 5` acks carry `(0, 0)` and the writer
does not refresh the helping values. -/
def acts9 : List (Act N M ℕ) :=
  [.invW 1] ++ dWs allS ++ [.endW, .ack {0, 1, 2, 3, 4, 5, 6, 8} (ba (some (d 0)))]

/-- When the write returns, fewer than `4t + 1` correct servers share a helping pair. -/
def lemma9Bad : Bool :=
  match run T Byz st9 acts9 with
  | some tr =>
    (tr.getLast?.map Prod.fst == some .retWrite) &&
    match tr.getLast? with
    | some (_, σ) => decide (∀ s0 : Fin N,
        (Finset.univ.filter fun s => s ∉ Byz ∧ (σ.srv s).help = (σ.srv s0).help).card < 4 * T + 1
        ∨ (σ.srv s0).help = none)
    | none => false
  | none => false

theorem lemma9Bad_eq : lemma9Bad = true := by decide

/-- **Lemma 9 is false as stated** (`n = 9`, `t = 1`): there is an execution in which a write
invoked at time `0` (`τ_no_tr = 0`) returns while no helping pair is stored by `4t + 1 = 5` correct
servers. -/
theorem lemma9_false : ∃ tr : List (Label ℕ × State N M ℕ),
    run T Byz st9 acts9 = some tr ∧ (∃ σ, tr.getLast? = some (.retWrite, σ) ∧
      ∀ x : D, (Finset.univ.filter fun s => s ∉ Byz ∧ (σ.srv s).help = some x).card < 4 * T + 1) := by
  have h := lemma9Bad_eq
  unfold lemma9Bad at h
  split at h
  · rename_i tr htr
    refine ⟨tr, htr, ?_⟩
    cases hl : tr.getLast? with
    | none => simp [hl] at h
    | some p =>
      obtain ⟨ℓ, σ⟩ := p
      simp only [hl, Option.map_some, beq_iff_eq, Option.some.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨rfl, h2⟩ := h
      refine ⟨σ, rfl, fun x => ?_⟩
      by_cases he : (Finset.univ.filter fun s => s ∉ Byz ∧ (σ.srv s).help = some x).Nonempty
      · obtain ⟨s0, hs0⟩ := he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs0
        rcases h2 s0 with h2 | h2
        · rwa [hs0.2] at h2
        · rw [hs0.2] at h2; simp at h2
      · rw [Finset.not_nonempty_iff_eq_empty] at he; rw [he]; decide
  · simp at h

end Podc.StabilizingByzStorage.Atomic.Cex
