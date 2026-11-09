import Papers.PODC2015.StabilizingByzStorage.RegularSafety
import Papers.PODC2015.StabilizingByzStorage.RegularLiveness

/-!
# Theorem 1: Fig. 2 is a stabilizing SWSR regular register

Combines Lemma 1 (`lemma1_write_terminates`), Lemma 2 (`lemma2_read_terminates`, for `6t < n`,
weaker than the paper's `8t < n`) and Lemma 3 (`lemma3_regular_exec`, `τ_stab` = the return of the
first write, any `n`, `t`).
-/

namespace Podc.StabilizingByzStorage.Regular

variable {n : ℕ} {V : Type} [DecidableEq V] {t : ℕ} {B : Finset (Fin n)}

/-- **Theorem 1** of [Bonomi, Dolev, Potop-Butucaru, Raynal, PODC 2015] (with `6t < n` instead of
`8t < n`). In every fair infinite execution of Fig. 2 starting in an arbitrary configuration of the
servers and links (clients between operations), with at most `t` Byzantine servers and at least one
write invoked: every write and every read terminates (liveness), and every read invoked after the
return of some write returns a regular value (eventual regularity, `τ_stab = τ_1w`). -/
theorem theorem1 {e : ℕ → State n V} {lab : ℕ → Label V} (hB : B.card ≤ t) (hn : 6 * t < n)
    (h0 : Init (e 0)) (hE : Exec t B e lab) (hF : Fair t B e)
    (hw : ∃ i v, lab i = .invWrite v) :
    (∀ a v, lab a = .invWrite v → ∃ j > a, lab j = .retWrite) ∧
    (∀ a, lab a = .invRead → ∃ j > a, ∃ v, lab j = .retRead v) ∧
    (∀ i j v, ReadOp lab i j v → (∃ k < i, lab k = .retWrite) → RegularRead lab i j v) :=
  ⟨fun _ _ ha => lemma1_write_terminates hE hF hB ha,
   fun _ ha => lemma2_read_terminates hE hF hB hn hw ha,
   fun _ j _ hr hk => lemma3_regular_exec (t := t) (B := B) (N := j + 1) h0 (fun k _ => hE k) (by omega) hr hk⟩

end Podc.StabilizingByzStorage.Regular
