import Papers.PODC2015.SetAgreementSpace.Safety
import Papers.PODC2015.SetAgreementSpace.Liveness
import Papers.PODC2015.SetAgreementSpace.Repeated

/-!
# Main results (Delporte-Gallet, Fauconnier, Kuznetsov, Ruppert, PODC 2015)

Summary of what is proved about the snapshot-based algorithms of Section 4.

* `theorem7_figure3_false`: the algorithm of Figure 3 is safe but **not** `m`-obstruction-free
  (not even obstruction-free), for all `1 ≤ m ≤ k < n`.
* `theorem7_corrected`: Figure 3 with one extra guard (adopt a value only if it differs from
  `pref`) solves one-shot `m`-obstruction-free `k`-set agreement among `n` processes with an
  `(n + 2m − k)`-component snapshot object.
* `theorem8_figure4_false`: the repeated algorithm of Figure 4 is not `m`-obstruction-free.

The lower bound (Theorem 2) is in `LowerBound.lean` / `LowerBoundLemma1.lean`.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

variable {V : Type} [DecidableEq V] [Inhabited V]

/-- **Theorem 7 (algorithm of Figure 3), as stated, fails**: Figure 3 satisfies validity and
`k`-agreement on one-shot executions, but it is not `m`-obstruction-free. -/
theorem theorem7_figure3_false {n m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k < n)
    [NeZero (n + 2 * m - k)] :
    (fig3 (V := V) false n m (n + 2 * m - k)).Solves (kSetAgreement (Fin n) V k) ∧
      ¬ (fig3 (V := V) false n m (n + 2 * m - k)).MObstructionFreeOn m OneShot ∧
      ¬ (fig3 (V := V) false n m (n + 2 * m - k)).ObstructionFreeOn OneShot :=
  ⟨fig3_solves false hmk, fig3_not_mObstructionFree hm hmk hkn hm,
    fig3_not_obstructionFree hm hmk hkn⟩

/-- **Theorem 7, corrected (snapshot version)**: for `m ≤ k`, the corrected algorithm of
Figure 3 solves one-shot `k`-set agreement among `n` processes using a snapshot object with
`n + 2m − k` components and is `m`-obstruction-free (on one-shot executions). -/
theorem theorem7_corrected {n m k : ℕ} (hmk : m ≤ k) [NeZero (n + 2 * m - k)] :
    (fig3 (V := V) true n m (n + 2 * m - k)).Solves (kSetAgreement (Fin n) V k) ∧
      (fig3 (V := V) true n m (n + 2 * m - k)).MObstructionFreeOn m OneShot :=
  ⟨fig3_solves true hmk, fig3Fixed_mObstructionFree⟩

/-- **Theorem 8 (algorithm of Figure 4), as stated, fails**: Figure 4 is not `m`-obstruction-free,
already in executions where each process proposes once. -/
theorem theorem8_figure4_false {n m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k < n)
    [NeZero (n + 2 * m - k)] :
    ¬ (fig4 (V := V) false n m (n + 2 * m - k)).MObstructionFreeOn m (fun _ => True) :=
  fig4_not_mObstructionFree hm hmk hkn hm

end Podc.SetAgreementSpace
