import Papers.PODC2019.ConcurrentSketches.ParSketchMain
import Papers.PODC2019.ConcurrentSketches.OptParSketchMain
import Papers.PODC2019.ConcurrentSketches.ThetaSketch

/-!
# Non-vacuity: the concurrent Θ sketch

For the paper's running example, the KMV Θ sketch (`thetaComposable`, Algorithm 1 with the
composable API), the paper's literal initial hint `1` is the hint of the empty sketch
(`Θ = 1`), so Lemma 1 and Theorem 1 apply to `ParSketch` and `OptParSketch` exactly as written
in the paper.
-/

namespace Podc.ConcurrentSketches

variable {E : Type} {Q : Type} [DecidableEq Q] {N : ℕ} [NeZero N]

/-- The hint `1` of the Θ sketch (hints are real numbers). -/
def thetaOne (k : ℕ) (hk : 0 < k) (hash : E → ℝ) (hle : ∀ a, hash a ≤ 1) :
    (thetaComposable k hk hash hle).Hint := (1 : ℝ)

/-- For the Θ sketch the paper's initial hint `1` is the hint of the empty sketch. -/
lemma theta_calcHint_init (k : ℕ) (hk : 0 < k) (hash : E → ℝ) (hle : ∀ a, hash a ≤ 1) :
    (thetaComposable k hk hash hle).calcHint (thetaComposable k hk hash hle).init =
      thetaOne k hk hash hle := by
  show theta {1} = 1
  exact theta_eq_one (by simp) (by simp)

lemma theta_hint_one_safe (k : ℕ) (hk : 0 < k) (hash : E → ℝ) (hle : ∀ a, hash a ≤ 1) :
    (thetaComposable k hk hash hle).Safe (thetaOne k hk hash hle) [] := by
  have := safe_init_hint (thetaComposable k hk hash hle)
  rwa [theta_calcHint_init] at this

/-- **Lemma 1 for the concurrent Θ sketch**, with the paper's initial hint `1`. -/
theorem lemma1_theta (k : ℕ) (hk : 0 < k) (hash : E → ℝ) (hle : ∀ a, hash a ≤ 1) {b : ℕ}
    (hb : 0 < b) :
    (parSketch (thetaComposable k hk hash hle) N Q b
      (thetaOne k hk hash hle)).HStronglyLinearizable
        (SeqSketchRPast (N * b) (thetaComposable k hk hash hle)) :=
  lemma1_pastOnly hb (theta_hint_one_safe k hk hash hle)

/-- **Theorem 1 for the concurrent Θ sketch**, with the paper's initial hint `1`. -/
theorem theorem1_theta (k : ℕ) (hk : 0 < k) (hash : E → ℝ) (hle : ∀ a, hash a ≤ 1) {b : ℕ}
    (hb : 0 < b) :
    (optParSketch (thetaComposable k hk hash hle) N Q b
      (thetaOne k hk hash hle)).HStronglyLinearizable
        (SeqSketchRPast (2 * N * b) (thetaComposable k hk hash hle)) :=
  theorem1_pastOnly hb (theta_hint_one_safe k hk hash hle)

end Podc.ConcurrentSketches
