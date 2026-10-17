import Papers.PODC2021.TimeOptimalSSLE.Model
import Papers.PODC2021.TimeOptimalSSLE.LowerBound
import Papers.PODC2021.TimeOptimalSSLE.SilentSSR
import Papers.PODC2021.TimeOptimalSSLE.RandomScheduler
import Papers.PODC2021.TimeOptimalSSLE.Observations
import Papers.PODC2021.TimeOptimalSSLE.Obs26Prob
import Papers.PODC2021.TimeOptimalSSLE.OptimalSilent
import Papers.PODC2021.TimeOptimalSSLE.OptimalSilentCorrect

/-!
# Time-Optimal Self-Stabilizing Leader Election in Population Protocols (PODC 2021)

Burman, Chen, Chen, Doty, Nowak, Severson, Xu. See `README.md` for the verdict and the map from
the paper's results to Lean declarations, and `differencies.md` for all differences.

* `Model.lean`: protocols with randomized transitions (support), SSLE / SSR, silence,
  sub-population embedding.
* `RandomScheduler.lean`: reachability of stably correct configurations ⇔ stabilization with
  probability 1 under the uniform random scheduler.
* `LowerBound.lean`: Theorem 2.1 (`≥ n` states; strong nonuniformity).
* `SilentSSR.lean`: Lemmas 2.2, 2.3 and the correctness part of Theorem 2.4.
* `Observations.lean`, `Obs26Prob.lean`: Observations 2.5 and 2.6.
* `OptimalSilent.lean`: Protocols 2–4 (`Optimal-Silent-SSR`) and the off-by-one counterexample.
* `OptimalSilentCorrect.lean`: correctness of `Optimal-Silent-SSR` with the fixed guard.
-/
