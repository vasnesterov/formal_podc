import Papers.PODC2012.CollaborativeSearchPlane.Theorem41
import Papers.PODC2012.CollaborativeSearchPlane.Theorem42
import Papers.PODC2012.CollaborativeSearchPlane.Footnote
import Papers.PODC2012.CollaborativeSearchPlane.NonVacuity
import Papers.PODC2012.CollaborativeSearchPlane.Theorem31
import Papers.PODC2012.CollaborativeSearchPlane.Theorem33
import Papers.PODC2012.CollaborativeSearchPlane.Theorem51

/-!
# Collaborative search on the plane without communication (Feinerman, Korman, Lotker, Sereni,
PODC 2012)

Main results (see `README.md`):

* `theorem_3_1`, `corollary_3_2` — `O(D + D²/k)` with (approximate) knowledge of `k`;
* `theorem_3_3` — a uniform `O(log^{1+ε} k)`-competitive algorithm;
* `theorem_4_1` (via `summable_inv_of_isCompetitive`) — no uniform algorithm is
  `O(log k)`-competitive;
* `theorem_4_2` — `Ω(ε(k) log k)` with `k^ε`-approximate knowledge of `k`;
* `theorem_5_1` — the harmonic algorithm;
* `footnote_2` — the trivial lower bound `Ω(D + D²/k)`.
-/
