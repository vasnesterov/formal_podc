import Papers.PODC2012.OptimalAPSP.Pebble
import Papers.PODC2012.OptimalAPSP.Algorithm1
import Papers.PODC2012.OptimalAPSP.Algorithm2
import Papers.PODC2012.OptimalAPSP.DiamApproxLB
import Papers.PODC2012.OptimalAPSP.Diam23LB

/-!
# Holzer–Wattenhofer, *Optimal Distributed All Pairs Shortest Paths and Applications* (PODC 2012)

Index of the formalization (see `README.md`):

* `Pebble.lean`: the pebble traversal of `T₁` (Remark 3) and **Lemma 1** (`PState.lemma1`).
* `Algorithm1.lean`: Algorithm 1 as a CONGEST algorithm with `O(log n)`-bit messages;
  **Theorem 1** (`theorem1`: APSP after `5n` rounds) and **Lemmas 2–6** (`lemmas2to6`).
* `Algorithm2.lean`: Algorithm 2 (S-SP) and the refutation of **Theorem 5** (`Alg2.theorem5_false`).
* `DiamApproxLB.lean`: **Lemmas 8, 9**, Claim 2, **Theorem 4** (`theorem4`, `theorem4_bound`) and
  the `(+,1)` parts of Lemma 10.
* `Diam23LB.lean`: **Lemma 15, Theorems 8, 9** (`theorem8`, `theorem8_linear`), the exact parts of
  Lemmas 10, 11, Lemma 16 and Theorem 11.
-/
