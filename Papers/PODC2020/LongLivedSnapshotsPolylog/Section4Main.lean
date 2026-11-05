import Papers.PODC2020.LongLivedSnapshotsPolylog.Section4
import Papers.PODC2012.LimitedUseSnapshots.SnapshotMain
import Papers.PODC2012.LimitedUseSnapshots.SnapshotCost

/-!
# Theorem 4.4: the unlimited-use snapshot (Algorithm 2)

Algorithm 2 of the paper is Algorithm 3 of Aspnes–Attiya–Censor-Hillel–Ellen [AACE] with every
bounded max array replaced by Algorithm 1 and every bounded max register by the unbounded max
register of Baig et al. With these objects taken as atomic (which is how the paper uses them, and
what Theorem 3.7 and [12] provide), Algorithm 2 is `Snapshot.alg3 T v₀` of
`Papers/PODC2012/LimitedUseSnapshots`, with unbounded components.

The proof of Theorem 4.4 in the paper only says that the proof of Section 4.1 of [AACE] "holds
also" here. That proof uses wrong linearization points (see
`Snapshot.Counterexample.paper_linearization_points_fail`); the statement is nevertheless true,
with the repaired linearization points of `Snapshot.theorem_4_2`, which needs no bound on the
number of `Update`s (the arrays are unbounded families). So Algorithm 2 is an **unlimited-use**
linearizable snapshot (`theorem_4_4_linearizable`).

Wait-freedom and the per-operation costs: an `Update` performs `depth · (MaxUpdate + MaxScan + 3)
+ WriteMax + 1` weighted accesses and a `Scan` `ReadMax + 1` (`theorem_4_4_update_cost`,
`theorem_4_4_scan_cost`, from Lemma 4.3 of [AACE]). Lemma 4.3 of the paper sums these per-object
costs with the *amortized* costs `O(log² n)` of Algorithm 1 (Lemma 3.6) and `O(log n)` of the
max register of [12]; since the total cost of the operations on each object is at most its
amortized cost times the number of its operations, the total is `O((|S| + |U|) log³ n)`. The
amortized costs of the black boxes are not modelled.
-/

namespace Podc.LongLivedSnapshotsPolylog.Section4

open Cslib.SharedMemory Podc.LimitedUseSnapshots
open Podc.LimitedUseSnapshots.Snapshot (BTree alg3 swSnap tauCost opCost Costs balanced)

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}

/-- **Theorem 4.4 (linearizability)** of [BHMT20]: Algorithm 2 (over atomic unbounded max arrays
and an atomic unbounded max register) is a linearizable implementation of a single-writer
snapshot, for every tree whose leaves are the processes; there is no bound on the number of
`Update`s (unlimited use). -/
theorem theorem_4_4_linearizable (hT : T.WF) : (alg3 T v₀).Linearizable :=
  Snapshot.theorem_4_2 hT

/-- **Theorem 4.4 (wait-freedom, `Update`)**: after process `p` invokes `Update(v)`, its
accesses cost at most `⌈log₂ n⌉ · (MaxUpdate + MaxScan + 3) + WriteMax + 1` (balanced tree on the
`n = l.length` processes), whatever the other processes do. -/
theorem theorem_4_4_update_cost (K : Costs) (d : P) (l : List P)
    {α γ : List (Label P (swSnap P V v₀))} {p : P} {v : V}
    {C₁ C' : Config (swSnap P V v₀) (Snapshot.objSpec P V v₀) P (Snapshot.Loc P V)}
    (h₁ : (alg3 (balanced d l) v₀).run (α ++ [.inv p (.update p v)]) = some C₁)
    (h : (alg3 (balanced d l) v₀).runFrom C₁ γ = some C') (hret : ∀ r, .ret p r ∉ γ) :
    tauCost (alg3 (balanced d l) v₀) (opCost v₀ K) p C₁ γ ≤
      Nat.clog 2 l.length * (K.upd + K.scan + 3) + K.wmax + 1 :=
  Snapshot.lemma_4_3_update_balanced v₀ K d l h₁ h hret

/-- **Theorem 4.4 (wait-freedom, `Scan`)**: a `Scan` costs at most `ReadMax + 1`. -/
theorem theorem_4_4_scan_cost (K : Costs) {α γ : List (Label P (swSnap P V v₀))} {p : P}
    {C₁ C' : Config (swSnap P V v₀) (Snapshot.objSpec P V v₀) P (Snapshot.Loc P V)}
    (h₁ : (alg3 T v₀).run (α ++ [.inv p .scan]) = some C₁)
    (h : (alg3 T v₀).runFrom C₁ γ = some C') (hret : ∀ r, .ret p r ∉ γ) :
    tauCost (alg3 T v₀) (opCost v₀ K) p C₁ γ ≤ K.rmax + 1 :=
  Snapshot.lemma_4_3_scan T v₀ K h₁ h hret

end Podc.LongLivedSnapshotsPolylog.Section4
