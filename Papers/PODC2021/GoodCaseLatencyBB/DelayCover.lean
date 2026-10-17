import Papers.PODC2021.GoodCaseLatencyBB.Basic
import Cslib.Computability.Distributed.Byzantine.PartialSync.Cover

/-!
# Covering systems with uniform message delay

The covering systems with time-dependent neighbourhoods and delivery offset `e` used by the
dishonest-majority lower bounds are the shared `Cslib.Byzantine.PartialSync.DCover`
(`Cslib/Computability/Distributed/Byzantine/PartialSync/Cover.lean`: covering lemma `DCover.st_run`,
locality `DCover.st_eq_of_level`, unforgeability `DCover.run_authValid`). This file adds the
bridge to this paper's synchronous runs (`SyncValid`).
-/

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

namespace DCover

variable {P Q M S V : Type*} [DecidableEq P] (A : Algorithm P M S V V) (e : ℕ) (C : DCover P Q V)

/-- `a < b` from `σ + Δ * a < Δ * b`. -/
theorem lt_of_add_mul_lt {σ Δ a b : ℕ} (h : σ + Δ * a < Δ * b) : a < b :=
  Nat.lt_of_mul_lt_mul_left (by omega : Δ * a < Δ * b)

/-- The covering run is a synchronous run with effective delay `e + 1`. -/
theorem run_syncValid {f : ℕ} {F : Finset P} (hF : F.card ≤ f) (lift : P → Q) :
    SyncValid f (e + 1) (C.run A e F lift) where
  card_faulty := hF
  dl_ge _ _ _ _ _ := by simp [DCover.run]
  dl_lt _ _ _ _ _ := by simp [DCover.run]

end DCover

end GoodCaseLatencyBB
