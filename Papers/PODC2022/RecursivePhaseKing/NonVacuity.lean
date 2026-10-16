import Papers.PODC2022.RecursivePhaseKing.EarlyStopping
import Papers.PODC2022.RecursivePhaseKing.Doubling

/-!
# Non-vacuity checks

* The hypotheses of Theorem 2.9 are satisfiable: for `P = Fin n` with `t = ⌈n/3⌉ - 1`
  (`3t < n`), the king schedule `king j = j mod n` of Algorithm 1 is injective on the first `t + 1`
  iterations (`kingFin_injOn`), and every adversary yields an execution (`syncRun`: the
  synchronous execution of `alg1` in which faulty nodes send arbitrary messages `byz`).
* On a concrete fault-free instance (`n = 4`, inputs `0,1,1,1`), all nodes decide `1` within 6
  rounds (`example_decides`), computed by `decide`.
* `badTrace` (in `Doubling.lean`) inhabits `Trace`, so the spec-level theorems are not vacuous.
-/

namespace RecursivePhaseKing

open Finset Cslib.Byzantine.PartialSync

/-- The paper's resilience `t = ⌈n/3⌉ - 1` satisfies `3t < n`. -/
theorem three_mul_paper_t_lt {n : ℕ} (hn : 0 < n) : 3 * ((n + 2) / 3 - 1) < n := by omega

/-- The king schedule of Algorithm 1 on `Fin n` (iteration `j` has king `j`, 0-based). -/
def kingFin (n : ℕ) [NeZero n] (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem kingFin_injOn {n t : ℕ} [NeZero n] (h3 : 3 * t < n) :
    ∀ i ≤ t, ∀ j ≤ t, kingFin n i = kingFin n j → i = j := by
  intro i hi j hj h
  have := congrArg Fin.val h
  simp only [kingFin] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

section SyncRun

variable {P : Type*} [Fintype P] [DecidableEq P] (t : ℕ) (king : ℕ → P)
  (tb : ℕ → P → St P → (P → Option Bool) → Bool)

/-- States of the synchronous execution of `alg1` with faulty set `F`, inputs `inp`, and
messages `byz r p q` from faulty `q` to `p` in round `r`. -/
def syncSt (F : Finset P) (inp : P → Bool) (byz : ℕ → P → P → Option Bool) : ℕ → P → St P
  | 0 => fun p => (alg1 t king tb).init p (inp p)
  | r + 1 => fun p => (alg1 t king tb).trans r p (syncSt F inp byz r p)
      (fun q => if q ∈ F then byz r p q else (alg1 t king tb).send r q (syncSt F inp byz r q) p)

/-- Every adversary (faulty set, inputs, Byzantine messages) yields a synchronous execution of
Algorithm 1: the hypotheses of Theorem 2.9 are satisfiable. -/
def syncRun (F : Finset P) (inp : P → Bool) (byz : ℕ → P → P → Option Bool) :
    RoundRun (alg1 t king tb) F inp where
  s := syncSt t king tb F inp byz
  rcv r p q := if q ∈ F then byz r p q else (alg1 t king tb).send r q (syncSt t king tb F inp byz r q) p
  s_zero _ := rfl
  s_succ _ _ := rfl
  honest r p q m hq h := by simpa [hq] using h

theorem syncRun_syncFrom (F : Finset P) (inp : P → Bool) (byz : ℕ → P → P → Option Bool) :
    (syncRun t king tb F inp byz).SyncFrom 0 := by
  intro r _ p q _ hq
  simp [syncRun, hq]

end SyncRun

/-- A fault-free run on 4 nodes with inputs `0, 1, 1, 1`: every node has decided `1` after six
rounds (computed). -/
theorem example_decides :
    ∀ p : Fin 4, ((syncRun 1 (kingFin 4) (fun _ _ _ _ => true) ∅
      (fun p => decide (p ≠ 0)) (fun _ _ _ => none)).s 6 p).out = some true := by
  decide

end RecursivePhaseKing
