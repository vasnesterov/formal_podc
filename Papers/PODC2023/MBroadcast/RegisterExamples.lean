import Papers.PODC2023.MBroadcast.RegisterSafety
import Cslib.Computability.Distributed.SharedMemory.Sequential

/-!
# Algorithm 3: example executions

* `alg3_weak_not_linearizable`: under the *literal* reading of mutual ordering
  (`WeakMutualOrdering`: "`p` mdelivers both messages, its own first"), Algorithm 3 is not
  linearizable. Process `p₀` writes `1` (both its messages are mdelivered only by itself) and
  then `p₁` reads `0` (its messages are mdelivered only by itself). The MBroadcast trace satisfies
  validity, no-duplication and the literal mutual ordering, and the execution is compatible with
  Global CS-termination if `p₀` crashes after its write. This is why we read "`p` mdelivers `m`
  before `m'`" as "when `p` mdelivers `m`, it has not mdelivered `m'`" (`DelivBefore`).
* `alg3_nonvacuous`: an execution satisfying the (strong) MBroadcast safety properties in which a
  write of `1` by `p₀` is followed by a read of `p₁` returning `1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Alg3

open Cslib.SharedMemory

/-- A configuration of two processes `false` (`p₀`) and `true` (`p₁`), nobody crashed. -/
def mk2 (l₀ l₁ : Loc Bool ℕ) (log : List (Ev Bool (Msg Bool ℕ))) : Cfg Bool ℕ :=
  ⟨fun b => if b then l₁ else l₀, log, ∅⟩

lemma reach_step {C C' D : Cfg Bool ℕ} {h : List (Label Bool (register ℕ 0))} {ℓ}
    (hr : Reach 0 C h) (hs : Step 0 C ℓ C') (hD : C' = D) : Reach 0 D (h ++ ℓ.toList) :=
  hD ▸ hr.step hs

@[simp] lemma mk2_loc_false (l₀ l₁ : Loc Bool ℕ) (log) : (mk2 l₀ l₁ log).loc false = l₀ := rfl
@[simp] lemma mk2_loc_true (l₀ l₁ : Loc Bool ℕ) (log) : (mk2 l₀ l₁ log).loc true = l₁ := rfl
@[simp] lemma mk2_log (l₀ l₁ : Loc Bool ℕ) (log) : (mk2 l₀ l₁ log).log = log := rfl
@[simp] lemma mk2_crashed (l₀ l₁ : Loc Bool ℕ) (log) : (mk2 l₀ l₁ log).crashed = ∅ := rfl

lemma mk2_upd_false (l₀ l₁ l : Loc Bool ℕ) (log es) :
    (mk2 l₀ l₁ log).upd false l es = mk2 l l₁ (log ++ es) := by
  simp only [Cfg.upd, mk2, Cfg.mk.injEq, and_true]
  funext b; cases b <;> simp

lemma mk2_upd_true (l₀ l₁ l : Loc Bool ℕ) (log es) :
    (mk2 l₀ l₁ log).upd true l es = mk2 l₀ l (log ++ es) := by
  simp only [Cfg.upd, mk2, Cfg.mk.injEq, and_true]
  funext b; cases b <;> simp

lemma initCfg_eq : (initCfg 0 : Cfg Bool ℕ) = mk2 ⟨0, ⊥, 0, .idle⟩ ⟨0, ⊥, 0, .idle⟩ [] := by
  simp only [initCfg, mk2, Cfg.mk.injEq, and_true]
  funext b; cases b <;> rfl

/-- The local states and traces of the two example executions. -/
abbrev L0 : Loc Bool ℕ := ⟨0, ⊥, 0, .idle⟩

/-- The trace of the write of `1` by `p₀`, all messages mdelivered only by `p₀`. -/
def wLog : List (Ev Bool (Msg Bool ℕ)) :=
  [.bc false (.synch 0), .dl false false (.synch 0),
    .bc false (.write 0 1 (ts 1 false)), .dl false false (.write 0 1 (ts 1 false))]

/-- After the write of `1` by `p₀`. -/
lemma reach_write : Reach (0 : ℕ) (mk2 ⟨1, ts 1 false, 1, .idle⟩ L0 wLog)
    [.inv false (.write 1), .ret false 1] := by
  have r0 : Reach (P := Bool) (0 : ℕ) (mk2 L0 L0 []) [] := initCfg_eq ▸ Reach.init
  have r1 := reach_step r0 (Step.invW _ false 1 (by simp) rfl)
    (D := mk2 ⟨0, ⊥, 0, .wSync 1⟩ L0 [.bc false (.synch 0)]) (by simp [mk2_upd_false])
  have r2 := reach_step r1 (Step.dlv _ false false (.synch 0) (by simp))
    (D := mk2 ⟨0, ⊥, 0, .wSync 1⟩ L0 [.bc false (.synch 0), .dl false false (.synch 0)])
    (by simp [mk2_upd_false, handle])
  have r3 := reach_step r2 (Step.line2 _ false 1 1 (by simp) rfl (by simp)
    (by simpa using bot_lt_ts 1 false))
    (D := mk2 ⟨0, ⊥, 0, .wFin 1 (ts 1 false)⟩ L0 [.bc false (.synch 0),
      .dl false false (.synch 0), .bc false (.write 0 1 (ts 1 false))])
    (by simp [mk2_upd_false])
  have r4 := reach_step r3 (Step.dlv _ false false (.write 0 1 (ts 1 false)) (by simp))
    (D := mk2 ⟨1, ts 1 false, 0, .wFin 1 (ts 1 false)⟩ L0 wLog)
    (by simp [mk2_upd_false, handle, bot_lt_ts, wLog])
  have r5 := reach_step r4 (Step.retW _ false 1 (ts 1 false) (by simp) rfl (by simp [wLog]))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ L0 wLog) (by simp [mk2_upd_false])
  simpa using r5

/-- The trace of the counterexample. -/
def weakLog : List (Ev Bool (Msg Bool ℕ)) :=
  wLog ++ [.bc true (.synch 0), .dl true true (.synch 0),
    .bc true (.write 0 0 ⊥), .dl true true (.write 0 0 ⊥)]

/-- The counterexample execution: after the write of `p₀`, `p₁` reads `0`; every message is
mdelivered only by its sender. -/
lemma reach_weak : Reach (0 : ℕ) (mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 1, .idle⟩ weakLog)
    [.inv false (.write 1), .ret false 1, .inv true .read, .ret true 0] := by
  have r5 := reach_write
  have r6 := reach_step r5 (Step.invR _ true (by simp) rfl)
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 0, .rSync⟩ (wLog ++ [.bc true (.synch 0)]))
    (by simp [mk2_upd_true])
  have r7 := reach_step r6 (Step.dlv _ true true (.synch 0) (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 0, .rSync⟩
      (wLog ++ [.bc true (.synch 0), .dl true true (.synch 0)]))
    (by simp [mk2_upd_true, handle])
  have r8 := reach_step r7 (Step.line5 _ true (by simp) rfl (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 0, .rFin 0 ⊥⟩
      (wLog ++ [.bc true (.synch 0), .dl true true (.synch 0), .bc true (.write 0 0 ⊥)]))
    (by simp [mk2_upd_true])
  have r9 := reach_step r8 (Step.dlv _ true true (.write 0 0 ⊥) (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 0, .rFin 0 ⊥⟩ weakLog)
    (by simp [mk2_upd_true, handle, weakLog])
  have r10 := reach_step r9 (Step.retR _ true 0 ⊥ (by simp) rfl (by simp [weakLog]))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 1, .idle⟩ weakLog) (by simp [mk2_upd_true])
  simpa using r10

/-- **Under the literal reading of mutual ordering, Theorem 2 is false.** A reachable
configuration of Algorithm 3 whose MBroadcast trace satisfies validity, no-duplication, unique
broadcasts and the literal mutual ordering (`WeakMutualOrdering`), but whose history — `p₀`
writes `1`, then `p₁` reads `0` — is not linearizable. -/
theorem alg3_weak_not_linearizable :
    ∃ C : Cfg Bool ℕ, ∃ h, Reach (0 : ℕ) C h ∧ Validity C.log ∧ NoDuplication C.log ∧
      UniqueBc C.log ∧ WeakMutualOrdering C.log ∧ ¬ ∃ L, IsLinearization h L := by
  refine ⟨_, _, reach_weak, validity_of_validB (by decide),
    noDuplication_of_noDupB (by decide), uniqueBc_of_uniqueBcB (by decide), ?_, ?_⟩
  · refine weakMutualOrdering_of_own (noDuplication_of_noDupB (by decide)) ?_
    intro p q m hm
    simp only [mk2_log, weakLog, wLog, List.cons_append, List.nil_append, List.mem_cons,
      reduceCtorEq, Ev.dl.injEq, List.not_mem_nil, or_false, false_or] at hm
    rcases hm with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl
  · rintro ⟨L, hL⟩
    have h := IsLinearization.legal_of_seqExec
      (H := [(false, (.write 1 : RWOp ℕ), (1 : ℕ), 0), (true, .read, 0, 0)])
      (A := register ℕ 0) (L := L) hL
    simp [LegalFrom] at h

/-- The trace of the non-vacuity example. -/
def goodLog : List (Ev Bool (Msg Bool ℕ)) :=
  wLog ++ [.bc true (.synch 0), .dl true false (.synch 0),
    .dl true false (.write 0 1 (ts 1 false)), .dl true true (.synch 0),
    .bc true (.write 0 1 (ts 1 false)), .dl true true (.write 0 1 (ts 1 false))]

/-- **Non-vacuity.** An execution of Algorithm 3 whose MBroadcast trace satisfies the safety
properties of MBroadcast (with the strong reading of mutual ordering): `p₀` writes `1`, then `p₁`
reads `1`. -/
theorem alg3_nonvacuous :
    ∃ C : Cfg Bool ℕ, Reach (0 : ℕ) C
      [.inv false (.write 1), .ret false 1, .inv true .read, .ret true 1] ∧ Safe C.log := by
  have r5 := reach_write
  have r6 := reach_step r5 (Step.invR _ true (by simp) rfl)
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 0, .rSync⟩ (wLog ++ [.bc true (.synch 0)]))
    (by simp [mk2_upd_true])
  have r7 := reach_step r6 (Step.dlv _ true false (.synch 0) (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨0, ⊥, 0, .rSync⟩
      (wLog ++ [.bc true (.synch 0), .dl true false (.synch 0)]))
    (by simp [mk2_upd_true, handle])
  have r8 := reach_step r7 (Step.dlv _ true false (.write 0 1 (ts 1 false)) (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨1, ts 1 false, 0, .rSync⟩
      (wLog ++ [.bc true (.synch 0), .dl true false (.synch 0),
        .dl true false (.write 0 1 (ts 1 false))]))
    (by simp [mk2_upd_true, handle, bot_lt_ts])
  have r9 := reach_step r8 (Step.dlv _ true true (.synch 0) (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨1, ts 1 false, 0, .rSync⟩
      (wLog ++ [.bc true (.synch 0), .dl true false (.synch 0),
        .dl true false (.write 0 1 (ts 1 false)), .dl true true (.synch 0)]))
    (by simp [mk2_upd_true, handle])
  have r10 := reach_step r9 (Step.line5 _ true (by simp) rfl (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨1, ts 1 false, 0, .rFin 1 (ts 1 false)⟩
      (wLog ++ [.bc true (.synch 0), .dl true false (.synch 0),
        .dl true false (.write 0 1 (ts 1 false)), .dl true true (.synch 0),
        .bc true (.write 0 1 (ts 1 false))]))
    (by simp [mk2_upd_true])
  have r11 := reach_step r10 (Step.dlv _ true true (.write 0 1 (ts 1 false)) (by simp))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨1, ts 1 false, 0, .rFin 1 (ts 1 false)⟩ goodLog)
    (by simp [mk2_upd_true, handle, goodLog])
  have r12 := reach_step r11 (Step.retR _ true 1 (ts 1 false) (by simp) rfl (by simp [goodLog]))
    (D := mk2 ⟨1, ts 1 false, 1, .idle⟩ ⟨1, ts 1 false, 1, .idle⟩ goodLog)
    (by simp [mk2_upd_true])
  refine ⟨_, by simpa using r12, validity_of_validB (by decide),
    noDuplication_of_noDupB (by decide), mutualOrdering_of_moB (by decide)⟩

end Podc.MBroadcast.Alg3
