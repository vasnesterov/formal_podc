import Papers.PODC2011.UnboundedConcurrency.Theorem10

/-!
# Non-vacuity of Theorem 10's hypotheses

Afek–Morrison–Wertheim, PODC 2011, Section 5. An algorithm in which every process proposes its
input to one *unbounded* consensus object (`consObj Bool`, accessible to all processes) and
decides the response solves binary consensus (agreement, validity, wait-freedom) under unbounded
concurrency (`consAlg_solvesCons`). So the requirements of `theorem_10` /
`no_consensus_of_rwLike_or_accessBounded` (agreement, weak validity, wait-freedom for all infinite
schedules) are jointly satisfiable in the model `Cslib.SharedMemory.Arrival`, and the hypothesis
`AccessBounded` (each consensus object is accessed by at most `c` processes) cannot be dropped.
-/

namespace Podc.UnboundedConcurrency.NonVacuity

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

/-- The objects: a single (unbounded) consensus object. -/
abbrev objs : Unit → ObjSpec := fun _ => consObj Bool

/-- Every process proposes its input to the consensus object and decides the response. -/
abbrev consAlg : Alg objs ℕ Bool Bool where
  L := Bool ⊕ Bool
  init _ v := .inl v
  act
    | .inl v => .access () v .inr
    | .inr v => .out v
  mem₀ _ := none

/-- Invariant: deciders hold the object's value; the object's value is the input of a process
that took a step; undecided processes still hold their input. -/
def Inv (x : ℕ → Bool) (σ : List ℕ) (C : Cfg consAlg) : Prop :=
  (∀ p v, C.loc p = .inr v → C.mem () = some v) ∧
  (∀ b, C.mem () = some b → ∃ q ∈ σ, x q = b) ∧
  (∀ p u, C.loc p = .inl u → u = x p)

lemma inv_exec (x : ℕ → Bool) (σ : List ℕ) : Inv x σ (consAlg.exec x σ) := by
  induction σ using List.reverseRecOn with
  | nil =>
    refine ⟨fun p v h => ?_, fun b h => ?_, fun p u h => ?_⟩
    · simp [Alg.exec, Alg.initCfg] at h
    · simp [Alg.exec, Alg.initCfg] at h
    · simpa [Alg.exec, Alg.initCfg, eq_comm] using h
  | append_singleton σ p ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Alg.exec_concat]
    set C := consAlg.exec x σ
    rcases hp : C.loc p with u | w
    · have hact : consAlg.act (C.loc p) = .access () u .inr := by rw [hp]
      rw [Arrival.Cfg.step_of_access hact]
      refine ⟨fun q v hq => ?_, fun b hb => ?_, fun q u' hq => ?_⟩
      · by_cases hqp : q = p
        · subst hqp; simp at hq ⊢; exact hq
        · simp [Function.update_of_ne hqp] at hq ⊢
          have := h1 q v hq; simp [this]
      · simp at hb
        cases hm : C.mem () with
        | none =>
          rw [hm] at hb; simp at hb
          exact ⟨p, by simp, by rw [← hb, h3 p u hp]⟩
        | some c =>
          rw [hm] at hb; simp at hb; subst hb
          obtain ⟨q, hq, hx⟩ := h2 c hm
          exact ⟨q, by simp [hq], hx⟩
      · by_cases hqp : q = p
        · subst hqp; simp at hq
        · simp [Function.update_of_ne hqp] at hq; exact h3 q u' hq
    · have hout : C.Out p w := by unfold Arrival.Cfg.Out; rw [hp]
      rw [Arrival.Cfg.step_of_out hout]
      refine ⟨h1, fun b hb => ?_, h3⟩
      obtain ⟨q, hq, hx⟩ := h2 b hb
      exact ⟨q, by simp [hq], hx⟩

lemma out_iff {C : Cfg consAlg} {p : ℕ} {v : Bool} : C.Out p v ↔ C.loc p = .inr v := by
  unfold Arrival.Cfg.Out
  rcases C.loc p with u | w <;> simp

/-- Non-vacuity of Theorem 10: one consensus object accessible to *all* processes solves binary
consensus wait-free under unbounded concurrency. -/
theorem consAlg_solvesCons : SolvesCons consAlg anySched infArrival where
  agreement x σ _ p _ q _ v w hv hw := by
    have h1 := (inv_exec x σ).1
    have := (h1 p v (out_iff.1 hv)).symm.trans (h1 q w (out_iff.1 hw))
    simpa using this
  validity x σ _ p _ v hv :=
    (inv_exec x σ).2.1 v ((inv_exec x σ).1 p v (out_iff.1 hv))
  waitFree x s _ p hp := by
    obtain ⟨t, -, ht⟩ := hp 0
    refine ⟨t + 1, ?_⟩
    rw [pre_succ, Alg.exec_concat, ht]
    set C := consAlg.exec x (pre s t)
    rcases hc : C.loc p with u | w
    · have hact : consAlg.act (C.loc p) = .access () u .inr := by rw [hc]
      exact ⟨_, by rw [out_iff, Arrival.Cfg.step_loc_self_of_access hact]⟩
    · have hout : C.Out p w := by unfold Arrival.Cfg.Out; rw [hc]
      exact ⟨w, hout.step p⟩

end Podc.UnboundedConcurrency.NonVacuity
