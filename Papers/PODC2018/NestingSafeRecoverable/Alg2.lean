import Papers.PODC2018.NestingSafeRecoverable.Alg2Succ

/-!
# Algorithm 2 of [ABH18] satisfies NRL (Lemma 3)

`lemma3`: every finite history of Algorithm 2 (the recoverable CAS object `alg2 P V`) whose
crash-free projection satisfies the environment assumption `Env2` (distinct `new` values per
process, `old ≠ new`) satisfies nesting-safe recoverable linearizability.

Proof: the invariant `Inv` (see `Alg2Lemmas.lean`) holds in every reachable configuration
(`inv_run`); it contains a linearization of `N(H)`.
-/

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL

namespace Alg2

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P] [DecidableEq V] [Fintype P]

variable {C : (alg2 P V).Cfg} {W : List (Cnt P V)} {L : Lin P V}

/-- Steps. -/
lemma Inv.ev_step (hI : Inv C W L) (henv : Env2 (N C.hist)) (p : P) :
    ∃ W' L', Inv (C.ev (.step p)) W' L' := by
  rcases hs : C.st p with _ | ⟨o, pc, v⟩
  · rw [Alg.ev_step_of_none C hs]; exact ⟨W, L, hI⟩
  · have hloc := (hI.pinv hs).2.1
    rcases o with ⟨old, new⟩ | _ <;> rcases pc with _ | _ | _ | _ | _ | _ | i | i | _ | _ <;>
      simp only [LocInv] at hloc
    · obtain ⟨L', h⟩ := hI.step_c2 hs; exact ⟨W, L', h⟩
    · obtain ⟨c, rfl, -⟩ := hloc
      obtain ⟨id, val⟩ := c
      by_cases h2 : val = old
      · rcases id with _ | k
        · exact ⟨W, L, hI.step_c3_none hs h2⟩
        · exact ⟨W, L, hI.step_c3_write hs h2⟩
      · exact ⟨W, L, hI.step_c3_ret hs h2⟩
    · obtain ⟨c, rfl, -⟩ := hloc
      by_cases hm : memC C = c
      · exact hI.step_c7_succ henv hs hm
      · exact ⟨W, L, hI.step_c7_fail hs hm⟩
    · rcases hloc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨W, L, hI.step_c8 hs⟩
    · exact ⟨W, L, hI.step_r13 hs⟩
    · exact ⟨W, L, hI.step_r14 hs⟩
    · exact ⟨W, L, hI.step_rR hs⟩
    · exact ⟨W, L, hI.step_rT hs⟩
    · obtain ⟨L', h⟩ := hI.step_rd10 hs; exact ⟨W, L', h⟩
    · obtain ⟨c, rfl, -⟩ := hloc
      exact ⟨W, L, hI.step_rd11 hs⟩

/-- The environment assumption is prefix closed. -/
lemma env2_prefix {h h' : List (Label P (casRObj V))} (hp : h <+: h') (he : Env2 h') :
    Env2 h := fun p =>
  ⟨(he p).1.sublist ((opsOf_prefix hp p).sublist.filterMap _),
    fun old new hm => (he p).2 old new ((opsOf_prefix hp p).subset hm)⟩

/-- The invariant holds in every reachable configuration (of an execution obeying `Env2`). -/
theorem inv_run (es : List (Ev P (casRObj V)))
    (he : Env2 (N ((alg2 P V).init.run es).hist)) :
    ∃ W L, Inv ((alg2 P V).init.run es) W L := by
  induction es using List.reverseRecOn with
  | nil => exact ⟨_, _, inv_init⟩
  | append_singleton es e ih =>
    rw [Alg.Cfg.run_concat] at he ⊢
    have hpre : Env2 (N ((alg2 P V).init.run es).hist) := by
      refine env2_prefix ?_ he
      obtain ⟨h, hh⟩ := Alg.ev_hist ((alg2 P V).init.run es) e
      rw [hh, N_append]
      exact List.prefix_append _ _
    obtain ⟨W, L, hI⟩ := ih hpre
    rcases e with ⟨p, o⟩ | p | p
    · exact ⟨W, L, hI.ev_inv (Alg.wfInv_run es) o he⟩
    · exact hI.ev_step hpre p
    · obtain ⟨L', h⟩ := hI.ev_crash (p := p); exact ⟨W, L', h⟩

/-- Non-vacuity of `Env2`: e.g. a process that invokes `CAS(null, 1)` and then `CAS(1, 2)`. -/
example : Env2 ([.inv 0 (.cas none 1), .ret 0 (.inl true), .inv 0 (.cas (some 1) 2)] :
    List (Label (Fin 2) (casRObj ℕ))) := by
  intro q
  fin_cases q <;> simp [opsOf, newOf, List.filterMap_cons, Label.invOf]
  rintro old new (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

end Alg2

open Alg2 in
/-- Lemma 3 of [ABH18]: Algorithm 2 satisfies NRL. (Under the assumption of the paper that every
process invokes `CAS` with pairwise distinct `new` values and never with `old = new`; `new` is
never `null`.) -/
theorem lemma3 (P V : Type) [DecidableEq P] [DecidableEq V] [Fintype P] :
    (alg2 P V).NRL Env2 :=
  (Alg.nrl_iff _).2 fun es he =>
    let ⟨_, L, hI⟩ := inv_run es he
    ⟨L, hI.lin⟩

end Podc.NestingSafeRecoverable
