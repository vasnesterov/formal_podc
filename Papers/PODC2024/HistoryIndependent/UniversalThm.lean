import Papers.PODC2024.HistoryIndependent.UniversalInv

/-!
# Algorithm 5: linearizability and state-quiescent history independence

Lemma 25 (linearizability, with the linearization function `hlin`), Lemmas 26–27 (in a
state-quiescent configuration `announce[i] = ⊥` and all contexts are empty) and the resulting
canonical memory representation `⟨q, ⊥⟩`: Algorithm 5 with atomic R-LLSC base objects is
state-quiescent history independent.
-/

namespace Cslib.SharedMemory

namespace Universal

open List

variable {A : ObjSpec} {n : ℕ} [DecidablePred A.ReadOnly]

lemma hlin_append (α β : List (Label (Fin n) A)) :
    ∃ M, hlin A n (α ++ β) = hlin A n α ++ M := by
  induction β using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton β ℓ ih =>
    obtain ⟨M, hM⟩ := ih
    exact ⟨M ++ contrib (α ++ β) ℓ, by rw [← List.append_assoc, hlin_snoc, hM, List.append_assoc]⟩

/-- **Lemma 25** (first part): `hlin` is a linearization function of Algorithm 5. -/
theorem isLinFun : (alg5 A n).IsLinFun (hlin A n) := by
  intro α ⟨C, hC⟩
  have hI := inv_run hC
  refine ⟨hI.nodup, hI.op_eq, hI.complete, ?_, ?_⟩
  · rintro a b ⟨β, γ, rfl, ha, hb⟩ hbL
    obtain ⟨Cβ, hCβ⟩ := (alg5 A n).valid_of_prefix ⟨C, hC⟩ (List.prefix_append β γ)
    have hIβ := inv_run hCβ
    obtain ⟨M, hM⟩ := hlin_append β γ
    rw [hM] at hbL ⊢
    have haβ := hIβ.complete a ha
    have hbβ : b ∉ (hlin A n β).map Prod.fst := fun hm => hb (hIβ.invoked hm)
    simp only [map_append, mem_append] at hbL ⊢
    rcases hbL with hbL | hbL
    · exact absurd hbL hbβ
    · exact (List.Sublist.append (List.singleton_sublist.2 haβ) (List.singleton_sublist.2 hbL) :
        [a] ++ [b] <+ _)
  · exact seqOK_of_respIn hI.nodup fun x r _ hr => hI.resp x r hr

/-- Algorithm 5 is linearizable. -/
theorem linearizable : (alg5 A n).Linearizable := ⟨_, isLinFun⟩

/-- **Lemma 25** (second part): `state(h_uc(α)) = q` where `head = ⟨q, _⟩`. -/
theorem linState_hlin {α : List (Label (Fin n) A)} {C : Config A (B A n) (Fin n) (Loc A n)}
    (h : (alg5 A n).run α = some C) : linState (hlin A n α) = (hv C.mem).1 :=
  (inv_run h).invC.h1

/-- The canonical memory representation of the abstract state `q`: `head = (⟨q, ⊥⟩, ∅)` and
`announce[j] = (⊥, ∅)`. -/
def canon (q : A.State) : Mem A n
  | .head => ((q, none), ∅)
  | .ann _ => (none, ∅)

/-- Program counters outside a state-changing operation. -/
def PC.quiet : PC A n → Bool
  | .idle | .ro _ | .roRet _ => true
  | _ => false

omit [DecidablePred A.ReadOnly] in
lemma quiet_of_stateQuiescent {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C : Config A (B A n) (Fin n) (Loc A n)} (hI : InvC L cur C.pend C.mem C.loc)
    (hq : C.StateQuiescent) (p : Fin n) : (C.loc p).pc.quiet = true ∧ av C.mem p = none := by
  have h := (hI.proc p).pinv
  cases hpc : (C.loc p).pc <;> rw [hpc] at h <;> simp only [PInv] at h <;>
    simp only [PC.quiet, true_and]
  all_goals first
    | exact absurd (hq p _ h.1) h.2.1
    | exact h.2
    | exact h.2.1
    | exact h.2.2.1
    | (obtain ⟨⟨o, h1, h2⟩, -⟩ := h; exact absurd (hq p o h1) h2)
    | (obtain ⟨o, h1, h2, -⟩ := h; exact absurd (hq p o h1) h2)

omit [DecidablePred A.ReadOnly] in
/-- **Lemmas 26 and 27** (and the end of the proof of Theorem 32): in a state-quiescent
configuration, `announce[i] = ⊥` for all `i`, `head = ⟨q, ⊥⟩`, and all contexts are empty; hence
the memory is the canonical representation of `q`. -/
theorem mem_eq_canon {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C : Config A (B A n) (Fin n) (Loc A n)} (hI : InvC L cur C.pend C.mem C.loc)
    (hq : C.StateQuiescent) : C.mem = canon (hv C.mem).1 := by
  have hQ := quiet_of_stateQuiescent hI hq
  have hav : ∀ j, av C.mem j = none := fun j => (hQ j).2
  have hpc : ∀ p, (C.loc p).pc.quiet = true := fun p => (hQ p).1
  have hmay : ∀ p, (C.loc p).pc.mayHC = false := fun p => by
    have := hpc p; revert this; cases (C.loc p).pc <;> simp [PC.quiet, PC.mayHC, PC.inLoop]
  have hhc : hc C.mem = ∅ := by
    ext p; simp only [Finset.notMem_empty, iff_false]
    intro hp; have := ((hI.proc p).ch hp).2; rw [hmay p] at this; cases this
  have hac : ∀ j, ac C.mem j = ∅ := fun j => by
    ext p; simp only [Finset.notMem_empty, iff_false]
    intro hp
    rcases (hI.proc p).ca2 j hp with ⟨-, e⟩ | e
    · have := hpc p; revert this e; cases (C.loc p).pc <;> simp [PC.quiet, PC.inVL]
    · exact e (hav j)
  have hhv : (hv C.mem).2 = none := by
    rcases h : (hv C.mem).2 with _ | ⟨rsp, j⟩
    · rfl
    · exfalso
      obtain ⟨-, e⟩ := (hI.proc j).h2 rsp h
      have := hpc j; revert this e
      cases (C.loc j).pc <;> simp [PC.quiet, PC.inLoop]
  funext i
  cases i with
  | head =>
    exact Prod.ext (Prod.ext rfl hhv) hhc
  | ann j =>
    exact Prod.ext (hav j) (hac j)

/-- **State-quiescent history independence** of Algorithm 5 with atomic R-LLSC base objects
(Section 6.2): with the linearization function `hlin`, two executions ending in state-quiescent
configurations whose linearizations reach the same abstract state have the same memory. -/
theorem stateQuiescentHI : (alg5 A n).StateQuiescentHI := by
  refine ⟨hlin A n, isLinFun, fun α α' C C' h h' hq hq' he => ?_⟩
  rw [mem_eq_canon (inv_run h).invC hq, mem_eq_canon (inv_run h').invC hq',
    ← linState_hlin h, ← linState_hlin h', he]

end Universal

end Cslib.SharedMemory
