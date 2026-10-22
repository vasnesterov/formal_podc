import Papers.PODC2022.RecoverableHarder.Theorem14

/-!
# Ruppert's theorem (Theorem 3), necessity

If objects of a deterministic type `S` and read/write objects solve wait-free consensus among
`n ≥ 2` processes, then `S` is `n`-discerning (Ruppert, SICOMP 2000; cited as Theorem 3 in the
paper, which uses it for Corollaries 17 and 20, Propositions 18 and 21). Readability is not
needed for this direction.

Proof: a crash-free critical execution; all processes are poised on one object `O`, which is not
read/write-like; teams by valency. If two schedules starting on opposite teams give a process `j`
the same response and `O` the same final value, `j` cannot distinguish them.
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

section RuppertNec

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-- The local state of a process `j` after a schedule of distinct processes poised on `O`, in
which `j` occurs at position `m`: it got the response of its operation on the value reached by the
processes before it. -/
lemma run_steps_loc {O : ι} (o : Fin n → (T O).Op) (κ : (p : Fin n) → (T O).Resp → A.L)
    (E : Cfg A) (hok : ∀ p, A.act (E.loc p) = .access O (o p) (κ p)) (σ : List (Fin n))
    (hσ : σ.Nodup) (m : ℕ) (hm : m < σ.length) :
    (run E (σ.map Ev.step)).loc σ[m] =
      κ σ[m] ((T O).δ (apply (T O) (E.mem O) o (σ.take m)) (o σ[m])).2 := by
  set j := σ[m]
  have hsplit : σ = σ.take m ++ j :: σ.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm]; exact (List.take_append_drop m σ).symm
  have hjt : j ∉ σ.take m := by
    intro h
    have := hsplit ▸ hσ
    rw [List.nodup_append] at this
    exact this.2.2 j h j (by simp) rfl
  have hjd : j ∉ σ.drop (m + 1) := by
    intro h
    have := hsplit ▸ hσ
    rw [List.nodup_append] at this
    exact (List.nodup_cons.1 this.2.1).1 h
  have hnd : (σ.take m).Nodup := hσ.sublist (List.take_sublist _ _)
  set E₁ := run E ((σ.take m).map Ev.step)
  have hloc₁ : E₁.loc j = E.loc j :=
    run_loc_other E _ (fun e he => by
      simp only [List.mem_map] at he; obtain ⟨q, hq, rfl⟩ := he
      exact fun h => hjt (by simpa [← h] using hq))
  have hmem₁ : E₁.mem O = apply (T O) (E.mem O) o (σ.take m) := by
    have := congrFun (run_steps_poised o κ (σ.take m) hnd E (fun p _ => hok p)) O
    rw [Function.update_self] at this; exact this
  have hact : A.act (E₁.loc j) = .access O (o j) (κ j) := by rw [hloc₁]; exact hok j
  conv_lhs => rw [hsplit]
  rw [List.map_append, run_append, List.map_cons, run_cons, Cfg.next_step]
  rw [run_loc_other _ _ (fun e he => by
      simp only [List.mem_map] at he; obtain ⟨q, hq, rfl⟩ := he
      exact fun h => hjd (by simpa [← h] using hq)),
    stepP_loc_self _ hact, hmem₁]

/-- **Ruppert's theorem, necessity.** If an algorithm for `n ≥ 2` processes solves wait-free
consensus, one of its object types is `n`-discerning. -/
theorem isDiscerning_of_wfConsensus (hn : 2 ≤ n) (hA : WFConsensus A) :
    ∃ i, IsDiscerning n (T i) := by
  classical
  have hAdm := admOK_crashFree (n := n)
  let x : Fin n → Bool := fun r => decide (r.val = 1)
  have hC : Reach A CrashFree (initCfg A x) := Reach.initial hAdm x
  have hb := biv_initial (z := 0) hA hAdm x ⟨⟨0, by omega⟩, by simp [x]⟩
    ⟨⟨1, by omega⟩, by simp [x]⟩
  obtain ⟨α, hc⟩ := exists_crit hA hAdm hC hb
  obtain ⟨O, hpo⟩ := hc.poised hA hAdm hC (by omega)
  choose o κ hok using hpo
  set E := run (initCfg A x) α
  choose val hval using fun p => hc.team p
  have huniq : ∀ p v, Team 0 (initCfg A x) α p v → v = val p :=
    fun p v h => Team.unique hA hAdm hC h (hval p)
  obtain ⟨⟨p0, hp0⟩, ⟨q0, hq0⟩⟩ := hc.teams hA hAdm hC (by omega)
  refine ⟨O, E.mem O, val, o, ⟨p0, (huniq p0 false hp0).symm⟩, ⟨q0, (huniq q0 true hq0).symm⟩, ?_⟩
  intro σ τ j m m' hm hm' hσ hτ hσne hτne tσ tτ hσj hτj heq
  obtain ⟨p, σ', rfl⟩ := List.exists_cons_of_ne_nil hσne
  obtain ⟨q, τ', rfl⟩ := List.exists_cons_of_ne_nil hτne
  simp only [List.head_cons] at tσ tτ
  have hp : Team 0 (initCfg A x) α p false := tσ ▸ hval p
  have hq : Team 0 (initCfg A x) α q (!false) := by simpa [tτ] using hval q
  obtain ⟨hresp, hfin⟩ := Prod.mk.inj heq
  -- the two crash-free extensions are indistinguishable to `j`
  have hag : AgreeOn {j} (run (initCfg A x) (α ++ [.step p] ++ σ'.map Ev.step))
      (run (initCfg A x) (α ++ [.step q] ++ τ'.map Ev.step)) := by
    have e1 : α ++ [.step p] ++ σ'.map Ev.step = α ++ (p :: σ').map Ev.step := by simp
    have e2 : α ++ [.step q] ++ τ'.map Ev.step = α ++ (q :: τ').map Ev.step := by simp
    rw [e1, e2, run_append _ α, run_append _ α]
    refine ⟨?_, fun r hr => ?_⟩
    · rw [run_steps_poised o κ _ hσ E (fun p _ => hok p),
        run_steps_poised o κ _ hτ E (fun p _ => hok p), hfin]
    · simp only [Set.mem_singleton_iff] at hr; subst hr
      refine ⟨?_, by simp⟩
      have h1 := run_steps_loc o κ E hok _ hσ m hm
      have h2 := run_steps_loc o κ E hok _ hτ m' hm'
      rw [hσj] at h1; rw [hτj] at h2
      rw [h1, h2, hresp]
  have hs : ∀ (l : List (Fin n)) (r : Fin n), InEs 0 (α ++ [.step r] ++ l.map Ev.step) :=
    fun l r => (hc.1.append_crashFree (crashFree_steps [r])).append_crashFree (crashFree_steps l)
  exact team_contra hA hAdm hC hp hq (hs σ' p) (hs τ' q) hag

/-- Read/write-like types are not discerning. -/
theorem not_isDiscerning_of_rwLike {S : ObjSpec} (hS : S.RWLike) : ¬ IsDiscerning n S := by
  intro h
  obtain ⟨u, team, o, ⟨i, hi⟩, ⟨j, hj⟩, hd⟩ := isDiscerning_iff.1 h
  have hij : team i ≠ team j := by simp [hi, hj]
  rcases hS (o i) with hro | hov
  · exact (DiscCond.pair hd hij).1 (by rw [hro u])
  · exact (DiscCond.pair hd (Ne.symm hij)).1 (hov _ _)

/-- Ruppert's theorem, necessity, for one type `S` with read/write objects. -/
theorem isDiscerning_of_wfSolvable {S : ObjSpec} (hn : 2 ≤ n) (h : WFSolvable S n) :
    IsDiscerning n S := by
  obtain ⟨ιR, ιS, _, _, R, hR, A, hA⟩ := h
  obtain ⟨i, hi⟩ := isDiscerning_of_wfConsensus hn hA
  rcases i with j | j
  · exact absurd hi (not_isDiscerning_of_rwLike (hR j))
  · exact hi

end RuppertNec

end Podc.RecoverableHarder
