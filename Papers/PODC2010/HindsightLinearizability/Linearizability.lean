import Papers.PODC2010.HindsightLinearizability.History

/-!
# Theorem 7.5: linearizability of the set algorithm

The proof follows the paper. The function `ι` of the paper maps an `add`/`remove` to the source
state of its (successful) atomic section and a `contains` to a state between its invocation and
response in which the link `p.n ↦ c` it last crossed was a backbone link (found by hindsight).
The sequential history orders the operations by `ι`, a `contains` before the `add`/`remove`
associated with the same state. Here this is the generic criterion
`Cslib.SharedMemory.exists_isLinearization_of_points` (staged in `Podc/`), fed with

* the abstract state `Abs (memAt α j)` of the `j`-th state (Section 7.2),
* the effects `effAt α n` (successful atomic sections of `add`/`remove`, Stage II case
  `add`/`remove`: `step_secOk`),
* the retroactive linearization points of `contains` (Stage II case `contains`: `HistC`, which
  combines Lemma 6.3, the Hindsight/Backbone Lemma and the Local Window Lemma).
-/

namespace Podc.HindsightLinearizability

open Cslib.SharedMemory HeapState

variable {P : Type} [DecidableEq P]

lemma Abs_initMem : Abs initMem = ∅ := by
  have hbb : IsBB initMem [1, 0] := by
    obtain ⟨L, hL⟩ := memInv_init.bb
    refine ⟨rfl, rfl, by simp [HeapState.Link, Mem.hs, initMem],
      by simp [initMem], ?_⟩
    intro u hu; simp only [initMem] at hu ⊢; simp; omega
  ext z
  rw [MemInv.IsBB.mem_Abs_iff memInv_init hbb]
  simp [initMem, fin]

lemma memAt_zero (α : List (Label P setSpec)) : memAt α 0 = initMem := by
  simp [memAt, cfgAt, Impl.initCfg, impl]

/-- **Lemma 7.4.** In every reachable state the abstraction function is the set of integer keys
of the unmarked allocated nodes: `Abs(σ) = {u.k | u ∈ N_σ ∧ ¬u.m} \ {-∞, ∞}`. (That every
execution is mark-data-shape-legal is part of Theorem 4.1, `theorem_4_1_state`/`_step`.) -/
theorem lemma_7_4 {α : List (Label P setSpec)} {C : Config setSpec (fun _ : Unit => heapObj) P Loc}
    (h : (impl P).run α = some C) (z : ℤ) :
    z ∈ Abs (C.mem ()) ↔ ∃ u < (C.mem ()).cnt, (C.mem ()).mark u = false ∧ (C.mem ()).key u = fin z := by
  have hm := (inv_of_run h).1
  simp only [Abs, backboneKeys, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨u, hu, hk⟩
    have hlt := hm.backbone_lt hu
    exact ⟨u, hlt, (hm.unmarked_iff_backbone hlt).2 hu, hk⟩
  · rintro ⟨u, hlt, hmk, hk⟩
    exact ⟨u, (hm.unmarked_iff_backbone hlt).1 hmk, hk⟩

/-- **Theorem 7.5.** Every finite execution of the set algorithm of Fig. 1 is linearizable with
respect to the sequential specification of a set (Fig. 2). -/
theorem theorem_7_5 : (impl P).Linearizable := by
  classical
  refine Impl.linearizable_of_run (fun α C hrun => ?_)
  have hval : (impl P).Valid α := ⟨C, hrun⟩
  obtain ⟨-, -, -, hHC, hHE, hHE2, hInj⟩ := hist_of_run hrun
  have hwf := Impl.Valid.wellFormed _ hval
  -- the retroactive points of `contains`
  let Good : OpId P → ℕ → Prop := fun x j => j ≤ α.length ∧ Invoked (α.take j) x ∧
    ¬ Completed (α.take j) x ∧ ∀ k r, opOf α x = some (.contains k) → respOf α x = some r →
      (k ∈ Abs (memAt α j) ↔ r = true)
  let pt : OpId P → ℕ := fun x => if h : ∃ j, Good x j then h.choose else 0
  have hpt : ∀ x, (∃ j, Good x j) → Good x (pt x) := by
    intro x h; simp only [pt, h, dite_true]; exact h.choose_spec
  -- facts about effects
  have heff : ∀ n < α.length, ∀ x o, effAt α n = some (x, o) →
      opOf α x = some o ∧ Invoked (α.take n) x ∧ ¬ Completed (α.take (n + 1)) x ∧
      (∀ k, o ≠ .contains k) ∧
      (setSpec.δ (Abs (memAt α n)) o).1 = Abs (memAt α (n + 1)) ∧
      ∀ r, respOf α x = some r → (setSpec.δ (Abs (memAt α n)) o).2 = r := by
    intro n hn x o h
    obtain ⟨p, hp, rfl, -, hpend, hnc, -, habs⟩ := effAt_some hval hn h
    obtain ⟨hinv, -, hop⟩ := (impl P).run_pend_curOp (run_take hval n) hpend
    refine ⟨?_, hinv, ?_, hnc, habs.symm, fun r hr => ((hHE n hn _ o h).1 r hr).symm⟩
    · have := opOf_append_of_eq_some hop (α.drop n); rwa [List.take_append_drop] at this
    · rw [List.take_succ_eq_append_getElem hn, hp,
        completed_append_of_not_ret (fun _ _ h => by cases h)]
      exact not_completed_curOp _ _
  refine exists_isLinearization_of_points (fun j => Abs (memAt α j)) (effAt α)
    (fun x => ∃ k, opOf α x = some (.contains k)) pt ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show Abs (memAt α 0) = ∅; rw [memAt_zero, Abs_initMem]
  · exact fun n hn h => abs_of_effAt_none hval hn h
  · intro n hn x o h
    obtain ⟨h1, h2, h3, -, h5, h6⟩ := heff n hn x o h
    exact ⟨h1, h2, h3, h5, h6⟩
  · exact hInj
  · rintro x ⟨k, hk⟩ hc
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
    obtain ⟨j, hj, h1, h2, h3⟩ := hHC x k r hk hr
    have hg : Good x (pt x) := hpt x ⟨j, hj, h1, h2, fun k' r' hk' hr' => by
      rw [hk] at hk'; cases hk'; rw [hr] at hr'; cases hr'; exact h3⟩
    obtain ⟨g1, g2, g3, g4⟩ := hg
    refine ⟨_, hk, g1, g2, g3, rfl, fun r' hr' => ?_⟩
    have := g4 k r' hk hr'
    show decide (k ∈ Abs (memAt α (pt x))) = r'
    cases r'
    · exact decide_eq_false (fun h => Bool.false_ne_true (this.1 h))
    · exact decide_eq_true (this.2 rfl)
  · intro x hc
    have hinv := hwf.invoked_of_completed hc
    obtain ⟨o, ho⟩ : ∃ o, opOf α x = some o := by
      simp only [opOf]; exact ⟨_, List.getElem?_eq_getElem hinv⟩
    cases o with
    | contains k => exact Or.inl ⟨k, ho⟩
    | add k =>
      obtain ⟨n, hn, h⟩ := hHE2 x _ ho (fun _ h => by cases h) hc; exact Or.inr ⟨n, hn, _, h⟩
    | remove k =>
      obtain ⟨n, hn, h⟩ := hHE2 x _ ho (fun _ h => by cases h) hc; exact Or.inr ⟨n, hn, _, h⟩
  · rintro x ⟨k, hk⟩ n hn o h
    obtain ⟨h1, -, -, hnc, -⟩ := heff n hn x o h
    rw [hk] at h1; cases h1; exact hnc k rfl

end Podc.HindsightLinearizability
