import Papers.PODC2014.RandomizationTwoHop.AStarPhase

/-!
# Analysis of `A*`, part 2: the run on an instance

Fix an instance `I = (V, E, i, c)` of `Πᶜ`. `Ip p = I^p` is `I` with the bits `b^p` added.

* `lang_Ip`: the views in `I^p` are the relabelled views of `I`; hence `Lv p (L∞(v)) =
  trunc p (L∞(v, I^p))` (the node computes its view of `I^p`).
* `bits_prefix`: bits only get extended (`b^p(u)` is a prefix of `b^q(u)` for `p ≤ q`).
* `outPhase_eq` (**Lemma 9**): every output produced in a phase `p ≤ P` coincides with the
  decision, after `p - 1` rounds, of the run `η` of `A_R` on `I` with the bits `b^P`.
  The proof is the locality lemma (`decided_local`): the simulation on the selected graph lasts
  `l ≤ p - 1` rounds and the node's view of tree depth `p ≥ l + 1` in `I^p` agrees with the
  view of `v*`.
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

namespace AStar

variable {In Out C : Type} [LinearOrder C] (Pb : Problem In Out) (AR : RAlg In Out)
  (I : LGraph (In × C))

/-- The bits `b^p(v)` on the instance. -/
noncomputable def bits (p : ℕ) (v : I.V) : List Bool := bL Pb AR p (⟪I⟫ v)

/-- The labelled graph `I^p = (V, E, i, c, b^p)`. -/
noncomputable def Ip (p : ℕ) : LGraph (L1 In C) := I.withLab fun v => (I.lab v, bits Pb AR I p v)

variable {I} (hIc : IsTwoHopColoring I.G (Prod.snd ∘ I.lab))
include hIc

theorem twoHop_I : I.TwoHop := hIc.of_comp Prod.snd

theorem lang_Ip (p : ℕ) (v : I.V) : ⟪Ip Pb AR I p⟫ v = relabel (bL Pb AR p) (⟪I⟫ v) :=
  lang_withLab_relabel (twoHop_I hIc) (bL Pb AR p) v

theorem Lv_eq (p : ℕ) (v : I.V) : Lv Pb AR p (⟪I⟫ v) = trunc p (⟪Ip Pb AR I p⟫ v) := by
  rw [lang_Ip Pb AR hIc]; rfl

theorem colors_Ip (p : ℕ) :
    IsTwoHopColoring (Ip Pb AR I p).G (Prod.snd ∘ Prod.fst ∘ (Ip Pb AR I p).lab) := hIc

theorem twoHop_Ip (p : ℕ) : (Ip Pb AR I p).TwoHop :=
  IsTwoHopColoring.of_comp (Prod.snd ∘ Prod.fst) (colors_Ip Pb AR hIc p)

omit hIc in
/-- Equal truncated views have equal root labels. -/
theorem lab_eq_of_trunc_eq {L : Type} {X Y : LGraph L} {u : X.V} {v : Y.V} {k : ℕ}
    (h : trunc k (⟪X⟫ u) = trunc k (⟪Y⟫ v)) : X.lab u = Y.lab v := by
  have : [X.lab u] ∈ trunc k (⟪Y⟫ v) := h ▸ ⟨single_mem_lang u, by simp⟩
  have := InLang.head this.1; simpa using this

theorem bits_succ_prefix (p : ℕ) (v : I.V) : bits Pb AR I p v <+: bits Pb AR I (p + 1) v := by
  unfold bits
  rw [bL_succ]
  cases h : (phase Pb AR p (Lv Pb AR p (⟪I⟫ v))).2 with
  | none => exact List.prefix_refl _
  | some b =>
    obtain ⟨J, -, vs, hvs, b', hb', rfl⟩ := phase_snd_spec Pb AR h
    rw [Lv_eq Pb AR hIc] at hvs
    have hl := lab_eq_of_trunc_eq hvs
    have : bitsJ J vs = bL Pb AR p (⟪I⟫ v) := by
      unfold bitsJ; rw [hl]; rfl
    rw [← this]; exact (hb'.1 vs).1

theorem bits_prefix {p q : ℕ} (hpq : p ≤ q) (v : I.V) : bits Pb AR I p v <+: bits Pb AR I q v := by
  induction hpq with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (bits_succ_prefix Pb AR hIc _ v)

omit hIc in
theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {k : ℕ} (hk : k < l₁.length) :
    l₁.getD k false = l₂.getD k false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

/-- **Lemma 9.** Every output produced by `A*` in a phase `p ≤ P` is the decision of `v` in the
execution `η` of `A_R` on `I` with the random bits `b^P` (within `p - 1` rounds). -/
theorem outPhase_eq {P p : ℕ} (hpP : p ≤ P) {v : I.V} {o : Out}
    (h : outPhase Pb AR p (⟪I⟫ v) = some o) :
    runX AR I (fun u => bitsOf (bits Pb AR I P u)) (p - 1) v = some o := by
  obtain ⟨hp1, J, hJc, vs, hvs, hall, hsim⟩ := phase_fst_spec Pb AR h
  rw [Lv_eq Pb AR hIc] at hvs
  set l := ⨅ T, (bitsJ J T).length with hl
  have hlvs : l ≤ (bitsJ J vs).length := ciInf_le (OrderBot.bddBelow _) vs
  have hlab := lab_eq_of_trunc_eq hvs
  have hbvs : bitsJ J vs = bits Pb AR I p v := by unfold bitsJ; rw [hlab]; rfl
  have hlp : l + 1 ≤ p := by
    have := length_bL Pb AR p (⟪I⟫ v)
    rw [hbvs] at hlvs; unfold bits at hlvs; omega
  have hJ2 : J.TwoHop := IsTwoHopColoring.of_comp (Prod.snd ∘ Prod.fst) hJc
  have hteq : TEq J.G J.lab (Ip Pb AR I p).G (Ip Pb AR I p).lab p vs v :=
    teq_of_trunc_lang_eq hJ2 (twoHop_Ip Pb AR hIc p) hvs
  have hteq' := (hteq.of_le hlp).map_lab (mG := runLab ((Prod.fst ∘ Prod.fst) ∘ J.lab)
      ((Prod.snd ∘ Prod.fst) ∘ J.lab) (fun T => bitsOf (bitsJ J T)) l)
    (mH := runLab (Prod.fst ∘ I.lab) (Prod.snd ∘ I.lab)
      (fun u => bitsOf (bits Pb AR I P u)) l) (by
      intro x y hxy
      have hx : l ≤ (bitsJ J x).length := ciInf_le (OrderBot.bddBelow _) x
      have hbx : bitsJ J x = bits Pb AR I p y := by unfold bitsJ; rw [hxy]; rfl
      simp only [runLab, Function.comp, hxy, Prod.mk.injEq, true_and]
      refine ⟨rfl, rfl, ?_⟩
      rw [List.ofFn_inj]; funext k
      unfold bitsOf
      rw [hbx]
      exact getD_of_prefix (bits_prefix Pb AR hIc hpP y) (by rw [← hbx]; omega))
  have hloc := decided_local AR (nbhdInj_of_twoHop (X := J.map Prod.fst) hJc)
    (nbhdInj_of_twoHop hIc) l vs v hteq'
  have : runX AR I (fun u => bitsOf (bits Pb AR I P u)) l v = some o := by
    rw [← hsim]; exact hloc.symm
  exact RAlg.decided_eq_some_mono (by omega) this

end AStar

end Podc.RandomizationTwoHop
