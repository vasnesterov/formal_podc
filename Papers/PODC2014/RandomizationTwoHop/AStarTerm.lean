import Papers.PODC2014.RandomizationTwoHop.AStarCorrect

/-!
# Analysis of `A*`, part 3: from phase `2n` on all nodes agree, and `A*` terminates

`n = |V∞|` is the number of different infinite views of the instance `I`.

* `card_S`: (**Observation 1**) adding the bits never separates nodes with equal infinite views:
  `I^p` has exactly `n` different infinite views.
* `mem_Fam` (**Lemma 6**): for `p ≥ n` the view graph of `I^p` is a candidate.
* `eq_of_mem_Fam` (**Lemma 7**): for `p ≥ 2n` every candidate with at most `n` views is the
  view graph of `I^p`; hence (`select_eq`, `phase_eq`) all nodes select it and `v* = L∞(v)`.
* `exists_ext`: some phase `z ≥ 2n` finds a successful extension of the bits (because `A_R`
  terminates with probability 1 on the view graph, which is an instance of `Π` by the lifting
  lemma for the decider). `terminates` (**Lemma 8**): in phase `z + 1` every node outputs, and the
  run of `A_R` on `I` with the bits `b^{z+1}` decides at every node within `z` rounds.
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

namespace AStar

variable {In Out C : Type} [LinearOrder C] (Pb : Problem In Out) (AR : RAlg In Out)
  {I : LGraph (In × C)}

omit [LinearOrder C] in
theorem relabel_injective {L β : Type} (f : Set (List L) → β) :
    Function.Injective (relabel f) := by
  intro T T' h
  have key : ∀ T : Set (List L), List.map Prod.fst '' relabel f T = T := by
    intro T; ext w; constructor
    · rintro ⟨_, ⟨w₀, hw₀, rfl⟩, rfl⟩; rw [map_fst_relabelWord]; exact hw₀
    · intro hw; exact ⟨_, ⟨w, hw, rfl⟩, map_fst_relabelWord f T w⟩
  rw [← key T, h, key]

/-- The node set of the view graph of `I^p`. -/
def S (p : ℕ) : Set (Set (List (L1 In C))) := Set.range ⟪Ip Pb AR I p⟫

variable (hIc : IsTwoHopColoring I.G (Prod.snd ∘ I.lab))
include hIc

theorem exR (p : ℕ) : ∃ G, Realizes (S Pb AR (I := I) p) G := ⟨Ip Pb AR I p, hIc, rfl⟩

/-- The simulation graph of phase `p` (the view graph of the canonical realizer of `S p`). -/
noncomputable def JJ (X : LGraph (L1 In C)) (h : ∃ G, Realizes (Set.range ⟪X⟫) G) :
    LGraph (L1 In C) := viewLGraph h.choose

omit hIc in
theorem JJ_congr {X Y : LGraph (L1 In C)} (e : X = Y) (hX : ∃ G, Realizes (Set.range ⟪X⟫) G)
    (hY : ∃ G, Realizes (Set.range ⟪Y⟫) G) : JJ X hX = JJ Y hY := by subst e; rfl

/-- `J_p`: the graph on which phase `p ≥ 2n` simulates `A_R`. -/
noncomputable def Jp (p : ℕ) : LGraph (L1 In C) := JJ (Ip Pb AR I p) (exR Pb AR hIc p)

theorem realizer_spec (p : ℕ) : Realizes (S Pb AR (I := I) p) (exR Pb AR hIc p).choose :=
  (exR Pb AR hIc p).choose_spec

theorem realizer_twoHop (p : ℕ) : (exR Pb AR hIc p).choose.TwoHop :=
  IsTwoHopColoring.of_comp (Prod.snd ∘ Prod.fst) (realizer_spec Pb AR hIc p).1

/-- The infinite view map `I^p → J_p`. -/
def gp (p : ℕ) (v : I.V) : (Jp Pb AR hIc p).V :=
  ⟨⟪Ip Pb AR I p⟫ v, mem_range_of_eq (realizer_spec Pb AR hIc p).2.symm v⟩

theorem isFactorMap_gp (p : ℕ) : IsFactorMap (Ip Pb AR I p) (Jp Pb AR hIc p) (gp Pb AR hIc p) :=
  isFactorMap_view (realizer_twoHop Pb AR hIc p) (twoHop_Ip Pb AR hIc p)
    (realizer_spec Pb AR hIc p).2.symm

theorem lang_gp (p : ℕ) (v : I.V) : ⟪Jp Pb AR hIc p⟫ (gp Pb AR hIc p v) = ⟪Ip Pb AR I p⟫ v :=
  (isFactorMap_gp Pb AR hIc p).lang_eq v

theorem colors_Jp (p : ℕ) :
    IsTwoHopColoring (Jp Pb AR hIc p).G (Prod.snd ∘ Prod.fst ∘ (Jp Pb AR hIc p).lab) :=
  (isFactorMap_gp Pb AR hIc p).toIsLocalIso.twoHop (Prod.snd ∘ Prod.fst)
    (isFactorMap_gp Pb AR hIc p).surj (colors_Ip Pb AR hIc p)

theorem twoHop_Jp (p : ℕ) : (Jp Pb AR hIc p).TwoHop :=
  IsTwoHopColoring.of_comp (Prod.snd ∘ Prod.fst) (colors_Jp Pb AR hIc p)

theorem lang_Jp (p : ℕ) (T : (Jp Pb AR hIc p).V) : ⟪Jp Pb AR hIc p⟫ T = T.1 :=
  lang_viewLGraph _ (realizer_twoHop Pb AR hIc p) T

theorem range_lang_Jp (p : ℕ) : Set.range ⟪Jp Pb AR hIc p⟫ = S Pb AR (I := I) p :=
  (range_lang_viewLGraph (realizer_twoHop Pb AR hIc p)).trans (realizer_spec Pb AR hIc p).2

/-- Bits of the simulation graph are the bits of the nodes. -/
theorem bitsJ_gp (p : ℕ) (v : I.V) :
    bitsJ (Jp Pb AR hIc p) (gp Pb AR hIc p v) = bits Pb AR I p v := by
  unfold bitsJ; rw [(isFactorMap_gp Pb AR hIc p).lab v]; rfl

/-- Simulations on `J_p` lift to runs on `I`. -/
theorem sim_gp (p : ℕ) (b : (Jp Pb AR hIc p).V → List Bool) (t : ℕ) (v : I.V) :
    sim AR (Jp Pb AR hIc p) b t (gp Pb AR hIc p v) =
      runX AR I (fun u => bitsOf (b (gp Pb AR hIc p u))) t v :=
  (runC_localIso AR (Prod.fst ∘ Prod.fst) (Prod.snd ∘ Prod.fst)
    (nbhdInj_of_twoHop (X := (Ip Pb AR I p).map Prod.fst) (colors_Ip Pb AR hIc p))
    (nbhdInj_of_twoHop (X := (Jp Pb AR hIc p).map Prod.fst) (colors_Jp Pb AR hIc p))
    (isFactorMap_gp Pb AR hIc p).toIsLocalIso (fun T => bitsOf (b T)) t v).symm

/-- **Observation 1.** `I^p` has as many different infinite views as `I`. -/
theorem card_S (p : ℕ) : (S Pb AR (I := I) p).ncard = Nat.card (viewLGraph I).V := by
  have : S Pb AR (I := I) p = relabel (bL Pb AR p) '' Set.range ⟪I⟫ := by
    ext T; constructor
    · rintro ⟨v, rfl⟩; exact ⟨_, ⟨v, rfl⟩, (lang_Ip Pb AR hIc p v).symm⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨v, lang_Ip Pb AR hIc p v⟩
  rw [this, Set.ncard_image_of_injective _ (relabel_injective _)]
  exact (Nat.card_coe_set_eq _).symm

theorem card_Jp (p : ℕ) : Nat.card (Jp Pb AR hIc p).V = Nat.card (viewLGraph I).V := by
  rw [← card_S Pb AR hIc p, ← (realizer_spec Pb AR hIc p).2]
  exact Nat.card_coe_set_eq _

variable {B : RAlg In Bool} (hB : Solves B (decision Pb.inst)) (hIi : Pb.inst (I.map Prod.fst))

include hB hIi in
/-- `J_p` is an instance of `Π` (lifting lemma for the decider). -/
theorem inst_Jp (p : ℕ) : Pb.inst (((Jp Pb AR hIc p).map Prod.fst).map Prod.fst) :=
  inst_of_isFactorMap hB (X := (Ip Pb AR I p).map Prod.fst) (colors_Ip Pb AR hIc p)
    (IsFactorMap.map Prod.fst (isFactorMap_gp Pb AR hIc p)) hIi

include hB hIi in
/-- **Lemma 6.** For `p ≥ n`, the view graph of `I^p` is a candidate. -/
theorem mem_Fam {p : ℕ} (hp : Nat.card (viewLGraph I).V ≤ p) (v : I.V) :
    S Pb AR (I := I) p ∈ Fam Pb p (trunc p (⟪Ip Pb AR I p⟫ v)) := by
  refine ⟨Jp Pb AR hIc p, ⟨?_, ⟨gp Pb AR hIc p v, ?_⟩, inst_Jp Pb AR hIc hB hIi p,
    colors_Jp Pb AR hIc p⟩, range_lang_Jp Pb AR hIc p⟩
  · rw [card_Jp]; exact hp
  · rw [lang_Jp]; rfl

/-- **Lemma 7.** For `p ≥ 2n`, a candidate with at most `n` views is the view graph of `I^p`. -/
theorem eq_of_mem_Fam {p : ℕ} (hp : 2 * Nat.card (viewLGraph I).V ≤ p) (v : I.V)
    {S' : Set (Set (List (L1 In C)))} (hS' : S' ∈ Fam Pb p (trunc p (⟪Ip Pb AR I p⟫ v)))
    (hcard : S'.ncard ≤ Nat.card (viewLGraph I).V) : S' = S Pb AR (I := I) p := by
  obtain ⟨G', ⟨-, ⟨v', hv'⟩, -, hG'c⟩, rfl⟩ := hS'
  have hG'2 : G'.TwoHop := IsTwoHopColoring.of_comp (Prod.snd ∘ Prod.fst) hG'c
  have hf' := lemma_2 G' hG'2
  have hteq : TEq (viewLGraph G').G (viewLGraph G').lab (Jp Pb AR hIc p).G (Jp Pb AR hIc p).lab p
      (toView G' v') (gp Pb AR hIc p v) := by
    apply teq_of_trunc_lang_eq (viewLGraph_twoHop G' hG'2) (twoHop_Jp Pb AR hIc p)
    rw [hf'.lang_eq, lang_gp, hv']
  have hc' : Nat.card (viewLGraph G').V = (Set.range ⟪G'⟫).ncard := Nat.card_coe_set_eq _
  have h2 : TEq (viewLGraph G').G (viewLGraph G').lab (Jp Pb AR hIc p).G (Jp Pb AR hIc p).lab
      (Nat.card (viewLGraph G').V + Nat.card (Jp Pb AR hIc p).V - 1)
      (toView G' v') (gp Pb AR hIc p v) := hteq.of_le (by rw [hc', card_Jp]; omega)
  have hall := teq_stable_two _ _ _ _ h2
  have hl := lang_eq_of_forall_teq hall
  rw [hf'.lang_eq, lang_gp] at hl
  rw [← reach_lang hG'2 v', hl, reach_lang (twoHop_Ip Pb AR hIc p) v]
  rfl

include hB hIi in
theorem select_eq {p : ℕ} (hp : 2 * Nat.card (viewLGraph I).V ≤ p) (v : I.V) :
    select (Fam Pb p (trunc p (⟪Ip Pb AR I p⟫ v))) = some (S Pb AR (I := I) p) := by
  have hmem := mem_Fam Pb AR hIc hB hIi (p := p) (by omega) v
  cases h : select (Fam Pb p (trunc p (⟪Ip Pb AR I p⟫ v))) with
  | none => rw [select_eq_none h] at hmem; exact absurd hmem (Set.notMem_empty _)
  | some S' =>
    obtain ⟨hS'F, hmin⟩ := select_spec h
    have := hmin _ hmem
    rw [card_S Pb AR hIc] at this
    rw [eq_of_mem_Fam Pb AR hIc hp v hS'F this]

include hB hIi in
/-- For `p ≥ 2n` all nodes select `J_p` and their own infinite view as `v*`. -/
theorem phase_eq {p : ℕ} (hp : 2 * Nat.card (viewLGraph I).V ≤ p) (v : I.V) :
    phase Pb AR p (Lv Pb AR p (⟪I⟫ v)) = phaseData AR p (Jp Pb AR hIc p) (gp Pb AR hIc p v) := by
  rw [Lv_eq Pb AR hIc]
  obtain ⟨vs, hvs, hph⟩ : ∃ vs : (Jp Pb AR hIc p).V,
      trunc p (⟪Jp Pb AR hIc p⟫ vs) = trunc p (⟪Ip Pb AR I p⟫ v) ∧
      phase Pb AR p (trunc p (⟪Ip Pb AR I p⟫ v)) = phaseData AR p (Jp Pb AR hIc p) vs := by
    obtain ⟨hR, -, -, vs, hvs, hph⟩ := phase_spec Pb AR (select_eq Pb AR hIc hB hIi hp v)
    exact ⟨vs, hvs, hph⟩
  rw [hph]
  congr 1
  -- uniqueness of `v*`
  have hteq : TEq (Jp Pb AR hIc p).G (Jp Pb AR hIc p).lab (Jp Pb AR hIc p).G
      (Jp Pb AR hIc p).lab p vs (gp Pb AR hIc p v) := by
    apply teq_of_trunc_lang_eq (twoHop_Jp Pb AR hIc p) (twoHop_Jp Pb AR hIc p)
    rw [hvs, lang_gp]
  have h2 : TEq (Jp Pb AR hIc p).G (Jp Pb AR hIc p).lab (Jp Pb AR hIc p).G
      (Jp Pb AR hIc p).lab (Nat.card (Jp Pb AR hIc p).V - 1) vs (gp Pb AR hIc p v) :=
    hteq.of_le (by rw [card_Jp]; omega)
  have hall := teq_stable _ _ h2
  have hl := lang_eq_of_forall_teq hall
  rw [lang_Jp, lang_Jp] at hl
  exact Subtype.ext hl

open Classical in
include hB hIi in
theorem bits_step {p : ℕ} (hp : 2 * Nat.card (viewLGraph I).V ≤ p) (v : I.V) :
    bits Pb AR I (p + 1) v = if hB : (extSet AR p (Jp Pb AR hIc p)).Nonempty then
      hB.some (gp Pb AR hIc p v) else bits Pb AR I p v := by
  unfold bits
  rw [bL_succ, phase_eq Pb AR hIc hB hIi hp v]
  simp only [phaseData]
  split_ifs <;> rfl

omit hIc in
theorem sim_eq_runX (J : LGraph (L1 In C)) (b : J.V → List Bool) :
    sim AR J b = runX AR (J.map Prod.fst) (fun T => bitsOf (b T)) := rfl

theorem length_bitsJ_Jp (p : ℕ) (T : (Jp Pb AR hIc p).V) : (bitsJ (Jp Pb AR hIc p) T).length ≤ p - 1 := by
  obtain ⟨u, rfl⟩ : ∃ u : I.V, gp Pb AR hIc p u = T := (isFactorMap_gp Pb AR hIc p).surj T
  rw [bitsJ_gp]; exact length_bL Pb AR p _

omit [LinearOrder C] hIc in
theorem bitsOf_ofFn {q k : ℕ} (f : Fin q → Bool) (hk : k < q) :
    bitsOf (List.ofFn f) k = f ⟨k, hk⟩ := by
  simp [bitsOf, List.getD_eq_getElem?_getD, hk]

include hB hIi in
/-- Some phase `z ≥ 2n` finds a successful extension (the termination part of Lemma 8). -/
theorem exists_ext (hA : Solves AR Pb) :
    ∃ z, 2 * Nat.card (viewLGraph I).V ≤ z ∧ (extSet AR z (Jp Pb AR hIc z)).Nonempty := by
  set N := Nat.card (viewLGraph I).V with hN
  by_contra hcon
  have hcon' : ∀ z, 2 * N ≤ z → ¬ (extSet AR z (Jp Pb AR hIc z)).Nonempty :=
    fun z hz hne => hcon ⟨z, hz, hne⟩
  have hconst : ∀ q, 2 * N ≤ q → bits Pb AR I q = bits Pb AR I (2 * N) := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => rfl
    | succ q hq ih =>
      funext v
      rw [bits_step Pb AR hIc hB hIi hq v, dif_neg (hcon' q hq), ih]
  have hJq : ∀ q, 2 * N ≤ q → Jp Pb AR hIc q = Jp Pb AR hIc (2 * N) := by
    intro q hq
    apply JJ_congr
    unfold Ip; rw [hconst q hq]
  have hAJ := hA.colored (X := (Jp Pb AR hIc (2 * N)).map Prod.fst) (inst_Jp Pb AR hIc hB hIi _) (colors_Jp Pb AR hIc _)
  obtain ⟨β, hag, t, ht⟩ := hAJ.1 (fun T => bitsOf (bitsJ (Jp Pb AR hIc (2 * N)) T)) (2 * N)
  set q := max (2 * N) t
  have hN1 : 1 ≤ N := Nat.card_pos
  apply hcon' q (le_max_left _ _)
  rw [hJq q (le_max_left _ _)]
  refine ⟨fun T => List.ofFn fun k : Fin q => β T k, fun T => ⟨?_, by simp⟩, fun T => ?_⟩
  · have hlen : (bitsJ (Jp Pb AR hIc (2 * N)) T).length < 2 * N := by
      have := length_bitsJ_Jp Pb AR hIc (2 * N) T; omega
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem
    · simp; omega
    · intro k hk _
      simp only [List.getElem_take, List.getElem_ofFn]
      rw [hag T k (by omega)]
      simp [bitsOf, List.getD_eq_getElem?_getD, hk]
  · rw [sim_eq_runX]
    have hb : ∀ T k, k < q → bitsOf (List.ofFn fun k : Fin q => β T k) k = β T k :=
      fun T k hk => bitsOf_ofFn _ hk
    change (AR.decided _ _ (fun T => bitsOf (List.ofFn fun k : Fin q => β T k)) q T).isSome
    rw [RAlg.decided_congr_bits hb, RAlg.decided_mono (le_max_right _ _) (ht T)]
    exact ht T

include hB hIi in
/-- **Lemma 8.** In phase `z + 1` all nodes output, and the run `η` of `A_R` on `I` with the bits
`b^{z+1}` decides at every node within `z` rounds. -/
theorem terminates (hA : Solves AR Pb) :
    ∃ z, (∀ v, (outPhase Pb AR (z + 1) (⟪I⟫ v)).isSome) ∧
      (∀ v, (runX AR I (fun u => bitsOf (bits Pb AR I (z + 1) u)) z v).isSome) := by
  obtain ⟨z, hz, hne⟩ := exists_ext Pb AR hIc hB hIi hA
  have hbz : bits Pb AR I (z + 1) = fun v => hne.some (gp Pb AR hIc z v) := by
    funext v; rw [bits_step Pb AR hIc hB hIi hz v, dif_pos hne]
  have hmem := hne.some_mem
  have hη : ∀ v, (runX AR I (fun u => bitsOf (bits Pb AR I (z + 1) u)) z v).isSome := by
    intro v
    rw [hbz, ← sim_gp]
    exact hmem.2 _
  refine ⟨z, fun v => ?_, hη⟩
  have hlen : ∀ T, (bitsJ (Jp Pb AR hIc (z + 1)) T).length = z := by
    intro T
    obtain ⟨u, rfl⟩ : ∃ u : I.V, gp Pb AR hIc (z + 1) u = T :=
      (isFactorMap_gp Pb AR hIc (z + 1)).surj T
    rw [bitsJ_gp, hbz]; exact (hmem.1 _).2
  have hl : (⨅ T, (bitsJ (Jp Pb AR hIc (z + 1)) T).length) = z := by
    simp only [hlen, ciInf_const]
  have hall : ∀ T, (sim AR (Jp Pb AR hIc (z + 1)) (bitsJ _) z T).isSome := by
    intro T
    obtain ⟨u, rfl⟩ : ∃ u : I.V, gp Pb AR hIc (z + 1) u = T :=
      (isFactorMap_gp Pb AR hIc (z + 1)).surj T
    rw [sim_gp]
    simp only [bitsJ_gp]
    exact hη u
  unfold outPhase
  rw [phase_eq Pb AR hIc hB hIi (by omega) v]
  simp only [phaseData]
  rw [hl, if_pos hall]
  exact hall _

end AStar

end Podc.RandomizationTwoHop
