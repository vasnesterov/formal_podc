import Papers.PODC2014.RandomizationTwoHop.AStar

/-!
# Analysis of `A*`, part 1: what a single phase does

`phase_spec`: if phase `p` selects a node set `S`, then the simulation graph `J` (the infinite
view graph of the canonical realizer of `S`) is 2-hop coloured, has node set `S`, and contains a
node `vs` (the node `v*`) whose view of tree depth `p` is the node's view `L`; the phase's output
and new bits are those of `vs`.
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

namespace AStar

variable {In Out C : Type} [LinearOrder C] (Pb : Problem In Out) (AR : RAlg In Out)

theorem IsFactorMap.map {L L' : Type} (g : L → L') {X Y : LGraph L} {f : X.V → Y.V}
    (hf : IsFactorMap X Y f) : IsFactorMap (X.map g) (Y.map g) f where
  lab v := congrArg g (hf.lab v)
  bij v := hf.bij v
  surj := hf.surj

open Classical in
/-- The data of a phase on a simulation graph `J` with selected node `vs`. -/
noncomputable def phaseData (p : ℕ) (J : LGraph (L1 In C)) (vs : J.V) :
    Option Out × Option (List Bool) :=
  (if ∀ T, (sim AR J (bitsJ J) (⨅ T, (bitsJ J T).length) T).isSome then
      sim AR J (bitsJ J) (⨅ T, (bitsJ J T).length) vs else none,
   if hB : (extSet AR p J).Nonempty then some (hB.some vs) else none)

theorem trunc_lang_eq_viewLGraph {G : LGraph (L1 In C)} (hG : G.TwoHop) (T : (viewLGraph G).V)
    (p : ℕ) : trunc p (⟪viewLGraph G⟫ T) = trunc p T.1 := by
  rw [lang_viewLGraph G hG]

theorem range_lang_viewLGraph {L : Type} {G : LGraph L} (hG : G.TwoHop) :
    Set.range ⟪viewLGraph G⟫ = Set.range ⟪G⟫ := by
  ext T; constructor
  · rintro ⟨x, rfl⟩; rw [lang_viewLGraph G hG]; exact x.2
  · intro hT; exact ⟨⟨T, hT⟩, lang_viewLGraph G hG _⟩

/-- **The structure of a phase.** -/
theorem phase_spec {p : ℕ} {L : Set (List (L1 In C))} {S : Set (Set (List (L1 In C)))}
    (hS : select (Fam Pb p L) = some S) :
    ∃ hR : (∃ G, Realizes S G),
      IsTwoHopColoring (viewLGraph hR.choose).G (Prod.snd ∘ Prod.fst ∘ (viewLGraph hR.choose).lab) ∧
      Set.range ⟪viewLGraph hR.choose⟫ = S ∧
      ∃ vs : (viewLGraph hR.choose).V, trunc p (⟪viewLGraph hR.choose⟫ vs) = L ∧
        phase Pb AR p L = phaseData AR p (viewLGraph hR.choose) vs := by
  obtain ⟨hSF, -⟩ := select_spec hS
  obtain ⟨G', ⟨-, ⟨v', hv'⟩, -, hG'c⟩, hG'r⟩ := hSF
  have hR : ∃ G, Realizes S G := ⟨G', hG'c, hG'r⟩
  refine ⟨hR, ?_⟩
  obtain ⟨h0c, h0r⟩ := hR.choose_spec
  have h02 : hR.choose.TwoHop := IsTwoHopColoring.of_comp (Prod.snd ∘ Prod.fst) h0c
  have hJ := lemma_2 hR.choose h02
  have hJc : IsTwoHopColoring (viewLGraph hR.choose).G
      (Prod.snd ∘ Prod.fst ∘ (viewLGraph hR.choose).lab) :=
    hJ.toIsLocalIso.twoHop (Prod.snd ∘ Prod.fst) hJ.surj h0c
  have hJr : Set.range ⟪viewLGraph hR.choose⟫ = S := (range_lang_viewLGraph h02).trans h0r
  refine ⟨hJc, hJr, ?_⟩
  have hex : ∃ T : (viewLGraph hR.choose).V, trunc p (⟪viewLGraph hR.choose⟫ T) = L := by
    have : ⟪G'⟫ v' ∈ Set.range ⟪hR.choose⟫ := by rw [h0r, ← hG'r]; exact ⟨v', rfl⟩
    refine ⟨(⟨_, this⟩ : (viewLGraph hR.choose).V), ?_⟩
    exact (trunc_lang_eq_viewLGraph h02 _ p).trans hv'
  refine ⟨hex.choose, hex.choose_spec, ?_⟩
  unfold phase
  rw [hS]
  simp only [phaseS, dif_pos hR, phaseJ]
  rw [dif_pos hex]
  rfl

theorem phase_none {p : ℕ} {L : Set (List (L1 In C))} (hS : select (Fam Pb p L) = none) :
    phase Pb AR p L = (none, none) := by
  unfold phase; rw [hS]

theorem one_le_of_select {p : ℕ} {L : Set (List (L1 In C))} {S : Set (Set (List (L1 In C)))}
    (hS : select (Fam Pb p L) = some S) : 1 ≤ p := by
  obtain ⟨⟨G', ⟨hc, -⟩, -⟩, -⟩ := select_spec hS
  have : 0 < Nat.card G'.V := Nat.card_pos
  omega

/-- If phase `p` produces an output, it is the output of a node `vs` (with the right view) in a
successful simulation on a 2-hop coloured graph `J`. -/
theorem phase_fst_spec {p : ℕ} {L : Set (List (L1 In C))} {o : Out}
    (h : (phase Pb AR p L).1 = some o) :
    1 ≤ p ∧ ∃ J : LGraph (L1 In C), IsTwoHopColoring J.G (Prod.snd ∘ Prod.fst ∘ J.lab) ∧
      ∃ vs : J.V, trunc p (⟪J⟫ vs) = L ∧
        (∀ T, (sim AR J (bitsJ J) (⨅ T, (bitsJ J T).length) T).isSome) ∧
        sim AR J (bitsJ J) (⨅ T, (bitsJ J T).length) vs = some o := by
  cases hS : select (Fam Pb p L) with
  | none => rw [phase_none Pb AR hS] at h; cases h
  | some S =>
    obtain ⟨hR, hJc, -, vs, hvs, hph⟩ := phase_spec Pb AR hS
    rw [hph] at h
    simp only [phaseData] at h
    split_ifs at h with hall
    exact ⟨one_le_of_select Pb hS, _, hJc, vs, hvs, hall, h⟩

/-- If phase `p` changes the bits, the new bits are the value at `vs` of a successful
`p`-extension. -/
theorem phase_snd_spec {p : ℕ} {L : Set (List (L1 In C))} {b : List Bool}
    (h : (phase Pb AR p L).2 = some b) :
    ∃ J : LGraph (L1 In C), IsTwoHopColoring J.G (Prod.snd ∘ Prod.fst ∘ J.lab) ∧
      ∃ vs : J.V, trunc p (⟪J⟫ vs) = L ∧ ∃ b' ∈ extSet AR p J, b = b' vs := by
  cases hS : select (Fam Pb p L) with
  | none => rw [phase_none Pb AR hS] at h; cases h
  | some S =>
    obtain ⟨hR, hJc, -, vs, hvs, hph⟩ := phase_spec Pb AR hS
    rw [hph] at h
    simp only [phaseData] at h
    split_ifs at h with hB
    exact ⟨_, hJc, vs, hvs, hB.some, hB.some_mem, (Option.some.inj h).symm⟩

theorem length_bL (p : ℕ) (W : Set (List (In × C))) : (bL (C := C) Pb AR p W).length ≤ p - 1 := by
  induction p with
  | zero => simp [bL]
  | succ p ih =>
    rw [bL_succ]
    cases h : (phase Pb AR p (Lv Pb AR p W)).2 with
    | none => simp only [Option.getD_none]; omega
    | some b =>
      obtain ⟨J, -, vs, -, b', hb', rfl⟩ := phase_snd_spec Pb AR h
      simp only [Option.getD_some, (hb'.1 vs).2]; omega

end AStar

end Podc.RandomizationTwoHop
