import Papers.PODC2014.RandomizationTwoHop.Model

/-!
# Theorem 2: `Π ∈ GRAN ⇒ Πᶜ` is solvable in the infinity model (§2)

In the *infinity model* a node `v` outputs `A∞(L∞(v))` for a fixed function `A∞` of its
depth-infinity view. We represent `L∞(v)` by the walk language `⟪X⟫ v` (labels = input and
colour); `lang_eq_of_forall_teq` shows that this is a function of the view tree, so a function of
`⟪X⟫ v` is an infinity-model algorithm.

Construction of `A∞` (§2.1–2.3): from `T = L∞(v)` reconstruct the node set `reach T = V∞` of the
infinite view graph (`reach_lang`); choose (canonically in `V∞`) a graph realizing it and simulate
`A_R` on its infinite view graph `J` with colour-sorted ports, picking a successful bit assignment
(canonically in `V∞`, so all nodes pick the same: Lemma 1). Output the decision of the node `T`.

Correctness (§2.3.2): `J` is a factor of the instance (`isFactorMap_view`), the decider of `Π`
does not distinguish `J` from the instance (`inst_of_isFactorMap`, the lifting lemma), so `J ∈ Π`
and a successful simulation exists; lifting it to the instance gives an execution of `A_R` whose
output labelling is the one produced by `A∞`, hence valid.
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph Cslib.PortNumbering

variable {In Out C : Type} [LinearOrder C]

theorem Option.getD_eq_of_eq_some {α : Type} {o : Option α} {a d : α} (h : o = some a) :
    o.getD d = a := by simp [h]

theorem Option.eq_some_of_get_eq {α : Type} {o : Option α} {a : α} {hs : o.isSome}
    (h : o.get hs = a) : o = some a := by subst h; simp

theorem Option.get_eq_of_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a)
    (hs : o.isSome) : o.get hs = a := by simp [h]

/-- Colours of a 2-hop coloured graph are injective on neighbourhoods. -/
theorem nbhdInj_of_twoHop {X : LGraph (In × C)} (h : IsTwoHopColoring X.G (Prod.snd ∘ X.lab)) :
    NbhdInj X.G (Prod.snd ∘ X.lab) := fun v => h.injOn_nbhd v

/-- The colour-sorted runs on `X` are runs of `Solves` on `X.map Prod.fst`. -/
noncomputable abbrev runX (A : RAlg In Out) (X : LGraph (In × C)) (β : X.V → ℕ → Bool) : ℕ → X.V → Option Out :=
  runC A Prod.fst Prod.snd (X := X) β

/-- Specialization of `Solves` to colour-sorted ports. -/
theorem Solves.colored {A : RAlg In Out} {Pb : Problem In Out} (hA : Solves A Pb)
    {X : LGraph (In × C)} (hXi : Pb.inst (X.map Prod.fst))
    (hXc : IsTwoHopColoring X.G (Prod.snd ∘ X.lab)) :
    (∀ (β₀ : X.V → ℕ → Bool) (t₀ : ℕ), ∃ β : X.V → ℕ → Bool,
        (∀ v k, k < t₀ → β v k = β₀ v k) ∧ ∃ t, ∀ v, (runX A X β t v).isSome) ∧
    (∀ (β : X.V → ℕ → Bool) (t : ℕ) (h : ∀ v, (runX A X β t v).isSome),
        Pb.valid (X.map Prod.fst) (fun v => (runX A X β t v).get (h v))) :=
  hA (X.map Prod.fst) hXi (colorPN X.G (Prod.snd ∘ X.lab))
    (colorPN_isSimple (nbhdInj_of_twoHop hXc)) (colorPN_toSimpleGraph (nbhdInj_of_twoHop hXc))

/-- **Lifting lemma for the decider** (§2.3.2): if `Π ∈ GRAN` (its instances are decided by a
randomized anonymous algorithm `B`), then the input instances of `Π` are closed under factors
(of 2-hop coloured graphs): `B` cannot distinguish a factor from the instance. -/
theorem inst_of_isFactorMap {Pb : Problem In Out} {B : RAlg In Bool}
    (hB : Solves B (decision Pb.inst)) {X Y : LGraph (In × C)}
    (hX : IsTwoHopColoring X.G (Prod.snd ∘ X.lab)) {f : X.V → Y.V} (hf : IsFactorMap X Y f)
    (hXi : Pb.inst (X.map Prod.fst)) : Pb.inst (Y.map Prod.fst) := by
  have hY : IsTwoHopColoring Y.G (Prod.snd ∘ Y.lab) := hf.toIsLocalIso.twoHop Prod.snd hf.surj hX
  have hBY := hB (Y.map Prod.fst) trivial (colorPN Y.G (Prod.snd ∘ Y.lab))
    (colorPN_isSimple (nbhdInj_of_twoHop hY)) (colorPN_toSimpleGraph (nbhdInj_of_twoHop hY))
  have hBX := hB (X.map Prod.fst) trivial (colorPN X.G (Prod.snd ∘ X.lab))
    (colorPN_isSimple (nbhdInj_of_twoHop hX)) (colorPN_toSimpleGraph (nbhdInj_of_twoHop hX))
  obtain ⟨β, -, t, ht⟩ := hBY.1 (fun _ _ => false) 0
  have hlift : ∀ v, runX B X (β ∘ f) t v = runX B Y β t (f v) := fun v =>
    runC_localIso B Prod.fst Prod.snd (nbhdInj_of_twoHop hX) (nbhdInj_of_twoHop hY)
      hf.toIsLocalIso β t v
  have ht' : ∀ v, (runX B X (β ∘ f) t v).isSome := fun v => by rw [hlift]; exact ht (f v)
  by_contra hn
  obtain ⟨w, hw⟩ := (hBY.2 β t ht).2 hn
  obtain ⟨v, rfl⟩ := hf.surj w
  have hv := (hBX.2 (β ∘ f) t ht').1 hXi v
  change (runX B X (β ∘ f) t v).get (ht' v) = true at hv
  change (runX B Y β t (f v)).get (ht (f v)) = false at hw
  have hv' := Option.eq_some_of_get_eq hv
  have hw' := Option.eq_some_of_get_eq hw
  rw [hlift, hw'] at hv'
  exact Bool.noConfusion (Option.some.inj hv')

variable (Pb : Problem In Out) (A : RAlg In Out)

open Classical in
/-- The core of `A∞`: given the node set `S = V∞` and the own view `T`, simulate `A_R` on the
infinite view graph of a (canonically chosen) graph realizing `S`, with a (canonically chosen)
successful bit assignment, and return the decision of the node `T`. -/
noncomputable def infCore [Nonempty Out] (S : Set (Set (List (In × C))))
    (T : Set (List (In × C))) : Out :=
  if h : ∃ X : LGraph (In × C), Pb.inst (X.map Prod.fst) ∧
      IsTwoHopColoring X.G (Prod.snd ∘ X.lab) ∧ Set.range ⟪X⟫ = S then
    if hs : ∃ (β : (viewLGraph h.choose).V → ℕ → Bool) (t : ℕ),
        ∀ v, (runX A (viewLGraph h.choose) β t v).isSome then
      if hT : T ∈ Set.range ⟪h.choose⟫ then
        (runX A (viewLGraph h.choose) hs.choose hs.choose_spec.choose ⟨T, hT⟩).getD
          (Classical.arbitrary Out)
      else Classical.arbitrary Out
    else Classical.arbitrary Out
  else Classical.arbitrary Out

/-- The infinity-model algorithm `A∞` (§2): a function of the depth-infinity view. -/
noncomputable def Ainf [Nonempty Out] (T : Set (List (In × C))) : Out :=
  infCore Pb A (reach T) T

/-- **Theorem 2.** If `Π ∈ GRAN`, then `Πᶜ` is solvable in the infinity model: there is a
function `A∞` of depth-infinity local views (represented by walk languages, see
`lang_eq_of_forall_teq`) such that on every instance of `Πᶜ` the labelling
`v ↦ A∞(L∞(v))` is valid. -/
theorem theorem_2 [Nonempty Out] (hP : GRAN Pb) :
    ∃ Ainf : Set (List (In × C)) → Out, ∀ X : LGraph (In × C), (colored C Pb).inst X →
      (colored C Pb).valid X (fun v => Ainf (⟪X⟫ v)) := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := hP
  refine ⟨Ainf Pb A, fun X ⟨hXi, hXc⟩ => ?_⟩
  have hX2 : X.TwoHop := hXc.of_comp Prod.snd
  have hreach : ∀ v, reach (⟪X⟫ v) = Set.range ⟪X⟫ := fun v => reach_lang hX2 v
  have hE : ∃ Y : LGraph (In × C), Pb.inst (Y.map Prod.fst) ∧
      IsTwoHopColoring Y.G (Prod.snd ∘ Y.lab) ∧ Set.range ⟪Y⟫ = Set.range ⟪X⟫ :=
    ⟨X, hXi, hXc, rfl⟩
  set X₀ := hE.choose with hX₀
  obtain ⟨h0i, h0c, h0r⟩ := hE.choose_spec
  rw [← hX₀] at h0i h0c h0r
  set J := viewLGraph X₀
  have hg := isFactorMap_view (h0c.of_comp Prod.snd) hX2 h0r.symm
  have hJ0 := lemma_2 X₀ (h0c.of_comp Prod.snd)
  have hJc : IsTwoHopColoring J.G (Prod.snd ∘ J.lab) := hJ0.toIsLocalIso.twoHop Prod.snd hJ0.surj h0c
  have hJi : Pb.inst (J.map Prod.fst) := inst_of_isFactorMap hB h0c hJ0 h0i
  have hs : ∃ (β : J.V → ℕ → Bool) (t : ℕ), ∀ v, (runX A J β t v).isSome := by
    obtain ⟨β, -, t, ht⟩ := (hA.colored hJi hJc).1 (fun _ _ => false) 0
    exact ⟨β, t, ht⟩
  set β := hs.choose
  set t := hs.choose_spec.choose
  have ht : ∀ v, (runX A J β t v).isSome := hs.choose_spec.choose_spec
  set g : X.V → J.V := fun y => ⟨⟪X⟫ y, mem_range_of_eq h0r.symm y⟩
  have hlift : ∀ v, runX A X (β ∘ g) t v = runX A J β t (g v) := fun v =>
    runC_localIso A Prod.fst Prod.snd (nbhdInj_of_twoHop hXc) (nbhdInj_of_twoHop hJc)
      hg.toIsLocalIso β t v
  have ht' : ∀ v, (runX A X (β ∘ g) t v).isSome := fun v => by rw [hlift]; exact ht (g v)
  have hval := (hA.colored hXi hXc).2 (β ∘ g) t ht'
  show Pb.valid (X.map Prod.fst) (fun v => Ainf Pb A (⟪X⟫ v))
  convert hval using 2 with v
  -- unfold `A∞` at `L∞(v)`
  have hAv : Ainf Pb A (⟪X⟫ v) = (runX A J β t (g v)).getD (Classical.arbitrary Out) := by
    unfold Ainf
    rw [hreach v]
    unfold infCore
    have hE' : ∃ Y : LGraph (In × C), Pb.inst (Y.map Prod.fst) ∧
        IsTwoHopColoring Y.G (Prod.snd ∘ Y.lab) ∧ Set.range ⟪Y⟫ = Set.range ⟪X⟫ := hE
    rw [dif_pos hE', dif_pos hs, dif_pos (show ⟪X⟫ v ∈ Set.range ⟪hE.choose⟫ from
      mem_range_of_eq h0r.symm v)]
  rw [hAv]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (ht (g v))
  rw [Option.getD_eq_of_eq_some ho, Option.get_eq_of_eq_some ((hlift v).trans ho)]

end Podc.RandomizationTwoHop
