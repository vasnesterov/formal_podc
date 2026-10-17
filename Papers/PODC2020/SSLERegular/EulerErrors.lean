import Papers.PODC2020.SSLERegular.EulerDynamics

/-!
# Detectable errors in the repaired SS-EulerCycle (part of Lemma 3.2)

From every configuration, either an error flag can be raised, or the configuration is coherent:
`Base` for its own skeleton, with colours injective on neighbourhoods (`InjCol`) and a virtual
edge on every edge (`EdgeOK`) (`error_or_coherent`). The errors are detected by:
* an edge without a virtual edge in either direction (one interaction);
* a matched SS-TwoHop pair with different bits: SS-TwoHop recolours, and recolouring the
  responder with a colour outside the initiator's slots breaks every virtual edge between them
  (`conflict_err`);
* two neighbours of a node with the same colour: the interaction sequence `(x,u), (x,v)` of the
  paper creates such a conflict.
-/

set_option linter.unusedSectionVars false

open Finset

namespace SSLERegular

variable {RS : Type*} {k : ℕ} {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  {R : RingProtocol RS}

/-- Some node has its error flag set. -/
def Err (C : V → EState k RS) : Prop := ∃ v, (C v).errFlag = true

/-- A colour outside all slots of a state. -/
lemma exists_fresh_color (hk : 1 ≤ k) (s : EState k RS) :
    ∃ c : Fin (4 * k ^ 2), ∀ i, (s.node i).succ ≠ c ∧ (s.node i).pred ≠ c := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin (4 * k ^ 2))) ⊆
      (Finset.univ.image fun i => (s.node i).succ) ∪ (Finset.univ.image fun i => (s.node i).pred) := by
    intro c _
    obtain ⟨i, hi⟩ := h c
    by_cases hs : (s.node i).succ = c
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hs⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi hs⟩)
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin k)))
    (f := fun i => (s.node i).succ)
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin k)))
    (f := fun i => (s.node i).pred)
  simp only [Finset.card_univ, Fintype.card_fin] at this h1 h2
  nlinarith

/-- A detected SS-TwoHop conflict leads to an error in one step. -/
lemma conflict_err (bidir : Bool) (hR : ∀ a b, (R.δ a b).Nonempty) (hk : 1 ≤ k)
    (C : V → EState k RS) {u v : V} (huv : G.Adj u v)
    (hc : (C u).prevColor = (C v).color ∧ (C v).prevColor = (C u).color ∧
      (C u).colorBit ≠ (C v).colorBit) :
    ∃ D, (ssEuler bidir k R).Step G C D ∧ Err D := by
  classical
  obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (C u).color (C u)
  obtain ⟨c', hc'⟩ := exists_fresh_color hk (C u)
  let ch3 := ch0.with3 c' (C u).color ch0.rb
  refine ⟨upd C u v (eulerStep bidir R ch3 (C u) (C v)), step_of_choice bidir C huv ch3
    (EChoice.with3_valid hch0 _ _ _), u, ?_⟩
  rw [upd_left _ (G.ne_of_adj huv), eulerStep_err]
  · rfl
  · rw [twoHopE_conflict _ _ _ hc]
    apply (tokenDetect_frame _).2.2
    have h1 : ¬ ∃ i, ((C u).node i).succ = c' := fun ⟨i, hi⟩ => (hc' i).1 hi
    have h2 : ¬ ∃ j, ((C u).node j).pred = c' := fun ⟨j, hj⟩ => (hc' j).2 hj
    simp only [ch3, EChoice.with3]
    simp [ringPart, FMatch, h1, h2]

/-- The "keep colours" interaction: an error, or only the SS-TwoHop memory changes in the
skeleton/bit data. -/
lemma keep_step (bidir : Bool) (ch0 : EChoice k RS) (hch0 : ch0.Valid R) (C : V → EState k RS)
    {u v : V} (huv : G.Adj u v) (rb : Bool) :
    (ssEuler bidir k R).Step G C
        (upd C u v (eulerStep bidir R (ch0.with3 (C v).color (C u).color rb) (C u) (C v))) ∧
      ((eulerStep bidir R (ch0.with3 (C v).color (C u).color rb) (C u) (C v)).1.errFlag = true ∨
        (Frame ((C u).withPrev (C v).color rb)
          (eulerStep bidir R (ch0.with3 (C v).color (C u).color rb) (C u) (C v)).1 ∧
         Frame ((C v).withPrev (C u).color rb)
          (eulerStep bidir R (ch0.with3 (C v).color (C u).color rb) (C u) (C v)).2)) := by
  refine ⟨step_of_choice bidir C huv _ (EChoice.with3_valid hch0 _ _ _), ?_⟩
  rcases eulerStep_cases bidir R (ch0.with3 (C v).color (C u).color rb) rfl (C u) (C v) with
    h | ⟨h1, h2, -, -⟩
  · exact Or.inl h
  · right
    have ht := twoHopE_keep rb (C u) (C v)
    simp only [EChoice.with3] at h1 h2 ht ⊢
    rw [ht] at h1 h2
    exact ⟨h1, h2⟩

/-- Two neighbours of `x` with the same colour lead to an error. -/
lemma samecolor_err (bidir : Bool) (hR : ∀ a b, (R.δ a b).Nonempty) (hk : 1 ≤ k)
    (C : V → EState k RS) {x u v : V} (hxu : G.Adj x u) (hxv : G.Adj x v) (huv : u ≠ v)
    (hcol : (C u).color = (C v).color) :
    ∃ D, (ssEuler bidir k R).Reachable G C D ∧ Err D := by
  classical
  obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (C x).color (C x)
  have hxu' := G.ne_of_adj hxu
  have hxv' := G.ne_of_adj hxv
  -- interaction 1: (x, u) with bit `false`
  obtain ⟨st1, r1⟩ := keep_step bidir ch0 hch0 C hxu false
  set C1 := upd C x u (eulerStep bidir R (ch0.with3 (C u).color (C x).color false) (C x) (C u))
    with hC1
  rcases r1 with e1 | ⟨f1x, f1u⟩
  · exact ⟨C1, Relation.ReflTransGen.single st1, x, by rw [hC1, upd_left _ hxu']; exact e1⟩
  have hC1x : Frame ((C x).withPrev (C u).color false) (C1 x) := by
    rw [hC1, upd_left _ hxu']; exact f1x
  have hC1u : Frame ((C u).withPrev (C x).color false) (C1 u) := by
    rw [hC1, upd_right]; exact f1u
  have hC1v : C1 v = C v := by rw [hC1, upd_other _ (Ne.symm hxv') (Ne.symm huv)]
  -- interaction 2: (x, v) with bit `true`
  obtain ⟨st2, r2⟩ := keep_step bidir ch0 hch0 C1 hxv true
  set C2 := upd C1 x v (eulerStep bidir R (ch0.with3 (C1 v).color (C1 x).color true) (C1 x) (C1 v))
    with hC2
  rcases r2 with e2 | ⟨f2x, -⟩
  · exact ⟨C2, (Relation.ReflTransGen.single st1).tail st2, x,
      by rw [hC2, upd_left _ hxv']; exact e2⟩
  have hC2x : Frame ((C1 x).withPrev (C1 v).color true) (C2 x) := by
    rw [hC2, upd_left _ hxv']; exact f2x
  have hC2u : C2 u = C1 u := by rw [hC2, upd_other _ (Ne.symm hxu') huv]
  -- the conflict at (x, u)
  have colx : (C2 x).color = (C x).color := by
    have a := congrArg Prod.fst hC2x.1; have b := congrArg Prod.fst hC1x.1
    simp only [skel, EState.withPrev] at a b; rw [a, b]
  have colu : (C2 u).color = (C u).color := by
    rw [hC2u]; have b := congrArg Prod.fst hC1u.1; simp only [skel, EState.withPrev] at b; exact b
  have hconf : (C2 x).prevColor = (C2 u).color ∧ (C2 u).prevColor = (C2 x).color ∧
      (C2 x).colorBit ≠ (C2 u).colorBit := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hC2x.2.1, colu]; simp only [EState.withPrev]; rw [hC1v, hcol]
    · rw [hC2u, hC1u.2.1, colx]; rfl
    · rw [hC2x.2.2, hC2u, hC1u.2.2]; simp [EState.withPrev]
  obtain ⟨D, hD, hE⟩ := conflict_err bidir hR hk C2 hxu hconf
  exact ⟨D, ((Relation.ReflTransGen.single st1).tail st2).tail hD, hE⟩

/-- **Error or coherence**: from every configuration of the repaired protocol, an error is
reachable, or the configuration is coherent for its own skeleton. -/
theorem error_or_coherent (hR : ∀ a b, (R.δ a b).Nonempty) (hk : 1 ≤ k) (C : V → EState k RS) :
    (∃ D, (ssEuler true k R).Reachable G C D ∧ Err D) ∨
      (InjCol G (fun v => skel (C v)) ∧ EdgeOK G (fun v => skel (C v)) ∧
        Base G (fun v => skel (C v)) C) := by
  classical
  by_cases hA : Err C
  · exact Or.inl ⟨C, Relation.ReflTransGen.refl, hA⟩
  have hN : NoErr C := fun v => by
    by_contra h; exact hA ⟨v, by simpa using h⟩
  -- colours injective on neighbourhoods
  by_cases hI : InjCol G (fun v => skel (C v))
  swap
  · left
    simp only [InjCol, not_forall] at hI
    obtain ⟨x, u, v, hxu, hxv, hcol, huv⟩ := hI
    exact samecolor_err true hR hk C hxu hxv huv hcol
  -- bit invariant
  by_cases hB : BitInv G C
  swap
  · left
    simp only [BitInv, not_forall] at hB
    obtain ⟨u, v, huv, h1, h2, h3⟩ := hB
    obtain ⟨D, hD, hE⟩ := conflict_err true hR hk C huv ⟨h1, h2, h3⟩
    exact ⟨D, Relation.ReflTransGen.single hD, hE⟩
  -- every edge carries a virtual edge
  by_cases hO : EdgeOK G (fun v => skel (C v))
  · exact Or.inr ⟨hI, hO, fun _ => rfl, hB, hN⟩
  left
  simp only [EdgeOK, not_forall, not_or] at hO
  obtain ⟨u, v, huv, hf, hb⟩ := hO
  obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (C u).color (C u)
  let ch := ch0.with3 (C v).color (C u).color ch0.rb
  refine ⟨_, Relation.ReflTransGen.single (step_of_choice true C huv ch
    (EChoice.with3_valid hch0 _ _ _)), u, ?_⟩
  rw [upd_left _ (G.ne_of_adj huv), eulerStep_err]
  · rfl
  · have ht := twoHopE_keep ch0.rb (C u) (C v)
    simp only [ch, EChoice.with3]
    rw [ht]
    apply (tokenDetect_frame _).2.2
    have h1 : ¬ ∃ i j, FMatch ((C u).withPrev (C v).color ch0.rb)
        ((C v).withPrev (C u).color ch0.rb) i j := by
      rintro ⟨i, j, h⟩
      exact hf ⟨i, j, huv, h.1, h.2⟩
    have h2 : ¬ ∃ i j, FMatch ((C v).withPrev (C u).color ch0.rb)
        ((C u).withPrev (C v).color ch0.rb) i j := by
      rintro ⟨i, j, h⟩
      exact hb ⟨i, j, huv.symm, h.1, h.2⟩
    dsimp only
    simp only [EState.withPrev] at h1 h2
    unfold ringPart
    rw [if_neg h1, if_neg (by simp only [true_and]; exact h2)]

end SSLERegular
