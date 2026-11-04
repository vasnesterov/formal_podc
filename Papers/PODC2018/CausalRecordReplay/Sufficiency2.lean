import Papers.PODC2018.CausalRecordReplay.Model2

/-!
# Lemma C.1 and Theorem 6.6: the record of Theorem 6.6 is good (RnR Model 2)

Throughout, `V` are strongly causal views, `R = rec2 true V` is the record of Theorem 6.6
(`R_i = Â_i(V) \ (SWO_i(V) ∪ PO ∪ B_i(V))`, with the distinctness `w₃ ≠ w₄` in Definition 6.4), and
`V'` are strongly causal views respecting `R`.

* `lemma_C_1_a`: `SWO(V) ⊆ SWO(V')` (the paper's proof, made precise);
* `cov_preserved`: every cover of `A_i(V)` is in `A_i(V')`. This replaces the paper's proof of
  Lemma C.1(b) (bad write pairs, Claims C.2 and C.3), whose reduction to "bad write pairs" and
  cycle surgery in Claim C.3 have gaps; our proof picks a violated cover whose `wᵢ^min` is maximal
  in `SWO(V)` (preferring violated covers starting at `wᵢ^min` itself), shows that
  `C_i(V, o₁, w₂) ⊆ SWO(V')` (Claim C.2) and transfers the cycle of Definition 6.5 into `V'_m`;
* `lemma_C_1_b`: `B_i(V) ⊆ V'_i`;
* `theorem_6_6`: the record is good.
-/

namespace Podc.CausalRecordReplay

open Relation

variable {P Op X : Type*} {π : Program P Op X}

namespace Program

variable {V V' : P → Op → Op → Prop}

/-- Two operations of the same process ordered by `A_p(V)` are ordered by `PO`. -/
theorem po_of_Arel (hV : π.StronglyCausal V) {p : P} {a b : Op} (h : π.Arel V p a b)
    (hab : π.proc a = π.proc b) : π.po a b :=
  hV.po_of_view (Arel_view hV h) hab

/-- `A_p(V)`-pairs ending at a write of `p` transfer to `A_p(V')` once `SWO` pairs into it do. -/
theorem transfer_to_write (hV : π.StronglyCausal V) {p : P} {x w : Op} (hw : π.IsWrite w)
    (hwp : π.proc w = p) (hA : ∀ z, π.SWO V z w → π.SWO V' z w)
    (h : ReflGen (π.Arel V p) x w) : ReflGen (π.Arel V' p) x w := by
  rcases h with _ | h
  · exact ReflGen.refl
  by_cases hx : π.IsWrite x
  · exact ReflGen.single (SWO_sub_Arel p (hA x (SWO_of_Arel_write h hx hw hwp)))
  · have hxo := (Arel_obs hV h).1
    have hxp : π.proc x = p := hxo.resolve_right hx
    exact ReflGen.single (Arel_of_po (po_of_Arel hV h (hxp.trans hwp.symm)) hxo
      (Arel_obs hV h).2)

/-- A cover of `A_i(V)` that is a `DRO(V_i)` pair and is ordered the same way by `V'_i` is in
`A_i(V')`. -/
theorem Arel'_of_cov_view {i : P} {x y : Op} (hc : Cov (π.Arel V i) x y) (hpo : ¬ π.po x y)
    (hs : ¬ π.SWOi V i x y) (hv : V' i x y) : π.Arel V' i x y := by
  rcases Agen_of_cov hc with h | h | h
  · exact Arel_of_dro ⟨hv, h.2⟩
  · exact absurd h hs
  · exact absurd h.1 hpo

variable [Finite Op]

omit [Finite Op] in
/-- **Observation B.2 (2)**: if `C¹_i(V, o₁, w₂) ⊆ SWO(V)` then `(o₁, w₂) ∉ B_i(V)`. -/
theorem not_B2_of_C0_sub (hV : π.StronglyCausal V) {i : P} {o₁ w₂ : Op}
    (h0 : ∀ a b, π.Ck true V i o₁ w₂ 0 a b → π.SWO V a b) : ¬ π.B2 true V i o₁ w₂ := by
  have hC : ∀ k a b, π.Ck true V i o₁ w₂ k a b → π.SWO V a b := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      intro a b hab
      obtain ⟨ha, hb, -, w₅, w₆, h56, hp, h6b⟩ := hab
      set p := π.proc b
      have hpath : ReflGen (π.Arel V p) a w₅ := by
        have : ReflTransGen (π.Arel V p) a w₅ := reflTransGen_mono' (fun x y hxy => by
          rcases hxy with hxy | hxy
          · exact hxy
          · exact SWO_sub_Arel p (ih _ _ hxy)) hp
        rcases this.cases_head with h | ⟨c, hac, hcw⟩
        · exact h ▸ ReflGen.refl
        · exact ReflGen.single (of_transGen_of_trans (Arel_strictPO hV p).transitive
            (TransGen.head' hac hcw))
      have h56' : π.Arel V p w₅ w₆ := SWO_sub_Arel p (ih _ _ h56)
      have : π.Arel V p a b := reflGen_trans_right (Arel_strictPO hV p).transitive
        (reflGen_trans_left (Arel_strictPO hV p).transitive hpath h56') h6b
      exact SWO_of_Arel_write this ha hb rfl
  rintro ⟨-, -, -, m, hm⟩
  have hCA : ∀ j a b, π.Crel true V i o₁ w₂ a b → π.Arel V j a b :=
    fun j a b ⟨k, hk⟩ => SWO_sub_Arel j (hC k a b hk)
  rcases hm with ⟨-, x, hx⟩ | ⟨rfl, x, hx⟩
  · have := of_transGen_of_trans (Arel_strictPO hV m).transitive
      (transGen_mono' (fun a b h => h.elim id (hCA m a b)) hx)
    exact (Arel_strictPO hV m).irrefl x this
  · have := of_transGen_of_trans (Arel_strictPO hV m).transitive
      (transGen_mono' (fun a b h => h.elim (fun h => h.1) (hCA m a b)) hx)
    exact (Arel_strictPO hV m).irrefl x this

/-- **Lemma C.1 (a).** Every replay certified for the record of Theorem 6.6 preserves the strong
write order: `SWO(V) ⊆ SWO(V')`. -/
theorem lemma_C_1_a (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) : ∀ a b, π.SWO V a b → π.SWO V' a b := by
  intro a b
  induction b using (SWO_strictPO hV).wellFounded.induction generalizing a with
  | _ b ih =>
  intro hab
  set p := π.proc b
  have haw := (SWO_write hab).1
  have hbw := (SWO_write hab).2
  have hA := (Arel_strictPO hV p)
  have hA' := (Arel_strictPO hV' p)
  have hab' : π.Arel V p a b := SWO_sub_Arel p hab
  have key : ReflGen (π.Arel V' p) a b ∨ π.Arel V' p a b := by
    refine chain_induction hA hab' (fun y => ReflGen (π.Arel V' p) a y ∨ π.Arel V' p a b)
      (Or.inl ReflGen.refl) ?_
    intro x y hax hxy hyb hQ
    rcases hQ with hQ | hQ
    swap
    · exact Or.inr hQ
    have hxo := (Arel_obs hV hxy.1).1
    have hyo := (Arel_obs hV hxy.1).2
    have ext : π.Arel V' p x y → ReflGen (π.Arel V' p) a y ∨ π.Arel V' p a b := fun h =>
      Or.inl (ReflGen.single (reflGen_trans_left hA'.transitive hQ h))
    by_cases hpo : π.po x y
    · exact ext (Arel_of_po hpo hxo hyo)
    by_cases hs : π.SWOi V p x y
    · -- Case 3
      have hyb' : π.Arel V p y b := by
        rcases hyb with _ | h
        · exact absurd rfl hs.2
        · exact h
      have hyw := (SWO_write hs.1).2
      have := ih y (SWO_of_Arel_write hyb' hyw hbw rfl) x hs.1
      exact ext (Arel_of_SWOi ⟨this, hs.2⟩)
    by_cases hb : π.B2 true V p x y
    · -- Case 4
      obtain ⟨u, hu⟩ := exists_wmin (exists_write_of_B2 hV hb)
      have hub : π.proc u = π.proc b := hu.2.1
      by_cases hbu : ReflGen π.po b u
      · -- Case 4 (i): `C¹ ⊆ SWO(V)`, so `(x, y) ∉ B_p(V)`
        refine absurd hb (not_B2_of_C0_sub hV fun w₃ w₄ h => ?_)
        obtain ⟨h3, h4, h4p, hne, hx4, h3y⟩ := h
        have hu4 : ReflGen π.po u w₄ := hu.2.2.2 w₄ h4 h4p hx4
        have hpoT : TransRel π.po := fun _ _ _ h1 h2 => π.po_trans h1 h2
        have hb4 : ReflGen π.po b w₄ := reflGen_trans hpoT hbu hu4
        have hb4' : ReflGen (π.Arel V p) b w₄ := by
          rcases hb4 with _ | h
          · exact ReflGen.refl
          · exact ReflGen.single (Arel_of_po h (π.write_obs hbw p) (π.write_obs h4 p))
        have h3b : ReflGen (π.Arel V p) w₃ b := reflGen_trans hA.transitive h3y hyb
        exact SWO_of_Arel_write (reflGen_of_ne (reflGen_trans hA.transitive h3b hb4') (hne rfl))
          h3 h4 h4p
      · -- Case 4 (ii): `u <_PO b`
        have hub' : π.po u b := by
          rcases π.po_total hub (fun h => hbu (h ▸ ReflGen.refl)) with h | h
          · exact h
          · exact absurd (ReflGen.single h) hbu
        have hsub : π.SWO V u b := SWO_of_po hub' hu.1 hbw
        have hxu : ReflGen (π.Arel V' p) x u :=
          transfer_to_write hV hu.1 hu.2.1 (fun z hz => ih u hsub z hz) hu.2.2.1
        exact Or.inr (reflGen_trans_right hA'.transitive
          (reflGen_trans_left hA'.transitive (reflGen_trans hA'.transitive hQ hxu)
            (Arel_of_po hub' (π.write_obs hu.1 p) (π.write_obs hbw p))) ReflGen.refl)
    · exact ext (Arel'_of_cov_view hxy hpo hs (hR p x y ⟨hxy, hs, hpo, hb⟩))
  have : π.Arel V' p a b := key.elim (fun h => reflGen_of_ne h (by rintro rfl; exact hA.irrefl _ hab')) id
  exact SWO_of_Arel_write this haw hbw rfl

/-! ### Violated covers -/

variable (π) in
/-- A violated cover: a cover of `A_i(V)` that is not in `A_i(V')`. -/
def Viol (V V' : P → Op → Op → Prop) (i : P) (o w : Op) : Prop :=
  Cov (π.Arel V i) o w ∧ ¬ π.Arel V' i o w

theorem viol_props (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) {i : P} {o w : Op} (h : π.Viol V V' i o w) :
    π.B2 true V i o w ∧ ¬ π.po o w ∧ ¬ π.SWOi V i o w ∧ π.Arel V' i w o := by
  have hC1 := lemma_C_1_a hV hV' hR
  obtain ⟨hc, hn⟩ := h
  have ho := (Arel_obs hV hc.1).1
  have hw := (Arel_obs hV hc.1).2
  have hpo : ¬ π.po o w := fun hp => hn (Arel_of_po hp ho hw)
  have hs : ¬ π.SWOi V i o w := fun hs => hn (Arel_of_SWOi ⟨hC1 _ _ hs.1, hs.2⟩)
  have hdro : π.DRO (V i) o w := by
    rcases Agen_of_cov hc with h' | h' | h'
    · exact h'
    · exact absurd h' hs
    · exact absurd h'.1 hpo
  have hb : π.B2 true V i o w := by
    by_contra hb
    exact hn (Arel'_of_cov_view hc hpo hs (hR i o w ⟨hc, hs, hpo, hb⟩))
  refine ⟨hb, hpo, hs, ?_⟩
  have hne : o ≠ w := by rintro rfl; exact (Arel_strictPO hV i).irrefl _ hc.1
  have hv : V' i w o := (hV'.total i).of_not ho hw hne
    (fun hv => hn (Arel'_of_cov_view hc hpo hs hv))
  exact Arel_of_dro ⟨hv, hdro.2.symm⟩

/-- Transfer of an `A_m(V)` pair to `A_m(V')` along its covers, with an escape `G` that may be
concluded whenever a violated cover is met. -/
theorem transfer_esc (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) {m : P} {a b : Op} (hab : π.Arel V m a b)
    {G : Prop} (hesc : ∀ x y u', ReflGen (π.Arel V m) a x → π.Viol V V' m x y →
      π.IsWmin V m x u' → G) : π.Arel V' m a b ∨ G := by
  have hA' := Arel_strictPO hV' m
  have key : ReflGen (π.Arel V' m) a b ∨ G := by
    refine chain_induction (Arel_strictPO hV m) hab
      (fun y => ReflGen (π.Arel V' m) a y ∨ G) (Or.inl ReflGen.refl) ?_
    intro x y hax hxy _ hQ
    rcases hQ with hQ | hQ
    swap
    · exact Or.inr hQ
    by_cases hxy' : π.Arel V' m x y
    · exact Or.inl (ReflGen.single (reflGen_trans_left hA'.transitive hQ hxy'))
    · have hv : π.Viol V V' m x y := ⟨hxy, hxy'⟩
      obtain ⟨u', hu'⟩ := exists_wmin (exists_write_of_B2 hV (viol_props hV hV' hR hv).1)
      exact Or.inr (hesc x y u' hax hv hu')
  rcases key with h | h
  · exact Or.inl (reflGen_of_ne h (by rintro rfl; exact (Arel_strictPO hV m).irrefl _ hab))
  · exact Or.inr h

omit [Finite Op] in
theorem reflGen_po_or {a b : Op} (h : π.proc a = π.proc b) :
    ReflGen π.po a b ∨ π.po b a := by
  by_cases hab : a = b
  · exact Or.inl (hab ▸ ReflGen.refl)
  · rcases π.po_total h hab with h' | h'
    · exact Or.inl (ReflGen.single h')
    · exact Or.inr h'

omit [Finite Op] in
theorem reflGen_Arel_of_po {p : P} {a b : Op} (ha : π.Obs p a) (hb : π.Obs p b)
    (h : ReflGen π.po a b) : ReflGen (π.Arel V p) a b := by
  rcases h with _ | h
  · exact ReflGen.refl
  · exact ReflGen.single (Arel_of_po h ha hb)

omit [Finite Op] in
theorem reflGen_antisymm {r : Op → Op → Prop} (hr : IsStrictPO r) {a b : Op} (h1 : ReflGen r a b)
    (h2 : ReflGen r b a) : a = b := by
  rcases h1 with _ | h1
  · rfl
  rcases h2 with _ | h2
  · rfl
  exact absurd (hr.trans h1 h2) (hr.irrefl a)

omit [Finite Op] in
theorem isWmin_self (hV : π.StronglyCausal V) {u : Op} (hu : π.IsWrite u) :
    π.IsWmin V (π.proc u) u u := by
  refine ⟨hu, rfl, ReflGen.refl, fun w hw hwp huw => ?_⟩
  rcases huw with _ | huw
  · exact ReflGen.refl
  · exact ReflGen.single (po_of_Arel hV huw hwp.symm)

section Core

variable (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
  (hR : ∀ i a b, π.rec2 true V i a b → V' i a b)
  {i : P} {o w u : Op} (hviol : π.Viol V V' i o w) (hu : π.IsWmin V i o u)
  (hmax : ∀ i' x y u', π.Viol V V' i' x y → π.IsWmin V i' x u' → ¬ π.SWO V u u')
include hV hV' hR hviol hu hmax

/-- **Claim C.2** (for the extremal violated cover): `C_i(V, o, w) ⊆ SWO(V')`. -/
theorem stepA : ∀ k a t, π.Ck true V i o w k a t → π.SWO V' a t := by
  have hC1 := lemma_C_1_a hV hV' hR
  have hA'i := Arel_strictPO hV' i
  have hpoT : TransRel π.po := fun _ _ _ h1 h2 => π.po_trans h1 h2
  obtain ⟨-, -, -, hwo⟩ := viol_props hV hV' hR hviol
  intro k
  induction k with
  | zero =>
    intro w₃ w₄ h
    obtain ⟨h3, h4, h4i, hne, h04, h3w⟩ := h
    have hne : w₃ ≠ w₄ := hne rfl
    have hu4 : ReflGen π.po u w₄ := hu.2.2.2 w₄ h4 h4i h04
    have hou : ReflGen (π.Arel V' i) o u :=
      transfer_to_write hV hu.1 hu.2.1 (fun z => hC1 z u) hu.2.2.1
    have hu4' : ReflGen (π.Arel V' i) u w₄ :=
      reflGen_Arel_of_po (π.write_obs hu.1 i) (π.write_obs h4 i) hu4
    have hw4 : π.Arel V' i w w₄ := reflGen_trans_right hA'i.transitive
      (reflGen_trans_right hA'i.transitive hwo hou) hu4'
    have fin : π.Arel V' i w₃ w₄ → π.SWO V' w₃ w₄ := fun h => SWO_of_Arel_write h h3 h4 h4i
    rcases h3w with _ | h3w
    · exact fin hw4
    rcases transfer_esc hV hV' hR h3w (G := π.SWO V' w₃ w₄) (fun x y u' h3x _ hu' => by
        rcases reflGen_po_or (hu'.2.1.trans h4i.symm) with h | h
        · have : ReflGen (π.Arel V i) w₃ w₄ := reflGen_trans (Arel_strictPO hV i).transitive
            (reflGen_trans (Arel_strictPO hV i).transitive h3x hu'.2.2.1)
            (reflGen_Arel_of_po (π.write_obs hu'.1 i) (π.write_obs h4 i) h)
          exact hC1 _ _ (SWO_of_Arel_write (reflGen_of_ne this hne) h3 h4 h4i)
        · exfalso
          have : π.po u u' := reflGen_trans_left hpoT hu4 h
          exact hmax i x y u' ‹_› hu' (SWO_of_po this hu.1 hu'.1)) with h | h
    · exact fin (hA'i.trans h hw4)
    · exact h
  | succ k ih =>
    intro w₃ w₄ h
    have htarget : ReflGen (π.SWO V) u w₄ := wmin_le_Ck_target hV hu h
    obtain ⟨h3, h4, hne, w₅, w₆, h56, hp, h64⟩ := h
    have hne : w₃ ≠ w₄ := hne rfl
    set p := π.proc w₄
    have hA'p := Arel_strictPO hV' p
    have claim : ∀ a, ReflTransGen (fun x y => π.Arel V p x y ∨ π.Ck true V i o w k x y) a w₅ →
        ReflGen (π.Arel V' p) a w₄ := by
      intro a ha
      induction ha using ReflTransGen.head_induction_on with
      | refl =>
        have h1 : π.Arel V' p w₅ w₆ := SWO_sub_Arel p (ih _ _ h56)
        have h2 : ReflGen (π.Arel V' p) w₆ w₄ :=
          transfer_to_write hV h4 rfl (fun z => hC1 z w₄) h64
        exact ReflGen.single (reflGen_trans_right hA'p.transitive h1 h2)
      | @head a a₁ hstep _ ih' =>
        rcases hstep with hstep | hstep
        · rcases transfer_esc hV hV' hR hstep (G := ReflGen (π.Arel V' p) a w₄)
            (fun x y u' hax _ hu' => by
              rcases reflGen_po_or (hu'.2.1.trans (rfl : p = π.proc w₄)) with h | h
              · have : ReflGen (π.Arel V p) a w₄ := reflGen_trans (Arel_strictPO hV p).transitive
                  (reflGen_trans (Arel_strictPO hV p).transitive hax hu'.2.2.1)
                  (reflGen_Arel_of_po (π.write_obs hu'.1 p) (π.write_obs h4 p) h)
                exact transfer_to_write hV h4 rfl (fun z => hC1 z w₄) this
              · exfalso
                have h' : π.SWO V w₄ u' := SWO_of_po h h4 hu'.1
                exact hmax p x y u' ‹_› hu' (reflGen_trans_left (SWO_strictPO hV).transitive
                  htarget h')) with h | h
          · exact ReflGen.single (reflGen_trans_right hA'p.transitive h ih')
          · exact h
        · exact ReflGen.single (reflGen_trans_right hA'p.transitive
            (SWO_sub_Arel p (ih _ _ hstep)) ih')
    exact SWO_of_Arel_write (reflGen_of_ne (claim w₃ hp) hne) h3 h4 rfl

end Core

/-- The relation `(A_i(V) \ {(o, w)}) ∪ C_i(V, o, w)` of the `m = i` clause of Definition 6.5. -/
def Gi (V : P → Op → Op → Prop) (i : P) (o w : Op) (x y : Op) : Prop :=
  (π.Arel V i x y ∧ ¬ (x = o ∧ y = w)) ∨ π.Crel true V i o w x y

omit [Finite Op] in
theorem Arem_trans (hV : π.StronglyCausal V) {i : P} {o w : Op} (hc : Cov (π.Arel V i) o w)
    {x y z : Op} (h1 : π.Arel V i x y ∧ ¬ (x = o ∧ y = w))
    (h2 : π.Arel V i y z ∧ ¬ (y = o ∧ z = w)) : π.Arel V i x z ∧ ¬ (x = o ∧ z = w) := by
  refine ⟨Arel_trans h1.1 h2.1, ?_⟩
  rintro ⟨rfl, rfl⟩
  exact hc.2 y h1.1 h2.1

omit [Finite Op] in
/-- Walking back along a `Gᵢ`-path from `u` to the last `C`-target (or `u` itself). -/
theorem walk_back (hV : π.StronglyCausal V) {i : P} {o w u : Op} (hc : Cov (π.Arel V i) o w)
    {z : Op} (h : ReflTransGen (π.Gi V i o w) u z) :
    ∃ t, (t = u ∨ ∃ s, π.Crel true V i o w s t) ∧
      ReflGen (fun x y => π.Arel V i x y ∧ ¬ (x = o ∧ y = w)) t z := by
  induction h with
  | refl => exact ⟨u, Or.inl rfl, ReflGen.refl⟩
  | @tail y z _ hyz ih =>
    obtain ⟨t, ht, hty⟩ := ih
    rcases hyz with hyz | hyz
    · refine ⟨t, ht, ReflGen.single ?_⟩
      rcases hty with _ | hty
      · exact hyz
      · exact Arem_trans hV hc hty hyz
    · exact ⟨z, Or.inr ⟨y, hyz⟩, ReflGen.refl⟩

/-- The key lemma replacing the cycle surgery of Claim C.3: if the extremal violated cover starts at
`u = wᵢ^min` itself, then no cycle of `(A_i(V) \ {(u, w)}) ∪ C_i(V, u, w)` passes through a `C` edge
into `u`. -/
theorem lemmaX (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) {i : P} {u w : Op}
    (hviol : π.Viol V V' i u w) (hu : π.IsWmin V i u u) :
    ∀ ℓ c, π.Ck true V i u w ℓ c u → ReflTransGen (π.Gi V i u w) u c → False := by
  have hc := hviol.1
  have hA := Arel_strictPO hV i
  have hC1 := lemma_C_1_a hV hV' hR
  -- a `C`-target or `u` itself is above `u` in `A_i(V)`
  have habove : ∀ t, (t = u ∨ ∃ s, π.Crel true V i u w s t) → ReflGen (π.Arel V i) u t := by
    rintro t (rfl | ⟨s, hs⟩)
    · exact ReflGen.refl
    · rcases wmin_le_Crel_target hV hu hs with _ | h
      · exact ReflGen.refl
      · exact ReflGen.single (SWO_sub_Arel i h)
  intro ℓ
  induction ℓ with
  | zero =>
    intro c hcu hpath
    have hcw : ReflGen (π.Arel V i) c w := hcu.2.2.2.2.2
    have hne : c ≠ u := hcu.2.2.2.1 rfl
    obtain ⟨t, ht, htc⟩ := walk_back hV hc hpath
    have hut := habove t ht
    rcases hut with _ | hut
    · -- `t = u`
      rcases htc with _ | htc
      · exact hne rfl
      · have hcw' : c ≠ w := fun h => htc.2 ⟨rfl, h⟩
        exact hc.2 c htc.1 (reflGen_of_ne hcw hcw')
    · -- `u < t`
      have htw : ReflGen (π.Arel V i) t w := reflGen_trans hA.transitive
        (by rcases htc with _ | htc
            · exact ReflGen.refl
            · exact ReflGen.single htc.1) hcw
      rcases htw with _ | htw
      · -- `t = w`: then `(u, w) ∈ SWO(V) ⊆ SWO(V')`, not violated
        rcases ht with rfl | ⟨s, hs⟩
        · exact hA.irrefl _ hut
        rcases wmin_le_Crel_target hV hu hs with _ | hsw
        · exact hA.irrefl _ hut
        · exact hviol.2 (SWO_sub_Arel i (hC1 _ _ hsw))
      · exact hc.2 t hut htw
  | succ ℓ ih =>
    intro c hcu hpath
    obtain ⟨-, -, hne, w₅, w₆, h56, hp, h6u⟩ := hcu
    have hne : c ≠ u := hne rfl
    rw [hu.2.1] at hp h6u
    have h6 : w₆ = u := by
      have h1 : ReflGen (π.Arel V i) u w₆ := by
        rcases wmin_le_Ck_target hV hu h56 with _ | h
        · exact ReflGen.refl
        · exact ReflGen.single (SWO_sub_Arel i h)
      exact (reflGen_antisymm hA h1 h6u).symm
    subst h6
    have claim : ∀ z, ReflTransGen (fun x y => π.Arel V i x y ∨ π.Ck true V i w₆ w ℓ x y) c z →
        ReflTransGen (π.Gi V i w₆ w) w₆ z ∧ z ≠ w₆ := by
      intro z hz
      induction hz with
      | refl => exact ⟨hpath, hne⟩
      | @tail y z _ hyz ihz =>
        obtain ⟨hy, hyu⟩ := ihz
        by_cases hzu : z = w₆
        · subst hzu
          rcases hyz with hyz | hyz
          · exfalso
            obtain ⟨t, ht, hty⟩ := walk_back hV hc hy
            have h1 := habove t ht
            have h2 : ReflGen (π.Arel V i) t y := by
              rcases hty with _ | hty
              · exact ReflGen.refl
              · exact ReflGen.single hty.1
            exact hA.irrefl _ (reflGen_trans_left hA.transitive
              (reflGen_trans hA.transitive h1 h2) hyz)
          · exact absurd hy (fun hy => ih y hyz hy)
        · refine ⟨ReflTransGen.tail hy ?_, hzu⟩
          rcases hyz with hyz | hyz
          · exact Or.inl ⟨hyz, fun h => hyu h.1⟩
          · exact Or.inr ⟨ℓ, hyz⟩
    exact ih w₅ h56 (claim w₅ hp).1

/-- First `C` edge of a path of `A ∪ C`. -/
theorem first_C_edge {m i : P} {o w : Op} {G : Op → Op → Prop}
    (hG : ∀ x y, G x y ↔ (π.Arel V m x y ∧ ¬ (m = i ∧ x = o ∧ y = w)) ∨ π.Crel true V i o w x y)
    {a b : Op} (h : TransGen G a b) :
    TransGen (π.Arel V m) a b ∨
      ∃ s t, π.Crel true V i o w s t ∧ ReflTransGen G a s ∧ ReflTransGen G t b := by
  induction h with
  | single hab =>
    rcases (hG _ _).1 hab with h | h
    · exact Or.inl (TransGen.single h.1)
    · exact Or.inr ⟨_, _, h, ReflTransGen.refl, ReflTransGen.refl⟩
  | @tail y z hay hyz ih =>
    rcases ih with ih | ⟨s, t, hst, has, hty⟩
    · rcases (hG _ _).1 hyz with h | h
      · exact Or.inl (TransGen.tail ih h.1)
      · exact Or.inr ⟨y, z, h, hay.to_reflTransGen, ReflTransGen.refl⟩
    · exact Or.inr ⟨s, t, hst, has, ReflTransGen.tail hty hyz⟩

/-- **Claim C.3** (for the extremal violated cover): the cycle of Definition 6.5 transfers to a cycle
of `A_m(V') ∪ SWO(V') ⊆ V'_m`, a contradiction. -/
theorem stepB (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) {i : P} {o w u : Op}
    (hviol : π.Viol V V' i o w) (hu : π.IsWmin V i o u)
    (hmax : ∀ i' x y u', π.Viol V V' i' x y → π.IsWmin V i' x u' → ¬ π.SWO V u u')
    (hpref : (∃ w', π.Viol V V' i u w') → o = u) : False := by
  obtain ⟨hB, -, -, -⟩ := viol_props hV hV' hR hviol
  have hCsub : ∀ a t, π.Crel true V i o w a t → π.SWO V' a t :=
    fun a t ⟨k, hk⟩ => stepA hV hV' hR hviol hu hmax k a t hk
  obtain ⟨-, -, -, m, hm⟩ := hB
  set Gm : Op → Op → Prop :=
    fun x y => (π.Arel V m x y ∧ ¬ (m = i ∧ x = o ∧ y = w)) ∨ π.Crel true V i o w x y with hGm
  have hcyc : ∃ x, TransGen Gm x x := by
    rcases hm with ⟨hmi, x, hx⟩ | ⟨rfl, x, hx⟩
    · exact ⟨x, transGen_mono' (fun a b h => h.elim (fun h => Or.inl ⟨h, fun h' => hmi h'.1⟩)
        Or.inr) hx⟩
    · exact ⟨x, transGen_mono' (fun a b h => h.elim (fun h => Or.inl ⟨h.1, fun h' => h.2 h'.2⟩)
        Or.inr) hx⟩
  obtain ⟨x, hx⟩ := hcyc
  have hAm := Arel_strictPO hV m
  have hA'm := Arel_strictPO hV' m
  rcases first_C_edge (G := Gm) (fun _ _ => Iff.rfl) hx with hx | ⟨s₀, t₀, hst₀, hxs, htx⟩
  · exact hAm.irrefl x (of_transGen_of_trans hAm.transitive hx)
  have hloop : ReflTransGen Gm t₀ s₀ := htx.trans hxs
  -- transfer from a `C` target
  have TP : ∀ s' t' z, π.Crel true V i o w s' t' → ReflTransGen Gm t' s' →
      ReflGen (π.Arel V m) t' z → ReflGen (π.Arel V' m) t' z := by
    intro s' t' z hs' hback htz
    rcases htz with _ | htz
    · exact ReflGen.refl
    rcases transfer_esc hV hV' hR htz (G := False) (fun x y u' htx hv hu' => by
        have hut' : ReflGen (π.Arel V m) u t' := by
          rcases wmin_le_Crel_target hV hu hs' with _ | h
          · exact ReflGen.refl
          · exact ReflGen.single (SWO_sub_Arel m h)
        have hux : ReflGen (π.Arel V m) u x := reflGen_trans hAm.transitive hut' htx
        have huu' : ReflGen (π.Arel V m) u u' := reflGen_trans hAm.transitive hux hu'.2.2.1
        by_cases hne : u = u'
        · subst hne
          have hxu : x = u := reflGen_antisymm hAm hu'.2.2.1 hux
          have htu : t' = u := reflGen_antisymm hAm (hxu ▸ htx) hut'
          subst hxu htu
          have hmi : m = i := hu'.2.1.symm.trans hu.2.1
          subst hmi
          have hou : o = t' := hpref ⟨y, hv⟩
          subst hou
          obtain ⟨ℓ, hℓ⟩ := hs'
          exact lemmaX hV hV' hR hviol hu ℓ s' hℓ (reflTransGen_mono' (fun a b h => by
            rcases h with h | h
            · exact Or.inl ⟨h.1, fun h' => h.2 ⟨rfl, h'⟩⟩
            · exact Or.inr h) hback)
        · exact hmax m x y u' hv hu'
            (SWO_of_Arel_write (reflGen_of_ne huu' hne) hu.1 hu'.1 hu'.2.1)) with h | h
    · exact ReflGen.single h
    · exact h.elim
  -- the invariant along the cycle
  have inv : ∀ z, ReflTransGen Gm t₀ z → ReflTransGen Gm z s₀ →
      ∃ s' t', π.Crel true V i o w s' t' ∧ ReflTransGen Gm t₀ s' ∧ ReflTransGen Gm t' z ∧
        ReflGen (π.Arel V' m) t₀ t' ∧ ReflGen (π.Arel V m) t' z := by
    intro z hz
    induction hz with
    | refl => exact fun _ => ⟨s₀, t₀, hst₀, hloop, ReflTransGen.refl, ReflGen.refl, ReflGen.refl⟩
    | @tail y z hty hyz ih =>
      intro hzs
      obtain ⟨s', t', hs', h0s', ht'y, h0t', ht'yA⟩ := ih (ReflTransGen.head hyz hzs)
      rcases hyz with hyz | hyz
      · exact ⟨s', t', hs', h0s', ReflTransGen.tail ht'y (Or.inl hyz), h0t',
          ReflGen.single (reflGen_trans_left hAm.transitive ht'yA hyz.1)⟩
      · have hback : ReflTransGen Gm t' s' :=
          ((ht'y.tail (Or.inr hyz)).trans hzs).trans (ReflTransGen.head (Or.inr hst₀) h0s')
        have h1 := TP s' t' y hs' hback ht'yA
        have h2 : π.Arel V' m y z := SWO_sub_Arel m (hCsub y z hyz)
        exact ⟨y, z, hyz, hty, ReflTransGen.refl,
          ReflGen.single (reflGen_trans_left hA'm.transitive (reflGen_trans hA'm.transitive h0t' h1)
            h2), ReflGen.refl⟩
  obtain ⟨s', t', hs', h0s', ht's, h0t', ht'sA⟩ := inv s₀ hloop ReflTransGen.refl
  have hback : ReflTransGen Gm t' s' := ht's.trans (ReflTransGen.head (Or.inr hst₀) h0s')
  have h1 := TP s' t' s₀ hs' hback ht'sA
  have h2 : π.Arel V' m s₀ t₀ := SWO_sub_Arel m (hCsub s₀ t₀ hst₀)
  exact hA'm.irrefl t₀ (reflGen_trans_left hA'm.transitive (reflGen_trans hA'm.transitive h0t' h1)
    h2)

/-- Every cover of `A_i(V)` is preserved: `Â_i(V) ⊆ A_i(V')` (the content of Lemma C.1(b) used by
the proof of Theorem 6.6). -/
theorem cov_preserved (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) :
    ∀ i o w, Cov (π.Arel V i) o w → π.Arel V' i o w := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, o₀, w₀, hc₀, hn₀⟩ := hcon
  let S : Set Op := {u | ∃ i o w, π.Viol V V' i o w ∧ π.IsWmin V i o u}
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := exists_wmin (exists_write_of_B2 hV
      (viol_props hV hV' hR (⟨hc₀, hn₀⟩ : π.Viol V V' i₀ o₀ w₀)).1)
    exact ⟨u, i₀, o₀, w₀, ⟨hc₀, hn₀⟩, hu⟩
  obtain ⟨u, ⟨i, o, w, hv, hu⟩, hmin⟩ := (SWO_strictPO hV).swap.wellFounded.has_min S hne
  have hmax : ∀ i' x y u', π.Viol V V' i' x y → π.IsWmin V i' x u' → ¬ π.SWO V u u' :=
    fun i' x y u' hv' hu' => hmin u' ⟨i', x, y, hv', hu'⟩
  by_cases hex : ∃ w', π.Viol V V' i u w'
  · obtain ⟨w', hw'⟩ := hex
    have huu : π.IsWmin V i u u := hu.2.1 ▸ isWmin_self hV hu.1
    exact stepB hV hV' hR hw' huu hmax (fun _ => rfl)
  · exact stepB hV hV' hR hv hu hmax (fun h => absurd h hex)

/-- `A_i(V) ⊆ A_i(V')` for every replay certified for the record of Theorem 6.6. -/
theorem Arel_preserved (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) (i : P) {a b : Op} (h : π.Arel V i a b) :
    π.Arel V' i a b :=
  of_transGen_of_trans (Arel_strictPO hV' i).transitive
    (transGen_mono' (fun x y hxy => cov_preserved hV hV' hR i x y hxy)
      (transGen_cov (Arel_strictPO hV i) h))

/-- **Lemma C.1 (b).** Every replay certified for the record of Theorem 6.6 contains `B_i(V)`. -/
theorem lemma_C_1_b (hV : π.StronglyCausal V) (hV' : π.StronglyCausal V')
    (hR : ∀ i a b, π.rec2 true V i a b → V' i a b) (i : P) {o w : Op}
    (h : π.B2 true V i o w) : V' i o w :=
  Arel_view hV' (Arel_preserved hV hV' hR i (Arel_of_dro h.2.2.1))

/-- **Theorem 6.6.** For views `V` explaining a strongly causally consistent execution, the record
`R_i = Â_i(V) \ (SWO_i(V) ∪ PO ∪ B_i(V))` is a good record of `V` in RnR Model 2 (with
Definition 6.4 read with `w₃ ≠ w₄`, as the paper's proofs use it). -/
theorem theorem_6_6 {ex : Program.Execution Op} (hV : π.SCCExplains ex V) :
    π.IsRecord2 V (π.rec2 true V) ∧ π.Good2 V (π.rec2 true V) := by
  refine ⟨rec2_isRecord2 true V, fun ex' V' hV' hR i => ?_⟩
  have hVi := hV.2.total i
  have hV'i := hV'.2.total i
  funext a b
  apply propext
  constructor
  · rintro ⟨hab, hvar⟩
    refine ⟨?_, hvar⟩
    by_contra hn
    obtain ⟨ha, hb⟩ := hV'i.supp hab
    have hba := hVi.of_not ha hb (hV'i.ne hab) hn
    have := Arel_view hV'.2 (Arel_preserved hV.2 hV'.2 hR i (Arel_of_dro ⟨hba, hvar.symm⟩))
    exact hV'i.asymm hab this
  · rintro ⟨hab, hvar⟩
    exact ⟨Arel_view hV'.2 (Arel_preserved hV.2 hV'.2 hR i (Arel_of_dro ⟨hab, hvar⟩)), hvar⟩

end Program

end Podc.CausalRecordReplay
