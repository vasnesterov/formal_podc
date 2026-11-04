import Papers.PODC2018.CausalRecordReplay.Model

/-!
# Section 5.1: optimal offline record for RnR Model 1 under strong causal consistency

* Definition 5.1 (`SCOi`), Definition 5.2 (`B1`), the record `rec1` of Theorem 5.3:
  `R_i = V̂_i \ (SCO_i(V) ∪ PO ∪ B_i(V))`;
* Lemma A.1 (`lemma_A_1_a`, `lemma_A_1_b`): strong causal order and the `B_i` edges are preserved
  by every replay certified for `R`;
* Theorem 5.3 (`theorem_5_3`): `R` is a good record;
* Theorem 5.4 (`theorem_5_4`): every good record contains `R` (so `R` is the least good record,
  `rec1_least`).
-/

namespace Podc.CausalRecordReplay

open Relation

variable {P Op X : Type*} (π : Program P Op X)

namespace Program

/-- Definition 5.1: `SCO_i(V)` — the strong-causal-order pairs whose second write is not by `i`. -/
def SCOi (V : P → Op → Op → Prop) (i : P) (a b : Op) : Prop := π.SCO V a b ∧ π.proc b ≠ i

/-- Definition 5.2: `B_i(V)` — pairs `(w¹ᵢ, w²ⱼ)` of a write of `i` and a write of `j ≠ i` ordered
this way by `V_i` and by some `V_k`, `k ∉ {i, j}`. -/
def B1 (V : P → Op → Op → Prop) (i : P) (a b : Op) : Prop :=
  π.IsWrite a ∧ π.IsWrite b ∧ π.proc a = i ∧ π.proc b ≠ i ∧ V i a b ∧
    ∃ k, k ≠ i ∧ k ≠ π.proc b ∧ V k a b

/-- The record of Theorem 5.3: `R_i = V̂_i \ (SCO_i(V) ∪ PO ∪ B_i(V))`. -/
def rec1 (V : P → Op → Op → Prop) (i : P) (a b : Op) : Prop :=
  Cov (V i) a b ∧ ¬ π.SCOi V i a b ∧ ¬ π.po a b ∧ ¬ π.B1 V i a b

variable {π}

theorem rec1_isRecord (V : P → Op → Op → Prop) : IsRecord1 V (π.rec1 V) :=
  fun _ _ _ h => h.1.1

variable [Finite Op]

/-- Lemma A.1 (a): every replay certified for `R` preserves the strong causal order. -/
theorem lemma_A_1_a {V V' : P → Op → Op → Prop} (hV : π.StronglyCausal V)
    (hV' : π.StronglyCausal V') (hR : ∀ i a b, π.rec1 V i a b → V' i a b) :
    ∀ a b, π.SCO V a b → π.SCO V' a b := by
  intro a b
  -- well-founded induction on the second write along `SCO(V)` ("a minimal bad write")
  induction b using hV.sco_strictPO.wellFounded.induction generalizing a with
  | _ b ih =>
  intro hab
  set p := π.proc b
  have hT := hV.total p
  have hT' := hV'.total p
  have hbw : π.IsWrite b := hab.2.1
  -- propagate along the covers of `V_p` from `a` to `b`
  have key : ReflGen (V' p) a b ∨ V' p a b := by
    refine chain_induction hT.toStrictPO hab.2.2 (fun y => ReflGen (V' p) a y ∨ V' p a b)
      (Or.inl ReflGen.refl) ?_
    intro x y hax hxy hyb hQ
    rcases hQ with hQ | hQ
    swap
    · exact Or.inr hQ
    have hx : π.Obs p x := (hT.supp hxy.1).1
    have hy : π.Obs p y := (hT.supp hxy.1).2
    by_cases hpo : π.po x y
    · exact Or.inl (ReflGen.single (reflGen_trans_left hT'.toStrictPO.transitive hQ
        (hV'.po p hpo hx hy)))
    by_cases hs : π.SCOi V p x y
    · -- Case 3: `y ≠ b`, and `y` is below `b` in `SCO(V)`, so not bad
      have hyb' : V p y b := by
        rcases hyb with _ | h
        · exact absurd rfl hs.2
        · exact h
      have hyb'' : π.SCO V y b := ⟨hs.1.2.1, hbw, hyb'⟩
      have := ih y hyb'' x hs.1
      exact Or.inl (ReflGen.single (reflGen_trans_left hT'.toStrictPO.transitive hQ
        (hV'.sco p this)))
    by_cases hb : π.B1 V p x y
    · -- Case 4: `x` is a write of `p`, hence `x <_PO b`
      have hxb : V p x b := reflGen_trans_right hT.toStrictPO.transitive hxy.1 hyb
      have hpo' : π.po x b := hV.po_of_view hxb (by rw [hb.2.2.1])
      exact Or.inr (reflGen_trans_left hT'.toStrictPO.transitive hQ
        (hV'.po p hpo' (hT.supp hxb).1 (hT.supp hxb).2))
    · -- Case 1: the edge is recorded
      exact Or.inl (ReflGen.single (reflGen_trans_left hT'.toStrictPO.transitive hQ
        (hR p x y ⟨hxy, hs, hpo, hb⟩)))
  have : V' p a b := key.elim (fun h => reflGen_of_ne h (hT.ne hab.2.2)) id
  exact ⟨hab.1, hab.2.1, this⟩

/-- Lemma A.1 (b): every replay certified for `R` contains each `B_i(V)`. -/
theorem lemma_A_1_b {V V' : P → Op → Op → Prop} (hV : π.StronglyCausal V)
    (hV' : π.StronglyCausal V') (hR : ∀ i a b, π.rec1 V i a b → V' i a b) :
    ∀ i a b, π.B1 V i a b → V' i a b := by
  have hA := lemma_A_1_a hV hV' hR
  intro i a
  -- well-founded induction on the first write along the reverse of `SCO(V)` (a maximal bad write)
  induction a using hV.sco_strictPO.swap.wellFounded.induction generalizing i with
  | _ a ih =>
  intro b hab
  obtain ⟨haw, hbw, hai, hbi, -, k, hki, hkb, hk⟩ := hab
  subst hai
  have hTk := hV.total k
  have hTk' := hV'.total k
  -- show `a <_{V'_k} b`
  have hk' : V' k a b := by
    refine reflGen_of_ne ?_ (hTk.ne hk)
    refine chain_induction hTk.toStrictPO hk (fun y => ReflGen (V' k) a y) ReflGen.refl ?_
    intro x y hax hxy hyb hQ
    have hx : π.Obs k x := (hTk.supp hxy.1).1
    have hy : π.Obs k y := (hTk.supp hxy.1).2
    refine ReflGen.single (reflGen_trans_left hTk'.toStrictPO.transitive hQ ?_)
    by_cases hpo : π.po x y
    · exact hV'.po k hpo hx hy
    by_cases hs : π.SCOi V k x y
    · exact hV'.sco k (hA _ _ hs.1)
    by_cases hb : π.B1 V k x y
    · -- Case 4: `x` is a write of `k ≠ proc a`, so `x ≠ a` and `(a, x) ∈ SCO(V)`
      have hxa : x ≠ a := by
        rintro rfl; exact hki hb.2.2.1.symm
      have hax' : V k a x := by
        rcases hax with _ | h
        · exact absurd rfl hxa
        · exact h
      have hsco : π.SCO V a x := ⟨haw, hb.1, by rw [hb.2.2.1]; exact hax'⟩
      exact ih x hsco k y hb
    · exact hR k x y ⟨hxy, hs, hpo, hb⟩
  -- if `b <_{V'_{proc a}} a` then `(b, a) ∈ SCO(V')`, contradicting `a <_{V'_k} b`
  have hT' := hV'.total (π.proc a)
  by_contra hn
  have hba : V' (π.proc a) b a :=
    hT'.of_not (π.write_obs haw _) (π.write_obs hbw _) (fun h => hbi (h ▸ rfl)) hn
  have hsco : π.SCO V' b a := ⟨hbw, haw, hba⟩
  exact hTk'.asymm hk' (hV'.sco k hsco)

/-- The core of Theorem 5.3: a strongly causal `V'` respecting `R` equals `V`. -/
theorem rec1_good_core {V V' : P → Op → Op → Prop} (hV : π.StronglyCausal V)
    (hV' : π.StronglyCausal V') (hR : ∀ i a b, π.rec1 V i a b → V' i a b) : V' = V := by
  have hA := lemma_A_1_a hV hV' hR
  have hB := lemma_A_1_b hV hV' hR
  funext i
  have hT := hV.total i
  have hT' := hV'.total i
  refine (hT.eq_of_le hT' fun a b hab => ?_).symm
  refine reflGen_of_ne ?_ (hT.ne hab)
  refine chain_induction hT.toStrictPO hab (fun y => ReflGen (V' i) a y) ReflGen.refl
    (fun x y _ hxy _ hQ => ?_)
  have hx : π.Obs i x := (hT.supp hxy.1).1
  have hy : π.Obs i y := (hT.supp hxy.1).2
  refine ReflGen.single (reflGen_trans_left hT'.toStrictPO.transitive hQ ?_)
  by_cases hpo : π.po x y
  · exact hV'.po i hpo hx hy
  by_cases hs : π.SCOi V i x y
  · exact hV'.sco i (hA _ _ hs.1)
  by_cases hb : π.B1 V i x y
  · exact hB i x y hb
  · exact hR i x y ⟨hxy, hs, hpo, hb⟩

/-- **Theorem 5.3.** For views `V` explaining a strongly causally consistent execution, the record
`R_i = V̂_i \ (SCO_i(V) ∪ PO ∪ B_i(V))` is a good record of `V` (RnR Model 1). -/
theorem theorem_5_3 {ex : Program.Execution Op} {V : P → Op → Op → Prop}
    (hV : π.SCCExplains ex V) : π.Good1 V (π.rec1 V) :=
  fun _ _ hV' hR => rec1_good_core hV.2 hV'.2 hR

/-- Swapping a cover pair `(a, b)` of a strict total order. -/
def swapPair (r : Op → Op → Prop) (a b : Op) (x y : Op) : Prop :=
  (r x y ∧ ¬ (x = a ∧ y = b)) ∨ (x = b ∧ y = a)

omit [Finite Op] in
theorem swapPair_total {S : Op → Prop} {r : Op → Op → Prop} (hr : IsStrictTotalOn S r) {a b : Op}
    (hab : Cov r a b) : IsStrictTotalOn S (swapPair r a b) := by
  have hab' := hab.1
  have hne : a ≠ b := hr.ne hab'
  have hSa := (hr.supp hab').1
  have hSb := (hr.supp hab').2
  refine ⟨fun {x y} h => ?_, fun x h => ?_, fun {x y z} hxy hyz => ?_, fun {x y} hx hy hxy => ?_⟩
  · rcases h with ⟨h, -⟩ | ⟨rfl, rfl⟩
    · exact hr.supp h
    · exact ⟨hSb, hSa⟩
  · rcases h with ⟨h, -⟩ | ⟨rfl, h⟩
    · exact hr.irrefl x h
    · exact hne h.symm
  · rcases hxy with ⟨hxy, nxy⟩ | ⟨ex, ey⟩ <;> rcases hyz with ⟨hyz, nyz⟩ | ⟨ey', ez⟩
    · refine Or.inl ⟨hr.trans hxy hyz, ?_⟩
      rintro ⟨rfl, rfl⟩
      exact hab.2 y hxy hyz
    · subst y z
      have hxa : x ≠ a := fun h => nxy ⟨h, rfl⟩
      have hxa' : r x a := by
        rcases hr.total (hr.supp hxy).1 hSa hxa with h | h
        · exact h
        · exact absurd hxy (hab.2 x h)
      exact Or.inl ⟨hxa', fun h => hxa h.1⟩
    · subst x y
      have hzb : z ≠ b := fun h => nyz ⟨rfl, h⟩
      have hbz : r b z := by
        rcases hr.total hSb (hr.supp hyz).2 (Ne.symm hzb) with h | h
        · exact h
        · exact absurd h (hab.2 z hyz)
      exact Or.inl ⟨hbz, fun h => hne h.1.symm⟩
    · exact absurd (ey.symm.trans ey') hne
  · rcases hr.total hx hy hxy with h | h
    · by_cases hh : x = a ∧ y = b
      · obtain ⟨rfl, rfl⟩ := hh
        exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inl ⟨h, hh⟩)
    · by_cases hh : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := hh
        exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨h, hh⟩)

/-- **Theorem 5.4.** For views `V` explaining a strongly causally consistent execution, every good
record `R` of `V` contains every edge of `V̂_i \ (PO ∪ SCO_i(V) ∪ B_i(V))`, for every process `i`. -/
theorem theorem_5_4 {ex : Program.Execution Op} {V : P → Op → Op → Prop}
    (hV : π.SCCExplains ex V) {R : P → Op → Op → Prop} (hR : IsRecord1 V R)
    (hgood : π.Good1 V R) {i : P} {o₁ o₂ : Op} (h₁ : π.Obs i o₁) (h₂ : π.Obs i o₂)
    (hcov : Cov (V i) o₁ o₂) (hpo : ¬ π.po o₁ o₂) (hs : ¬ π.SCOi V i o₁ o₂)
    (hb : ¬ π.B1 V i o₁ o₂) : R i o₁ o₂ := by
  classical
  have hV2 := hV.2
  by_contra hnR
  let V' : P → Op → Op → Prop := Function.update V i (swapPair (V i) o₁ o₂)
  have hVi : V' i = swapPair (V i) o₁ o₂ := Function.update_self _ _ _
  have hVj : ∀ j, j ≠ i → V' j = V j := fun j hj => Function.update_of_ne hj _ _
  have hTi := hV2.total i
  have hne : o₁ ≠ o₂ := hTi.ne hcov.1
  have hT' : ∀ j, IsStrictTotalOn (π.Obs j) (V' j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hVi]; exact swapPair_total hTi hcov
    · rw [hVj j hj]; exact hV2.total j
  -- `V'` agrees with `V` except on the swapped pair
  have hV'of : ∀ j x y, V j x y → ¬ (j = i ∧ x = o₁ ∧ y = o₂) → V' j x y := by
    intro j x y hxy hn
    by_cases hj : j = i
    · subst hj; rw [hVi]; exact Or.inl ⟨hxy, fun h => hn ⟨rfl, h⟩⟩
    · rw [hVj j hj]; exact hxy
  have hSC : π.StronglyCausal V' := by
    rw [stronglyCausal_iff]
    refine fun j => ⟨hT' j, fun x y hxy => ?_, fun x y hxy => ?_⟩
    · obtain ⟨hxw, hyw, hxy⟩ := hxy
      by_cases hyi : π.proc y = i
      · rw [hyi, hVi] at hxy
        rcases hxy with ⟨hxy, nxy⟩ | ⟨rfl, rfl⟩
        · refine hV'of j x y (hV2.sco j ⟨hxw, hyw, hyi ▸ hxy⟩) fun h => nxy ⟨h.2.1, h.2.2⟩
        · -- the new pair `(o₂, o₁)` with `o₁` a write of `i`
          have hq : π.proc x ≠ i := by
            intro hq
            exact hpo (hV2.po_of_view hcov.1 (hq.trans hyi.symm).symm)
          by_cases hj : j = i
          · subst hj; rw [hVi]; exact Or.inr ⟨rfl, rfl⟩
          rw [hVj j hj]
          have hnot : ¬ V j y x := by
            intro h
            by_cases hjq : j = π.proc x
            · exact hs ⟨⟨hyw, hxw, hjq ▸ h⟩, hq⟩
            · exact hb ⟨hyw, hxw, hyi, hq, hcov.1, j, hj, hjq, h⟩
          exact (hV2.total j).of_not (π.write_obs hyw j) (π.write_obs hxw j) hne hnot
      · rw [hVj _ hyi] at hxy
        refine hV'of j x y (hV2.sco j ⟨hxw, hyw, hxy⟩) ?_
        rintro ⟨rfl, rfl, rfl⟩
        exact hs ⟨⟨hxw, hyw, hxy⟩, hyi⟩
    · refine hV'of j x y (hV2.po j hxy.1 hxy.2.1 hxy.2.2) ?_
      rintro ⟨-, rfl, rfl⟩
      exact hpo hxy.1
  obtain ⟨ex', hex'⟩ := π.exists_explains V' hT'
  have hresp : ∀ j x y, R j x y → V' j x y := by
    intro j x y hxy
    refine hV'of j x y (hR j x y hxy) ?_
    rintro ⟨rfl, rfl, rfl⟩
    exact hnR hxy
  have heq := hgood ex' V' ⟨hex', hSC⟩ hresp
  have h21 : V' i o₂ o₁ := by rw [hVi]; exact Or.inr ⟨rfl, rfl⟩
  rw [heq] at h21
  exact hTi.asymm hcov.1 h21

/-- Theorems 5.3 and 5.4 together: `R_i = V̂_i \ (SCO_i(V) ∪ PO ∪ B_i(V))` is the least good record:
it is good and contained in every good record. -/
theorem rec1_least {ex : Program.Execution Op} {V : P → Op → Op → Prop}
    (hV : π.SCCExplains ex V) :
    π.Good1 V (π.rec1 V) ∧ ∀ R, IsRecord1 V R → π.Good1 V R → ∀ i a b, π.rec1 V i a b → R i a b :=
  ⟨theorem_5_3 hV, fun _ hR hg i _ _ h =>
    theorem_5_4 hV hR hg ((hV.2.total i).supp h.1.1).1 ((hV.2.total i).supp h.1.1).2 h.1 h.2.2.1
      h.2.1 h.2.2.2⟩

end Program

end Podc.CausalRecordReplay
