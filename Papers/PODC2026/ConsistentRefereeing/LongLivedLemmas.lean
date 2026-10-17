import Papers.PODC2026.ConsistentRefereeing.LongLivedSteps
import Cslib.Foundations.Data.Finset.Card
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Valencies of closed and supervalent executions (Lemmas 20–22, 27, 28 of [ACE26])

We treat Sections 5.1 (read/write registers, `n ≥ 3`) and 5.2 (`w`-window registers and
test&set objects, `n ≥ 4`, `3w ≤ n`) uniformly: the hypothesis `LLCtx.Hyp X w` says that every
base object is window-like with window `w` (registers are window-like with window `1`), or is
test&set-like and there are at least `4` processes; `1 ≤ w`, `n ≥ 3` and `3w ≤ n`.

* `pair` — the case analysis of Lemma 20 / Lemma 27 for two competitors `q`, `q'` with `αq`
  closed and `W(αq) ∩ W(αq') = ∅`: both must be poised to write to the same window register;
* `window_final` — the "all competitors write to `R`" case of Lemmas 27 and 28;
* `lemma20` — Lemma 20 (for window `w ≤ 1`, e.g. registers);
* `lemma27` (= Lemma 21 for registers) — closed executions have singleton valency;
* `lemma28` (= Lemma 22 for registers) — supervalent executions have empty valency.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Referee

open Impl

namespace LLCtx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] [Fintype P]
  (X : LLCtx P ι L B)

/-- Hypotheses on the base objects and the number of processes shared by Theorems 25 and 30. -/
structure Hyp (X : LLCtx P ι L B) (w : ℕ) : Prop where
  obj : ∀ i, (B i).WindowLike w ∨ ((B i).TASLike ∧ 4 ≤ Fintype.card P)
  w1 : 1 ≤ w
  card3 : 3 ≤ Fintype.card P
  cardw : 3 * w ≤ Fintype.card P

variable {X}

/-! ### Choosing competitors -/

lemma exists_comp (hn : 2 ≤ Fintype.card P) : ∃ c, c ≠ X.ref :=
  Fintype.exists_ne_of_one_lt_card hn X.ref

lemma exists_comp_ne (hn : 3 ≤ Fintype.card P) (q : P) : ∃ c, c ≠ X.ref ∧ c ≠ q :=
  Fintype.exists_ne_ne_of_two_lt_card hn X.ref q

lemma exists_comp_ne₂ (hn : 4 ≤ Fintype.card P) (q q' : P) :
    ∃ c, c ≠ X.ref ∧ c ≠ q ∧ c ≠ q' := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {X.ref, q, q'})
    (t := Finset.univ) (Finset.card_le_three.trans_lt (by rw [Finset.card_univ]; exact hn))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc⟩

/-- Three disjoint lists of `m` competitors avoiding `q` and `q'`. -/
lemma exists_lists {m : ℕ} (hn : 3 * m + 3 ≤ Fintype.card P) (q q' : P) :
    ∃ l₁ l₂ l₃ : List P, l₁.length = m ∧ l₂.length = m ∧ l₃.length = m ∧
      (l₁ ++ l₂ ++ l₃).Nodup ∧ ∀ x ∈ l₁ ++ l₂ ++ l₃, x ≠ X.ref ∧ x ≠ q ∧ x ≠ q' := by
  have hc := (Finset.card_filter_notMem_univ ({X.ref, q, q'} : Finset P)).ge
  have h2 := Finset.card_le_three (a := X.ref) (b := q) (c := q')
  set S := Finset.univ.filter (fun x => x ∉ ({X.ref, q, q'} : Finset P)) with hS
  set Lst := S.toList with hL
  have hlen : 3 * m ≤ Lst.length := by rw [hL, Finset.length_toList]; omega
  refine ⟨Lst.take m, (Lst.drop m).take m, (Lst.drop (m + m)).take m, ?_, ?_, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · simp; omega
  · have : Lst.take m ++ (Lst.drop m).take m ++ (Lst.drop (m + m)).take m =
        Lst.take (m + m + m) := by
      rw [List.take_add, List.take_add]
    rw [this]
    exact (List.take_sublist _ _).nodup (Finset.nodup_toList S)
  · intro x hx
    have : x ∈ Lst := by
      have e : Lst.take m ++ (Lst.drop m).take m ++ (Lst.drop (m + m)).take m =
          Lst.take (m + m + m) := by rw [List.take_add, List.take_add]
      rw [e] at hx; exact List.mem_of_mem_take hx
    rw [hL, Finset.mem_toList, hS] at this
    simpa using this

/-! ### Small helpers -/

lemma W_disj_contra {A B' : Set ℕ} (h : Disjoint A B') {x : ℕ} (h1 : x ∈ A) (h2 : x ∈ B') :
    False := Set.disjoint_left.1 h h1 h2

lemma Good.pend_ref_ext {β : List (LLabel P)} (hβ : X.Good β)
    (hp : (X.cfg β).pend X.ref ≠ none) {σ : List P} (hσ : X.Comp σ) :
    (X.cfg (X.ext β σ)).pend X.ref ≠ none := by
  rw [(hβ.ext_other hσ.not_mem).2]; exact hp

/-- If `x ∈ W(β)` and `decide()` is not in `h β`, then `x ∈ W(βq)` for some competitor `q`. -/
lemma mem_W_cons {β : List (LLabel P)} {x : ℕ} (hx : x ∈ X.W β) (hnd : ¬ X.DecIn β) :
    ∃ q, q ≠ X.ref ∧ x ∈ X.W (X.ext β [q]) := by
  obtain ⟨τ, hτ, hd⟩ := hx
  cases τ with
  | nil => exact absurd ⟨x, by simpa using hd⟩ hnd
  | cons q τ =>
    refine ⟨q, hτ q List.mem_cons_self, τ, fun p hp => hτ p (List.mem_cons_of_mem _ hp), ?_⟩
    rw [← ext_append]; simpa using hd

lemma W_cons_subset (β : List (LLabel P)) (q : P) (σ : List P) (hσ : X.Comp σ) :
    X.W (X.ext β (q :: σ)) ⊆ X.W (X.ext β [q]) := by
  have : q :: σ = [q] ++ σ := rfl
  rw [this, ext_append]; exact W_ext_subset _ hσ

lemma comp_cons {q : P} {σ : List P} (hq : q ≠ X.ref) (hσ : X.Comp σ) : X.Comp (q :: σ) := by
  intro p hp; rcases List.mem_cons.1 hp with rfl | hp
  · exact hq
  · exact hσ p hp

variable {w : ℕ}

/-! ### The pair analysis (Lemmas 20 and 27) -/

/-- **Case analysis of Lemmas 20 and 27 of [ACE26].** Let `βq` be closed, `decide` pending, and
`W(βq) ∩ W(βq') = ∅`. Then `q` and `q'` are poised to apply non-read-only primitives to the same
base object `R`, which is window-like (the cases "`q` or `q'` reads", "distinct objects" and
"same test&set object" contradict Lemma 17). -/
theorem pair (hH : X.Hyp w) {β : List (LLabel P)} (hβ : X.Good β)
    (hpend : (X.cfg β).pend X.ref ≠ none) {q q' : P} (hq : q ≠ X.ref) (hq' : q' ≠ X.ref)
    (hqq : q ≠ q') (hcl : X.Closed (X.ext β [q]))
    (hdis : Disjoint (X.W (X.ext β [q])) (X.W (X.ext β [q']))) :
    ∃ R, X.Writes (X.cfg β) q R ∧ X.Writes (X.cfg β) q' R ∧ (B R).WindowLike w := by
  have hpq : (X.cfg (X.ext β [q])).pend X.ref ≠ none := hβ.pend_ref_ext hpend (comp_singleton hq)
  rcases quiet_or_writes (X := X) (X.cfg β) q' with hq'q | ⟨R', hR'⟩
  · -- `q'` reads: `βq` and `βq'q` are indistinguishable to the referee and `q`
    have S := ((hβ.sim_quiet hq' hq'q).ext (σ := [q]) (fun p hp => by
      simp at hp; subst hp; exact hqq)).symm
    obtain ⟨x, hx1, hx2⟩ := X.lemma17 (hβ.ext _) S.good' hcl hpq hq (Q := {x | x ≠ q'})
      hqq (Ne.symm hq') S.agree
    rw [← ext_append] at hx2
    exact (W_disj_contra hdis hx1 (W_cons_subset β q' [q] (comp_singleton hq) hx2)).elim
  rcases quiet_or_writes (X := X) (X.cfg β) q with hqq' | ⟨R, hR⟩
  · -- `q` reads: `βq'` and `βqq'` are indistinguishable to the referee and `q'`
    have S := (hβ.sim_quiet hq hqq').ext (σ := [q']) (fun p hp => by
      simp at hp; subst hp; exact Ne.symm hqq)
    have hcl' : X.Closed (X.ext (X.ext β [q]) [q']) := hcl.ext (hβ.ext _) (comp_singleton hq')
    obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl'
      (hβ.pend_ref_ext hpend (comp_singleton hq) |> fun h =>
        ((hβ.ext _).pend_ref_ext h (comp_singleton hq'))) hq' (Q := {x | x ≠ q})
      (Ne.symm hqq) (Ne.symm hq) S.agree
    exact (W_disj_contra hdis (W_ext_subset _ (comp_singleton hq') hx1) hx2).elim
  by_cases hRR : R = R'
  · subst hRR
    rcases hH.obj R with hW | ⟨hT, h4⟩
    · exact ⟨R, hR, hR', hW⟩
    · -- same test&set object: `βq` and `βq'` are indistinguishable to the referee and `q''`
      obtain ⟨q'', h1, h2, h3⟩ := exists_comp_ne₂ (X := X) h4 q q'
      have S := hβ.sim_tas hT hR.accesses hR'.accesses hq hq'
      obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl hpq h1
        (Q := {x | x ≠ q ∧ x ≠ q'}) ⟨h2, h3⟩ ⟨Ne.symm hq, Ne.symm hq'⟩ S.agree
      exact (W_disj_contra hdis hx1 hx2).elim
  · -- distinct objects: the steps commute
    have S := hβ.sim_swap hqq (nonConflict_of_ne hR.accesses hR'.accesses hRR)
    have hcl' : X.Closed (X.ext β [q, q']) := by
      have : X.ext β [q, q'] = X.ext (X.ext β [q]) [q'] := by rw [← ext_append]; rfl
      rw [this]; exact hcl.ext (hβ.ext _) (comp_singleton hq')
    obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl'
      (hβ.pend_ref_ext hpend (comp_cons hq (comp_singleton hq'))) hq (Q := Set.univ)
      trivial trivial S.agree
    exact (W_disj_contra hdis (W_cons_subset β q [q'] (comp_singleton hq') hx1)
      (W_cons_subset β q' [q] (comp_singleton hq) hx2)).elim

/-- **The window case of Lemmas 27 and 28 of [ACE26].** If all competitors are poised to write
to the window register `R`, `βq` is closed and `W(βq) ∩ W(βq') = ∅`, then `βqγ` and `βq'qγ`
(`γ`: `w - 1` other competitors) are indistinguishable to the referee and `q` — contradicting
Lemma 17. -/
theorem window_final (hH : X.Hyp w) {β : List (LLabel P)} (hβ : X.Good β)
    (hpend : (X.cfg β).pend X.ref ≠ none) {q q' : P} (hq : q ≠ X.ref) (hq' : q' ≠ X.ref)
    (hqq : q ≠ q') (hcl : X.Closed (X.ext β [q]))
    (hdis : Disjoint (X.W (X.ext β [q])) (X.W (X.ext β [q']))) {R : ι}
    (hW : (B R).WindowLike w) (hall : ∀ c, c ≠ X.ref → X.Writes (X.cfg β) c R) : False := by
  obtain ⟨l, _, _, hl, -, -, hnd, hmem⟩ := exists_lists (X := X) (m := w - 1)
    (by have := hH.cardw; have := hH.w1; omega) q q'
  have hlnd : l.Nodup := (List.nodup_append.1 (List.nodup_append.1 hnd).1).1
  have hlm : ∀ x ∈ l, x ≠ X.ref ∧ x ≠ q ∧ x ≠ q' := fun x hx => hmem x (by simp [hx])
  have hlc : X.Comp l := fun x hx => (hlm x hx).1
  set ws := q :: l with hws
  have hwsnd : ws.Nodup := List.nodup_cons.2 ⟨fun h => (hlm q h).2.1 rfl, hlnd⟩
  have hwsq' : ∀ a ∈ ws, a ≠ q' := by
    intro a ha; rcases List.mem_cons.1 ha with rfl | ha
    · exact hqq
    · exact (hlm a ha).2.2
  have hg1 := hβ.ext [q']
  have hstate : ∀ x, x ≠ q' → (X.cfg β).loc x = (X.cfg (X.ext β [q'])).loc x ∧
      (X.cfg β).pend x = (X.cfg (X.ext β [q'])).pend x := fun x hx => by
    have := hβ.ext_other (σ := [q']) (by simpa using hx); exact ⟨this.1.symm, this.2.symm⟩
  have S := hβ.sim_window hg1 hW hwsnd (List.cons_ne_nil _ _)
    (by simp [hws, hl]; have := hH.w1; omega) (Q := {x | x ≠ q'})
    (fun x hx => hstate x hx) (fun a ha => hstate a (hwsq' a ha))
    (fun j hj => by
      rw [ext_singleton, hβ.mem_ext1 (fun h => hj (Accesses.unique h (hall q' hq').accesses))])
    (fun a ha => hall a (by rcases List.mem_cons.1 ha with rfl | ha
                            · exact hq
                            · exact (hlm a ha).1))
    (by rw [ext_singleton, opsOf_ext1_of_ne (Ne.symm hq')])
  have hcl' : X.Closed (X.ext β ws) := by
    rw [hws, ext_cons, ← ext_singleton]; exact hcl.ext (hβ.ext _) hlc
  obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl'
    (hβ.pend_ref_ext hpend (comp_cons hq hlc)) hq (Q := {x | x ≠ q'}) hqq (Ne.symm hq')
    S.agree
  exact W_disj_contra hdis (W_cons_subset β q l hlc hx1) (W_ext_subset _ (comp_cons hq hlc) hx2)

/-- **Lemma 20 of [ACE26]** (for window `w ≤ 1`, in particular read/write registers, `n ≥ 3`).
If `αq` is closed, then `W(αq) ∩ W(αq') ≠ ∅` for every other competitor `q'`. -/
theorem lemma20 (hH : X.Hyp w) (hw : w ≤ 1) {α : List (LLabel P)} (hα : X.Good α)
    {q q' : P} (hq : q ≠ X.ref) (hq' : q' ≠ X.ref)
    (hqq : q ≠ q') (hcl : X.Closed (X.ext α [q])) :
    ∃ x, x ∈ X.W (X.ext α [q]) ∧ x ∈ X.W (X.ext α [q']) := by
  by_cases hc : respsOf α X.ref ≠ []
  · -- `decide` has returned in `α`: both valencies are its output
    obtain ⟨x, -, hx⟩ := hα.dec_of_completed hc
    refine ⟨x, ?_, ?_⟩
    · rw [W_eq_of_dec (hα.ext _) (hx.mono (hα.ext _) (prefix_ext _ _))]; rfl
    · rw [W_eq_of_dec (hα.ext _) (hx.mono (hα.ext _) (prefix_ext _ _))]; rfl
  push Not at hc
  have hpend : (X.cfg α).pend X.ref ≠ none := by
    refine hα.pend_ref_ne_none_iff.2 ⟨?_, hc⟩
    have := hcl.invoked (hα.ext _) hq
    rwa [opsOf_ext_of_not_mem (by simpa using Ne.symm hq)] at this
  by_contra hno
  have hdis : Disjoint (X.W (X.ext α [q])) (X.W (X.ext α [q'])) :=
    Set.disjoint_left.2 fun x h1 h2 => hno ⟨x, h1, h2⟩
  obtain ⟨R, hR, hR', hW⟩ := X.pair hH hα hpend hq hq' hqq hcl hdis
  -- with window `≤ 1`, the write of `q` erases the write of `q'`
  have hg1 := hα.ext [q']
  have S := hα.sim_window hg1 hW (ws := [q]) (by simp) (by simp) (by simp; omega)
    (Q := {x | x ≠ q'})
    (fun x hx => by have := hα.ext_other (σ := [q']) (by simpa using hx)
                    exact ⟨this.1.symm, this.2.symm⟩)
    (fun a ha => by simp at ha; subst ha
                    have := hα.ext_other (σ := [q']) (by simpa using hqq)
                    exact ⟨this.1.symm, this.2.symm⟩)
    (fun j hj => by
      rw [ext_singleton, hα.mem_ext1 (fun h => hj (Accesses.unique h hR'.accesses))])
    (fun a ha => by simp at ha; subst ha; exact hR)
    (by rw [ext_singleton, opsOf_ext1_of_ne (Ne.symm hq')])
  obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl
    (hα.pend_ref_ext hpend (comp_singleton hq)) hq (Q := {x | x ≠ q'}) hqq (Ne.symm hq')
    S.agree
  exact hno ⟨x, hx1, W_ext_subset _ (comp_singleton hq) hx2⟩

/-! ### Lemmas 21/27 and 22/28 -/

/-- **Lemma 27 of [ACE26]** (Lemma 21 for registers): if `α` is closed, `|W(α)| = 1`. -/
theorem lemma27 (hH : X.Hyp w) : X.Sing := by
  intro α hα hcl
  obtain ⟨c₀, hc₀⟩ := exists_comp (X := X) (by have := hH.card3; omega)
  obtain ⟨x, hx⟩ := hcl.nonempty hc₀
  by_contra hno
  push Not at hno
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ X.W α, y ≠ x := by
    by_contra h; push Not at h
    exact hno x (Set.eq_singleton_iff_unique_mem.2 ⟨hx, h⟩)
  set Φ : List P → Prop := fun σ => ∃ a b, a ≠ b ∧ a ∈ X.W (X.ext α σ) ∧ b ∈ X.W (X.ext α σ)
    with hΦ
  obtain ⟨σ, hσ, hΦσ, hcrit⟩ := X.exists_critical Φ ⟨y, x, hyx, by simpa using hy,
    by simpa using hx⟩ (by
      intro s hs hall
      obtain ⟨n, z, hz⟩ := hcl s hs
      obtain ⟨a, b, hab, ha, hb⟩ := hall n
      rw [W_eq_of_dec (hα.ext _) hz] at ha hb
      exact hab (ha.trans hb.symm))
  set β := X.ext α σ with hβ_def
  have hβ : X.Good β := hα.ext σ
  have hclβ : X.Closed β := hcl.ext hα hσ
  obtain ⟨a, b, hab, ha, hb⟩ := hΦσ
  have hnd : ¬ X.DecIn β := by
    rintro ⟨z, hz⟩
    rw [W_eq_of_dec hβ hz] at ha hb
    exact hab (ha.trans hb.symm)
  have hpend := hclβ.pend hβ hnd hc₀
  -- every `βq` is closed with a singleton valency
  have hsing : ∀ q, q ≠ X.ref → X.Closed (X.ext β [q]) ∧ ∃ z, X.W (X.ext β [q]) = {z} := by
    intro q hq
    have hclq := hclβ.ext hβ (comp_singleton hq)
    refine ⟨hclq, ?_⟩
    obtain ⟨z, hz⟩ := hclq.nonempty hq
    refine ⟨z, Set.eq_singleton_iff_unique_mem.2 ⟨hz, fun z' hz' => ?_⟩⟩
    by_contra hne
    apply hcrit q hq
    rw [hβ_def, ← ext_append] at hz hz'
    exact ⟨z', z, hne, hz', hz⟩
  choose! hclq z hz using hsing
  have hval : ∀ v ∈ X.W β, ∃ q, q ≠ X.ref ∧ z q = v := by
    intro v hv
    obtain ⟨q, hq, hvq⟩ := mem_W_cons hv hnd
    rw [hz q hq] at hvq
    exact ⟨q, hq, hvq.symm⟩
  obtain ⟨q₁, hq₁, rfl⟩ := hval a ha
  obtain ⟨q₂, hq₂, rfl⟩ := hval b hb
  have hq12 : q₁ ≠ q₂ := fun h => hab (by rw [h])
  have hdisj : ∀ q q', q ≠ X.ref → q' ≠ X.ref → z q ≠ z q' →
      Disjoint (X.W (X.ext β [q])) (X.W (X.ext β [q'])) := by
    intro q q' hq hq' hne
    rw [hz q hq, hz q' hq', Set.disjoint_singleton]; exact hne
  obtain ⟨R, hR1, hR2, hW⟩ := X.pair hH hβ hpend hq₁ hq₂ hq12 (hclq q₁ hq₁)
    (hdisj q₁ q₂ hq₁ hq₂ hab)
  have hall : ∀ c, c ≠ X.ref → X.Writes (X.cfg β) c R := by
    intro c hc
    by_cases h1 : z c = z q₁
    · have hne : z q₂ ≠ z c := by rw [h1]; exact Ne.symm hab
      by_cases hcq : c = q₂
      · rw [hcq]; exact hR2
      · obtain ⟨R', h1', h2', -⟩ := X.pair hH hβ hpend hq₂ hc (Ne.symm hcq) (hclq q₂ hq₂)
          (hdisj q₂ c hq₂ hc hne)
        rwa [Accesses.unique hR2.accesses h1'.accesses]
    · by_cases hcq : c = q₁
      · rw [hcq]; exact hR1
      · obtain ⟨R', h1', h2', -⟩ := X.pair hH hβ hpend hq₁ hc (Ne.symm hcq) (hclq q₁ hq₁)
          (hdisj q₁ c hq₁ hc (Ne.symm h1))
        rwa [Accesses.unique hR1.accesses h1'.accesses]
  exact X.window_final hH hβ hpend hq₁ hq₂ hq12 (hclq q₁ hq₁) (hdisj q₁ q₂ hq₁ hq₂ hab) hW hall

/-- **Lemma 28 of [ACE26]** (Lemma 22 for registers): if `α` is supervalent, `W(α) = ∅`. -/
theorem lemma28 (hH : X.Hyp w) {α : List (LLabel P)} (hα : X.Good α) (hsup : ¬ X.Closed α) :
    X.NoDec α := by
  rw [noDec_iff]
  intro x hx
  obtain ⟨c₀, hc₀⟩ := exists_comp (X := X) (by have := hH.card3; omega)
  set Φ : List P → Prop := fun σ => ¬ X.Closed (X.ext α σ) ∧ x ∈ X.W (X.ext α σ) with hΦ
  obtain ⟨σ, hσ, ⟨hsupβ, hxβ⟩, hcrit⟩ := X.exists_critical Φ ⟨by simpa using hsup,
    by simpa using hx⟩ (by
      intro s hs hall
      obtain ⟨c', hc'⟩ := exists_infinitely_often s
      have hc'r : c' ≠ X.ref := by obtain ⟨m, -, hm⟩ := hc' 0; rw [← hm]; exact hs m
      obtain ⟨n, hn⟩ := X.resps_unbounded hα hs hc' x
      have hv : x < (respsOf (X.ext α (pre s n)) c').length := by
        rw [ext_eq_append, respsOf_append, List.length_append]; omega
      obtain ⟨h1, h2⟩ := hall n
      exact not_mem_W_of_resps (hα.ext _) (not_decIn_of_super h1) hc'r hv [] (by simpa using h2))
  set β := X.ext α σ with hβ_def
  have hβ : X.Good β := hα.ext σ
  have hnd : ¬ X.DecIn β := not_decIn_of_super hsupβ
  have hcritβ : ∀ q, q ≠ X.ref → x ∈ X.W (X.ext β [q]) → X.Closed (X.ext β [q]) := by
    intro q hq hxq
    by_contra hsq
    apply hcrit q hq
    rw [hβ_def, ← ext_append] at hsq hxq
    exact ⟨hsq, hxq⟩
  obtain ⟨q', hq', hsq'⟩ := exists_super_ext1 hsupβ
  have hxq' : x ∉ X.W (X.ext β [q']) := fun h => hsq' (hcritβ q' hq' h)
  obtain ⟨q, hq, hxq⟩ := mem_W_cons hxβ hnd
  have hclq := hcritβ q hq hxq
  have hWq : X.W (X.ext β [q]) = {x} := by
    obtain ⟨z, hz⟩ := X.lemma27 hH _ (hβ.ext _) hclq
    rw [hz] at hxq ⊢; simp only [Set.mem_singleton_iff] at hxq; rw [hxq]
  have hqq : q ≠ q' := fun h => hsq' (h ▸ hclq)
  have hpend : (X.cfg β).pend X.ref ≠ none := by
    apply hβ.pend_ref_ne_none_iff.2 ⟨?_, hβ.resps_ref_eq_nil hnd⟩
    have := hclq.invoked (hβ.ext _) hq
    rwa [opsOf_ext_of_not_mem (by simpa using Ne.symm hq)] at this
  have hdis : Disjoint (X.W (X.ext β [q])) (X.W (X.ext β [q'])) := by
    rw [hWq, Set.disjoint_singleton_left]; exact hxq'
  obtain ⟨R, hR1, hR2, hW⟩ := X.pair hH hβ hpend hq hq' hqq hclq hdis
  have hall : ∀ c, c ≠ X.ref → X.Writes (X.cfg β) c R := by
    intro c hc
    by_cases hcq : c = q
    · rw [hcq]; exact hR1
    by_cases hcq' : c = q'
    · rw [hcq']; exact hR2
    by_cases hxc : x ∈ X.W (X.ext β [c])
    · have hclc := hcritβ c hc hxc
      have hWc : X.W (X.ext β [c]) = {x} := by
        obtain ⟨z, hz⟩ := X.lemma27 hH _ (hβ.ext _) hclc
        rw [hz] at hxc ⊢; simp only [Set.mem_singleton_iff] at hxc; rw [hxc]
      obtain ⟨R', h1', h2', -⟩ := X.pair hH hβ hpend hc hq' hcq' hclc
        (by rw [hWc, Set.disjoint_singleton_left]; exact hxq')
      rwa [Accesses.unique hR2.accesses h2'.accesses]
    · obtain ⟨R', h1', h2', -⟩ := X.pair hH hβ hpend hq hc (Ne.symm hcq) hclq
        (by rw [hWq, Set.disjoint_singleton_left]; exact hxc)
      rwa [Accesses.unique hR1.accesses h1'.accesses]
  exact X.window_final hH hβ hpend hq hq' hqq hclq hdis hW hall


/-- **Lemma 21 of [ACE26]** (read/write registers): see `lemma27`. -/
theorem lemma21 (hH : X.Hyp 1) : X.Sing := X.lemma27 hH

/-- **Lemma 22 of [ACE26]** (read/write registers): see `lemma28`. -/
theorem lemma22 (hH : X.Hyp 1) {α : List (LLabel P)} (hα : X.Good α) (hsup : ¬ X.Closed α) :
    X.NoDec α := X.lemma28 hH hα hsup

end LLCtx

end Cslib.SharedMemory.Referee
