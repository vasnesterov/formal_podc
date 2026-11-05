import Papers.PODC2012.LimitedUseSnapshots.Spec
import Papers.PODC2012.LimitedUseSnapshots.CriterionAux
import Mathlib.Data.Finset.Max

/-!
# A linearizability criterion for 2-component max arrays

History-level sufficient condition for an execution of a max-array implementation to be
linearizable, in the style of the paper's proof of Theorem 3.4 (and of its erratum): the results
of the scans are pairwise comparable (H1); every scan sees the contribution of every operation that
precedes it (H2); and every non-zero component `w` of a scan result has a *witness* update with
value `w` that is invoked before the scan returns and whose real-time predecessors are all seen by
the scan (H3).

The linearization orders the completed scans by (sum of the result, response position) and inserts
every invoked update immediately before the first scan that may see it.
-/

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-! ### Proof of the criterion

Scans are ordered by `sk` = (sum of the result, response position). An update `U` is placed
immediately before the first scan `S` that is *good* for it (`MAGood`): every scan preceding `U`
comes before `S`, and `S` sees `U` and everything preceding `U`. -/

section CriterionProof

/-- The result of a scan (`(0, 0)` if pending). -/
noncomputable def maRes (α : List (Label P maxArrObj)) (x : OpId P) : ℕ × ℕ :=
  (respOf α x).getD (0, 0)

/-- The sort key of a scan: (sum of its result, response position), lexicographically. -/
noncomputable def maSk (α : List (Label P maxArrObj)) (x : OpId P) : ℕ ×ₗ ℕ :=
  toLex ((maRes α x).1 + (maRes α x).2, retPos α x)

/-- The completed scan `S` may be linearized after the update `U`. -/
def MAGood (α : List (Label P maxArrObj)) (U S : OpId P) : Prop :=
  opOf α S = some .scan ∧ Completed α S ∧
    (∀ S', opOf α S' = some .scan → Precedes α S' U → maSk α S' < maSk α S) ∧
    (∀ y, (y = U ∨ Precedes α y U) → contribOf α y ≤ maRes α S)

open Classical in
/-- The key of the first scan good for `U` (`⊤` if none). -/
noncomputable def maCut (α : List (Label P maxArrObj)) (U : OpId P) : WithTop (ℕ ×ₗ ℕ) :=
  (((invIds α).toFinset.filter (MAGood α U)).image (maSk α)).min

open Classical in
/-- The linearization key: scans by `maSk`, updates just before the first good scan. -/
noncomputable def maKey (α : List (Label P maxArrObj)) (x : OpId P) : WithTop (ℕ ×ₗ ℕ) ×ₗ ℕ :=
  if opOf α x = some .scan then toLex (((maSk α x : ℕ ×ₗ ℕ) : WithTop (ℕ ×ₗ ℕ)), 1)
  else toLex (maCut α x, 0)

/-- The linearized instances: completed scans and all invoked updates. -/
def MAX (α : List (Label P maxArrObj)) (x : OpId P) : Prop :=
  (opOf α x = some .scan ∧ Completed α x) ∨ (Invoked α x ∧ opOf α x ≠ some .scan)

lemma maRes_eq {α : List (Label P maxArrObj)} {x : OpId P} {r : ℕ × ℕ}
    (h : respOf α x = some r) : maRes α x = r := by simp [maRes, h]

lemma contribOf_scan {α : List (Label P maxArrObj)} {x : OpId P} (h : opOf α x = some .scan) :
    contribOf α x = maRes α x := by simp [contribOf, h, maRes]

lemma exists_respOf {α : List (Label P maxArrObj)} {x : OpId P} (h : Completed α x) :
    ∃ r, respOf α x = some r :=
  Option.isSome_iff_exists.1 (completed_iff_respOf.1 h)

lemma runOps_le (q t : ℕ × ℕ) (os : List MAOp) (hq : q ≤ t)
    (h : ∀ o ∈ os, o.contrib (0, 0) ≤ t) : maxArrObj.runOps q os ≤ t := by
  induction os generalizing q with
  | nil => exact hq
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    apply ih _ _ fun o' ho' => h o' (by simp [ho'])
    have ho := h o (by simp)
    rw [Prod.le_def] at hq ho ⊢
    cases o <;> simp at ho ⊢ <;> omega

lemma le_runOps (q : ℕ × ℕ) (os : List MAOp) :
    q ≤ maxArrObj.runOps q os ∧ ∀ o ∈ os, o.contrib (0, 0) ≤ maxArrObj.runOps q os := by
  induction os generalizing q with
  | nil => exact ⟨le_rfl, by simp⟩
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    obtain ⟨h1, h2⟩ := ih (maxArrObj.δ q o).1
    refine ⟨le_trans ?_ h1, ?_⟩
    · rw [Prod.le_def]; cases o <;> simp
    · intro o' ho'
      rcases List.mem_cons.1 ho' with rfl | ho'
      · refine le_trans ?_ h1
        rw [Prod.le_def]; cases o' <;> simp
      · exact h2 o' ho'

variable {α : List (Label P maxArrObj)}

/-- Under (H1), the order of scans by `maSk` refines the order of their results. -/
lemma maRes_le_of_maSk_le
    (H1 : ∀ x y r s, opOf α x = some .scan → respOf α x = some r →
      opOf α y = some .scan → respOf α y = some s → r ≤ s ∨ s ≤ r)
    {S₁ S₂ : OpId P} (h₁ : opOf α S₁ = some .scan) (c₁ : Completed α S₁)
    (h₂ : opOf α S₂ = some .scan) (c₂ : Completed α S₂) (h : maSk α S₁ ≤ maSk α S₂) :
    maRes α S₁ ≤ maRes α S₂ := by
  obtain ⟨r, hr⟩ := exists_respOf c₁
  obtain ⟨s, hs⟩ := exists_respOf c₂
  rcases H1 _ _ _ _ h₁ hr h₂ hs with h' | h'
  · rwa [maRes_eq hr, maRes_eq hs]
  · simp only [maSk, maRes_eq hr, maRes_eq hs, Prod.Lex.toLex_le_toLex] at h
    rw [maRes_eq hr, maRes_eq hs]
    rw [Prod.le_def] at h' ⊢
    omega

lemma maGood_mono
    (H1 : ∀ x y r s, opOf α x = some .scan → respOf α x = some r →
      opOf α y = some .scan → respOf α y = some s → r ≤ s ∨ s ≤ r)
    {U S S₂ : OpId P} (hg : MAGood α U S) (h₂ : opOf α S₂ = some .scan) (c₂ : Completed α S₂)
    (h : maSk α S ≤ maSk α S₂) : MAGood α U S₂ :=
  ⟨h₂, c₂, fun S' h' hp => (hg.2.2.1 S' h' hp).trans_le h,
    fun y hy => (hg.2.2.2 y hy).trans (maRes_le_of_maSk_le H1 hg.1 hg.2.1 h₂ c₂ h)⟩

lemma maCut_le (hwf : WellFormed α) {U S : OpId P} (hg : MAGood α U S) :
    maCut α U ≤ ((maSk α S : ℕ ×ₗ ℕ) : WithTop (ℕ ×ₗ ℕ)) := by
  classical
  unfold maCut
  apply Finset.min_le
  apply Finset.mem_image_of_mem
  simp only [Finset.mem_filter, List.mem_toFinset, mem_invIds]
  exact ⟨hwf.invoked_of_completed hg.2.1, by convert hg⟩

lemma exists_maGood_of_maCut {U : OpId P} {m : ℕ ×ₗ ℕ} (h : maCut α U = m) :
    ∃ S, MAGood α U S ∧ maSk α S = m := by
  classical
  unfold maCut at h
  have := Finset.mem_of_min (by convert h)
  simp only [Finset.mem_image, Finset.mem_filter] at this
  obtain ⟨S, ⟨-, hS⟩, e⟩ := this
  exact ⟨S, by convert hS, e⟩

lemma maGood_of_maCut_le
    (H1 : ∀ x y r s, opOf α x = some .scan → respOf α x = some r →
      opOf α y = some .scan → respOf α y = some s → r ≤ s ∨ s ≤ r)
    {U S : OpId P} (hS : opOf α S = some .scan) (cS : Completed α S)
    (h : maCut α U ≤ ((maSk α S : ℕ ×ₗ ℕ) : WithTop (ℕ ×ₗ ℕ))) : MAGood α U S := by
  cases hc : maCut α U with
  | top => rw [hc] at h; exact absurd h (by simp)
  | coe m =>
    obtain ⟨S₀, hg, e⟩ := exists_maGood_of_maCut hc
    rw [hc, WithTop.coe_le_coe] at h
    exact maGood_mono H1 hg hS cS (e ▸ h)

lemma lt_maCut {U S' : OpId P} (h : opOf α S' = some .scan) (hp : Precedes α S' U) :
    ((maSk α S' : ℕ ×ₗ ℕ) : WithTop (ℕ ×ₗ ℕ)) < maCut α U := by
  cases hc : maCut α U with
  | top => exact WithTop.coe_lt_top _
  | coe m =>
    obtain ⟨S₀, hg, e⟩ := exists_maGood_of_maCut hc
    rw [WithTop.coe_lt_coe, ← e]
    exact hg.2.2.1 S' h hp

lemma maSk_lt_of_precedes (hwf : WellFormed α)
    (H2 : ∀ x r y, opOf α x = some .scan → respOf α x = some r → Precedes α y x →
      contribOf α y ≤ r)
    {S' S : OpId P} (h' : opOf α S' = some .scan) (h : opOf α S = some .scan)
    (cS : Completed α S) (hp : Precedes α S' S) : maSk α S' < maSk α S := by
  obtain ⟨r, hr⟩ := exists_respOf cS
  have hle := H2 S r S' h hr hp
  rw [contribOf_scan h'] at hle
  have h1 := (precedes_iff_retPos_lt_invPos.1 hp).2
  have h2 := invPos_le_retPos hwf cS
  simp only [maSk, maRes_eq hr, Prod.Lex.toLex_lt_toLex] at hle ⊢
  rw [Prod.le_def] at hle
  omega

/-- A witness update of (H3) is good for the scan. -/
lemma maGood_of_witness {S u : OpId P} (hS : opOf α S = some .scan) (cS : Completed α S)
    (hu : contribOf α u ≤ maRes α S) (hnp : ¬ Precedes α S u)
    (hpred : ∀ y, Precedes α y u → contribOf α y ≤ maRes α S) : MAGood α u S := by
  refine ⟨hS, cS, fun S' h' hp => ?_, fun y hy => ?_⟩
  · have hle := hpred S' hp
    rw [contribOf_scan h'] at hle
    have h1 := (precedes_iff_retPos_lt_invPos.1 hp).2
    have h2 : invPos α u ≤ retPos α S := by
      by_contra hc
      exact hnp (precedes_iff_retPos_lt_invPos.2 ⟨cS, by omega⟩)
    simp only [maSk, Prod.Lex.toLex_lt_toLex]
    rw [Prod.le_def] at hle
    omega
  · rcases hy with rfl | hy
    · exact hu
    · exact hpred y hy

end CriterionProof

/-- Linearizability criterion for max arrays. Besides (H1)–(H3) it needs (H0): completed updates
return the dummy response `(0, 0)` of the specification (without it, a single update returning
anything else is a non-linearizable history satisfying (H1)–(H3) vacuously). -/
theorem exists_isLinearization_maxArr (α : List (Label P maxArrObj)) (hwf : WellFormed α)
    (H1 : ∀ x y r s, opOf α x = some .scan → respOf α x = some r →
      opOf α y = some .scan → respOf α y = some s → r ≤ s ∨ s ≤ r)
    (H2 : ∀ x r y, opOf α x = some .scan → respOf α x = some r → Precedes α y x →
      contribOf α y ≤ r)
    (H3a : ∀ x r, opOf α x = some .scan → respOf α x = some r → 0 < r.1 →
      ∃ u, opOf α u = some (.upd0 r.1) ∧ ¬ Precedes α x u ∧
        ∀ y, Precedes α y u → contribOf α y ≤ r)
    (H3b : ∀ x r, opOf α x = some .scan → respOf α x = some r → 0 < r.2 →
      ∃ u, opOf α u = some (.upd1 r.2) ∧ ¬ Precedes α x u ∧
        ∀ y, Precedes α y u → contribOf α y ≤ r)
    (H0 : ∀ x o r, opOf α x = some o → respOf α x = some r → o ≠ .scan → r = (0, 0)) :
    ∃ L, IsLinearization α L := by
  classical
  refine exists_isLinearization_of_key α hwf (MAX α) (maKey α) ?_ ?_ ?_ ?_
  · rintro x (⟨-, hc⟩ | ⟨hi, -⟩)
    · exact hwf.invoked_of_completed hc
    · exact hi
  · intro x hc
    by_cases h : opOf α x = some .scan
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨hwf.invoked_of_completed hc, h⟩
  · intro a b hab hb
    by_cases ha : opOf α a = some .scan <;> by_cases hbs : opOf α b = some .scan
    · have cb : Completed α b := hb.elim (fun h => h.2) (fun h => absurd hbs h.2)
      simp only [maKey, ha, hbs, ↓reduceIte, Prod.Lex.toLex_le_toLex, WithTop.coe_lt_coe]
      exact Or.inl (maSk_lt_of_precedes hwf H2 ha hbs cb hab)
    · simp only [maKey, ha, hbs, ↓reduceIte, Prod.Lex.toLex_le_toLex]
      exact Or.inl (lt_maCut ha hab)
    · have cb : Completed α b := hb.elim (fun h => h.2) (fun h => absurd hbs h.2)
      obtain ⟨r, hr⟩ := exists_respOf cb
      have hg : MAGood α a b := ⟨hbs, cb,
        fun S' h' hp => maSk_lt_of_precedes hwf H2 h' hbs cb (hp.trans hwf hab),
        fun y hy => by
          rw [maRes_eq hr]
          exact H2 b r y hbs hr (hy.elim (fun e => e ▸ hab) (fun h => h.trans hwf hab))⟩
      have := maCut_le hwf hg
      simp only [maKey, ha, hbs, ↓reduceIte, Prod.Lex.toLex_le_toLex]
      rcases this.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega⟩
    · have hle : maCut α a ≤ maCut α b := by
        cases hc : maCut α b with
        | top => exact le_top
        | coe m =>
          obtain ⟨S, hg, e⟩ := exists_maGood_of_maCut hc
          have hga : MAGood α a S := ⟨hg.1, hg.2.1,
            fun S' h' hp => hg.2.2.1 S' h' (hp.trans hwf hab),
            fun y hy => hg.2.2.2 y (Or.inr (hy.elim (fun e => e ▸ hab)
              (fun h => h.trans hwf hab)))⟩
          rw [← e]
          exact maCut_le hwf hga
      simp only [maKey, ha, hbs, ↓reduceIte, Prod.Lex.toLex_le_toLex]
      rcases hle.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, le_rfl⟩
  · intro L₁ x o r hx hxo hr hL1 hlt _
    cases o with
    | upd0 v => exact (H0 x _ r hxo hr (by simp)).symm
    | upd1 v => exact (H0 x _ r hxo hr (by simp)).symm
    | scan =>
      have cx : Completed α x := Completed.of_respOf_eq_some hr
      show maxArrObj.runOps (0, 0) (L₁.map Prod.snd) = r
      apply le_antisymm
      · apply runOps_le _ _ _ (by rw [Prod.le_def]; simp)
        intro o' ho'
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ho'
        obtain ⟨hyo, -, hyk⟩ := hL1 y hy
        by_cases hys : y.2 = .scan
        · rw [hys, Prod.le_def]; simp
        · have hyk' : maCut α y.1 ≤ ((maSk α x : ℕ ×ₗ ℕ) : WithTop (ℕ ×ₗ ℕ)) := by
            have hyo' : opOf α y.1 ≠ some .scan := by rw [hyo]; simpa using hys
            simp only [maKey, hxo, hyo', ↓reduceIte, Prod.Lex.toLex_le_toLex] at hyk
            rcases hyk with h | ⟨h, -⟩
            · exact h.le
            · exact h.le
          have hg := maGood_of_maCut_le H1 hxo cx hyk'
          have := hg.2.2.2 y.1 (Or.inl rfl)
          rw [maRes_eq hr] at this
          have e : y.2.contrib (0, 0) = contribOf α y.1 := by
            simp only [contribOf, hyo]
            generalize y.2 = o' at hys
            cases o' <;> first | rfl | exact absurd rfl hys
          rw [e]; exact this
      · obtain ⟨-, hrun⟩ := le_runOps (0, 0) (L₁.map Prod.snd)
        have key : ∀ u o, opOf α u = some o → o ≠ .scan → contribOf α u ≤ r → ¬ Precedes α x u →
            (∀ y, Precedes α y u → contribOf α y ≤ r) →
            o.contrib (0, 0) ≤ maxArrObj.runOps (0, 0) (L₁.map Prod.snd) := by
          intro u o hu hos hcu hnp hpred
          have hg : MAGood α u x := maGood_of_witness hxo cx (by rwa [maRes_eq hr]) hnp
            (by rw [maRes_eq hr]; exact hpred)
          have hus : opOf α u ≠ some .scan := by rw [hu]; simpa using hos
          have hXu : MAX α u := Or.inr ⟨Invoked.of_opOf_eq_some hu, hus⟩
          have hku : maKey α u < maKey α x := by
            simp only [maKey, hus, hxo, ↓reduceIte, Prod.Lex.toLex_lt_toLex]
            rcases (maCut_le hwf hg).lt_or_eq with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h, by omega⟩
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hlt u hXu hku)
          have hyo := (hL1 y hy).1
          rw [hu, Option.some_inj] at hyo
          rw [hyo]
          exact hrun y.2 (List.mem_map_of_mem hy)
        rw [Prod.le_def]
        constructor
        · rcases Nat.eq_zero_or_pos r.1 with h0 | hpos
          · rw [h0]; exact Nat.zero_le _
          · obtain ⟨u, hu, hnp, hpred⟩ := H3a x r hxo hr hpos
            have := key u _ hu (by simp)
              (by simp only [contribOf, hu, MAOp.contrib_upd0, Prod.le_def]; simp) hnp hpred
            rw [Prod.le_def] at this
            simpa using this.1
        · rcases Nat.eq_zero_or_pos r.2 with h0 | hpos
          · rw [h0]; exact Nat.zero_le _
          · obtain ⟨u, hu, hnp, hpred⟩ := H3b x r hxo hr hpos
            have := key u _ hu (by simp)
              (by simp only [contribOf, hu, MAOp.contrib_upd1, Prod.le_def]; simp) hnp hpred
            rw [Prod.le_def] at this
            simpa using this.2

end Podc.LimitedUseSnapshots
