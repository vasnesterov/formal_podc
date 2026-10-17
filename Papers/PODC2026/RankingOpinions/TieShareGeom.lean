import Papers.PODC2026.RankingOpinions.TieShare

/-!
# Circles_TieSharing: modulo ranges, sectors and arcs

Geometry used in the proof of Theorem 4.2. Fix a set `S` of colors with at least two elements
(`S` is the set `M` of colors in relative majority, or, for the unique-majority case, the smallest
greedy independent set with at least two elements). The colors are split into *sectors*
`[μ, nxt S μ]_k` for `μ ∈ S`. A braket `⟨g|h⟩` is an `S`-arc if `g ≠ h` and no element of `S` lies
strictly inside `[g, h]_k` (Claim 2 of the paper: after stabilization every braket is such an arc).
An arc lies in the sector of `secOf S g` (the element of `S` closest to `g` counterclockwise), at
offsets `off ≤ en ≤ secLen` (`arc_en_le`). In these coordinates the paper's inclusion of modulo
ranges is inclusion of intervals inside one sector (`rsub_iff`), etc.
-/

namespace RankingOpinions

open Finset

variable {k : ℕ}

/-! ### Clockwise distance -/

lemma w_eq_cdist {x y : Fin k} (h : x ≠ y) : w k x y = Fin.cdist x y := by
  rw [w_val, Fin.cdist_eq_ite]; have := Fin.val_ne_of_ne h; split_ifs <;> omega

lemma inRng_iff (e : Braket k) (z : Fin k) : inRng e z ↔ Fin.cdist e.1 z ≤ Fin.cdist e.1 e.2 :=
  Iff.rfl

/-! ### Sectors -/

variable (S : Finset (Fin k))

/-- The start of the sector of `z`: the element of `S` closest to `z` counterclockwise. -/
noncomputable def secOf (z : Fin k) : Fin k :=
  if h : S.Nonempty then (S.exists_min_image (fun μ => Fin.cdist μ z) h).choose else z

/-- The length of the sector starting at `μ`. -/
noncomputable def secLen (μ : Fin k) : ℕ := Fin.cdist μ (nxt S μ)

variable {S}

lemma secOf_mem (hS : S.Nonempty) (z : Fin k) : secOf S z ∈ S := by
  simp only [secOf, hS, dite_true]; exact (S.exists_min_image _ hS).choose_spec.1

lemma secOf_min (z : Fin k) {μ : Fin k} (hμ : μ ∈ S) : Fin.cdist (secOf S z) z ≤ Fin.cdist μ z := by
  have hS : S.Nonempty := ⟨μ, hμ⟩
  simp only [secOf, hS, dite_true]
  exact (S.exists_min_image (fun μ => Fin.cdist μ z) hS).choose_spec.2 μ hμ

lemma secOf_of_mem {μ : Fin k} (hμ : μ ∈ S) : secOf S μ = μ := by
  have := secOf_min μ hμ; rw [Fin.cdist_self] at this
  exact Fin.cdist_eq_zero.1 (Nat.le_zero.1 this)

/-- Standing assumption: `S` has at least two elements, i.e. no `μ ∈ S` is its own successor. -/
def TwoPlus (S : Finset (Fin k)) : Prop := ∀ μ ∈ S, nxt S μ ≠ μ

lemma secLen_pos (hS : TwoPlus S) {μ : Fin k} (hμ : μ ∈ S) : 0 < secLen S μ := by
  unfold secLen
  rcases Nat.eq_zero_or_pos (Fin.cdist μ (nxt S μ)) with h | h
  · exact absurd (Fin.cdist_eq_zero.1 h).symm (hS μ hμ)
  · exact h

lemma secLen_lt (μ : Fin k) : secLen S μ < k := Fin.cdist_lt _ _

/-- No element of `S` lies strictly inside a sector. -/
lemma secLen_le (hS : TwoPlus S) {μ ν : Fin k} (hμ : μ ∈ S) (hν : ν ∈ S) (hne : ν ≠ μ) :
    secLen S μ ≤ Fin.cdist μ ν := by
  have := nxt_min hμ hν
  rw [w_eq_cdist (Ne.symm (hS μ hμ)), w_eq_cdist (Ne.symm hne)] at this
  exact this

/-- A point at distance less than the sector length from `μ ∈ S` is in the sector of `μ`. -/
lemma secOf_eq (hS : TwoPlus S) {μ z : Fin k} (hμ : μ ∈ S) (hz : Fin.cdist μ z < secLen S μ) :
    secOf S z = μ := by
  by_contra hne
  have hmem := secOf_mem ⟨μ, hμ⟩ z
  have h1 := secOf_min z hμ
  have h2 := secLen_le hS hμ hmem hne
  have h3 := Fin.cdist_add_cdist μ (secOf S z) z
  have h4 := Fin.cdist_lt μ (secOf S z)
  omega

lemma dst_secOf_lt (hS : TwoPlus S) (hne : S.Nonempty) (z : Fin k) :
    Fin.cdist (secOf S z) z < secLen S (secOf S z) := by
  obtain ⟨μ, hμd⟩ : ∃ μ, secOf S z = μ := ⟨_, rfl⟩
  have hμ : μ ∈ S := hμd ▸ secOf_mem hne z
  rw [hμd]
  by_contra hle; push Not at hle
  have hν := nxt_mem hμ
  have h1 := secOf_min z hν
  rw [hμd] at h1
  have h2 := Fin.cdist_add_cdist μ (nxt S μ) z
  have h3 := secLen_pos hS hμ
  unfold secLen at hle h3
  have h4 := Fin.cdist_lt (nxt S μ) z
  omega

/-- Iterating `nxt S` from any element of `S` reaches every element of `S`. -/
lemma nxt_iterate_reach (hS : TwoPlus S) {μ ν : Fin k} (hμ : μ ∈ S) (hν : ν ∈ S) :
    ∃ n, (nxt S)^[n] μ = ν := by
  induction h : Fin.cdist μ ν using Nat.strong_induction_on generalizing μ with
  | _ d ih =>
  by_cases he : μ = ν
  · exact ⟨0, he⟩
  · have hle := secLen_le hS hμ hν (Ne.symm he)
    have h1 := Fin.cdist_add_cdist μ (nxt S μ) ν
    have h2 := secLen_pos hS hμ
    have h3 := Fin.cdist_lt (nxt S μ) ν
    unfold secLen at hle h2
    obtain ⟨n, hn⟩ := ih (Fin.cdist (nxt S μ) ν) (by omega) (nxt_mem hμ) rfl
    exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

/-- Distances from a fixed `μ₀ ∈ S` increase along the sectors, until `μ₀` is reached again. -/
lemma dst_nxt (hS : TwoPlus S) {μ₀ μ : Fin k} (h0 : μ₀ ∈ S) (hμ : μ ∈ S) (hne : nxt S μ ≠ μ₀) :
    Fin.cdist μ₀ (nxt S μ) = Fin.cdist μ₀ μ + secLen S μ := by
  have h1 := Fin.cdist_add_cdist μ₀ μ (nxt S μ)
  unfold secLen
  rcases h1 with h1 | h1
  · omega
  · exfalso
    by_cases h : μ = μ₀
    · subst h; rw [Fin.cdist_self] at h1; have := Fin.cdist_lt μ (nxt S μ); omega
    · have h2 := secLen_le hS hμ h0 (Ne.symm h)
      have h3 := Fin.cdist_add_cdist_swap (Ne.symm h)
      unfold secLen at h2
      have h4 := Fin.cdist_lt μ₀ (nxt S μ)
      -- `μ₀` would lie at the end of the sector of `μ`
      have h5 : Fin.cdist μ μ₀ = Fin.cdist μ (nxt S μ) := by omega
      exact hne (Fin.cdist_right_injective _ h5).symm

/-! ### Arcs -/

/-- An `S`-arc: a non-diagonal braket with no element of `S` strictly inside its range. -/
def IsArc (S : Finset (Fin k)) (e : Braket k) : Prop :=
  e.1 ≠ e.2 ∧ ∀ ν ∈ S, ¬ (0 < Fin.cdist e.1 ν ∧ Fin.cdist e.1 ν < Fin.cdist e.1 e.2)

/-- The sector of an arc. -/
noncomputable def sec (S : Finset (Fin k)) (e : Braket k) : Fin k := secOf S e.1
/-- Offset of the bra of an arc in its sector. -/
noncomputable def off (S : Finset (Fin k)) (e : Braket k) : ℕ := Fin.cdist (sec S e) e.1
/-- Offset of the ket of an arc in its sector. -/
noncomputable def en (S : Finset (Fin k)) (e : Braket k) : ℕ := off S e + Fin.cdist e.1 e.2

lemma IsArc.len_pos {e : Braket k} (he : IsArc S e) : 0 < Fin.cdist e.1 e.2 := by
  rcases Nat.eq_zero_or_pos (Fin.cdist e.1 e.2) with h | h
  · exact absurd (Fin.cdist_eq_zero.1 h) he.1
  · exact h

lemma off_lt_en {e : Braket k} (he : IsArc S e) : off S e < en S e := by
  unfold en; have := he.len_pos; omega

/-- An arc ends inside its sector. -/
lemma arc_en_le (hS : TwoPlus S) (hne : S.Nonempty) {e : Braket k} (he : IsArc S e) :
    en S e ≤ secLen S (sec S e) := by
  set μ := sec S e
  have hμ : μ ∈ S := secOf_mem hne e.1
  have hlt := dst_secOf_lt hS hne e.1
  have h1 := Fin.cdist_add_cdist μ e.1 (nxt S μ)
  have h2 := he.2 (nxt S μ) (nxt_mem hμ)
  have h3 := Fin.cdist_lt e.1 (nxt S μ)
  unfold en off; unfold secLen at hlt ⊢
  change Fin.cdist μ e.1 < Fin.cdist μ (nxt S μ) at hlt
  change Fin.cdist μ e.1 + Fin.cdist e.1 e.2 ≤ Fin.cdist μ (nxt S μ)
  omega

lemma en_lt (hS : TwoPlus S) (hne : S.Nonempty) {e : Braket k} (he : IsArc S e) : en S e < k :=
  lt_of_le_of_lt (arc_en_le hS hne he) (secLen_lt _)

lemma sec_mem (hne : S.Nonempty) (e : Braket k) : sec S e ∈ S := secOf_mem hne e.1

lemma dst_sec_ket (hS : TwoPlus S) (hne : S.Nonempty) {e : Braket k} (he : IsArc S e) :
    Fin.cdist (sec S e) e.2 = en S e := by
  have h1 := Fin.cdist_add_cdist (sec S e) e.1 e.2
  have h2 := en_lt hS hne he
  have h3 := Fin.cdist_lt (sec S e) e.2
  unfold en off at *; omega

/-- Membership in the range of an arc, in sector coordinates. -/
lemma mem_arc (hS : TwoPlus S) (hne : S.Nonempty) {e : Braket k} (he : IsArc S e) (z : Fin k) :
    inRng e z ↔ off S e ≤ Fin.cdist (sec S e) z ∧ Fin.cdist (sec S e) z ≤ en S e := by
  have h1 := Fin.cdist_add_cdist (sec S e) e.1 z
  have h2 := en_lt hS hne he
  have h3 := Fin.cdist_lt e.1 z
  rw [inRng_iff]; unfold en off at *
  constructor
  · intro h; omega
  · intro h; omega

/-- Same bra iff same sector and same offset. -/
lemma bra_eq_iff {e f : Braket k} : e.1 = f.1 ↔ sec S e = sec S f ∧ off S e = off S f := by
  constructor
  · intro h; unfold off sec; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; unfold off at h2; rw [h1] at h2; exact Fin.cdist_right_injective _ h2

/-- **Inclusion of modulo ranges of arcs** (with the paper's extra condition): it holds iff the
two arcs are in the same sector and the intervals of offsets are nested. -/
lemma rsub_iff (hS : TwoPlus S) (hne : S.Nonempty) {e f : Braket k} (he : IsArc S e)
    (hf : IsArc S f) :
    RSub e f ↔ sec S e = sec S f ∧ off S f ≤ off S e ∧ en S e ≤ en S f := by
  constructor
  · rintro ⟨hsub, hextra⟩
    obtain ⟨σ, hσ⟩ : ∃ σ, sec S f = σ := ⟨_, rfl⟩
    have hσS : σ ∈ S := hσ ▸ sec_mem hne f
    have hmf : ∀ z, inRng f z ↔ off S f ≤ Fin.cdist σ z ∧ Fin.cdist σ z ≤ en S f := by
      intro z; rw [← hσ]; exact mem_arc hS hne hf z
    have hfL : en S f ≤ secLen S σ := hσ ▸ arc_en_le hS hne hf
    have hketf : Fin.cdist σ f.2 = en S f := hσ ▸ dst_sec_ket hS hne hf
    have hbraf : Fin.cdist σ f.1 = off S f := by unfold off; rw [hσ]
    -- the bra and the ket of `e` are in the range of `f`
    have hg := (hmf e.1).1 (hsub e.1 (by rw [inRng_iff, Fin.cdist_self]; exact Nat.zero_le _))
    have hh := (hmf e.2).1 (hsub e.2 (by rw [inRng_iff]))
    have hadd := Fin.cdist_add_cdist σ e.1 e.2
    have hlen := he.len_pos
    have hLf := secLen_lt (S := S) σ
    rcases hadd with hadd | hadd
    · -- no wrap-around: `e` lies in the sector of `σ`
      have hsec : sec S e = σ := secOf_eq hS hσS (by omega)
      refine ⟨hsec.trans hσ.symm, ?_, ?_⟩
      · unfold off; rw [hsec, hσ]; omega
      · show off S e + Fin.cdist e.1 e.2 ≤ en S f
        unfold off; rw [hsec]; omega
    · -- wrap-around: impossible
      exfalso
      have hlt2 := Fin.cdist_lt e.1 e.2
      have hgpos : 0 < Fin.cdist σ e.1 := by omega
      have hgne : σ ≠ e.1 := fun h => by rw [h, Fin.cdist_self] at hgpos; exact lt_irrefl _ hgpos
      have hc := Fin.cdist_add_cdist_swap hgne
      -- `σ` lies on `e`, hence is its ket
      have hσe : Fin.cdist e.1 σ = Fin.cdist e.1 e.2 := by
        have := he.2 σ hσS
        omega
      have hket : σ = e.2 := Fin.cdist_right_injective _ hσe
      have hketd : Fin.cdist σ e.2 = 0 := by rw [← hket, Fin.cdist_self]
      -- the point just before `σ` is on `e`, hence in `f`
      have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (Fin.cdist_lt σ σ)
      obtain ⟨z1, hz1⟩ := Fin.exists_cdist_eq σ (show k - 1 < k by omega)
      have hz1e : Fin.cdist e.1 z1 = k - 1 - Fin.cdist σ e.1 := by
        have := Fin.cdist_add_cdist σ e.1 z1; have := Fin.cdist_lt e.1 z1
        have := Fin.cdist_lt σ e.1; omega
      have hz1f := (hmf z1).1 (hsub z1 (by rw [inRng_iff]; omega))
      -- `f` is the whole sector of `σ`, of length `k - 1`
      have hen : en S f = k - 1 := by omega
      have hoff : off S f = 0 := by omega
      have hnxt : nxt S σ = z1 := by
        apply Fin.cdist_right_injective σ; unfold secLen at hfL hLf; omega
      -- `z1 ∈ S` lies on `e`, hence is its bra
      have hz1S : z1 ∈ S := hnxt ▸ nxt_mem hσS
      have hbra : Fin.cdist e.1 z1 = 0 := by
        have := he.2 z1 hz1S; omega
      have hez1 : e.1 = z1 := Fin.cdist_eq_zero.1 hbra
      -- so `e = ⟨z1|σ⟩` and `f = ⟨σ|z1⟩`, excluded by the extra condition
      have hf1 : f.1 = σ := (Fin.cdist_eq_zero.1 (hbraf.trans hoff)).symm
      have hf2 : f.2 = z1 := by
        apply Fin.cdist_right_injective σ; rw [hketf, hen, hz1]
      rcases hextra with h | h
      · exact h (by rw [hez1, hf2])
      · exact h (by rw [hf1, hket])
  · rintro ⟨hsec, hoff, hen⟩
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [mem_arc hS hne he] at hz; rw [mem_arc hS hne hf, ← hsec]; omega
    · left
      intro h
      have h1 : Fin.cdist (sec S f) e.1 = off S e := by unfold off; rw [hsec]
      have h2 := dst_sec_ket hS hne hf
      rw [h] at h1
      have := off_lt_en he
      omega

/-- Equality of the ranges of two arcs in the same sector. -/
lemma rng_eq_iff (hS : TwoPlus S) (hne : S.Nonempty) {e f : Braket k} (he : IsArc S e)
    (hf : IsArc S f) (hsec : sec S e = sec S f) :
    (∀ z, inRng e z ↔ inRng f z) ↔ off S e = off S f ∧ en S e = en S f := by
  obtain ⟨σ, hσe⟩ : ∃ σ, sec S e = σ := ⟨_, rfl⟩
  have hσf : sec S f = σ := hsec ▸ hσe
  have me : ∀ z, inRng e z ↔ off S e ≤ Fin.cdist σ z ∧ Fin.cdist σ z ≤ en S e := by
    intro z; rw [← hσe]; exact mem_arc hS hne he z
  have mf : ∀ z, inRng f z ↔ off S f ≤ Fin.cdist σ z ∧ Fin.cdist σ z ≤ en S f := by
    intro z; rw [← hσf]; exact mem_arc hS hne hf z
  have e1 : Fin.cdist σ e.1 = off S e := by unfold off; rw [hσe]
  have e2 : Fin.cdist σ e.2 = en S e := hσe ▸ dst_sec_ket hS hne he
  have f1 : Fin.cdist σ f.1 = off S f := by unfold off; rw [hσf]
  have f2 : Fin.cdist σ f.2 = en S f := hσf ▸ dst_sec_ket hS hne hf
  have oe := off_lt_en he; have of := off_lt_en hf
  constructor
  · intro h
    have g1 := (mf e.1).1 ((h e.1).1 ((me e.1).2 (by omega)))
    have g2 := (me f.1).1 ((h f.1).2 ((mf f.1).2 (by omega)))
    have g3 := (mf e.2).1 ((h e.2).1 ((me e.2).2 (by omega)))
    have g4 := (me f.2).1 ((h f.2).2 ((mf f.2).2 (by omega)))
    omega
  · rintro ⟨h1, h2⟩ z
    rw [mem_arc hS hne he, mem_arc hS hne hf, hsec, h1, h2]

/-- Strict inclusion of modulo ranges of arcs. -/
lemma rssub_iff (hS : TwoPlus S) (hne : S.Nonempty) {e f : Braket k} (he : IsArc S e)
    (hf : IsArc S f) :
    RSSub e f ↔ sec S e = sec S f ∧ off S f ≤ off S e ∧ en S e ≤ en S f ∧
      (off S e ≠ off S f ∨ en S e ≠ en S f) := by
  unfold RSSub
  rw [rsub_iff hS hne he hf]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    rw [rng_eq_iff hS hne he hf h1] at h4
    refine ⟨h1, h2, h3, ?_⟩
    by_contra h; push Not at h; exact h4 h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, h3⟩, ?_⟩
    rw [rng_eq_iff hS hne he hf h1]
    rintro ⟨h5, h6⟩; rcases h4 with h | h <;> contradiction

/-- The ket of an arc is the bra of `f` iff `f` starts where `e` ends: in the same sector, or
`e` ends at the end of its sector and `f` starts the next sector. -/
lemma ket_eq_bra_iff (hS : TwoPlus S) (hne : S.Nonempty) {e f : Braket k} (he : IsArc S e) :
    e.2 = f.1 ↔ (sec S e = sec S f ∧ en S e = off S f ∧ en S e < secLen S (sec S e)) ∨
      (en S e = secLen S (sec S e) ∧ off S f = 0 ∧ sec S f = nxt S (sec S e)) := by
  have hket := dst_sec_ket hS hne he
  have hle := arc_en_le hS hne he
  have hσ := sec_mem hne e
  constructor
  · intro h
    rcases Nat.lt_or_ge (en S e) (secLen S (sec S e)) with hlt | hge
    · left
      have : secOf S e.2 = sec S e := secOf_eq hS hσ (by rw [hket]; exact hlt)
      have hs : sec S f = sec S e := by unfold sec; rw [← h]; exact this
      refine ⟨hs.symm, ?_, hlt⟩
      unfold off; rw [hs, ← h, hket]
    · right
      have hL : en S e = secLen S (sec S e) := le_antisymm hle hge
      have hn : e.2 = nxt S (sec S e) := by
        apply Fin.cdist_right_injective (sec S e); rw [hket, hL]; rfl
      have hs : sec S f = nxt S (sec S e) := by
        unfold sec; rw [← h, hn]; exact secOf_of_mem (nxt_mem hσ)
      refine ⟨hL, ?_, hs⟩
      unfold off; rw [hs, ← h, hn, Fin.cdist_self]
  · rintro (⟨hs, h1, -⟩ | ⟨hL, h0, hs⟩)
    · apply Fin.cdist_right_injective (sec S e); rw [hket, h1]; unfold off; rw [hs]
    · have h1 : f.1 = sec S f := (Fin.cdist_eq_zero.1 h0).symm
      rw [h1, hs]; apply Fin.cdist_right_injective (sec S e); rw [hket, hL]; rfl

/-- The top arc of a sector. -/
lemma top_iff (hS : TwoPlus S) (hne : S.Nonempty) {e : Braket k} (he : IsArc S e) :
    (off S e = 0 ∧ en S e = secLen S (sec S e)) ↔ e = (sec S e, nxt S (sec S e)) := by
  constructor
  · rintro ⟨h0, hL⟩
    apply Prod.ext
    · exact (Fin.cdist_eq_zero.1 h0).symm
    · apply Fin.cdist_right_injective (sec S e); rw [dst_sec_ket hS hne he, hL]; rfl
  · intro h
    have h1 : e.1 = sec S e := congrArg Prod.fst h
    have h2 : e.2 = nxt S (sec S e) := congrArg Prod.snd h
    refine ⟨?_, ?_⟩
    · unfold off; rw [← h1, Fin.cdist_self]
    · rw [← dst_sec_ket hS hne he, h2]; rfl

/-- The circle braket `⟨μ|nxt S μ⟩` is an arc. -/
lemma isArc_circle (hS : TwoPlus S) {μ : Fin k} (hμ : μ ∈ S) : IsArc S (μ, nxt S μ) := by
  refine ⟨(hS μ hμ).symm, fun ν hν ⟨h1, h2⟩ => ?_⟩
  have hne : ν ≠ μ := fun h => by rw [h, Fin.cdist_self] at h1; exact lt_irrefl _ h1
  have := secLen_le hS hμ hν hne
  unfold secLen at this; simp only at h2; omega

/-- A braket `⟨g|nxt G g⟩` of a set `G ⊇ S` is an `S`-arc (if not diagonal). -/
lemma isArc_of_sup {G : Finset (Fin k)} (hSG : S ⊆ G) {g : Fin k} (hg : g ∈ G)
    (hd : nxt G g ≠ g) : IsArc S (g, nxt G g) := by
  refine ⟨hd.symm, fun ν hν ⟨h1, h2⟩ => ?_⟩
  have hne : ν ≠ g := fun h => by rw [h, Fin.cdist_self] at h1; exact lt_irrefl _ h1
  have := nxt_min hg (hSG hν)
  rw [w_eq_cdist hd.symm, w_eq_cdist hne.symm] at this
  simp only at h2; omega

/-! ### Diagonal brakets -/

lemma inRng_diag (g z : Fin k) : inRng (g, g) z ↔ z = g := by
  rw [inRng_iff]; simp only [Fin.cdist_self, Nat.le_zero]
  exact ⟨fun h => (Fin.cdist_eq_zero.1 h).symm, fun h => by rw [h, Fin.cdist_self]⟩

lemma inRng_self (e : Braket k) : inRng e e.1 := by
  rw [inRng_iff, Fin.cdist_self]; exact Nat.zero_le _

/-- Nothing is strictly inside the range `{g}` of a diagonal braket. -/
lemma not_rssub_diag (f : Braket k) (g : Fin k) : ¬ RSSub f (g, g) := by
  rintro ⟨⟨hsub, -⟩, hne⟩
  have hf : f.1 = g := (inRng_diag g f.1).1 (hsub _ (inRng_self f))
  apply hne
  intro z
  refine ⟨hsub z, fun hz => ?_⟩
  rw [(inRng_diag g z).1 hz, ← hf]; exact inRng_self f

lemma not_rsub_diag_diag {g h : Fin k} (hgh : g ≠ h) : ¬ RSub (g, g) (h, h) := by
  rintro ⟨hsub, -⟩
  exact hgh ((inRng_diag h g).1 (hsub g (inRng_self (g, g))))

end RankingOpinions
