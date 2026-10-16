import Papers.PODC2012.MaximalMatching.Glue
import Papers.PODC2012.MaximalMatching.BaseCase

/-!
# The inductive step (§3.9 of Hirvonen–Suomela)

From an `h`-critical pair `(S, T)` with `1 ≤ h < d` we build the colour pickers `Q` (for `T`) and
`P` (for `S`), the extensions `K = ext(S, P)`, `L = ext(T, Q)`, the colour `χ = A(T, τ, e)`, the
glued template `X`, and finally an `(h+1)`-critical pair (Lemma 16). The parity argument is
Lemma 15 (`lemma15`).
-/

namespace Papers.PODC2012.MaximalMatching

open Cslib.ColourSystem FreeCox Pointwise Template

variable {k : ℕ} {A : Algorithm k} {r h : ℕ}

/-! ### Matching partners -/

/-- The partner of `x` in the output of `A` on `T` (`x` itself if `x` is unmatched). -/
noncomputable def partner (A : Algorithm k) (T : Template k) (x : FreeCox k) : FreeCox k :=
  (T.out A x).elim x (fun c => x * gen c)

theorem len_le_len_partner (A : Algorithm k) (T : Template k) (x : FreeCox k) :
    len x ≤ len (partner A T x) + 1 := by
  unfold partner
  cases T.out A x with
  | none => simp
  | some c => exact le_len_mul_gen x c

theorem Good.partner_spec (hA : Good A r) {T : Template k} {h' : ℕ} (hT : IsTemplate h' T)
    {x : FreeCox k} (hx : x ∈ T.carrier) (hm : T.Matched A x) :
    partner A T x ∈ T.carrier ∧ partner A T (partner A T x) = x ∧ partner A T x ≠ x ∧
      T.Matched A (partner A T x) := by
  obtain ⟨c, hc, hout⟩ := hm
  have hxc : x * gen c ∈ T.carrier := mem_colours.1 hc
  have hout' := hA.out_mul_gen hT hx hout hxc
  have e1 : partner A T x = x * gen c := by simp [partner, hout]
  have e2 : partner A T (x * gen c) = x := by simp [partner, hout']
  refine ⟨by rw [e1]; exact hxc, by rw [e1, e2], ?_, ?_⟩
  · rw [e1]; intro h1
    exact gen_ne_one c (by simpa using congrArg (x⁻¹ * ·) h1)
  · rw [e1]; exact ⟨c, by rw [mem_colours, mul_gen_mul_gen]; exact hx, hout'⟩

/-! ### Colour pickers -/

open Classical in
/-- An arbitrary free colour (junk if there is none). -/
noncomputable def someFree (T : Template k) (t : FreeCox k) : Fin k :=
  if hc : ∃ c, T.Free t c then hc.choose else T.forb t

theorem someFree_free {T : Template k} {t : FreeCox k} (h : ∃ c, T.Free t c) :
    T.Free t (someFree T t) := by
  rw [someFree, dite_eq_left h]; exact h.choose_spec

open Classical in
/-- The picker `Q` for `(T, τ)`: the output colour if it is free, otherwise any free colour. -/
noncomputable def pickerQ (A : Algorithm k) (T : Template k) (t : FreeCox k) : Fin k :=
  if hq : ∃ c, T.out A t = some c ∧ T.Free t c then hq.choose else someFree T t

theorem pickerQ_eq {T : Template k} {t : FreeCox k} {c : Fin k} (h : T.out A t = some c)
    (hc : T.Free t c) : pickerQ A T t = c := by
  have hq : ∃ c, T.out A t = some c ∧ T.Free t c := ⟨c, h, hc⟩
  rw [pickerQ, dite_eq_left hq]
  exact Option.some.inj (hq.choose_spec.1.symm.trans h)

theorem pickerQ_free {T : Template k} {t : FreeCox k} (hex : ∃ c, T.Free t c) :
    T.Free t (pickerQ A T t) := by
  unfold pickerQ
  split_ifs with hq
  · exact hq.choose_spec.2
  · exact someFree_free hex

open Classical in
/-- The picker `P` for `(S, σ)`: agrees with `Q` near `e`. -/
noncomputable def pickerP (A : Algorithm k) (h : ℕ) (S T : Template k) (s : FreeCox k) : Fin k :=
  if len s + 1 ≤ h then pickerQ A T s else someFree S s

theorem free_iff_of_compatible {S T : Template k} (hc : Compatible h S T) {s : FreeCox k}
    (hs : s ∈ S.carrier) (hs1 : len s + 1 ≤ h) (c : Fin k) : S.Free s c ↔ T.Free s c := by
  unfold Free
  rw [hc.2 s hs hs1, mem_iff_of_ball_eq hc.1 (by have := len_mul_gen_le s c; omega)]

/-! ### The data of the inductive step -/

/-- The properties of `χ`, `K`, `L` used in the inductive step (observations (a)–(h) before
Lemma 15). -/
structure StepHyp (A : Algorithm k) (h : ℕ) (χ : Fin k) (K L : Template k) : Prop where
  tK : IsTemplate (h + 1) K
  tL : IsTemplate (h + 1) L
  compat : Compatible h K L
  memK : gen χ ∈ K.carrier
  memL : gen χ ∈ L.carrier
  symK : SymmAt χ K
  symL : SymmAt χ L
  matchedK : ∀ x ∈ K.carrier, K.Matched A x
  matchedL : ∀ x ∈ L.carrier, L.Matched A x
  outK : K.out A 1 ≠ some χ
  outL : L.out A 1 = some χ

theorem Good.out_extend (_hA : Good A r) {T : Template k} {P : FreeCox k → Fin k} {h' : ℕ}
    (hT : IsTemplate h' T) (hP : IsPicker T P) {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) :
    (T.extend P).out A x = T.out A (T.pos P x) := by
  simp only [out, real_extend hT hP hx]

theorem stepHyp_of_critical (hA : Good A r) (hh1 : 1 ≤ h) (hhk : h + 1 < k)
    {S T : Template k} (hcrit : IsCritical A h S T) : ∃ χ K L, StepHyp A h χ K L := by
  obtain ⟨tS, tT, hc, hC3, hC4⟩ := hcrit
  set Q := pickerQ A T
  set P := pickerP A h S T
  have hQ : IsPicker T Q := fun t ht => pickerQ_free (tT.exists_free hhk ht)
  have hP : IsPicker S P := by
    intro s hs
    unfold P pickerP
    split_ifs with hs1
    · have hsT : s ∈ T.carrier := (mem_iff_of_ball_eq hc.1 (by omega)).1 hs
      exact (free_iff_of_compatible hc hs hs1 _).2 (pickerQ_free (tT.exists_free hhk hsT))
    · exact someFree_free (tS.exists_free hhk hs)
  obtain ⟨χ, hχ⟩ := Option.ne_none_iff_exists'.1 (hA.out_ne_none tT hhk tT.1.one_mem)
  have hχC : χ ∉ colours T.carrier 1 := fun h1 => hC3 ⟨χ, h1, hχ⟩
  have hχF : T.Free 1 χ := (hA.out_cases tT tT.1.one_mem hχ).resolve_left hχC
  have hQ1 : Q 1 = χ := pickerQ_eq hχ hχF
  have hP1 : P 1 = χ := by
    unfold P pickerP; rw [ite_eq_left (by simp; omega)]; exact hQ1
  set K := S.extend P
  set L := T.extend Q
  have tK := isTemplate_extend tS hP
  have tL := isTemplate_extend tT hQ
  obtain ⟨memK, posK⟩ := pos_mul_gen_of_loop (P := P) tS.1 hP (one_mem_extend (T := S))
  obtain ⟨memL, posL⟩ := pos_mul_gen_of_loop (P := Q) tT.1 hQ (one_mem_extend (T := T))
  simp only [pos_one, hP1, hQ1, one_mul] at memK posK memL posL
  -- walks agree near `e`
  have hwalk : ∀ x, len x ≤ h → (S.extGraph P).walk 1 x = (T.extGraph Q).walk 1 x := by
    apply ColouredGraph.walk_eq_of_agree
    intro x b hx hb c
    have hbS : b ∈ S.carrier := tGraph_walk_mem tS.1.one_mem hb
    have hlen : len b ≤ len x := by have := tGraph_len_walk_le hb; simpa using this
    apply tGraph_step_congr
    · exact mem_iff_of_ball_eq hc.1 (by omega)
    · exact mem_iff_of_ball_eq hc.1 (by have := len_mul_gen_le b c; omega)
    · have : P b = Q b := by unfold P pickerP; rw [ite_eq_left (by omega)]
      simp [this]
  have hpos : ∀ x, len x ≤ h → S.pos P x = T.pos Q x := by
    intro x hx; simp only [pos, hwalk x hx]
  refine ⟨χ, K, L, tK, tL, ⟨?_, ?_⟩, memK, memL, extend_symm memK posK, extend_symm memL posL,
    ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_ball, K, L, extend, ColouredGraph.view, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
    · rwa [← hwalk x h2]
    · rwa [hwalk x h2]
  · intro x hx hx1
    rw [extend_forb, extend_forb, ← hpos x (by omega)]
    exact hc.2 _ (pos_mem tS.1 hx) (by have := len_pos_le hx; omega)
  · intro x hx
    obtain ⟨c, hcS, hout⟩ := hC4 _ (pos_mem tS.1 hx)
    refine ⟨c, (colours_extend tS.1 hx c).2 (Or.inl (mem_colours.1 hcS)), ?_⟩
    rw [hA.out_extend tS hP hx, hout]
  · intro x hx
    have hpx := pos_mem tT.1 hx
    obtain ⟨c, hout⟩ := Option.ne_none_iff_exists'.1 (hA.out_ne_none tT hhk hpx)
    refine ⟨c, (colours_extend tT.1 hx c).2 ?_, by rw [hA.out_extend tT hQ hx, hout]⟩
    rcases hA.out_cases tT hpx hout with h1 | h1
    · exact Or.inl (mem_colours.1 h1)
    · exact Or.inr (pickerQ_eq hout h1).symm
  · rw [hA.out_extend tS hP one_mem_extend, pos_one]
    obtain ⟨c, hcS, hout⟩ := hC4 1 tS.1.one_mem
    rw [hout]
    rintro h1
    cases h1
    apply hχC
    rw [mem_colours, one_mul] at hcS ⊢
    exact (mem_iff_of_ball_eq hc.1 (by simp; omega)).1 hcS
  · rw [hA.out_extend tT hQ one_mem_extend, pos_one, hχ]

/-! ### Lemma 15 -/

/-- Lemma 15: some node of the glued template is not matched along an edge of the template. -/
theorem lemma15 (hA : Good A r) {χ : Fin k} {K L : Template k} (hs : StepHyp A h χ K L) :
    ∃ y ∈ (glue χ K L).carrier, ¬ (glue χ K L).Matched A y := by
  classical
  set X := glue χ K L with hXdef
  have tX : IsTemplate (h + 1) X :=
    isTemplate_glue hs.tK.1 hs.tL.1 hs.memK hs.memL hs.tK hs.tL
  by_contra hcon
  push Not at hcon
  set R := r + 2 with hR
  -- far from `e`, the outputs in `X` agree with those in `K` and `L`
  have distK : ∀ v z, ¬ startsWith χ v → startsWith χ (v * z) → len z = len v + len (v * z) := by
    intro v z hv hvz
    have := len_inv_mul_of_startsWith hvz hv
    rwa [inv_mul_cancel_left] at this
  have distL : ∀ v z, startsWith χ v → ¬ startsWith χ (v * z) → len z = len (v * z) + len v := by
    intro v z hv hvz
    have := len_inv_mul_of_startsWith hv hvz
    rwa [mul_inv_rev, inv_mul_cancel_right, len_inv] at this
  have farK : ∀ v ∈ K.carrier, ¬ startsWith χ v → R ≤ len v → X.out A v = K.out A v := by
    intro v hv hst hlen
    apply hA.out_eq_of_agree ((mem_glue_of_not hst).2 hv)
    · intro z hz
      by_cases h1 : startsWith χ (v * z)
      · have := distK v z hst h1; omega
      · exact mem_glue_of_not h1
    · intro z hz _
      by_cases h1 : startsWith χ (v * z)
      · have := distK v z hst h1; omega
      · exact glue_forb_of_not h1
  have farL : ∀ v ∈ L.carrier, startsWith χ v → R ≤ len v → X.out A v = L.out A v := by
    intro v hv hst hlen
    apply hA.out_eq_of_agree ((mem_glue_of_starts hst).2 hv)
    · intro z hz
      by_cases h1 : startsWith χ (v * z)
      · exact mem_glue_of_starts h1
      · have := distL v z hst h1; omega
    · intro z hz _
      by_cases h1 : startsWith χ (v * z)
      · exact glue_forb_of_starts h1
      · have := distL v z hst h1; omega
  set μX := partner A X
  set μK := partner A K
  set μL := partner A L
  have μfarK : ∀ v ∈ K.carrier, ¬ startsWith χ v → R ≤ len v → μX v = μK v := by
    intro v hv hst hlen; simp only [μX, μK, partner, farK v hv hst hlen]
  have μfarL : ∀ v ∈ L.carrier, startsWith χ v → R ≤ len v → μX v = μL v := by
    intro v hv hst hlen; simp only [μX, μL, partner, farL v hv hst hlen]
  have specX : ∀ v ∈ X.carrier, μX v ∈ X.carrier ∧ μX (μX v) = v ∧ μX v ≠ v := fun v hv =>
    let s := hA.partner_spec tX hv (hcon v hv); ⟨s.1, s.2.1, s.2.2.1⟩
  have specK : ∀ v ∈ K.carrier, μK v ∈ K.carrier ∧ μK (μK v) = v ∧ μK v ≠ v := fun v hv =>
    let s := hA.partner_spec hs.tK hv (hs.matchedK v hv); ⟨s.1, s.2.1, s.2.2.1⟩
  have specL : ∀ v ∈ L.carrier, μL v ∈ L.carrier ∧ μL (μL v) = v ∧ μL v ≠ v := fun v hv =>
    let s := hA.partner_spec hs.tL hv (hs.matchedL v hv); ⟨s.1, s.2.1, s.2.2.1⟩
  -- the matching of `K` does not use the edge `{e, χ}`
  have closK : ∀ v ∈ K.carrier, ¬ startsWith χ v → ¬ startsWith χ (μK v) := by
    intro v hv hst h1
    obtain ⟨c, -, hout⟩ := hs.matchedK v hv
    have e1 : μK v = v * gen c := by simp [μK, partner, hout]
    rw [e1] at h1
    obtain ⟨rfl, h2 | rfl⟩ := startsWith_mul_gen (c := χ) (c' := c) (x := v) (by tauto)
    · subst h2; exact hs.outK hout
    · exact hst (startsWith_gen.2 rfl)
  have hμχ : μL (gen χ) = 1 := by
    have := hA.out_mul_gen hs.tL hs.tL.1.one_mem hs.outL (by simpa using hs.memL)
    rw [one_mul] at this
    simp [μL, partner, this]
  have closL : ∀ v ∈ L.carrier, startsWith χ v → v ≠ gen χ → startsWith χ (μL v) := by
    intro v hv hst hne
    by_contra h1
    obtain ⟨c, -, hout⟩ := hs.matchedL v hv
    have e1 : μL v = v * gen c := by simp [μL, partner, hout]
    rw [e1] at h1
    obtain ⟨rfl, h2 | rfl⟩ := startsWith_mul_gen (c := χ) (c' := c) (x := v) (by tauto)
    · subst h2; exact not_startsWith_one _ hst
    · exact hne rfl
  have μL_ne : ∀ v ∈ L.carrier, startsWith χ v → μL v ≠ gen χ := by
    intro v hv hst h1
    have := (specL v hv).2.1
    rw [h1, hμχ] at this
    subst this
    exact not_startsWith_one χ hst
  -- the far parts
  let K3 : FreeCox k → Prop := fun v =>
    v ∈ K.carrier ∧ ¬ startsWith χ v ∧ R ≤ len v ∧ R ≤ len (μK v)
  let L3 : FreeCox k → Prop := fun v =>
    v ∈ L.carrier ∧ startsWith χ v ∧ R ≤ len v ∧ R ≤ len (μL v)
  have K3_swap : ∀ v, K3 v → K3 (μK v) := by
    rintro v ⟨h1, h2, h3, h4⟩
    exact ⟨(specK v h1).1, closK v h1 h2, h4, by rw [(specK v h1).2.1]; exact h3⟩
  have L3_swap : ∀ v, L3 v → L3 (μL v) := by
    rintro v ⟨h1, h2, h3, h4⟩
    have hne : v ≠ gen χ := by rintro rfl; simp at h3; omega
    exact ⟨(specL v h1).1, closL v h1 h2 hne, h4, by rw [(specL v h1).2.1]; exact h3⟩
  set B := (finite_len_le (k := k) R).toFinset
  set N := B.filter (fun v => v ∈ X.carrier ∧ ¬ K3 v ∧ ¬ L3 v)
  have memN : ∀ v, v ∈ N ↔ v ∈ X.carrier ∧ ¬ K3 v ∧ ¬ L3 v := by
    intro v
    simp only [N, B, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · exact fun h1 => h1.2
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h1, h2, h3⟩
      by_cases hst : startsWith χ v
      · have hv := (mem_glue_of_starts hst).1 h1
        have : len v ≤ len (μL v) + 1 := len_le_len_partner A L v
        by_contra hlt
        exact h3 ⟨hv, hst, by omega, by omega⟩
      · have hv := (mem_glue_of_not hst).1 h1
        have : len v ≤ len (μK v) + 1 := len_le_len_partner A K v
        by_contra hlt
        exact h2 ⟨hv, hst, by omega, by omega⟩
  -- (1) `μX` is a fixed-point-free involution on `N`
  have evenN : Even N.card := by
    apply even_card_of_involution N μX
    · intro v hv
      rw [memN] at hv ⊢
      obtain ⟨hvX, hK3, hL3⟩ := hv
      refine ⟨(specX v hvX).1, ?_, ?_⟩
      · intro hw
        apply hK3
        have e1 := μfarK _ hw.1 hw.2.1 hw.2.2.1
        rw [(specX v hvX).2.1] at e1
        rw [e1]
        exact K3_swap _ hw
      · intro hw
        apply hL3
        have e1 := μfarL _ hw.1 hw.2.1 hw.2.2.1
        rw [(specX v hvX).2.1] at e1
        rw [e1]
        exact L3_swap _ hw
    · intro v hv; exact (specX v ((memN v).1 hv).1).2.1
    · intro v hv; exact (specX v ((memN v).1 hv).1).2.2
  -- (2) `μK` is a fixed-point-free involution on `N ∩ K₁`
  have evenK : Even (N.filter (fun v => ¬ startsWith χ v)).card := by
    apply even_card_of_involution _ μK
    · intro v hv
      rw [Finset.mem_filter, memN] at hv ⊢
      obtain ⟨⟨hvX, hK3, -⟩, hst⟩ := hv
      have hvK := (mem_glue_of_not hst).1 hvX
      have hst' := closK v hvK hst
      refine ⟨⟨(mem_glue_of_not hst').2 (specK v hvK).1, ?_, fun h1 => hst' h1.2.1⟩, hst'⟩
      intro h1
      apply hK3
      have := K3_swap _ h1
      rwa [(specK v hvK).2.1] at this
    · intro v hv
      rw [Finset.mem_filter, memN] at hv
      exact (specK v ((mem_glue_of_not hv.2).1 hv.1.1)).2.1
    · intro v hv
      rw [Finset.mem_filter, memN] at hv
      exact (specK v ((mem_glue_of_not hv.2).1 hv.1.1)).2.2
  -- (3) `μL` is a fixed-point-free involution on `N ∩ L₁ - χ`
  have evenL : Even ((N.filter (fun v => startsWith χ v)).erase (gen χ)).card := by
    apply even_card_of_involution _ μL
    · intro v hv
      rw [Finset.mem_erase, Finset.mem_filter, memN] at hv ⊢
      obtain ⟨hne, ⟨hvX, -, hL3⟩, hst⟩ := hv
      have hvL := (mem_glue_of_starts hst).1 hvX
      have hst' := closL v hvL hst hne
      refine ⟨μL_ne v hvL hst, ⟨(mem_glue_of_starts hst').2 (specL v hvL).1,
        fun h1 => h1.2.1 hst', ?_⟩, hst'⟩
      intro h1
      apply hL3
      have := L3_swap _ h1
      rwa [(specL v hvL).2.1] at this
    · intro v hv
      rw [Finset.mem_erase, Finset.mem_filter, memN] at hv
      exact (specL v ((mem_glue_of_starts hv.2.2).1 hv.2.1.1)).2.1
    · intro v hv
      rw [Finset.mem_erase, Finset.mem_filter, memN] at hv
      exact (specL v ((mem_glue_of_starts hv.2.2).1 hv.2.1.1)).2.2
  -- `χ ∈ N ∩ L₁`
  have hχN : gen χ ∈ N.filter (fun v => startsWith χ v) := by
    rw [Finset.mem_filter, memN]
    have hst : startsWith χ (gen χ) := startsWith_gen.2 rfl
    refine ⟨⟨(mem_glue_of_starts hst).2 hs.memL, fun h1 => h1.2.1 hst, ?_⟩, hst⟩
    rintro ⟨-, -, h1, -⟩
    simp at h1; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := N) (fun v => startsWith χ v)
  rw [← Finset.card_erase_add_one hχN] at hsplit
  obtain ⟨a, ha⟩ := evenN
  obtain ⟨b, hb⟩ := evenK
  obtain ⟨c, hc⟩ := evenL
  omega

/-! ### Lemma 16 and the induction -/

/-- Lemma 16: an `h`-critical pair with `1 ≤ h < d` yields an `(h+1)`-critical pair. -/
theorem exists_critical_succ (hA : Good A r) (hh1 : 1 ≤ h) (hhk : h + 1 < k)
    {S T : Template k} (hcrit : IsCritical A h S T) :
    ∃ S' T' : Template k, IsCritical A (h + 1) S' T' := by
  obtain ⟨χ, K, L, hs⟩ := stepHyp_of_critical hA hh1 hhk hcrit
  obtain ⟨y, hyX, hy⟩ := lemma15 hA hs
  have tX : IsTemplate (h + 1) (glue χ K L) :=
    isTemplate_glue hs.tK.1 hs.tL.1 hs.memK hs.memL hs.tK hs.tL
  by_cases hst : startsWith χ y
  · have hyL := (mem_glue_of_starts hst).1 hyX
    refine ⟨y⁻¹ • L, y⁻¹ • glue χ K L, hs.tL.smul hyL, tX.smul hyX,
      compatible_glue_right hs.compat hst, ?_, ?_⟩
    · rw [matched_inv_smul, mul_one]; exact hy
    · intro s hs'
      rw [smul_carrier, mem_inv_smul] at hs'
      rw [matched_inv_smul]
      exact hs.matchedL _ hs'
  · have hyK := (mem_glue_of_not hst).1 hyX
    refine ⟨y⁻¹ • K, y⁻¹ • glue χ K L, hs.tK.smul hyK, tX.smul hyX,
      compatible_glue_left hs.compat hs.symK hs.symL hst, ?_, ?_⟩
    · rw [matched_inv_smul, mul_one]; exact hy
    · intro s hs'
      rw [smul_carrier, mem_inv_smul] at hs'
      rw [matched_inv_smul]
      exact hs.matchedK _ hs'

/-- By induction: there is an `h`-critical pair for every `1 ≤ h ≤ d = k - 1`. -/
theorem exists_critical (hk : 3 ≤ k) (hA : Good A r) :
    ∀ h, 1 ≤ h → h + 1 ≤ k → ∃ S T : Template k, IsCritical A h S T := by
  intro h hh1 hhk
  induction h with
  | zero => omega
  | succ h ih =>
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · exact exists_critical_one hk hA
    · obtain ⟨S, T, hST⟩ := ih hpos (by omega)
      exact exists_critical_succ hA hpos (by omega) hST

end Papers.PODC2012.MaximalMatching
