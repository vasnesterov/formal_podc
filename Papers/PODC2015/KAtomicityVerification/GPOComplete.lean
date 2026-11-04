import Papers.PODC2015.KAtomicityVerification.GPOCorrect

/-!
# Completeness of GPO: Lemma 4.5 and Theorem 4.10

If `H` is `k`-atomic (and satisfies Assumptions 3.4 and 4.1), GPO never finds an overfull
obligation set. Following the paper, we keep the predicate `P(x)`:

* (a) the constructed suffix extends to some `k`-atomic value order (`PA`);
* (b) every value of `B[i]` occupies one of the `i` positions immediately to the left of the
  suffix in *every* `k`-atomic value order extending it (`PB`);
* (c) is the field `oblig` of `Inv` (it holds for every run, `k`-atomic or not).

Value orders are represented by bijections `σ : V ≃ Fin |V|` counted from the right
(`σ v = 0` is the last value), so "`T` is a suffix of `T'`" becomes `Ext st σ`.
-/

set_option linter.unusedSectionVars false

namespace Podc.KAtomicityVerification

open Finset

variable {V R : Type*} [Fintype V] [LinearOrder V] [Fintype R]

namespace History

variable (H : History V R)

/-- A `k`-atomic value order, read from right to left: `σ v` is the distance of `v` from the
right end. `G_W` edges point right, `G_R` edges point left by less than `k`. -/
def IsRevOrder (k : ℕ) (σ : V ≃ Fin (Fintype.card V)) : Prop :=
  (∀ a b, H.EW a b → (σ b : ℕ) < σ a) ∧ (∀ a b, H.ER a b → (σ b : ℕ) < σ a + k)

/-- The value order `σ` has the constructed sequence `st.T` as a suffix. -/
def Ext (st : GState V) (σ : V ≃ Fin (Fintype.card V)) : Prop :=
  ∀ v, (v ∈ st.T ↔ (σ v : ℕ) < st.T.length) ∧ (v ∈ st.T → (σ v : ℕ) = st.rpos v)

/-- Part (b) of the predicate `P(x)` of Lemma 4.5. -/
def PB (k : ℕ) (st : GState V) : Prop :=
  ∀ σ, H.IsRevOrder k σ → Ext st σ → ∀ i, 1 ≤ i → i ≤ k - 1 → ∀ z ∈ st.B i,
    st.T.length ≤ (σ z : ℕ) ∧ (σ z : ℕ) < st.T.length + i

variable {H}

/-- A `k`-atomic history has a `k`-atomic value order (Lemma 3.8), here read from the right. -/
lemma exists_revOrder (hA : H.Assumption34) {k : ℕ} (hk : 0 < k) (h : H.KAtomic k) :
    ∃ σ, H.IsRevOrder k σ := by
  obtain ⟨T, hT⟩ := (kAtomic_iff_exists_valueOrder hA hk).1 h
  have hlen : T.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hT.nodup]
    congr 1
    ext v; simp [hT.complete v]
  have hl : ∀ v, T.idxOf v < T.length := fun v => List.idxOf_lt_length_iff.2 (hT.complete v)
  let g : V → Fin (Fintype.card V) := fun v =>
    ⟨Fintype.card V - 1 - T.idxOf v, by have := hl v; omega⟩
  have hg : Function.Injective g := by
    intro a b h
    simp only [g, Fin.mk.injEq] at h
    have ha := hl a; have hb := hl b
    have : T.idxOf a = T.idxOf b := by omega
    have e1 := hT.getElem_idxOf a
    have e2 := hT.getElem_idxOf b
    grind
  let σ := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp⟩)
  have hr := hT.rank
  refine ⟨σ, fun a b hab => ?_, fun a b hab => ?_⟩
  · have := hr.2.1 a b hab
    simp only at this
    have := hl a; have := hl b
    simp only [σ, Equiv.ofBijective_apply, g]
    omega
  · have := hr.2.2 a b hab
    simp only at this
    have := hl a; have := hl b
    simp only [σ, Equiv.ofBijective_apply, g]
    omega

lemma ext_init (σ : V ≃ Fin (Fintype.card V)) : Ext GState.init σ := by
  intro v; simp [GState.init]

lemma PB_init (k : ℕ) : H.PB k GState.init := by
  intro σ _ _ i _ _ z hz; simp [GState.init] at hz

/-- `Ext` for the next state is `Ext` for the current state plus "the chosen value is next". -/
lemma ext_next_iff {k : ℕ} {st : GState V} (hI : H.Inv k st) (hU : st.U.Nonempty)
    (σ : V ≃ Fin (Fintype.card V)) :
    Ext (H.next k st hU) σ ↔ Ext st σ ∧ (σ (H.choice k st hU) : ℕ) = st.T.length := by
  set v := H.choice k st hU
  have hvU : v ∈ st.U := choice_mem hU hI.BU
  have hvT : v ∉ st.T := fun h => (hI.memT v).1 h hvU
  have hneT : ∀ u ∈ st.T, u ≠ v := fun u hu h => hvT (h ▸ hu)
  have hrv : (H.next k st hU).rpos v = st.T.length := rpos_next_self st hU
  have hru : ∀ u ∈ st.T, (H.next k st hU).rpos u = st.rpos u :=
    fun u hu => rpos_next_of_mem st hU (hneT u hu) hu
  have hmemT' : ∀ u, u ∈ (H.next k st hU).T ↔ u = v ∨ u ∈ st.T := by
    intro u; rw [next_T]; exact List.mem_cons
  have hlen : (H.next k st hU).T.length = st.T.length + 1 := by simp [next_T]
  constructor
  · intro h
    have hσv : (σ v : ℕ) = st.T.length := by
      rw [(h v).2 ((hmemT' v).2 (Or.inl rfl)), hrv]
    refine ⟨fun u => ⟨⟨fun huT => ?_, fun hlt => ?_⟩, fun hu => ?_⟩, hσv⟩
    · rw [(h u).2 ((hmemT' u).2 (Or.inr huT)), hru u huT]
      exact rpos_lt huT
    · have := (h u).1.2 (by rw [hlen]; omega)
      rcases (hmemT' u).1 this with rfl | h'
      · omega
      · exact h'
    · rw [← hru u hu]; exact (h u).2 ((hmemT' u).2 (Or.inr hu))
  · rintro ⟨h, hσv⟩ u
    constructor
    · rw [hmemT', hlen, (h u).1]
      constructor
      · rintro (rfl | h') <;> omega
      · intro hlt
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
        · exact Or.inr h'
        · left; exact σ.injective (Fin.ext (by omega))
    · intro hu
      rcases (hmemT' u).1 hu with rfl | hu
      · rw [hrv, hσv]
      · rw [hru u hu]; exact (h u).2 hu

/-- `P(x+1)`-(b) of Lemma 4.5. -/
lemma PB_next {k : ℕ} (hk : 2 ≤ k) {st : GState V} (hI : H.Inv k st) (hU : st.U.Nonempty)
    (hPB : H.PB k st) : H.PB k (H.next k st hU) := by
  intro σ hσ hext i hi1 hik z hz
  rw [ext_next_iff hI hU] at hext
  obtain ⟨hext, hσv⟩ := hext
  have hlen : (H.next k st hU).T.length = st.T.length + 1 := by simp [next_T]
  rw [hlen]
  obtain ⟨hzv, hzU, hz3⟩ := next_B_sub hk st hU hI.BU hi1 hik hz
  have hzx : (σ z : ℕ) ≠ st.T.length := by
    intro h; apply hzv; exact σ.injective (Fin.ext (by omega))
  have hzT : z ∉ st.T := fun h => (hI.memT z).1 h hzU
  have hzge : st.T.length ≤ (σ z : ℕ) := by
    by_contra h; exact hzT ((hext z).1.2 (by omega))
  rcases hz3 with ⟨hlt, h⟩ | ⟨rfl, h | h | h⟩
  · have := hPB σ hσ hext (i + 1) (by omega) (by omega) z h
    omega
  · have := hPB σ hσ hext (k - 1) (by omega) le_rfl z h
    omega
  · obtain ⟨-, r, hr, hzr⟩ := (mem_setW (H := H)).1 h
    have := hσ.2 _ _ ⟨fun h => hzv h.symm, r, hr, hzr⟩
    omega
  · obtain ⟨-, y, hy, hyz⟩ := (mem_setW' (H := H)).1 h
    obtain ⟨hyU, r, hr, hyr⟩ := (mem_setW (H := H)).1 hy
    have hyv : y ≠ H.choice k st hU := (mem_erase.1 hyU).1
    have := hσ.2 _ _ ⟨fun h => hyv h.symm, r, hr, hyr⟩
    have := hσ.1 _ _ hyz
    omega

lemma hb_of_wf_le {a b : V} {r : R} (h1 : H.wf a ≤ H.wf b) (h2 : H.hb (.inl b) (.inr r)) :
    H.hb (.inl a) (.inr r) := by
  unfold hb at *; unfold wf at h1; omega

lemma wf_lt_of_EW {a b : V} (h : H.EW a b) : H.wf a < H.wf b :=
  lt_trans h (H.s_lt_f _)

lemma EW_of_wf_le {a b c : V} (h1 : H.wf a ≤ H.wf b) (h2 : H.EW b c) : H.EW a c := by
  unfold EW hb at *; unfold wf at h1; omega

/-- `P(x+1)`-(a) of Lemma 4.5: the suffix extended by the greedy choice still extends to a
`k`-atomic value order. This is the exchange argument of Claims 4.6–4.9. -/
lemma exists_ext_next (h41 : H.Assumption41) {k : ℕ} (hk : 2 ≤ k) {st : GState V}
    (hI : H.Inv k st) (hU : st.U.Nonempty)
    (hPA : ∃ σ, H.IsRevOrder k σ ∧ Ext st σ) (hPB : H.PB k st) :
    ∃ σ, H.IsRevOrder k σ ∧ Ext (H.next k st hU) σ := by
  classical
  set v' := H.choice k st hU with hv'
  set x := st.T.length with hx
  have hv'U : v' ∈ st.U := choice_mem hU hI.BU
  have hex : ∃ m, ∃ σ, H.IsRevOrder k σ ∧ Ext st σ ∧ (σ v' : ℕ) = m := by
    obtain ⟨σ, h1, h2⟩ := hPA; exact ⟨_, σ, h1, h2, rfl⟩
  obtain ⟨σ, hσ, hext, hm⟩ := Nat.find_spec hex
  set m := Nat.find hex with hmdef
  have hmin : ∀ σ' : V ≃ Fin (Fintype.card V), H.IsRevOrder k σ' → Ext st σ' →
      m ≤ (σ' v' : ℕ) :=
    fun σ' h1 h2 => Nat.find_min' hex ⟨σ', h1, h2, rfl⟩
  have hUiff : ∀ u, u ∈ st.U ↔ x ≤ (σ u : ℕ) := by
    intro u
    have h1 : u ∈ st.U ↔ u ∉ st.T :=
      ⟨fun h h' => (hI.memT u).1 h' h, fun h => by by_contra h'; exact h ((hI.memT u).2 h')⟩
    rw [h1, (hext u).1]; omega
  have hv'T : v' ∉ st.T := fun h => (hI.memT v').1 h hv'U
  have hxm : x ≤ m := by have := (hUiff v').1 hv'U; omega
  by_cases hmx : m = x
  · exact ⟨σ, hσ, (ext_next_iff hI hU σ).2 ⟨hext, by rw [← hv', ← hx]; omega⟩⟩
  have hmN : m < Fintype.card V := by have := (σ v').2; omega
  set v0 := σ.symm ⟨x, by omega⟩ with hv0
  have hσv0 : (σ v0 : ℕ) = x := by simp [v0]
  have hv0ne : v0 ≠ v' := fun h => by rw [h] at hσv0; omega
  -- Claim 4.6 (case of line 7) and Claim 4.7
  have hF_bound : ∀ hF : (fullIdx k st).Nonempty, m < x + (fullIdx k st).min' hF := by
    intro hF
    have hmem := min'_mem _ hF
    rw [mem_fullIdx] at hmem
    have := hPB σ hσ hext _ hmem.1 hmem.2.1 v' (choice_of_full hU hF).1
    omega
  have hmax : ∀ u, x ≤ (σ u : ℕ) → (σ u : ℕ) ≤ m → H.wf u ≤ H.wf v' := by
    intro u hu1 hu2
    by_cases hF : (fullIdx k st).Nonempty
    · obtain ⟨-, hmaxB⟩ := choice_of_full (H := H) hU hF
      have hmem := min'_mem _ hF
      rw [mem_fullIdx] at hmem
      have himg : (st.B ((fullIdx k st).min' hF)).image (fun z => (σ z : ℕ)) =
          Ico x (x + (fullIdx k st).min' hF) := by
        apply eq_of_subset_of_card_le
        · intro n hn
          simp only [mem_image] at hn
          obtain ⟨z, hz, rfl⟩ := hn
          have := hPB σ hσ hext _ hmem.1 hmem.2.1 z hz
          simp only [mem_Ico]; omega
        · rw [card_image_of_injective _ (fun a b h => σ.injective (Fin.ext h)), Nat.card_Ico,
            hmem.2.2]
          omega
      have hu : (σ u : ℕ) ∈ Ico x (x + (fullIdx k st).min' hF) := by
        have := hF_bound hF; simp only [mem_Ico]; omega
      rw [← himg, mem_image] at hu
      obtain ⟨z, hz, hzu⟩ := hu
      have : z = u := σ.injective (Fin.ext hzu)
      subst this
      exact hmaxB z hz
    · exact (choice_of_not_full (H := H) hU hF).2 u ((hUiff u).2 hu1)
  -- Claim 4.6
  have hmk : m < x + k := by
    by_cases hF : (fullIdx k st).Nonempty
    · have := hF_bound hF
      have hmem := min'_mem _ hF
      rw [mem_fullIdx] at hmem
      omega
    · obtain ⟨r, hr, hv'r⟩ := h41 v'
      have hle := hmax v0 (by omega) (by omega)
      have hER : H.ER v0 v' := ⟨hv0ne, r, hr, hb_of_wf_le hle hv'r⟩
      have := hσ.2 _ _ hER
      omega
  set s := m - x with hs
  -- Claim 4.8
  have claim48 : ∀ v'', x ≤ (σ v'' : ℕ) → (σ v'' : ℕ) < m →
      (∀ a b, H.EW a b → (σ (Equiv.swap v' v'' b) : ℕ) < σ (Equiv.swap v' v'' a)) →
      v'' ∈ st.B s := by
    intro v'' h1 h2 htopo
    have hne : v'' ≠ v' := fun h => by rw [h] at h2; omega
    set σ'' := (Equiv.swap v' v'').trans σ with hσ''
    have hσ''app : ∀ u, σ'' u = σ (Equiv.swap v' v'' u) := fun u => rfl
    have hv''T : v'' ∉ st.T := fun h => by have := (hext v'').1.1 h; omega
    have hext'' : Ext st σ'' := by
      intro u
      rw [hσ''app]
      by_cases hu1 : u = v'
      · rw [hu1, Equiv.swap_apply_left]
        exact ⟨⟨fun h => absurd h hv'T, fun h => by omega⟩, fun h => absurd h hv'T⟩
      by_cases hu2 : u = v''
      · rw [hu2, Equiv.swap_apply_right]
        exact ⟨⟨fun h => absurd h hv''T, fun h => by omega⟩, fun h => absurd h hv''T⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hu1 hu2]; exact hext u
    have hnot : ¬ H.IsRevOrder k σ'' := by
      intro h
      have := hmin σ'' h hext''
      rw [hσ''app, Equiv.swap_apply_left] at this
      omega
    have : ∃ a b, H.ER a b ∧ (σ'' a : ℕ) + k ≤ σ'' b := by
      by_contra hcon
      push Not at hcon
      exact hnot ⟨fun a b h => htopo a b h, fun a b h => hcon a b h⟩
    obtain ⟨a, b, hab, hlt'⟩ := this
    simp only [hσ''app] at hlt'
    have hσER := hσ.2
    by_cases ha1 : a = v'
    · subst ha1
      rw [Equiv.swap_apply_left] at hlt'
      by_cases hb1 : b = v'
      · exact absurd hb1.symm hab.1
      by_cases hb2 : b = v''
      · subst hb2; rw [Equiv.swap_apply_right] at hlt'; omega
      · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at hlt'
        obtain ⟨-, r, hr, hbr⟩ := hab
        have hle := hmax v0 (by omega) (by omega)
        have hv0b : v0 ≠ b := fun h => by rw [← h] at hlt'; omega
        have := hσER v0 b ⟨hv0b, r, hr, hb_of_wf_le hle hbr⟩
        omega
    by_cases ha2 : a = v''
    · subst ha2
      rw [Equiv.swap_apply_right] at hlt'
      by_cases hb1 : b = v'
      · subst hb1; rw [Equiv.swap_apply_left] at hlt'; omega
      by_cases hb2 : b = a
      · exact absurd hb2.symm hab.1
      · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at hlt'
        have := hσER _ _ hab
        omega
    rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2] at hlt'
    by_cases hb1 : b = v'
    · subst hb1
      rw [Equiv.swap_apply_left] at hlt'
      have := hσER _ _ hab
      omega
    by_cases hb2 : b = v''
    · subst hb2
      rw [Equiv.swap_apply_right] at hlt'
      have haT : a ∈ st.T := (hext a).1.2 (by omega)
      obtain ⟨-, hB⟩ := hI.oblig a b haT hv''T hab
      have hra : (σ a : ℕ) = st.rpos a := (hext a).2 haT
      have := hB (k - 1 - s) (by omega)
      rwa [show k - 1 - (k - 1 - s) = s by omega] at this
    · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at hlt'
      have := hσER _ _ hab
      omega
  -- Claim 4.8 applies when no value of `S` has a `G_W` edge into `v''`
  have hno : ∀ v'', x ≤ (σ v'' : ℕ) → (σ v'' : ℕ) < m →
      (∀ c, x ≤ (σ c : ℕ) → (σ c : ℕ) ≤ m → ¬ H.EW c v'') → v'' ∈ st.B s := by
    intro v'' h1 h2 hc
    have hne : v'' ≠ v' := fun h => by rw [h] at h2; omega
    have hσEW := hσ.1
    apply claim48 v'' h1 h2
    intro a b hab
    by_cases ha1 : a = v'
    · subst ha1
      rw [Equiv.swap_apply_left]
      by_cases hb2 : b = v''
      · subst hb2
        have := wf_lt_of_EW hab
        have := hmax b h1 h2.le
        omega
      have hb1 : b ≠ v' := fun h => by rw [h] at hab; exact EW_irrefl _ hab
      rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
      have := hσEW _ _ hab
      have hwf := wf_lt_of_EW hab
      by_contra hcon
      have := hmax b (by omega) (by omega)
      omega
    by_cases ha2 : a = v''
    · subst ha2
      rw [Equiv.swap_apply_right]
      by_cases hb1 : b = v'
      · subst hb1; rw [Equiv.swap_apply_left]; omega
      have hb2 : b ≠ a := fun h => by rw [h] at hab; exact EW_irrefl _ hab
      rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
      have := hσEW _ _ hab
      omega
    rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2]
    by_cases hb1 : b = v'
    · subst hb1; rw [Equiv.swap_apply_left]
      have := hσEW _ _ hab
      omega
    by_cases hb2 : b = v''
    · subst hb2; rw [Equiv.swap_apply_right]
      have := hσEW _ _ hab
      by_contra hcon
      exact hc a (by omega) (by omega) hab
    · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
      exact hσEW _ _ hab
  -- Claim 4.9
  have claim49 : ∀ v'', x ≤ (σ v'' : ℕ) → (σ v'' : ℕ) < m → v'' ∈ st.B s := by
    intro v'' h1 h2
    by_cases hc : ∃ c, x ≤ (σ c : ℕ) ∧ (σ c : ℕ) ≤ m ∧ H.EW c v''
    swap
    · push Not at hc
      exact hno v'' h1 h2 hc
    obtain ⟨c, hc1, hc2, hcv⟩ := hc
    set Z := univ.filter (fun u => x ≤ (σ u : ℕ) ∧ (σ u : ℕ) < m) with hZ
    have hZne : Z.Nonempty := ⟨v'', by simp [Z, h1, h2]⟩
    obtain ⟨z, hzZ, hzmin⟩ := Z.exists_min_image H.wf hZne
    simp only [Z, mem_filter, mem_univ, true_and] at hzZ
    have hzB : z ∈ st.B s := by
      apply hno z hzZ.1 hzZ.2
      intro c' hc'1 hc'2 hc'z
      have hlt := wf_lt_of_EW hc'z
      by_cases hc'm : (σ c' : ℕ) = m
      · have : c' = v' := σ.injective (Fin.ext (by omega))
        subst this
        have := hmax z hzZ.1 hzZ.2.le
        omega
      · have := hzmin c' (by simp only [Z, mem_filter, mem_univ, true_and]; omega)
        omega
    by_cases hzv : z = v''
    · rw [← hzv]; exact hzB
    have hcm : (σ c : ℕ) ≠ m := by
      intro h
      have : c = v' := σ.injective (Fin.ext (by omega))
      subst this
      have := hmax v'' h1 h2.le
      have := wf_lt_of_EW hcv
      omega
    have hzc : H.wf z ≤ H.wf c := hzmin c (by simp only [Z, mem_filter, mem_univ, true_and]; omega)
    exact hI.closed s z hzB v'' ((hUiff v'').2 h1) (EW_of_wf_le hzc hcv)
  -- counting: `S \ {v'}` has `s` elements, all in `B[s]`, so `B[s]` is full
  have hs1 : 1 ≤ s := by omega
  have hsk : s ≤ k - 1 := by omega
  have hsub : univ.filter (fun u => x ≤ (σ u : ℕ) ∧ (σ u : ℕ) < m) ⊆ st.B s := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    exact claim49 u hu.1 hu.2
  have hcardS : (univ.filter (fun u => x ≤ (σ u : ℕ) ∧ (σ u : ℕ) < m)).card = s := by
    have himg : (univ.filter (fun u => x ≤ (σ u : ℕ) ∧ (σ u : ℕ) < m)).image
        (fun u => (σ u : ℕ)) = Ico x m := by
      ext n
      simp only [mem_image, mem_filter, mem_univ, true_and, mem_Ico]
      constructor
      · rintro ⟨u, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨σ.symm ⟨n, by omega⟩, by simp; omega, by simp⟩
    rw [← card_image_of_injective _ (fun a b h => σ.injective (Fin.ext h)), himg, Nat.card_Ico]
  have hBs : (st.B s).card = s :=
    le_antisymm (hI.card s) (by have := card_le_card hsub; omega)
  have hsF : s ∈ fullIdx k st := mem_fullIdx.2 ⟨hs1, hsk, hBs⟩
  have hF : (fullIdx k st).Nonempty := ⟨s, hsF⟩
  have := hF_bound hF
  have := min'_le _ _ hsF
  omega

/-- `P(x+1)`-(b) bounds the obligation sets: no overfull set appears. -/
lemma not_overfull_next {k : ℕ} {st : GState V} (hU : st.U.Nonempty)
    (hPA : ∃ σ, H.IsRevOrder k σ ∧ Ext (H.next k st hU) σ) (hPB : H.PB k (H.next k st hU)) :
    ¬ Overfull k (H.next k st hU) := by
  obtain ⟨σ, hσ, hext⟩ := hPA
  rintro ⟨i, hi, hlt⟩
  rw [mem_Icc] at hi
  have hsub : ((H.next k st hU).B i).image (fun z => (σ z : ℕ)) ⊆
      Ico (H.next k st hU).T.length ((H.next k st hU).T.length + i) := by
    intro n hn
    simp only [mem_image] at hn
    obtain ⟨z, hz, rfl⟩ := hn
    have := hPB σ hσ hext i hi.1 hi.2 z hz
    simp only [mem_Ico]; omega
  have := card_le_card hsub
  rw [card_image_of_injective _ (fun a b h => σ.injective (Fin.ext h)), Nat.card_Ico] at this
  omega

/-- The core of Lemma 4.5: from a state satisfying `P(x)`, all remaining iterations succeed. -/
lemma run_isSome (h41 : H.Assumption41) {k : ℕ} (hk : 2 ≤ k) :
    ∀ (n : ℕ) {st : GState V}, H.Inv k st → (∃ σ, H.IsRevOrder k σ ∧ Ext st σ) → H.PB k st →
      (H.run k n st).isSome
  | 0, st, _, _, _ => rfl
  | n + 1, st, hI, hPA, hPB => by
    by_cases hU : st.U.Nonempty
    · have hPA' := exists_ext_next h41 hk hI hU hPA hPB
      have hPB' := PB_next hk hI hU hPB
      have hO := not_overfull_next hU hPA' hPB'
      have hstep : H.step k st = some (H.next k st hU) := by
        unfold step; rw [dite_eq_left hU, ite_eq_right hO]
      simp only [run, hstep, Option.bind_some]
      exact run_isSome h41 hk n (inv_next hk hI hU hO) hPA' hPB'
    · have hstep : H.step k st = some st := by unfold step; rw [dite_eq_right hU]
      simp only [run, hstep, Option.bind_some]
      exact run_isSome h41 hk n hI hPA hPB

/-- **Lemma 4.5** of [Golab–Li–López-Ortiz–Nishimura]. If `H` is `k`-atomic then GPO outputs
YES (for `k ≥ 2`, under Assumptions 3.4 and 4.1). -/
theorem lemma_4_5 (hA : H.Assumption34) (h41 : H.Assumption41) {k : ℕ} (hk : 2 ≤ k)
    (h : H.KAtomic k) : H.gpo k = true := by
  obtain ⟨σ, hσ⟩ := exists_revOrder hA (by omega) h
  exact run_isSome h41 hk _ (inv_init k) ⟨σ, hσ, ext_init σ⟩ (PB_init k)

/-- **Lemma 4.2** of [Golab–Li–López-Ortiz–Nishimura]: after every iteration `x` of the outer
loop (that did not return NO), (a) every value is in exactly one of `T_x`, `U_x`, and
(b) `v ∈ B_x[i]`, `v' ∈ U_x` and `w(v) <_H w(v')` imply `v' ∈ B_x[i]`. -/
theorem lemma_4_2 {k : ℕ} (hk : 2 ≤ k) {x : ℕ} {st : GState V}
    (h : H.run k x GState.init = some st) :
    (∀ v, v ∈ st.T ↔ v ∉ st.U) ∧
      ∀ i, 1 ≤ i → i ≤ k - 1 → ∀ v ∈ st.B i, ∀ v' ∈ st.U, H.EW v v' → v' ∈ st.B i := by
  have hI := inv_run hk x (inv_init (H := H) k) h
  exact ⟨hI.memT, fun i _ _ => hI.closed i⟩

/-- **Theorem 4.10** of [Golab–Li–López-Ortiz–Nishimura] (correctness part). For a history
satisfying Assumptions 3.2 (built into the model), 3.4 and 4.1, and `k ≥ 2`, algorithm GPO
outputs YES iff `H` is `k`-atomic. -/
theorem theorem_4_10 (hA : H.Assumption34) (h41 : H.Assumption41) {k : ℕ} (hk : 2 ≤ k) :
    H.gpo k = true ↔ H.KAtomic k :=
  ⟨lemma_4_4 hA hk, lemma_4_5 hA h41 hk⟩

end History

end Podc.KAtomicityVerification
