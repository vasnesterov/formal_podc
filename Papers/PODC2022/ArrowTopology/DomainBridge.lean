import Papers.PODC2022.ArrowTopology.ThreeAlt

/-!
# Domain restrictions: aggregation maps ↔ sign functions

Bridge between the Arrovian social-choice side (`Cslib.SocialChoice`) and the sign model of the
input complex `N_I` (`SignModel.lean`) for **restricted domains**, as used in Section 4 of
S. Rajsbaum, A. Raventós-Pujol, *A Distributed Combinatorial Topology Approach to Arrow's
Impossibility Theorem*, PODC 2022.

For three alternatives (`T3 : ThreeAlts X`) and any domain `D` of profiles (any set of voters `ι`):

* `admitsNonDictatorial_iff_sign`: `D` admits a unanimous, IIA, non-dictatorial aggregation map
  iff there is a sign function `s` on the vertices of `N_I` that is unanimous and simplicial on the
  triangles `T3.sig '' D` spanned by `D`, and is not a projection on them.
* `AdmitsNonDictatorial.mono`: if `D ⊆ D'` and every pairwise pattern occurring in `D'` already
  occurs in `D`, then `D'` admitting a non-dictatorial map implies that `D` does
  (non-dictatoriality only depends on which "vertices" occur).
* `PairFree`: the classical notion of a *free pair* (Le Breton–Weymark); a domain in which every
  pair is free contains all vertices of `N_I` (`forall_exists_sig_eq_of_pairFree`).
-/

namespace Podc.ArrowTopology

open Cslib.SocialChoice Classical

variable {ι X : Type*}

/-! ### A domain-level monotonicity lemma (no assumption on `X`) -/

/-- If `D ⊆ D'` and every pattern of the voters on a pair `a, b` that occurs in a profile of `D'`
also occurs in some profile of `D`, then any unanimous IIA non-dictatorial map on `D'` restricts
to one on `D`. -/
theorem AdmitsNonDictatorial.mono {D D' : Set (Profile ι X)} (hDD' : D ⊆ D')
    (hcov : ∀ R' ∈ D', ∀ a b : X, ∃ R ∈ D, ∀ i, ((R i).P a b ↔ (R' i).P a b))
    (h : AdmitsNonDictatorial D') : AdmitsNonDictatorial D := by
  obtain ⟨F, hU, hI, hnd⟩ := h
  refine ⟨F, fun R hR => hU R (hDD' hR), fun R hR S hS => hI R (hDD' hR) S (hDD' hS),
    fun k hk => hnd k ?_⟩
  intro R' hR' a b hab
  obtain ⟨R, hR, hRR'⟩ := hcov R' hR' a b
  exact (hI R (hDD' hR) R' hR' a b hRR').1 (hk R hR a b ((hRR' k).2 hab))

/-- A pair `a, b` is *free* on `D` if every pattern of the voters' preferences on `{a, b}` is
realised by some profile of `D` (Le Breton–Weymark). -/
def PairFree (D : Set (Profile ι X)) (a b : X) : Prop :=
  ∀ c : ι → Bool, ∃ R ∈ D, ∀ i, ((R i).P a b ↔ c i = true)

namespace ThreeAlts

variable (T3 : ThreeAlts X)

theorem pr_fst_ne_snd (j : Fin 3) : (T3.pr j).1 ≠ (T3.pr j).2 := by
  fin_cases j
  · exact T3.hxy
  · exact T3.hyz
  · exact T3.hxz.symm

/-- Every pair of distinct alternatives is one of the three pairs `AB, BC, CA`, in one of the two
orientations. -/
theorem exists_pr (a b : X) (hab : a ≠ b) : ∃ j, T3.pr j = (a, b) ∨ T3.pr j = (b, a) := by
  rcases T3.cover a with rfl | rfl | rfl <;> rcases T3.cover b with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | exact ⟨0, Or.inl rfl⟩
    | exact ⟨0, Or.inr rfl⟩
    | exact ⟨1, Or.inl rfl⟩
    | exact ⟨1, Or.inr rfl⟩
    | exact ⟨2, Or.inl rfl⟩
    | exact ⟨2, Or.inr rfl⟩

/-- Two preferences have the same sign on `pr j` iff they agree on the comparison of `pr j`. -/
theorem sig1_eq_sig1_iff (r r' : Pref X) (j : Fin 3) :
    T3.sig1 r j = T3.sig1 r' j ↔
      (r.P (T3.pr j).1 (T3.pr j).2 ↔ r'.P (T3.pr j).1 (T3.pr j).2) := by
  rw [← T3.sig1_eq_true_iff, ← T3.sig1_eq_true_iff]
  cases T3.sig1 r j <;> cases T3.sig1 r' j <;> simp

/-- The comparison of `a, b` (an oriented pair `pr j`) is read off the sign on `pr j`. -/
theorem P_iff_of_pr {r : Pref X} {a b : X} {j : Fin 3} (h : T3.pr j = (a, b) ∨ T3.pr j = (b, a)) :
    r.P a b ↔ (T3.sig1 r j = true ∧ T3.pr j = (a, b)) ∨ (T3.sig1 r j = false ∧ T3.pr j = (b, a)) := by
  have hne := T3.pr_fst_ne_snd j
  rcases h with h | h
  · have hab : a ≠ b := by rw [h] at hne; exact hne
    rw [T3.sig1_eq_true_iff, T3.sig1_eq_false_iff, h]
    have : (a, b) ≠ (b, a) := fun e => hab (Prod.ext_iff.1 e).1
    simp [this]
  · have hab : b ≠ a := by rw [h] at hne; exact hne
    rw [T3.sig1_eq_true_iff, T3.sig1_eq_false_iff, h]
    have : (b, a) ≠ (a, b) := fun e => hab (Prod.ext_iff.1 e).1
    simp [this]

/-- For `a ≠ b` lying on the pair `pr j`, `r.P a b` says that the sign on `pr j` is `true` iff
`pr j` is oriented as `(a, b)`. -/
theorem P_iff_sig1_eq {r : Pref X} {a b : X} (hab : a ≠ b) {j : Fin 3}
    (h : T3.pr j = (a, b) ∨ T3.pr j = (b, a)) :
    r.P a b ↔ T3.sig1 r j = decide (T3.pr j = (a, b)) := by
  rw [T3.P_iff_of_pr h]
  have : (a, b) ≠ (b, a) := fun e => hab (Prod.ext_iff.1 e).1
  rcases h with h | h <;> simp [h, this, this.symm]

/-- If two preferences have the same sign on the pair `{a, b}`, they agree on `a` vs `b`. -/
theorem P_iff_P_of_sig1_eq {r r' : Pref X} {a b : X} {j : Fin 3}
    (h : T3.pr j = (a, b) ∨ T3.pr j = (b, a)) (he : T3.sig1 r j = T3.sig1 r' j) :
    r.P a b ↔ r'.P a b := by
  rw [T3.P_iff_of_pr h, T3.P_iff_of_pr h, he]

/-- If `r` dominates `r'` (every strict comparison of `r` holds in `r'`) they have equal signs. -/
theorem sig1_eq_of_imp {r r' : Pref X} (h : ∀ a b, r.P a b → r'.P a b) (j : Fin 3) :
    T3.sig1 r j = T3.sig1 r' j := by
  cases hb : T3.sig1 r j
  · exact ((T3.sig1_eq_false_iff r' j).2 (h _ _ ((T3.sig1_eq_false_iff r j).1 hb))).symm
  · exact ((T3.sig1_eq_true_iff r' j).2 (h _ _ ((T3.sig1_eq_true_iff r j).1 hb))).symm

/-- A domain in which every pair is free contains all vertices of `N_I`. -/
theorem forall_exists_sig_eq_of_pairFree {D : Set (Profile ι X)}
    (hD : ∀ a b, a ≠ b → PairFree D a b) (j : Fin 3) (σ : ι → Bool) :
    ∃ R ∈ D, T3.sig R j = σ := by
  obtain ⟨R, hR, h⟩ := hD _ _ (T3.pr_fst_ne_snd j) σ
  refine ⟨R, hR, funext fun i => ?_⟩
  have := h i
  rw [← T3.sig1_eq_true_iff] at this
  simp only [sig]
  cases hs : T3.sig1 (R i) j <;> cases hσ : σ i <;> simp_all

/-- If `D` contains all vertices of `N_I`, every pattern on every pair occurring anywhere occurs
in `D` (the coverage hypothesis of `AdmitsNonDictatorial.mono`). -/
theorem cover_of_forall_exists_sig_eq {D : Set (Profile ι X)}
    (hD : ∀ (j : Fin 3) (σ : ι → Bool), ∃ R ∈ D, T3.sig R j = σ) (R' : Profile ι X) (a b : X) :
    ∃ R ∈ D, ∀ i, ((R i).P a b ↔ (R' i).P a b) := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨R, hR, -⟩ := hD 0 (fun _ => true)
    exact ⟨R, hR, fun i => by simp [(R i).irrefl, (R' i).irrefl]⟩
  obtain ⟨j, hj⟩ := T3.exists_pr a b hab
  obtain ⟨R, hR, he⟩ := hD j (T3.sig R' j)
  exact ⟨R, hR, fun i => T3.P_iff_P_of_sig1_eq hj (congrFun he i)⟩

/-! ### The bridge -/

/-- **Bridge lemma.** For three alternatives, a domain `D` admits a unanimous, IIA,
non-dictatorial aggregation map iff some sign function on the vertices of `N_I` is unanimous and
simplicial on the triangles spanned by `D`, and is not a projection on them. -/
theorem admitsNonDictatorial_iff_sign (D : Set (Profile ι X)) :
    AdmitsNonDictatorial D ↔ ∃ s : Vtx ι → Bool, SignUnanimousOn (T3.sig '' D) s ∧
      SignSimplicialOn (T3.sig '' D) s ∧ ∀ k, ¬ SignProjectionOn (T3.sig '' D) s k := by
  constructor
  · rintro ⟨F, hU, hI, hnd⟩
    let s : Vtx ι → Bool := fun v =>
      if h : ∃ R ∈ D, T3.sig R v.1 = v.2 then T3.sig1 (F h.choose) v.1 else false
    have hs : ∀ R ∈ D, ∀ j, s (j, T3.sig R j) = T3.sig1 (F R) j := by
      intro R hR j
      have h : ∃ R' ∈ D, T3.sig R' j = T3.sig R j := ⟨R, hR, rfl⟩
      simp only [s, dite_eq_left h]
      obtain ⟨hR', he⟩ := h.choose_spec
      rw [T3.sig1_eq_sig1_iff]
      apply hI _ hR' _ hR
      intro i
      exact (T3.sig1_eq_sig1_iff _ _ j).1 (congrFun he i)
    refine ⟨s, ?_, ?_, ?_⟩
    · rintro _ ⟨R, hR, rfl⟩ j b hb
      rw [hs R hR j]
      have hb' : ∀ i, T3.sig1 (R i) j = b := fun i => congrFun hb i
      cases b
      · exact (T3.sig1_eq_false_iff _ j).2
          (hU R hR _ _ fun i => (T3.sig1_eq_false_iff _ j).1 (hb' i))
      · exact (T3.sig1_eq_true_iff _ j).2
          (hU R hR _ _ fun i => (T3.sig1_eq_true_iff _ j).1 (hb' i))
    · rintro _ ⟨R, hR, rfl⟩
      rw [hs R hR 0, hs R hR 1, hs R hR 2]
      exact T3.sig1_outTri (F R)
    · intro k hk
      apply hnd k
      intro R hR a b hab
      have hFR : F R = R k := T3.sig1_injective fun j => by
        rw [← hs R hR j]; exact hk _ ⟨R, hR, rfl⟩ j
      rw [hFR]; exact hab
  · rintro ⟨s, hU, hS, hP⟩
    let F : Aggregation ι X := fun R =>
      T3.ofSigns (s (0, T3.sig R 0)) (s (1, T3.sig R 1)) (s (2, T3.sig R 2))
    have hF : ∀ R ∈ D, ∀ j, T3.sig1 (F R) j = s (j, T3.sig R j) := by
      intro R hR j
      have := T3.sig1_ofSigns (hS _ ⟨R, hR, rfl⟩)
      fin_cases j
      · exact this.1
      · exact this.2.1
      · exact this.2.2
    refine ⟨F, ?_, ?_, ?_⟩
    · intro R hR a b hab
      by_cases hne : a = b
      · subst hne
        by_cases hι : Nonempty ι
        · obtain ⟨i⟩ := hι
          exact absurd (hab i) ((R i).irrefl a)
        · have h0 : T3.sig R 0 = fun _ => true := funext fun i => absurd ⟨i⟩ hι
          have h1 : T3.sig R 0 = fun _ => false := funext fun i => absurd ⟨i⟩ hι
          have e0 := hU _ ⟨R, hR, rfl⟩ 0 true h0
          have e1 := hU _ ⟨R, hR, rfl⟩ 0 false h1
          rw [e0] at e1; exact absurd e1 (by decide)
      obtain ⟨j, hj⟩ := T3.exists_pr a b hne
      have hc : T3.sig R j = fun _ => decide (T3.pr j = (a, b)) :=
        funext fun i => (T3.P_iff_sig1_eq hne hj).1 (hab i)
      rw [T3.P_iff_sig1_eq hne hj, hF R hR j]
      exact hU _ ⟨R, hR, rfl⟩ j _ hc
    · intro R hR S hS a b hRS
      by_cases hne : a = b
      · subst hne; simp [(F R).irrefl, (F S).irrefl]
      obtain ⟨j, hj⟩ := T3.exists_pr a b hne
      have he : T3.sig R j = T3.sig S j := funext fun i => by
        have := hRS i
        rw [T3.P_iff_sig1_eq hne hj, T3.P_iff_sig1_eq hne hj] at this
        simp only [sig]
        revert this
        cases T3.sig1 (R i) j <;> cases T3.sig1 (S i) j <;> cases decide (T3.pr j = (a, b)) <;>
          simp
      rw [T3.P_iff_sig1_eq hne hj, T3.P_iff_sig1_eq hne hj, hF R hR j, hF S hS j, he]
    · intro k hk
      apply hP k
      rintro _ ⟨R, hR, rfl⟩ j
      rw [← hF R hR j]
      exact (T3.sig1_eq_of_imp (hk R hR) j).symm

end ThreeAlts

end Podc.ArrowTopology
