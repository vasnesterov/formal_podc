import Mathlib
import Cslib.Foundations.SocialChoice.Aggregation
import Cslib.Foundations.Combinatorics.SimplicialComplex.Nerve

/-!
# The complexes `N_I`, `N_O` and simplicial aggregation maps (Section 2.3)

Following Baryshnikov and Section 2.3 of the paper, for any set of alternatives `X` and voters `ι`:

* `U a b σ` (`σ : ι → Bool`, `true = +`) is the set of profiles in which voter `i` ranks `a` above
  `b` iff `σ i`; `Uo a b s` is the set of preferences ranking `a` above `b` iff `s`.
  Note `U a b σ = U b a (¬σ)` (`U_swap`).
* The vertices of the input complex `N_I` are the *sets* `U a b σ` (`a ≠ b`), `VI ι X`; those of the
  output complex `N_O` are the sets `Uo a b s`, `VO X`. In both complexes a finite set of vertices
  is a simplex iff the sets intersect (`NI`, `NO`: nerves).
* A map `f : VI ι X → VO X` is *chromatic* if it maps `U^σ_{ab}` to some `U^s_{ab}`, *unanimous*
  if `f (U^{(+,…,+)}_{ab}) = U^+_{ab}`, and a *projection* if `f (U^σ_{ab}) = U^{σ k}_{ab}`.
* `Induces F f`: `F` maps every profile of a vertex `v` into the vertex `f v`.

Results:
* `prop_3_forward`, `prop_3_backward` (Proposition 3 of the full version): IIA aggregation maps
  induce chromatic simplicial maps `N_I → N_O`, and conversely.
* `prop_4_unanimity`, `prop_4_dictator` (Proposition 4 of the full version): for corresponding
  `F, f`, `F` is unanimous iff `f` is, and `F` is dictatorial iff `f` is a projection.
* `isChromatic_of_unanimous`: a unanimous simplicial map is automatically chromatic. This is why
  the PODC statement of Theorem 2.2 (which omits "chromatic", unlike the full version) is still
  correct.
-/

namespace Podc.ArrowTopology

open Cslib.SocialChoice PreAbstractSimplicialComplex

variable {ι X : Type*}

/-- `Ranks r a b s`: `r` ranks `a` above `b` if `s = true` (`+`), `b` above `a` if `s = false`. -/
def Ranks (r : Pref X) (a b : X) : Bool → Prop
  | true => r.P a b
  | false => r.P b a

@[simp] theorem ranks_true (r : Pref X) (a b : X) : Ranks r a b true ↔ r.P a b := Iff.rfl
@[simp] theorem ranks_false (r : Pref X) (a b : X) : Ranks r a b false ↔ r.P b a := Iff.rfl

theorem ranks_swap (r : Pref X) (a b : X) (s : Bool) : Ranks r b a (!s) ↔ Ranks r a b s := by
  cases s <;> rfl

theorem ranks_unique {r : Pref X} {a b : X} {s t : Bool} (hs : Ranks r a b s)
    (ht : Ranks r a b t) : s = t := by
  cases s <;> cases t <;> simp_all [Ranks]
  · exact (r.asymm hs ht).elim
  · exact (r.asymm hs ht).elim

open Classical in
theorem ranks_of_ne (r : Pref X) {a b : X} (hab : a ≠ b) : Ranks r a b (decide (r.P a b)) := by
  by_cases h : r.P a b
  · simp [h]
  · simpa [h] using (r.not_P_iff hab).1 h

theorem ranks_iff_of {r r' : Pref X} {a b : X} {s : Bool} (h : Ranks r a b s)
    (h' : Ranks r' a b s) : (r.P a b ↔ r'.P a b) := by
  cases s
  · simp only [ranks_false] at h h'; simp [r.asymm h, r'.asymm h']
  · simp only [ranks_true] at h h'; simp [h, h']

/-- `U^σ_{ab}`: the profiles where voter `i` ranks `a` above `b` iff `σ i`. -/
def U (a b : X) (σ : ι → Bool) : Set (Profile ι X) := {R | ∀ i, Ranks (R i) a b (σ i)}

/-- `U^s_{ab}` in `N_O`: the preferences ranking `a` above `b` iff `s`. -/
def Uo (a b : X) (s : Bool) : Set (Pref X) := {r | Ranks r a b s}

theorem U_swap (a b : X) (σ : ι → Bool) : U b a (fun i => !σ i) = U a b σ := by
  ext R; simp [U, ranks_swap]

theorem Uo_swap (a b : X) (s : Bool) : Uo b a (!s) = Uo a b s := by
  ext r; simp [Uo, ranks_swap]

/-- Vertices of the input complex `N_I`. -/
abbrev VI (ι X : Type*) := {S : Set (Profile ι X) // ∃ a b σ, a ≠ b ∧ S = U a b σ}

/-- Vertices of the output complex `N_O`. -/
abbrev VO (X : Type*) := {S : Set (Pref X) // ∃ a b s, a ≠ b ∧ S = Uo a b s}

/-- The input complex `N_I`: a set of vertices is a simplex iff they have a common profile. -/
def NI (ι X : Type*) : PreAbstractSimplicialComplex (VI ι X) := nerve Subtype.val

/-- The output complex `N_O`: a set of vertices is a simplex iff they have a common order. -/
def NO (X : Type*) : PreAbstractSimplicialComplex (VO X) := nerve Subtype.val

/-- The vertex `U^σ_{ab}` of `N_I`. -/
def vI (a b : X) (σ : ι → Bool) (h : a ≠ b) : VI ι X := ⟨U a b σ, a, b, σ, h, rfl⟩

/-- The vertex `U^s_{ab}` of `N_O`. -/
def vO (a b : X) (s : Bool) (h : a ≠ b) : VO X := ⟨Uo a b s, a, b, s, h, rfl⟩

theorem vI_swap (a b : X) (σ : ι → Bool) (h : a ≠ b) :
    vI b a (fun i => !σ i) h.symm = vI a b σ h := Subtype.ext (U_swap a b σ)

theorem vO_swap (a b : X) (s : Bool) (h : a ≠ b) : vO b a (!s) h.symm = vO a b s h :=
  Subtype.ext (Uo_swap a b s)

/-- `f` is unanimous: `f (U^{(+,…,+)}_{ab}) = U^+_{ab}`. -/
def IsUnanimousMap (f : VI ι X → VO X) : Prop :=
  ∀ a b (h : a ≠ b), f (vI a b (fun _ => true) h) = vO a b true h

/-- `f` is chromatic: it preserves the colour (the pair of alternatives) of every vertex. -/
def IsChromatic (f : VI ι X → VO X) : Prop :=
  ∀ a b (σ : ι → Bool) (h : a ≠ b), ∃ s, f (vI a b σ h) = vO a b s h

/-- `f` is a projection: `f (U^σ_{ab}) = U^{σ k}_{ab}` for a fixed voter `k`. -/
def IsProjection (f : VI ι X → VO X) : Prop :=
  ∃ k, ∀ a b (σ : ι → Bool) (h : a ≠ b), f (vI a b σ h) = vO a b (σ k) h

/-- `F` and `f` correspond: `F` maps every profile of a vertex `v` of `N_I` into `f v`. -/
def Induces (F : Aggregation ι X) (f : VI ι X → VO X) : Prop :=
  ∀ v : VI ι X, ∀ R ∈ v.1, F R ∈ (f v).1

/-! ### Building preferences and profiles -/

open Classical in
/-- Two comparisons on different pairs can always be realised simultaneously. -/
theorem exists_pref_two {a b c d : X} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a))) (s t : Bool) :
    ∃ r : Pref X, Ranks r a b s ∧ Ranks r c d t := by
  -- reduce to `s = t = true` by swapping
  suffices key : ∀ a b c d : X, a ≠ b → c ≠ d → ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) →
      ∃ r : Pref X, r.P a b ∧ r.P c d by
    obtain ⟨a', b', ha'⟩ : ∃ a' b' : X, (a' = a ∧ b' = b ∧ s = true) ∨ (a' = b ∧ b' = a ∧ s = false)
      := by cases s <;> simp
    obtain ⟨c', d', hc'⟩ : ∃ c' d' : X, (c' = c ∧ d' = d ∧ t = true) ∨ (c' = d ∧ d' = c ∧ t = false)
      := by cases t <;> simp
    obtain ⟨r, h1, h2⟩ := key a' b' c' d' (by rcases ha' with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;>
        [exact hab; exact hab.symm]) (by rcases hc' with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;>
        [exact hcd; exact hcd.symm]) (by
        rcases ha' with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;>
          rcases hc' with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> tauto)
    refine ⟨r, ?_, ?_⟩
    · rcases ha' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simpa using h1
    · rcases hc' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simpa using h2
  intro a b c d hab hcd hne
  let p : X → ℕ := fun x => (if x = b ∨ x = d then 1 else 0) +
    (if (x = d ∧ c = b) ∨ (x = b ∧ a = d) then 1 else 0)
  refine ⟨Pref.ofRank p, Pref.ofRank_P_of_lt ?_, Pref.ofRank_P_of_lt ?_⟩ <;>
  · simp only [p]
    by_cases h1 : c = b <;> by_cases h2 : a = d <;> simp_all

theorem U_nonempty (a b : X) (σ : ι → Bool) (h : a ≠ b) : (U a b σ).Nonempty := by
  classical
  have : ∀ i, ∃ r : Pref X, Ranks r a b (σ i) := by
    intro i
    cases σ i
    · exact Pref.exists_P h.symm
    · exact Pref.exists_P h
  choose r hr using this
  exact ⟨r, hr⟩

theorem Uo_nonempty (a b : X) (s : Bool) (h : a ≠ b) : (Uo a b s).Nonempty := by
  obtain ⟨R, hR⟩ := U_nonempty (ι := Unit) a b (fun _ => s) h
  exact ⟨R (), hR ()⟩

theorem vO_inj {a b : X} {s t : Bool} {h : a ≠ b} (e : vO a b s h = vO a b t h) : s = t := by
  obtain ⟨r, hr⟩ := Uo_nonempty a b s h
  have hr' : r ∈ Uo a b t := by
    have := congrArg Subtype.val e; simp only [vO] at this; rw [← this]; exact hr
  exact ranks_unique hr hr'

/-- The colour of a vertex is determined by the set (`ι` nonempty). -/
theorem U_eq_U [Nonempty ι] {a b c d : X} {σ τ : ι → Bool} (hab : a ≠ b) (hcd : c ≠ d)
    (e : U a b σ = U c d τ) :
    (c = a ∧ d = b ∧ τ = σ) ∨ (c = b ∧ d = a ∧ τ = fun i => !σ i) := by
  classical
  obtain ⟨R, hR⟩ := U_nonempty a b σ hab
  have hR' : R ∈ U c d τ := e ▸ hR
  by_cases hp : (c = a ∧ d = b) ∨ (c = b ∧ d = a)
  · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; refine ⟨rfl, rfl, funext fun i => ranks_unique (hR' i) (hR i)⟩
    · right; refine ⟨rfl, rfl, funext fun i => ?_⟩
      exact ranks_unique (hR' i) ((ranks_swap (R i) _ _ (σ i)).2 (hR i))
  · exfalso
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨r, hr1, hr2⟩ := exists_pref_two hab hcd hp (σ i₀) (!τ i₀)
    let R' : Profile ι X := Function.update R i₀ r
    have hR'1 : R' ∈ U a b σ := by
      intro i; by_cases hi : i = i₀
      · subst hi; simp [R', hr1]
      · simp only [R', Function.update_of_ne hi]; exact hR i
    have hR'2 : R' ∈ U c d τ := e ▸ hR'1
    have h1 := hR'2 i₀
    simp only [R', Function.update_self] at h1
    have := ranks_unique h1 hr2
    revert this; cases τ i₀ <;> decide

/-! ### Proposition 3 -/

open Classical in
/-- **Proposition 3** (full version), first part: an aggregation map satisfying IIA induces a
chromatic simplicial map `f : N_I → N_O` (with `ι` nonempty, i.e. `n ≥ 1`). -/
theorem prop_3_forward [Nonempty ι] {F : Aggregation ι X} (hF : IIA F) :
    ∃ f : VI ι X → VO X, Induces F f ∧ IsChromatic f ∧ IsSimplicialMap (NI ι X) (NO X) f := by
  -- choose a representation of each vertex and a profile in it
  have hrep : ∀ v : VI ι X, ∃ a b σ, ∃ h : a ≠ b, v = vI a b σ h := by
    rintro ⟨S, a, b, σ, h, rfl⟩; exact ⟨a, b, σ, h, rfl⟩
  choose a b σ h hv using hrep
  let f : VI ι X → VO X := fun v =>
    vO (a v) (b v) (decide ((F (U_nonempty (a v) (b v) (σ v) (h v)).some).P (a v) (b v))) (h v)
  have hind : Induces F f := by
    intro v R hR
    rw [hv v] at hR
    set R₀ := (U_nonempty (a v) (b v) (σ v) (h v)).some
    have hR₀ : R₀ ∈ U (a v) (b v) (σ v) := (U_nonempty (a v) (b v) (σ v) (h v)).some_mem
    have hiff : (F R).P (a v) (b v) ↔ (F R₀).P (a v) (b v) :=
      hF R R₀ _ _ fun i => ranks_iff_of (hR i) (hR₀ i)
    show Ranks (F R) (a v) (b v) _
    by_cases hP : (F R₀).P (a v) (b v)
    · rw [decide_eq_true hP]; exact hiff.2 hP
    · rw [decide_eq_false hP]
      exact ((F R).not_P_iff (h v)).1 (fun h' => hP (hiff.1 h'))
  refine ⟨f, hind, ?_, ?_⟩
  · intro c d τ hcd
    obtain ⟨s', hs'⟩ : ∃ s', f (vI c d τ hcd) =
        vO (a (vI c d τ hcd)) (b (vI c d τ hcd)) s' (h _) := ⟨_, rfl⟩
    have e := congrArg Subtype.val (hv (vI c d τ hcd))
    rcases U_eq_U (h _) hcd e.symm with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · refine ⟨s', ?_⟩
      rw [hs']; apply Subtype.ext; show Uo _ _ s' = Uo c d s'; rw [← h1, ← h2]
    · refine ⟨!s', ?_⟩
      rw [hs']; apply Subtype.ext; show Uo _ _ s' = Uo c d (!s')
      rw [Uo_swap d c s', ← h1, ← h2]
  · rw [NI, NO, isSimplicialMap_nerve_iff]
    rintro s - ⟨R, hR⟩
    exact ⟨F R, fun v hv => hind v R (hR v hv)⟩

/-- The sign vector of a profile on the pair `(a, b)`. -/
noncomputable def sigVec (R : Profile ι X) (a b : X) : ι → Bool :=
  fun i => @decide ((R i).P a b) (Classical.propDecidable _)

theorem mem_U_sigVec (R : Profile ι X) {a b : X} (h : a ≠ b) : R ∈ U a b (sigVec R a b) := by
  intro i; exact ranks_of_ne (R i) h

theorem sigVec_of_mem {R : Profile ι X} {a b : X} {σ : ι → Bool} (hR : R ∈ U a b σ) :
    sigVec R a b = σ := by
  classical
  funext i
  have := hR i
  cases hσ : σ i <;> simp only [hσ, ranks_true, ranks_false] at this <;>
    simp [sigVec, this, (R i).asymm this]

/-- From a chromatic map, the sign of the image of `U^σ_{ab}`. -/
theorem chromatic_sign {f : VI ι X → VO X} (hc : IsChromatic f) {a b : X} (σ : ι → Bool)
    (h : a ≠ b) : f (vI a b σ h) = vO a b true h ∨ f (vI a b σ h) = vO a b false h := by
  obtain ⟨s, hs⟩ := hc a b σ h; cases s <;> simp [hs]

open Classical in
/-- **Proposition 3** (full version), second part: a chromatic simplicial map `N_I → N_O` comes
from an aggregation map satisfying IIA. -/
theorem prop_3_backward {f : VI ι X → VO X} (hc : IsChromatic f)
    (hs : IsSimplicialMap (NI ι X) (NO X) f) : ∃ F : Aggregation ι X, IIA F ∧ Induces F f := by
  rw [NI, NO, isSimplicialMap_nerve_iff] at hs
  -- `G R a b`: society ranks `a` above `b`
  let G : Profile ι X → X → X → Prop := fun R a b =>
    ∃ h : a ≠ b, f (vI a b (sigVec R a b) h) = vO a b true h
  have hsym : ∀ R a b (h : a ≠ b), f (vI b a (sigVec R b a) h.symm) = f (vI a b (sigVec R a b) h) := by
    intro R a b h
    congr 1
    apply Subtype.ext
    show U b a (sigVec R b a) = U a b (sigVec R a b)
    rw [← U_swap a b (sigVec R a b)]
    congr 1
    funext i
    simp only [sigVec]
    by_cases h1 : (R i).P a b
    · simp [h1, (R i).asymm h1]
    · simp [h1, ((R i).not_P_iff h).1 h1]
  have gab : ∀ R a b (h : a ≠ b), G R a b ↔ f (vI a b (sigVec R a b) h) = vO a b true h :=
    fun R a b h => ⟨fun ⟨_, e⟩ => e, fun e => ⟨h, e⟩⟩
  have gba : ∀ R a b (h : a ≠ b), G R b a ↔ f (vI a b (sigVec R a b) h) = vO a b false h := by
    intro R a b h
    constructor
    · rintro ⟨_, e⟩; rw [← hsym R a b h, e]; exact vO_swap a b false h
    · intro e; refine ⟨h.symm, ?_⟩; rw [hsym R a b h, e]; exact (vO_swap a b false h).symm
  have hG : ∀ R a b (h : a ≠ b), G R a b ↔ ¬ G R b a := by
    intro R a b h
    rw [gab R a b h, gba R a b h]
    rcases chromatic_sign hc (sigVec R a b) h with e | e <;> rw [e]
    · simp only [true_iff]; intro e'; exact absurd (vO_inj e') (by decide)
    · simp only [not_true_eq_false, iff_false]; intro e'; exact absurd (vO_inj e') (by decide)
  let F : Aggregation ι X := fun R =>
    { P := G R
      irrefl := fun a ⟨h, _⟩ => h rfl
      trans := by
        intro a b c hab hbc
        obtain ⟨h1, e1⟩ := hab
        obtain ⟨h2, e2⟩ := hbc
        have h3 : a ≠ c := by
          rintro rfl
          exact (hG R a b h1).1 ⟨h1, e1⟩ ⟨h2, e2⟩
        refine ⟨h3, ?_⟩
        obtain ⟨r, hr⟩ := hs {vI a b (sigVec R a b) h1, vI b c (sigVec R b c) h2,
          vI a c (sigVec R a c) h3} (by simp) ⟨R, by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl <;> exact mem_U_sigVec R ‹_›⟩
        have r1 : r.P a b := by
          have := hr (vI a b (sigVec R a b) h1) (by simp); rw [e1] at this; exact this
        have r2 : r.P b c := by
          have := hr (vI b c (sigVec R b c) h2) (by simp); rw [e2] at this; exact this
        have r3 := hr (vI a c (sigVec R a c) h3) (by simp)
        rcases chromatic_sign hc (sigVec R a c) h3 with e | e
        · exact e
        · rw [e] at r3; exact absurd (r.trans r1 r2) (r.asymm r3)
      total := by
        intro a b h
        by_cases hab : G R a b
        · exact Or.inl hab
        · exact Or.inr ((hG R b a h.symm).2 hab) }
  refine ⟨F, ?_, ?_⟩
  · intro R S a b hRS
    show G R a b ↔ G S a b
    have : sigVec R a b = sigVec S a b := by
      funext i; simp only [sigVec]; exact decide_eq_decide.2 (hRS i)
    simp only [G, this]
  · rintro ⟨_, a, b, σ, h, rfl⟩ R hR
    have hσ : sigVec R a b = σ := sigVec_of_mem hR
    obtain ⟨t, ht⟩ := hc a b σ h
    show F R ∈ (f (vI a b σ h)).1
    rw [ht]
    show Ranks (F R) a b t
    cases t
    · show G R b a
      rw [gba R a b h, hσ]; exact ht
    · show G R a b
      rw [gab R a b h, hσ]; exact ht

/-! ### Proposition 4 -/

/-- **Proposition 4** (full version), unanimity: for an IIA map `F` and the chromatic map `f` it
induces, `F` is unanimous iff `f` is. -/
theorem prop_4_unanimity [Nonempty ι] {F : Aggregation ι X} {f : VI ι X → VO X} (hFf : Induces F f)
    (hc : IsChromatic f) : Unanimity F ↔ IsUnanimousMap f := by
  constructor
  · intro hF a b h
    obtain ⟨s, hs⟩ := hc a b _ h
    obtain ⟨R, hR⟩ := U_nonempty a b (fun _ : ι => true) h
    have h1 : F R ∈ Uo a b s := by have := hFf (vI a b _ h) R hR; rw [hs] at this; exact this
    have h2 : Ranks (F R) a b true := hF R a b hR
    rw [hs, ranks_unique h1 h2]
  · intro hf R a b hab
    have h : a ≠ b := (R (Classical.arbitrary _)).ne_of_P (hab _)
    have := hFf (vI a b (fun _ => true) h) R hab
    rw [hf a b h] at this
    exact this

/-- **Proposition 4** (full version), dictatorship: for an IIA map `F` and the chromatic map `f`
it induces, voter `k` is a dictator of `F` iff `f` is the projection to `k`. -/
theorem prop_4_dictator {F : Aggregation ι X} {f : VI ι X → VO X} (hFf : Induces F f)
    (hc : IsChromatic f) (k : ι) :
    IsDictator F k ↔ ∀ a b (σ : ι → Bool) (h : a ≠ b), f (vI a b σ h) = vO a b (σ k) h := by
  constructor
  · intro hF a b σ h
    obtain ⟨s, hs⟩ := hc a b σ h
    obtain ⟨R, hR⟩ := U_nonempty a b σ h
    have h1 : F R ∈ Uo a b s := by have := hFf (vI a b _ h) R hR; rw [hs] at this; exact this
    have h2 : Ranks (F R) a b (σ k) := by
      have := hR k
      cases hσ : σ k <;> rw [hσ] at this
      · exact hF R b a this
      · exact hF R a b this
    rw [hs, ranks_unique h1 h2]
  · intro hf R a b hab
    have h : a ≠ b := (R k).ne_of_P hab
    have hR := mem_U_sigVec R h
    have := hFf (vI a b _ h) R hR
    rw [hf a b _ h] at this
    have hk : sigVec R a b k = true := by
      classical
      simp [sigVec, hab]
    rw [hk] at this
    exact this

theorem prop_4_dictatorial {F : Aggregation ι X} {f : VI ι X → VO X} (hFf : Induces F f)
    (hc : IsChromatic f) : Dictatorial F ↔ IsProjection f :=
  exists_congr fun k => prop_4_dictator hFf hc k

/-- A unanimous simplicial map `N_I → N_O` is chromatic. (For a vertex `U^σ_{ab}` whose image had
another colour `cd`, the edges `{U^σ_{ab}, U^{+…+}_{cd}}` and `{U^σ_{ab}, U^{−…−}_{cd}}` of `N_I`
would force the image to be both `U^+_{cd}` and `U^-_{cd}`.) -/
theorem isChromatic_of_unanimous {f : VI ι X → VO X} (hs : IsSimplicialMap (NI ι X) (NO X) f)
    (hu : IsUnanimousMap f) : IsChromatic f := by
  classical
  rw [NI, NO, isSimplicialMap_nerve_iff] at hs
  intro a b σ h
  obtain ⟨c, d, t, hcd, e⟩ := (f (vI a b σ h)).2
  by_cases hp : (c = a ∧ d = b) ∨ (c = b ∧ d = a)
  · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨t, Subtype.ext e⟩
    · exact ⟨!t, Subtype.ext (e.trans (Uo_swap _ _ _).symm)⟩
  · exfalso
    -- the image of `U^σ_{ab}` is `U^t_{cd}` with `{c, d} ≠ {a, b}`
    have key : ∀ u : Bool, f (vI c d (fun _ => u) hcd) = vO c d u hcd → t = u := by
      intro u hu
      have : ∀ i, ∃ r : Pref X, Ranks r a b (σ i) ∧ Ranks r c d u :=
        fun i => exists_pref_two h hcd hp (σ i) u
      choose R hR using this
      obtain ⟨r, hr⟩ := hs {vI a b σ h, vI c d (fun _ => u) hcd} (by simp)
        ⟨R, by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact fun i => (hR i).1
          · exact fun i => (hR i).2⟩
      have h1 : r ∈ Uo c d t := e ▸ hr (vI a b σ h) (by simp)
      have h2 : r ∈ Uo c d u := by
        have := hr (vI c d (fun _ => u) hcd) (by simp); rw [hu] at this; exact this
      exact ranks_unique h1 h2
    have ht := key true (hu c d hcd)
    have hf := key false (by
      have := hu d c hcd.symm
      rw [← vI_swap d c (fun _ => true) hcd.symm, ← vO_swap d c true hcd.symm] at this
      exact this)
    exact absurd (ht.symm.trans hf) (by decide)


end Podc.ArrowTopology
