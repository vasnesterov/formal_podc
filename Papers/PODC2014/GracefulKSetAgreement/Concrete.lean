import Papers.PODC2014.GracefulKSetAgreement.MajInf
import Papers.PODC2014.GracefulKSetAgreement.Decide

/-!
# Membership of concrete, eventually constant runs in `VSRC(k, d)` and `MAJINF(k)`

A concrete communication pattern on `Fin n` is given by a Boolean adjacency `g : ℕ → Fin n → Fin n →
Bool` (`ρB g t u v ↔ g t u v`) that is constant from round index `T` on (`EvConst g T`). This file
reduces membership of `ρB g` in `VSRCkAll` (Definition 15) and `MAJINF` (Definition 21) to
finitely many decidable checks:

* `Vd_sub`: every maximal VSRC of length `≥ d` is in a given list `vs` (the list entries are
  `(F, a, some m)` for `F^{[a, m]}` and `(F, a, none)` for `F^{[a, ∞)}`);
* `IS_toV`: influence sets (Definition 18) are computed by `isB`;
* `mem_MAJINF_of`, `mem_VSRCkAll_of`.
-/

-- CSLib candidate (generic tools for concrete dynamic networks)

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

/-- At most `|P|` root components per round (they are disjoint and non-empty). -/
theorem ncard_rootComps_le {P : Type} [Fintype P] (G : Graph P) :
    {R | IsRootComp G R}.ncard ≤ Fintype.card P := by
  classical
  let f : {R // IsRootComp G R} → P := fun R => R.2.nonempty.some
  have hf : Function.Injective f := fun R S h =>
    Subtype.ext (R.2.eq_of_mem S.2 R.2.nonempty.some_mem
      (by have := S.2.nonempty.some_mem; simp only [f] at h; rwa [h]))
  calc {R | IsRootComp G R}.ncard = Nat.card {R // IsRootComp G R} :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card P := Nat.card_le_card_of_injective f hf
    _ = Fintype.card P := Nat.card_eq_fintype_card

namespace BoolPat

variable {n : ℕ}

/-- The communication pattern of a Boolean adjacency function. -/
def ρB (g : ℕ → Fin n → Fin n → Bool) : ℕ → Graph (Fin n) := fun t u v => g t u v = true

theorem hρB (g : ℕ → Fin n → Fin n → Bool) : ∀ t u v, ρB g t u v ↔ g t u v = true :=
  fun _ _ _ => Iff.rfl

theorem jset_congr (g : ℕ → Fin n → Fin n → Bool) {x y : ℕ} {p : Fin n} :
    ∀ k, (∀ i < k, g (x + i) = g (y + i)) → jset g x p k = jset g y p k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [jset]
    rw [jset_congr g k (fun i hi => h i (by omega)), h k (by omega)]

/-- `g` is constant from round index `T` on, and all reachability computations are complete. -/
structure EvConst (g : ℕ → Fin n → Fin n → Bool) (T : ℕ) : Prop where
  ge : ∀ t, T ≤ t → g t = g T
  closed : ∀ t ≤ T, AllClosed (g t)

variable {g : ℕ → Fin n → Fin n → Bool} {T : ℕ}

theorem EvConst.allClosed (h : EvConst g T) (t : ℕ) : AllClosed (g t) := by
  rcases le_or_gt t T with ht | ht
  · exact h.closed t ht
  · rw [h.ge t ht.le]; exact h.closed T le_rfl

theorem EvConst.isRootComp_iff (h : EvConst g T) (t : ℕ) (R : Set (Fin n)) :
    IsRootComp (ρB g t) R ↔ ∃ F ∈ rootsB (g t), R = ↑F :=
  isRootComp_iff_rootsB (hρB g t) (h.allClosed t) R

theorem EvConst.isRootComp_coe (h : EvConst g T) (t : ℕ) (F : Finset (Fin n)) :
    IsRootComp (ρB g t) ↑F ↔ F ∈ rootsB (g t) := by
  rw [h.isRootComp_iff]
  constructor
  · rintro ⟨F', hF', h⟩
    rwa [Finset.coe_inj.1 h]
  · intro h
    exact ⟨F, h, rfl⟩

/-! ### Finite descriptions of VSRCs -/

/-- A VSRC with a finite vertex set and an optional last round (`none` = forever). -/
abbrev FV (n : ℕ) := Finset (Fin n) × ℕ × Option ℕ

/-- The corresponding element of `VSRCI`. -/
def toV (Z : FV n) : VSRCI (Fin n) :=
  (↑Z.1, Z.2.1, match Z.2.2 with | some b => (b : ℕ∞) | none => ⊤)

theorem toV_injective : Function.Injective (toV (n := n)) := by
  rintro ⟨F, a, b⟩ ⟨F', a', b'⟩ h
  simp only [toV, Prod.mk.injEq, Finset.coe_inj] at h
  obtain ⟨rfl, rfl, h⟩ := h
  cases b <;> cases b' <;> simp_all

theorem isMaxVSRC_fin (h : EvConst g T) (F : Finset (Fin n)) (a m : ℕ) (h1 : a ≤ m)
    (h2 : ∀ t < m + 1, a ≤ t → F ∈ rootsB (g t)) (h3 : a = 0 ∨ F ∉ rootsB (g (a - 1)))
    (h4 : F ∉ rootsB (g (m + 1))) : IsMaxVSRC (ρB g) ↑F a (m : ℕ∞) := by
  refine ⟨by exact_mod_cast h1, fun t ht1 ht2 => (h.isRootComp_coe _ _).2
    (h2 t (by have : t ≤ m := by exact_mod_cast ht2
              omega) ht1), fun t ht hR => ?_, fun t ht hR => ?_⟩
  · rcases h3 with h3 | h3
    · omega
    · exact h3 (by rw [show a - 1 = t by omega]; exact (h.isRootComp_coe _ _).1 hR)
  · rw [show t = m by exact_mod_cast ht.symm] at hR
    exact h4 ((h.isRootComp_coe _ _).1 hR)

theorem isMaxVSRC_inf (h : EvConst g T) (F : Finset (Fin n)) (a : ℕ) (h1 : a ≤ T)
    (h2 : ∀ t < T + 1, a ≤ t → F ∈ rootsB (g t)) (h3 : a = 0 ∨ F ∉ rootsB (g (a - 1))) :
    IsMaxVSRC (ρB g) ↑F a ⊤ := by
  refine ⟨le_top, fun t ht1 _ => (h.isRootComp_coe _ _).2 ?_, fun t ht hR => ?_,
    fun t ht => absurd ht.symm (ENat.natCast_ne_top t)⟩
  · rcases le_or_gt t T with htT | htT
    · exact h2 t (by omega) ht1
    · rw [h.ge t htT.le]; exact h2 T (by omega) h1
  · rcases h3 with h3 | h3
    · omega
    · exact h3 (by rw [show a - 1 = t by omega]; exact (h.isRootComp_coe _ _).1 hR)

theorem mem_Vd_fin (h : EvConst g T) {d : ℕ} (F : Finset (Fin n)) (a m : ℕ) (hd : a + d ≤ m + 1)
    (h1 : a ≤ m) (h2 : ∀ t < m + 1, a ≤ t → F ∈ rootsB (g t))
    (h3 : a = 0 ∨ F ∉ rootsB (g (a - 1))) (h4 : F ∉ rootsB (g (m + 1))) :
    toV (F, a, some m) ∈ Vd (ρB g) d :=
  ⟨isMaxVSRC_fin h F a m h1 h2 h3 h4, by simp only [toV]; exact_mod_cast hd⟩

theorem mem_Vd_inf (h : EvConst g T) {d : ℕ} (F : Finset (Fin n)) (a : ℕ) (h1 : a ≤ T)
    (h2 : ∀ t < T + 1, a ≤ t → F ∈ rootsB (g t)) (h3 : a = 0 ∨ F ∉ rootsB (g (a - 1))) :
    toV (F, a, none) ∈ Vd (ρB g) d :=
  ⟨isMaxVSRC_inf h F a h1 h2 h3, by simp [toV]⟩

/-- **Upper bound on `V_d`** by finitely many checks. -/
theorem Vd_sub (h : EvConst g T) {d : ℕ} (vs : List (FV n))
    (hfin : ∀ a < T, ∀ m < T, a + d ≤ m + 1 → ∀ F ∈ rootsB (g a),
      (∀ t < m + 1, a ≤ t → F ∈ rootsB (g t)) → (a = 0 ∨ F ∉ rootsB (g (a - 1))) →
      F ∉ rootsB (g (m + 1)) → (F, a, some m) ∈ vs)
    (hinf : ∀ F ∈ rootsB (g T), ∀ a < T + 1, (∀ t < T + 1, a ≤ t → F ∈ rootsB (g t)) →
      (a = 0 ∨ F ∉ rootsB (g (a - 1))) → (F, a, none) ∈ vs) :
    ∀ X ∈ Vd (ρB g) d, ∃ Z ∈ vs, X = toV Z := by
  rintro ⟨R, a, b⟩ ⟨⟨hab, hroot, hstart, hend⟩, hlen⟩
  dsimp only at hab hroot hstart hend hlen
  obtain ⟨F, hF, rfl⟩ := (h.isRootComp_iff a R).1 (hroot a le_rfl hab)
  have hr : ∀ t, a ≤ t → (t : ℕ∞) ≤ b → F ∈ rootsB (g t) :=
    fun t h1 h2 => (h.isRootComp_coe t F).1 (hroot t h1 h2)
  have hst : a = 0 ∨ F ∉ rootsB (g (a - 1)) := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · exact Or.inl h0
    · exact Or.inr fun h' => hstart (a - 1) (by omega) ((h.isRootComp_coe _ _).2 h')
  induction b using ENat.recTopCoe with
  | top =>
    have ha : a ≤ T := by
      by_contra hc
      refine hstart (a - 1) (by omega) ((h.isRootComp_coe _ _).2 ?_)
      rw [h.ge (a - 1) (by omega), ← h.ge a (by omega)]
      exact hr a le_rfl le_top
    exact ⟨_, hinf F (hr T ha le_top) a (by omega) (fun t _ h1 => hr t h1 le_top) hst, rfl⟩
  | coe m =>
    have ham : a ≤ m := by exact_mod_cast hab
    have hlen' : a + d ≤ m + 1 := by exact_mod_cast hlen
    have hmT : m < T := by
      by_contra hc
      refine hend m rfl ((h.isRootComp_coe _ _).2 ?_)
      rw [h.ge (m + 1) (by omega), ← h.ge m (by omega)]
      exact hr m ham le_rfl
    refine ⟨_, hfin a (by omega) m hmT hlen' F hF
      (fun t ht h1 => hr t h1 (by exact_mod_cast Nat.lt_succ_iff.1 ht)) hst
      (fun h' => hend m rfl ((h.isRootComp_coe _ _).2 h')), rfl⟩

/-! ### Influence sets -/

/-- Influence sets between finitely described VSRCs, computed (Definitions 17–18). -/
def isB (g : ℕ → Fin n → Fin n → Bool) (Z Z' : FV n) : Finset (Fin n) :=
  match Z.2.2 with
  | some b =>
    if b < Z'.2.1 then Z'.1.filter (fun q => ∃ p ∈ Z.1, q ∈ jset g (b + 1) p (Z'.2.1 - b))
    else ∅
  | none => ∅

theorem IS_toV (g : ℕ → Fin n → Fin n → Bool) (Z Z' : FV n) :
    IS (ρB g) (toV Z) (toV Z') = ↑(isB g Z Z') := by
  obtain ⟨F, a, b⟩ := Z
  obtain ⟨F', a', b'⟩ := Z'
  ext q
  cases b with
  | none =>
    simp only [IS, Influences, toV, isB, Set.mem_ofPred_eq, Finset.coe_empty,
      Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    intro _ _ _ c h
    exact absurd h.symm (ENat.natCast_ne_top c)
  | some b =>
    simp only [IS, Influences, toV, isB, Set.mem_ofPred_eq, Finset.mem_coe]
    by_cases hb : b < a'
    · simp only [hb, ↓reduceIte, Finset.mem_filter]
      have hj : ∀ p, Journey (ρB g) (b + 1) p (a' + 1) q ↔ q ∈ jset g (b + 1) p (a' - b) := by
        intro p
        rw [← journey_iff_jset (hρB g)]
        rw [show b + 1 + (a' - b) = a' + 1 by omega]
      constructor
      · rintro ⟨hq, p, hp, c, hc, -, hJ⟩
        obtain rfl : b = c := by exact_mod_cast hc
        exact ⟨hq, p, hp, (hj p).1 hJ⟩
      · rintro ⟨hq, p, hp, hJ⟩
        exact ⟨hq, p, hp, b, rfl, hb, (hj p).2 hJ⟩
    · simp only [hb, ↓reduceIte, Finset.notMem_empty, iff_false, not_and, not_exists]
      intro _ _ _ c hc hlt
      obtain rfl : b = c := by exact_mod_cast hc
      exact absurd hlt hb

/-! ### Majority influence and `MAJINF` -/

/-- `Z` ends before `Z'` starts. -/
def precB (Z Z' : FV n) : Bool :=
  match Z.2.2 with
  | some b => decide (b < Z'.2.1)
  | none => false

/-- Majority influence (Definition 19, charitable reading) among the VSRCs of the list `vs`. -/
def majB (g : ℕ → Fin n → Fin n → Bool) (vs : List (FV n)) (Z Z' : FV n) : Prop :=
  precB Z Z' = true ∧ ∀ W ∈ vs, W ≠ Z →
    (isB g W Z = ∅ → (isB g W Z').card < (isB g Z Z').card) ∧
    (isB g W Z ≠ ∅ → (isB g W Z').card ≤ (isB g Z Z').card)

instance (g : ℕ → Fin n → Fin n → Bool) (vs : List (FV n)) (Z Z' : FV n) :
    Decidable (majB g vs Z Z') := by
  unfold majB; infer_instance

theorem majInf_of {D : ℕ} {vs : List (FV n)}
    (hmem : ∀ Z ∈ vs, toV Z ∈ Vd (ρB g) (2 * D + 1))
    (hsub : ∀ X ∈ Vd (ρB g) (D + 1), ∃ Z ∈ vs, X = toV Z)
    {Z Z' : FV n} (hZ : Z ∈ vs) (hZ' : Z' ∈ vs) (h : majB g vs Z Z') :
    MajInf (ρB g) D (toV Z) (toV Z') := by
  refine ⟨hmem Z hZ, hmem Z' hZ', ?_, fun R hR hne => ?_⟩
  · obtain ⟨F, a, b⟩ := Z
    cases b with
    | none => exact absurd h.1 (by simp [precB])
    | some b => exact ⟨b, rfl, by simpa [precB, toV] using h.1⟩
  · obtain ⟨W, hW, rfl⟩ := hsub R hR
    have hWZ : W ≠ Z := fun e => hne (e ▸ rfl)
    simp only [IS_toV, Set.ncard_coe_finset, Ne, Finset.coe_eq_empty]
    exact h.2 W hW hWZ

/-- **Membership in `MAJINF(k)`** by finitely many checks: `V_{D+1} = V_{2D+1} = vs`, and every
entry of `vs` outside `Ks` (`|Ks| ≤ k`) is majority-influenced by an entry of `vs`. -/
theorem mem_MAJINF_of {D k : ℕ} {vs : List (FV n)}
    (hmem : ∀ Z ∈ vs, toV Z ∈ Vd (ρB g) (2 * D + 1))
    (hsub : ∀ X ∈ Vd (ρB g) (D + 1), ∃ Z ∈ vs, X = toV Z)
    (Ks : List (FV n)) (hKs : ∀ Z ∈ Ks, Z ∈ vs) (hlen : Ks.length ≤ k)
    (hmaj : ∀ W ∈ vs, W ∉ Ks → ∃ Z ∈ vs, majB g vs Z W) : ρB g ∈ MAJINF D k := by
  classical
  refine ⟨↑(Ks.map toV).toFinset, fun X hX => ?_, ?_, fun Y ⟨hY, hYK⟩ => ?_⟩
  · simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hX
    obtain ⟨Z, hZ, rfl⟩ := hX
    exact hmem Z (hKs Z hZ)
  · rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast (List.toFinset_card_le _).trans ((List.length_map _).le.trans hlen)
  · obtain ⟨W, hW, rfl⟩ := hsub Y (Vd_mono (by omega) hY)
    have hWK : W ∉ Ks := by
      intro h'
      apply hYK
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact ⟨W, h', rfl⟩
    obtain ⟨Z, hZ, hm⟩ := hmaj W hW hWK
    exact ⟨toV Z, hmem Z hZ, majInf_of hmem hsub hZ hW hm⟩

/-! ### `VSRC(k, d)` -/

/-- **Membership in `VSRC(k, d)`** (strong reading of (iii)) for a pattern that is constant from
`T` on with a single root component `F₀` there. -/
theorem mem_VSRCkAll_of {D H k d : ℕ} (h : EvConst g T) (hD1 : 1 ≤ D) (hk : n ≤ k) (hk1 : 1 ≤ k)
    {F₀ : Finset (Fin n)} (hroots : rootsB (g T) = [F₀])
    (hD : ∀ x < T + 1, ∀ F ∈ rootsB (g x), (∀ i < D, F ∈ rootsB (g (x + i))) →
      ∀ p ∈ F, ∀ q ∈ F, q ∈ jset g x p D)
    (hH : ∀ q, ∃ p ∈ F₀, q ∈ jset g T p H) : ρB g ∈ VSRCkAll D H k d := by
  have hTr : ∀ t, T ≤ t → ∀ R, IsRootComp (ρB g t) R ↔ R = ↑F₀ := by
    intro t ht R
    rw [h.isRootComp_iff, h.ge t ht, hroots]
    simp
  refine ⟨fun t => (ncard_rootComps_le (ρB g t)).trans (by simpa using hk), ?_, T, {↑F₀},
    by simp, by simpa using hk1, ?_, ?_, ?_⟩
  · intro R a b hR
    right
    intro x hax hxb p hp q hq
    obtain ⟨F, hF, rfl⟩ := (h.isRootComp_iff x R).1 (hR x hax (by omega))
    have hall : ∀ i < D, F ∈ rootsB (g (x + i)) :=
      fun i hi => (h.isRootComp_coe _ F).1 (hR (x + i) (by omega) (by omega))
    rw [journey_iff_jset (hρB g)]
    rcases le_or_gt x T with hxT | hxT
    · exact hD x (by omega) F hF hall p hp q hq
    · have hg : ∀ i < D, g (x + i) = g (T + i) := fun i _ => by
        rw [h.ge (x + i) (by omega), h.ge (T + i) (by omega)]
      rw [jset_congr g D hg]
      refine hD T (by omega) F (by rw [← h.ge x hxT.le]; exact hF)
        (fun i hi => by rw [← hg i hi]; exact hall i hi) p hp q hq
  · intro R hR t h1 _
    rw [Set.mem_singleton_iff.1 hR]
    exact (hTr t h1 _).2 rfl
  · right
    intro x hx _ q
    obtain ⟨p, hp, hq⟩ := hH q
    refine ⟨↑F₀, rfl, p, hp, ?_⟩
    rw [journey_iff_jset (hρB g), jset_congr g (x := x) (y := T) H (fun i _ => by
      rw [h.ge (x + i) (by omega), h.ge (T + i) (by omega)])]
    exact hq
  · intro t h1 _ R hR
    exact (hTr t h1 R).1 hR

end BoolPat

end Podc.GracefulKSetAgreement
