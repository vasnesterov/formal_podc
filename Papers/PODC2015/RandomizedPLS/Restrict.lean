import Papers.PODC2015.RandomizedPLS.Crossing

/-!
# Restricting a configuration to a union of components

The lower bounds of Section 5 apply the crossing tool to a *connected component* of the crossed
configuration (proof of Theorem 5.1: "`σ₁(P) ∉ F`, but `C` is a connected component of `σ₁(P)` and
`C ∈ F`"). This is sound because verification is local: a node of a set `U` closed under taking
neighbours sees the same thing in `c` and in `c.restrict U`.

* `accepts_restrict`: deterministic acceptance passes to `c.restrict U`.
* `RScheme.accProb_le_restrict`: the acceptance probability can only grow (fewer nodes must accept;
  `uprob_comp_restrict` is the marginal lemma for uniform product spaces).
* `RScheme.acceptsAll_restrict`: acceptance for all coin outcomes passes to `c.restrict U`.
-/

namespace Podc.RandomizedPLS

open Classical

/-- **Marginals of uniform product spaces.** An event that only depends on the coordinates in `U`
has the same probability in the full product space and in the product over `U`. -/
-- CSLib candidate
theorem uprob_comp_restrict {α : Type*} [Fintype α] [DecidableEq α] {X : α → Type*}
    [∀ a, Fintype (X a)] [∀ a, Nonempty (X a)] (U : Set α) (E : (∀ u : U, X u) → Prop) :
    Cslib.Probability.uprob (fun ω : ∀ a, X a => E (fun u => ω u)) =
      Cslib.Probability.uprob E := by
  unfold Cslib.Probability.uprob
  let e := Equiv.piEquivPiSubtypeProd (· ∈ U) X
  have h1 : Nat.card {ω : ∀ a, X a // E (fun u => ω u)} =
      Nat.card {p : (∀ u : U, X u) × (∀ u : {a // a ∉ U}, X u) // E p.1} :=
    Nat.card_congr (e.subtypeEquiv fun ω => Iff.rfl)
  have h2 : Nat.card {p : (∀ u : U, X u) × (∀ u : {a // a ∉ U}, X u) // E p.1} =
      Nat.card {a : ∀ u : U, X u // E a} * Fintype.card (∀ u : {a // a ∉ U}, X u) := by
    rw [Nat.card_congr Equiv.prodSubtypeFstEquivSubtypeProd, Nat.card_prod,
      Nat.card_eq_fintype_card (α := ∀ u : {a // a ∉ U}, X u)]
  have h3 : Fintype.card (∀ a, X a) =
      Fintype.card (∀ u : U, X u) * Fintype.card (∀ u : {a // a ∉ U}, X u) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [h1, h2, h3]
  have hpos : 0 < Fintype.card (∀ u : {a // a ∉ U}, X u) := Fintype.card_pos
  push_cast
  rw [mul_div_mul_right _ _ (by exact_mod_cast hpos.ne')]

-- CSLib candidate
lemma idxOf_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (x : α) (l : List α) : (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    by_cases hy : y = x
    · subst hy; simp
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun h => hy (hf h)), List.idxOf_cons_ne _ hy, ih]

/-- The restriction of a configuration to a set of nodes closed under taking neighbours. -/
@[reducible] noncomputable def Config.restrict {S : Type} (c : Config S) (U : Set c.V)
    (hU : ∀ v ∈ U, ∀ w ∈ c.nbrs v, w ∈ U) : Config S where
  V := U
  nbrs v := (c.nbrs v.1).pmap (fun w hw => (⟨w, hw⟩ : U)) (fun w hw => hU v.1 v.2 w hw)
  nodup v := (c.nodup v.1).pmap fun _ _ _ _ h => congrArg Subtype.val h
  loopless v h := by
    obtain ⟨w, hw, he⟩ := List.mem_pmap.1 h
    have : w = v.1 := congrArg Subtype.val he
    exact c.loopless v.1 (this ▸ hw)
  symm v w h := by
    obtain ⟨w', hw', rfl⟩ := List.mem_pmap.1 h
    exact List.mem_pmap.2 ⟨v.1, c.symm _ _ hw', rfl⟩
  state v := c.state v.1
  deg v := c.deg v.1
  deg_eq v := by rw [List.length_pmap, c.deg_eq]

namespace Config

variable {S : Type} (c : Config S) (U : Set c.V) (hU : ∀ v ∈ U, ∀ w ∈ c.nbrs v, w ∈ U)

lemma restrict_nbrs_map (v : (c.restrict U hU).V) :
    ((c.restrict U hU).nbrs v).map Subtype.val = c.nbrs v.1 := by
  change ((c.nbrs v.1).pmap _ _).map Subtype.val = _
  rw [List.map_pmap]; simp

lemma restrict_port (v w : (c.restrict U hU).V) :
    (c.restrict U hU).port v w = c.port v.1 w.1 := by
  unfold Config.port
  rw [← c.restrict_nbrs_map U hU v]
  exact (idxOf_map_of_injective Subtype.val Subtype.val_injective w _).symm

end Config

/-- Deterministic acceptance passes to a union of components. -/
lemma accepts_restrict {S : Type} {ver : Verifier S} {c : Config S} {U : Set c.V}
    (hU : ∀ v ∈ U, ∀ w ∈ c.nbrs v, w ∈ U) {ℓ : c.V → List Bool} (h : Accepts ver c ℓ) :
    Accepts ver (c.restrict U hU) (fun v => ℓ v.1) := by
  intro v
  have := h v.1
  change ver (c.state v.1) (ℓ v.1) (((c.restrict U hU).nbrs v).map fun v => ℓ v.1) = true
  rwa [show (fun v : U => ℓ v.1) = ℓ ∘ Subtype.val from rfl, ← List.map_map,
    c.restrict_nbrs_map U hU v]

namespace RScheme

variable {S L : Type} (σ : RScheme S L) {c : Config S} {U : Set c.V}
  (hU : ∀ v ∈ U, ∀ w ∈ c.nbrs v, w ∈ U) (ℓ : c.V → L)

lemma received_restrict (ω : σ.Coins c ℓ) (v : (c.restrict U hU).V) :
    σ.received (c.restrict U hU) (fun v => ℓ v.1) (fun v => ω v.1) v = σ.received c ℓ ω v.1 := by
  unfold received
  rw [← c.restrict_nbrs_map U hU v, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  simp only [Function.comp_apply, sent, c.restrict_port U hU]

lemma acceptsAll_restrict_of (ω : σ.Coins c ℓ) (h : σ.AcceptsAll c ℓ ω) :
    σ.AcceptsAll (c.restrict U hU) (fun v => ℓ v.1) (fun v => ω v.1) := by
  intro v
  have := h v.1
  change σ.dec (c.state v.1) (ℓ v.1) _ = true
  rwa [received_restrict]

/-- Acceptance for every outcome of the coins passes to a union of components. -/
lemma acceptsAll_restrict (h : ∀ ω, σ.AcceptsAll c ℓ ω) :
    ∀ ω', σ.AcceptsAll (c.restrict U hU) (fun v => ℓ v.1) ω' := by
  intro ω'
  let ω : σ.Coins c ℓ := fun v => if hv : v ∈ U then ω' ⟨v, hv⟩ else Classical.arbitrary _
  have : (fun v : (c.restrict U hU).V => ω v.1) = ω' := by
    funext v; simp only [ω, dite_eq_left v.2]
  rw [← this]
  exact σ.acceptsAll_restrict_of hU ℓ ω (h ω)

/-- The acceptance probability can only grow when restricting to a union of components. -/
lemma accProb_le_restrict :
    σ.accProb c ℓ ≤ σ.accProb (c.restrict U hU) (fun v => ℓ v.1) := by
  unfold accProb
  calc Cslib.Probability.uprob (σ.AcceptsAll c ℓ)
      ≤ Cslib.Probability.uprob (fun ω : σ.Coins c ℓ =>
          σ.AcceptsAll (c.restrict U hU) (fun v => ℓ v.1) (fun v => ω v.1)) :=
        Cslib.Probability.uprob_mono fun ω h => σ.acceptsAll_restrict_of hU ℓ ω h
    _ = _ := uprob_comp_restrict (X := fun v => σ.Ω (c.state v) (ℓ v) (c.deg v)) U
          (σ.AcceptsAll (c.restrict U hU) (fun v => ℓ v.1))

end RScheme

end Podc.RandomizedPLS
