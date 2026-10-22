import Papers.PODC2016.RationalConsensus.Protocol

/-!
# The random dictator of `σ_cons` is uniform

With independent uniform seeds, `S = Σ_{l ∈ NC} x_l[t] mod |NC|` is uniform on `{0, …, |NC| - 1}`
as soon as `NC ≠ ∅` (shift one summand), so the agent with the `(S + 1)`-st highest identifier is a
uniformly random member of `NC`: the probability of deciding `b` is the fraction of members of `NC`
preferring `b` (`seedMeasure_dictator`).
-/

namespace Podc.RationalConsensus.Cons

open Classical MeasureTheory

variable {n f p : ℕ} [NeZero p] [Fact (f < n)]

/-- The uniform seed measure counts. -/
lemma seedMeasure_apply (E : Set (Fin n → Seed n f p)) :
    seedMeasure n f p E = (Finset.univ.filter (· ∈ E)).card / Fintype.card (Fin n → Seed n f p) := by
  rw [seedMeasure, PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_uniformOfFintype_apply,
    Fintype.card_subtype]

section Dictator

variable (S : Finset (Fin n)) (t : Fin (f + 1))

/-- The sum of the secrets `x_l[t]`, `l ∈ S`, in `Fin (n - t)`. -/
def secretSum (ω : Fin n → Seed n f p) : Fin (n - t) :=
  haveI : NeZero (n - t) := ⟨by have := (Fact.out : f < n); have := t.2; omega⟩
  ∑ l ∈ S, (ω l t).1

omit [NeZero p] in
lemma secretSum_val (ω : Fin n → Seed n f p) :
    ((secretSum S t ω : Fin (n - t)) : ℕ) = (∑ l ∈ S, ((ω l t).1 : ℕ)) % (n - t) := by
  have : NeZero (n - t) := ⟨by have := (Fact.out : f < n); have := t.2; omega⟩
  unfold secretSum
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Fin.val_add, ih, Nat.add_mod_mod]

/-- Shift the secret `x_{l₀}[t]` by `d`. -/
def shiftSeed (l₀ : Fin n) (d : Fin (n - t)) (ω : Fin n → Seed n f p) : Fin n → Seed n f p :=
  haveI : NeZero (n - t) := ⟨by have := (Fact.out : f < n); have := t.2; omega⟩
  Function.update ω l₀ (Function.update (ω l₀) t ((ω l₀ t).1 + d, (ω l₀ t).2))

omit [NeZero p] in
lemma shiftSeed_injective (l₀ : Fin n) (d : Fin (n - t)) :
    Function.Injective (shiftSeed (f := f) (p := p) t l₀ d) := by
  have : NeZero (n - t) := ⟨by have := (Fact.out : f < n); have := t.2; omega⟩
  intro ω ω' h
  funext l
  by_cases hl : l = l₀
  · subst hl
    have h1 := congrFun h l
    simp only [shiftSeed, Function.update_self] at h1
    funext s
    have h2 := congrFun h1 s
    by_cases hs : s = t
    · subst hs
      simp only [Function.update_self, Prod.mk.injEq, add_left_inj] at h2
      exact Prod.ext h2.1 h2.2
    · simpa [Function.update_of_ne hs] using h2
  · simpa [shiftSeed, Function.update_of_ne hl] using congrFun h l

omit [NeZero p] in
lemma secretSum_shiftSeed {l₀ : Fin n} (hl₀ : l₀ ∈ S) (d : Fin (n - t))
    (ω : Fin n → Seed n f p) :
    secretSum S t (shiftSeed t l₀ d ω) = secretSum S t ω + d := by
  have : NeZero (n - t) := ⟨by have := (Fact.out : f < n); have := t.2; omega⟩
  unfold secretSum
  rw [← Finset.add_sum_erase _ _ hl₀, ← Finset.add_sum_erase _ _ hl₀]
  have : ∀ l ∈ S.erase l₀, (shiftSeed t l₀ d ω l t).1 = (ω l t).1 := by
    intro l hl
    simp [shiftSeed, Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [Finset.sum_congr rfl this]
  simp only [shiftSeed, Function.update_self]
  abel

/-- All values of `secretSum` are equally likely. -/
lemma card_secretSum_eq {l₀ : Fin n} (hl₀ : l₀ ∈ S) (j j' : Fin (n - t)) :
    (Finset.univ.filter fun ω : Fin n → Seed n f p => secretSum S t ω = j).card =
      (Finset.univ.filter fun ω : Fin n → Seed n f p => secretSum S t ω = j').card := by
  have : NeZero (n - t) := ⟨by have := (Fact.out : f < n); have := t.2; omega⟩
  have key : ∀ j j' : Fin (n - t),
      (Finset.univ.filter fun ω : Fin n → Seed n f p => secretSum S t ω = j).card ≤
        (Finset.univ.filter fun ω : Fin n → Seed n f p => secretSum S t ω = j').card := by
    intro j j'
    refine Finset.card_le_card_of_injOn (shiftSeed t l₀ (j' - j)) (fun ω hω => ?_)
      (fun ω _ ω' _ h => shiftSeed_injective t l₀ _ h)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
    rw [secretSum_shiftSeed S t hl₀, hω]
    abel
  exact le_antisymm (key j j') (key j' j)

lemma card_secretSum_mul {l₀ : Fin n} (hl₀ : l₀ ∈ S) (j : Fin (n - t)) :
    (Finset.univ.filter fun ω : Fin n → Seed n f p => secretSum S t ω = j).card * (n - t) =
      Fintype.card (Fin n → Seed n f p) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n → Seed n f p)))
    (t := Finset.univ) (f := secretSum S t) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl fun j' _ => card_secretSum_eq S t hl₀ j' j, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- **The random dictator.** The agent with the `(S + 1)`-st highest identifier in `S`, where
`S = Σ x_l[t] mod |S|`, prefers `b` with probability `#{l ∈ S | g l = b} / |S|`. -/
theorem seedMeasure_dictator (hS : S.card = n - t) (hne : S.Nonempty) (g : Fin n → Bool) (b : Bool) :
    seedMeasure n f p {ω | ((S.sort (· ≤ ·)).reverse[(∑ l ∈ S, ((ω l t).1 : ℕ)) % (n - t)]?).map g
        = some b} = (S.filter fun l => g l = b).card / S.card := by
  have : NeZero (n - t) := ⟨by have := (Fact.out : f < n); have := t.2; omega⟩
  obtain ⟨l₀, hl₀⟩ := hne
  set L := (S.sort (· ≤ ·)).reverse with hL
  have hLlen : L.length = n - t := by simp [hL, hS]
  have hLnd : L.Nodup := by simp [hL, Finset.sort_nodup]
  have hLmem : ∀ l, l ∈ L ↔ l ∈ S := by simp [hL]
  -- the dictator as a function of `secretSum`
  let D : Fin (n - t) → Fin n := fun j => L[(j : ℕ)]'(by rw [hLlen]; exact j.2)
  have hD : ∀ ω : Fin n → Seed n f p,
      L[(∑ l ∈ S, ((ω l t).1 : ℕ)) % (n - t)]? = some (D (secretSum S t ω)) := by
    intro ω
    simp only [D, ← secretSum_val]
    exact List.getElem?_eq_getElem _
  have hDinj : Function.Injective D := by
    intro j j' h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hLnd).1 h)
  have hDmem : ∀ j, D j ∈ S := fun j => (hLmem _).1 (List.getElem_mem _)
  have hDsurj : ∀ l ∈ S, ∃ j, D j = l := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ((hLmem l).2 hl)
    exact ⟨⟨k, hLlen ▸ hk⟩, rfl⟩
  -- the event, fibred over the values of `secretSum`
  set J := Finset.univ.filter fun j : Fin (n - t) => g (D j) = b
  have hJ : J.card = (S.filter fun l => g l = b).card := by
    rw [← Finset.card_image_of_injective _ hDinj]
    congr 1
    ext l
    simp only [J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨hDmem j, hj⟩
    · rintro ⟨hl, hb⟩
      obtain ⟨j, rfl⟩ := hDsurj l hl
      exact ⟨j, hb, rfl⟩
  set N := (Finset.univ.filter fun ω : Fin n → Seed n f p => secretSum S t ω = 0).card
  have hN : N * (n - t) = Fintype.card (Fin n → Seed n f p) := card_secretSum_mul S t hl₀ 0
  have hcard : (Finset.univ.filter (· ∈ {ω : Fin n → Seed n f p | (L[(∑ l ∈ S, ((ω l t).1 : ℕ)) %
      (n - t)]?).map g = some b})).card = J.card * N := by
    have : (Finset.univ.filter (· ∈ {ω : Fin n → Seed n f p | (L[(∑ l ∈ S, ((ω l t).1 : ℕ)) %
        (n - t)]?).map g = some b})) =
        J.biUnion fun j => Finset.univ.filter fun ω => secretSum S t ω = j := by
      ext ω
      simp [hD, J]
    rw [this, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun j _ => card_secretSum_eq S t hl₀ j 0, Finset.sum_const,
        smul_eq_mul]
    · intro j _ j' _ hjj'
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro ω _ h1 h2; exact hjj' (h1.symm.trans h2)
  rw [seedMeasure_apply]
  simp only [Set.mem_ofPred_eq] at hcard ⊢
  rw [hcard, ← hN, ← hJ, hS]
  have hN0 : (N : ENNReal) ≠ 0 := by
    have : 0 < Fintype.card (Fin n → Seed n f p) := Fintype.card_pos
    rw [← hN] at this
    exact_mod_cast (Nat.pos_of_mul_pos_right this).ne'
  push_cast
  rw [mul_comm (N : ENNReal), ENNReal.mul_div_mul_right _ _ hN0 (ENNReal.natCast_ne_top _)]

end Dictator

end Podc.RationalConsensus.Cons
