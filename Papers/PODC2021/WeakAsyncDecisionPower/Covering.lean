import Podc.Computability.Distributed.DistributedAutomata.Fairness

/-!
# Adversarial selection cannot distinguish a graph from its coverings (Lemma 3.2, Corollary 3.3)

Czerner, Guttenberg, Helfrich, Esparza, *Decision Power of Weak Asynchronous Models of Distributed
Computing*, PODC 2021 (arXiv:2102.11630v2), Section 3.

* `IsCovering H G f`: `f` is a covering map (surjective, label-preserving, bijective on
  neighbourhoods).
* `lemma_3_2`: an automaton with adversarial scheduling (any selection constraint, any counting
  bound, any acceptance) accepts `G` iff it accepts any covering `H` of `G`.
* `corollary_3_3`: if it decides a labelling property, it cannot distinguish label counts `L` and
  `λ • L`, also when restricted to graphs of maximum degree `k ≥ 2`. The witnesses are labelled
  cycles `cycleL` on `ZMod m` and the `λ`-fold covering `ZMod (λ n) → ZMod n`.
-/

namespace Podc.WeakAsyncDecisionPower

open Cslib.DistributedAutomata Set

variable {Λ Q : Type*}

/-- `f : H → G` is a covering map: a surjection that preserves labels and maps the neighbourhood
of every node bijectively onto the neighbourhood of its image. -/
structure IsCovering (H G : LGraph Λ) (f : H.V → G.V) : Prop where
  surjective : Function.Surjective f
  label_eq : ∀ v, G.label (f v) = H.label v
  bijOn : ∀ v, BijOn f {u | H.graph.Adj v u} {x | G.graph.Adj (f v) x}

lemma IsCovering.not_adj_of_eq {H G : LGraph Λ} {f : H.V → G.V} (hf : IsCovering H G f)
    {u u' : H.V} (h : f u = f u') : ¬ H.graph.Adj u u' := by
  intro hadj
  have := (hf.bijOn u).mapsTo hadj
  simp only [mem_ofPred_eq] at this
  rw [h] at this
  exact G.graph.irrefl this

/-- **Lemma 3.2.** Let `A` be an automaton with adversarial scheduling (a `DAf`-automaton; the
selection constraint is arbitrary). If `H` covers `G`, then `A` accepts `G` iff it accepts `H`. -/
theorem lemma_3_2 (A : Automaton Λ Q) (hfair : A.fair = .adversarial) {k : ℕ∞}
    (hA : A.Consistent k) {G H : LGraph Λ} (hG : G.Admissible k) (hH : H.Admissible k)
    {f : H.V → G.V} (hf : IsCovering H G f) : A.Accepts G ↔ A.Accepts H := by
  have := hG.nonempty
  obtain ⟨σ, hσ⟩ := exists_fair (V := G.V) A.sel A.fair
  let R : ℕ → Set H.V := fun t => f ⁻¹' σ t
  have hR : ∀ t, A.sel.Liftable H.graph (R t) := by
    intro t
    have hp := hσ.1 t
    cases hsel : A.sel with
    | liberal => trivial
    | exclusive =>
      rw [hsel] at hp
      obtain ⟨v, hv⟩ := hp
      refine ⟨fun a ha b hb _ => hf.not_adj_of_eq ?_, ?_⟩
      · simp only [R, hv, mem_preimage, mem_singleton_iff] at ha hb; rw [ha, hb]
      · obtain ⟨u, hu⟩ := hf.surjective v
        exact ⟨u, by simp [R, hv, hu]⟩
    | synchronous =>
      rw [hsel] at hp
      show f ⁻¹' σ t = univ
      rw [show σ t = univ from hp, preimage_univ]
  have hRfair : ∀ v N, ∃ t ≥ N, v ∈ R t := fun v N => hσ.2.1 (f v) N
  obtain ⟨σ', hσ', hev⟩ := exists_fair_of_liftable A.M H.graph A.sel R hR hRfair (A.init H)
  rw [← hfair] at hσ'
  have hinit : A.init H = A.init G ∘ f := by
    funext v; simp [Automaton.init, hf.label_eq]
  have hlift : ∀ t, runFrom A.M H.graph (A.init H) R t = A.run G σ t ∘ f := by
    intro t
    rw [hinit]
    exact sim_global A.M G.graph H.graph f σ (A.init G)
      (fun C w => view_comp_of_bijOn (hf.bijOn w) C) t
  rw [A.accepts_iff hA hG hσ, A.accepts_iff hA hH hσ']
  simp only [Automaton.run]
  rw [hev]
  constructor
  · rintro ⟨t₀, ht₀⟩
    refine ⟨t₀, fun t ht v => ?_⟩
    rw [hlift]
    exact ht₀ t ht (f v)
  · rintro ⟨t₀, ht₀⟩
    refine ⟨t₀, fun t ht v => ?_⟩
    obtain ⟨u, rfl⟩ := hf.surjective v
    have := ht₀ t ht u
    rw [hlift] at this
    exact this

/-! ### Labelled cycles and their coverings -/

/-- The cycle on `ZMod m`. -/
def cyc (m : ℕ) : SimpleGraph (ZMod m) := SimpleGraph.fromRel fun u v => v = u + 1

lemma cyc_adj {m : ℕ} {u v : ZMod m} : (cyc m).Adj u v ↔ u ≠ v ∧ (v = u + 1 ∨ u = v + 1) := by
  simp [cyc]

lemma two_ne_zero_zmod {m : ℕ} (hm : 3 ≤ m) : (2 : ZMod m) ≠ 0 := by
  have : ((2 : ℕ) : ZMod m) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  simpa using this

lemma one_ne_zero_zmod {m : ℕ} (hm : 3 ≤ m) : (1 : ZMod m) ≠ 0 := by
  have : ((1 : ℕ) : ZMod m) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  simpa using this

lemma cyc_nbr {m : ℕ} (hm : 3 ≤ m) (u : ZMod m) : {v | (cyc m).Adj u v} = {u + 1, u - 1} := by
  ext v
  simp only [mem_ofPred_eq, cyc_adj, mem_insert_iff, mem_singleton_iff]
  have h1 := one_ne_zero_zmod hm
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl h
    · right; rw [h]; ring
  · rintro (h | h)
    · refine ⟨fun h' => h1 ?_, Or.inl h⟩
      have : u + 1 - u = u - u := by rw [← h, h']
      simpa using this
    · refine ⟨fun h' => h1 ?_, Or.inr (by rw [h]; ring)⟩
      have : u - (u - 1) = u - u := by rw [← h, h']
      simpa using this

lemma cyc_connected (m : ℕ) [NeZero m] (hm : 3 ≤ m) : (cyc m).Connected := by
  have h1 := one_ne_zero_zmod hm
  have hreach : ∀ n : ℕ, (cyc m).Reachable 0 (n : ZMod m) := by
    intro n
    induction n with
    | zero => simpa using SimpleGraph.Reachable.refl _
    | succ n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [cyc_adj]
      refine ⟨fun h => h1 ?_, Or.inl (by push_cast; ring)⟩
      have : ((n + 1 : ℕ) : ZMod m) - n = (n : ZMod m) - n := by rw [h]
      simpa using this
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, fun u => by simpa using hreach u.val⟩

/-- A labelled cycle of length `m`. -/
def cycleL (m : ℕ) [NeZero m] (lab : ZMod m → Λ) : LGraph Λ where
  V := ZMod m
  graph := cyc m
  label := lab

lemma cycleL_admissible {m : ℕ} [NeZero m] (hm : 3 ≤ m) (lab : ZMod m → Λ) {k : ℕ∞}
    (hk : 2 ≤ k) : (cycleL m lab).Admissible k where
  connected := cyc_connected m hm
  three_le := by simp [cycleL, Nat.card_zmod, hm]
  degree_le := by
    intro (v : ZMod m)
    show (({u : ZMod m | (cyc m).Adj v u}.ncard : ℕ) : ℕ∞) ≤ k
    rw [cyc_nbr hm]
    refine le_trans ?_ hk
    exact_mod_cast (ncard_insert_le _ _).trans (by simp)

/-- The additive projection `ZMod m → ZMod n` (for `n ∣ m`) is a covering of cycles. -/
lemma cyc_covering {m n : ℕ} [NeZero m] [NeZero n] (hm : 3 ≤ m) (hn : 3 ≤ n) (hnm : n ∣ m)
    (lab : ZMod n → Λ) :
    IsCovering (cycleL m (lab ∘ ZMod.castHom hnm (ZMod n))) (cycleL n lab)
      (ZMod.castHom hnm (ZMod n)) where
  surjective := ZMod.castHom_surjective hnm
  label_eq := fun _ => rfl
  bijOn := by
    intro (u : ZMod m)
    show BijOn (ZMod.castHom hnm (ZMod n)) {v : ZMod m | (cyc m).Adj u v}
      {x : ZMod n | (cyc n).Adj (ZMod.castHom hnm (ZMod n) u) x}
    rw [cyc_nbr hm, cyc_nbr hn]
    set f := ZMod.castHom hnm (ZMod n)
    have h2 := two_ne_zero_zmod hn
    refine ⟨?_, ?_, ?_⟩
    · rintro v (rfl | rfl) <;> simp [map_add, map_sub, map_one]
    · rintro a (rfl | rfl) b (rfl | rfl) hab
      · rfl
      · exfalso; apply h2; simp [map_add, map_sub, map_one] at hab
        linear_combination hab
      · exfalso; apply h2; simp [map_add, map_sub, map_one] at hab
        linear_combination -hab
      · rfl
    · rintro x (rfl | rfl)
      · exact ⟨u + 1, by simp, by simp⟩
      · exact ⟨u - 1, by simp, by simp⟩

/-- Preimages under a surjective additive map `ZMod m → ZMod n` have `m / n` times as many
elements. -/
lemma ncard_preimage_castHom {m n : ℕ} [NeZero m] [NeZero n] (hnm : n ∣ m) (S : Set (ZMod n)) :
    (ZMod.castHom hnm (ZMod n) ⁻¹' S).ncard = (m / n) * S.ncard := by
  classical
  set f := ZMod.castHom hnm (ZMod n)
  have hsurj := ZMod.castHom_surjective hnm
  let c := (Finset.univ.filter fun g : ZMod m => f g = 0).card
  have hfib : ∀ y, (Finset.univ.filter fun g : ZMod m => f g = y).card = c := fun y =>
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hsurj y) (hsurj 0)
  have hpre : ∀ T : Finset (ZMod n),
      (Finset.univ.filter fun g : ZMod m => f g ∈ T).card = T.card * c := by
    intro T
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := T) (fun g hg => by simpa using hg)]
    rw [Finset.sum_congr rfl (g := fun _ => c), Finset.sum_const, smul_eq_mul]
    intro y hy
    rw [← hfib y]
    congr 1; ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro h; exact ⟨h ▸ hy, h⟩
  have hc : m = n * c := by
    have := hpre Finset.univ
    simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, ZMod.card] at this
    exact this
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmn : m / n = c := by rw [hc, Nat.mul_div_cancel_left _ hn0]
  rw [hmn, Set.ncard_eq_toFinset_card' (f ⁻¹' S),
    Set.ncard_eq_toFinset_card' S, mul_comm]
  have := hpre S.toFinset
  convert this using 2
  ext g; simp

/-- **Corollary 3.3.** Let `A` be an automaton with adversarial scheduling that decides a labelling
property, on graphs of maximum degree `k ≥ 2` (`k = ⊤`: arbitrary graphs). If `L_H = λ • L_G` with
`λ > 0`, then `A` accepts `G` iff it accepts `H`. -/
theorem corollary_3_3 (A : Automaton Λ Q) (hfair : A.fair = .adversarial) {k : ℕ∞} (hk : 2 ≤ k)
    (hA : A.Consistent k) (hL : A.IsLabelling k) {G H : LGraph Λ} (hG : G.Admissible k)
    (hH : H.Admissible k) {l : ℕ} (hl : 0 < l) (hcount : H.count = l • G.count) :
    A.Accepts G ↔ A.Accepts H := by
  set n := Nat.card G.V with hn_def
  have hn : 3 ≤ n := hG.three_le
  have : NeZero n := ⟨by omega⟩
  have : NeZero (l * n) := ⟨by positivity⟩
  obtain ⟨e⟩ : Nonempty (ZMod n ≃ G.V) := Finite.card_eq.1 (by rw [Nat.card_zmod])
  have hnm : n ∣ l * n := dvd_mul_left n l
  let G' := cycleL n (G.label ∘ e)
  let H' := cycleL (l * n) ((G.label ∘ e) ∘ ZMod.castHom hnm (ZMod n))
  have hG' : G'.Admissible k := cycleL_admissible hn _ hk
  have hH' : H'.Admissible k := cycleL_admissible (by nlinarith) _ hk
  have hcG : G'.count = G.count := by
    funext ℓ
    simp only [LGraph.count, G', cycleL, Function.comp]
    rw [show {x : ZMod n | G.label (e x) = ℓ} = e ⁻¹' {v | G.label v = ℓ} from rfl,
      ncard_preimage_of_injective_subset_range e.injective (by simp)]
  have hcH : H'.count = H.count := by
    funext ℓ
    rw [hcount, ← hcG]
    simp only [LGraph.count, H', G', cycleL, Function.comp, Pi.smul_apply, smul_eq_mul]
    rw [show {x : ZMod (l * n) | G.label (e (ZMod.castHom hnm (ZMod n) x)) = ℓ} =
      ZMod.castHom hnm (ZMod n) ⁻¹' {y | G.label (e y) = ℓ} from rfl,
      ncard_preimage_castHom hnm, Nat.mul_div_cancel _ (by omega)]
  rw [hL G G' hG hG' hcG.symm, hL H H' hH hH' hcH.symm]
  exact lemma_3_2 A hfair hA hG' hH' (cyc_covering (by nlinarith) hn hnm _)

end Podc.WeakAsyncDecisionPower
