import Papers.PODC2020.MISInapproxCongest.Reduction

/-!
# Non-vacuity of `ApproxMIS`

For every finite node set `V` there is a deterministic CONGEST algorithm (with large bandwidth)
that computes an exact maximum-weight independent set within `|V|` rounds on every graph with
weights `≤ |V|`; hence the hypothesis `ApproxMIS A γ T ε` of the main theorems is satisfiable for
all `γ ≤ 1`, `ε ≥ 0`.

The algorithm is full-information flooding: a node's state is a finite set of *facts* (weights
`(a, w a)` and edges `(a, b)`); every round it sends all of them to every neighbour, merges what it
receives, and records the edges to the neighbours it heard from. After `|V|` rounds every node
knows exactly the weights and edges of its connected component and outputs its membership in a
canonical maximum-weight independent set of that component.
-/

namespace Podc.MISInapproxCongest

open Finset Cslib.Congest

namespace NonVacuity

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Facts: a weight `(a, w a)` (capped at `|V|`) or an edge `(a, b)`. -/
abbrev Fact (V : Type) [Fintype V] := (V × Fin (Fintype.card V + 1)) ⊕ (V × V)

/-- Knowledge of a node: a finite set of facts. -/
abbrev Know (V : Type) [Fintype V] := Finset (Fact V)

/-- Bits needed to encode an element of `α`. -/
noncomputable def bits (α : Type) [Fintype α] : ℕ := Nat.clog 2 (Fintype.card α)

/-- Injective binary encoding. -/
noncomputable def enc {α : Type} [Fintype α] : α → Msg (bits α) := fun k =>
  (Fintype.equivFin (Msg (bits α))).symm
    (Fin.castLE (by
      have : Fintype.card (Msg (bits α)) = 2 ^ bits α := by simp [Msg]
      rw [this]
      exact Nat.le_pow_clog (by norm_num) _) (Fintype.equivFin α k))

lemma enc_injective {α : Type} [Fintype α] : Function.Injective (enc (α := α)) := by
  intro a b h
  simp only [enc, EmbeddingLike.apply_eq_iff_eq, Fin.castLE_inj] at h
  exact h

/-- Decoding. -/
noncomputable def dec {α : Type} [Fintype α] [Nonempty α] : Msg (bits α) → α :=
  Function.invFun enc

lemma dec_enc {α : Type} [Fintype α] [Nonempty α] (k : α) : dec (enc k) = k :=
  Function.leftInverse_invFun enc_injective k

/-- Weight capped at `|V|`. -/
def cap (x : ℕ) : Fin (Fintype.card V + 1) := ⟨min x (Fintype.card V), by omega⟩

/-- Nodes whose weight is known. -/
noncomputable def supp (K : Know V) : Finset V := by
  classical exact univ.filter fun a => ∃ j, Sum.inl (a, j) ∈ K

/-- Known weight (`0` if unknown). -/
noncomputable def wt (K : Know V) (a : V) : ℕ := by
  classical
  exact if h : ∃ j, Sum.inl (a, j) ∈ K then (Classical.choose h : Fin _).val else 0

/-- `I` is independent in the known graph. -/
def KIndep (K : Know V) (I : Finset V) : Prop := ∀ a ∈ I, ∀ b ∈ I, Sum.inr (a, b) ∉ K

/-- Candidate sets: known-independent sets of known nodes. -/
noncomputable def cands (K : Know V) : Finset (Finset V) := by
  classical exact (supp K).powerset.filter (KIndep K)

lemma cands_nonempty (K : Know V) : (cands K).Nonempty :=
  ⟨∅, by classical simp [cands, KIndep]⟩

lemma exists_best (K : Know V) :
    ∃ I ∈ cands K, ∀ I' ∈ cands K, ∑ a ∈ I', wt K a ≤ ∑ a ∈ I, wt K a :=
  exists_max_image _ _ (cands_nonempty K)

/-- A canonical maximum-weight independent set of the known graph. -/
noncomputable def best (K : Know V) : Finset V := Classical.choose (exists_best K)

lemma best_mem (K : Know V) : best K ∈ cands K := (Classical.choose_spec (exists_best K)).1

lemma best_max (K : Know V) {I : Finset V} (hI : I ∈ cands K) :
    ∑ a ∈ I, wt K a ≤ ∑ a ∈ best K, wt K a :=
  (Classical.choose_spec (exists_best K)).2 I hI

lemma mem_cands {K : Know V} {I : Finset V} : I ∈ cands K ↔ I ⊆ supp K ∧ KIndep K I := by
  classical
  unfold cands
  rw [mem_filter, mem_powerset]

lemma mem_supp {K : Know V} {a : V} : a ∈ supp K ↔ ∃ j, Sum.inl (a, j) ∈ K := by
  classical
  unfold supp
  rw [mem_filter]
  simp only [mem_univ, true_and]

/-- The flooding algorithm. -/
noncomputable def alg (V : Type) [Fintype V] [DecidableEq V] :
    Algorithm V (ℕ × Unit) (Know V) (bits (Know V)) := by
  classical
  exact
  { init := fun v x => {Sum.inl (v, cap x.1)}
    send := fun _ K _ => enc K
    step := fun v K m => K ∪ univ.filter (fun f => ∃ u c, m u = some c ∧ f ∈ dec c) ∪
      univ.filter (fun f => ∃ u, (m u).isSome ∧ (f = Sum.inr (v, u) ∨ f = Sum.inr (u, v)))
    out := fun v K => decide (v ∈ best K) }

variable (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → ℕ × Unit)

lemma mem_run_zero {v : V} {f : Fact V} :
    f ∈ (alg V).run G inp 0 v ↔ f = Sum.inl (v, cap (inp v).1) := by
  simp [Algorithm.run, alg]

lemma mem_run_succ {t : ℕ} {v : V} {f : Fact V} :
    f ∈ (alg V).run G inp (t + 1) v ↔ f ∈ (alg V).run G inp t v ∨
      (∃ u, G.Adj u v ∧ f ∈ (alg V).run G inp t u) ∨
      (∃ u, G.Adj u v ∧ (f = Sum.inr (v, u) ∨ f = Sum.inr (u, v))) := by
  simp only [Algorithm.run]
  simp only [alg, mem_union, mem_filter, mem_univ, true_and]
  refine or_assoc.trans (or_congr Iff.rfl (or_congr ?_ ?_))
  · constructor
    · rintro ⟨u, c, hc, hf⟩
      by_cases hu : G.Adj u v
      · simp only [hu, ↓reduceIte, Option.some.injEq] at hc
        subst hc
        rw [dec_enc] at hf
        exact ⟨u, hu, hf⟩
      · simp [hu] at hc
    · rintro ⟨u, hu, hf⟩
      exact ⟨u, _, by simp only [hu, ↓reduceIte]; rfl, by rw [dec_enc]; exact hf⟩
  · constructor
    · rintro ⟨u, hu, hf⟩
      by_cases h : G.Adj u v
      · exact ⟨u, h, hf⟩
      · simp [h] at hu
    · rintro ⟨u, hu, hf⟩
      exact ⟨u, by simp [hu], hf⟩

/-- Validity of a fact for node `v`: true and about `v`'s connected component. -/
def Valid (v : V) : Fact V → Prop
  | Sum.inl (a, j) => j = cap (inp a).1 ∧ G.Reachable v a
  | Sum.inr (a, b) => G.Adj a b ∧ G.Reachable v a

lemma Valid.of_adj {u v : V} (huv : G.Adj u v) {f : Fact V} (h : Valid G inp u f) :
    Valid G inp v f := by
  have hr : G.Reachable v u := huv.symm.reachable
  rcases f with ⟨a, j⟩ | ⟨a, b⟩
  · exact ⟨h.1, hr.trans h.2⟩
  · exact ⟨h.1, hr.trans h.2⟩

/-- **Soundness**: all known facts are valid. -/
lemma sound : ∀ (t : ℕ) (v : V) (f : Fact V), f ∈ (alg V).run G inp t v → Valid G inp v f
  | 0, v, f, h => by
    rw [mem_run_zero] at h
    subst h
    exact ⟨rfl, SimpleGraph.Reachable.refl v⟩
  | t + 1, v, f, h => by
    rcases (mem_run_succ G inp).1 h with h | ⟨u, hu, h⟩ | ⟨u, hu, rfl | rfl⟩
    · exact sound t v f h
    · exact (sound t u f h).of_adj G inp hu
    · exact ⟨hu.symm, SimpleGraph.Reachable.refl v⟩
    · exact ⟨hu, hu.symm.reachable⟩

lemma run_mono_succ (t : ℕ) (v : V) : (alg V).run G inp t v ⊆ (alg V).run G inp (t + 1) v :=
  fun _ h => (mem_run_succ G inp).2 (Or.inl h)

lemma run_mono {s t : ℕ} (hst : s ≤ t) (v : V) :
    (alg V).run G inp s v ⊆ (alg V).run G inp t v := by
  induction hst with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (run_mono_succ G inp _ v)

/-- Facts propagate along walks, one edge per round. -/
lemma propagate {f : Fact V} {s : ℕ} {a : V} (hf : f ∈ (alg V).run G inp s a) :
    ∀ {v : V} (p : G.Walk v a), f ∈ (alg V).run G inp (s + p.length) v
  | _, .nil => by simpa using hf
  | v, .cons (v := u) hvu q => by
    have ih := propagate hf q
    rw [SimpleGraph.Walk.length_cons, ← add_assoc]
    exact (mem_run_succ G inp).2 (Or.inr (Or.inl ⟨u, hvu.symm, ih⟩))

lemma exists_short_walk {v a : V} (h : G.Reachable v a) :
    ∃ p : G.Walk v a, p.length < Fintype.card V := by
  obtain ⟨p⟩ := h
  exact ⟨p.bypass, p.bypass_isPath.length_lt⟩

/-- **Completeness**: after `|V|` rounds every valid fact is known. -/
lemma complete {v : V} {f : Fact V} (hf : Valid G inp v f) :
    f ∈ (alg V).run G inp (Fintype.card V) v := by
  rcases f with ⟨a, j⟩ | ⟨a, b⟩
  · obtain ⟨rfl, hr⟩ := hf
    obtain ⟨p, hp⟩ := exists_short_walk G hr
    have h0 : Sum.inl (a, cap (inp a).1) ∈ (alg V).run G inp 0 a := (mem_run_zero G inp).2 rfl
    have := propagate G inp h0 p
    exact run_mono G inp (by omega) v this
  · obtain ⟨hab, hr⟩ := hf
    obtain ⟨p, hp⟩ := exists_short_walk G hr
    have h1 : (Sum.inr (a, b) : Fact V) ∈ (alg V).run G inp 1 a :=
      (mem_run_succ G inp).2 (Or.inr (Or.inr ⟨b, hab.symm, Or.inl rfl⟩))
    have := propagate G inp h1 p
    exact run_mono G inp (by omega) v this

/-- The exact knowledge of the component of `v`. -/
noncomputable def KC (v : V) : Know V := by
  classical exact univ.filter (Valid G inp v)

lemma mem_KC {v : V} {f : Fact V} : f ∈ KC G inp v ↔ Valid G inp v f := by
  classical
  unfold KC
  rw [mem_filter]
  simp only [mem_univ, true_and]

lemma run_eq_KC (v : V) : (alg V).run G inp (Fintype.card V) v = KC G inp v := by
  ext f
  rw [mem_KC]
  exact ⟨sound G inp _ v f, complete G inp⟩

lemma KC_eq_of_reachable {u v : V} (h : G.Reachable u v) : KC G inp u = KC G inp v := by
  ext f
  rw [mem_KC, mem_KC]
  rcases f with ⟨a, j⟩ | ⟨a, b⟩
  · exact and_congr Iff.rfl ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
  · exact and_congr Iff.rfl ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

lemma mem_supp_KC {v a : V} : a ∈ supp (KC G inp v) ↔ G.Reachable v a := by
  rw [mem_supp]
  constructor
  · rintro ⟨j, hj⟩
    exact ((mem_KC G inp).1 hj).2
  · intro h
    exact ⟨cap (inp a).1, (mem_KC G inp).2 ⟨rfl, h⟩⟩

lemma wt_KC {v a : V} (h : G.Reachable v a) : wt (KC G inp v) a = (cap (V := V) (inp a).1).val := by
  classical
  unfold wt
  have hex : ∃ j, Sum.inl (a, j) ∈ KC G inp v := ⟨cap (inp a).1, (mem_KC G inp).2 ⟨rfl, h⟩⟩
  simp only [hex, ↓reduceDIte]
  exact congrArg Fin.val ((mem_KC G inp).1 (Classical.choose_spec hex)).1

/-- The output set, written via the knowledge `KC`. -/
noncomputable def O : Finset V := by
  classical exact univ.filter fun v => v ∈ best (KC G inp v)

lemma mem_O {v : V} : v ∈ O G inp ↔ v ∈ best (KC G inp v) := by
  classical
  unfold O
  rw [mem_filter]
  simp only [mem_univ, true_and]

lemma O_indep : IsIndep G (O G inp) := by
  intro u hu v hv huv
  rw [mem_O] at hu hv
  have hKC : KC G inp v = KC G inp u := KC_eq_of_reachable G inp huv.reachable.symm
  rw [hKC] at hv
  exact (mem_cands.1 (best_mem (KC G inp u))).2 u hu v hv
    ((mem_KC G inp).2 ⟨huv, SimpleGraph.Reachable.refl u⟩)

lemma O_opt (hw : ∀ v, (inp v).1 ≤ Fintype.card V) {J : Finset V} (hJ : IsIndep G J) :
    wsum (fun v => (inp v).1) J ≤ wsum (fun v => (inp v).1) (O G inp) := by
  classical
  have hcap : ∀ a, (cap (inp a).1 : Fin (Fintype.card V + 1)).val = (inp a).1 := fun a => by
    simp [cap, hw a]
  unfold wsum
  rw [← sum_fiberwise_of_maps_to (s := J) (t := univ.image (KC G inp)) (g := KC G inp)
      (fun i _ => mem_image_of_mem _ (mem_univ i)),
    ← sum_fiberwise_of_maps_to (s := O G inp) (t := univ.image (KC G inp)) (g := KC G inp)
      (fun i _ => mem_image_of_mem _ (mem_univ i))]
  refine sum_le_sum fun K hK => ?_
  obtain ⟨r, -, rfl⟩ := mem_image.1 hK
  have hO : (O G inp).filter (fun x => KC G inp x = KC G inp r) = best (KC G inp r) := by
    ext x
    rw [mem_filter, mem_O]
    constructor
    · rintro ⟨h1, h2⟩
      rwa [h2] at h1
    · intro h
      have hx : G.Reachable r x := (mem_supp_KC G inp).1 ((mem_cands.1 (best_mem _)).1 h)
      have he := KC_eq_of_reachable G inp hx
      exact ⟨by rwa [← he], he.symm⟩
  have hJr : J.filter (fun x => KC G inp x = KC G inp r) ∈ cands (KC G inp r) := by
    rw [mem_cands]
    refine ⟨fun x hx => ?_, fun a ha b hb hab => ?_⟩
    · rw [mem_filter] at hx
      rw [← hx.2, mem_supp_KC]
    · exact hJ a (mem_filter.1 ha).1 b (mem_filter.1 hb).1 ((mem_KC G inp).1 hab).1
  have hsupp : ∀ I ∈ cands (KC G inp r),
      ∑ x ∈ I, wt (KC G inp r) x = ∑ x ∈ I, (inp x).1 := by
    intro I hI
    refine sum_congr rfl fun x hx => ?_
    rw [wt_KC G inp ((mem_supp_KC G inp).1 ((mem_cands.1 hI).1 hx)), hcap]
  rw [hO, ← hsupp _ (best_mem _), ← hsupp _ hJr]
  exact best_max _ hJr

lemma outSet_eq (w : V → ℕ) (r : V → Unit) :
    outSet (alg V) G w r (Fintype.card V) = O G (fun v => (w v, r v)) := by
  classical
  ext v
  unfold outSet
  rw [mem_filter, mem_O, ← run_eq_KC]
  simp [alg]

end NonVacuity

open NonVacuity in
/-- **Non-vacuity of `ApproxMIS`.** For every finite node set there is a deterministic CONGEST
algorithm (full-information flooding, bandwidth `B = ⌈log₂ |σ|⌉`, `T = |V|` rounds) that outputs a
maximum-weight independent set on every graph with weights `≤ |V|`; in particular it satisfies
`ApproxMIS A γ T ε` for all `γ ≤ 1` and `ε ≥ 0`. -/
theorem exists_approxMIS (V : Type) [Fintype V] [DecidableEq V] :
    ∃ (B T : ℕ) (σ : Type) (A : Cslib.Congest.Algorithm V (ℕ × Unit) σ B),
      ∀ γ : ℝ, γ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ApproxMIS A γ T ε := by
  refine ⟨_, Fintype.card V, _, alg V, fun γ hγ ε hε G _ w hw => ?_⟩
  have happ : ∀ r : V → Unit, IsApprox γ G w (outSet (alg V) G w r (Fintype.card V)) := by
    intro r
    rw [outSet_eq]
    refine ⟨O_indep G _, ?_⟩
    have hle : opt G w ≤ wsum w (O G fun v => (w v, r v)) :=
      opt_le fun J hJ => O_opt G (fun v => (w v, r v)) hw hJ
    have h0 : (0 : ℝ) ≤ opt G w := Nat.cast_nonneg _
    calc γ * opt G w ≤ 1 * opt G w := mul_le_mul_of_nonneg_right hγ h0
      _ = opt G w := one_mul _
      _ ≤ _ := by exact_mod_cast hle
  unfold ApproxOn failCount
  simp only [happ, not_true_eq_false, filter_false, card_empty, Nat.cast_zero]
  exact mul_nonneg hε (Nat.cast_nonneg _)

end Podc.MISInapproxCongest
