import Podc.Foundations.Combinatorics.SimpleGraph.EdgeColoring.Basic

/-!
# Round-scheduled greedy edge colouring

Lemma 5.1 and Theorem 5.2 of the paper colour the edges of a graph round by round: some edges are
already coloured (`pre`, colouring `c₀`); every other edge `e` is coloured in round `time e` by one
of its endpoints, which picks a colour `< K` different from the colours of all adjacent edges that
are pre-coloured or coloured in an earlier round **or in the same round** (`EdgeSchedule.Follows`).
The schedules of the paper guarantee that two adjacent edges coloured in the same round are chosen by
their common endpoint, so this rule can be executed locally (see `Lemma51`/`Theorem52`).

* `EdgeSchedule.Follows.isEdgeColoring`: every colouring following the rule is proper (given that
  `c₀` is proper on the pre-coloured edges).
* `EdgeSchedule.exists_follows`: the rule can always be followed if every edge has fewer than `K`
  adjacent edges that are pre-coloured or not scheduled later ("load" `< K`).

-- CSLib candidate: `Cslib/Foundations/Combinatorics/SimpleGraph/EdgeColoring/Scheduled.lean`
-/

open Finset

namespace Podc.DeltaEdgeColoring

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A colouring schedule: `pre e` means `e` is coloured beforehand; otherwise `e` is coloured in
round `time e`. -/
structure EdgeSchedule (V : Type*) where
  /-- The pre-coloured edges. -/
  pre : Sym2 V → Prop
  /-- The round in which a non-pre-coloured edge is coloured. -/
  time : Sym2 V → ℕ

namespace EdgeSchedule

variable (σ : EdgeSchedule V) (G : SimpleGraph V)

/-- The rule of the round-by-round algorithm: pre-coloured edges keep their colour `c₀`; every other
edge `uv` gets a colour `< K` that differs from the colour of every other edge `uw` at `u` that is
pre-coloured or coloured no later than `uv` (this is required at both endpoints, as `u` ranges over
both). -/
def Follows (c₀ c : Sym2 V → ℕ) (K : ℕ) : Prop :=
  (∀ ⦃u v⦄, G.Adj u v → σ.pre s(u, v) → c s(u, v) = c₀ s(u, v)) ∧
  ∀ ⦃u v⦄, G.Adj u v → ¬ σ.pre s(u, v) → c s(u, v) < K ∧
    ∀ ⦃w⦄, G.Adj u w → w ≠ v → (σ.pre s(u, w) ∨ σ.time s(u, w) ≤ σ.time s(u, v)) →
      c s(u, w) ≠ c s(u, v)

variable {σ G}

/-- Every colouring that follows the rule is a proper edge colouring, provided that the
pre-colouring is proper on the pre-coloured edges. -/
theorem Follows.isEdgeColoring {c₀ c : Sym2 V → ℕ} {K : ℕ} (hf : σ.Follows G c₀ c K)
    (hc₀ : ∀ ⦃u v w⦄, G.Adj u v → G.Adj u w → σ.pre s(u, v) → σ.pre s(u, w) →
      c₀ s(u, v) = c₀ s(u, w) → v = w) :
    G.IsEdgeColoring c := by
  intro u v w huv huw he
  by_contra hvw
  by_cases hpv : σ.pre s(u, v) <;> by_cases hpw : σ.pre s(u, w)
  · rw [hf.1 huv hpv, hf.1 huw hpw] at he
    exact hvw (hc₀ huv huw hpv hpw he)
  · exact (hf.2 huw hpw).2 huv hvw (Or.inl hpv) he
  · exact (hf.2 huv hpv).2 huw (Ne.symm hvw) (Or.inl hpw) he.symm
  · rcases le_total (σ.time s(u, w)) (σ.time s(u, v)) with h | h
    · exact (hf.2 huv hpv).2 huw (Ne.symm hvw) (Or.inr h) he.symm
    · exact (hf.2 huw hpw).2 huv hvw (Or.inr h) he

/-- A colouring following the rule uses the colours `< max k₀ K` if `c₀` uses colours `< k₀` on the
pre-coloured edges. -/
theorem Follows.isProperEdgeColoring {c₀ c : Sym2 V → ℕ} {K k₀ : ℕ} (hf : σ.Follows G c₀ c K)
    (hc₀ : ∀ ⦃u v w⦄, G.Adj u v → G.Adj u w → σ.pre s(u, v) → σ.pre s(u, w) →
      c₀ s(u, v) = c₀ s(u, w) → v = w)
    (hk₀ : ∀ ⦃u v⦄, G.Adj u v → σ.pre s(u, v) → c₀ s(u, v) < k₀) :
    G.IsProperEdgeColoring c (max k₀ K) := by
  refine ⟨fun u v huv => ?_, hf.isEdgeColoring hc₀⟩
  by_cases hp : σ.pre s(u, v)
  · rw [hf.1 huv hp]; exact lt_max_of_lt_left (hk₀ huv hp)
  · exact lt_max_of_lt_right (hf.2 huv hp).1

open Classical in
/-- The load of the edge `uv` at its endpoint `u`: the other edges `uw` that are pre-coloured or not
scheduled after `uv`. -/
noncomputable def load (σ : EdgeSchedule V) (G : SimpleGraph V) (u v : V) : Finset V :=
  {w | G.Adj u w ∧ w ≠ v ∧ (σ.pre s(u, w) ∨ σ.time s(u, w) ≤ σ.time s(u, v))}

open Classical in
/-- **Feasibility of the rule.** If for every non-pre-coloured edge `uv` fewer than `K` adjacent
edges are pre-coloured or not scheduled after `uv`, then some colouring follows the rule. (The
colours can be chosen greedily in the order of the rounds.) -/
theorem exists_follows (c₀ : Sym2 V → ℕ) {K : ℕ}
    (hload : ∀ ⦃u v⦄, G.Adj u v → ¬ σ.pre s(u, v) →
      #(σ.load G u v) + #(σ.load G v u) < K) :
    ∃ c, σ.Follows G c₀ c K := by
  -- the edges still to be coloured
  set R : Finset (Sym2 V) := {e | e ∈ G.edgeSet ∧ ¬ σ.pre e}
  -- invariant after colouring the edges of `T ⊆ R`
  let P : Finset (Sym2 V) → Prop := fun T =>
    ∃ c : Sym2 V → ℕ, (∀ e ∉ T, c e = c₀ e) ∧ (∀ e ∈ T, c e < K) ∧
      ∀ ⦃u v w⦄, G.Adj u v → G.Adj u w → w ≠ v → s(u, v) ∈ T →
        (σ.pre s(u, w) ∨ (s(u, w) ∈ T ∧ σ.time s(u, w) ≤ σ.time s(u, v))) →
        c s(u, w) ≠ c s(u, v)
  have hR : ∀ T ⊆ R, P T := by
    intro T
    induction T using Finset.induction_on_max_value σ.time with
    | empty => exact fun _ => ⟨c₀, fun _ _ => rfl, fun _ h => absurd h (notMem_empty _),
        fun _ _ _ _ _ _ h => absurd h (notMem_empty _)⟩
    | insert e T heT hmax ih =>
      intro hsub
      obtain ⟨c, hout, hlt, hprop⟩ := ih ((subset_insert _ _).trans hsub)
      have heR := hsub (mem_insert_self e T)
      induction e using Sym2.ind with
      | _ a b =>
      simp only [R, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet] at heR
      obtain ⟨hab, hpab⟩ := heR
      -- colours to avoid: at `a` and at `b`, edges that are pre-coloured or already coloured
      set Fa : Finset V := {w | G.Adj a w ∧ w ≠ b ∧ (σ.pre s(a, w) ∨ s(a, w) ∈ T)}
      set Fb : Finset V := {w | G.Adj b w ∧ w ≠ a ∧ (σ.pre s(b, w) ∨ s(b, w) ∈ T)}
      have hFa : Fa ⊆ σ.load G a b := by
        intro w hw
        simp only [Fa, mem_filter, mem_univ, true_and] at hw
        simp only [load, mem_filter, mem_univ, true_and]
        refine ⟨hw.1, hw.2.1, hw.2.2.imp_right fun h => hmax _ h⟩
      have hFb : Fb ⊆ σ.load G b a := by
        intro w hw
        simp only [Fb, mem_filter, mem_univ, true_and] at hw
        simp only [load, mem_filter, mem_univ, true_and]
        refine ⟨hw.1, hw.2.1, hw.2.2.imp_right fun h => ?_⟩
        have := hmax _ h
        rwa [Sym2.eq_swap (a := b) (b := a)]
      set A : Finset ℕ := Fa.image (fun w => c s(a, w)) ∪ Fb.image (fun w => c s(b, w))
      have hA : #A < #(range K) := by
        rw [card_range]
        calc #A ≤ #Fa + #Fb := (card_union_le _ _).trans
              (Nat.add_le_add card_image_le card_image_le)
          _ ≤ #(σ.load G a b) + #(σ.load G b a) :=
              Nat.add_le_add (card_le_card hFa) (card_le_card hFb)
          _ < K := hload hab hpab
      obtain ⟨α, hαK, hαA⟩ := exists_mem_notMem_of_card_lt_card hA
      rw [mem_range] at hαK
      refine ⟨Function.update c s(a, b) α, fun e he => ?_, fun e he => ?_, ?_⟩
      · rw [mem_insert, not_or] at he
        rw [Function.update_of_ne he.1]; exact hout e he.2
      · rcases mem_insert.1 he with rfl | he
        · simpa using hαK
        · have hne : e ≠ s(a, b) := fun h => heT (by rw [← h]; exact he)
          rw [Function.update_of_ne hne]; exact hlt e he
      · -- the invariant for `insert s(a,b) T`
        have hnot : ∀ ⦃u w : V⦄, G.Adj u w → s(u, w) = s(a, b) →
            ∀ ⦃x⦄, G.Adj u x → x ≠ w → (σ.pre s(u, x) ∨ s(u, x) ∈ T) → c s(u, x) ≠ α := by
          intro u w huw hue x hux hxw hx heq
          apply hαA
          rcases Sym2.eq_iff.1 hue with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact mem_union_left _ (mem_image.2 ⟨x, by
              simp only [Fa, mem_filter, mem_univ, true_and]; exact ⟨hux, hxw, hx⟩, heq⟩)
          · exact mem_union_right _ (mem_image.2 ⟨x, by
              simp only [Fb, mem_filter, mem_univ, true_and]; exact ⟨hux, hxw, hx⟩, heq⟩)
        intro u v w huv huw hwv hv hw
        by_cases hve : s(u, v) = s(a, b)
        · -- the new edge
          have hwe : s(u, w) ≠ s(a, b) := by
            rw [← hve]; intro h; exact hwv (Sym2.congr_right.1 h)
          rw [Function.update_of_ne hwe, hve, Function.update_self]
          refine hnot huv hve huw hwv ?_
          rcases hw with hw | ⟨hw, -⟩
          · exact Or.inl hw
          · exact Or.inr ((mem_insert.1 hw).resolve_left hwe)
        · have hvT : s(u, v) ∈ T := (mem_insert.1 hv).resolve_left hve
          rw [Function.update_of_ne hve]
          by_cases hwe : s(u, w) = s(a, b)
          · rw [hwe, Function.update_self]
            intro heq
            have hwe' : s(u, w) = s(a, b) := hwe
            refine hnot huw hwe' huv (Ne.symm hwv) (Or.inr hvT) heq.symm
          · rw [Function.update_of_ne hwe]
            refine hprop huv huw hwv hvT ?_
            rcases hw with hw | ⟨hw, ht⟩
            · exact Or.inl hw
            · exact Or.inr ⟨(mem_insert.1 hw).resolve_left hwe, ht⟩
  obtain ⟨c, hout, hlt, hprop⟩ := hR R subset_rfl
  have hmemR : ∀ ⦃u v⦄, G.Adj u v → ¬ σ.pre s(u, v) → s(u, v) ∈ R := fun u v huv hp => by
    simp only [R, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet]; exact ⟨huv, hp⟩
  refine ⟨c, fun u v huv hp => hout _ fun h => ?_, fun u v huv hp => ⟨hlt _ (hmemR huv hp),
    fun w huw hwv hw => hprop huv huw hwv (hmemR huv hp) ?_⟩⟩
  · simp only [R, mem_filter, mem_univ, true_and] at h; exact h.2 hp
  · by_cases hpw : σ.pre s(u, w)
    · exact Or.inl hpw
    · exact Or.inr ⟨hmemR huw hpw, hw.resolve_left hpw⟩

end EdgeSchedule

end Podc.DeltaEdgeColoring
