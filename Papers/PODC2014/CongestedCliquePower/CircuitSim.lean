import Papers.PODC2014.CongestedCliquePower.CircuitAssign
import Podc.Computability.Distributed.CongestedClique.Bandwidth

/-!
# Simulating circuits on the congested clique (Theorems 2 and 4 of [DKO14])

Model: `CLIQUE-UCAST_{n,B}`: `n = |V|` players, synchronous rounds, in every round every player
sends `B` bits to every player (a separate message per ordered pair); no failures, no randomness,
local computation is free. Programs are `Prog V Bool σ ρ` (`Phases.lean`) and their round count at
bandwidth `B` is `Prog.roundsAt B` (`Bandwidth.lean`). The input `x : X → Bool` is partitioned by
`part : X → V`: initially player `v` knows exactly the bits `x i` with `part i = v`
(`inputState`).

The protocol (proof of Theorem 2), given an assignment `I : C → V` of the gates to the players and
a set `H` of heavy gates:

* step 0: the owner of every input bit sends it to the owner of its input gate;
* stage `r = 0, …, D`: the owner of every non-input gate `G` of rank `r` computes its value:
  - if `G` is heavy, every player `u` sends to `I G` the `b` bits `g_u(values of the in-neighbours
    of G owned by u)` (separability for the partition of `in(G)` induced by `I`);
  - if `G` is light, the owner of every in-neighbour `G'` sends the value of `G'` to `I G`.

All patterns are fixed in advance, so each step is executed by oblivious routing
(`Prog.exists_slots`), in two rounds of bandwidth `b + 4s + 3`. The invariant `Inv r` says that
the owner of every input gate and of every gate of rank `< r` knows its value.
-/

namespace Podc.CongestedCliquePower

open Finset Cslib.CongestedClique

open Classical

noncomputable section

/-- The initial states: player `v` knows the input bits `x i` with `part i = v`. -/
def inputState {X V : Type} (part : X → V) (x : X → Bool) : V → X → Option Bool :=
  fun v i => if part i = v then some (x i) else none

/-- Iterating a family of programs: `stagesProg Q r = Q 0 ++ Q 1 ++ ⋯ ++ Q (r - 1)`. -/
def stagesProg {V W σ : Type} (Q : ℕ → Prog V W σ σ) : ℕ → Prog V W σ σ
  | 0 => .done σ
  | r + 1 => (stagesProg Q r).append (Q r)

lemma stagesProg_spec {V W σ : Type} [Fintype V] (Q : ℕ → Prog V W σ σ)
    (Inv : ℕ → (V → σ) → Prop) (B c : ℕ) (ok : W → Prop)
    (hinv : ∀ r st, Inv r st → Inv (r + 1) ((Q r).run st))
    (hrounds : ∀ r st, (Q r).roundsAt B st ≤ c) (hvalid : ∀ r st, (Q r).Valid ok st) :
    ∀ r st, Inv 0 st → Inv r ((stagesProg Q r).run st) ∧
      (stagesProg Q r).roundsAt B st ≤ c * r ∧ (stagesProg Q r).Valid ok st := by
  intro r st h0
  induction r with
  | zero => exact ⟨h0, by simp [stagesProg], trivial⟩
  | succ r ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simp only [stagesProg, Prog.run_append]; exact hinv _ _ h1
    · simp only [stagesProg, Prog.roundsAt_append]
      have := hrounds r ((stagesProg Q r).run st)
      rw [Nat.mul_succ]; omega
    · simp only [stagesProg, Prog.valid_append]; exact ⟨h3, hvalid _ _⟩

namespace Circuit

variable {X C V : Type} [Fintype C] [Fintype V] [DecidableEq V] (Γ : Circuit X C)

/-! ### The protocol -/

/-- Step 0, slots from `u` to `v`: the input gates owned by `v` whose input is owned by `u`. -/
def inSlots (I : C → V) (part : X → V) (u v : V) : Finset C :=
  {G | I G = v ∧ ∃ i, Γ.src G = some i ∧ part i = u}

/-- Step 0, the bit sent for the input gate `G`. -/
def inEnc (_ : V) (st : X → Option Bool) (G : C) : Bool :=
  ((Γ.src G).bind st).getD false

/-- Step 0, the new state: the values of the input gates. -/
def inRecv (part : X → V) (_ : V) (_ : X → Option Bool) (m : V → C → Bool) : C → Bool :=
  fun G => (Γ.src G).elim false fun i => m (part i) G

/-- Stage `r`, value slots from `u` to `v`: the gates `G'` owned by `u` with a wire to a light gate
of rank `r` owned by `v`. -/
def valSlots (H : C → Prop) (I : C → V) (r : ℕ) (u v : V) : Finset C :=
  {G' | I G' = u ∧ ∃ G, Γ.wire G' G ∧ ¬ H G ∧ I G = v ∧ Γ.rank G = r}

/-- Stage `r`, separability slots to `v`: `b` bits for every heavy gate of rank `r` owned by
`v`. -/
def partSlots (H : C → Prop) (I : C → V) (b r : ℕ) (v : V) : Finset (C × Fin b) :=
  (univ.filter fun G => H G ∧ I G = v ∧ Γ.rank G = r) ×ˢ (univ : Finset (Fin b))

/-- Stage `r`, all slots from `u` to `v`. -/
def slots (H : C → Prop) (I : C → V) (b r : ℕ) (u v : V) : Finset (C ⊕ C × Fin b) :=
  (Γ.valSlots H I r u v).disjSum (Γ.partSlots H I b r v)

/-- Stage `r`, the bit sent for a slot: the value of a gate, or the `k`-th bit of `g_u`. -/
def stEnc {b : ℕ} {I : C → V}
    (gs : (G : C) → (j : V) → ({i : {g // Γ.wire g G} // I i.1 = j} → Bool) → Fin b → Bool)
    (u : V) (st : C → Bool) : C ⊕ C × Fin b → Bool
  | .inl G' => st G'
  | .inr (G, k) => gs G u (fun i => st i.1.1) k

/-- Stage `r`, the new state: the owner of a non-input gate of rank `r` computes its value. -/
def stRecv {b : ℕ} (H : C → Prop) (I : C → V) (hs : C → (V → Fin b → Bool) → Bool) (r : ℕ)
    (v : V) (st : C → Bool) (m : V → C ⊕ C × Fin b → Bool) : C → Bool :=
  fun G => if I G = v ∧ Γ.src G = none ∧ Γ.rank G = r then
      (if H G then hs G (fun u k => m u (.inr (G, k))) else Γ.op G fun g => m (I g.1) (.inl g.1))
    else st G

/-- The invariant before stage `r`. -/
def Inv (I : C → V) (x : X → Bool) (r : ℕ) (st : V → C → Bool) : Prop :=
  ∀ G, ((Γ.src G).isSome ∨ Γ.rank G < r) → st (I G) G = Γ.eval x G

/-! ### Correctness -/

omit [Fintype V] in
lemma inv_zero (I : C → V) (part : X → V) (x : X → Bool) :
    Γ.Inv I x 0 fun v => Γ.inRecv part v (inputState part x v) fun u t =>
      if t ∈ Γ.inSlots I part u v then Γ.inEnc u (inputState part x u) t else false := by
  intro G hG
  have hs : (Γ.src G).isSome := by simpa using hG
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
  have hmem : G ∈ Γ.inSlots I part (part i) (I G) := by
    simp [inSlots, hi]
  simp only [inRecv, hi, Option.elim, hmem, ↓reduceIte, inEnc, Option.bind_some, inputState,
    Γ.eval_of_src_some hi]
  simp

omit [Fintype V] in
lemma inv_succ {b : ℕ} (H : C → Prop) (I : C → V)
    (gs : (G : C) → (j : V) → ({i : {g // Γ.wire g G} // I i.1 = j} → Bool) → Fin b → Bool)
    (hs : C → (V → Fin b → Bool) → Bool)
    (hgs : ∀ G, Γ.src G = none → ∀ y, Γ.op G y = hs G fun j => gs G j fun i => y i.1)
    (x : X → Bool) (r : ℕ) (st : V → C → Bool) (hinv : Γ.Inv I x r st) :
    Γ.Inv I x (r + 1) fun v => Γ.stRecv H I hs r v (st v) fun u t =>
      if t ∈ Γ.slots H I b r u v then Γ.stEnc gs u (st u) t else false := by
  intro G hG
  simp only [stRecv, true_and]
  split_ifs with hc hH
  · rw [Γ.eval_of_src_none hc.1]
    · rw [hgs G hc.1]
      congr 1
      funext u k
      have hmem : (Sum.inr (G, k) : C ⊕ C × Fin b) ∈ Γ.slots H I b r u (I G) := by
        simp [slots, partSlots, hH, hc.2]
      simp only [hmem, ↓reduceIte, stEnc]
      congr 2
      funext i
      obtain ⟨⟨g, hw⟩, hi⟩ := i
      subst hi
      exact hinv g (Or.inr (hc.2 ▸ Γ.rank_lt _ _ hw))
  · rw [Γ.eval_of_src_none hc.1]
    · congr 1
      funext g
      have hmem : (Sum.inl g.1 : C ⊕ C × Fin b) ∈ Γ.slots H I b r (I g.1) (I G) := by
        simp only [slots, valSlots, Finset.inl_mem_disjSum, mem_filter, mem_univ, true_and]
        exact ⟨G, g.2, hH, rfl, hc.2⟩
      simp only [hmem, ↓reduceIte, stEnc]
      exact hinv g.1 (Or.inr (hc.2 ▸ Γ.rank_lt _ _ g.2))
  · apply hinv
    rcases hG with hG | hG
    · exact Or.inl hG
    · by_cases hr : Γ.rank G = r
      · left
        rw [Option.isSome_iff_ne_none]
        exact fun h => hc ⟨h, hr⟩
      · right; omega

/-! ### Load bounds -/

section Bounds

variable {H : C → Prop} {I : C → V} {L : ℕ}

omit [Fintype V] in
lemma card_heavy_le_one (hH : ∀ G G', H G → H G' → I G = I G' → G = G') (v : V) :
    #{G | H G ∧ I G = v} ≤ 1 :=
  Finset.card_le_one.mpr fun a ha a' ha' => by
    simp only [mem_filter, mem_univ, true_and] at ha ha'
    exact hH _ _ ha.1 ha'.1 (ha.2.trans ha'.2.symm)

omit [Fintype V] in
lemma sum_light_le (hL : ∀ v, ∑ G ∈ {G | ¬ H G ∧ I G = v}, Γ.weight G ≤ L) (v : V)
    (c : C → ℕ) (hc : ∀ G, c G ≤ Γ.weight G) : ∑ G ∈ {G | ¬ H G ∧ I G = v}, c G ≤ L :=
  le_trans (Finset.sum_le_sum fun G _ => hc G) (hL v)

lemma inSlots_row [Fintype X] (part : X → V) (u : V) :
    ∑ v, #(Γ.inSlots I part u v) ≤ Fintype.card {i // part i = u} := by
  calc ∑ v, #(Γ.inSlots I part u v)
      ≤ ∑ G ∈ {G | ∃ i, Γ.src G = some i ∧ part i = u}, 1 := by
        refine sum_card_le_sum _ _ _ (fun v G hG => ?_) (fun G _ => ?_)
        · simp only [inSlots, mem_filter, mem_univ, true_and] at hG ⊢; exact hG.2
        · refine Finset.card_le_one.mpr fun v hv v' hv' => ?_
          simp only [inSlots, mem_filter, mem_univ, true_and] at hv hv'
          rw [← hv.1, ← hv'.1]
    _ = #{G | ∃ i, Γ.src G = some i ∧ part i = u} := by simp
    _ ≤ _ := by
      rw [← Fintype.card_subtype]
      refine Fintype.card_le_of_injective
        (fun G : {G // ∃ i, Γ.src G = some i ∧ part i = u} =>
          (⟨G.2.choose, G.2.choose_spec.2⟩ : {i // part i = u}))
        fun G G' h => Subtype.ext ?_
      have h' : G.2.choose = G'.2.choose := congrArg Subtype.val h
      exact Γ.src_inj _ _ _ G.2.choose_spec.1 (h' ▸ G'.2.choose_spec.1)

lemma inSlots_col (hH : ∀ G G', H G → H G' → I G = I G' → G = G')
    (hL : ∀ v, ∑ G ∈ {G | ¬ H G ∧ I G = v}, Γ.weight G ≤ L) (part : X → V) (v : V) :
    ∑ u, #(Γ.inSlots I part u v) ≤ 1 + L := by
  calc ∑ u, #(Γ.inSlots I part u v)
      ≤ ∑ G ∈ {G | I G = v ∧ (Γ.src G).isSome}, 1 := by
        refine sum_card_le_sum _ _ _ (fun u G hG => ?_) (fun G _ => ?_)
        · simp only [inSlots, mem_filter, mem_univ, true_and] at hG ⊢
          obtain ⟨h1, i, h2, -⟩ := hG
          exact ⟨h1, by simp [h2]⟩
        · refine Finset.card_le_one.mpr fun u hu u' hu' => ?_
          simp only [inSlots, mem_filter, mem_univ, true_and] at hu hu'
          obtain ⟨-, i, hi, rfl⟩ := hu
          obtain ⟨-, i', hi', rfl⟩ := hu'
          rw [hi] at hi'
          cases hi'
          rfl
    _ = #{G | I G = v ∧ (Γ.src G).isSome} := by simp
    _ ≤ #{G | H G ∧ I G = v} + #{G ∈ {G | ¬ H G ∧ I G = v} | (Γ.src G).isSome} := by
        refine le_trans (Finset.card_le_card fun G hG => ?_) (Finset.card_union_le _ _)
        simp only [mem_filter, mem_univ, true_and, mem_union] at hG ⊢
        by_cases h : H G
        · exact Or.inl ⟨h, hG.1⟩
        · exact Or.inr ⟨⟨h, hG.1⟩, hG.2⟩
    _ ≤ 1 + L := by
        have h1 := card_heavy_le_one hH v
        have h2 : #{G ∈ {G | ¬ H G ∧ I G = v} | (Γ.src G).isSome} ≤ L := by
          rw [Finset.card_filter]
          exact Γ.sum_light_le hL v _ fun G => by unfold weight; split_ifs <;> omega
        omega

omit [Fintype V] in
lemma partSlots_card (hH : ∀ G G', H G → H G' → I G = I G' → G = G') (b r : ℕ) (v : V) :
    #(Γ.partSlots H I b r v) ≤ b := by
  rw [partSlots, Finset.card_product, card_univ, Fintype.card_fin]
  have : #{G | H G ∧ I G = v ∧ Γ.rank G = r} ≤ 1 :=
    le_trans (Finset.card_le_card fun G hG => by
      simp only [mem_filter, mem_univ, true_and] at hG ⊢; exact ⟨hG.1, hG.2.1⟩)
      (card_heavy_le_one hH v)
  calc _ ≤ 1 * b := Nat.mul_le_mul_right _ this
    _ = b := one_mul b

lemma slots_row (hH : ∀ G G', H G → H G' → I G = I G' → G = G')
    (hL : ∀ v, ∑ G ∈ {G | ¬ H G ∧ I G = v}, Γ.weight G ≤ L) (b r : ℕ) (u : V) :
    ∑ v, #(Γ.slots H I b r u v) ≤ Fintype.card V * b + Fintype.card V + L := by
  simp only [slots, Finset.card_disjSum, Finset.sum_add_distrib]
  have hp : ∑ v, #(Γ.partSlots H I b r v) ≤ Fintype.card V * b := by
    calc _ ≤ ∑ _v : V, b := Finset.sum_le_sum fun v _ => Γ.partSlots_card hH b r v
      _ = _ := by simp
  -- value slots: heavy senders and light senders
  set T : V → Finset C := fun v => {G' | (¬ H G' ∧ I G' = u) ∧ ∃ G, Γ.wire G' G ∧ I G = v}
  have hval : ∀ v, #(Γ.valSlots H I r u v) ≤ 1 + #(T v) := fun v => by
    refine le_trans (Finset.card_le_card fun G' hG' => ?_)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (card_heavy_le_one hH u) _))
    simp only [valSlots, T, mem_filter, mem_univ, true_and, mem_union] at hG' ⊢
    obtain ⟨h1, G, h2, -, h3, -⟩ := hG'
    by_cases h : H G'
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨⟨h, h1⟩, G, h2, h3⟩
  have hT : ∑ v, #(T v) ≤ L := by
    refine le_trans (sum_card_le_sum T {G' | ¬ H G' ∧ I G' = u} Γ.outdeg
      (fun v G' hG' => ?_) (fun G' _ => ?_)) (Γ.sum_light_le hL u _ fun G => ?_)
    · simp only [T, mem_filter, mem_univ, true_and] at hG' ⊢; exact hG'.1
    · refine le_trans (Finset.card_le_card (t := Finset.image I {h | Γ.wire G' h})
        fun v hv => ?_) Finset.card_image_le
      simp only [T, mem_filter, mem_univ, true_and] at hv
      obtain ⟨-, G, h1, h2⟩ := hv
      exact Finset.mem_image.mpr ⟨G, by simpa using h1, h2⟩
    · unfold weight; omega
  have : ∑ v, #(Γ.valSlots H I r u v) ≤ Fintype.card V + L := by
    calc _ ≤ ∑ v, (1 + #(T v)) := Finset.sum_le_sum fun v _ => hval v
      _ = Fintype.card V + ∑ v, #(T v) := by simp [Finset.sum_add_distrib]
      _ ≤ _ := by omega
  omega

lemma slots_col (hH : ∀ G G', H G → H G' → I G = I G' → G = G')
    (hL : ∀ v, ∑ G ∈ {G | ¬ H G ∧ I G = v}, Γ.weight G ≤ L) (b r : ℕ) (v : V) :
    ∑ u, #(Γ.slots H I b r u v) ≤ Fintype.card V * b + L := by
  simp only [slots, Finset.card_disjSum, Finset.sum_add_distrib]
  have hp : ∑ _u : V, #(Γ.partSlots H I b r v) ≤ Fintype.card V * b := by
    calc _ ≤ ∑ _u : V, b := Finset.sum_le_sum fun _ _ => Γ.partSlots_card hH b r v
      _ = _ := by simp
  have hval : ∑ u, #(Γ.valSlots H I r u v) ≤ L := by
    calc ∑ u, #(Γ.valSlots H I r u v)
        ≤ ∑ G' ∈ {G' | ∃ G, Γ.wire G' G ∧ ¬ H G ∧ I G = v ∧ Γ.rank G = r}, 1 := by
          refine sum_card_le_sum _ _ _ (fun u G hG => ?_) (fun G _ => ?_)
          · simp only [valSlots, mem_filter, mem_univ, true_and] at hG ⊢; exact hG.2
          · refine Finset.card_le_one.mpr fun u hu u' hu' => ?_
            simp only [valSlots, mem_filter, mem_univ, true_and] at hu hu'
            rw [← hu.1, ← hu'.1]
      _ = #{G' | ∃ G, Γ.wire G' G ∧ ¬ H G ∧ I G = v ∧ Γ.rank G = r} := by simp
      _ ≤ #(({G | ¬ H G ∧ I G = v} : Finset C).biUnion fun G => {g | Γ.wire g G}) := by
          refine Finset.card_le_card fun G' hG' => ?_
          simp only [mem_filter, mem_univ, true_and, mem_biUnion] at hG' ⊢
          obtain ⟨G, h1, h2, h3, -⟩ := hG'
          exact ⟨G, ⟨h2, h3⟩, h1⟩
      _ ≤ ∑ G ∈ {G | ¬ H G ∧ I G = v}, Γ.indeg G := Finset.card_biUnion_le
      _ ≤ L := Γ.sum_light_le hL v _ fun G => by unfold weight; omega
  omega

end Bounds

end Circuit

/-! ### Theorems 2 and 4 -/

/-- `f` can be computed in `CLIQUE-UCAST_{n,B}` in `R` rounds under the input partition `part`:
some protocol leaves the value `f x` at some player `p₀`, for every input `x`. -/
def UcastComputable {V X : Type} [Fintype V] [DecidableEq V] (part : X → V)
    (f : (X → Bool) → Bool) (B R : ℕ) : Prop :=
  ∃ (P : Prog V Bool (X → Option Bool) Bool) (p₀ : V), ∀ x : X → Bool,
    P.run (inputState part x) p₀ = f x ∧ P.roundsAt B (inputState part x) ≤ R ∧
      P.Valid (fun _ => True) (inputState part x)

/-- **Theorem 2 of [DKO14]** (with explicit constants). Let `f : {0,1}^X → {0,1}`, `|X| ≤ n²`, be
computed by a circuit of depth at most `D` with at most `n² s` wires whose non-input gates are
`b`-separable. Then for every input partition giving every player at most `n (b + s)` input bits,
`f` can be computed in `CLIQUE-UCAST_{n, b + 4s + 3}` in `2D + 4` rounds. -/
theorem theorem_2 {V X C : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype X] [Fintype C]
    (Γ : Circuit X C) (out : C) (f : (X → Bool) → Bool) (hf : Γ.Computes out f) (b s D : ℕ)
    (hX : Fintype.card X ≤ Fintype.card V ^ 2)
    (hsep : ∀ G, Γ.src G = none → Separable b (Γ.op G))
    (hN : Γ.numWires ≤ Fintype.card V ^ 2 * s) (hD : Γ.DepthLE D)
    (part : X → V) (hpart : ∀ v, Fintype.card {i // part i = v} ≤ Fintype.card V * (b + s)) :
    UcastComputable part f (b + 4 * s + 3) (2 * D + 4) := by
  set n := Fintype.card V with hn_def
  have hn : 0 < n := Fintype.card_pos
  set M := n * (2 * s + 1) with hM
  set K := b + 4 * s + 3 with hK
  have hKpos : 0 < K := by omega
  have hKK : (K + K - 1) / K = 1 := Prog.ceilDiv_self hKpos
  have hnK : n * K = n * b + n + 2 * M := by rw [hK, hM]; ring
  obtain ⟨I, hI1, hI2⟩ := Γ.exists_assignment s hX hN
  -- the separability data, for the partition of `in(G)` induced by `I`
  have hsep' : ∀ G, ∃ (g : (j : V) → ({i : {g // Γ.wire g G} // I i.1 = j} → Bool) → Fin b → Bool)
      (h : (V → Fin b → Bool) → Bool),
      Γ.src G = none → ∀ y, Γ.op G y = h fun j => g j fun i => y i.1 := by
    intro G
    by_cases hG : Γ.src G = none
    · obtain ⟨g, h, hgh⟩ := hsep G hG V (fun i => I i.1)
      exact ⟨g, h, fun _ => hgh⟩
    · exact ⟨fun _ _ _ => false, fun _ => false, fun h => absurd h hG⟩
  choose gs hs hgs using hsep'
  -- step 0: the input bits
  obtain ⟨Q0, hQ0⟩ := Prog.exists_slots (W := Bool) (Γ.inSlots I part) K K
    (fun u => le_trans (Γ.inSlots_row part u) (by rw [hnK]; have := hpart u; nlinarith))
    (fun v => le_trans (Γ.inSlots_col hI1 hI2 part v) (by rw [hnK]; nlinarith))
    Γ.inEnc (Γ.inRecv part)
  -- stage `r`
  have hstage := fun r => Prog.exists_slots (W := Bool) (Γ.slots (Γ.Heavy M) I b r) K K
    (fun u => le_trans (Γ.slots_row hI1 hI2 b r u) hnK.ge)
    (fun v => le_trans (Γ.slots_col hI1 hI2 b r v) (by rw [hnK]; nlinarith))
    (Γ.stEnc gs) (Γ.stRecv (Γ.Heavy M) I hs r)
  choose Qs hQs using hstage
  refine ⟨Q0.append ((stagesProg Qs (D + 1)).append (Prog.compute fun _ st => st out)), I out,
    fun x => ?_⟩
  obtain ⟨h0run, h0rounds, h0valid⟩ := hQ0 (inputState part x)
  obtain ⟨hinv, hrounds, hvalid⟩ := stagesProg_spec Qs (Γ.Inv I x) K 2 (fun _ => True)
    (fun r st h => by rw [(hQs r st).1]; exact Γ.inv_succ _ I gs hs hgs x r st h)
    (fun r st => by have := (hQs r st).2.1; rw [hKK] at this; omega)
    (fun r st => (hQs r st).2.2 _ fun _ _ _ _ => trivial) (D + 1)
    (Q0.run (inputState part x)) (by rw [h0run]; exact Γ.inv_zero I part x)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prog.run_append, Prog.run_compute]
    rw [hinv out (Or.inr (Nat.lt_succ_of_le (hD out))), hf x]
  · simp only [Prog.roundsAt_append, Prog.roundsAt_compute]
    rw [hKK] at h0rounds
    omega
  · simp only [Prog.valid_append, Prog.valid_compute, and_true]
    exact ⟨h0valid _ fun _ _ _ _ => trivial, hvalid⟩

/-- **Theorem 4 of [DKO14]** (contrapositive of Theorem 2, explicit constants). If `f` cannot be
computed in `CLIQUE-UCAST_{n, b + 4s + 3}` in `R` rounds under a balanced input partition, then
`f` is not computed by any circuit of depth `D` with `2D + 4 ≤ R`, at most `n² s` wires and
`b`-separable non-input gates. -/
theorem theorem_4 {V X : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype X]
    (f : (X → Bool) → Bool) (b s R : ℕ) (hX : Fintype.card X ≤ Fintype.card V ^ 2)
    (part : X → V) (hpart : ∀ v, Fintype.card {i // part i = v} ≤ Fintype.card V * (b + s))
    (hR : ¬ UcastComputable part f (b + 4 * s + 3) R)
    {C : Type} [Fintype C] (Γ : Circuit X C) (out : C) (D : ℕ) (hDR : 2 * D + 4 ≤ R)
    (hsep : ∀ G, Γ.src G = none → Separable b (Γ.op G))
    (hN : Γ.numWires ≤ Fintype.card V ^ 2 * s) (hD : Γ.DepthLE D) :
    ¬ Γ.Computes out f := by
  intro hf
  obtain ⟨P, p₀, hP⟩ := theorem_2 Γ out f hf b s D hX hsep hN hD part hpart
  exact hR ⟨P, p₀, fun x => ⟨(hP x).1, le_trans (hP x).2.1 hDR, (hP x).2.2⟩⟩

/-- Non-vacuity of Theorem 2: the circuit `x₀ ∧ x₁` (`andCircuit`) with two players, each holding
one input bit (`b = 1`, `s = 1`, `D = 1`), gives a protocol with bandwidth `8` and `6` rounds. -/
theorem andCircuit_ucast :
    UcastComputable (id : Fin 2 → Fin 2) (fun x => x 0 && x 1) (1 + 4 * 1 + 3) (2 * 1 + 4) := by
  refine theorem_2 andCircuit 2 _ andCircuit_eval 1 1 1 (by simp) (fun G _ => ?_)
    (by rw [andCircuit_numWires]; simp) (fun g => ?_) id (fun v => ?_)
  · convert separable_and (ι := {g // andCircuit.wire g G}) using 2
    exact decide_eq_decide.mpr Iff.rfl
  · simp only [andCircuit]; split_ifs <;> omega
  · simp

end

end Podc.CongestedCliquePower
