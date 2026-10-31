/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Papers.PODC2021.HTLCBrokeringHardness.Flower

/-!
# Lemma 4.3 and the backward direction of Lemma 4.4

For the flower graph `F = flower K m c` (any `m`, any `c` below every weight):

* `broker_mem`: in an adequate leader set either `b` is a leader or `s, y₁, z₁` all are;
* `not_adequate_of_supplier_not_mem`: a leader set containing at most one party `p` besides `b`
  and not containing the supplier `s` is inadequate (needs `V ≥ 2` and every `vᵢ < V`);
* `lemma_4_3`: every adequate leader set has size `≥ 2`, and an adequate one of size `2` is `{b, s}`;
* `satisfiable_of_adequate`: if `{b, s}` (or a subset) is adequate then `K` is satisfiable
  (backward direction of Lemma 4.4; needs `m ≥ 1`).

All proofs use the *first hit* argument: look at the reachable state just before the first creation of
a contract of a well-chosen set `T`; the follower rule and the broker's balances in that state give a
contradiction (or the knapsack solution).
-/

namespace Podc.HTLCBrokeringHardness

open Finset Flower

namespace Flower

variable {n m c : ℕ} {K : Knapsack n}

@[simp] lemma own_b (a : Asset) : flowerOwn K m c .b a = 0 := by
  simp [flowerOwn, TxGraph.brokerOwn]

end Flower

namespace TxGraph

open Flower

variable {n m c : ℕ} {K : Knapsack n}

/-- The broker never escrows more than it received. -/
lemma Reachable.balance_b {L : Finset (Party n m)} {S : Finset (Edge n m)}
    (hS : (flower K m c).Reachable (flowerOwn K m c) L S) (a : Asset) :
    (flower K m c).outflow S .b a ≤ (flower K m c).inflow S .b a := by
  simpa using hS.balance .b a

/-- Follower rule in a reachable state: a created contract `e` whose sender is not a leader implies
that each contract `e'` into its sender is created. -/
lemma Reachable.follower {L : Finset (Party n m)} {S : Finset (Edge n m)}
    (hS : (flower K m c).Reachable (flowerOwn K m c) L S) {e e' : Edge n m} (he : e ∈ S)
    (hd : (flower K m c).dst e' = (flower K m c).src e) : (flower K m c).src e ∈ L ∨ e' ∈ S :=
  (hS.closed he).imp id fun h => h e' hd

end TxGraph

open Flower

variable {n m c : ℕ} {K : Knapsack n}

/-- Lemma 4.3, first step: if `b` is not a leader then `s`, `y₁` and `z₁` are leaders. -/
theorem broker_mem {L : Finset (Party n m)} (hA : (flower K m c).Adequate (flowerOwn K m c) L)
    (hb : Party.b ∉ L) : Party.s ∈ L ∧ Party.y 0 ∈ L ∧ Party.z 0 ∈ L := by
  obtain ⟨S, hS, hdis, e, heT, -, hal, -⟩ :=
    hA.first_hit (T := univ.filter fun e => (flower K m c).src e = .b) ⟨.toS, by simp [flower]⟩
  simp only [mem_filter, mem_univ, true_and] at heT
  rw [heT] at hal
  have hin := hal.resolve_left hb
  have hnot : ∀ e', (flower K m c).src e' = .b → e' ∉ S := fun e' h h' =>
    disjoint_left.1 hdis h' (by simp [h])
  refine ⟨?_, ?_, ?_⟩
  · exact (hS.follower (hin .fromS rfl) (e' := .toS) rfl).resolve_right (hnot _ rfl)
  · exact (hS.follower (hin (.fromY 0) rfl) (e' := .toY 0) rfl).resolve_right (hnot _ rfl)
  · exact (hS.follower (hin (.fromZ 0) rfl) (e' := .toZ 0) rfl).resolve_right (hnot _ rfl)

/-- `p` sits at a level `≤ k` of the chain, or is an item. -/
def LowParty (p : Party n m) (k : ℕ) : Prop :=
  (∃ i, p = .x i) ∨ ∃ j : Fin (m + 1), (j : ℕ) ≤ k ∧ (p = .y j ∨ p = .z j)

/-- Lemma 4.3, main step: if the supplier `s` is not a leader and the only leader besides `b` is
`p`, then the leader set is inadequate. (Requires `V ≥ 2`, `vᵢ < V` and `c < wᵢ` for all items.) -/
theorem not_adequate_of_supplier_not_mem (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hc : ∀ i, c < K.w i)
    {L : Finset (Party n m)} (p : Party n m) (hLs : Party.s ∉ L) (hL : ∀ q ∈ L, q = .b ∨ q = p) :
    ¬ (flower K m c).Adequate (flowerOwn K m c) L := by
  intro hA
  obtain ⟨S, hS, hdis, e, heT, hen⟩ := hA.first_hit
    (T := univ.filter fun e => e = .toS ∨ ∃ k : Fin (m + 1), (k : ℕ) ≠ 0 ∧ e = .toY k) ⟨.toS, by simp⟩
  have htoS : Edge.toS ∉ S := fun h => disjoint_left.1 hdis h (by simp)
  have htoY : ∀ k : Fin (m + 1), (k : ℕ) ≠ 0 → Edge.toY k ∉ S := fun k hk h =>
    disjoint_left.1 hdis h (by simp only [mem_filter, mem_univ, true_and]; exact Or.inr ⟨k, hk, rfl⟩)
  have hleader : ∀ q, q ∈ L → q ≠ .b → q = p := fun q hq hqb => (hL q hq).resolve_left hqb
  -- non-leaders among the chain parties above level 0 are never activated
  have hfromY : ∀ k : Fin (m + 1), (k : ℕ) ≠ 0 → Edge.fromY k ∈ S → p = .y k := fun k hk h =>
    ((hleader _ ((hS.follower h (e' := .toY k) rfl).resolve_right (htoY k hk)) (by simp [flower])).symm)
  have hfromYB : ∀ j, Edge.fromYB j ∈ S → p = .y (ybLevel j) := fun j h =>
    ((hleader _ ((hS.follower h (e' := .toY (ybLevel j)) rfl).resolve_right
      (htoY _ (by simp [ybLevel]))) (by simp [flower])).symm)
  -- the supplier never gives its bitcoins
  have hfromS : Edge.fromS ∉ S := fun h =>
    hLs ((hS.follower h (e' := .toS) rfl).resolve_right htoS)
  -- the broker has at most `c` bitcoins, so it never funds an item
  have hinB : (flower K m c).inflow S .b .B ≤ c := by
    rw [inflow_B, ite_eq_right hfromS, zero_add]
    calc ∑ j, (if Edge.fromYB j ∈ S then c else 0)
        ≤ ∑ j, (if p = .y (ybLevel j) then c else 0) :=
          sum_le_sum fun j _ => by
            by_cases h : Edge.fromYB j ∈ S
            · simp [h, hfromYB j h]
            · simp [h]
      _ = (univ.filter fun j => p = .y (ybLevel j)).card * c := by
          rw [← sum_filter, sum_const, smul_eq_mul]
      _ ≤ 1 * c := by
          gcongr
          refine card_le_one.2 fun a ha b hb => ?_
          simp only [mem_filter, mem_univ, true_and] at ha hb
          have := ha.symm.trans hb
          simp only [Party.y.injEq, ybLevel, Fin.mk.injEq] at this
          exact Fin.ext (by omega)
      _ = c := one_mul c
  have htoX : ∀ i, Edge.toX i ∉ S := by
    intro i h
    have h1 := (hS.balance_b .B)
    rw [outflow_B] at h1
    have h2 : K.w i ≤ ∑ i, (if Edge.toX i ∈ S then K.w i else 0) :=
      le_trans (by simp [h]) (single_le_sum (f := fun i => if Edge.toX i ∈ S then K.w i else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ i))
    have := hc i; omega
  have hfromX : ∀ i, Edge.fromX i ∈ S → p = .x i := fun i h =>
    ((hleader _ ((hS.follower h (e' := .toX i) rfl).resolve_right (htoX i)) (by simp [flower])).symm)
  -- the broker's coins `E`: at most `V - 1`, none unless `p` is an item
  have hinE : (flower K m c).inflow S .b .E ≤ K.V - 1 ∧
      ((∀ i, p ≠ .x i) → (flower K m c).inflow S .b .E = 0) := by
    rw [inflow_E]
    refine ⟨?_, fun hp => sum_eq_zero fun i _ => by
      by_cases h : Edge.fromX i ∈ S
      · exact absurd (hfromX i h) (hp i)
      · simp [h]⟩
    by_cases hp : ∃ i, p = .x i
    · obtain ⟨i₀, rfl⟩ := hp
      calc ∑ i, (if Edge.fromX i ∈ S then K.v i else 0)
          ≤ ∑ i, (if i = i₀ then K.v i else 0) := sum_le_sum fun i _ => by
              by_cases h : Edge.fromX i ∈ S
              · have := hfromX i h; simp only [Party.x.injEq] at this; simp [h, this]
              · simp [h]
        _ = K.v i₀ := by simp
        _ ≤ K.V - 1 := by have := hv i₀; omega
    · push Not at hp
      rw [sum_eq_zero fun i _ => by
        by_cases h : Edge.fromX i ∈ S
        · exact absurd (hfromX i h) (hp i)
        · simp [h]]
      exact Nat.zero_le _
  have hbalE := hS.balance_b .E
  rw [outflow_E] at hbalE
  -- level by level: at most one of `y_{k+1}, z_{k+1}` is active, none above `p`'s level
  have key : ∀ k (hk : k ≤ m),
      ¬ (Edge.fromY ⟨k, by omega⟩ ∈ S ∧ Edge.fromZ ⟨k, by omega⟩ ∈ S) ∧
      (¬ LowParty p k → Edge.fromY ⟨k, by omega⟩ ∉ S ∧ Edge.fromZ ⟨k, by omega⟩ ∉ S) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hy0 : Edge.fromY ⟨0, by omega⟩ ∈ S → Party.y ⟨0, by omega⟩ ∈ L ∨ Edge.toY 0 ∈ S :=
        fun hh => hS.follower hh (e' := .toY 0) rfl
      have hz0 : Edge.fromZ ⟨0, by omega⟩ ∈ S → Party.z ⟨0, by omega⟩ ∈ L ∨ Edge.toZ 0 ∈ S :=
        fun hh => hS.follower hh (e' := .toZ 0) rfl
      constructor
      · rintro ⟨hy, hz⟩
        rcases hy0 hy with hy | hy <;> rcases hz0 hz with hz | hz
        · have h1 := hleader _ hy (by simp); have h2 := hleader _ hz (by simp)
          rw [← h1] at h2; simp at h2
        · have h1 := hleader _ hy (by simp)
          have := hinE.2 (by rw [← h1]; simp); simp [hz] at hbalE; omega
        · have h1 := hleader _ hz (by simp)
          have := hinE.2 (by rw [← h1]; simp); simp [hy] at hbalE; omega
        · have := hinE.1; simp [hy, hz] at hbalE; omega
      · intro hlow
        have hnotx : ∀ i, p ≠ .x i := fun i h => hlow (Or.inl ⟨i, h⟩)
        have hny : p ≠ .y 0 := fun h => hlow (Or.inr ⟨0, by simp, Or.inl h⟩)
        have hnz : p ≠ .z 0 := fun h => hlow (Or.inr ⟨0, by simp, Or.inr h⟩)
        have hE0 := hinE.2 hnotx
        constructor
        · intro hy
          rcases hy0 hy with hy | hy
          · exact hny (hleader _ hy (by simp)).symm
          · simp [hy] at hbalE; omega
        · intro hz
          rcases hz0 hz with hz | hz
          · exact hnz (hleader _ hz (by simp)).symm
          · simp [hz] at hbalE; omega
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      set kk : Fin (m + 1) := ⟨k, by omega⟩
      set k1 : Fin (m + 1) := ⟨k + 1, by omega⟩
      have hy : Edge.fromY k1 ∈ S → p = .y k1 := hfromY k1 (by simp [k1])
      -- funding `z_{k+2}` needs a coin `C_{k+1}`, i.e. an active party at level `k`
      have hz : Edge.fromZ k1 ∈ S → p = .z k1 ∨ (Edge.fromY kk ∈ S ∨ Edge.fromZ kk ∈ S) := by
        intro h
        rcases hS.follower h (e' := .toZ k1) rfl with h | h
        · exact Or.inl (hleader _ h (by simp [flower])).symm
        · right
          have hb := hS.balance_b (.C (k + 1))
          rw [show (k + 1 : ℕ) = (k1 : ℕ) from rfl, outflow_C _ _ _ S k1 (by simp [k1])] at hb
          rw [show ((k1 : ℕ)) = (kk : ℕ) + 1 from rfl, inflow_C _ _ _ S kk (by simp [kk]; omega)] at hb
          by_contra hc'
          push Not at hc'
          simp [h, hc'.1, hc'.2] at hb
      have hlow_y : ¬ LowParty (Party.y k1 : Party n m) k := by
        rintro (⟨i, hi⟩ | ⟨j, hj, hj' | hj'⟩)
        · cases hi
        · have h' : (k1 : ℕ) ≤ k := (Party.y.inj hj') ▸ hj
          simp [k1] at h'
        · cases hj'
      constructor
      · rintro ⟨h1, h2⟩
        have hp := hy h1
        rcases hz h2 with h | h
        · rw [hp] at h; simp at h
        · have := ih2 (by rw [hp]; exact hlow_y)
          rcases h with h | h
          · exact this.1 h
          · exact this.2 h
      · intro hlow
        have hlowk : ¬ LowParty p k := fun h => hlow (by
          rcases h with h | ⟨j, hj, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, by omega, h⟩)
        constructor
        · intro h1; exact hlow (Or.inr ⟨k1, le_rfl, Or.inl (hy h1)⟩)
        · intro h2
          rcases hz h2 with h | h
          · exact hlow (Or.inr ⟨k1, le_rfl, Or.inr h⟩)
          · have := ih2 hlowk
            rcases h with h | h
            · exact this.1 h
            · exact this.2 h
  -- the first contract of `T` cannot be created
  simp only [mem_filter, mem_univ, true_and] at heT
  obtain ⟨-, -, hpay⟩ := hen
  rcases heT with rfl | ⟨k, hk, rfl⟩
  · have h := (key m le_rfl).1
    change (flower K m c).outflow S .b .D + 2 ≤ flowerOwn K m c .b .D + (flower K m c).inflow S .b .D
      at hpay
    rw [own_b, zero_add, inflow_D] at hpay
    have h' : ¬ (Edge.fromY (Fin.last m) ∈ S ∧ Edge.fromZ (Fin.last m) ∈ S) := h
    by_cases h1 : Edge.fromY (Fin.last m) ∈ S <;> by_cases h2 : Edge.fromZ (Fin.last m) ∈ S <;>
      simp_all
  · obtain ⟨k', hk'⟩ : ∃ k', (k : ℕ) = k' + 1 := ⟨k - 1, by omega⟩
    have h := (key k' (by omega)).1
    change (flower K m c).outflow S .b (inAsset k) + (if (k : ℕ) = 0 then K.V - 1 else 3) ≤
      flowerOwn K m c .b (inAsset k) + (flower K m c).inflow S .b (inAsset k) at hpay
    rw [ite_eq_right hk] at hpay
    have hasset : inAsset k = .C (((⟨k', by omega⟩ : Fin (m + 1)) : ℕ) + 1) := by
      simp [inAsset, hk']
    rw [own_b, zero_add, hasset, inflow_C _ _ _ S ⟨k', by omega⟩ (by simp; omega)] at hpay
    by_cases h1 : Edge.fromY ⟨k', by omega⟩ ∈ S <;> by_cases h2 : Edge.fromZ ⟨k', by omega⟩ ∈ S <;>
      simp_all

/-- **Lemma 4.3** of [Chan–Lesani]: an adequate leader set for `F` has size at least two, and an
adequate leader set of size two is `{s, b}`. (Under the paper's standing assumption that no single
item has value `≥ V`, plus `V ≥ 2` and `c < wᵢ` for all items; the paper takes `c = min_w(X) − 1`.) -/
theorem lemma_4_3 (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hc : ∀ i, c < K.w i)
    {L : Finset (Party n m)} (hA : (flower K m c).Adequate (flowerOwn K m c) L) :
    2 ≤ L.card ∧ (L.card = 2 → L = {.b, .s}) := by
  by_cases hb : Party.b ∈ L
  swap
  · obtain ⟨h1, h2, h3⟩ := broker_mem hA hb
    have hsub : ({.s, .y 0, .z 0} : Finset (Party n m)) ⊆ L := by
      intro q hq; simp only [mem_insert, mem_singleton] at hq; rcases hq with rfl | rfl | rfl <;> assumption
    have h3' := card_le_card hsub
    have : ({.s, .y 0, .z 0} : Finset (Party n m)).card = 3 := by
      rw [card_insert_of_notMem (by simp), card_pair (by simp)]
    omega
  constructor
  · by_contra hlt
    push Not at hlt
    have hone : ∀ q ∈ L, q = .b := fun q hq => card_le_one.1 (by omega) q hq .b hb
    exact not_adequate_of_supplier_not_mem hV hv hc .b (fun hs => by simpa using hone _ hs)
      (fun q hq => Or.inl (hone q hq)) hA
  · intro h2
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 h2
    have hs : Party.s ∈ ({x, y} : Finset _) := by
      by_contra hs
      rcases (by simpa using hb : Party.b = x ∨ Party.b = y) with rfl | rfl
      · exact not_adequate_of_supplier_not_mem hV hv hc y hs (by simp) hA
      · exact not_adequate_of_supplier_not_mem hV hv hc x hs (fun q hq => by
          simp only [mem_insert, mem_singleton] at hq; tauto) hA
    simp only [mem_insert, mem_singleton] at hb hs
    rcases hb with rfl | rfl <;> rcases hs with h | h
    · exact absurd h (by simp)
    · rw [← h]
    · rw [← h, pair_comm]
    · exact absurd h (by simp)

/-- **Lemma 4.4, backward direction** of [Chan–Lesani]: if `{b, s}` (or a subset of it) is an adequate
leader set of `F`, then `K` is satisfiable. -/
theorem satisfiable_of_adequate (hm : 1 ≤ m) {L : Finset (Party n m)} (hL : L ⊆ {.b, .s})
    (hA : (flower K m c).Adequate (flowerOwn K m c) L) : K.Satisfiable := by
  obtain ⟨S, hS, hdis, e, heT, hen⟩ := hA.first_hit
    (T := univ.filter fun e => ∃ k : Fin (m + 1), (k : ℕ) ≠ 0 ∧ e = .toY k)
    ⟨.toY ⟨1, by omega⟩, by simp only [mem_filter, mem_univ, true_and]; exact ⟨⟨1, by omega⟩, by simp, rfl⟩⟩
  have htoY : ∀ k : Fin (m + 1), (k : ℕ) ≠ 0 → Edge.toY k ∉ S := fun k hk h =>
    disjoint_left.1 hdis h (by simp only [mem_filter, mem_univ, true_and]; exact ⟨k, hk, rfl⟩)
  have hLy : ∀ k, Party.y k ∉ L := fun k h => by simpa using hL h
  have hLz : ∀ k, Party.z k ∉ L := fun k h => by simpa using hL h
  have hLx : ∀ i, Party.x i ∉ L := fun i h => by simpa using hL h
  have hfromY : ∀ k : Fin (m + 1), (k : ℕ) ≠ 0 → Edge.fromY k ∉ S := fun k hk h =>
    ((hS.follower h (e' := .toY k) rfl).resolve_left (hLy k)) |> htoY k hk
  have hfromYB : ∀ j, Edge.fromYB j ∉ S := fun j h =>
    ((hS.follower h (e' := .toY (ybLevel j)) rfl).resolve_left (hLy _)) |> htoY _ (by simp [ybLevel])
  simp only [mem_filter, mem_univ, true_and] at heT
  obtain ⟨k, hk, rfl⟩ := heT
  obtain ⟨-, -, hpay⟩ := hen
  obtain ⟨k', hk'⟩ : ∃ k', (k : ℕ) = k' + 1 := ⟨k - 1, by omega⟩
  change (flower K m c).outflow S .b (inAsset k) + (if (k : ℕ) = 0 then K.V - 1 else 3) ≤
    flowerOwn K m c .b (inAsset k) + (flower K m c).inflow S .b (inAsset k) at hpay
  have hasset : inAsset k = .C (((⟨k', by omega⟩ : Fin (m + 1)) : ℕ) + 1) := by
    simp [inAsset, hk']
  rw [ite_eq_right hk, own_b, zero_add, hasset, inflow_C _ _ _ S ⟨k', by omega⟩ (by simp; omega)] at hpay
  -- both `y_{k'+1}` and `z_{k'+1}` are active, so `k' = 0`
  have hY : Edge.fromY ⟨k', by omega⟩ ∈ S := by by_contra h; simp [h] at hpay; split_ifs at hpay <;> omega
  have hk0 : k' = 0 := by by_contra h; exact hfromY _ (by simpa using h) hY
  subst hk0
  have hY' : Edge.fromY (0 : Fin (m + 1)) ∈ S := hY
  have hZ : Edge.fromZ (0 : Fin (m + 1)) ∈ S := by
    by_contra h; simp only [Fin.zero_eta, hY', h, ite_true, ite_false] at hpay; omega
  have hY0 : Edge.toY 0 ∈ S := (hS.follower hY (e' := .toY 0) rfl).resolve_left (hLy _)
  have hZ0 : Edge.toZ 0 ∈ S := (hS.follower hZ (e' := .toZ 0) rfl).resolve_left (hLz _)
  -- the funded items form a knapsack solution
  refine ⟨univ.filter fun i => Edge.toX i ∈ S, ?_, ?_⟩
  · have hbal := hS.balance_b .E
    rw [outflow_E, inflow_E, ite_eq_left hY0, ite_eq_left hZ0] at hbal
    rw [sum_filter]
    calc K.V ≤ K.V - 1 + 1 := by omega
      _ ≤ _ := hbal
      _ ≤ _ := sum_le_sum fun i _ => by
          by_cases h : Edge.fromX i ∈ S
          · simp [h, (hS.follower h (e' := .toX i) rfl).resolve_left (hLx i)]
          · simp [h]
  · have hbal := hS.balance_b .B
    rw [outflow_B, inflow_B, sum_eq_zero fun j _ => ite_eq_right (hfromYB j)] at hbal
    rw [sum_filter]
    refine hbal.trans ?_
    split_ifs <;> simp

end Podc.HTLCBrokeringHardness
