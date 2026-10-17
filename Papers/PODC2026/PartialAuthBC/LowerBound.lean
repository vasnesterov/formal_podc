import Papers.PODC2026.PartialAuthBC.Model
import Podc.Computability.Distributed.Byzantine.LockStep.Cover

/-!
# Lower bounds: Theorem 4.1 and Corollary 4.2

Theorem 4.1 of the paper: with `s` registered parties among `n`, Byzantine broadcast with an
*unregistered* sender is impossible if `t ≥ max {⌈s/2⌉, ⌈n/3⌉}`; Corollary 4.2: the same for
Byzantine agreement. Note `t ≥ ⌈s/2⌉ ∧ t ≥ ⌈n/3⌉ ⇔ s ≤ 2t ∧ n ≤ 3t`.

## The cover

The parties are split into three groups `A` (label `0`), `B` (label `1`), `C` (label `2`), each of
size `≤ t`, with `B`, `C` nonempty, `A` free of registered parties, and (for broadcast) the sender in
`A` (`exists_lab`). The covering system lives on `P × Bool` (`φ = Prod.fst`) and uses only the
copies `A₀ = A × {false}`, `A₁ = A × {true}`, `B₀`, `C₀`, arranged on the line

  `A₀ — B₀ — C₀ — A₁`

(`A₀` and `A₁` are complete inside themselves; a node listens to nobody for the missing edges, e.g.
`A₀` does not hear `C`, `A₁` does not hear `B`). Inputs: `A₀`, `B₀` get `v₀`; `C₀`, `A₁` get `v₁`.

* Byzantine `C`, honest `A₀ ∪ B₀`: all honest inputs `v₀` (sender included), so `B₀` decides `v₀`.
* Byzantine `B`, honest `A₁ ∪ C₀`: all honest inputs `v₁`, so `C₀` decides `v₁`.
* Byzantine `A`, honest `B₀ ∪ C₀`: agreement between `B` and `C` is violated.

The covering adversaries respect unforgeability: every node listened to is an honest lift, a copy of
a Byzantine party, or a copy of an `A`-party, which is unregistered and hence never signs
(`CoverSystem.scenario_authValid_pa`). Registered parties occur only in `B ∪ C`, each with a single
copy, which is why `s ≤ 2t` is the relevant bound.

## Degenerate cases

Without a lower bound on `n`, both statements fail for tiny `n`:
for `n = 2` broadcast is trivially solvable (`bb_solvable_card_two`, `theorem41_false_card_two`),
and for `n = 1` agreement is (`ba_solvable_card_one`, `corollary42_false_card_one`).
-/

namespace PartialAuthBC

open Cslib.Byzantine.LockStep

namespace LowerBound

variable {P V : Type*}

/-! ### The partition into three groups -/

/-- Splitting the parties into groups `0` (unregistered, containing `S0`), `1`, `2`, each of size
`≤ t`, groups `1` and `2` nonempty. -/
lemma exists_lab [Fintype P] {Reg : Set P} {t : ℕ} (S0 : Finset P) (hS0 : ∀ p ∈ S0, p ∉ Reg)
    (hs : Reg.ncard ≤ 2 * t) (hn : Fintype.card P ≤ 3 * t) (ht : S0.card ≤ t)
    (h2 : 2 + S0.card ≤ Fintype.card P) :
    ∃ lab : P → Fin 3, (∀ p, lab p = 0 → p ∉ Reg) ∧ (∀ z, {p | lab p = z}.ncard ≤ t) ∧
      (∃ b, lab b = 1) ∧ (∃ c, lab c = 2) ∧ ∀ p ∈ S0, lab p = 0 := by
  classical
  set n := Fintype.card P with hn_def
  set k := max (max Reg.ncard (n - t)) 2 with hk_def
  have hk1 : Reg.ncard ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk2 : n - t ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hk3 : 2 ≤ k := le_max_right _ _
  have hRS : Reg.toFinset ⊆ Finset.univ \ S0 := by
    intro p hp
    simp only [Set.mem_toFinset] at hp
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h => hS0 p h hp
  have hcardS : (Finset.univ \ S0).card = n - S0.card := Finset.card_univ_sdiff S0
  have hRcard : Reg.ncard = Reg.toFinset.card := Set.ncard_eq_toFinset_card' Reg
  have hRle : Reg.toFinset.card ≤ (Finset.univ \ S0).card := Finset.card_le_card hRS
  have hk_le : k ≤ (Finset.univ \ S0).card := by
    refine max_le (max_le (by omega) (by omega)) (by omega)
  have hk2t : k ≤ 2 * t := max_le (max_le hs (by omega)) (by omega)
  obtain ⟨K, hRK, hKS, hK⟩ := Finset.exists_subsuperset_card_eq hRS (by omega) hk_le
  obtain ⟨B, hBK, hB⟩ := Finset.exists_subset_card_eq (s := K) (n := k - k / 2) (by omega)
  have hC : (K \ B).card = k / 2 := by rw [Finset.card_sdiff_of_subset hBK]; omega
  refine ⟨fun p => if p ∈ K then (if p ∈ B then 1 else 2) else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp hpR
    have : p ∈ K := hRK (by simpa using hpR)
    simp only [this, ↓reduceIte] at hp
    split_ifs at hp <;> exact absurd hp (by decide)
  · have e0 : {p | (if p ∈ K then (if p ∈ B then 1 else 2) else 0 : Fin 3) = 0} =
        ↑(Finset.univ \ K) := by
      ext p; simp only [Set.mem_ofPred_eq, Finset.coe_sdiff, Finset.coe_univ, Set.mem_sdiff,
        Set.mem_univ, true_and, Finset.mem_coe]
      split_ifs <;> simp_all
    have e1 : {p | (if p ∈ K then (if p ∈ B then 1 else 2) else 0 : Fin 3) = 1} = ↑B := by
      ext p; simp only [Set.mem_ofPred_eq, Finset.mem_coe]
      split_ifs with h1 h2 <;> simp_all
      exact fun h => h1 (hBK h)
    have e2 : {p | (if p ∈ K then (if p ∈ B then 1 else 2) else 0 : Fin 3) = 2} =
        ↑(K \ B) := by
      ext p; simp only [Set.mem_ofPred_eq, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
      split_ifs <;> simp_all
    have hKc : (Finset.univ \ K).card = n - k := by rw [Finset.card_univ_sdiff, hK]
    intro z
    fin_cases z
    · simp only [Fin.zero_eta, Fin.isValue]; rw [e0, Set.ncard_coe_finset]; omega
    · simp only [Fin.mk_one, Fin.isValue]; rw [e1, Set.ncard_coe_finset]; omega
    · simp only [Fin.reduceFinMk, Fin.isValue]; rw [e2, Set.ncard_coe_finset]; omega
  · obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
    exact ⟨b, by simp [hBK hb, hb]⟩
  · obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < (K \ B).card by omega)
    rw [Finset.mem_sdiff] at hc
    exact ⟨c, by simp [hc.1, hc.2]⟩
  · intro p hp
    have : p ∉ K := fun h => (Finset.mem_sdiff.mp (hKS h)).2 hp
    simp [this]

/-! ### The covering system -/

/-- `lnk a c b`: the copy that a node of group `a` in copy `c` listens to as a sender of group `b`
(`none`: it hears nothing). Only the copies `A₀, A₁, B₀, C₀` are used. -/
def lnk (a : Fin 3) (c : Bool) (b : Fin 3) : Option Bool :=
  if a = 0 then
    (if c then (if b = 0 then some true else if b = 1 then none else some false)
     else (if b = 2 then none else some false))
  else if c then none
  else if a = 2 ∧ b = 0 then some true else some false

/-- The covering system of the proof of Theorem 4.1 (the line `A₀ — B₀ — C₀ — A₁`). -/
def cover (lab : P → Fin 3) (v₀ v₁ : V) : CoverSystem P V (P × Bool) :=
  CoverSystem.doubleCover (fun q c p => lnk (lab q) c (lab p))
    fun q => if lab q.1 = 0 then (if q.2 then v₁ else v₀) else if lab q.1 = 1 then v₀ else v₁

lemma xq_eq (lab : P → Fin 3) (v₀ v₁ : V) (p : P) (c : Bool) :
    (cover lab v₀ v₁).xq (p, c) =
      if lab p = 0 then (if c then v₁ else v₀) else if lab p = 1 then v₀ else v₁ := rfl

lemma Fin3_cases {a : Fin 3} (h : a ≠ 2) : a = 0 ∨ a = 1 := by revert a h; decide

lemma Fin3_cases' {a : Fin 3} (h : a ≠ 1) : a = 0 ∨ a = 2 := by revert a h; decide

lemma lnk_false {a : Fin 3} {c : Bool} {b : Fin 3} {c' : Bool} (h : lnk a c b = some c')
    (hb : b ≠ 0) : c' = false := by
  revert h hb; revert a c b c'; decide

/-- The general cover argument: any problem whose solutions satisfy validity (when all honest
inputs are equal and group `0` is honest) and agreement is unsolvable. -/
theorem not_solvablePA_of_lab {Reg : Set P} {Z : AdvStructure P} {spec : Spec P V V}
    (lab : P → Fin 3) (hA : ∀ p, lab p = 0 → p ∉ Reg) (hZ : ∀ z, {p | lab p = z} ∈ Z)
    {b c : P} (hb : lab b = 1) (hc : lab c = 2) {v₀ v₁ : V} (hne : v₀ ≠ v₁)
    (hval : ∀ x H dec v, spec x H dec → {p | lab p = 0} ⊆ H → (∀ p ∈ H, x p = v) →
      ∀ p ∈ H, dec p v)
    (hagr : ∀ x H dec, spec x H dec → ∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p v → dec q w → v = w) :
    ¬ SolvablePA Reg Z spec := by
  rintro ⟨M, S, Au, alg, hR, hU, hsolve⟩
  set C := cover lab v₀ v₁ with hC
  have hφ : ∀ q p q', C.nbr q p = some q' → C.φ q' = p :=
    fun _ _ _ h => CoverSystem.doubleCover_φ_of_nbr_eq_some h
  have hsim : ∀ (z : Fin 3) (σ : P → P × Bool), (∀ p, lab p ≠ z → lab p ≠ 0 → σ p = (p, false)) →
      ∀ q p q', (⊤ : SimpleGraph P).Adj p (C.φ q) → C.nbr q p = some q' →
      (∃ p', p' ∉ {p | lab p = z} ∧ q' = σ p') ∨ C.φ q' ∈ {p | lab p = z} ∨ C.φ q' ∉ Reg := by
    intro z σ hσ q p q' _ h
    simp only [C, cover, CoverSystem.doubleCover_nbr, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    by_cases h0 : lab p = 0
    · exact Or.inr (Or.inr (hA p h0))
    by_cases hz : lab p = z
    · exact Or.inr (Or.inl hz)
    · refine Or.inl ⟨p, hz, ?_⟩
      rw [hσ p hz h0, lnk_false hc' h0]
  -- one run of the cover: Byzantine group `z`, honest parties lifted by `σ`
  have run : ∀ (z : Fin 3) (σ : P → P × Bool), C.Lift ⊤ {p | lab p = z} σ →
      (∀ p, lab p ≠ z → lab p ≠ 0 → σ p = (p, false)) →
      spec (C.scenario ⊤ alg {p | lab p = z} σ fun _ => v₀).input {p | lab p = z}ᶜ
        (Decides ⊤ alg (C.scenario ⊤ alg {p | lab p = z} σ fun _ => v₀)) :=
    fun z σ hL hσ => hsolve _ (hZ z) (C.scenario_reliable _)
      (CoverSystem.scenario_authValid_pa C Reg hR hU hL hφ (hsim z σ hσ) _)
  have hin : ∀ (z : Fin 3) (σ : P → P × Bool) p, lab p ≠ z →
      (C.scenario ⊤ alg {p | lab p = z} σ fun _ => v₀).input p = C.xq (σ p) :=
    fun z σ p hp => C.scenario_input_of_not_mem _ (show p ∉ {p | lab p = z} from hp)
  -- Scenario 1: `C` Byzantine, `A₀ ∪ B₀` honest, all inputs `v₀`.
  have hL1 : C.Lift ⊤ {p | lab p = 2} (fun p => (p, false)) := by
    refine ⟨fun _ _ => rfl, fun p q hp hq _ => ?_⟩
    have key : ∀ a b : Fin 3, a ≠ 2 → b ≠ 2 → lnk a false b = some false := by decide
    simp only [C, cover, CoverSystem.doubleCover_nbr, key _ _ hq hp, Option.map_some]
  have d1 : C.Decides ⊤ alg (b, false) v₀ := by
    have hs := run 2 _ hL1 (fun _ _ _ => rfl)
    have hb' : b ∉ {p | lab p = 2} := by simp [hb]
    refine (C.decides_scenario_iff hL1 _ hb' _).mp (hval _ _ _ v₀ hs ?_ ?_ b hb')
    · intro p (hp : lab p = 0)
      show lab p ≠ 2
      rw [hp]; decide
    · intro p (hp : lab p ≠ 2)
      rw [hin 2 _ p hp, xq_eq]
      have := Fin3_cases hp
      split_ifs <;> simp_all
  -- Scenario 3: `B` Byzantine, `A₁ ∪ C₀` honest, all inputs `v₁`.
  have hL3 : C.Lift ⊤ {p | lab p = 1} (fun p => (p, decide (lab p = 0))) := by
    refine ⟨fun _ _ => rfl, fun p q hp hq _ => ?_⟩
    have key : ∀ a b : Fin 3, a ≠ 1 → b ≠ 1 →
        lnk a (decide (a = 0)) b = some (decide (b = 0)) := by decide
    simp only [C, cover, CoverSystem.doubleCover_nbr, key _ _ hq hp, Option.map_some]
  have d3 : C.Decides ⊤ alg (c, false) v₁ := by
    have hs := run 1 _ hL3 (fun p _ h0 => by simp [h0])
    have hc' : c ∉ {p | lab p = 1} := by simp [hc]
    have := (C.decides_scenario_iff hL3 _ hc' _).mp (hval _ _ _ v₁ hs ?_ ?_ c hc')
    · have e : decide (lab c = 0) = false := by simp [hc]
      rwa [e] at this
    · intro p (hp : lab p = 0)
      show lab p ≠ 1
      rw [hp]; decide
    · intro p (hp : lab p ≠ 1)
      rw [hin 1 _ p hp, xq_eq]
      have := Fin3_cases' hp
      split_ifs <;> simp_all
  -- Scenario 2: `A` Byzantine, `B₀ ∪ C₀` honest: disagreement.
  have hL2 : C.Lift ⊤ {p | lab p = 0} (fun p => (p, false)) := by
    refine ⟨fun _ _ => rfl, fun p q hp hq _ => ?_⟩
    have key : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → lnk a false b = some false := by decide
    simp only [C, cover, CoverSystem.doubleCover_nbr, key _ _ hq hp, Option.map_some]
  have hs := run 0 _ hL2 (fun _ _ _ => rfl)
  have hb' : b ∉ {p | lab p = 0} := by simp [hb]
  have hc' : c ∉ {p | lab p = 0} := by simp [hc]
  exact hne (hagr _ _ _ hs b hb' c hc' v₀ v₁ ((C.decides_scenario_iff hL2 _ hb' _).mpr d1)
    ((C.decides_scenario_iff hL2 _ hc' _).mpr d3))

end LowerBound

open LowerBound

/-- **Theorem 4.1** (corrected: the sender must be unregistered, and `n ≥ 3`). With `s` registered
parties among `n ≥ 3`, an unregistered sender and `t ≥ max {⌈s/2⌉, ⌈n/3⌉}`, Byzantine broadcast
(with at least two values) is impossible in the partially authenticated synchronous model. -/
theorem theorem41 {P V : Type*} [Fintype P] (Reg : Set P) (snd : P) (hsnd : snd ∉ Reg) (t : ℕ)
    (hn : 3 ≤ Fintype.card P)
    (ht : max ((Reg.ncard + 1) / 2) ((Fintype.card P + 2) / 3) ≤ t) {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    ¬ SolvablePA Reg (atMost t) (BB (V := V) snd) := by
  classical
  have h1 : (Reg.ncard + 1) / 2 ≤ t := le_trans (le_max_left _ _) ht
  have h2 : (Fintype.card P + 2) / 3 ≤ t := le_trans (le_max_right _ _) ht
  obtain ⟨lab, hA, hZ, ⟨b, hb⟩, ⟨c, hc⟩, hS⟩ := exists_lab (Reg := Reg) (t := t) {snd}
    (by simpa using hsnd) (by omega) (by omega) (by simp; omega) (by simp; omega)
  have hsnd0 : lab snd = 0 := hS snd (Finset.mem_singleton_self _)
  refine not_solvablePA_of_lab lab hA hZ hb hc hv ?_ (fun _ _ _ h => h.2.2)
  intro x H dec v h hsub hx p hp
  have hsH : snd ∈ H := hsub hsnd0
  simpa [hx snd hsH] using h.2.1 hsH p hp

/-- **Corollary 4.2** (corrected: `n ≥ 2`). With `s` registered parties among `n ≥ 2` and
`t ≥ max {⌈s/2⌉, ⌈n/3⌉}`, Byzantine agreement (with at least two values) is impossible in the
partially authenticated synchronous model. -/
theorem corollary42 {P V : Type*} [Fintype P] (Reg : Set P) (t : ℕ) (hn : 2 ≤ Fintype.card P)
    (ht : max ((Reg.ncard + 1) / 2) ((Fintype.card P + 2) / 3) ≤ t) {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    ¬ SolvablePA Reg (atMost t) (BA (P := P) (V := V)) := by
  classical
  have h1 : (Reg.ncard + 1) / 2 ≤ t := le_trans (le_max_left _ _) ht
  have h2 : (Fintype.card P + 2) / 3 ≤ t := le_trans (le_max_right _ _) ht
  obtain ⟨lab, hA, hZ, ⟨b, hb⟩, ⟨c, hc⟩, -⟩ := exists_lab (Reg := Reg) (t := t) ∅
    (by simp) (by omega) (by omega) (by simp) (by simp; omega)
  exact not_solvablePA_of_lab lab hA hZ hb hc hv
    (fun x H dec v h _ hx => h.2.1 v hx) (fun _ _ _ h => h.2.2)

/-! ### Degenerate cases: the size hypotheses are needed -/

section Degenerate

variable {P : Type*} [DecidableEq P]

/-- The trivial broadcast protocol: the sender sends its input to everybody and decides it at
round `0`; everybody else decides, after one round, the value received from the sender (its own
input if nothing arrived). -/
def trivialBB {V : Type} (snd : P) : Protocol P V V V where
  send p x _ _ := if p = snd then some x else none
  decide p x h := if p = snd then some x else h.head?.map fun ib => (ib snd).getD x

lemma trivialBB_decides_snd {V : Type} (snd : P) (s : Scenario P V V) :
    Decides ⊤ (trivialBB snd) s snd (s.input snd) :=
  ⟨0, by simp [status, trivialBB], fun _ h => absurd h (Nat.not_lt_zero _)⟩

lemma trivialBB_decides {V : Type} (snd : P) (s : Scenario P V V) {p : P} (hp : p ≠ snd) :
    Decides ⊤ (trivialBB snd) s p
      ((deliver ⊤ (trivialBB snd) s (hist ⊤ (trivialBB snd) s 0) 0 snd p).getD (s.input p)) := by
  refine ⟨1, ?_, fun r hr => ?_⟩
  · simp [status, trivialBB, hp, hist_succ]
  · obtain rfl : r = 0 := by omega
    simp [status, trivialBB, hp]

lemma trivialBB_deliver {V : Type} (snd : P) (s : Scenario P V V) (hs : s.Reliable)
    (hsnd : snd ∉ s.byz) {p : P} (hp : p ≠ snd) :
    deliver ⊤ (trivialBB snd) s (hist ⊤ (trivialBB snd) s 0) 0 snd p = some (s.input snd) := by
  simp [deliver, hsnd, hs 0 snd p, trivialBB, Ne.symm hp]

/-- With two parties, Byzantine broadcast is solvable against any corruptions (for any set of
registered parties, any sender and any value type). -/
theorem bb_solvable_card_two [Fintype P] (hP : Fintype.card P = 2) (Reg : Set P) (snd : P)
    (V : Type) : SolvablePA Reg Set.univ (BB (V := V) snd) := by
  refine Solvable.solvablePA ⟨V, trivialBB snd, fun s _ hs => ?_⟩
  -- every party other than `snd` is the same party
  have huniq : ∀ p q : P, p ≠ snd → q ≠ snd → p = q := by
    intro p q hp hq
    by_contra hpq
    have : ({p, q, snd} : Finset P).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq, hp]), Finset.card_pair hq]
    have := Finset.card_le_univ ({p, q, snd} : Finset P)
    omega
  -- decisions when the sender is honest
  have hval : snd ∈ s.honest → ∀ p ∈ s.honest, Decides ⊤ (trivialBB snd) s p (s.input snd) := by
    intro hsnd p _
    by_cases hp : p = snd
    · subst hp; exact trivialBB_decides_snd _ s
    · have := trivialBB_decides snd s hp
      rwa [trivialBB_deliver snd s hs hsnd hp] at this
  refine ⟨fun p _ => ?_, hval, fun p hp q hq v w hv hw => ?_⟩
  · by_cases h : p = snd
    · subst h; exact ⟨_, trivialBB_decides_snd _ s⟩
    · exact ⟨_, trivialBB_decides snd s h⟩
  · by_cases hsnd : snd ∈ s.honest
    · exact (Decides.unique _ _ hv (hval hsnd p hp)).trans (Decides.unique _ _ hw (hval hsnd q hq)).symm
    · have hp' : p ≠ snd := fun h => hsnd (h ▸ hp)
      have hq' : q ≠ snd := fun h => hsnd (h ▸ hq)
      obtain rfl := huniq p q hp' hq'
      exact Decides.unique _ _ hv hw

/-- **Theorem 4.1 is false for `n = 2`**: two parties, nobody registered, unregistered sender `0`,
`t = 1 = max {⌈0/2⌉, ⌈2/3⌉}`, binary values — all hypotheses of Theorem 4.1 except `n ≥ 3` hold,
yet Byzantine broadcast is solvable. -/
theorem theorem41_false_card_two :
    (0 : Fin 2) ∉ (∅ : Set (Fin 2)) ∧
    max (((∅ : Set (Fin 2)).ncard + 1) / 2) ((Fintype.card (Fin 2) + 2) / 3) ≤ 1 ∧
    (true ≠ false) ∧
    SolvablePA (∅ : Set (Fin 2)) (atMost 1) (BB (V := Bool) (0 : Fin 2)) :=
  ⟨by simp, by simp, by decide,
    (bb_solvable_card_two (by simp) ∅ 0 Bool).mono (Set.subset_univ _)⟩

/-- The trivial agreement protocol: decide your own input at round `0`. -/
def trivialBA {V : Type*} : Protocol P V Unit V where
  send _ _ _ _ := none
  decide _ x _ := some x

omit [DecidableEq P] in
/-- With one party, Byzantine agreement is solvable (for any set of registered parties and any
value type). -/
theorem ba_solvable_card_one [Fintype P] (hP : Fintype.card P = 1) (Reg : Set P) (V : Type*) :
    SolvablePA Reg Set.univ (BA (P := P) (V := V)) := by
  have hdec : ∀ (s : Scenario P V Unit) p, Decides ⊤ (trivialBA (P := P)) s p (s.input p) :=
    fun s p => ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hsub : ∀ p q : P, p = q := fun p q =>
    Fintype.card_le_one_iff.mp hP.le p q
  refine Solvable.solvablePA ⟨Unit, trivialBA, fun s _ _ => ⟨fun p _ => ⟨_, hdec s p⟩,
    fun v hv p hp => hv p hp ▸ hdec s p, fun p _ q _ v w hv hw => ?_⟩⟩
  obtain rfl := hsub p q
  exact Decides.unique _ _ hv hw

/-- **Corollary 4.2 is false for `n = 1`**: one unregistered party, `t = 1 = max {⌈0/2⌉, ⌈1/3⌉}`,
binary values — all hypotheses except `n ≥ 2` hold, yet Byzantine agreement is solvable. -/
theorem corollary42_false_card_one :
    max (((∅ : Set (Fin 1)).ncard + 1) / 2) ((Fintype.card (Fin 1) + 2) / 3) ≤ 1 ∧
    (true ≠ false) ∧
    SolvablePA (∅ : Set (Fin 1)) (atMost 1) (BA (P := Fin 1) (V := Bool)) :=
  ⟨by simp, by decide, (ba_solvable_card_one (by simp) ∅ Bool).mono (Set.subset_univ _)⟩

end Degenerate

end PartialAuthBC
