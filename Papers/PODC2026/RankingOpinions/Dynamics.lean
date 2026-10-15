import Papers.PODC2026.RankingOpinions.Layers
import Cslib.Computability.Distributed.PopulationProtocols.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Dynamics of the braket part of Circles

Breitkopf, Dallot, El-Hayek, Schmid, PODC 2026, Section 3.

The braket part of Circles (rule (1)): two agents exchange their kets iff this strictly decreases
the minimum weight of their two brakets. We prove
* the global braket invariant (Lemma 3.3): bras never change, kets are permuted;
* termination (Theorem 3.4): in *every* execution there are finitely many ket exchanges.
  Instead of the paper's ordinal potential `ω^{n-1} w_1 + … + w_n` we use the natural number
  `Φ = ∑_a 3^(k - w(a))`, which strictly increases at every ket exchange and is bounded;
* under weak fairness, the final braket configuration is stable, hence (Lemma 3.7) its multiset of
  brakets is `⋃_p f(G_p)`.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ}

/-- Rule (1) of Circles: exchange the kets iff it strictly decreases the minimum weight. -/
def exch (e f : Braket k) : Braket k × Braket k :=
  if Profitable e f then ((e.1, f.2), (f.1, e.2)) else (e, f)

/-- The braket part of Circles (the protocol "Circles without the `out` entry", footnote 1). -/
def circlesCore (k : ℕ) : Protocol (Braket k) := ⟨exch⟩

variable {A : Type*} [DecidableEq A]

lemma core_interact (C : Config A (Braket k)) {a b : A} (hab : a ≠ b) :
    (circlesCore k).interact C a b =
      if Profitable (C a) (C b) then fun x => ((C x).1, (C (Equiv.swap a b x)).2) else C := by
  funext x
  simp only [Protocol.interact, circlesCore, exch]
  by_cases hxa : x = a
  · subst hxa; split_ifs <;> simp_all
  · by_cases hxb : x = b
    · subst hxb; split_ifs <;> simp_all
    · split_ifs <;> simp_all [Equiv.swap_apply_of_ne_of_ne]

lemma core_interact_fst (C : Config A (Braket k)) {a b : A} (hab : a ≠ b) (x : A) :
    ((circlesCore k).interact C a b x).1 = (C x).1 := by
  rw [core_interact C hab]; split_ifs <;> rfl

lemma core_interact_eq_of_not {C : Config A (Braket k)} {a b : A} (hab : a ≠ b)
    (h : ¬ Profitable (C a) (C b)) : (circlesCore k).interact C a b = C := by
  rw [core_interact C hab, if_neg h]

variable [Fintype A]

/-- Multiset of brakets of a configuration. -/
def brakets (C : Config A (Braket k)) : Multiset (Braket k) := univ.val.map C

lemma core_kets_interact (C : Config A (Braket k)) {a b : A} (hab : a ≠ b) :
    (brakets ((circlesCore k).interact C a b)).map Prod.snd = (brakets C).map Prod.snd := by
  rw [core_interact C hab]
  split_ifs
  · simp only [brakets, Multiset.map_map]
    have : (Prod.snd ∘ fun x => ((C x).1, (C (Equiv.swap a b x)).2)) =
        (Prod.snd ∘ C) ∘ (Equiv.swap a b) := rfl
    rw [this, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  · rfl

lemma core_bras_interact (C : Config A (Braket k)) {a b : A} (hab : a ≠ b) :
    (brakets ((circlesCore k).interact C a b)).map Prod.fst = (brakets C).map Prod.fst := by
  simp only [brakets, Multiset.map_map, Function.comp_def, core_interact_fst C hab]

/-! ### The potential -/

/-- The termination potential `Φ(C) = ∑_a 3^(k - w(C a))`. -/
def pot (C : Config A (Braket k)) : ℕ := ∑ a, 3 ^ (k - w k (C a).1 (C a).2)

lemma pot_le (C : Config A (Braket k)) : pot C ≤ Fintype.card A * 3 ^ k := by
  unfold pot
  calc ∑ a, 3 ^ (k - w k (C a).1 (C a).2) ≤ ∑ _a : A, 3 ^ k :=
        Finset.sum_le_sum fun a _ => Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    _ = Fintype.card A * 3 ^ k := by simp

lemma sum_split (g : A → ℕ) {a b : A} (hab : a ≠ b) :
    ∑ x, g x = g a + g b + ∑ x ∈ (univ.erase a).erase b, g x := by
  rw [← Finset.add_sum_erase _ _ (mem_univ a), ← Finset.add_sum_erase _ _
    (mem_erase.2 ⟨Ne.symm hab, mem_univ b⟩), add_assoc]

/-- Each ket exchange strictly increases the potential. -/
lemma pot_lt_interact {C : Config A (Braket k)} {a b : A} (hab : a ≠ b)
    (h : Profitable (C a) (C b)) : pot C < pot ((circlesCore k).interact C a b) := by
  set C' := (circlesCore k).interact C a b with hC'
  have hrest : ∑ x ∈ (univ.erase a).erase b, 3 ^ (k - w k (C x).1 (C x).2) =
      ∑ x ∈ (univ.erase a).erase b, 3 ^ (k - w k (C' x).1 (C' x).2) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [mem_erase] at hx
    rw [hC', Protocol.interact_other _ _ hx.2.1 hx.1]
  have hCa : C' a = ((C a).1, (C b).2) := by
    rw [hC', core_interact C hab, if_pos h]; simp
  have hCb : C' b = ((C b).1, (C a).2) := by
    rw [hC', core_interact C hab, if_pos h]; simp
  unfold pot
  rw [sum_split _ hab, sum_split (fun x => 3 ^ (k - w k (C' x).1 (C' x).2)) hab, hrest, hCa, hCb]
  simp only
  unfold Profitable at h
  set m := min (w k (C a).1 (C b).2) (w k (C b).1 (C a).2)
  have h1 : m < w k (C a).1 (C a).2 := lt_of_lt_of_le h (min_le_left _ _)
  have h2 : m < w k (C b).1 (C b).2 := lt_of_lt_of_le h (min_le_right _ _)
  have hk1 := w_le (C a).1 (C a).2
  have hk2 := w_le (C b).1 (C b).2
  have e1 : 3 ^ (k - w k (C a).1 (C a).2) ≤ 3 ^ (k - m - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : 3 ^ (k - w k (C b).1 (C b).2) ≤ 3 ^ (k - m - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : 3 ^ (k - m) = 3 * 3 ^ (k - m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e4 : 3 ^ (k - m) ≤ 3 ^ (k - w k (C a).1 (C b).2) + 3 ^ (k - w k (C b).1 (C a).2) := by
    rcases min_choice (w k (C a).1 (C b).2) (w k (C b).1 (C a).2) with hm | hm
    · have : m = w k (C a).1 (C b).2 := hm
      rw [this]; exact Nat.le_add_right _ _
    · have : m = w k (C b).1 (C a).2 := hm
      rw [this]; exact Nat.le_add_left _ _
  have : 0 < 3 ^ (k - m - 1) := Nat.pow_pos (by omega)
  omega

/-! ### Executions of the braket protocol -/

variable (E : (circlesCore k).Execution A)

/-- Bras never change. -/
lemma bra_const (t : ℕ) (a : A) : (E.config t a).1 = (E.config 0 a).1 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [E.step t, core_interact_fst _ (E.sched_ne t), ih]

lemma kets_const (t : ℕ) :
    (brakets (E.config t)).map Prod.snd = (brakets (E.config 0)).map Prod.snd := by
  induction t with
  | zero => rfl
  | succ t ih => rw [E.step t, core_kets_interact _ (E.sched_ne t), ih]

lemma bras_const (t : ℕ) :
    (brakets (E.config t)).map Prod.fst = (brakets (E.config 0)).map Prod.fst := by
  induction t with
  | zero => rfl
  | succ t ih => rw [E.step t, core_bras_interact _ (E.sched_ne t), ih]

lemma pot_mono_step (t : ℕ) : pot (E.config t) ≤ pot (E.config (t + 1)) := by
  rw [E.step t]
  by_cases h : Profitable (E.config t (E.sched t).1) (E.config t (E.sched t).2)
  · exact (pot_lt_interact (E.sched_ne t) h).le
  · rw [core_interact_eq_of_not (E.sched_ne t) h]

lemma pot_mono {s t : ℕ} (h : s ≤ t) : pot (E.config s) ≤ pot (E.config t) := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact ih.trans (pot_mono_step E t)

/-- **Theorem 3.4** (Stabilization): in every execution (fair or not), the agents exchange their
kets only finitely many times: from some time `T` on, the configuration never changes. -/
theorem eventually_const : ∃ T, ∀ t ≥ T, E.config t = E.config T := by
  -- the potential is bounded and monotone, hence eventually constant
  set S := Set.range fun t => pot (E.config t)
  have hbdd : BddAbove S := ⟨Fintype.card A * 3 ^ k, by rintro _ ⟨t, rfl⟩; exact pot_le _⟩
  obtain ⟨T, hT⟩ : sSup S ∈ S := Nat.sSup_mem ⟨_, 0, rfl⟩ hbdd
  have hmax : ∀ t, pot (E.config t) ≤ pot (E.config T) := fun t => by
    rw [show pot (E.config T) = sSup S from hT]; exact le_csSup hbdd ⟨t, rfl⟩
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [E.step t]
    have hnp : ¬ Profitable (E.config t (E.sched t).1) (E.config t (E.sched t).2) := by
      intro hp
      have := pot_lt_interact (E.sched_ne t) hp
      rw [← E.step t] at this
      have := hmax (t + 1); have := pot_mono E ht
      omega
    rw [core_interact_eq_of_not (E.sched_ne t) hnp, ih]

/-- A configuration is stable if no two distinct agents can profitably exchange kets. -/
def Stable (C : Config A (Braket k)) : Prop := ∀ a b, a ≠ b → ¬ Profitable (C a) (C b)

lemma Stable.closed : (circlesCore k).Closed (Stable (A := A)) := by
  rintro C C' hC ⟨a, b, hab, rfl⟩
  rwa [core_interact_eq_of_not hab (hC a b hab)]

lemma Stable.reachable_eq {C C' : Config A (Braket k)} (hC : Stable C)
    (h : (circlesCore k).Reachable C C') : C' = C := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨a, b, hab, rfl⟩ := hst
    rw [ih] at *
    exact (core_interact_eq_of_not hab (hC a b hab))

/-- Under weak fairness, the configuration from which nothing changes any more is stable. -/
lemma stable_of_weaklyFair (hE : E.WeaklyFair) {T : ℕ}
    (hT : ∀ t ≥ T, E.config t = E.config T) : Stable (E.config T) := by
  intro a b hab hp
  obtain ⟨t, ht, hs⟩ := hE a b hab T
  have h1 := hT (t + 1) (by omega)
  rw [E.step t, hT t ht] at h1
  have hne := E.sched_ne t
  rcases hs with hs | hs
  · rw [hs] at h1 hne
    simp only at h1 hne
    rw [core_interact _ hne, if_pos hp] at h1
    have := congrFun h1 a
    simp only [Equiv.swap_apply_left] at this
    exact hp.ket_ne (Prod.ext_iff.1 this).2.symm
  · rw [hs] at h1 hne
    simp only at h1 hne
    rw [core_interact _ hne, if_pos (profitable_comm.1 hp)] at h1
    have := congrFun h1 a
    simp only [Equiv.swap_apply_right] at this
    exact hp.ket_ne (Prod.ext_iff.1 this).2.symm

/-- Stable configurations have stable braket multisets. -/
lemma Stable.mstable {C : Config A (Braket k)} (hC : Stable C) : MStable (brakets C) := by
  intro e f hle
  have he : e ∈ brakets C := Multiset.mem_of_le hle (Multiset.mem_cons_self _ _)
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 he
  have hsplit : brakets C = C a ::ₘ (univ.erase a).val.map C := by
    rw [brakets, Finset.erase_val, ← Multiset.map_cons,
      Multiset.cons_erase (by simp : a ∈ (univ : Finset A).val)]
  rw [hsplit, Multiset.cons_le_cons_iff] at hle
  have hf : f ∈ (univ.erase a).val.map C := Multiset.mem_of_le hle (Multiset.mem_cons_self _ _)
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hf
  exact hC a b (Ne.symm (Finset.ne_of_mem_erase hb))

/-- Number of agents with input color `c` (`x_c` in the paper). -/
def inputCount (input : A → Fin k) (c : Fin k) : ℕ := (univ.filter fun a => input a = c).card

/-- The initial braket configuration: every agent holds `⟨i|i⟩` for its input color `i`. -/
def initBrakets (input : A → Fin k) : Config A (Braket k) := fun a => (input a, input a)

lemma counts_init (input : A → Fin k) :
    Counts (brakets (initBrakets input)) (inputCount input) := by
  intro c
  simp only [brakets, initBrakets, Multiset.map_map, Function.comp_def, inputCount,
    Multiset.count_map]
  constructor <;> simp [Finset.card, Finset.filter_val, eq_comm]

/-- **Lemma 3.3** (Global braket invariant): in every configuration of an execution starting from
the initial configuration, color `c` occurs `x_c` times as a bra and `x_c` times as a ket. -/
lemma counts_execution (input : A → Fin k) (h0 : E.config 0 = initBrakets input) (t : ℕ) :
    Counts (brakets (E.config t)) (inputCount input) := by
  intro c
  rw [bras_const, kets_const, h0]
  exact counts_init input c

/-- **Lemma 3.7** for executions: once stable, the multiset of brakets is `⋃_p f(G_p)`. -/
theorem brakets_eq_layers (input : A → Fin k) (h0 : E.config 0 = initBrakets input) {T : ℕ}
    (hT : Stable (E.config T)) : brakets (E.config T) = layers (inputCount input) :=
  eq_layers_of_stable _ _ (counts_execution E input h0 T) hT.mstable

/-- **Theorem 1.1, braket part.** Under a weakly fair scheduler the braket configuration of
Circles eventually never changes, and in that configuration an agent `⟨i|i⟩` exists iff `i` is the
unique color in relative majority (and has at least one supporter). -/
theorem circlesCore_main (input : A → Fin k) (h0 : E.config 0 = initBrakets input)
    (hE : E.WeaklyFair) :
    ∃ T, (∀ t ≥ T, E.config t = E.config T) ∧ Stable (E.config T) ∧
      brakets (E.config T) = layers (inputCount input) ∧
      ∀ i, (∃ a, E.config T a = (i, i)) ↔
        0 < inputCount input i ∧ ∀ c, c ≠ i → inputCount input c < inputCount input i := by
  obtain ⟨T, hT⟩ := eventually_const E
  have hS := stable_of_weaklyFair E hE hT
  refine ⟨T, hT, hS, brakets_eq_layers E input h0 hS, fun i => ?_⟩
  rw [← diag_mem_layers_iff, ← brakets_eq_layers E input h0 hS]
  simp [brakets]

end RankingOpinions
