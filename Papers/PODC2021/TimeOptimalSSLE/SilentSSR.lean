import Papers.PODC2021.TimeOptimalSSLE.Model
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Podc.Foundations.Data.Fin.Cyclic

/-!
# Protocol 1 (`Silent-n-state-SSR`, Cai–Izumi–Wada): Lemmas 2.2, 2.3 and Theorem 2.4

States are ranks `Fin n`; when the initiator and the responder have the same rank, the responder
increments its rank modulo `n`:

  `if a.rank = b.rank then b.rank ← (b.rank + 1) mod n`.

* `IsBarrier C k` is inequality (1) of the paper: `∑_{d=0}^{r} m_{(k-d) mod n}(C) ≤ r + 1` for all
  `r < n`, where `m_i(C)` is the number of agents with rank `i`.
* `exists_barrier` (**Lemma 2.2**): every configuration has a barrier rank. We use a different
  (extremal) proof than the paper: a rank `k` maximising `∑_a ((k - rank a) mod n)` is a barrier.
* `IsBarrier.step` (**Lemma 2.3**): a barrier stays a barrier forever.
* With a barrier `k` fixed, every non-null interaction decreases `∑_a ((k - rank a) mod n)` by
  exactly one (`potential_step`), so **every** execution, under any scheduler, has at most
  `n (n - 1)` non-null interactions (`card_changes_le`).
* **Theorem 2.4 (correctness part)**: the protocol solves self-stabilizing ranking
  (`solvesSSR`), every weakly fair execution becomes silent in a correctly ranked configuration
  (`weaklyFair_eventually_ranked`), and with `leader ↔ rank = 0` it solves SSLE
  (`solvesSSLE`). The time bounds of Theorem 2.4 are not formalized.
-/

open Cslib.PopulationProtocol Finset Fin.NatCast

set_option linter.unusedSectionVars false

namespace TimeOptimalSSLE.SilentSSR

variable {n : ℕ} [NeZero n]

/-- Protocol 1, `Silent-n-state-SSR`. -/
def silentSSR (n : ℕ) [NeZero n] : Protocol (Fin n) where
  δ i j := if i = j then (i, j + 1) else (i, j)

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- `m_i(C)`: the number of agents with rank `i`. -/
def count (C : Config A (Fin n)) (i : Fin n) : ℕ := (univ.filter fun a => C a = i).card

/-- Inequality (1) of the paper: `k` is a *barrier rank* for `C`. -/
def IsBarrier (C : Config A (Fin n)) (k : Fin n) : Prop :=
  ∀ r < n, ∑ d ∈ range (r + 1), count C (k - (d : Fin n)) ≤ r + 1

/-- Number of agents whose rank is at cyclic distance `≤ r` below `k`. -/
def win (C : Config A (Fin n)) (k : Fin n) (r : ℕ) : ℕ :=
  (univ.filter fun a => (k - C a).val ≤ r).card

lemma val_natCast_of_lt {d : ℕ} (hd : d < n) : ((d : Fin n)).val = d := by
  rw [Fin.val_natCast, Nat.mod_eq_of_lt hd]

lemma sum_count_eq_win (C : Config A (Fin n)) (k : Fin n) {r : ℕ} (hr : r < n) :
    ∑ d ∈ range (r + 1), count C (k - (d : Fin n)) = win C k r := by
  unfold win
  rw [card_eq_sum_card_fiberwise (f := C) (t := univ.filter fun i : Fin n => (k - i).val ≤ r)
    (fun a ha => by simpa using ha)]
  refine sum_nbij' (fun d => k - (d : Fin n)) (fun i => (k - i).val) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_range] at hd
    simp only [mem_filter, mem_univ, true_and, sub_sub_cancel]
    rw [val_natCast_of_lt (by omega)]; omega
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_range]; omega
  · intro d hd
    simp only [mem_range] at hd
    simp only [sub_sub_cancel]
    exact val_natCast_of_lt (by omega)
  · intro i _
    simp
  · intro d hd
    simp only [mem_range] at hd
    unfold count
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, h⟩
      rw [h, sub_sub_cancel, val_natCast_of_lt (by omega)]; omega
    · intro h; exact h.2

lemma isBarrier_iff (C : Config A (Fin n)) (k : Fin n) :
    IsBarrier C k ↔ ∀ r < n, win C k r ≤ r + 1 := by
  unfold IsBarrier
  exact forall₂_congr fun r hr => by rw [sum_count_eq_win C k hr]

lemma win_le_card (C : Config A (Fin n)) (k : Fin n) (r : ℕ) : win C k r ≤ Fintype.card A :=
  card_le_univ _

/-- The potential `∑_a ((k - rank a) mod n)`. -/
def pot (C : Config A (Fin n)) (k : Fin n) : ℕ := ∑ a, (k - C a).val

/-- Shifting the candidate barrier down by `r + 1` changes the potential by
`n * (win - (r + 1))`. -/
lemma pot_shift (C : Config A (Fin n)) (k : Fin n) {r : ℕ} (hr : r + 1 < n) :
    pot C (k - ((r + 1 : ℕ) : Fin n)) + Fintype.card A * (r + 1) = pot C k + n * win C k r := by
  have hb : (((r + 1 : ℕ) : Fin n)).val = r + 1 := val_natCast_of_lt hr
  have key : ∀ a, (k - ((r + 1 : ℕ) : Fin n) - C a).val + (r + 1) =
      (k - C a).val + (if (k - C a).val ≤ r then n else 0) := by
    intro a
    have : k - ((r + 1 : ℕ) : Fin n) - C a = (k - C a) - ((r + 1 : ℕ) : Fin n) := by abel
    rw [this]
    set x := k - C a
    have hx := x.isLt
    by_cases hxr : x.val ≤ r
    · rw [ite_eq_left hxr]
      have hlt : x < ((r + 1 : ℕ) : Fin n) := by rw [Fin.lt_def, hb]; omega
      rw [Fin.coe_sub_iff_lt.mpr hlt, hb]; omega
    · rw [ite_eq_right hxr]
      have hle : ((r + 1 : ℕ) : Fin n) ≤ x := by rw [Fin.le_def, hb]; omega
      rw [Fin.sub_val_of_le hle, hb]; omega
  have h1 : ∑ a, ((k - ((r + 1 : ℕ) : Fin n) - C a).val + (r + 1)) =
      ∑ a, ((k - C a).val + if (k - C a).val ≤ r then n else 0) := sum_congr rfl fun a _ => key a
  have e1 : ∑ a : A, ((k - ((r + 1 : ℕ) : Fin n) - C a).val + (r + 1)) =
      pot C (k - ((r + 1 : ℕ) : Fin n)) + Fintype.card A * (r + 1) := by
    unfold pot; rw [sum_add_distrib]; simp
  have e2 : ∑ a : A, ((k - C a).val + if (k - C a).val ≤ r then n else 0) =
      pot C k + n * win C k r := by
    unfold pot win; rw [sum_add_distrib, ← sum_filter]; simp [mul_comm]
  rw [← e1, ← e2]; exact h1

/-- **Lemma 2.2.** Every configuration of `Silent-n-state-SSR` has a barrier rank. -/
theorem exists_barrier (hA : Fintype.card A = n) (C : Config A (Fin n)) :
    ∃ k, IsBarrier C k := by
  obtain ⟨k, -, hk⟩ := exists_max_image univ (pot C) univ_nonempty
  refine ⟨k, (isBarrier_iff C k).mpr fun r hr => ?_⟩
  by_contra hlt
  push Not at hlt
  have hr1 : r + 1 < n := by
    have := win_le_card C k r; omega
  have h := pot_shift C k hr1
  have := hk (k - ((r + 1 : ℕ) : Fin n)) (mem_univ _)
  rw [hA] at h
  nlinarith

/-- The protocol in closed form: a collision moves the responder up by one rank. -/
lemma interact_eq (C : Config A (Fin n)) (a b : A) (hab : a ≠ b) :
    (silentSSR n).interact C a b =
      if C a = C b then Function.update C b (C b + 1) else C := by
  funext x
  simp only [Protocol.interact, silentSSR]
  by_cases hxa : x = a
  · subst hxa; split_ifs <;> simp [Function.update, *]
  · by_cases hxb : x = b
    · subst hxb; split_ifs <;> simp_all
    · split_ifs <;> simp_all [Function.update]

/-- At a barrier, no two agents have the barrier rank. -/
lemma IsBarrier.collision_ne {C : Config A (Fin n)} {k : Fin n} (hk : IsBarrier C k) {a b : A}
    (hab : a ≠ b) (hC : C a = C b) : (k - C b).val ≠ 0 := by
  intro h0
  have hw := ((isBarrier_iff C k).mp hk) 0 (NeZero.pos n)
  have : ({a, b} : Finset A) ⊆ univ.filter fun x => (k - C x).val ≤ 0 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [mem_filter, mem_univ, true_and, hC] <;> omega
  have := card_le_card this
  rw [card_pair hab] at this
  unfold win at hw; omega

/-- Moving up by one rank decreases the distance to the barrier by one. -/
lemma val_sub_succ {k i : Fin n} (h : (k - i).val ≠ 0) : (k - (i + 1)).val = (k - i).val - 1 := by
  have hn : 1 < n := by
    by_contra hn
    have := (k - i).isLt; omega
  have h1 : ((1 : Fin n)).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt hn]
  have : k - (i + 1) = (k - i) - 1 := by abel
  rw [this, Fin.sub_val_of_le (by rw [Fin.le_def, h1]; omega), h1]

/-- **Lemma 2.3.** A barrier remains a barrier after any interaction. -/
theorem IsBarrier.step {C C' : Config A (Fin n)} {k : Fin n} (hk : IsBarrier C k)
    (h : (silentSSR n).Step C C') : IsBarrier C' k := by
  obtain ⟨a, b, hab, rfl⟩ := h
  rw [interact_eq C a b hab]
  split_ifs with hC
  swap; · exact hk
  have hx := hk.collision_ne hab hC
  set x := (k - C b).val with hxdef
  have hxn : x < n := (k - C b).isLt
  rw [isBarrier_iff] at hk ⊢
  intro r hr
  -- the new window is contained in the old one plus `b`
  have hsub : univ.filter (fun y => (k - Function.update C b (C b + 1) y).val ≤ r) ⊆
      insert b (univ.filter fun y => (k - C y).val ≤ r) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    by_cases hyb : y = b
    · subst hyb; simp
    · rw [Function.update_of_ne hyb] at hy; simp [hy]
  by_cases hrx : r + 1 = x
  · -- the only critical window: `r = x - 1`
    have hbig : insert a (insert b (univ.filter fun y => (k - C y).val ≤ r)) ⊆
        univ.filter fun y => (k - C y).val ≤ x := by
      intro y hy
      simp only [mem_insert, mem_filter, mem_univ, true_and] at hy
      simp only [mem_filter, mem_univ, true_and]
      rcases hy with rfl | rfl | hy
      · rw [hC]
      · exact le_rfl
      · omega
    have hbnot : b ∉ univ.filter fun y => (k - C y).val ≤ r := by simp; omega
    have hanot : a ∉ insert b (univ.filter fun y => (k - C y).val ≤ r) := by
      simp only [mem_insert, mem_filter, mem_univ, true_and, not_or]
      exact ⟨hab, by rw [hC]; omega⟩
    have h1 := card_le_card hbig
    rw [card_insert_of_notMem hanot, card_insert_of_notMem hbnot] at h1
    have h2 := hk x hxn
    have h3 := card_le_card hsub
    unfold win at h2 ⊢
    have := card_insert_le b (univ.filter fun y => (k - C y).val ≤ r)
    omega
  · have hsub' : univ.filter (fun y => (k - Function.update C b (C b + 1) y).val ≤ r) ⊆
        univ.filter fun y => (k - C y).val ≤ r := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      by_cases hyb : y = b
      · subst hyb
        rw [Function.update_self, val_sub_succ hx] at hy
        omega
      · rwa [Function.update_of_ne hyb] at hy
    exact (card_le_card hsub').trans (hk r hr)

lemma IsBarrier.reachable {C C' : Config A (Fin n)} {k : Fin n} (hk : IsBarrier C k)
    (h : (silentSSR n).Reachable C C') : IsBarrier C' k := by
  induction h with
  | refl => exact hk
  | tail _ hst ih => exact ih.step hst

/-- A non-null interaction decreases the potential by exactly one. -/
lemma potential_step {C : Config A (Fin n)} {k : Fin n} (hk : IsBarrier C k) {a b : A}
    (hab : a ≠ b) (hC : C a = C b) :
    pot (Function.update C b (C b + 1)) k + 1 = pot C k := by
  have hx := hk.collision_ne hab hC
  unfold pot
  rw [← add_sum_erase _ _ (mem_univ b), ← add_sum_erase _ _ (mem_univ b)]
  have : ∑ x ∈ univ.erase b, (k - Function.update C b (C b + 1) x).val =
      ∑ x ∈ univ.erase b, (k - C x).val :=
    sum_congr rfl fun x hx => by rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [this, Function.update_self, val_sub_succ hx]
  omega

lemma pot_le (C : Config A (Fin n)) (k : Fin n) : pot C k ≤ Fintype.card A * (n - 1) := by
  unfold pot
  calc ∑ a, (k - C a).val ≤ ∑ _a : A, (n - 1) :=
        sum_le_sum fun a _ => by have := (k - C a).isLt; omega
    _ = Fintype.card A * (n - 1) := by simp

/-- A configuration with pairwise distinct ranks is silent. -/
lemma interact_of_injective {C : Config A (Fin n)} (hC : Function.Injective C) {a b : A}
    (hab : a ≠ b) : (silentSSR n).interact C a b = C := by
  rw [interact_eq C a b hab, ite_eq_right (fun h => hab (hC h))]

lemma silent_of_injective {C : Config A (Fin n)} (hC : Function.Injective C) :
    (NProtocol.ofProtocol (silentSSR n)).Silent C := by
  intro a b hab o ho
  simp only [NProtocol.ofProtocol, Protocol.toN_δ, silentSSR, Set.mem_singleton_iff] at ho
  rw [ho, ite_eq_right (fun h => hab (hC h))]

lemma bijective_of_injective (hA : Fintype.card A = n) {C : Config A (Fin n)}
    (hC : Function.Injective C) : Function.Bijective C :=
  (Fintype.bijective_iff_injective_and_card C).mpr ⟨hC, by simp [hA]⟩

/-- From every configuration, a silent, correctly ranked configuration is reachable (by resolving
collisions one at a time). -/
theorem reachable_ranked (hA : Fintype.card A = n) (C : Config A (Fin n)) :
    ∃ D, (silentSSR n).Reachable C D ∧ Function.Bijective D := by
  obtain ⟨k, hk⟩ := exists_barrier hA C
  suffices ∀ m, ∀ C : Config A (Fin n), IsBarrier C k → pot C k = m →
      ∃ D, (silentSSR n).Reachable C D ∧ Function.Bijective D from this _ C hk rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hk hm
    by_cases hinj : Function.Injective C
    · exact ⟨C, Relation.ReflTransGen.refl, bijective_of_injective hA hinj⟩
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨a, b, hC, hab⟩ := hinj
      have hst : (silentSSR n).Step C (Function.update C b (C b + 1)) :=
        ⟨a, b, hab, by rw [interact_eq C a b hab, ite_eq_left hC]⟩
      have hpot := potential_step hk hab hC
      obtain ⟨D, hD, hDb⟩ := ih _ (by omega) _ (hk.step hst) rfl
      exact ⟨D, Relation.ReflTransGen.head hst hD, hDb⟩

/-- **Theorem 2.4 (correctness).** `Silent-n-state-SSR` solves self-stabilizing ranking. -/
theorem solvesSSR (hA : Fintype.card A = n) :
    (NProtocol.ofProtocol (silentSSR n)).SolvesSSR (A := A) (id : Fin n → Fin n) := by
  intro C
  obtain ⟨D, hD, hDb⟩ := reachable_ranked hA C
  refine ⟨D, (NProtocol.ofProtocol_reachable_iff _ _ _).mpr hD, ?_⟩
  exact (silent_of_injective hDb.1).stablyIn hDb

/-- **Theorem 2.4 (correctness), leader election.** With `leader ↔ rank = 0`,
`Silent-n-state-SSR` solves self-stabilizing leader election. -/
theorem solvesSSLE (hA : Fintype.card A = n) :
    (NProtocol.ofProtocol (silentSSR n)).SolvesSSLE (A := A) (fun i => decide (i = 0)) := by
  intro C
  obtain ⟨D, hD, hDb⟩ := reachable_ranked hA C
  refine ⟨D, (NProtocol.ofProtocol_reachable_iff _ _ _).mpr hD,
    (silent_of_injective hDb.1).stablyIn ?_⟩
  obtain ⟨a, ha⟩ := hDb.2 0
  show NProtocol.LeaderCorrect _ D
  unfold NProtocol.LeaderCorrect NProtocol.numLeaders
  rw [card_eq_one]
  refine ⟨a, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, mem_singleton]
  exact ⟨fun hx => hDb.1 (hx.trans ha.symm), fun hx => hx ▸ ha⟩

/-! ### Executions under arbitrary and weakly fair schedulers -/

/-- In **every** execution (under any scheduler), at most `n (n - 1)` interactions change the
configuration. -/
theorem card_changes_le (hA : Fintype.card A = n) (E : (silentSSR n).Execution A) (T : ℕ) :
    ((range T).filter fun t => E.config (t + 1) ≠ E.config t).card ≤ n * (n - 1) := by
  obtain ⟨k, hk⟩ := exists_barrier hA (E.config 0)
  have hkt : ∀ t, IsBarrier (E.config t) k := fun t => hk.reachable (E.reachable_of_le (Nat.zero_le t))
  -- potential plus number of changes is constant
  have key : ∀ T, pot (E.config T) k +
      ((range T).filter fun t => E.config (t + 1) ≠ E.config t).card = pot (E.config 0) k := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [range_add_one, filter_insert]
      have hstep := E.step T
      rw [interact_eq _ _ _ (E.sched_ne T)] at hstep
      by_cases hC : E.config T (E.sched T).1 = E.config T (E.sched T).2
      · rw [ite_eq_left hC] at hstep
        have hp := potential_step (hkt T) (E.sched_ne T) hC
        rw [← hstep] at hp
        have hne : E.config (T + 1) ≠ E.config T := fun h => by rw [h] at hp; omega
        rw [ite_eq_left hne, card_insert_of_notMem (by simp)]
        omega
      · rw [ite_eq_right hC] at hstep
        rw [ite_eq_right (not_not.mpr hstep), hstep]
        exact ih
  have := key T
  have := pot_le (E.config 0) k
  rw [hA] at this
  omega

/-- **Theorem 2.4 (correctness), weakly fair scheduler.** Every weakly fair execution of
`Silent-n-state-SSR` eventually becomes constant (silent) in a correctly ranked configuration. -/
theorem weaklyFair_eventually_ranked (hA : Fintype.card A = n) (E : (silentSSR n).Execution A)
    (hE : E.WeaklyFair) :
    ∃ T, (∀ t ≥ T, E.config t = E.config T) ∧ Function.Bijective (E.config T) := by
  -- the set of change times is bounded
  have hfin : ∃ T, ∀ t ≥ T, E.config (t + 1) = E.config t := by
    by_contra hcon
    push Not at hcon
    -- build `n (n - 1) + 1` change times
    have : ∀ m, ∃ T, m ≤ ((range T).filter fun t => E.config (t + 1) ≠ E.config t).card := by
      intro m
      induction m with
      | zero => exact ⟨0, by simp⟩
      | succ m ih =>
        obtain ⟨T, hT⟩ := ih
        obtain ⟨t, ht, hne⟩ := hcon T
        refine ⟨t + 1, le_trans (Nat.succ_le_succ hT) ?_⟩
        rw [range_add_one, filter_insert, ite_eq_left hne, card_insert_of_notMem (by simp)]
        exact Nat.succ_le_succ (card_le_card (filter_subset_filter _ (range_subset_range.mpr ht)))
    obtain ⟨T, hT⟩ := this (n * (n - 1) + 1)
    have := card_changes_le hA E T
    omega
  obtain ⟨T, hT⟩ := hfin
  have hconst : ∀ t ≥ T, E.config t = E.config T := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hT t ht, ih]
  refine ⟨T, hconst, bijective_of_injective hA ?_⟩
  intro a b hab
  by_contra hne
  have hn : 1 < n := by
    have : 2 ≤ Fintype.card A := by
      rw [← card_pair hne]; exact card_le_univ _
    omega
  obtain ⟨t, ht, hs⟩ := hE a b hne T
  have hstep := E.step t
  rw [hconst (t + 1) (by omega), hconst t ht] at hstep
  rcases hs with hs | hs <;> rw [hs] at hstep <;> simp only at hstep
  · rw [interact_eq _ _ _ hne, ite_eq_left hab] at hstep
    have := congrFun hstep b
    simp only [Function.update_self] at this
    exact Fin.add_one_ne_self hn.ne' _ this.symm
  · rw [interact_eq _ _ _ (Ne.symm hne), ite_eq_left hab.symm] at hstep
    have := congrFun hstep a
    simp only [Function.update_self] at this
    exact Fin.add_one_ne_self hn.ne' _ this.symm

end TimeOptimalSSLE.SilentSSR
