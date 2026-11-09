import Papers.PODC2014.GracefulKSetAgreement.Model

/-!
# Set agreement under `Σ_{n−1}-MAJ` (Section 7.1, Algorithm 3, Theorem 10)

Algorithm 3 of the paper, for `n` processes `Fin n` (the algorithm knows `n`). Process `p_i` keeps
a proposal `v_i` (initially its input `x_i`) and a decision `y_i` (initially `⊥ = none`); both are
broadcast every round. In round `r`, with `N` the set of *other* processes heard:

```
5:  v_i := max {v_i, v_j : j ∈ N}
6:  if ∃ j ∈ N : y_j ≠ ⊥ ∧ y_i = ⊥ then
7:     y_i := y_j
8:  if N = ∅ ∧ y_i = ⊥ then
9:     y_i := v_i
10: if r = n ∧ y_i = ⊥ then
11:    y_i := v_i ; terminate
```

In the full-information model of `Model.lean` the received states are the senders' states at the
beginning of the round. The state carries the number `r` of completed rounds (the paper's round
number is `r + 1`). When several heard processes have decided, line 7 adopts the decision of a
fixed (choice-function-selected) one of them: the paper says "some `p_j`", and the proof works
for any choice. After round `n` the processes keep running, but their decisions are frozen
(`terminate`).

## Main results

* `alg3_decided_at_n`: every process has decided at time `n` (after `n` rounds), for every
  communication pattern.
* `theorem10`: Algorithm 3 solves `(n − 1)`-set agreement under `SigmaMaj` (Definition 16), for
  every `n` (for `n ≤ 1` the adversary `SigmaMaj` is empty, since it asks for two distinct
  processes) and every linearly ordered value set `V` (`Inhabited` only to fill the unreachable
  branch of the transition function).
* `complete_mem_sigmaMaj`: non-vacuity for `n ≥ 2`.

The proof follows the paper's induction, organised as follows. If `n` different values are
decided, the decision map `D` is injective (hence a permutation of the inputs, which are then
distinct), and no process ever adopts a decision (it would duplicate one). By strong induction on
the rank of the input, every process `p` decides its own input `x_p`, in the round where it
first decides, which is at most its rank; hence that round is one in which `p` is deaf (Line 9;
for the maximal input, Line 11 can only fire in a deaf round as well). These `n` singleton root
components, applied to Definition 16, yield a causal chain from one deciding process (after its
decision) to another one (before its decision); decisions propagate along causal chains, a
contradiction.
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

/-- The local state of Algorithm 3: the number `r` of completed rounds, the proposal `v`, and the
decision `y` (`none = ⊥`). -/
structure SAState (V : Type) where
  /-- Number of completed rounds. -/
  r : ℕ
  /-- Proposal value. -/
  v : V
  /-- Decision value (`none` = undecided). -/
  y : Option V

namespace SetAgreement

variable {n : ℕ} {V : Type} [LinearOrder V]

/-- Line 5: the maximum of the own proposal and the received proposals. -/
noncomputable def newV (i : Fin n) (s : SAState V) (m : Fin n → Option (SAState V)) : V :=
  Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ fun j => ((m j).map SAState.v).getD s.v

open Classical in
/-- Line 7: the decision of some heard process `j ≠ i` that has decided (if any). -/
noncomputable def adopt (i : Fin n) (m : Fin n → Option (SAState V)) : Option V :=
  if h : ∃ j, j ≠ i ∧ (m j).bind SAState.y ≠ none then (m (Classical.choose h)).bind SAState.y
  else none

open Classical in
/-- One round of Algorithm 3 (lines 5–11) of process `i` in state `s`, receiving `m`. -/
noncomputable def upd (i : Fin n) (s : SAState V) (m : Fin n → Option (SAState V)) :
    SAState V :=
  let v' := newV i s m                                                      -- line 5
  let y₁ := if s.y = none then adopt i m else s.y                           -- lines 6–7
  let y₂ := if (∀ j, j ≠ i → m j = none) ∧ y₁ = none then some v' else y₁   -- lines 8–9
  let y₃ := if s.r + 1 = n ∧ y₂ = none then some v' else y₂                 -- lines 10–11
  ⟨s.r + 1, v', y₃⟩

section upd

variable {i : Fin n} {s : SAState V} {m : Fin n → Option (SAState V)}

theorem newV_ge_self (hm : m i = some s) : s.v ≤ newV i s m := by
  have := Finset.le_sup' (fun j => ((m j).map SAState.v).getD s.v) (Finset.mem_univ i)
  simpa [newV, hm] using this

theorem le_newV {j : Fin n} {s' : SAState V} (hj : m j = some s') : s'.v ≤ newV i s m := by
  have := Finset.le_sup' (fun j => ((m j).map SAState.v).getD s.v) (Finset.mem_univ j)
  simpa [newV, hj] using this

theorem newV_mem : newV i s m = s.v ∨ ∃ j s', m j = some s' ∧ newV i s m = s'.v := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) ⟨i, Finset.mem_univ i⟩
    (fun j => ((m j).map SAState.v).getD s.v)
  rw [newV, hj]
  cases h : m j with
  | none => left; simp
  | some s' => right; exact ⟨j, s', h, by simp⟩

omit [LinearOrder V] in
theorem adopt_some {w : V} (h : adopt i m = some w) :
    ∃ j, j ≠ i ∧ (m j).bind SAState.y = some w := by
  unfold adopt at h
  split_ifs at h with hh
  · exact ⟨_, (Classical.choose_spec hh).1, h⟩

omit [LinearOrder V] in
theorem adopt_ne_none (h : ∃ j, j ≠ i ∧ (m j).bind SAState.y ≠ none) : adopt i m ≠ none := by
  unfold adopt
  split_ifs
  exact (Classical.choose_spec h).2

theorem upd_r : (upd i s m).r = s.r + 1 := rfl

theorem upd_v : (upd i s m).v = newV i s m := rfl

theorem upd_y_of_some {w : V} (h : s.y = some w) : (upd i s m).y = some w := by
  simp [upd, h]

theorem upd_y_adopt (h : s.y = none) (hj : ∃ j, j ≠ i ∧ (m j).bind SAState.y ≠ none) :
    ∃ j, j ≠ i ∧ (m j).bind SAState.y ≠ none ∧ (upd i s m).y = (m j).bind SAState.y := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (adopt_ne_none hj)
  obtain ⟨j, hji, hjw⟩ := adopt_some hw
  refine ⟨j, hji, by simp [hjw], ?_⟩
  simp [upd, h, hw, hjw]

theorem upd_y_own (h : s.y = none) (hno : ∀ j, j ≠ i → (m j).bind SAState.y = none)
    (hd : (upd i s m).y ≠ none) :
    (upd i s m).y = some (newV i s m) ∧ ((∀ j, j ≠ i → m j = none) ∨ s.r + 1 = n) := by
  have ha : adopt i m = none := by
    by_contra hne
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨j, hji, hjw⟩ := adopt_some hw
    rw [hno j hji] at hjw
    exact absurd hjw (by simp)
  simp only [upd, h, ha, ite_true] at hd ⊢
  split_ifs at hd ⊢ with h1 h2 <;> simp_all

theorem upd_y_deaf (hno : ∀ j, j ≠ i → m j = none) : (upd i s m).y ≠ none := by
  cases h : s.y with
  | some w => simp [upd_y_of_some h]
  | none =>
    simp only [upd, h, ite_true]
    split_ifs <;> simp_all

theorem upd_y_last (hr : s.r + 1 = n) : (upd i s m).y ≠ none := by
  simp only [upd]
  split_ifs <;> simp_all

theorem upd_y_cases {w : V} (h : (upd i s m).y = some w) :
    s.y = some w ∨ (∃ j, (m j).bind SAState.y = some w) ∨ w = newV i s m := by
  simp only [upd] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 <;>
    first
    | (left; simp_all; done)
    | (right; right; simp_all; done)
    | skip
  obtain ⟨j, -, hj⟩ := adopt_some h
  exact Or.inr (Or.inl ⟨j, hj⟩)

end upd

end SetAgreement

open SetAgreement

/-- **Algorithm 3** of the paper (set agreement), for the processes `Fin n`. The state of a
process is `⟨r, v, y⟩`; the decision is `y`. (The branch `m i = none` never occurs in runs: a
process always receives its own state.) -/
noncomputable def alg3 (n : ℕ) (V : Type) [LinearOrder V] [Inhabited V] :
    Alg (Fin n) V (SAState V) where
  init _ x := ⟨0, x, none⟩
  step i m := match m i with
    | some s => upd i s m
    | none => ⟨0, default, none⟩
  dec s := s.y
  dec_stable i m s w hs hw := by
    simp only [hs]
    exact upd_y_of_some hw

namespace SetAgreement

variable {n : ℕ} {V : Type} [LinearOrder V] [Inhabited V] (x : Fin n → V) (ρ : ℕ → Graph (Fin n))

omit [LinearOrder V] [Inhabited V] in
theorem msgs_self {σ : Type} (G : Graph (Fin n)) (C : Fin n → σ) (i : Fin n) :
    msgs G C i i = some (C i) := by
  simp [msgs, hears_self]

omit [LinearOrder V] [Inhabited V] in
open Classical in
theorem msgs_bind_y (G : Graph (Fin n)) (C : Fin n → SAState V) (i j : Fin n) :
    (msgs G C i j).bind SAState.y = if Hears G i j then (C j).y else none := by
  unfold msgs; split_ifs <;> rfl

theorem run_zero (i : Fin n) : (alg3 n V).run x ρ 0 i = ⟨0, x i, none⟩ := rfl

theorem run_succ (t : ℕ) (i : Fin n) :
    (alg3 n V).run x ρ (t + 1) i =
      upd i ((alg3 n V).run x ρ t i) (msgs (ρ t) ((alg3 n V).run x ρ t) i) := by
  show next (alg3 n V).step (ρ t) ((alg3 n V).run x ρ t) i = _
  simp [next, alg3, msgs_self]

theorem run_r (t : ℕ) (i : Fin n) : ((alg3 n V).run x ρ t i).r = t := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih => rw [run_succ, upd_r, ih]

theorem run_v_le {t : ℕ} {i j : Fin n} (hj : Hears (ρ t) i j) :
    ((alg3 n V).run x ρ t j).v ≤ ((alg3 n V).run x ρ (t + 1) i).v := by
  rw [run_succ, upd_v]
  exact le_newV (j := j) (s' := (alg3 n V).run x ρ t j) (by simp only [msgs, hj, ↓reduceIte])

theorem run_v_mono {t t' : ℕ} (i : Fin n) (h : t ≤ t') :
    ((alg3 n V).run x ρ t i).v ≤ ((alg3 n V).run x ρ t' i).v := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (run_v_le x ρ (hears_self _ i))

theorem run_x_le (t : ℕ) (i : Fin n) : x i ≤ ((alg3 n V).run x ρ t i).v :=
  (run_v_mono x ρ i (Nat.zero_le t))

theorem run_v_valid (t : ℕ) (i : Fin n) : ∃ j, ((alg3 n V).run x ρ t i).v = x j := by
  induction t generalizing i with
  | zero => exact ⟨i, rfl⟩
  | succ t ih =>
    rw [run_succ, upd_v]
    rcases newV_mem (i := i) (s := (alg3 n V).run x ρ t i)
        (m := msgs (ρ t) ((alg3 n V).run x ρ t) i) with h | ⟨j, s', hj, h⟩
    · rw [h]; exact ih i
    · rw [h]
      unfold msgs at hj
      split_ifs at hj
      cases hj
      exact ih j

theorem run_y_valid {t : ℕ} {i : Fin n} {w : V} (h : ((alg3 n V).run x ρ t i).y = some w) :
    ∃ j, x j = w := by
  induction t generalizing i w with
  | zero => simp [run_zero] at h
  | succ t ih =>
    rw [run_succ] at h
    rcases upd_y_cases h with h | ⟨j, hj⟩ | h
    · exact ih h
    · rw [msgs_bind_y] at hj
      split_ifs at hj
      exact ih hj
    · obtain ⟨j, hj⟩ := run_v_valid x ρ (t + 1) i
      rw [run_succ, upd_v] at hj
      exact ⟨j, (h.trans hj).symm⟩

theorem run_y_stable {t t' : ℕ} {i : Fin n} {w : V} (h : ((alg3 n V).run x ρ t i).y = some w)
    (htt : t ≤ t') : ((alg3 n V).run x ρ t' i).y = some w :=
  (alg3 n V).dec_conf_mono (C := (alg3 n V).initC x) h htt

theorem run_y_ne_none_mono {t t' : ℕ} {i : Fin n} (h : ((alg3 n V).run x ρ t i).y ≠ none)
    (htt : t ≤ t') : ((alg3 n V).run x ρ t' i).y ≠ none := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp h
  rw [run_y_stable x ρ hw htt]; simp

/-- Lines 6–7: an undecided process hearing a decided one adopts the decision of some decided
process it hears. -/
theorem run_adopt {t : ℕ} {i j : Fin n} (hi : ((alg3 n V).run x ρ t i).y = none) (hji : j ≠ i)
    (hj : ρ t j i) (hjd : ((alg3 n V).run x ρ t j).y ≠ none) :
    ∃ j', j' ≠ i ∧ ((alg3 n V).run x ρ t j').y ≠ none ∧
      ((alg3 n V).run x ρ (t + 1) i).y = ((alg3 n V).run x ρ t j').y := by
  have hH : ∀ j', j' ≠ i → (Hears (ρ t) i j' ↔ ρ t j' i) := fun j' hj' =>
    ⟨fun h => h.resolve_left hj', Or.inr⟩
  obtain ⟨j', hj'i, hj'd, hy⟩ := upd_y_adopt (m := msgs (ρ t) ((alg3 n V).run x ρ t) i) hi
    ⟨j, hji, by rw [msgs_bind_y]; simp only [(hH j hji).2 hj, ↓reduceIte]; exact hjd⟩
  rw [msgs_bind_y] at hj'd hy
  split_ifs at hj'd hy
  · exact ⟨j', hj'i, hj'd, by rw [run_succ]; exact hy⟩
  · exact absurd rfl hj'd

/-- Hearing a decided process makes a process decided. -/
theorem run_hear_decided {t : ℕ} {i j : Fin n} (hj : Hears (ρ t) i j)
    (hjd : ((alg3 n V).run x ρ t j).y ≠ none) : ((alg3 n V).run x ρ (t + 1) i).y ≠ none := by
  rcases hj with rfl | hj
  · exact run_y_ne_none_mono x ρ hjd (Nat.le_succ t)
  by_cases hji : j = i
  · subst hji; exact run_y_ne_none_mono x ρ hjd (Nat.le_succ t)
  cases hi : ((alg3 n V).run x ρ t i).y with
  | some w => rw [run_succ, upd_y_of_some hi]; simp
  | none =>
    obtain ⟨j', -, hj'd, hy⟩ := run_adopt x ρ hi hji hj hjd
    rw [hy]; exact hj'd

/-- Lines 8–9: a deaf process decides. -/
theorem run_deaf {t : ℕ} {i : Fin n} (hd : Deaf (ρ t) i) :
    ((alg3 n V).run x ρ (t + 1) i).y ≠ none := by
  rw [run_succ]
  refine upd_y_deaf fun j hji => ?_
  simp only [msgs, ite_eq_right_iff]
  intro h
  exact absurd (hd.eq h) hji

/-- A process that becomes decided without hearing a decided process decides its (new)
proposal, and it is deaf in that round or it is round `n`. -/
theorem run_own {t : ℕ} {i : Fin n} (hi : ((alg3 n V).run x ρ t i).y = none)
    (hno : ∀ j, j ≠ i → ρ t j i → ((alg3 n V).run x ρ t j).y = none)
    (hd : ((alg3 n V).run x ρ (t + 1) i).y ≠ none) :
    ((alg3 n V).run x ρ (t + 1) i).y = some ((alg3 n V).run x ρ (t + 1) i).v ∧
      (Deaf (ρ t) i ∨ t + 1 = n) := by
  rw [run_succ] at hd ⊢
  obtain ⟨h1, h2⟩ := upd_y_own hi (fun j hji => by
    rw [msgs_bind_y]; split_ifs with h
    · exact hno j hji (h.resolve_left hji)
    · rfl) hd
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | h2
  · left
    intro j hj
    by_contra hji
    have := h2 j hji
    simp only [msgs, ite_eq_right_iff, reduceCtorEq, imp_false] at this
    exact this (Or.inr hj)
  · right; rw [run_r] at h2; exact h2

end SetAgreement

open SetAgreement

/-- **Termination of Algorithm 3**: after `n` rounds every process has decided, for every input
vector and every communication pattern (Line 10–11). -/
theorem alg3_decided_at_n {n : ℕ} {V : Type} [LinearOrder V] [Inhabited V] (x : Fin n → V)
    (ρ : ℕ → Graph (Fin n)) (i : Fin n) :
    ∃ v, (alg3 n V).dec ((alg3 n V).run x ρ n i) = some v := by
  obtain ⟨t, ht⟩ : ∃ t, n = t + 1 := ⟨n - 1, by have := i.pos; omega⟩
  suffices h : ((alg3 n V).run x ρ n i).y ≠ none from Option.ne_none_iff_exists'.mp h
  cases h : ((alg3 n V).run x ρ t i).y with
  | some w => exact run_y_ne_none_mono x ρ (t := t) (by simp [h]) (by omega)
  | none =>
    have := upd_y_last (i := i) (s := (alg3 n V).run x ρ t i)
      (m := msgs (ρ t) ((alg3 n V).run x ρ t) i) (by rw [run_r]; exact ht.symm)
    rwa [← run_succ, ← ht] at this

namespace SetAgreement

variable {n : ℕ} {V : Type} [LinearOrder V] [Inhabited V] (x : Fin n → V) (ρ : ℕ → Graph (Fin n))

/-- Decisions propagate along causal chains (Lines 6–7). -/
theorem run_journey {s t : ℕ} {a b : Fin n} (hJ : Journey ρ s a t b)
    (ha : ((alg3 n V).run x ρ s a).y ≠ none) : ((alg3 n V).run x ρ t b).y ≠ none := by
  induction hJ with
  | refl => exact ha
  | step _ hyz ih => exact run_hear_decided x ρ hyz ih

/-- The core of Theorem 10: under `Σ_{n−1}-MAJ`, the decisions (made by time `n`) are not
pairwise distinct. -/
theorem not_injective_decisions (hρ : ρ ∈ SigmaMaj) (D : Fin n → V)
    (hD : ∀ i, ((alg3 n V).run x ρ n i).y = some (D i)) : ¬ Function.Injective D := by
  classical
  intro hinj
  -- shorthand
  set C := (alg3 n V).run x ρ with hC
  have hDw : ∀ t i w, (C t i).y = some w → D i = w := by
    intro t i w h
    have h1 := run_y_stable x ρ h (le_max_left t n)
    have h2 := run_y_stable x ρ (hD i) (le_max_right t n)
    rw [h1] at h2
    exact (Option.some_injective _ h2).symm
  -- first decision times
  have hex : ∀ i, ∃ t, (C t i).y ≠ none := fun i => ⟨n, by rw [hD i]; simp⟩
  let k : Fin n → ℕ := fun i => Nat.find (hex i)
  have hk_le : ∀ i, k i ≤ n := fun i => Nat.find_min' _ (by rw [hD i]; simp)
  have hk_und : ∀ i t, t < k i → (C t i).y = none := fun i t ht => by
    have := Nat.find_min (hex i) ht
    simpa using this
  have hk_dec : ∀ i, (C (k i) i).y = some (D i) := fun i => by
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (Nat.find_spec (hex i))
    rw [hw, hDw _ _ _ hw]
  have hk_pos : ∀ i, 0 < k i := fun i => by
    by_contra h
    have h0 : k i = 0 := by omega
    have := hk_dec i
    rw [h0] at this
    simp [hC, run_zero] at this
  have hdec_of_le : ∀ i t, k i ≤ t → (C t i).y ≠ none := fun i t ht =>
    run_y_ne_none_mono x ρ (by rw [hk_dec i]; simp) ht
  -- no adoption: the deciding round of every process
  have hOD : ∀ p, (∀ j, j ≠ p → ρ (k p - 1) j p → (C (k p - 1) j).y = none) ∧
      D p = (C (k p) p).v ∧ (Deaf (ρ (k p - 1)) p ∨ k p = n) := by
    intro p
    obtain ⟨t, ht⟩ : ∃ t, k p = t + 1 := ⟨k p - 1, by have := hk_pos p; omega⟩
    rw [ht, Nat.add_sub_cancel]
    have hu : (C t p).y = none := hk_und p t (by omega)
    have hd : (C (t + 1) p).y = some (D p) := ht ▸ hk_dec p
    have hno : ∀ j, j ≠ p → ρ t j p → (C t j).y = none := by
      intro j hjp hj
      by_contra hjd
      obtain ⟨j', hj'p, -, hy⟩ := run_adopt x ρ hu hjp hj hjd
      rw [hd] at hy
      exact hj'p (hinj (hDw _ _ _ hy.symm))
    refine ⟨hno, ?_⟩
    obtain ⟨h1, h2⟩ := run_own x ρ hu hno (by rw [hd]; simp)
    rw [hd] at h1
    exact ⟨Option.some_injective _ h1, h2⟩
  have hDv : ∀ p, D p = (C (k p) p).v := fun p => (hOD p).2.1
  have hDx : ∀ i, x i ≤ D i := fun i => (hDv i) ▸ run_x_le x ρ _ i
  -- the decisions are a permutation of the inputs, and the inputs are distinct
  have hsub : Finset.univ.image D ⊆ Finset.univ.image x := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j, hj⟩ := run_y_valid x ρ (hD i)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hcardD : (Finset.univ.image D).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcardx : (Finset.univ.image x).card ≤ n :=
    Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
  have heq : Finset.univ.image D = Finset.univ.image x :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hxinj : Function.Injective x := by
    have : (Finset.univ.image x).card = (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]; rw [← heq]; exact hcardD
    have := Finset.card_image_iff.mp this
    exact fun a b hab => this (by simp) (by simp) hab
  have hsurj : ∀ p, ∃ d, D d = x p := fun p => by
    have : x p ∈ Finset.univ.image D := heq ▸ Finset.mem_image_of_mem x (Finset.mem_univ p)
    obtain ⟨d, -, hd⟩ := Finset.mem_image.mp this
    exact ⟨d, hd⟩
  -- ranks
  let ℓ : Fin n → ℕ := fun p => (Finset.univ.filter fun q => x q < x p).card
  have hℓlt : ∀ p q, x q < x p → ℓ q < ℓ p := by
    intro p q hqp
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (fun r hr => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢; exact hr.trans hqp)]
    exact ⟨q, by simpa using hqp, by simp⟩
  have hℓn : ∀ p, ℓ p < n := by
    intro p
    have : (Finset.univ.filter fun q => x q < x p) ⊂ Finset.univ :=
      Finset.filter_ssubset.mpr ⟨p, Finset.mem_univ _, lt_irrefl _⟩
    simpa using Finset.card_lt_card this
  -- the induction of the paper
  have claim : ∀ m p, ℓ p = m → D p = x p ∧ k p ≤ ℓ p + 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro p hp
    have ih' : ∀ q, x q < x p → D q = x q ∧ k q ≤ ℓ q + 1 :=
      fun q hq => ih (ℓ q) (hp ▸ hℓlt p q hq) q rfl
    have hDp : D p = x p := by
      obtain ⟨d, hd⟩ := hsurj p
      rcases ((hDx d).trans_eq hd).lt_or_eq with h | h
      · exact absurd ((ih' d h).1.symm.trans hd) h.ne
      · rw [hxinj h] at hd; exact hd
    refine ⟨hDp, ?_⟩
    by_contra hk
    set t := ℓ p
    have hu1 : (C (t + 1) p).y = none := hk_und p _ (by omega)
    refine run_deaf x ρ (t := t) (i := p) (fun j hj => ?_) hu1
    by_contra hjp
    rcases lt_trichotomy (x j) (x p) with h | h | h
    · have := (ih' j h).2
      have := hℓlt p j h
      exact run_hear_decided x ρ (Or.inr hj) (hdec_of_le j t (by omega)) hu1
    · exact hjp (hxinj h)
    · have h1 := run_x_le x ρ t j
      have h2 := run_v_le x ρ (t := t) (Or.inr hj : Hears (ρ t) p j)
      have h3 := run_v_mono x ρ p (show t + 1 ≤ k p by omega)
      have h4 := hDv p
      exact absurd (h.trans_le (h1.trans (h2.trans (h3.trans (h4.symm.trans hDp).le))))
        (lt_irrefl _)
  -- every process decides in a round in which it is deaf
  have hdeaf : ∀ p, Deaf (ρ (k p - 1)) p := by
    intro p
    rcases (hOD p).2.2 with h | hkn
    · exact h
    intro j hj
    by_contra hjp
    have hju := (hOD p).1 j hjp hj
    have hkp := hk_pos p
    rcases lt_trichotomy (x j) (x p) with h | h | h
    · have := (claim _ j rfl).2
      have := hℓlt p j h
      have := hℓn p
      exact hdec_of_le j (k p - 1) (by omega) hju
    · exact hjp (hxinj h)
    · have h1 := run_x_le x ρ (k p - 1) j
      have h2 := run_v_le x ρ (t := k p - 1) (Or.inr hj : Hears (ρ (k p - 1)) p j)
      rw [Nat.sub_add_cancel hkp] at h2
      have h4 := (hDv p).symm.trans (claim _ p rfl).1
      exact absurd (h.trans_le (h1.trans (h2.trans h4.le))) (lt_irrefl _)
  -- Definition 16 applied to the `n` singleton root components
  obtain ⟨i, j, -, hJ⟩ := hρ (fun i => k i - 1) (fun i => k i - 1) (fun _ => le_rfl)
    (fun i t h1 h2 => by
      obtain rfl : t = k i - 1 := by omega
      exact isRootComp_singleton_iff.mpr (hdeaf i))
  have hi : (C (k i - 1 + 1) i).y ≠ none := by
    rw [Nat.sub_add_cancel (hk_pos i), hk_dec i]; simp
  exact run_journey x ρ hJ hi (hk_und j _ (by have := hk_pos j; omega))

end SetAgreement

/-- **Theorem 10** of [paper]: Algorithm 3 solves `(n − 1)`-set agreement under the message
adversary `Σ_{n−1}-MAJ` (Definition 16). -/
theorem theorem10 {n : ℕ} {V : Type} [LinearOrder V] [Inhabited V] :
    (alg3 n V).SolvesKSet (n - 1) SigmaMaj := by
  classical
  intro x ρ hρ
  choose D hD using alg3_decided_at_n x ρ
  have hDdec : ∀ i w, (alg3 n V).Decides x ρ i w → D i = w := fun i w hw =>
    Alg.Decides.unique (alg3 n V) ⟨n, hD i⟩ hw
  refine ⟨fun S hS => ?_, fun i w ⟨t, ht⟩ => run_y_valid x ρ ht, fun i => ⟨D i, n, hD i⟩⟩
  by_contra hlt
  rw [not_le] at hlt
  have hsub : S ⊆ Finset.univ.image D := fun w hw => by
    obtain ⟨i, hi⟩ := hS w hw
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hDdec i w hi⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.image D).card ≤ n :=
    Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
  have h3 : (Finset.univ.image D).card = (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  have := Finset.card_image_iff.mp h3
  exact not_injective_decisions x ρ hρ D hD fun a b hab => this (by simp) (by simp) hab

/-- Non-vacuity: for `n ≥ 2`, the pattern in which every process always hears every other process
belongs to `Σ_{n−1}-MAJ` (there are no singleton root components at all). -/
theorem complete_mem_sigmaMaj {n : ℕ} (hn : 2 ≤ n) :
    (fun _ (a b : Fin n) => a ≠ b) ∈ (SigmaMaj : Set (ℕ → Graph (Fin n))) := by
  intro a b hab h
  have h0 := isRootComp_singleton_iff.mp (h ⟨0, by omega⟩ _ le_rfl (hab _))
  exact absurd (h0 ⟨1, by omega⟩ (by simp [Fin.ext_iff])) (by simp [Fin.ext_iff])

end Podc.GracefulKSetAgreement
