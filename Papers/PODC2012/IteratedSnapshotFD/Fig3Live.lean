import Papers.PODC2012.IteratedSnapshotFD.Fig3
import Papers.PODC2012.IteratedSnapshotFD.SimulationCores

/-!
# Theorems 2 and 3: the simulation of Figure 3 with `Ω_k` and with `◇P`

We use the operational semantics of `Fig3.lean` (atomic collect and write-snapshot steps).
Crashes: a simulator is *correct* (`SCorrect`) iff it takes infinitely many steps; a crashed
simulator simply stops being scheduled.

* `simSchedule`: the IIS schedule simulated by a run (participants of round `k` = simulators that
  complete the paper's round `k + 1`; views = the views returned by `arw_write_snapshot`).
* Theorem 2 (`Ω_k`, predicate `propOmega`): `theorem2_live` (every correct simulator simulates
  every round), `theorem2_correct_iff` (correct simulated processes = correct simulators),
  `theorem2_omegaStar` (the simulated failure detector is in `Ω*_k`).
* Theorem 3 (`◇P`, predicate `propDP`): `theorem3_live`, `theorem3_SC` (every correct simulated
  process is strongly correct), `theorem3_diamondPStar`.
-/

set_option linter.unusedSectionVars false

namespace Podc.IteratedSnapshotFD.Fig3

variable {n : ℕ} [NeZero n]

/-- The predicate `PROP_{Ω_k}` of Section 4.2. -/
def propOmega (arwView fdVal : Finset (Fin n)) (i : Fin n) : Prop :=
  ∃ l ∈ fdVal, l = i ∨ l ∈ arwView

instance (a b : Finset (Fin n)) (i : Fin n) : Decidable (propOmega a b i) := by
  unfold propOmega; infer_instance

/-- A simulator is correct iff it takes infinitely many steps. -/
def SCorrect (sched : ℕ → Fin n) (i : Fin n) : Prop := ∀ T, ∃ t ≥ T, sched t = i

/-- `H` is an `Ω_k` history: after some time every simulator outputs the same set `L`, which
contains a correct simulator. (The constraint `|L| = k` is not needed.) -/
def IsOmegaK (sched : ℕ → Fin n) (H : Fin n → ℕ → Finset (Fin n)) : Prop :=
  ∃ L : Finset (Fin n), (∃ a ∈ L, SCorrect sched a) ∧ ∃ T, ∀ t ≥ T, ∀ i, H i t = L

/-- `H` is a `◇P` history (trusted sets): after some time every simulator trusts exactly the
correct simulators. -/
def IsDiamondP (sched : ℕ → Fin n) (H : Fin n → ℕ → Finset (Fin n)) : Prop :=
  ∃ T, ∀ t ≥ T, ∀ i j, j ∈ H i t ↔ SCorrect sched j

section
variable (prop : Finset (Fin n) → Finset (Fin n) → Fin n → Prop) [∀ a b i, Decidable (prop a b i)]
  (H : Fin n → ℕ → Finset (Fin n)) (sched : ℕ → Fin n)

/-- Simulator `i` has completed the simulation of round `r` at some time. -/
def Done (r : ℕ) (i : Fin n) : Prop := ∃ t, r < ((run prop H sched t).loc i).rnd

open Classical in
/-- The view returned to `q_i` in round `r` (`∅` if never returned). -/
noncomputable def limView (r : ℕ) (i : Fin n) : Finset (Fin n) :=
  if h : Done prop H sched r i then (run prop H sched (Nat.find h)).view r i else ∅

open Classical in
/-- The output of the simulated `C*` at `q_i` in round `r`. -/
noncomputable def limOut (r : ℕ) (i : Fin n) : Finset (Fin n) :=
  if h : Done prop H sched r i then (run prop H sched (Nat.find h)).out r i else ∅

/-! ### Step lemmas and the run invariant -/

section Aux
variable {prop} {H} {sched}

theorem step_start {t : ℕ} {c : Cfg n} {i : Fin n} (h : (c.loc i).pc = .start) :
    step prop H t c i = { c with loc := (Function.update c.loc i
      ⟨(c.loc i).rnd, if owner (c.loc i).rnd = i ∧ ¬ prop (c.S (c.loc i).rnd) (H i t) i
        then .start else .write, H i t⟩) } := by
  simp only [step, h]
  split_ifs <;> simp_all

theorem step_write {t : ℕ} {c : Cfg n} {i : Fin n} (h : (c.loc i).pc = .write) :
    step prop H t c i =
    { loc := Function.update c.loc i ⟨(c.loc i).rnd + 1, .start, (c.loc i).fdval⟩
      S := Function.update c.S (c.loc i).rnd (insert i (c.S (c.loc i).rnd))
      view := Function.update c.view (c.loc i).rnd
        (Function.update (c.view (c.loc i).rnd) i (insert i (c.S (c.loc i).rnd)))
      out := Function.update c.out (c.loc i).rnd
        (Function.update (c.out (c.loc i).rnd) i (c.loc i).fdval) } := by
  simp only [step, h]

theorem step_loc_ne {t : ℕ} {c : Cfg n} {i j : Fin n} (h : j ≠ i) :
    (step prop H t c i).loc j = c.loc j := by
  cases hp : (c.loc i).pc
  · rw [step_start hp]; simp [Function.update_of_ne h]
  · rw [step_write hp]; simp [Function.update_of_ne h]

theorem step_S_sub {t : ℕ} (c : Cfg n) (p : Fin n) (r : ℕ) :
    c.S r ⊆ (step prop H t c p).S r := by
  cases hp : (c.loc p).pc
  · rw [step_start hp]
  · rw [step_write hp]
    intro x hx
    by_cases h : r = (c.loc p).rnd
    · subst h; simp [hx]
    · simp [Function.update_of_ne h, hx]

theorem step_rnd_le {t : ℕ} (c : Cfg n) (p i : Fin n) :
    (c.loc i).rnd ≤ ((step prop H t c p).loc i).rnd := by
  by_cases h : i = p
  · subst h
    cases hp : (c.loc i).pc
    · rw [step_start hp]; simp
    · rw [step_write hp]; simp
  · rw [step_loc_ne h]

end Aux

/-- The invariant of the run of Figure 3 at time `t`. -/
structure Inv (c : Cfg n) (t : ℕ) : Prop where
  rnd_pos : ∀ i, 1 ≤ (c.loc i).rnd
  rnd_le : ∀ i, (c.loc i).rnd ≤ t + 1
  memS : ∀ r i, i ∈ c.S r ↔ 1 ≤ r ∧ r < (c.loc i).rnd
  self_mem : ∀ r i, i ∈ c.S r → i ∈ c.view r i
  view_sub : ∀ r i, i ∈ c.S r → c.view r i ⊆ c.S r
  contain : ∀ r i j, i ∈ c.S r → j ∈ c.S r → c.view r i ⊆ c.view r j ∨ c.view r j ⊆ c.view r i
  immed : ∀ r i j, i ∈ c.S r → j ∈ c.S r → i ∈ c.view r j → c.view r i ⊆ c.view r j
  fd : ∀ i, (c.loc i).pc = .write → ∃ t', (c.loc i).rnd ≤ t' + 1 ∧ (c.loc i).fdval = H i t' ∧
    (owner (c.loc i).rnd = i → ∃ A ⊆ c.S (c.loc i).rnd, prop A (H i t') i)
  out : ∀ r i, i ∈ c.S r → ∃ t', r ≤ t' + 1 ∧ c.out r i = H i t' ∧
    (owner r = i → ∃ A ⊆ c.view r i, prop A (H i t') i)

section Aux2
variable {prop} {H} {sched}

theorem Inv.not_mem_S {c : Cfg n} {t : ℕ} (hc : Inv prop H c t) (p : Fin n) :
    p ∉ c.S (c.loc p).rnd := by
  rw [hc.memS]; omega

theorem Inv.step_view {c : Cfg n} {t : ℕ} (hc : Inv prop H c t) (p : Fin n) {r : ℕ} {i : Fin n}
    (hi : i ∈ c.S r) :
    (step prop H t c p).view r i = c.view r i ∧ (step prop H t c p).out r i = c.out r i := by
  cases hp : (c.loc p).pc
  · rw [step_start hp]; simp
  · rw [step_write hp]
    by_cases h : r = (c.loc p).rnd
    · subst h
      have hip : i ≠ p := by rintro rfl; exact hc.not_mem_S i hi
      simp [Function.update_of_ne hip]
    · simp [Function.update_of_ne h]

theorem Inv.next {c : Cfg n} {t : ℕ} (hc : Inv prop H c t) (p : Fin n) :
    Inv prop H (step prop H t c p) (t + 1) := by
  cases hp : (c.loc p).pc
  · rw [step_start hp]
    have hrnd : ∀ i, ((Function.update c.loc p ⟨(c.loc p).rnd,
        if owner (c.loc p).rnd = p ∧ ¬ prop (c.S (c.loc p).rnd) (H p t) p then .start else .write,
        H p t⟩) i).rnd = (c.loc i).rnd := by
      intro i
      by_cases h : i = p
      · subst h; simp
      · simp [Function.update_of_ne h]
    refine ⟨fun i => by rw [hrnd]; exact hc.rnd_pos i, fun i => by rw [hrnd]; have := hc.rnd_le i; omega,
      fun r i => by rw [hrnd]; exact hc.memS r i, hc.self_mem, hc.view_sub, hc.contain, hc.immed,
      ?_, hc.out⟩
    intro i hi
    by_cases h : i = p
    · subst h
      simp only [Function.update_self] at hi ⊢
      refine ⟨t, hc.rnd_le i, rfl, fun ho => ⟨_, le_rfl, ?_⟩⟩
      by_contra hn
      simp [ho, hn] at hi
    · simp only [Function.update_of_ne h] at hi ⊢
      exact hc.fd i hi
  · have e := step_write (prop := prop) (H := H) (t := t) hp
    have hpS := hc.not_mem_S p
    have hold : ∀ r' i, i ∈ c.S r' → (step prop H t c p).view r' i = c.view r' i ∧
        (step prop H t c p).out r' i = c.out r' i := fun r' i hi => hc.step_view p hi
    have hsub : ∀ r', c.S r' ⊆ (step prop H t c p).S r' := fun r' => step_S_sub c p r'
    have hfd := hc.fd p hp
    have hrp := hc.rnd_pos p
    have hrl := hc.rnd_le p
    generalize (step prop H t c p) = c' at e hold hsub ⊢
    obtain ⟨r, hr⟩ : ∃ r, (c.loc p).rnd = r := ⟨_, rfl⟩
    rw [hr] at e hpS hfd hrp hrl
    subst e
    dsimp only at hold hsub ⊢
    have hlocne : ∀ i, i ≠ p → (Function.update c.loc p ⟨r + 1, .start, (c.loc p).fdval⟩) i
        = c.loc i := fun i h => Function.update_of_ne h _ _
    have hmem : ∀ r' i, i ∈ Function.update c.S r (insert p (c.S r)) r' ↔
        (r' = r ∧ i = p) ∨ i ∈ c.S r' := by
      intro r' i
      by_cases h : r' = r
      · subst h; simp
      · simp [h]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro i
      by_cases h : i = p
      · subst h; simp
      · rw [hlocne i h]; exact hc.rnd_pos i
    · intro i
      by_cases h : i = p
      · subst h; simp; omega
      · rw [hlocne i h]; have := hc.rnd_le i; omega
    · intro r' i
      rw [hmem]
      by_cases h : i = p
      · subst h; simp only [Function.update_self, and_true]; rw [hc.memS, hr]; omega
      · rw [hlocne i h, hc.memS]; simp [h]
    · intro r' i hi
      rcases (hmem r' i).1 hi with ⟨rfl, rfl⟩ | hi'
      · simp
      · rw [(hold r' i hi').1]; exact hc.self_mem r' i hi'
    · intro r' i hi
      rcases (hmem r' i).1 hi with ⟨rfl, rfl⟩ | hi'
      · simp
      · rw [(hold r' i hi').1]; exact (hc.view_sub r' i hi').trans (hsub r')
    · intro r' i j hi hj
      rcases (hmem r' i).1 hi with ⟨rfl, rfl⟩ | hi' <;>
        rcases (hmem r' j).1 hj with ⟨hh, rfl⟩ | hj'
      · exact Or.inl le_rfl
      · right
        rw [(hold _ j hj').1]
        simpa using (hc.view_sub _ j hj').trans (Finset.subset_insert _ _)
      · subst hh
        left
        rw [(hold _ i hi').1]
        simpa using (hc.view_sub _ i hi').trans (Finset.subset_insert _ _)
      · rw [(hold r' i hi').1, (hold r' j hj').1]; exact hc.contain r' i j hi' hj'
    · intro r' i j hi hj hij
      rcases (hmem r' i).1 hi with ⟨rfl, rfl⟩ | hi' <;>
        rcases (hmem r' j).1 hj with ⟨hh, rfl⟩ | hj'
      · exact le_rfl
      · rw [(hold _ j hj').1] at hij
        exact absurd (hc.view_sub _ j hj' hij) hpS
      · subst hh
        rw [(hold _ i hi').1]
        simpa using (hc.view_sub _ i hi').trans (Finset.subset_insert _ _)
      · rw [(hold r' i hi').1, (hold r' j hj').1] at *; exact hc.immed r' i j hi' hj' hij
    · intro i hi
      by_cases h : i = p
      · subst h; simp at hi
      · rw [hlocne i h] at hi ⊢
        obtain ⟨t', h1, h2, h3⟩ := hc.fd i hi
        exact ⟨t', h1, h2, fun ho => (h3 ho).imp fun A ⟨hA, hpA⟩ => ⟨hA.trans (hsub _), hpA⟩⟩
    · intro r' i hi
      rcases (hmem r' i).1 hi with ⟨rfl, rfl⟩ | hi'
      · obtain ⟨t', h1, h2, h3⟩ := hfd
        refine ⟨t', h1, by simpa using h2, fun ho => ?_⟩
        obtain ⟨A, hA, hpA⟩ := h3 ho
        exact ⟨A, by simpa using hA.trans (Finset.subset_insert _ _), hpA⟩
      · rw [(hold r' i hi').1, (hold r' i hi').2]; exact hc.out r' i hi'

/-! ### Properties of the run -/

theorem run_succ (t : ℕ) :
    run prop H sched (t + 1) = step prop H t (run prop H sched t) (sched t) := rfl

theorem inv_run (t : ℕ) : Inv prop H (run prop H sched t) t := by
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [run, Cfg.init]
    omega
  | succ t ih => exact ih.next _

theorem mem_S_run {t r : ℕ} {i : Fin n} :
    i ∈ (run prop H sched t).S r ↔ 1 ≤ r ∧ r < ((run prop H sched t).loc i).rnd :=
  (inv_run t).memS r i

theorem rnd_mono {t t' : ℕ} (h : t ≤ t') (i : Fin n) :
    ((run prop H sched t).loc i).rnd ≤ ((run prop H sched t').loc i).rnd := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (step_rnd_le _ _ _)

theorem S_mono {t t' : ℕ} (h : t ≤ t') (r : ℕ) :
    (run prop H sched t).S r ⊆ (run prop H sched t').S r := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (step_S_sub _ _ _)

theorem view_stable {t t' r : ℕ} {i : Fin n} (hi : i ∈ (run prop H sched t).S r) (h : t ≤ t') :
    (run prop H sched t').view r i = (run prop H sched t).view r i ∧
      (run prop H sched t').out r i = (run prop H sched t).out r i := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step hle ih =>
    rw [run_succ, ((inv_run _).step_view _ (S_mono hle r hi)).1,
      ((inv_run _).step_view _ (S_mono hle r hi)).2]
    exact ih

theorem view_eq_of_mem {t t' r : ℕ} {i : Fin n} (hi : i ∈ (run prop H sched t).S r)
    (hi' : i ∈ (run prop H sched t').S r) :
    (run prop H sched t).view r i = (run prop H sched t').view r i ∧
      (run prop H sched t).out r i = (run prop H sched t').out r i := by
  rcases le_total t t' with h | h
  · obtain ⟨h1, h2⟩ := view_stable hi h; exact ⟨h1.symm, h2.symm⟩
  · exact view_stable hi' h

/-- Frame: the local state of `i` does not change while `i` takes no step. -/
theorem loc_frame {t t' : ℕ} {i : Fin n} (h : t ≤ t') (hs : ∀ u, t ≤ u → u < t' → sched u ≠ i) :
    (run prop H sched t').loc i = (run prop H sched t).loc i := by
  induction h with
  | refl => rfl
  | step hle ih =>
    rw [run_succ, step_loc_ne (hs _ hle (Nat.lt_succ_self _)).symm]
    exact ih fun u h1 h2 => hs u h1 (Nat.lt_succ_of_lt h2)

theorem done_iff {r : ℕ} (hr : 1 ≤ r) {i : Fin n} :
    Done prop H sched r i ↔ ∃ t, i ∈ (run prop H sched t).S r := by
  simp only [Done, mem_S_run, hr, true_and]

theorem limView_eq {t r : ℕ} {i : Fin n} (hi : i ∈ (run prop H sched t).S r) :
    limView prop H sched r i = (run prop H sched t).view r i ∧
      limOut prop H sched r i = (run prop H sched t).out r i := by
  have hr : 1 ≤ r := (mem_S_run.1 hi).1
  have hd : Done prop H sched r i := (done_iff hr).2 ⟨t, hi⟩
  have h0 : i ∈ (run prop H sched (Nat.find hd)).S r := mem_S_run.2 ⟨hr, Nat.find_spec hd⟩
  simp only [limView, limOut, hd, ↓reduceDIte]
  exact view_eq_of_mem h0 hi

end Aux2

/-- The IIS schedule simulated by the run (round `k` = the paper's round `k + 1`). -/
noncomputable def simSchedule : Schedule (Fin n) where
  rd k :=
    { part := open Classical in Finset.univ.filter (Done prop H sched (k + 1))
      view := limView prop H sched (k + 1)
      view_sub := by
        intro i hi j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        obtain ⟨t, ht⟩ := (done_iff (by omega)).1 hi
        rw [(limView_eq ht).1] at hj
        exact (done_iff (by omega)).2 ⟨t, (inv_run t).view_sub _ _ ht hj⟩
      self_mem := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨t, ht⟩ := (done_iff (by omega)).1 hi
        rw [(limView_eq ht).1]
        exact (inv_run t).self_mem _ _ ht
      contain := by
        intro i hi j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        obtain ⟨t, ht⟩ := (done_iff (by omega)).1 hi
        obtain ⟨t', ht'⟩ := (done_iff (by omega)).1 hj
        have hi2 := S_mono (le_max_left t t') _ ht
        have hj2 := S_mono (le_max_right t t') _ ht'
        rw [(limView_eq hi2).1, (limView_eq hj2).1]
        exact (inv_run _).contain _ _ _ hi2 hj2
      immed := by
        intro i hi j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        obtain ⟨t, ht⟩ := (done_iff (by omega)).1 hi
        obtain ⟨t', ht'⟩ := (done_iff (by omega)).1 hj
        have hi2 := S_mono (le_max_left t t') _ ht
        have hj2 := S_mono (le_max_right t t') _ ht'
        rw [(limView_eq hi2).1, (limView_eq hj2).1]
        exact (inv_run _).immed _ _ _ hi2 hj2 }
  mono := by
    intro k i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨t, ht⟩ := hi
    exact ⟨t, by omega⟩

end

/-! ### Generic liveness facts -/

section Live
variable {prop : Finset (Fin n) → Finset (Fin n) → Fin n → Prop} [∀ a b i, Decidable (prop a b i)]
  {H : Fin n → ℕ → Finset (Fin n)} {sched : ℕ → Fin n}

theorem part_iff (k : ℕ) (i : Fin n) :
    i ∈ ((simSchedule prop H sched).rd k).part ↔ Done prop H sched (k + 1) i := by
  simp [simSchedule]

theorem view_simSchedule (k : ℕ) (i : Fin n) :
    ((simSchedule prop H sched).rd k).view i = limView prop H sched (k + 1) i := rfl

theorem done_zero (i : Fin n) : Done prop H sched 0 i :=
  ⟨0, by simp [run, Cfg.init]⟩

/-- A correct simulator takes a step at some time `≥ s`, in the local state it had at `s`. -/
theorem next_step {i : Fin n} (hi : SCorrect sched i) (s : ℕ) :
    ∃ t ≥ s, sched t = i ∧ (run prop H sched t).loc i = (run prop H sched s).loc i := by
  classical
  have h : ∃ t, s ≤ t ∧ sched t = i := by
    obtain ⟨t, ht, he⟩ := hi s; exact ⟨t, ht, he⟩
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2,
    loc_frame (Nat.find_spec h).1 fun u hu1 hu2 he => Nat.find_min h hu2 ⟨hu1, he⟩⟩

theorem rnd_write {t : ℕ} {i : Fin n} (hs : sched t = i)
    (hpc : ((run prop H sched t).loc i).pc = .write) :
    ((run prop H sched (t + 1)).loc i).rnd = ((run prop H sched t).loc i).rnd + 1 := by
  rw [run_succ, hs, step_write hpc]; simp

theorem loc_start {t : ℕ} {i : Fin n} (hs : sched t = i)
    (hpc : ((run prop H sched t).loc i).pc = .start)
    (hp : owner ((run prop H sched t).loc i).rnd = i →
      prop ((run prop H sched t).S ((run prop H sched t).loc i).rnd) (H i t) i) :
    ((run prop H sched (t + 1)).loc i).rnd = ((run prop H sched t).loc i).rnd ∧
      ((run prop H sched (t + 1)).loc i).pc = .write := by
  rw [run_succ, hs, step_start hpc]
  simp only [Function.update_self, true_and]
  split_ifs with h
  · exact absurd (hp h.1) h.2
  · rfl

/-- **Progress.** A correct simulator that has completed round `r` completes round `r + 1`,
provided that (if it owns round `r + 1`) its predicate eventually holds. -/
theorem progress {i : Fin n} (hi : SCorrect sched i) {r : ℕ} (hr : Done prop H sched r i)
    (hw : ∃ T, ∀ t ≥ T, owner (r + 1) = i → prop ((run prop H sched t).S (r + 1)) (H i t) i) :
    Done prop H sched (r + 1) i := by
  obtain ⟨t0, ht0⟩ := hr
  obtain ⟨T, hT⟩ := hw
  have hs : r < ((run prop H sched (max t0 T)).loc i).rnd :=
    lt_of_lt_of_le ht0 (rnd_mono (le_max_left _ _) i)
  by_cases hgt : r + 1 < ((run prop H sched (max t0 T)).loc i).rnd
  · exact ⟨_, hgt⟩
  have heq : ((run prop H sched (max t0 T)).loc i).rnd = r + 1 := by omega
  obtain ⟨t1, ht1, hsch1, hloc1⟩ := next_step (prop := prop) (H := H) hi (max t0 T)
  rw [← hloc1] at heq
  cases hpc : ((run prop H sched t1).loc i).pc
  · obtain ⟨hr2, hpc2⟩ := loc_start hsch1 hpc fun ho => by
      rw [heq] at ho ⊢; exact hT t1 (le_trans (le_max_right _ _) ht1) ho
    obtain ⟨t2, -, hsch2, hloc2⟩ := next_step (prop := prop) (H := H) hi (t1 + 1)
    have := rnd_write hsch2 (by rw [hloc2]; exact hpc2)
    exact ⟨t2 + 1, by rw [this, hloc2, hr2, heq]; omega⟩
  · exact ⟨t1 + 1, by rw [rnd_write hsch1 hpc, heq]; omega⟩

/-- A faulty simulator simulates only finitely many rounds. -/
theorem bounded_of_not_correct {i : Fin n} (hi : ¬ SCorrect sched i) :
    ∃ B, ∀ t, ((run prop H sched t).loc i).rnd ≤ B := by
  simp only [SCorrect, not_forall, not_exists, not_and] at hi
  obtain ⟨T, hT⟩ := hi
  refine ⟨((run prop H sched T).loc i).rnd, fun t => ?_⟩
  rcases le_total t T with h | h
  · exact rnd_mono h i
  · rw [loc_frame h fun u hu _ => hT u hu]

theorem correct_iff_of_live
    (hlive : ∀ i, SCorrect sched i → ∀ r, Done prop H sched r i) (i : Fin n) :
    (simSchedule prop H sched).Correct i ↔ SCorrect sched i := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨B, hB⟩ := bounded_of_not_correct (prop := prop) (H := H) hc
    obtain ⟨t, ht⟩ := (part_iff B i).1 (h B)
    have := hB t; omega
  · intro h k
    exact (part_iff k i).2 (hlive i h (k + 1))

/-- After some round, only correct simulators complete rounds. -/
theorem late_correct : ∃ R, ∀ r ≥ R, ∀ i, Done prop H sched r i → SCorrect sched i := by
  classical
  have key : ∀ i, ∃ B, ∀ r ≥ B, Done prop H sched r i → SCorrect sched i := by
    intro i
    by_cases hi : SCorrect sched i
    · exact ⟨0, fun _ _ _ => hi⟩
    · obtain ⟨B, hB⟩ := bounded_of_not_correct (prop := prop) (H := H) hi
      refine ⟨B, fun r hr ⟨t, ht⟩ => absurd (hB t) (by omega)⟩
  choose B hB using key
  refine ⟨Finset.univ.sup B, fun r hr i hd => hB i r ?_ hd⟩
  exact le_trans (Finset.le_sup (f := B) (Finset.mem_univ i)) hr

/-- The output and the wait of a completed round. -/
theorem limOut_spec {r : ℕ} (hr : 1 ≤ r) {i : Fin n} (hd : Done prop H sched r i) :
    ∃ t', r ≤ t' + 1 ∧ limOut prop H sched r i = H i t' ∧
      (owner r = i → ∃ A ⊆ limView prop H sched r i, prop A (H i t') i) := by
  obtain ⟨t, ht⟩ := (done_iff hr).1 hd
  rw [(limView_eq ht).1, (limView_eq ht).2]
  exact (inv_run t).out r i ht

theorem owner_frequently (i : Fin n) (R : ℕ) : ∃ k ≥ R, owner (k + 1) = i := by
  have hn := Nat.pos_of_neZero n
  refine ⟨n * R + i.val + (n - 1), by nlinarith, ?_⟩
  ext
  simp only [owner]
  have : n * R + i.val + (n - 1) + 1 = i.val + n * (R + 1) := by
    rw [mul_add, mul_one]; generalize n * R = m; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

end Live

/-! ### Theorem 2 -/

/-- **Theorem 2 (b), liveness.** With `Ω_k`, every correct simulator simulates every round. -/
theorem theorem2_live {H : Fin n → ℕ → Finset (Fin n)} {sched : ℕ → Fin n}
    (hH : IsOmegaK sched H) {i : Fin n} (hi : SCorrect sched i) (r : ℕ) :
    Done propOmega H sched r i := by
  obtain ⟨L, ⟨a, haL, ha⟩, T, hT⟩ := hH
  induction r generalizing i with
  | zero => exact done_zero i
  | succ r ih =>
    have nonowner : ∀ j, SCorrect sched j → owner (r + 1) ≠ j →
        Done propOmega H sched (r + 1) j :=
      fun j hj ho => progress hj (ih hj) ⟨0, fun _ _ h => absurd h ho⟩
    refine progress hi (ih hi) ?_
    by_cases hia : i = a
    · subst hia
      refine ⟨T, fun t ht _ => ?_⟩
      unfold propOmega
      exact ⟨i, by rw [hT t ht]; exact haL, Or.inl rfl⟩
    · by_cases ho : owner (r + 1) = i
      · obtain ⟨ta, hta⟩ := (done_iff (by omega)).1
          (nonowner a ha fun h => hia (ho.symm.trans h))
        refine ⟨max T ta, fun t ht _ => ?_⟩
        unfold propOmega
        exact ⟨a, by rw [hT t (le_trans (le_max_left _ _) ht)]; exact haL,
          Or.inr (S_mono (le_trans (le_max_right _ _) ht) _ hta)⟩
      · exact ⟨0, fun _ _ h => absurd h ho⟩

/-- **Theorem 2 (b).** A simulated process is correct iff its simulator is correct. -/
theorem theorem2_correct_iff {H : Fin n → ℕ → Finset (Fin n)} {sched : ℕ → Fin n}
    (hH : IsOmegaK sched H) (i : Fin n) :
    (simSchedule propOmega H sched).Correct i ↔ SCorrect sched i :=
  correct_iff_of_live (fun _ hj r => theorem2_live hH hj r) i

/-- **Theorem 2 (c).** The simulated failure detector is in `Ω*_k`: after some round all simulated
processes output the same set `L`, and `L` contains a strongly correct process. -/
theorem theorem2_omegaStar {H : Fin n → ℕ → Finset (Fin n)} {sched : ℕ → Fin n}
    (hH : IsOmegaK sched H) :
    ∃ L : Finset (Fin n), (∃ l ∈ L, l ∈ (simSchedule propOmega H sched).SC) ∧
      ∃ R, ∀ k ≥ R, ∀ i ∈ ((simSchedule propOmega H sched).rd k).part,
        limOut propOmega H sched (k + 1) i = L := by
  classical
  have hcorr := correct_iff_of_live (fun _ hj r => theorem2_live hH hj r)
  obtain ⟨L, ⟨a, haL, ha⟩, T, hT⟩ := hH
  obtain ⟨R1, hR1⟩ := late_correct (prop := propOmega) (H := H) (sched := sched)
  set σ := simSchedule propOmega H sched with hσ
  refine ⟨L, ?_, T, fun k hk i hi => ?_⟩
  · have hsee : ∀ k ≥ max T R1, owner (k + 1) ∈ σ.SC → owner (k + 1) ∉ (↑L : Set (Fin n)) →
        ∃ l ∈ (↑L : Set (Fin n)), σ.Correct l ∧ σ.Sees k (owner (k + 1)) l := by
      intro k hk hoSC hoL
      have h1 := le_max_left T R1
      have h2 := le_max_right T R1
      have hd : Done propOmega H sched (k + 1) (owner (k + 1)) :=
        (part_iff k _).1 (σ.correct_of_mem_SC hoSC k)
      obtain ⟨t', ht', -, hA⟩ := limOut_spec (by omega) hd
      obtain ⟨A, hAv, hpA⟩ := hA rfl
      obtain ⟨l, hl, hl'⟩ := hpA
      rw [hT t' (by omega)] at hl
      rcases hl' with hlo | hlA
      · exact absurd (hlo ▸ hl) hoL
      · have hlv : l ∈ (σ.rd k).view (owner (k + 1)) := hAv hlA
        have hlp : l ∈ (σ.rd k).part := (σ.rd k).view_sub _ ((part_iff k _).2 hd) hlv
        exact ⟨l, hl, (hcorr l).2 (hR1 (k + 1) (by omega) l ((part_iff k l).1 hlp)),
          (part_iff k _).2 hd, hlv⟩
    obtain ⟨l, hlL, hl⟩ := σ.thm2c_core (fun k => owner (k + 1))
      (fun i _ R => owner_frequently i R) (↑L) (max T R1) hsee ((hcorr a).2 ha)
    exact ⟨l, hlL, hl⟩
  · obtain ⟨t', ht', hout, -⟩ := limOut_spec (by omega) ((part_iff k i).1 hi)
    rw [hout, hT t' (by omega)]

/-! ### Theorem 3 -/

/-- **Theorem 3, liveness.** With `◇P`, every correct simulator simulates every round. -/
theorem theorem3_live {H : Fin n → ℕ → Finset (Fin n)} {sched : ℕ → Fin n}
    (hH : IsDiamondP sched H) {i : Fin n} (hi : SCorrect sched i) (r : ℕ) :
    Done propDP H sched r i := by
  classical
  obtain ⟨T, hT⟩ := hH
  induction r generalizing i with
  | zero => exact done_zero i
  | succ r ih =>
    have nonowner : ∀ j, SCorrect sched j → owner (r + 1) ≠ j → Done propDP H sched (r + 1) j :=
      fun j hj ho => progress hj (ih hj) ⟨0, fun _ _ h => absurd h ho⟩
    refine progress hi (ih hi) ?_
    by_cases ho : owner (r + 1) = i
    · have key : ∀ j, ∃ tj, SCorrect sched j → j ≠ i → j ∈ (run propDP H sched tj).S (r + 1) := by
        intro j
        by_cases hj : SCorrect sched j ∧ j ≠ i
        · obtain ⟨tj, htj⟩ := (done_iff (by omega)).1
            (nonowner j hj.1 fun h => hj.2 (h.symm.trans ho))
          exact ⟨tj, fun _ _ => htj⟩
        · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
      choose tj htj using key
      refine ⟨max T (Finset.univ.sup tj), fun t ht _ => ?_⟩
      intro j hj
      have hjc := (hT t (le_trans (le_max_left _ _) ht) i j).1 hj
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (S_mono (le_trans (Finset.le_sup (f := tj) (Finset.mem_univ j))
          (le_trans (le_max_right _ _) ht)) _ (htj j hjc hji))
    · exact ⟨0, fun _ _ h => absurd h ho⟩

/-- **Theorem 3.** With `◇P`, every correct simulator simulates a strongly correct process. -/
theorem theorem3_SC {H : Fin n → ℕ → Finset (Fin n)} {sched : ℕ → Fin n}
    (hH : IsDiamondP sched H) {i : Fin n} (hi : SCorrect sched i) :
    i ∈ (simSchedule propDP H sched).SC := by
  have hcorr := correct_iff_of_live (fun _ hj r => theorem3_live hH hj r)
  obtain ⟨T, hT⟩ := hH
  set σ := simSchedule propDP H sched with hσ
  refine σ.thm3_core (fun k => owner (k + 1)) (fun j _ R => owner_frequently j R) T ?_
    ((hcorr i).2 hi) i ((hcorr i).2 hi)
  intro k hk j ho hj
  have hd := (part_iff k _).1 (ho k)
  obtain ⟨t', ht', -, hA⟩ := limOut_spec (by omega) hd
  obtain ⟨A, hAv, hpA⟩ := hA rfl
  refine ⟨ho k, ?_⟩
  rcases hpA j ((hT t' (by omega) _ j).2 ((hcorr j).1 hj)) with h | h
  · rw [h]; exact (σ.rd k).self_mem _ (ho k)
  · exact hAv h

/-- **Theorem 3.** The simulated failure detector is in `◇P*`: after some round every simulated
process trusts exactly the strongly correct processes. -/
theorem theorem3_diamondPStar {H : Fin n → ℕ → Finset (Fin n)} {sched : ℕ → Fin n}
    (hH : IsDiamondP sched H) :
    ∃ R, ∀ k ≥ R, ∀ i ∈ ((simSchedule propDP H sched).rd k).part, ∀ j,
      j ∈ limOut propDP H sched (k + 1) i ↔ j ∈ (simSchedule propDP H sched).SC := by
  have hcorr := correct_iff_of_live (fun _ hj r => theorem3_live hH hj r)
  obtain ⟨T, hT⟩ := id hH
  refine ⟨T, fun k hk i hi j => ?_⟩
  obtain ⟨t', ht', hout, -⟩ := limOut_spec (by omega) ((part_iff k i).1 hi)
  rw [hout, hT t' (by omega) i j]
  exact ⟨fun h => theorem3_SC hH h, fun h => (hcorr j).1 (Schedule.correct_of_mem_SC _ h)⟩

/-! ### Non-vacuity -/
/-- Non-vacuity of Theorems 2 and 3 with a crash: two simulators, `p_1` crashes initially
(never scheduled), `Ω_k` and `◇P` both output `{p_0}`; the hypotheses hold and `p_0` simulates
every round. -/
theorem nonvacuous_crash :
    ¬ SCorrect (n := 2) (fun _ => 0) 1 ∧
    IsOmegaK (n := 2) (fun _ => 0) (fun _ _ => {0}) ∧
    IsDiamondP (n := 2) (fun _ => 0) (fun _ _ => {0}) ∧
    (∀ r, Done propOmega (fun _ _ => ({0} : Finset (Fin 2))) (fun _ => 0) r 0) ∧
    (∀ r, Done propDP (fun _ _ => ({0} : Finset (Fin 2))) (fun _ => 0) r 0) := by
  have h0 : SCorrect (n := 2) (fun _ => 0) 0 := fun T => ⟨T, le_rfl, rfl⟩
  have h1 : ¬ SCorrect (n := 2) (fun _ => 0) 1 := fun h => by
    obtain ⟨t, -, ht⟩ := h 0; exact absurd ht (by simp)
  have hΩ : IsOmegaK (n := 2) (fun _ => 0) (fun _ _ => {0}) :=
    ⟨{0}, ⟨0, by simp, h0⟩, 0, fun _ _ _ => rfl⟩
  have hP : IsDiamondP (n := 2) (fun _ => 0) (fun _ _ => {0}) := by
    refine ⟨0, fun _ _ _ j => ?_⟩
    fin_cases j
    · simpa using h0
    · simpa using h1
  exact ⟨h1, hΩ, hP, fun r => theorem2_live hΩ h0 r, fun r => theorem3_live hP h0 r⟩

end Podc.IteratedSnapshotFD.Fig3
