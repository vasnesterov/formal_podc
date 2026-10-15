import Papers.PODC2024.RecoverableConsensus.Defs

/-!
# Configuration-level notions of Section 3 (Ovens, PODC'24)

For a critical execution `α` from `D` (w.r.t. `E*_z(D)`), all processes are poised to access one
object `O` (Lemma 9). We define

* `valAfter E O σ` — the value of `O` after the processes of the schedule `σ` take one step each;
* `U z D α O v` — the paper's `U_v`: values of `O` after schedules starting with a team-`v` process;
* `Hiding z D α O v` — `Cα` is `v`-hiding; `Recording z D α O` — `Cα` is `n`-recording;
* `lam k` — the schedule `λ_k = c_k c_{k+1} … c_{n-1}`;

and prove Observation 11 (`obs11`) and that an `n`-recording configuration makes the type of `O`
`n`-recording (`Recording.isRecording`). (Observation 5, `UnivQ.transfer`, lives in
`Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`.)
-/

namespace Cslib.SharedMemory.Recoverable.Ovens

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-! ## Reachability with arbitrary crashes -/

lemma reach_run {C : Cfg A} (hC : Reach A (fun _ => True) C) (β : List (Ev n)) :
    Reach A (fun _ => True) (run C β) := by
  obtain ⟨x, γ, -, rfl⟩ := hC
  exact ⟨x, γ ++ β, trivial, by rw [run_append]⟩

/-! ## Schedules of distinct processes poised on one object -/

/-- Value of `O` after each process of `σ` takes one step from `E`. -/
def valAfter (E : Cfg A) (O : ι) (σ : List (Fin n)) : (T O).State := (run E (σ.map Ev.step)).mem O

/-- If the processes of a schedule of distinct processes are poised to apply `o p` to `O`, the
schedule only changes `O`, whose new value is `apply`. -/
lemma run_steps_poised {O : ι} (o : Fin n → (T O).Op) (k : (p : Fin n) → (T O).Resp → A.L)
    (σ : List (Fin n)) (hσ : σ.Nodup) (E : Cfg A)
    (hE : ∀ p ∈ σ, A.act (E.loc p) = .access O (o p) (k p)) :
    (run E (σ.map Ev.step)).mem = Function.update E.mem O (apply (T O) (E.mem O) o σ) := by
  induction σ generalizing E with
  | nil => simp
  | cons p σ ih =>
    rw [List.nodup_cons] at hσ
    simp only [List.map_cons, run_cons, Cfg.next]
    rw [stepP_of_access E (hE p (by simp))]
    rw [ih hσ.2]
    · simp
    · intro q hq
      have hqp : q ≠ p := fun h => hσ.1 (h ▸ hq)
      simp only [Function.update_of_ne hqp]
      exact hE q (by simp [hq])

/-- Two schedules of distinct processes poised on `O` reaching the same value of `O` reach the
same memory. -/
lemma mem_eq_of_valAfter_eq {E : Cfg A} {O : ι} (hpo : ∀ p, E.Poised p O) {σ τ : List (Fin n)}
    (hσ : σ.Nodup) (hτ : τ.Nodup) (h : valAfter E O σ = valAfter E O τ) :
    (run E (σ.map Ev.step)).mem = (run E (τ.map Ev.step)).mem := by
  choose o k hok using hpo
  have h1 := run_steps_poised o k σ hσ E (fun p _ => hok p)
  have h2 := run_steps_poised o k τ hτ E (fun p _ => hok p)
  have h1' := congrFun h1 O
  have h2' := congrFun h2 O
  simp only [Function.update_self] at h1' h2'
  unfold valAfter at h
  rw [h1, h2, ← h1', ← h2', h]

lemma valAfter_eq_apply {E : Cfg A} {O : ι} (o : Fin n → (T O).Op)
    (k : (p : Fin n) → (T O).Resp → A.L) (hok : ∀ p, A.act (E.loc p) = .access O (o p) (k p))
    {σ : List (Fin n)} (hσ : σ.Nodup) : valAfter E O σ = apply (T O) (E.mem O) o σ := by
  have := congrFun (run_steps_poised o k σ hσ E (fun p _ => hok p)) O
  simpa [valAfter] using this

/-- A schedule of distinct processes poised on `O` that does not change the value of `O` does not
change the memory. -/
lemma mem_eq_of_valAfter_eq_self {E : Cfg A} {O : ι} (hpo : ∀ p, E.Poised p O)
    {σ : List (Fin n)} (hσ : σ.Nodup) (h : valAfter E O σ = E.mem O) :
    (run E (σ.map Ev.step)).mem = E.mem := by
  have := mem_eq_of_valAfter_eq hpo hσ List.nodup_nil (by simpa [valAfter] using h)
  simpa using this

/-! ## Crash blocks `λ_k` -/

/-- `λ_k = c_k c_{k+1} … c_{n-1}`: crashes of all processes with identifier `≥ k`. -/
def lam (n k : ℕ) : List (Ev n) :=
  ((List.finRange n).filter (fun c => decide (k ≤ c.val))).map Ev.crash

lemma mem_lam {k : ℕ} {e : Ev n} : e ∈ lam n k ↔ ∃ c : Fin n, k ≤ c.val ∧ e = .crash c := by
  simp [lam, eq_comm]

lemma run_crashes_mem (C : Cfg A) (cs : List (Fin n)) : (run C (cs.map Ev.crash)).mem = C.mem := by
  induction cs generalizing C with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, run_cons]; rw [ih]; rfl

lemma run_crashes_loc (C : Cfg A) (cs : List (Fin n)) (r : Fin n) :
    (run C (cs.map Ev.crash)).loc r = if r ∈ cs then A.init r (C.inp r) else C.loc r := by
  induction cs generalizing C with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, run_cons]
    rw [ih]
    by_cases hr : r = c
    · subst hr; simp
    · simp only [List.mem_cons, hr, false_or, next_inp]
      split_ifs <;> simp [Cfg.next, Function.update_of_ne hr]

lemma run_lam_mem (C : Cfg A) (k : ℕ) : (run C (lam n k)).mem = C.mem := run_crashes_mem C _

lemma run_lam_loc (C : Cfg A) (k : ℕ) (r : Fin n) :
    (run C (lam n k)).loc r = if k ≤ r.val then A.init r (C.inp r) else C.loc r := by
  rw [lam, run_crashes_loc]
  simp

lemma lam_proc {k : ℕ} {e : Ev n} (he : e ∈ lam n k) : k ≤ e.proc.val := by
  obtain ⟨c, hc, rfl⟩ := mem_lam.1 he
  simpa using hc

lemma lam_ne_nil {k : ℕ} (hk : k < n) : lam n k ≠ [] := by
  intro h
  have : Ev.crash (⟨n - 1, by omega⟩ : Fin n) ∈ lam n k := mem_lam.2 ⟨_, by simp; omega, rfl⟩
  rw [h] at this
  simp at this

lemma crashes_lam (k : ℕ) (r : Fin n) : crashes r (lam n k) = if k ≤ r.val then 1 else 0 := by
  unfold crashes lam
  rw [List.count_map_of_injective _ _ (fun a b h => by cases h; rfl)]
  split_ifs with hr
  · exact List.count_eq_one_of_mem (List.Nodup.filter _ (List.nodup_finRange n)) (by simpa using hr)
  · exact List.count_eq_zero_of_not_mem (by simpa using hr)

lemma stepsBelow_crashes (r : Fin n) (cs : List (Fin n)) :
    stepsBelow r (cs.map Ev.crash) = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa using ih

lemma stepsBelow_lam (k : ℕ) (r : Fin n) : stepsBelow r (lam n k) = 0 := stepsBelow_crashes _ _

lemma stepsBelow_steps_pos {l : List (Fin n)} {q r : Fin n} (hq : q ∈ l) (hqr : q < r) :
    1 ≤ stepsBelow r (l.map Ev.step) := by
  unfold stepsBelow
  rw [Nat.one_le_iff_ne_zero, Ne, List.countP_eq_zero]
  push Not
  exact ⟨.step q, by simp [hq], by simp [Ev.isStepBelow, hqr]⟩

lemma crashes_steps (r : Fin n) (l : List (Fin n)) : crashes r (l.map Ev.step) = 0 :=
  crashes_eq_zero_of_crashFree (crashFree_steps l) r

/-- Steps followed by one crash of each process of `cs`, where every crashing process has a
smaller process among the steppers, are in `E*_z` (for `z n ≥ 1`). -/
lemma inEs_steps_crashes {z : ℕ} (hzn : 1 ≤ z * n) (l : List (Fin n)) (cs : List (Fin n))
    (hcs : cs.Nodup) (hbelow : ∀ c ∈ cs, ∃ q ∈ l, q < c) :
    InEs z (l.map Ev.step ++ cs.map Ev.crash) := by
  intro m r
  rw [List.take_append, crashes_append, stepsBelow_append,
    crashes_eq_zero_of_crashFree ((crashFree_steps l).take m), Nat.zero_add]
  by_cases hlm : l.length ≤ m
  · rw [List.take_of_length_le (l := l.map Ev.step) (by simpa using hlm)]
    have hc : crashes r ((cs.map Ev.crash).take (m - (l.map Ev.step).length)) ≤
        if r ∈ cs then 1 else 0 := by
      unfold crashes
      refine ((List.take_sublist _ _).count_le _).trans ?_
      rw [List.count_map_of_injective _ _ (fun a b h => by cases h; rfl)]
      split_ifs with hr
      · exact (List.nodup_iff_count_le_one.1 hcs) r
      · exact (List.count_eq_zero_of_not_mem hr).le
    split_ifs at hc with hr
    · obtain ⟨q, hq, hqr⟩ := hbelow r hr
      have h1 := stepsBelow_steps_pos hq hqr
      calc _ ≤ 1 := hc
        _ ≤ z * n * 1 := by simpa using hzn
        _ ≤ z * n * (stepsBelow r (l.map Ev.step) + _) :=
          Nat.mul_le_mul_left _ (le_trans h1 (Nat.le_add_right _ _))
    · omega
  · have hlt : m - (l.map Ev.step).length = 0 := by simp; omega
    rw [hlt]
    simp

variable {z : ℕ}

/-! ## Hiding and recording configurations -/

/-- The paper's `U_v` for the critical execution `α` from `D`: values of `O` after schedules of
distinct processes starting with a process on team `v`. -/
def U (z : ℕ) (D : Cfg A) (α : List (Ev n)) (O : ι) (v : Bool) : Set (T O).State :=
  {u | ∃ p σ, Team z D α p v ∧ (p :: σ).Nodup ∧ u = valAfter (run D α) O (p :: σ)}

/-- `Cα` is `v`-hiding. -/
def Hiding (z : ℕ) (D : Cfg A) (α : List (Ev n)) (O : ι) (v : Bool) : Prop :=
  Disjoint (U z D α O false) (U z D α O true) ∧ (run D α).mem O ∈ U z D α O v

/-- `Cα` is `n`-recording. -/
def Recording (z : ℕ) (D : Cfg A) (α : List (Ev n)) (O : ι) : Prop :=
  Disjoint (U z D α O false) (U z D α O true) ∧
    ∀ v, (run D α).mem O ∈ U z D α O v → ∃! p, Team z D α p (!v)

/-- **Observation 11.** `Cα` is `n`-recording, or `v`-hiding for some `v`, or two schedules
starting with processes on different teams give `O` the same value. -/
theorem obs11 (D : Cfg A) (α : List (Ev n)) (O : ι) :
    Recording z D α O ∨ (∃ v, Hiding z D α O v) ∨
      ∃ p σ q τ, Team z D α p false ∧ Team z D α q true ∧ (p :: σ).Nodup ∧ (q :: τ).Nodup ∧
        valAfter (run D α) O (p :: σ) = valAfter (run D α) O (q :: τ) := by
  by_cases hd : Disjoint (U z D α O false) (U z D α O true)
  · by_cases h0 : (run D α).mem O ∈ U z D α O false
    · exact Or.inr (Or.inl ⟨false, hd, h0⟩)
    by_cases h1 : (run D α).mem O ∈ U z D α O true
    · exact Or.inr (Or.inl ⟨true, hd, h1⟩)
    refine Or.inl ⟨hd, fun v hv => ?_⟩
    cases v <;> contradiction
  · right; right
    rw [Set.not_disjoint_iff] at hd
    obtain ⟨u, ⟨p, σ, hp, hσ, rfl⟩, ⟨q, τ, hq, hτ, he⟩⟩ := hd
    exact ⟨p, σ, q, τ, hp, hq, hσ, hτ, he⟩

/-- Hiding but not recording: team `v̄` has at least two members. -/
lemma Hiding.not_unique {D : Cfg A} {α : List (Ev n)} {O : ι} {v : Bool}
    (hh : Hiding z D α O v) (hr : ¬ Recording z D α O) : ¬ ∃! p, Team z D α p (!v) := by
  intro hu
  apply hr
  refine ⟨hh.1, fun w hw => ?_⟩
  by_cases hwv : w = v
  · subst hwv; exact hu
  · exfalso
    have hw' : w = !v := by cases w <;> cases v <;> simp_all
    subst hw'
    cases v
    · exact Set.disjoint_left.1 hh.1 hh.2 hw
    · exact Set.disjoint_left.1 hh.1 hw hh.2

/-- **An `n`-recording configuration in which all processes are poised on `O` shows that the type
of `O` is `n`-recording** (remark before Observation 11). -/
theorem Recording.isRecording (hA : RecConsensus A) {D : Cfg A} (hD : Reach A (fun _ => True) D)
    (hn : 0 < n) {α : List (Ev n)} (hc : Crit z D α) {O : ι}
    (hpo : ∀ p, (run D α).Poised p O) (hrec : Recording z D α O) : IsRecording n (T O) := by
  classical
  have hAdm := admOK_true (n := n) z
  choose o k hok using hpo
  let tm : Fin n → Bool := fun p => decide (Team z D α p true)
  have htm : ∀ p, Team z D α p (tm p) := by
    intro p
    by_cases h : Team z D α p true
    · simp [tm, h]
    · obtain ⟨w, hw⟩ := hc.team p
      cases w
      · simpa [tm, h] using hw
      · exact absurd hw h
  have htm_iff : ∀ p v, Team z D α p v ↔ tm p = v := by
    intro p v
    constructor
    · intro h; exact (htm p).unique hA hAdm hD h
    · rintro rfl; exact htm p
  obtain ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩⟩ := hc.teams hA hAdm hD hn
  refine ⟨(run D α).mem O, tm, o, ⟨p₀, (htm_iff _ _).1 hp₀⟩, ⟨q₀, (htm_iff _ _).1 hq₀⟩, ?_, ?_⟩
  · intro p σ q τ hσ hτ hp hq he
    rw [← valAfter_eq_apply o k hok hσ, ← valAfter_eq_apply o k hok hτ] at he
    exact Set.disjoint_left.1 hrec.1 ⟨p, σ, (htm_iff _ _).2 hp, hσ, rfl⟩
      ⟨q, τ, (htm_iff _ _).2 hq, hτ, he⟩
  · intro p σ hσ he
    rw [← valAfter_eq_apply o k hok hσ] at he
    obtain ⟨q, hq, huniq⟩ := hrec.2 (tm p) ⟨p, σ, htm p, hσ, he.symm⟩
    exact ⟨q, (htm_iff _ _).1 hq, fun r hr => huniq r ((htm_iff _ _).2 hr)⟩

end Cslib.SharedMemory.Recoverable.Ovens
