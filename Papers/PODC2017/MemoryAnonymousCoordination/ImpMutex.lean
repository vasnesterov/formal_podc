import Papers.PODC2017.MemoryAnonymousCoordination.ImpCommon
import Cslib.Computability.Distributed.SharedMemory.Mutex

/-!
# Theorem 6.2: no deadlock-free mutual exclusion with unnamed registers for unknown `n`

Taubenfeld, *Coordination Without Prior Agreement*, PODC 2017, Section 6.2.

There is no deadlock-free mutual exclusion algorithm using unnamed read/write registers when the
number of processes is not a priori known (`theorem_6_2`). The same covering argument shows that
`n ≥ 2` processes need at least `n` unnamed registers (`mutex_card_lt`; for named registers this
is the classical Burns–Lynch bound).

Mutual exclusion and deadlock-freedom are CSLib's `Impl.MutualExclusion` and
`Impl.DeadlockFree` (fair, client-well-formed infinite executions; processes may stay in the
remainder section forever). For a finite but unknown number of processes, deadlock-freedom is
only required of executions with finitely many participants (`DeadlockFreeFin`, used in
`theorem_6_2`); `theorem_6_2_unbounded` is the corollary for `Impl.DeadlockFree`.

## Deadlock-freedom used as a progress guarantee

`df_progress`: if, after a client-well-formed execution in which nobody is in the critical
section, exactly the processes of `ps` are pending (all trying), then running them in round-robin
order some process of `ps` eventually returns from `lock()`. Otherwise the round-robin execution
is fair and client-well-formed and contradicts deadlock-freedom.
-/

open Cslib.SharedMemory Impl

namespace Podc.MemoryAnonymousCoordination

section Regions

variable {P : Type} [DecidableEq P]

/-- The region of `p` only depends on the labels of `p`. -/
lemma regionOf_filter (α : List (Label P mutexObj)) (p : P) :
    regionOf α p = regionOf (α.filter (fun ℓ => ℓ.proc = p)) p := by
  unfold regionOf
  generalize (some Region.rem : Option Region) = x
  induction α generalizing x with
  | nil => rfl
  | cons ℓ α ih =>
    by_cases h : ℓ.proc = p
    · simp [h, ih]
    · simp [h, ih]

lemma regionOf_append_middle {α β γ : List (Label P mutexObj)} {p : P}
    (h : ∀ ℓ ∈ β, ℓ.proc ≠ p) : regionOf (α ++ β ++ γ) p = regionOf (α ++ γ) p := by
  rw [regionOf_filter, regionOf_filter (α ++ γ)]
  congr 1
  have : β.filter (fun ℓ => ℓ.proc = p) = [] := List.filter_eq_nil_iff.2 (by simpa using h)
  simp only [List.filter_append, this, List.append_nil]

lemma regionOf_append_outer {α β γ : List (Label P mutexObj)} {p : P}
    (hα : ∀ ℓ ∈ α, ℓ.proc ≠ p) (hγ : ∀ ℓ ∈ γ, ℓ.proc ≠ p) :
    regionOf (α ++ β ++ γ) p = regionOf β p := by
  rw [regionOf_filter, regionOf_filter β]
  have h1 : α.filter (fun ℓ => ℓ.proc = p) = [] := List.filter_eq_nil_iff.2 (by simpa using hα)
  have h3 : γ.filter (fun ℓ => ℓ.proc = p) = [] := List.filter_eq_nil_iff.2 (by simpa using hγ)
  simp only [List.filter_append, h1, h3, List.nil_append, List.append_nil]

lemma regionOf_of_forall_ne {α : List (Label P mutexObj)} {p : P}
    (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) : regionOf α p = some .rem := by
  rw [regionOf_filter, List.filter_eq_nil_iff.2 (by simpa using h)]
  rfl

lemma regionOf_append_tau (α : List (Label P mutexObj)) (p q : P) :
    regionOf (α ++ [.tau q]) p = regionOf α p := by
  rw [regionOf_append_singleton]
  split_ifs
  · rcases regionOf α p with _ | r
    · rfl
    · cases r <;> rfl
  · rfl

lemma regionOf_append_taus (α : List (Label P mutexObj)) (σ : ℕ → P) (k : ℕ) :
    regionOf (α ++ (List.range k).map (fun i => (Label.tau (σ i) : Label P mutexObj))) =
      regionOf α := by
  funext s
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, ← List.append_assoc, List.map_singleton,
      regionOf_append_tau, ih]

/-- The region of a process that invoked `lock` once and never returned is `trying`, and the
region of a process that invoked nothing is `rem`. -/
lemma regionOf_of_ops {p : P} : ∀ (β : List (Label P mutexObj)), respsOf β p = [] →
    (opsOf β p = [] → regionOf β p = some .rem) ∧
    (opsOf β p = [.lock] → regionOf β p = some .trying) := by
  intro β
  induction β using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton β ℓ ih =>
    intro hr
    rw [respsOf_append] at hr
    have ih' := ih (List.append_eq_nil_iff.1 hr).1
    rw [regionOf_append_singleton, opsOf_append]
    cases ℓ with
    | inv s o =>
      by_cases hs : s = p
      · subst hs
        simp only [Label.proc, ↓reduceIte, opsOf_cons, opsOf_nil, Label.invOf]
        refine ⟨fun h => by simp at h, fun h => ?_⟩
        simp only [List.append_eq_singleton_iff] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp at h2
          subst h2; rw [ih'.1 h1]; rfl
        · simp at h2
      · have hne : (Label.inv s o : Label P mutexObj).proc ≠ p := hs
        have : opsOf [(Label.inv s o : Label P mutexObj)] p = [] := by
          simp [opsOf, Label.invOf, hs]
        simp only [hne, ↓reduceIte, this, List.append_nil]
        exact ih'
    | tau s =>
      have : opsOf [(Label.tau s : Label P mutexObj)] p = [] := rfl
      rw [this, List.append_nil]
      split_ifs
      · refine ⟨fun h => by rw [ih'.1 h]; rfl, fun h => by rw [ih'.2 h]; rfl⟩
      · exact ih'
    | ret s r =>
      by_cases hs : s = p
      · subst hs; simp [respsOf, Label.retOf] at hr
      · have hne : (Label.ret s r : Label P mutexObj).proc ≠ p := hs
        have : opsOf [(Label.ret s r : Label P mutexObj)] p = [] := rfl
        simp only [hne, ↓reduceIte, this, List.append_nil]
        exact ih'

end Regions

variable {ι : Type} {B : ι → ObjSpec} {L P : Type} [DecidableEq P] [DecidableEq ι]

section RoundRobin

variable (J : Impl mutexObj B P L) (σ : ℕ → P)

/-- Round-robin configurations: at time `t` the process `σ t` takes a solo step. -/
noncomputable def rr (C : Config mutexObj B P L) : ℕ → Config mutexObj B P L
  | 0 => C
  | t + 1 => J.soloStep (σ t) (rr C t)

/-- The labels of the round-robin run. -/
noncomputable def rrLabels (C : Config mutexObj B P L) : ℕ → List (Label P mutexObj)
  | 0 => []
  | t + 1 => rrLabels C t ++ J.soloLabels (σ t) (rr J σ C t) 1

lemma runFrom_rrLabels (C : Config mutexObj B P L) (t : ℕ) :
    J.runFrom C (rrLabels J σ C t) = some (rr J σ C t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [rrLabels, rr]
    rw [runFrom_append, ih, Option.bind_some, J.runFrom_soloLabels]
    rfl

end RoundRobin


section ClientWF

variable {P : Type} [DecidableEq P]

lemma regionOf_append_none {β : List (Label P mutexObj)} {p : P} (h : regionOf β p = none)
    (γ : List (Label P mutexObj)) : regionOf (β ++ γ) p = none := by
  induction γ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton γ ℓ ih =>
    rw [← List.append_assoc, regionOf_append_singleton, ih]
    split_ifs <;> rfl

lemma clientWF_of_append {β γ : List (Label P mutexObj)} (h : ClientWF (β ++ γ)) :
    ClientWF β := fun p hp => h p (regionOf_append_none hp γ)

lemma clientWF_of_prefix {β γ : List (Label P mutexObj)} (h : ClientWF γ) (hp : β <+: γ) :
    ClientWF β := by
  obtain ⟨δ, rfl⟩ := hp; exact clientWF_of_append h

lemma clientWF_append_tau {β : List (Label P mutexObj)} (h : ClientWF β) (q : P) :
    ClientWF (β ++ [.tau q]) := fun p => by rw [regionOf_append_tau]; exact h p

end ClientWF

section DF

variable {J : Impl mutexObj B P L}

/-- Deadlock-freedom for a finite but not a priori known number of processes: CSLib's
`Impl.DeadlockFree` restricted to infinite executions in which only finitely many processes take
part. With infinitely many potential participants (`[Infinite P]`) this is weaker than
`Impl.DeadlockFree`, which also constrains executions with infinitely many participants (the
"unbounded" model of the paper); an algorithm that is deadlock-free for every finite number of
processes satisfies it. -/
def DeadlockFreeFin (J : Impl mutexObj B P L) : Prop :=
  ∀ e : J.InfExec, (∃ S : Finset P, ∀ t, (e.lbl t).proc ∈ S) → (∀ t, ClientWF (e.pre t)) →
    e.Fair → ∀ t, (∃ p, (e.cfg t).pend p ≠ none) → (∀ q, ¬ InCS (e.pre t) q) →
      ∃ t' ≥ t, ∃ p r, e.lbl t' = .ret p r

lemma deadlockFreeFin_of_deadlockFree (h : J.DeadlockFree) : DeadlockFreeFin J :=
  fun e _ => h e

/-- Round-robin schedule over a nonempty list of processes. -/
def rrSched (ps : List P) (hps : ps ≠ []) (t : ℕ) : P :=
  ps[t % ps.length]'(Nat.mod_lt _ (List.length_pos_iff.2 hps))

omit [DecidableEq P] in
lemma rrSched_mem (ps : List P) (hps : ps ≠ []) (t : ℕ) : rrSched ps hps t ∈ ps :=
  List.getElem_mem _

omit [DecidableEq P] in
lemma rrSched_fair (ps : List P) (hps : ps ≠ []) {p : P} (hp : p ∈ ps) (t : ℕ) :
    ∃ t' ≥ t, rrSched ps hps t' = p := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hlen : 0 < ps.length := List.length_pos_iff.2 hps
  refine ⟨ps.length * t + i, ?_, ?_⟩
  · exact le_trans (Nat.le_mul_of_pos_left t hlen) (Nat.le_add_right _ _)
  · simp only [rrSched, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

/-- **Deadlock-freedom as progress.** After a client-well-formed execution `α` in which nobody is
in the critical section and exactly the processes of `ps` are pending, the round-robin run of
`ps` eventually makes some process of `ps` return. -/
theorem df_progress (hdf : DeadlockFreeFin J) {α : List (Label P mutexObj)}
    {F : Config mutexObj B P L} (hα : J.run α = some F) (hwf : ClientWF α)
    (hncs : ∀ s, ¬ InCS α s) (ps : List P) (hps : ps ≠ [])
    (hpend : ∀ s, F.pend s ≠ none ↔ s ∈ ps) :
    ∃ t, ∃ p ∈ ps, (rr J (rrSched ps hps) F t).pend p = none := by
  by_contra hcon
  push Not at hcon
  set σ := rrSched ps hps
  -- every round-robin step is an internal step
  have hstep : ∀ t, J.soloLabels (σ t) (rr J σ F t) 1 = [.tau (σ t)] ∧
      (rr J σ F (t + 1)).pend = (rr J σ F t).pend := by
    intro t
    have hp := hcon t (σ t) (rrSched_mem ps hps t)
    have hr := J.runFrom_soloLabels (σ t) (rr J σ F t) 1
    rw [J.soloLabels_succ] at hr
    simp only [hp, ↓reduceIte, soloLabels] at hr
    cases hact : J.act (σ t) ((rr J σ F t).loc (σ t)) with
    | access i o k =>
      have hnl : J.nextLabel (rr J σ F t) (σ t) = .tau (σ t) := by simp [nextLabel, hact]
      rw [hnl, runFrom_singleton] at hr
      refine ⟨by rw [J.soloLabels_succ]; simp [hp, hnl, soloLabels], ?_⟩
      have := (step_tau hr).2.1
      simpa [rr] using this
    | ret r l =>
      exfalso
      have hnl : J.nextLabel (rr J σ F t) (σ t) = .ret (σ t) r := by simp [nextLabel, hact]
      rw [hnl, runFrom_singleton] at hr
      exact hcon (t + 1) (σ t) (rrSched_mem ps hps t) (by
        have := congrFun (step_ret hr).2.1 (σ t); simpa [rr] using this)
  have hpend_rr : ∀ t, (rr J σ F t).pend = F.pend := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => rw [(hstep t).2, ih]
  have hlabs : ∀ t, rrLabels J σ F t = (List.range t).map (fun i => .tau (σ i)) := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => simp [rrLabels, ih, (hstep t).1, List.range_succ]
  set E : ℕ → List (Label P mutexObj) := fun k => α ++ rrLabels J σ F k with hE
  have hErun : ∀ k, J.run (E k) = some (rr J σ F k) := fun k => by
    simp only [E]; rw [run, runFrom_append]; rw [run] at hα; rw [hα]; exact runFrom_rrLabels J σ F k
  have hElen : ∀ k, (E k).length = α.length + k := fun k => by simp [E, hlabs]
  obtain ⟨e, he1, he2⟩ := J.exists_infExec_of_chain E
    (fun k => by simp only [E, rrLabels]; rw [← List.append_assoc]; exact List.prefix_append _ _)
    (fun k => by rw [hElen]; omega) (fun k => ⟨_, hErun k⟩)
  set N := α.length
  have hlbl : ∀ s, e.lbl (N + s) = .tau (σ s) := by
    intro s
    rw [he1 (s + 1) (N + s) (by rw [hElen]; omega)]
    simp only [E, hlabs]
    rw [List.getElem_append_right (by omega)]
    simp [N]
  have hcfg : ∀ s, e.cfg (N + s) = rr J σ F s := by
    intro s
    have := he2 s (N + s) (by rw [hElen])
    rw [List.take_of_length_le (by rw [hElen]), hErun s] at this
    exact (Option.some.inj this).symm
  have hpre : ∀ t, e.pre t <+: E t := fun t => by
    rw [e.pre_eq_take (β := E t) (by rw [hElen]; omega) (fun n hn => he1 t n hn)]
    exact List.take_prefix _ _
  have hwfE : ∀ k, ClientWF (E k) := by
    intro k; induction k with
    | zero => simpa [E, rrLabels] using hwf
    | succ k ih =>
      simp only [E, rrLabels, (hstep k).1, ← List.append_assoc]
      exact clientWF_append_tau ih _
  have hfair : e.Fair := by
    intro p t hp
    by_cases h : (e.cfg (N + t)).pend p = none
    · obtain ⟨t', h1, -, r, hr⟩ := e.exists_ret_between (by omega : t ≤ N + t) hp h
      exact ⟨t', h1, by rw [hr]; rfl, by rw [hr]; trivial⟩
    · rw [hcfg, hpend_rr] at h
      obtain ⟨t', ht', hσ⟩ := rrSched_fair ps hps ((hpend p).1 h) t
      exact ⟨N + t', by omega, by rw [hlbl, ← hσ]; rfl, by rw [hlbl]; trivial⟩
  obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil ps hps
  have hpreN : e.pre N = α := by
    rw [e.pre_eq_take (β := E 0) (by rw [hElen]; omega) (fun n hn => he1 0 n hn)]
    simp [E, rrLabels, N]
  have hfin : ∃ S : Finset P, ∀ t, (e.lbl t).proc ∈ S := by
    refine ⟨(α.map Label.proc).toFinset ∪ ps.toFinset, fun t => ?_⟩
    by_cases ht : t < N
    · have hE0 : ∀ x ∈ E 0, x ∈ α := by simp [E, rrLabels]
      rw [he1 0 t (by rw [hElen]; omega)]
      exact Finset.mem_union_left _
        (List.mem_toFinset.2 (List.mem_map_of_mem (hE0 _ (List.getElem_mem _))))
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 ht)
      rw [hlbl]
      exact Finset.mem_union_right _ (List.mem_toFinset.2 (rrSched_mem ps hps s))
  obtain ⟨t', ht', q, r, hq⟩ := hdf e hfin (fun t => clientWF_of_prefix (hwfE t) (hpre t)) hfair N
    ⟨p₀, by
      have h0 := hcfg 0; simp only [Nat.add_zero] at h0; rw [h0]; exact (hpend p₀).2 hp₀⟩
    (fun s => by rw [hpreN]; exact hncs s)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht'
  rw [hlbl] at hq
  cases hq

/-- One round-robin step of a pending process: an internal step or a return. -/
lemma rr_step_cases (σ : ℕ → P) (F : Config mutexObj B P L) (t : ℕ)
    (hp : (rr J σ F t).pend (σ t) ≠ none) :
    (J.soloLabels (σ t) (rr J σ F t) 1 = [.tau (σ t)] ∧
      (rr J σ F (t + 1)).pend = (rr J σ F t).pend) ∨
    ∃ r, J.soloLabels (σ t) (rr J σ F t) 1 = [.ret (σ t) r] ∧
      (rr J σ F (t + 1)).pend = Function.update (rr J σ F t).pend (σ t) none := by
  have hr := J.runFrom_soloLabels (σ t) (rr J σ F t) 1
  rw [J.soloLabels_succ] at hr
  simp only [hp, ↓reduceIte, soloLabels] at hr
  cases hact : J.act (σ t) ((rr J σ F t).loc (σ t)) with
  | access i o k =>
    have hnl : J.nextLabel (rr J σ F t) (σ t) = .tau (σ t) := by simp [nextLabel, hact]
    rw [hnl, runFrom_singleton] at hr
    exact Or.inl ⟨by rw [J.soloLabels_succ]; simp [hp, hnl, soloLabels],
      by simpa [rr] using (step_tau hr).2.1⟩
  | ret r l =>
    have hnl : J.nextLabel (rr J σ F t) (σ t) = .ret (σ t) r := by simp [nextLabel, hact]
    rw [hnl, runFrom_singleton] at hr
    exact Or.inr ⟨r, by rw [J.soloLabels_succ]; simp [hp, hnl, soloLabels],
      by simpa [rr] using (step_ret hr).2.1⟩

/-- **Deadlock-freedom as progress**, execution form: some process of `ps` enters its critical
section in a continuation consisting of steps of `ps` only (no invocations). -/
theorem df_enter (hdf : DeadlockFreeFin J) {α : List (Label P mutexObj)}
    {F : Config mutexObj B P L} (hα : J.run α = some F) (hwf : ClientWF α)
    (hncs : ∀ s, ¬ InCS α s) (ps : List P) (hps : ps ≠ [])
    (hpend : ∀ s, F.pend s ≠ none ↔ s ∈ ps) (htry : ∀ p ∈ ps, regionOf α p = some .trying) :
    ∃ γ F', (∀ ℓ ∈ γ, ℓ.proc ∈ ps) ∧ (∀ s, opsOf γ s = []) ∧ J.runFrom F γ = some F' ∧
      ClientWF (α ++ γ) ∧ ∃ p ∈ ps, InCS (α ++ γ) p := by
  classical
  have h := df_progress hdf hα hwf hncs ps hps hpend
  set σ := rrSched ps hps
  set t₀ := Nat.find h
  have hmin : ∀ t < t₀, ∀ p ∈ ps, (rr J σ F t).pend p ≠ none := by
    intro t ht p hp hn; exact Nat.find_min h ht ⟨p, hp, hn⟩
  obtain ⟨p₁, hp₁, hp₁n⟩ := Nat.find_spec h
  change (rr J σ F t₀).pend p₁ = none at hp₁n
  obtain ⟨k, hk⟩ : ∃ k, t₀ = k + 1 := by
    rcases Nat.exists_eq_succ_of_ne_zero (n := t₀) (fun h0 => by
      rw [h0] at hp₁n; exact (hpend p₁).2 hp₁ hp₁n) with ⟨k, hk⟩
    exact ⟨k, hk⟩
  -- steps before `k` are internal
  have htau : ∀ t < k, J.soloLabels (σ t) (rr J σ F t) 1 = [.tau (σ t)] ∧
      (rr J σ F (t + 1)).pend = (rr J σ F t).pend := by
    intro t ht
    rcases rr_step_cases σ F t (hmin t (by omega) _ (rrSched_mem ps hps t)) with h1 | ⟨r, -, h2⟩
    · exact h1
    · exfalso
      apply hmin (t + 1) (by omega) (σ t) (rrSched_mem ps hps t)
      rw [h2]; simp
  have hlabs : ∀ t ≤ k, rrLabels J σ F t = (List.range t).map (fun i => .tau (σ i)) := by
    intro t ht; induction t with
    | zero => rfl
    | succ t ih => simp [rrLabels, ih (by omega), (htau t (by omega)).1, List.range_succ]
  -- step `k` is a return
  obtain ⟨r, hlk, hpk⟩ : ∃ r, J.soloLabels (σ k) (rr J σ F k) 1 = [.ret (σ k) r] ∧
      (rr J σ F (k + 1)).pend = Function.update (rr J σ F k).pend (σ k) none := by
    rcases rr_step_cases σ F k (hmin k (by omega) _ (rrSched_mem ps hps k)) with h1 | h2
    · exfalso
      rw [hk, h1.2] at hp₁n
      exact hmin k (by omega) p₁ hp₁ hp₁n
    · exact h2
  set γ := (List.range k).map (fun i => (Label.tau (σ i) : Label P mutexObj)) ++ [.ret (σ k) r]
  have hγ : rrLabels J σ F t₀ = γ := by
    rw [hk]; simp only [rrLabels, hlabs k le_rfl, hlk, γ]
  have hσk := rrSched_mem ps hps k
  have hregk := regionOf_append_taus α σ k
  refine ⟨γ, rr J σ F t₀, fun ℓ hℓ => ?_, fun s => ?_, by rw [← hγ]; exact runFrom_rrLabels J σ F t₀,
    fun s => ?_, σ k, hσk, ?_⟩
  · simp only [γ, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hℓ
    rcases hℓ with ⟨i, -, rfl⟩ | rfl
    · exact rrSched_mem ps hps i
    · exact hσk
  · simp [γ, opsOf, List.filterMap_map, Function.comp_def, Label.invOf]
  · rw [show α ++ γ = (α ++ (List.range k).map (fun i => (Label.tau (σ i) : Label P mutexObj))) ++
      [.ret (σ k) r] by simp [γ], regionOf_append_singleton, hregk]
    split_ifs with hs
    · simp only [Label.proc] at hs ⊢; subst hs; rw [htry _ hσk]; simp [Region.next]
    · exact hwf s
  · show regionOf (α ++ γ) (σ k) = some .cs
    rw [show α ++ γ = (α ++ (List.range k).map (fun i => (Label.tau (σ i) : Label P mutexObj))) ++
      [.ret (σ k) r] by simp [γ], regionOf_append_singleton, hregk, htry _ hσk]
    simp [Region.next, Label.proc]

end DF

section Unnamed

variable {ι V P L : Type} {v₀ : V} [DecidableEq P] [DecidableEq ι]
  {I : Impl mutexObj (RegFamily ι V v₀) P L}

lemma rr_const (J : Impl mutexObj (RegFamily ι V v₀) P L) {σ : ℕ → P} {p : P}
    (hσ : ∀ t, σ t = p) (C : Config mutexObj (RegFamily ι V v₀) P L) (t : ℕ) :
    rr J σ C t = (J.soloStep p)^[t] C := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ← ih, ← hσ t]; rfl

/-- The configuration after `p` invokes `lock` from the initial configuration. -/
lemma run_inv_lock {π : P → Equiv.Perm ι} (hall : ∀ p o, I.allowed p o) (p : P) :
    ∃ F, (I.unnamed π).run [.inv p .lock] = some F ∧ ∀ s, F.pend s ≠ none ↔ s ∈ [p] := by
  refine ⟨_, by simp only [run, runFrom_cons, runFrom_nil]
                rw [step_inv_eq_some (I := I.unnamed π) rfl (by simpa using hall p .lock)]; rfl,
    fun s => ?_⟩
  by_cases h : s = p <;> simp [h]

lemma regions_inv_lock (p : P) :
    ClientWF ([.inv p .lock] : List (Label P mutexObj)) ∧
    (∀ s, ¬ InCS ([.inv p .lock] : List (Label P mutexObj)) s) ∧
    regionOf ([.inv p .lock] : List (Label P mutexObj)) p = some .trying := by
  have h : ∀ s, regionOf ([.inv p .lock] : List (Label P mutexObj)) s =
      if s = p then some .trying else some .rem := by
    intro s
    by_cases hs : s = p
    · subst hs; simp [regionOf, Label.proc, Region.next]
    · simp [regionOf, Label.proc, Ne.symm hs, hs]
  refine ⟨fun s => by rw [h s]; split_ifs <;> simp, fun s hs => ?_, by rw [h p]; simp⟩
  unfold InCS at hs; rw [h s] at hs; split_ifs at hs <;> simp at hs

/-- Under deadlock-freedom, a process running `lock()` solo from the initial configuration enters
its critical section. -/
lemma solo_lock {π : P → Equiv.Perm ι} (hdf : DeadlockFreeFin (I.unnamed π))
    (hall : ∀ p o, I.allowed p o) (p : P) :
    ∃ β D, (∀ ℓ ∈ β, ℓ.proc = p) ∧ (I.unnamed π).run β = some D ∧ ClientWF β ∧ InCS β p := by
  obtain ⟨F, hF, hpend⟩ := run_inv_lock hall p
  obtain ⟨hwf, hncs, htry⟩ := regions_inv_lock p
  obtain ⟨γ, F', hγ, -, hr, hwf', p', hp', hcs⟩ :=
    df_enter hdf hF hwf hncs [p] (by simp) hpend (fun s hs => by simp at hs; subst hs; exact htry)
  simp only [List.mem_singleton] at hp' hγ; subst hp'
  refine ⟨_, F', fun ℓ hℓ => ?_, by rw [run, runFrom_append]; rw [run] at hF; rw [hF]; exact hr,
    hwf', hcs⟩
  rcases List.mem_append.1 hℓ with h | h
  · simp at h; rw [h]; rfl
  · exact hγ ℓ h

/-- If a process enters its critical section in an execution that leaves the memory in its
initial state, another process can run `lock()` solo afterwards and enter too. -/
lemma mutex_false_of_silent {π : P → Equiv.Perm ι} (hme : (I.unnamed π).MutualExclusion)
    (hdf : DeadlockFreeFin (I.unnamed π)) (hall : ∀ p o, I.allowed p o)
    {p : P} {α : List (Label P mutexObj)} {C : Config _ _ P L}
    (hα : (I.unnamed π).run α = some C) (hlab : ∀ ℓ ∈ α, ℓ.proc = p) (hwf : ClientWF α)
    (hcs : InCS α p) (hmem : C.mem = fun _ => v₀) {p' : P} (hp' : p' ≠ p) : False := by
  obtain ⟨β, D, hβ, hrun, hwfβ, hcsβ⟩ := solo_lock hdf hall p'
  have hαp' : ∀ ℓ ∈ α, ℓ.proc ≠ p' := fun ℓ hℓ h => hp' (h.symm.trans (hlab ℓ hℓ))
  have hβp : ∀ ℓ ∈ β, ℓ.proc ≠ p := fun ℓ hℓ h => hp' ((hβ ℓ hℓ).symm.trans h)
  have hag : AgreeOn {p'} (I.unnamed π).initCfg C :=
    (I.agreeOn_init_of_silent π hα hmem hαp').symm
  obtain ⟨D', hD', -⟩ := runFrom_agreeOn hag (fun ℓ hℓ => by simp [hβ ℓ hℓ]) hrun
  have hrun' : (I.unnamed π).run (α ++ β) = some D' := by
    rw [run, runFrom_append]; rw [run] at hα; rw [hα]; exact hD'
  have hreg : ∀ s, regionOf (α ++ β) s = if s = p then regionOf α s else regionOf β s := by
    intro s
    split_ifs with hs
    · subst hs
      simpa using regionOf_append_outer (α := []) (β := α) (γ := β) (by simp) hβp
    · have : ∀ ℓ ∈ α, ℓ.proc ≠ s := fun ℓ hℓ h => hs (h.symm.trans (hlab ℓ hℓ))
      simpa using regionOf_append_outer (α := α) (β := β) (γ := []) this (by simp)
  have hwf' : ClientWF (α ++ β) := fun s => by
    rw [hreg s]; split_ifs
    · exact hwf s
    · exact hwfβ s
  exact hp' (hme _ ⟨D', hrun'⟩ hwf' p' p (by unfold InCS; rw [hreg]; simp only [hp', ↓reduceIte]; exact hcsβ)
    (by unfold InCS; rw [hreg]; simp only [↓reduceIte]; exact hcs))

/-- Every process running `lock()` solo from the initial memory reads until it writes ("a process
must write at least once before it enters its critical section"). -/
lemma mutex_must_write (hme : (I.unnamed fun _ => 1).MutualExclusion)
    (hdf : DeadlockFreeFin (I.unnamed fun _ => 1)) (hall : ∀ p o, I.allowed p o)
    (h2 : ∀ p : P, ∃ p', p' ≠ p) (p : P) :
    ∃ j, (∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) .lock))) ∧
      I.IsWrite p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) .lock)) := by
  obtain ⟨j, hr, hw | ⟨r, l', hret⟩⟩ := I.unnamed_blind_cases_of_fin (fun _ => 1) p .lock
    (hall p .lock) (fun C₁ hC₁ => by
      obtain ⟨F, hF, hpend⟩ := run_inv_lock (π := fun _ => 1) hall p
      rw [hF] at hC₁; cases hC₁
      obtain ⟨hwf, hncs, -⟩ := regions_inv_lock p
      obtain ⟨t, p', hp', hn⟩ := df_progress hdf hF hwf hncs [p] (by simp) hpend
      simp only [List.mem_singleton] at hp'; subst hp'
      exact ⟨t, by rwa [rr_const _ (p := p') (fun t => by simp [rrSched]) C₁ t] at hn⟩)
  · exact ⟨j, hr, hw⟩
  · exfalso
    have hrun := I.unnamed_run_silent (fun _ => 1) (hall p .lock) hr hret
    set α : List (Label P mutexObj) := (.inv p .lock :: List.replicate j (.tau p)) ++ [.ret p r]
    have hlab : ∀ ℓ ∈ α, ℓ.proc = p := by
      intro ℓ hℓ
      simp only [α, List.mem_append, List.mem_cons, List.mem_replicate] at hℓ
      rcases hℓ with (rfl | ⟨-, rfl⟩) | rfl | h <;> first | rfl | simp at h
    have hregp : regionOf α p = some .cs := by
      have e : α = ([.inv p .lock] ++ (List.range j).map (fun _ => (Label.tau p : Label P mutexObj)))
          ++ [.ret p r] := by simp [α, List.map_const']
      rw [e, regionOf_append_singleton, regionOf_append_taus _ (fun _ => p)]
      simp [regionOf, Label.proc, Region.next]
    have hwf : ClientWF α := fun s => by
      by_cases hs : s = p
      · subst hs; rw [hregp]; simp
      · rw [regionOf_of_forall_ne (fun ℓ hℓ h => hs (h.symm.trans (hlab ℓ hℓ)))]; simp
    obtain ⟨p', hp'⟩ := h2 p
    exact mutex_false_of_silent hme hdf hall hrun hlab hwf hregp rfl hp'

/-- The core of Theorem 6.2 (cf. `consensus_impossible`). -/
theorem mutex_impossible (I : Impl mutexObj (RegFamily ι V v₀) P L)
    (hall : ∀ p o, I.allowed p o) (h2 : ∃ p p' : P, p ≠ p')
    (hP : ∀ (q : P) (W : Finset ι), ∃ ps : List P, ps.Nodup ∧ q ∉ ps ∧ ps.length = W.card) :
    ¬ ∀ π, (I.unnamed π).MutualExclusion ∧ DeadlockFreeFin (I.unnamed π) := by
  intro H
  obtain ⟨q, q', hqq'⟩ := h2
  have h2' : ∀ p : P, ∃ p', p' ≠ p := fun p => by
    by_cases h : q = p
    · exact ⟨q', h ▸ hqq'.symm⟩
    · exact ⟨q, h⟩
  have hw := mutex_must_write (H fun _ => 1).1 (H fun _ => 1).2 hall h2'
  -- `q` runs `lock()` alone and enters its critical section
  obtain ⟨y, Cy, hyq, hy, hwfy, hcsy⟩ := solo_lock (H fun _ => 1).2 hall q
  obtain ⟨W, hW⟩ := runFrom_exists_finset _ hy
  have hW' : ∀ i ∉ W, Cy.mem i = v₀ := fun i hi => hW i hi
  by_cases hW0 : W = ∅
  · exact mutex_false_of_silent (H fun _ => 1).1 (H fun _ => 1).2 hall hy hyq hwfy hcsy
      (funext fun i => hW' i (by simp [hW0])) hqq'.symm
  obtain ⟨ps, hnd, hqps, hlen⟩ := hP q W
  obtain ⟨π, -, x, bw, C, D, hlab, hops, hresps, hC, hD, hag, -, -⟩ :=
    covering_construction q hyq hy W hW' ps hnd hqps hlen (fun _ => .lock) (fun p => hall p _) hw
  have hps : ps ≠ [] := by
    intro h; rw [h] at hlen; exact hW0 (Finset.card_eq_zero.1 hlen.symm)
  set J := I.unnamed π
  -- the configuration after the block write: exactly `ps` are trying
  have hpendC : ∀ s, C.pend s ≠ none ↔ s ∈ ps := by
    intro s
    have hc := J.run_counts hC s
    rw [hops s, hresps s] at hc
    by_cases hs : s ∈ ps
    · simp only [hs, ↓reduceIte] at hc; simp only [hs, iff_true]; rcases hc with h | h <;> simp_all
    · simp only [hs, ↓reduceIte] at hc; simp only [hs, iff_false, not_not]
      rcases hc with h | h <;> simp_all
  have hregC : ∀ s, regionOf (x ++ bw) s = if s ∈ ps then some .trying else some .rem := by
    intro s
    have := regionOf_of_ops (x ++ bw) (hresps s)
    split_ifs with hs
    · exact this.2 (by simp [hops s, hs])
    · exact this.1 (by simp [hops s, hs])
  obtain ⟨γ, E, hγ, -, hE, hwfγ, p₀, hp₀, hcs₀⟩ := df_enter (H π).2 hC
    (fun s => by rw [hregC s]; split_ifs <;> simp)
    (fun s hs => by unfold InCS at hs; rw [hregC s] at hs; split_ifs at hs <;> simp at hs)
    ps hps hpendC (fun p hp => by rw [hregC p]; simp [hp])
  have hp₀q : p₀ ≠ q := fun h => hqps (h ▸ hp₀)
  -- with `q` inserted before the block write
  obtain ⟨E', hE', -⟩ := runFrom_agreeOn hag (fun ℓ hℓ => hγ ℓ hℓ) hE
  have hρ : J.run (x ++ y ++ bw ++ γ) = some E' := by
    rw [run, runFrom_append]; rw [run] at hD; rw [hD]; exact hE'
  have hxq : ∀ ℓ ∈ x, ℓ.proc ≠ q := fun ℓ hℓ h => hqps (h ▸ hlab ℓ (by simp [hℓ]))
  have hbγq : ∀ ℓ ∈ bw ++ γ, ℓ.proc ≠ q := fun ℓ hℓ h => by
    rcases List.mem_append.1 hℓ with h' | h'
    · exact hqps (h ▸ hlab ℓ (by simp [h']))
    · exact hqps (h ▸ hγ ℓ h')
  have hreg : ∀ s, regionOf (x ++ y ++ bw ++ γ) s =
      if s = q then regionOf y s else regionOf (x ++ bw ++ γ) s := by
    intro s
    rw [List.append_assoc (x ++ y) bw γ]
    split_ifs with hs
    · subst hs; exact regionOf_append_outer hxq hbγq
    · have : ∀ ℓ ∈ y, ℓ.proc ≠ s := fun ℓ hℓ h => hs (h.symm.trans (hyq ℓ hℓ))
      rw [regionOf_append_middle this, ← List.append_assoc]
  have hwfρ : ClientWF (x ++ y ++ bw ++ γ) := fun s => by
    rw [hreg s]; split_ifs
    · exact hwfy s
    · exact hwfγ s
  exact hp₀q ((H π).1 _ ⟨E', hρ⟩ hwfρ p₀ q
    (by unfold InCS; rw [hreg]; simp only [hp₀q, ↓reduceIte]; exact hcs₀)
    (by unfold InCS; rw [hreg]; simp only [↓reduceIte]; exact hcsy))

/-- **Theorem 6.2** of [Taubenfeld, PODC 2017]. There is no deadlock-free mutual exclusion
algorithm using unnamed registers when the number of processes is not a priori known: for an
unbounded set `P` of potential participants, every read/write algorithm violates mutual exclusion,
or deadlock-freedom in some execution with finitely many participants (`DeadlockFreeFin`), for
some numbering `π` of the registers. -/
theorem theorem_6_2 [Infinite P] (I : Impl mutexObj (RegFamily ι V v₀) P L)
    (hall : ∀ p o, I.allowed p o) :
    ∃ π, ¬ ((I.unnamed π).MutualExclusion ∧ DeadlockFreeFin (I.unnamed π)) := by
  by_contra h
  push Not at h
  obtain ⟨p, p', hpp'⟩ := exists_pair_ne P
  exact mutex_impossible I hall ⟨p, p', hpp'⟩ exists_ps_of_infinite fun π => h π

/-- Theorem 6.2 with CSLib's `Impl.DeadlockFree` (all fair executions, also those with infinitely
many participants: the paper's "unbounded" model). -/
theorem theorem_6_2_unbounded [Infinite P] (I : Impl mutexObj (RegFamily ι V v₀) P L)
    (hall : ∀ p o, I.allowed p o) :
    ∃ π, ¬ ((I.unnamed π).MutualExclusion ∧ (I.unnamed π).DeadlockFree) := by
  obtain ⟨π, hπ⟩ := theorem_6_2 I hall
  exact ⟨π, fun h => hπ ⟨h.1, deadlockFreeFin_of_deadlockFree h.2⟩⟩

/-- The same covering argument for a known number `n ≥ 2` of processes: they need at least `n`
unnamed registers (not stated in the paper; for named registers this is Burns–Lynch). -/
theorem mutex_card_lt [Fintype P] [Fintype ι] (I : Impl mutexObj (RegFamily ι V v₀) P L)
    (hn : 2 ≤ Fintype.card P) (hm : Fintype.card ι ≤ Fintype.card P - 1)
    (hall : ∀ p o, I.allowed p o) :
    ∃ π, ¬ ((I.unnamed π).MutualExclusion ∧ (I.unnamed π).DeadlockFree) := by
  by_contra h
  push Not at h
  obtain ⟨p, p', hpp'⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
  exact mutex_impossible I hall ⟨p, p', hpp'⟩ (exists_ps_of_card_lt (by omega)) fun π =>
    ⟨(h π).1, deadlockFreeFin_of_deadlockFree (h π).2⟩

end Unnamed

end Podc.MemoryAnonymousCoordination
