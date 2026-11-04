import Papers.PODC2011.AtMostOnceEffectiveness.Progress

/-!
# Lemma 4.3: `KK_β` is wait-free (for `β ≥ m`)

We show that every run of `KK_β` takes only finitely many steps (`lemma_4_3`): there is no
infinite execution at all, fair or not (an infinite execution is fair for the set of processes
that take finitely many steps, so this is the paper's "no infinite fair execution").

Proof outline (following the paper, with one repair, see below). Suppose a run takes infinitely
many steps; let `S` be the set of processes stepping infinitely often (`S ≠ ∅`).
1. The lines of `done` only grow and are bounded, so after some time `K0` they are constant, and
   the processes outside `S` take no more steps (`After`). Then no process of `S` is ever in
   status `do`/`done`/`end` after `K0` (`After.status_ok`): its next step would perform or record
   a job, or it could not step.
2. Every process of `S` keeps cycling `compNext → setNext → gatherTry* → gatherDone* → check →
   compNext` (a measure `mu` increases at every step except `check → compNext`).
3. Stable predicates (once true after `K0`, true forever): `DONE_p = recorded` (all recorded jobs);
   `TRY_p` contains the (frozen) `next` values of all processes outside `S` (`TryFull`);
   `NEXT_p` and `next_p` have rank `≥ k_p` in `POOL` (`GoodNext`), where
   `POOL = (J \ recorded) \ {next_q | q ∉ S}` and `k_p = kIdx m p |J \ recorded|`.
4. For the smallest `p₀ ∈ S`, the element `x₀` of rank `k_{p₀}` of `POOL` is never in `TRY_{p₀}`
   (other processes of `S` hold jobs of higher rank since `kIdx` is strictly increasing in `p`;
   processes outside `S` hold jobs outside `POOL`), so `p₀` eventually picks `x₀` and passes
   `check` — contradiction with 1.

**Repair.** The paper defines `POOL_α = J \ (J_α ∪ STUCK_α)` with `STUCK_α` the jobs held by
*crashed* processes only and claims that no process other than `p₀` ever holds `x₀`. A process
that *terminated* (status `end`) keeps its last value in `next`, which may be an unperformed job
of `POOL_α`, possibly `x₀`. We exclude the values held by all processes outside `S` (crashed or
terminated) from `POOL`; with this change the argument goes through.
-/

set_option linter.unusedSectionVars false

namespace Podc.AtMostOnceEffectiveness

open Function

variable {m n β : ℕ}

/-! ## Monotonicity of the `done` lines along runs -/

section Lines

variable {C C' : Config m Reg ℕ LState} {p : Fin m}

lemma reachable_step_line (hβ : 1 ≤ β) (hC : (kk m n β).Reachable C)
    (hs : (kk m n β).step C p = some C') (q : Fin m) : ∃ l, line C' q = line C q ++ l := by
  have hI := Inv.of_reachable hβ hC
  have hs' := step_inv hs
  by_cases hqp : q = p
  · subst hqp; exact ⟨_, hs'.line_self (hI.posOwn q)⟩
  · exact ⟨[], by rw [hs'.line_ne hqp, List.append_nil]⟩

lemma Alg.Run.line_mono (hβ : 1 ≤ β) (r : (kk m n β).Run) {k k' : ℕ} (h : k ≤ k') (q : Fin m) :
    ∃ l, line (r.cfg k') q = line (r.cfg k) q ++ l := by
  induction k', h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ k' hk ih =>
    obtain ⟨l, hl⟩ := ih
    have h := r.cfg_succ k'
    cases hk' : r.ev k' with
    | none =>
      rw [hk'] at h; simp only [Alg.stepO, Option.some.injEq] at h
      exact ⟨l, by rw [← h, hl]⟩
    | some p =>
      rw [hk'] at h
      obtain ⟨l', hl'⟩ := reachable_step_line hβ (r.reachable k') h q
      exact ⟨l ++ l', by rw [hl', hl, List.append_assoc]⟩

/-- Total length of the `done` lines. -/
def totalLines (C : Config m Reg ℕ LState) : ℕ := ∑ q : Fin m, (line C q).length

lemma eventually_const_of_mono_bdd (f : ℕ → ℕ) (hf : Monotone f) (B : ℕ) (hB : ∀ k, f k ≤ B) :
    ∃ K, ∀ k ≥ K, f k = f K := by
  have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨k, rfl⟩; exact hB k⟩
  obtain ⟨K, hK⟩ := Nat.sSup_mem hne hbdd
  refine ⟨K, fun k hk => le_antisymm ?_ (hf hk)⟩
  rw [hK]; exact le_csSup hbdd ⟨k, rfl⟩

/-- The `done` lines are eventually constant. -/
lemma Alg.Run.exists_lines_const (hβ : 1 ≤ β) (r : (kk m n β).Run) :
    ∃ K, ∀ k ≥ K, ∀ q, line (r.cfg k) q = line (r.cfg K) q := by
  have hmono : Monotone (fun k => totalLines (r.cfg k)) := by
    intro k k' h
    apply Finset.sum_le_sum
    intro q _
    obtain ⟨l, hl⟩ := r.line_mono hβ h q
    simp [hl]
  obtain ⟨K, hK⟩ := eventually_const_of_mono_bdd _ hmono (m * n) (by
    intro k
    have hI := Inv.of_reachable hβ (r.reachable k)
    calc totalLines (r.cfg k) ≤ ∑ _q : Fin m, n :=
          Finset.sum_le_sum (fun q _ => hI.line_length_le q)
      _ = m * n := by simp)
  refine ⟨K, fun k hk q => ?_⟩
  have h1 := hK k hk
  simp only [totalLines] at h1
  have hle : ∀ q, (line (r.cfg K) q).length ≤ (line (r.cfg k) q).length := by
    intro q; obtain ⟨l, hl⟩ := r.line_mono hβ hk q; simp [hl]
  have heq : ∀ q ∈ Finset.univ, (line (r.cfg k) q).length = (line (r.cfg K) q).length :=
    fun q hq => ((Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).mp h1.symm q hq).symm
  obtain ⟨l, hl⟩ := r.line_mono hβ hk q
  have := heq q (Finset.mem_univ _)
  rw [hl] at this ⊢
  simp only [List.length_append, add_eq_left, List.length_eq_zero_iff] at this
  simp [this]

end Lines

/-! ## Runs after stabilisation -/

lemma KStep.status_of_doIt {C C' : Config m Reg ℕ LState} {p : Fin m}
    (hs : KStep m n β C p C') (h : (C.loc p).status = .doIt) : (C'.loc p).status = .done := by
  cases hs <;> simp_all

lemma KStep.not_finished {C C' : Config m Reg ℕ LState} {p : Fin m}
    (hs : KStep m n β C p C') (h : (C.loc p).status = .finished) : False := by
  cases hs <;> simp_all

section After

variable (r : (kk m n β).Run)

lemma Alg.Run.kstep_of_ev {k : ℕ} {p : Fin m} (h : r.ev k = some p) :
    KStep m n β (r.cfg k) p (r.cfg (k + 1)) := by
  have := r.cfg_succ k
  rw [h] at this
  exact step_inv this

lemma Alg.Run.cfg_succ_of_none {k : ℕ} (h : r.ev k = none) : r.cfg (k + 1) = r.cfg k := by
  have := r.cfg_succ k
  rw [h] at this
  simp only [Alg.stepO, Option.some.injEq] at this
  exact this.symm

lemma Alg.Run.loc_succ_of_ne {k : ℕ} {p : Fin m} (h : r.ev k ≠ some p) :
    (r.cfg (k + 1)).loc p = (r.cfg k).loc p := by
  cases hk : r.ev k with
  | none => rw [r.cfg_succ_of_none hk]
  | some q =>
    have hq : p ≠ q := fun e => h (by rw [hk, e])
    exact (r.kstep_of_ev hk).loc_ne hq

lemma Alg.Run.loc_const_of_ne {t t' : ℕ} {p : Fin m} (htt : t ≤ t')
    (h : ∀ j, t ≤ j → j < t' → r.ev j ≠ some p) : (r.cfg t').loc p = (r.cfg t).loc p := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ t' ht ih =>
    rw [r.loc_succ_of_ne (h t' ht (by omega)), ih (fun j hj hj' => h j hj (by omega))]

/-- The run after stabilisation at time `K0`: the processes of `S` step infinitely often, the
others do not step any more, and the `done` lines are constant. -/
structure After (S : Finset (Fin m)) (K0 : ℕ) : Prop where
  inf : ∀ p ∈ S, ∀ k, ∃ k' ≥ k, r.ev k' = some p
  quiet : ∀ k ≥ K0, ∀ q, r.ev k = some q → q ∈ S
  lines : ∀ k ≥ K0, ∀ q, line (r.cfg k) q = line (r.cfg K0) q

variable {r} {S : Finset (Fin m)} {K0 : ℕ}

/-- The next step of a process of `S`. -/
lemma After.next_step (hA : After r S K0) {p : Fin m} (hp : p ∈ S) (t : ℕ) :
    ∃ t' ≥ t, r.ev t' = some p ∧ (r.cfg t').loc p = (r.cfg t).loc p := by
  classical
  have hex : ∃ t', t ≤ t' ∧ r.ev t' = some p := by
    obtain ⟨t', h1, h2⟩ := hA.inf p hp t; exact ⟨t', h1, h2⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  apply r.loc_const_of_ne (Nat.find_spec hex).1
  intro j hj hj' he
  exact Nat.find_min hex hj' ⟨hj, he⟩

lemma After.loc_frozen (hA : After r S K0) {q : Fin m} (hq : q ∉ S) {k : ℕ} (hk : K0 ≤ k) :
    (r.cfg k).loc q = (r.cfg K0).loc q :=
  r.loc_const_of_ne hk (fun j hj _ he => hq (hA.quiet j hj q he))

lemma After.mem_next_frozen (hA : After r S K0) {q : Fin m} (hq : q ∉ S) {k : ℕ} (hk : K0 ≤ k) :
    (r.cfg k).mem (.next q) = (r.cfg K0).mem (.next q) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih]
    cases he : r.ev k with
    | none => rw [r.cfg_succ_of_none he]
    | some p =>
      have hpq : q ≠ p := fun e => hq (e ▸ hA.quiet k hk p he)
      exact (r.kstep_of_ev he).mem_next_ne _ (val_ne_of_ne hpq)

lemma After.recorded_eq (hA : After r S K0) {k : ℕ} (hk : K0 ≤ k) :
    recorded (r.cfg k) = recorded (r.cfg K0) := by
  unfold recorded; simp_rw [hA.lines k hk]

variable (hβ : 1 ≤ β)
include hβ

/-- After `K0`, no process of `S` is busy or terminated. -/
lemma After.status_ok (hA : After r S K0) {p : Fin m} (hp : p ∈ S) {k : ℕ} (hk : K0 ≤ k) :
    ((r.cfg k).loc p).status ≠ .doIt ∧ ((r.cfg k).loc p).status ≠ .done ∧
      ((r.cfg k).loc p).status ≠ .finished := by
  have hdone : ∀ k, K0 ≤ k → ((r.cfg k).loc p).status ≠ .done := by
    intro k hk h
    obtain ⟨t, ht, he, hloc⟩ := hA.next_step hp k
    have hs := r.kstep_of_ev he
    have hI := Inv.of_reachable hβ (r.reachable t)
    have hl := hs.line_self (hI.posOwn p)
    rw [hA.lines (t + 1) (by omega), hA.lines t (by omega)] at hl
    have : pend (r.cfg t) p = [] := by simpa using hl.symm
    simp [pend, hloc, h] at this
  refine ⟨fun h => ?_, hdone k hk, fun h => ?_⟩
  · obtain ⟨t, ht, he, hloc⟩ := hA.next_step hp k
    have hs := r.kstep_of_ev he
    rw [← hloc] at h
    exact hdone (t + 1) (by omega) (hs.status_of_doIt h)
  · obtain ⟨t, ht, he, hloc⟩ := hA.next_step hp k
    have hs := r.kstep_of_ev he
    rw [← hloc] at h
    exact hs.not_finished h

/-- The progress measure of a process within one iteration. -/
def mu (m n : ℕ) (s : LState) : ℕ :=
  match s.status with
  | .compNext => 0
  | .setNext => 1
  | .gatherTry => 2 + s.q
  | .gatherDone => 2 + m + s.q * (n + 2) + min (s.pos s.q) (n + 1)
  | .check => 2 + m + m * (n + 2)
  | _ => 0

omit hβ in
lemma mu_le {s : LState} (hq : s.status = .gatherTry ∨ s.status = .gatherDone → s.q < m) :
    mu m n s ≤ 2 + m + m * (n + 2) := by
  unfold mu
  split
  · omega
  · omega
  · rename_i h; have := hq (Or.inl h); omega
  · rename_i h; have := hq (Or.inr h)
    have : s.q * (n + 2) + (n + 2) ≤ m * (n + 2) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ this
    omega
  · omega
  · omega

omit hβ in
lemma KStep.mu_lt {C C' : Config m Reg ℕ LState} {p : Fin m} (hI : Inv m n C)
    (hs : KStep m n β C p C') (h1 : (C.loc p).status ≠ .check)
    (h2 : (C'.loc p).status ≠ .finished) (h3 : (C.loc p).status ≠ .doIt)
    (h4 : (C.loc p).status ≠ .done) : mu m n (C.loc p) < mu m n (C'.loc p) := by
  cases hs with
  | compNext h hb => simp [mu, h]
  | finish h hb => simp at h2
  | setNext h => simp [mu, h]; omega
  | tryRead h hq =>
    have hqm := hI.qlt p (Or.inl h)
    simp only [update_self]
    unfold mu LState.adv; split_ifs <;> simp [h] <;> omega
  | trySkip h hq =>
    have hqm := hI.qlt p (Or.inl h)
    simp only [update_self]
    unfold mu LState.adv; split_ifs <;> simp [h] <;> omega
  | doneRead h hq hp hv =>
    simp only [update_self]
    unfold mu; simp [h]; omega
  | doneAdv h hq =>
    have hqm := hI.qlt p (Or.inr h)
    simp only [update_self]
    unfold mu LState.adv
    split_ifs with h3
    · simp only [h]
      have : (C.loc p).q * (n + 2) + (n + 2) ≤ ((C.loc p).q + 1) * (n + 2) := by ring_nf; omega
      omega
    · simp only [h]
      have : (C.loc p).q * (n + 2) + (n + 2) ≤ m * (n + 2) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
  | checkOk h _ _ => exact absurd h h1
  | checkFail h _ => exact absurd h h1
  | perform h => exact absurd h h3
  | writeDone h => exact absurd h h4

omit hβ in
lemma KStep.status_ne_compNext {C C' : Config m Reg ℕ LState} {p : Fin m}
    (hs : KStep m n β C p C') (h1 : (C.loc p).status ≠ .check) (h2 : (C.loc p).status ≠ .done) :
    (C'.loc p).status ≠ .compNext := by
  cases hs with
  | tryRead h hq => simp only [update_self, adv_status]; split_ifs <;> simp [h]
  | trySkip h hq => simp only [update_self, adv_status]; split_ifs <;> simp [h]
  | doneAdv h hq => simp only [update_self, adv_status]; split_ifs <;> simp [h]
  | _ => simp_all

omit hβ in
lemma KStep.check_result {C C' : Config m Reg ℕ LState} {p : Fin m}
    (hs : KStep m n β C p C') (h : (C.loc p).status = .check) :
    (C'.loc p).status = .doIt ∨ (C'.loc p).status = .compNext := by
  cases hs <;> simp_all

/-- From any time after `K0`, a process of `S` reaches `check`; if it is not at `compNext`, its
`NEXT` does not change on the way. -/
lemma After.reach_check (hA : After r S K0) {p : Fin m} (hp : p ∈ S) {t : ℕ} (ht : K0 ≤ t) :
    ∃ t' ≥ t, ((r.cfg t').loc p).status = .check ∧
      (((r.cfg t).loc p).status ≠ .compNext → ((r.cfg t').loc p).nxt = ((r.cfg t).loc p).nxt) := by
  suffices H : ∀ d, ∀ t, K0 ≤ t → 2 + m + m * (n + 2) - mu m n ((r.cfg t).loc p) = d →
      ∃ t' ≥ t, ((r.cfg t').loc p).status = .check ∧
      (((r.cfg t).loc p).status ≠ .compNext → ((r.cfg t').loc p).nxt = ((r.cfg t).loc p).nxt) from
    H _ t ht rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro t ht hd
  by_cases hc : ((r.cfg t).loc p).status = .check
  · exact ⟨t, le_rfl, hc, fun _ => rfl⟩
  obtain ⟨t1, ht1, he, hloc⟩ := hA.next_step hp t
  have hs := r.kstep_of_ev he
  have hI := Inv.of_reachable hβ (r.reachable t1)
  have hI' := Inv.of_reachable hβ (r.reachable (t1 + 1))
  have hok1 := hA.status_ok hβ hp (k := t1) (by omega)
  have hok2 := hA.status_ok hβ hp (k := t1 + 1) (by omega)
  have hc1 : ((r.cfg t1).loc p).status ≠ .check := by rw [hloc]; exact hc
  have hlt := hs.mu_lt hI hc1 hok2.2.2 hok1.1 hok1.2.1
  have hle := mu_le (n := n) (hI'.qlt p)
  rw [hloc] at hlt
  obtain ⟨t', ht', hc', hn'⟩ := ih _ (by omega) (t1 + 1) (by omega) rfl
  refine ⟨t', by omega, hc', fun hne => ?_⟩
  rw [hn' (hs.status_ne_compNext hc1 hok1.2.1), hs.nxt_eq (by rw [hloc]; exact hne), hloc]

/-- From any time after `K0`, a process of `S` reaches `compNext`. -/
lemma After.reach_compNext (hA : After r S K0) {p : Fin m} (hp : p ∈ S) {t : ℕ} (ht : K0 ≤ t) :
    ∃ t' ≥ t, ((r.cfg t').loc p).status = .compNext := by
  obtain ⟨t1, ht1, hc, -⟩ := hA.reach_check hβ hp ht
  obtain ⟨t2, ht2, he, hloc⟩ := hA.next_step hp t1
  have hs := r.kstep_of_ev he
  rw [← hloc] at hc
  rcases hs.check_result hc with h | h
  · exact absurd h (hA.status_ok hβ hp (k := t2 + 1) (by omega)).1
  · exact ⟨t2 + 1, by omega, h⟩

omit hβ in
/-- Stable predicates: true at some time `t ≥ K0` and preserved after `K0` ⇒ true from `t` on. -/
lemma stable_of {P : Config m Reg ℕ LState → Prop} {t : ℕ} (ht : K0 ≤ t) (h0 : P (r.cfg t))
    (hstep : ∀ k ≥ K0, P (r.cfg k) → P (r.cfg (k + 1))) : ∀ k ≥ t, P (r.cfg k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h0
  | succ k hk ih => exact hstep k (by omega) ih

omit hβ in
lemma KStep.check_ok {C C' : Config m Reg ℕ LState} {p : Fin m}
    (hs : KStep m n β C p C') (h : (C.loc p).status = .check)
    (h1 : (C.loc p).nxt ∉ (C.loc p).tryS) (h2 : (C.loc p).nxt ∉ (C.loc p).doneS) :
    (C'.loc p).status = .doIt := by
  cases hs <;> simp_all

omit hβ in
/-- A process that leaves line `a` in `gatherDone` (empty cell or end of line) knows the whole
line. -/
lemma Inv.line_subset_doneS {C : Config m Reg ℕ LState} (hI : Inv m n C) {p a : Fin m}
    (ha : a ≠ p) (hq : ¬ ((C.loc p).pos a ≤ n ∧ 0 < C.mem (.done a ((C.loc p).pos a)))) :
    ∀ x ∈ line C a, x ∈ (C.loc p).doneS := by
  obtain ⟨r1, r2, r3⟩ := hI.reader p a ha
  have hlen : (line C a).length ≤ (C.loc p).pos a - 1 := by
    by_contra hc; push Not at hc
    apply hq
    have hj := hI.lineJ a _ (List.getElem_mem hc)
    rw [hI.line_getElem a _ hc, show (C.loc p).pos ↑a - 1 + 1 = (C.loc p).pos a by omega] at hj
    have := hI.line_length_le a
    simp only [Finset.mem_Icc] at hj
    constructor <;> omega
  intro x hx
  exact r3 _ (by rw [List.take_of_length_le hlen]; exact hx)

omit hβ in
/-- Strict monotonicity of the chosen rank in the process identifier. -/
lemma kIdx_lt {m p q F : ℕ} (hpq : p < q) (hqm : q < m) : kIdx m p F < kIdx m q F := by
  unfold kIdx
  have hm : 0 < m := by omega
  split_ifs with h
  · set x := F - (m - 1)
    have hx : m ≤ x := by omega
    have : p * x / m + 1 ≤ q * x / m := by
      rw [← Nat.add_div_right _ hm]
      apply Nat.div_le_div_right
      have : p * x + x ≤ q * x := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hpq
      omega
    omega
  · omega

omit hβ in
lemma kIdx_pos (m p F : ℕ) : 1 ≤ kIdx m p F := by unfold kIdx; split_ifs <;> simp

omit hβ in
/-- The rank chosen by `compNext` exists: `kIdx ≤ |FREE \ TRY|`. -/
lemma kIdx_le_avail {m p F A β : ℕ} (hp : p < m) (hmβ : m ≤ β) (hA : β ≤ A)
    (hFA : F ≤ A + (m - 1)) : kIdx m p F ≤ A := by
  unfold kIdx
  split_ifs with h
  · obtain ⟨x, hxd⟩ : ∃ x, x = F - (m - 1) := ⟨_, rfl⟩
    rw [← hxd]
    have hx : m ≤ x := by omega
    have h1 : p * x / m ≤ (m - 1) * x / m :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
    have h2 : (m - 1) * x / m < x := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : (m - 1) * x < m * x := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      linarith
    omega
  · omega

/-- The case analysis of a step after `K0`. -/
lemma After.step_cases (hA : After r S K0) {k : ℕ} (hk : K0 ≤ k) :
    r.cfg (k + 1) = r.cfg k ∨ ∃ q ∈ S, KStep m n β (r.cfg k) q (r.cfg (k + 1)) := by
  cases he : r.ev k with
  | none => exact Or.inl (r.cfg_succ_of_none he)
  | some q => exact Or.inr ⟨q, hA.quiet k hk q he, r.kstep_of_ev he⟩

/-- `p` knows the lines it has passed in the current `gatherDone` loop. -/
def PassInv (C : Config m Reg ℕ LState) (p : Fin m) : Prop :=
  ((C.loc p).status = .gatherDone → ∀ a : Fin m, a ≠ p → a.val < (C.loc p).q →
      ∀ x ∈ line C a, x ∈ (C.loc p).doneS) ∧
  ((C.loc p).status = .check → ∀ a : Fin m, a ≠ p → ∀ x ∈ line C a, x ∈ (C.loc p).doneS)

lemma After.passInv_step (hA : After r S K0) (p : Fin m) {k : ℕ} (hk : K0 ≤ k)
    (h : PassInv (r.cfg k) p) : PassInv (r.cfg (k + 1)) p := by
  have hl : ∀ a, line (r.cfg (k + 1)) a = line (r.cfg k) a := fun a => by
    rw [hA.lines _ (by omega), hA.lines _ hk]
  have hI := Inv.of_reachable hβ (r.reachable k)
  rcases hA.step_cases hβ hk with he | ⟨q, -, hs⟩
  · rw [he]; exact h
  unfold PassInv at h ⊢
  simp only [hl]
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨h1, h2⟩ := h
    generalize r.cfg (k + 1) = C' at hs ⊢
    cases hs with
    | tryRead hst hq =>
      simp only [update_self, adv_status, adv_q, adv_doneS]
      constructor <;> intro hs' <;> split_ifs at hs' ⊢ <;> simp_all
    | trySkip hst hq =>
      simp only [update_self, adv_status, adv_q, adv_doneS]
      constructor <;> intro hs' <;> split_ifs at hs' ⊢ <;> simp_all
    | doneRead hst hq hp hv =>
      simp only [update_self]
      refine ⟨fun _ a ha hlt x hx => Finset.mem_insert_of_mem (h1 hst a ha hlt x hx), ?_⟩
      intro hc; simp [hst] at hc
    | doneAdv hst hq =>
      simp only [update_self, adv_status, adv_q, adv_doneS]
      have hqm := hI.qlt q (Or.inr hst)
      have hnew : ∀ a : Fin m, a ≠ q → a.val = (r.cfg k |>.loc q).q →
          ∀ x ∈ line (r.cfg k) a, x ∈ ((r.cfg k).loc q).doneS := by
        intro a ha haq
        apply hI.line_subset_doneS ha
        rcases hq with hq | hq
        · exact absurd (Fin.ext (haq.trans hq)) ha
        · rwa [haq]
      constructor
      · intro hs' a ha hlt
        split_ifs at hs' hlt with h3
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | hlt
          · exact h1 hst a ha hlt
          · exact hnew a ha hlt
      · intro hs' a ha
        split_ifs at hs' with h3
        · simp [hst] at hs'
        · rcases Nat.lt_or_ge a.val ((r.cfg k).loc q).q with hlt | hlt
          · exact h1 hst a ha hlt
          · exact hnew a ha (by have := a.isLt; omega)
    | _ => simp_all
  · rw [hs.loc_ne (Ne.symm hqp)]; exact h

lemma After.eventually_passInv (hA : After r S K0) {p : Fin m} (hp : p ∈ S) :
    ∃ T ≥ K0, ∀ k ≥ T, PassInv (r.cfg k) p := by
  obtain ⟨t, ht, hc⟩ := hA.reach_compNext hβ hp (le_refl K0)
  refine ⟨t, ht, stable_of (P := fun C => PassInv C p) ht ?_
    (fun k hk h => hA.passInv_step hβ p hk h)⟩
  unfold PassInv; simp [hc]

/-- `p` knows all recorded jobs. -/
def Synced (C : Config m Reg ℕ LState) (p : Fin m) : Prop := recorded C ⊆ (C.loc p).doneS

lemma After.synced_step (hA : After r S K0) (p : Fin m) {k : ℕ} (hk : K0 ≤ k)
    (h : Synced (r.cfg k) p) : Synced (r.cfg (k + 1)) p := by
  unfold Synced at h ⊢
  rw [hA.recorded_eq (k := k + 1) (by omega), ← hA.recorded_eq hk]
  rcases hA.step_cases hβ hk with he | ⟨q, -, hs⟩
  · rw [he]; exact h
  by_cases hqp : q = p
  · subst hqp; exact h.trans hs.doneS_mono
  · rw [hs.loc_ne (Ne.symm hqp)]; exact h

lemma After.eventually_synced (hA : After r S K0) {p : Fin m} (hp : p ∈ S) :
    ∃ T ≥ K0, ∀ k ≥ T, Synced (r.cfg k) p := by
  obtain ⟨T, hT, hP⟩ := hA.eventually_passInv hβ hp
  obtain ⟨t, ht, hc, -⟩ := hA.reach_check hβ hp hT
  refine ⟨t, by omega, stable_of (P := fun C => Synced C p) (by omega) ?_
    (fun k hk h => hA.synced_step hβ p hk h)⟩
  have hI := Inv.of_reachable hβ (r.reachable t)
  intro x hx
  simp only [recorded, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset] at hx
  obtain ⟨a, ha⟩ := hx
  by_cases hap : a = p
  · subst hap; exact hI.own a x ha
  · exact (hP t ht).2 hc a hap x ha

/-- `TRY_p` contains the `next` values of all processes outside `S` read in this iteration. -/
def TryFull (S : Finset (Fin m)) (C : Config m Reg ℕ LState) (p : Fin m) : Prop :=
  ((C.loc p).status = .gatherTry → ∀ a : Fin m, a ∉ S → a.val < (C.loc p).q →
      0 < C.mem (.next a) → C.mem (.next a) ∈ (C.loc p).tryS) ∧
  (((C.loc p).status = .gatherDone ∨ (C.loc p).status = .check ∨
      (C.loc p).status = .compNext) →
    ∀ a : Fin m, a ∉ S → 0 < C.mem (.next a) → C.mem (.next a) ∈ (C.loc p).tryS)

lemma After.tryFull_step (hA : After r S K0) {p : Fin m} (hp : p ∈ S) {k : ℕ} (hk : K0 ≤ k)
    (h : TryFull S (r.cfg k) p) : TryFull S (r.cfg (k + 1)) p := by
  have hI := Inv.of_reachable hβ (r.reachable k)
  have hok := hA.status_ok hβ hp hk
  have hmem : ∀ a : Fin m, a ∉ S → (r.cfg (k + 1)).mem (.next a) = (r.cfg k).mem (.next a) :=
    fun a ha => by rw [hA.mem_next_frozen ha (by omega), hA.mem_next_frozen ha hk]
  rcases hA.step_cases hβ hk with he | ⟨q, hqS, hs⟩
  · rw [he]; exact h
  unfold TryFull at h ⊢
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨h1, h2⟩ := h
    have hmem' := hmem
    generalize r.cfg (k + 1) = C' at hs hmem' ⊢
    cases hs with
    | tryRead hst hq =>
      simp only [update_self, adv_status, adv_q, adv_tryS]
      have hqm := hI.qlt q (Or.inl hst)
      have key : ∀ a : Fin m, a ∉ S → a.val ≤ ((r.cfg k).loc q).q →
          0 < (r.cfg k).mem (.next a) →
          (r.cfg k).mem (.next a) ∈ addTry ((r.cfg k).mem (.next ((r.cfg k).loc q).q))
            ((r.cfg k).loc q).tryS := by
        intro a ha hle hpos
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact subset_addTry _ _ (h1 hst a ha hlt hpos)
        · rw [← heq]; exact mem_addTry hpos
      constructor
      · intro hs' a ha hlt hpos
        rw [hmem' a ha] at hpos ⊢
        split_ifs at hs' hlt with h3 <;> first | exact key a ha (by omega) hpos | simp_all
      · intro hs' a ha hpos
        rw [hmem' a ha] at hpos ⊢
        split_ifs at hs' with h3
        · simp [hst] at hs'
        · exact key a ha (by have := a.isLt; omega) hpos
    | trySkip hst hq =>
      simp only [update_self, adv_status, adv_q, adv_tryS]
      have hqm := hI.qlt q (Or.inl hst)
      have key : ∀ a : Fin m, a ∉ S → a.val ≤ ((r.cfg k).loc q).q →
          0 < (r.cfg k).mem (.next a) → (r.cfg k).mem (.next a) ∈ ((r.cfg k).loc q).tryS := by
        intro a ha hle hpos
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact h1 hst a ha hlt hpos
        · exact absurd (Fin.ext (heq.trans hq)) (fun e => ha (e ▸ hqS))
      constructor
      · intro hs' a ha hlt hpos
        rw [hmem' a ha] at hpos ⊢
        split_ifs at hs' hlt with h3 <;> first | exact key a ha (by omega) hpos | simp_all
      · intro hs' a ha hpos
        rw [hmem' a ha] at hpos ⊢
        split_ifs at hs' with h3
        · simp [hst] at hs'
        · exact key a ha (by have := a.isLt; omega) hpos
    | setNext hst =>
      simp only [update_self]
      refine ⟨fun _ a _ hlt => by simp [hI.qSet q hst] at hlt, fun hs' => by simp at hs'⟩
    | compNext hst hb => simp
    | finish hst hb => simp
    | doneRead hst hq hp' hv =>
      simp only [update_self]
      refine ⟨fun hs' => by simp [hst] at hs', fun _ a ha hpos => ?_⟩
      rw [hmem' a ha] at hpos ⊢; exact h2 (Or.inl hst) a ha hpos
    | doneAdv hst hq =>
      simp only [update_self, adv_status, adv_tryS]
      refine ⟨fun hs' => by split_ifs at hs' <;> simp [hst] at hs', fun _ a ha hpos => ?_⟩
      rw [hmem' a ha] at hpos ⊢; exact h2 (Or.inl hst) a ha hpos
    | checkOk hst _ _ => simp
    | checkFail hst _ =>
      simp only [update_self]
      refine ⟨fun hs' => by simp at hs', fun _ a ha hpos => ?_⟩
      rw [hmem' a ha] at hpos ⊢; exact h2 (Or.inr (Or.inl hst)) a ha hpos
    | perform hst => simp
    | writeDone hst => exact absurd hst hok.2.1
  · rw [hs.loc_ne (Ne.symm hqp)]
    refine ⟨fun hs' a ha hlt hpos => ?_, fun hs' a ha hpos => ?_⟩
    · rw [hmem a ha] at hpos ⊢; exact h.1 hs' a ha hlt hpos
    · rw [hmem a ha] at hpos ⊢; exact h.2 hs' a ha hpos

lemma After.eventually_tryFull (hA : After r S K0) {p : Fin m} (hp : p ∈ S) :
    ∃ T ≥ K0, ∀ k ≥ T, TryFull S (r.cfg k) p := by
  obtain ⟨t, ht, hc⟩ := hA.reach_compNext hβ hp (le_refl K0)
  obtain ⟨t1, ht1, he, hloc⟩ := hA.next_step hp t
  have hs := r.kstep_of_ev he
  rw [← hloc] at hc
  have hok := hA.status_ok hβ hp (k := t1 + 1) (by omega)
  have hst : ((r.cfg (t1 + 1)).loc p).status = .setNext := by
    generalize r.cfg (t1 + 1) = C' at hs hok ⊢
    cases hs <;> simp_all
  refine ⟨t1 + 1, by omega, stable_of (P := fun C => TryFull S C p) (by omega) ?_
    (fun k hk h => hA.tryFull_step hβ hp hk h)⟩
  unfold TryFull; simp [hst]

omit hβ in
lemma KStep.mem_next_self {C C' : Config m Reg ℕ LState} {p : Fin m}
    (hs : KStep m n β C p C') (h : (C.loc p).status ≠ .setNext) :
    C'.mem (.next p) = C.mem (.next p) := by
  cases hs <;> simp_all

variable (r S K0) in
/-- Values held in `next` by the processes outside `S` (frozen after `K0`). -/
noncomputable def frozenVals : Finset ℕ :=
  (Finset.univ.filter (· ∉ S)).image (fun a : Fin m => (r.cfg K0).mem (.next a))

variable (r K0) in
/-- The unrecorded jobs (after `K0`). -/
def freeJobs : Finset ℕ := Finset.Icc 1 n \ recorded (r.cfg K0)

variable (r S K0) in
/-- `POOL`: unrecorded jobs not held by a process outside `S`. -/
noncomputable def pool : Finset ℕ := freeJobs r K0 \ frozenVals r S K0

variable (r S K0) in
/-- `x` is in `POOL` with rank at least the rank `k_p` targeted by `p`. -/
def Good (p : Fin m) (x : ℕ) : Prop :=
  x ∈ pool r S K0 ∧ kIdx m p (freeJobs r K0).card - 1 ≤ below (pool r S K0) x

/-- The view of a synchronised process at `compNext`. -/
lemma After.compNext_view (hA : After r S K0) {p : Fin m} (hp : p ∈ S) {k : ℕ} (hk : K0 ≤ k)
    (hsy : Synced (r.cfg k) p) (htf : TryFull S (r.cfg k) p)
    (hc : ((r.cfg k).loc p).status = .compNext) :
    free n ((r.cfg k).loc p) = freeJobs r K0 ∧
      free n ((r.cfg k).loc p) \ ((r.cfg k).loc p).tryS ⊆ pool r S K0 ∧
      (free n ((r.cfg k).loc p)).card ≤
        (free n ((r.cfg k).loc p) \ ((r.cfg k).loc p).tryS).card + (m - 1) := by
  obtain ⟨hI, hI2⟩ := inv_of_reachable hβ (r.reachable k)
  have hdone : ((r.cfg k).loc p).doneS = recorded (r.cfg K0) := by
    rw [← hA.recorded_eq hk]
    exact Finset.Subset.antisymm (hI2.doneRec p) hsy
  have hfree : free n ((r.cfg k).loc p) = freeJobs r K0 := by
    unfold free freeJobs; rw [hdone]
  refine ⟨hfree, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hfree] at hx1
    unfold pool
    refine Finset.mem_sdiff.mpr ⟨hx1, fun hz => hx2 ?_⟩
    simp only [frozenVals, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [← hA.mem_next_frozen ha hk] at hx1 ⊢
    have hpos : 0 < (r.cfg k).mem (.next a) := by
      simp only [freeJobs, Finset.mem_sdiff, Finset.mem_Icc] at hx1; omega
    exact htf.2 (Or.inr (Or.inr hc)) a ha hpos
  · have h1 := Finset.card_sdiff_add_card_inter (free n ((r.cfg k).loc p)) ((r.cfg k).loc p).tryS
    have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := free n ((r.cfg k).loc p))
      (s₂ := ((r.cfg k).loc p).tryS))
    have h3 := tryS_card_le hI2 hI p
    omega

/-- After a synchronised `compNext`, `NEXT_p` is good, and the target rank exists. -/
lemma After.compNext_good (hA : After r S K0) (hβm : m ≤ β) {p : Fin m} (hp : p ∈ S) {k : ℕ}
    (hk : K0 ≤ k) (hsy : Synced (r.cfg k) p) (htf : TryFull S (r.cfg k) p)
    (hc : ((r.cfg k).loc p).status = .compNext) (hs : KStep m n β (r.cfg k) p (r.cfg (k + 1))) :
    ((r.cfg (k + 1)).loc p).nxt = rank (free n ((r.cfg k).loc p) \ ((r.cfg k).loc p).tryS)
        (kIdx m p (freeJobs r K0).card) ∧
      ((r.cfg (k + 1)).loc p).status = .setNext ∧
      Good r S K0 p ((r.cfg (k + 1)).loc p).nxt ∧
      kIdx m p (freeJobs r K0).card ≤ (pool r S K0).card := by
  obtain ⟨hfree, hsub, hcard⟩ := hA.compNext_view hβ hp hk hsy htf hc
  have hok := hA.status_ok hβ hp (k := k + 1) (by omega)
  have hres : β ≤ (free n ((r.cfg k).loc p) \ ((r.cfg k).loc p).tryS).card ∧
      ((r.cfg (k + 1)).loc p).nxt = rank (free n ((r.cfg k).loc p) \ ((r.cfg k).loc p).tryS)
        (kIdx m p (free n ((r.cfg k).loc p)).card) ∧
      ((r.cfg (k + 1)).loc p).status = .setNext := by
    generalize r.cfg (k + 1) = C' at hs hok ⊢
    cases hs <;> simp_all
  obtain ⟨hb, hnxt, hst⟩ := hres
  rw [show (free n ((r.cfg k).loc p)).card = (freeJobs r K0).card by rw [hfree]] at hnxt hcard
  set A := free n ((r.cfg k).loc p) \ ((r.cfg k).loc p).tryS
  have hkp := kIdx_le_avail (F := (freeJobs r K0).card) p.isLt hβm hb hcard
  have hk1 := kIdx_pos m p (freeJobs r K0).card
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hmem := rank_mem hne (kIdx m p (freeJobs r K0).card)
  refine ⟨hnxt, hst, ⟨hnxt ▸ hsub hmem, ?_⟩, hkp.trans (Finset.card_le_card hsub)⟩
  rw [hnxt, ← below_rank hk1 hkp]
  exact below_mono hsub _

variable (r S K0) in
/-- `NEXT_p` and `next_p` are good. -/
def GoodNext (C : Config m Reg ℕ LState) (p : Fin m) : Prop :=
  Good r S K0 p (C.loc p).nxt ∧ Good r S K0 p (C.mem (.next p))

lemma After.goodNext_step (hA : After r S K0) (hβm : m ≤ β) {p : Fin m} (hp : p ∈ S) {T : ℕ}
    (hT : K0 ≤ T) (hsy : ∀ k ≥ T, Synced (r.cfg k) p) (htf : ∀ k ≥ T, TryFull S (r.cfg k) p)
    {k : ℕ} (hk : T ≤ k) (h : GoodNext r S K0 (r.cfg k) p) :
    GoodNext r S K0 (r.cfg (k + 1)) p := by
  rcases hA.step_cases hβ (k := k) (by omega) with he | ⟨q, hqS, hs⟩
  · rw [he]; exact h
  unfold GoodNext at h ⊢
  by_cases hqp : q = p
  · subst hqp
    by_cases hc : ((r.cfg k).loc q).status = .compNext
    · obtain ⟨-, -, hg, -⟩ := hA.compNext_good hβ hβm hp (by omega) (hsy k hk) (htf k hk) hc hs
      exact ⟨hg, by rw [hs.mem_next_self (by rw [hc]; simp)]; exact h.2⟩
    · rw [hs.nxt_eq hc]
      refine ⟨h.1, ?_⟩
      by_cases hsn : ((r.cfg k).loc q).status = .setNext
      · have : (r.cfg (k + 1)).mem (.next q) = ((r.cfg k).loc q).nxt := by
          generalize r.cfg (k + 1) = C' at hs ⊢
          cases hs <;> simp_all
        rw [this]; exact h.1
      · rw [hs.mem_next_self hsn]; exact h.2
  · rw [hs.loc_ne (Ne.symm hqp), hs.mem_next_ne _ (val_ne_of_ne (Ne.symm hqp))]; exact h

lemma After.eventually_goodNext (hA : After r S K0) (hβm : m ≤ β) {p : Fin m} (hp : p ∈ S) :
    ∃ T ≥ K0, ∀ k ≥ T, GoodNext r S K0 (r.cfg k) p ∧ Synced (r.cfg k) p ∧
      TryFull S (r.cfg k) p := by
  obtain ⟨T1, hT1, hsy⟩ := hA.eventually_synced hβ hp
  obtain ⟨T2, hT2, htf⟩ := hA.eventually_tryFull hβ hp
  set T := max T1 T2
  have hsy' : ∀ k ≥ T, Synced (r.cfg k) p := fun k hk => hsy k (by omega)
  have htf' : ∀ k ≥ T, TryFull S (r.cfg k) p := fun k hk => htf k (by omega)
  obtain ⟨a, ha, hc⟩ := hA.reach_compNext hβ hp (t := T) (by omega)
  obtain ⟨a1, ha1, he1, hloc1⟩ := hA.next_step hp a
  rw [← hloc1] at hc
  obtain ⟨-, hst, hg, -⟩ := hA.compNext_good hβ hβm hp (by omega) (hsy' a1 (by omega))
    (htf' a1 (by omega)) hc (r.kstep_of_ev he1)
  obtain ⟨a2, ha2, he2, hloc2⟩ := hA.next_step hp (a1 + 1)
  rw [← hloc2] at hst hg
  have hs2 := r.kstep_of_ev he2
  have hreg : (r.cfg (a2 + 1)).mem (.next p) = ((r.cfg a2).loc p).nxt := by
    generalize r.cfg (a2 + 1) = C' at hs2 ⊢
    cases hs2 <;> simp_all
  have hnx : ((r.cfg (a2 + 1)).loc p).nxt = ((r.cfg a2).loc p).nxt :=
    hs2.nxt_eq (by rw [hst]; simp)
  refine ⟨a2 + 1, by omega, fun k hk => ⟨?_, hsy' k (by omega), htf' k (by omega)⟩⟩
  refine stable_of (K0 := T) (P := fun C => GoodNext r S K0 C p) (t := a2 + 1) (by omega) ?_
    (fun k hk h => hA.goodNext_step hβ hβm hp (by omega) hsy' htf' hk h) k hk
  exact ⟨hnx ▸ hg, hreg ▸ hg⟩

variable (r S K0) in
/-- Every job of `POOL` in `TRY_{p₀}` has rank `> k_{p₀}`. -/
def GoodTry (C : Config m Reg ℕ LState) (p₀ : Fin m) : Prop :=
  ∀ x ∈ (C.loc p₀).tryS, x ∈ pool r S K0 → kIdx m p₀ (freeJobs r K0).card ≤ below (pool r S K0) x

lemma After.goodTry_step (hA : After r S K0) {p₀ : Fin m} (hp₀ : p₀ ∈ S)
    (hmin : ∀ q ∈ S, p₀ ≤ q) {T : ℕ} (hT : K0 ≤ T)
    (hgood : ∀ q ∈ S, ∀ k ≥ T, GoodNext r S K0 (r.cfg k) q)
    {k : ℕ} (hk : T ≤ k) (h : GoodTry r S K0 (r.cfg k) p₀) :
    GoodTry r S K0 (r.cfg (k + 1)) p₀ := by
  have hI := Inv.of_reachable hβ (r.reachable k)
  rcases hA.step_cases hβ (k := k) (by omega) with he | ⟨q, hqS, hs⟩
  · rw [he]; exact h
  unfold GoodTry at h ⊢
  by_cases hqp : q = p₀
  · subst hqp
    generalize r.cfg (k + 1) = C' at hs ⊢
    cases hs with
    | compNext hst hb => simp
    | tryRead hst hq =>
      simp only [update_self, adv_tryS]
      intro x hx hxp
      unfold addTry at hx
      split_ifs at hx with hv
      · rcases Finset.mem_insert.mp hx with hx | hx
        · subst hx
          have hqm := hI.qlt q (Or.inl hst)
          set a : Fin m := ⟨((r.cfg k).loc q).q, hqm⟩
          by_cases haS : a ∈ S
          · have hg := (hgood a haS k hk).2
            have hlt : q < a := lt_of_le_of_ne (hmin a haS)
              (fun e => hq (by rw [show (q : ℕ) = a.val from congrArg Fin.val e]))
            have := kIdx_lt (F := (freeJobs r K0).card) hlt a.isLt
            have h2 := hg.2
            simp only [a] at h2 this
            omega
          · exfalso
            have hz : (r.cfg k).mem (.next a) ∈ frozenVals r S K0 := by
              rw [hA.mem_next_frozen haS (by omega)]
              simp only [frozenVals, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨a, haS, rfl⟩
            exact (Finset.mem_sdiff.mp hxp).2 hz
        · exact h x hx hxp
      · exact h x hx hxp
    | _ => simpa using h
  · rw [hs.loc_ne (Ne.symm hqp)]; exact h

/-- The main contradiction: after stabilisation, the smallest process of `S` performs a job. -/
theorem After.false (hA : After r S K0) (hβm : m ≤ β) (hS : S.Nonempty) : False := by
  classical
  set p₀ := S.min' hS
  have hp₀ : p₀ ∈ S := S.min'_mem hS
  have hmin : ∀ q ∈ S, p₀ ≤ q := fun q hq => S.min'_le q hq
  have hT : ∀ p ∈ S, ∃ T ≥ K0, ∀ k ≥ T, GoodNext r S K0 (r.cfg k) p ∧ Synced (r.cfg k) p ∧
      TryFull S (r.cfg k) p := fun p hp => hA.eventually_goodNext hβ hβm hp
  choose! Tf hTf hTg using hT
  set T := max K0 (S.sup Tf)
  have hTK : K0 ≤ T := le_max_left _ _
  have hall : ∀ p ∈ S, ∀ k ≥ T, GoodNext r S K0 (r.cfg k) p ∧ Synced (r.cfg k) p ∧
      TryFull S (r.cfg k) p := by
    intro p hp k hk
    exact hTg p hp k (le_trans (Finset.le_sup hp) (le_trans (le_max_right _ _) hk))
  set F := (freeJobs r K0).card
  set kp := kIdx m p₀ F
  -- first synchronised `compNext` of `p₀`: `TRY_{p₀}` is reset, and `k_{p₀} ≤ |POOL|`
  obtain ⟨a, ha, hca⟩ := hA.reach_compNext hβ hp₀ hTK
  obtain ⟨a1, ha1, he1, hloc1⟩ := hA.next_step hp₀ a
  rw [← hloc1] at hca
  have hs1 := r.kstep_of_ev he1
  obtain ⟨-, -, -, hkpool⟩ := hA.compNext_good hβ hβm hp₀ (by omega)
    (hall p₀ hp₀ a1 (by omega)).2.1 (hall p₀ hp₀ a1 (by omega)).2.2 hca hs1
  have hok1 := hA.status_ok hβ hp₀ (k := a1 + 1) (by omega)
  have htry0 : ((r.cfg (a1 + 1)).loc p₀).tryS = ∅ := by
    generalize r.cfg (a1 + 1) = C' at hs1 hok1 ⊢
    cases hs1 <;> simp_all
  have hgt : ∀ k ≥ a1 + 1, GoodTry r S K0 (r.cfg k) p₀ := by
    refine stable_of (K0 := T) (P := fun C => GoodTry r S K0 C p₀) (by omega) ?_
      (fun k hk h => hA.goodTry_step hβ hp₀ hmin hTK (fun q hq k hk => (hall q hq k hk).1) hk h)
    unfold GoodTry; simp [htry0]
  -- the target job `x₀`
  have hk1 : 1 ≤ kp := kIdx_pos m p₀ F
  have hkpool' : kp ≤ (pool r S K0).card := hkpool
  have hpne : (pool r S K0).Nonempty := Finset.card_pos.mp (by omega)
  set x₀ := rank (pool r S K0) kp
  have hx₀ : x₀ ∈ pool r S K0 := rank_mem hpne kp
  have hbx₀ : below (pool r S K0) x₀ = kp - 1 := below_rank hk1 hkpool
  have hnotry : ∀ k ≥ a1 + 1, ∀ y ∈ pool r S K0, y ≤ x₀ → y ∉ ((r.cfg k).loc p₀).tryS := by
    intro k hk y hy hyx hyt
    have h3 : kp ≤ below (pool r S K0) y := hgt k hk y hyt hy
    rcases Nat.lt_or_eq_of_le hyx with hlt | heq
    · have := below_strictMono hy hlt; omega
    · subst heq; omega
  -- second synchronised `compNext`: `p₀` picks `x₀`
  obtain ⟨b, hb, hcb⟩ := hA.reach_compNext hβ hp₀ (t := a1 + 1) (by omega)
  obtain ⟨b1, hb1, he2, hloc2⟩ := hA.next_step hp₀ b
  rw [← hloc2] at hcb
  have hs2 := r.kstep_of_ev he2
  obtain ⟨hnxt, hst2, -, -⟩ := hA.compNext_good hβ hβm hp₀ (by omega)
    (hall p₀ hp₀ b1 (by omega)).2.1 (hall p₀ hp₀ b1 (by omega)).2.2 hcb hs2
  obtain ⟨hfree, hsub, -⟩ := hA.compNext_view hβ hp₀ (k := b1) (by omega)
    (hall p₀ hp₀ b1 (by omega)).2.1 (hall p₀ hp₀ b1 (by omega)).2.2 hcb
  have hpool_free : pool r S K0 ⊆ freeJobs r K0 := Finset.sdiff_subset
  have hpick : ((r.cfg (b1 + 1)).loc p₀).nxt = x₀ := by
    rw [hnxt]
    apply rank_eq_of_below _ hk1
    · apply le_antisymm
      · rw [← hbx₀]; exact below_mono hsub _
      · rw [← hbx₀]
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        refine ⟨Finset.mem_sdiff.mpr ⟨hfree ▸ hpool_free hy.1, ?_⟩, hy.2⟩
        exact hnotry b1 (by omega) y hy.1 hy.2.le
    · exact Finset.mem_sdiff.mpr ⟨hfree ▸ hpool_free hx₀, hnotry b1 (by omega) x₀ hx₀ le_rfl⟩
  -- `p₀` reaches `check` with `NEXT = x₀` and passes it
  obtain ⟨c, hc, hcc, hcn⟩ := hA.reach_check hβ hp₀ (t := b1 + 1) (by omega)
  have hcn' : ((r.cfg c).loc p₀).nxt = x₀ := by rw [hcn (by rw [hst2]; simp), hpick]
  obtain ⟨hI, hI2⟩ := inv_of_reachable hβ (r.reachable c)
  have hdone : ((r.cfg c).loc p₀).doneS = recorded (r.cfg K0) := by
    rw [← hA.recorded_eq (k := c) (by omega)]
    exact Finset.Subset.antisymm (hI2.doneRec p₀) (hall p₀ hp₀ c (by omega)).2.1
  have h1 : ((r.cfg c).loc p₀).nxt ∉ ((r.cfg c).loc p₀).tryS := by
    rw [hcn']; exact hnotry c (by omega) x₀ hx₀ le_rfl
  have h2 : ((r.cfg c).loc p₀).nxt ∉ ((r.cfg c).loc p₀).doneS := by
    rw [hcn', hdone]
    have := hpool_free hx₀
    simp only [freeJobs, Finset.mem_sdiff] at this
    exact this.2
  obtain ⟨c1, hc1, he3, hloc3⟩ := hA.next_step hp₀ c
  have hs3 := r.kstep_of_ev he3
  rw [← hloc3] at hcc h1 h2
  exact (hA.status_ok hβ hp₀ (k := c1 + 1) (by omega)).1 (hs3.check_ok hcc h1 h2)

end After

end Podc.AtMostOnceEffectiveness

namespace Podc.AtMostOnceEffectiveness

variable {m n β : ℕ}

/-- A run with infinitely many steps stabilises. -/
lemma exists_after (hβ : 1 ≤ β) (r : (kk m n β).Run) (hinf : ∀ K, ∃ k ≥ K, r.ev k ≠ none) :
    ∃ S K0, S.Nonempty ∧ After r S K0 := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun p => ∀ k, ∃ k' ≥ k, r.ev k' = some p)
  have hfin : ∀ p, p ∉ S → ∃ K, ∀ k ≥ K, r.ev k ≠ some p := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_exists,
      not_and] at hp
    obtain ⟨K, hK⟩ := hp
    exact ⟨K, fun k hk he => hK k hk he⟩
  choose! Kp hKp using hfin
  obtain ⟨K1, hK1⟩ := r.exists_lines_const hβ
  set K0 := max K1 (Finset.univ.sup Kp)
  have hquiet : ∀ k ≥ K0, ∀ q, r.ev k = some q → q ∈ S := by
    intro k hk q he
    by_contra hq
    exact hKp q hq k (le_trans (Finset.le_sup (Finset.mem_univ q))
      (le_trans (le_max_right _ _) hk)) he
  refine ⟨S, K0, ?_, ⟨?_, hquiet, ?_⟩⟩
  · obtain ⟨k, hk, he⟩ := hinf K0
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp he
    exact ⟨q, hquiet k hk q hq⟩
  · intro p hp
    simpa [S] using hp
  · intro k hk q
    rw [hK1 k (by omega), hK1 K0 (le_max_left _ _)]

/-- **Lemma 4.3** of [Kentros–Kiayias] (wait-freedom): for `β ≥ m`, every run of `KK_β` takes only
finitely many steps. In particular there is no infinite fair execution (for any set of crashed
processes). -/
theorem lemma_4_3 (hβm : m ≤ β) (r : (kk m n β).Run) : ∃ K, ∀ k ≥ K, r.ev k = none := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨0, fun k _ => by cases h : r.ev k with
      | none => rfl
      | some p => exact p.elim0⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨S, K0, hS, hA⟩ := exists_after (by omega) r hcon
  exact hA.false (by omega) hβm hS

end Podc.AtMostOnceEffectiveness
