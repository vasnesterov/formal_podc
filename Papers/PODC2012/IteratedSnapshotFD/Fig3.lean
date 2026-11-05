import Papers.PODC2012.IteratedSnapshotFD.Model

/-!
# The generic simulation of `IIS_n[C*]` in `ARW_n[C]` (Figure 3) and the class `Σ`

## The simulation (Figure 3)

Simulators `p_0, …, p_{n-1}` (the paper's `p_1, …, p_n`). Simulated round `r ≥ 1` is *owned* by
`p_{r mod n}` (line 1). Atomic steps of simulator `i` in round `r`:

* `start`, owner (lines 2–3, one iteration of the repeat loop): `arw_view ← S[r].collect()`,
  `FD_VAL[i] ← C.read()`; if `PROP(arw_view, FD_VAL[i])` holds go to `write`, else iterate again;
* `start`, non-owner (line 4): `FD_VAL[i] ← C.read()`, go to `write`;
* `write` (lines 6–7): `iis_view ← S[r].arw_write_snapshot()`; this ends the simulation of
  `IS[r].write_snapshot()` by `q_i`, whose `C*.read()` returns `FD_VAL[i]`.

The collect and the write-snapshot are taken atomic (a sequential execution of these objects is
one of their legal executions), so `arw_write_snapshot` returns the set of simulators that have
written `S[r]` so far. The failure-detector history is `H i t` (output of `C` at simulator `i` at
time `t`); `sched t` is the simulator that moves at time `t`.

## Σ (Section 4.4, Theorem 4)

Section 4.4 claims that Figure 3 with `PROP_{◇P}(arw_view) = ∀ j ∈ FD_VAL[i], j = i ∨ ⟨j,-⟩ ∈
arw_view` correctly simulates `IIS_n[Σ*]` in `ARW_n[Σ]` (and the same for `S, ◇S, S_x, ◇S_x`);
Theorem 4 states it "for the failure detector classes studied in this paper" (with `t = n − 1`
the extra conjunct `|arw_view| ≥ n − t − 1` is vacuous). `sigma_simulation_false` refutes it with
two simulators: `p_0` always runs its round first, so it never sees `p_1` and `q_1` is weakly correct,
while `p_0`'s Σ-quorum, read at the rounds it does not own, is `{p_0, p_1}`. The outputs of the
simulated `Σ*` then contain the non-strongly-correct `q_1` forever, at every process.
-/

set_option linter.unusedSectionVars false

namespace Podc.IteratedSnapshotFD.Fig3

/-- Program counter of a simulator. -/
inductive PC
  | start
  | write
  deriving DecidableEq

/-- Local state of simulator `p_i`: current simulated round, program counter, `FD_VAL[i]`. -/
structure SimLoc (n : ℕ) where
  rnd : ℕ
  pc : PC
  fdval : Finset (Fin n)

/-- A configuration of the simulation, with the record of the simulated IIS execution. -/
@[ext] structure Cfg (n : ℕ) where
  loc : Fin n → SimLoc n
  /-- The simulators that have written `S[r]`. -/
  S : ℕ → Finset (Fin n)
  /-- `view r i`: view returned to `q_i` by `IS[r].write_snapshot()` (`∅` if not yet returned). -/
  view : ℕ → Fin n → Finset (Fin n)
  /-- `out r i`: the value of `FD_VAL[i]` when `q_i` invokes `S[r].arw_write_snapshot()`, i.e. the
  output of the simulated `C*` at `q_i` in round `r` (`∅` if not yet). -/
  out : ℕ → Fin n → Finset (Fin n)

/-- Initial configuration: everybody about to simulate round `1`. -/
def Cfg.init (n : ℕ) : Cfg n := ⟨fun _ => ⟨1, .start, ∅⟩, fun _ => ∅, fun _ _ => ∅, fun _ _ => ∅⟩

/-- Owner of round `r` (line 1: `(r mod n) + 1 = i` in the paper's 1-based numbering). -/
def owner {n : ℕ} [NeZero n] (r : ℕ) : Fin n := ⟨r % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

theorem owner_two (r : ℕ) : (owner r : Fin 2) = if r % 2 = 0 then 0 else 1 := by
  ext; simp only [owner]; split_ifs with h <;> simp [h]; omega

/-- One atomic step of simulator `i` at time `t`, with failure-detector history `H` and predicate
`prop arw_view fd_val i`. -/
def step {n : ℕ} [NeZero n] (prop : Finset (Fin n) → Finset (Fin n) → Fin n → Prop)
    [∀ a b i, Decidable (prop a b i)] (H : Fin n → ℕ → Finset (Fin n)) (t : ℕ) (c : Cfg n)
    (i : Fin n) : Cfg n :=
  let s := c.loc i
  let r := s.rnd
  match s.pc with
  | .start =>
    if owner r = i then
      if prop (c.S r) (H i t) i then
        { c with loc := Function.update c.loc i ⟨r, .write, H i t⟩ }
      else
        { c with loc := Function.update c.loc i ⟨r, .start, H i t⟩ }
    else
      { c with loc := Function.update c.loc i ⟨r, .write, H i t⟩ }
  | .write =>
    { loc := Function.update c.loc i ⟨r + 1, .start, s.fdval⟩
      S := Function.update c.S r (insert i (c.S r))
      view := Function.update c.view r (Function.update (c.view r) i (insert i (c.S r)))
      out := Function.update c.out r (Function.update (c.out r) i s.fdval) }

/-- The run of the simulation under the schedule `sched`. -/
def run {n : ℕ} [NeZero n] (prop : Finset (Fin n) → Finset (Fin n) → Fin n → Prop)
    [∀ a b i, Decidable (prop a b i)] (H : Fin n → ℕ → Finset (Fin n)) (sched : ℕ → Fin n) :
    ℕ → Cfg n
  | 0 => Cfg.init n
  | t + 1 => step prop H t (run prop H sched t) (sched t)

/-- The predicate `PROP_{◇P}` of Section 4.3, also used for `Σ` (Section 4.4). -/
def propDP {n : ℕ} (arwView fdVal : Finset (Fin n)) (i : Fin n) : Prop :=
  ∀ j ∈ fdVal, j = i ∨ j ∈ arwView

instance {n : ℕ} (a b : Finset (Fin n)) (i : Fin n) : Decidable (propDP a b i) := by
  unfold propDP; infer_instance

/-- `H` is a history of the class `Σ` in a failure-free run: any two quorums, at any times,
intersect (the completeness part is void when nobody crashes). -/
def IsSigma {n : ℕ} (H : Fin n → ℕ → Finset (Fin n)) : Prop :=
  ∀ i j t t', (H i t ∩ H j t').Nonempty

/-- `out` (indexed by the rounds `0, 1, …` of `σ`) is a history of the class `Σ*` for the IIS
schedule `σ`: quorums intersect and eventually contain only strongly correct processes. -/
def IsSigmaStar {n : ℕ} (σ : Schedule (Fin n)) (out : ℕ → Fin n → Finset (Fin n)) : Prop :=
  (∀ r r' i j, i ∈ (σ.rd r).part → j ∈ (σ.rd r').part → (out r i ∩ out r' j).Nonempty) ∧
  ∃ R, ∀ r ≥ R, ∀ i ∈ (σ.rd r).part, ∀ j ∈ out r i, j ∈ σ.SC

/-! ### The counterexample -/

/-- Simulator `p_0`'s Σ-output is `{p_0}` during the rounds it owns (even rounds) and `{p_0, p_1}`
otherwise; `p_1`'s is always `{p_0, p_1}`. Time `t` belongs to simulated round `t / 4 + 1`. -/
def Hc : Fin 2 → ℕ → Finset (Fin 2)
  | 0, t => if (t / 4 + 1) % 2 = 0 then {0} else Finset.univ
  | 1, _ => Finset.univ

/-- In each round, `p_0` takes its two steps, then `p_1` takes its two steps. -/
def schedc (t : ℕ) : Fin 2 := if t % 4 < 2 then 0 else 1

theorem Hc_sigma : IsSigma Hc := by
  intro i j t t'
  refine ⟨0, ?_⟩
  fin_cases i <;> fin_cases j <;> simp [Hc] <;> split_ifs <;> simp_all

theorem schedc_fair (i : Fin 2) (T : ℕ) : ∃ t ≥ T, schedc t = i := by
  fin_cases i
  · exact ⟨4 * T, by omega, by simp [schedc]⟩
  · exact ⟨4 * T + 2, by omega, by simp [schedc]⟩

/-- The views of the simulated IIS execution: `q_0` always alone, `q_1` sees both. -/
def Vc : Fin 2 → Finset (Fin 2)
  | 0 => {0}
  | 1 => Finset.univ

/-- `FD_VAL` after round `m`. -/
def fdc (i : Fin 2) (m : ℕ) : Finset (Fin 2) :=
  if m = 0 then ∅ else if i = 0 ∧ m % 2 = 0 then {0} else Finset.univ

/-- The configuration at time `4 m` (after `m` complete rounds). -/
def cfgAt (m : ℕ) : Cfg 2 where
  loc i := ⟨m + 1, .start, fdc i m⟩
  S r := if 1 ≤ r ∧ r ≤ m then Finset.univ else ∅
  view r i := if 1 ≤ r ∧ r ≤ m then Vc i else ∅
  out r i := if 1 ≤ r ∧ r ≤ m then fdc i r else ∅

/-- The run of Figure 3 with `PROP_{◇P}` under `Hc` and `schedc`. -/
def runc : ℕ → Cfg 2 := run propDP Hc schedc

theorem cfgAt_zero : cfgAt 0 = Cfg.init 2 := by
  simp only [cfgAt, Cfg.init, fdc]
  congr 1 <;> funext <;> simp <;> omega

theorem runc_four_mul (m : ℕ) : runc (4 * m) = cfgAt m := by
  induction m with
  | zero => simp [runc, run, cfgAt_zero]
  | succ m ih =>
    have e : 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 := by ring
    rw [e]
    simp only [runc, run] at ih ⊢
    rw [ih]
    have h0 : schedc (4 * m) = 0 := by simp [schedc]
    have h1 : schedc (4 * m + 1) = 0 := by simp [schedc]
    have h2 : schedc (4 * m + 1 + 1) = 1 := by simp [schedc]; omega
    have h3 : schedc (4 * m + 1 + 1 + 1) = 1 := by simp [schedc]; omega
    rw [h0, h1, h2, h3]
    rcases Nat.mod_two_eq_zero_or_one (m + 1) with h | h
    · simp [step, cfgAt, owner_two, h, Hc, fdc, propDP]
      refine ⟨?_, ?_, ?_, ?_⟩
      · funext i; fin_cases i <;> simp [Function.update]
      · funext r; simp only [Function.update_apply]; split_ifs <;> first | rfl | decide | omega
      · funext r i; fin_cases i <;> simp only [Function.update_apply] <;> split_ifs <;>
          simp_all [Vc] <;> first | rfl | decide | omega
      · funext r i; fin_cases i <;> simp only [Function.update_apply] <;> split_ifs <;>
          simp_all <;> omega
    · simp [step, cfgAt, owner_two, h, Hc, fdc, propDP]
      refine ⟨?_, ?_, ?_, ?_⟩
      · funext i; fin_cases i <;> simp [Function.update]
      · funext r; simp only [Function.update_apply]; split_ifs <;> first | rfl | decide | omega
      · funext r i; fin_cases i <;> simp only [Function.update_apply] <;> split_ifs <;>
          simp_all [Vc] <;> first | rfl | decide | omega
      · funext r i; fin_cases i <;> simp only [Function.update_apply] <;> split_ifs <;>
          simp_all <;> omega

/-- The simulated IIS schedule (round `k` of `σc` is the paper's round `k + 1`). -/
def σc : Schedule (Fin 2) where
  rd _ :=
    { part := Finset.univ
      view := Vc
      view_sub := by intro i _; exact Finset.subset_univ _
      self_mem := by intro i _; fin_cases i <;> simp [Vc]
      contain := by intro i _ j _; fin_cases i <;> fin_cases j <;> simp [Vc]
      immed := by intro i _ j _; fin_cases i <;> fin_cases j <;> simp [Vc] }
  mono _ := le_rfl

/-- The outputs of the simulated `Σ*` (round `k` of `σc` is the paper's round `k + 1`). -/
def outc (k : ℕ) (i : Fin 2) : Finset (Fin 2) := fdc i (k + 1)

theorem σc_correct (i : Fin 2) : σc.Correct i := fun _ => Finset.mem_univ _

theorem one_not_mem_SCk (k : ℕ) : (1 : Fin 2) ∉ σc.SCk k := by
  induction k with
  | zero =>
    intro h
    obtain ⟨r, -, -, hall⟩ := σc.mem_SCk_zero.1 h 0
    have := (hall 0 (σc_correct 0)).2
    simp [σc, Vc] at this
  | succ k ih =>
    intro h
    obtain ⟨r, -, j, hj, -, hsee⟩ := σc.mem_SCk_succ.1 h 0
    fin_cases j
    · simp [σc, Vc] at hsee
    · exact ih hj

/-- In the simulated execution only `q_0` is strongly correct; `q_1` is weakly correct. -/
theorem σc_SC : σc.SC = {0} := by
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Set.mem_singleton_iff, iff_true]
    refine ⟨0, σc.mem_SCk_zero.2 fun R => ⟨R, le_rfl, Finset.mem_univ _, fun j _ => ?_⟩⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    fin_cases j <;> simp [σc, Vc]
  · simp only [Fin.mk_one, Fin.isValue, Set.mem_singleton_iff, one_ne_zero, iff_false]
    rintro ⟨k, hk⟩
    exact one_not_mem_SCk k hk

/-- **Section 4.4 / Theorem 4 are false for `Σ`.** Figure 3 with `PROP_{◇P}`, run in
`ARW_2[Σ]` (failure-free, a legal `Σ` history `Hc`, a fair schedule `schedc`): every simulator
simulates every round (`rnd`), the simulated views and `Σ*` outputs are those of `σc` and `outc`,
`q_1` is not strongly correct, and the simulated outputs are **not** a `Σ*` history — at `q_0`, a
strongly correct process, the quorum `{q_0, q_1}` recurs forever. -/
theorem sigma_simulation_false :
    IsSigma Hc ∧ (∀ i T, ∃ t ≥ T, schedc t = i) ∧
    (∀ m i, ((runc (4 * m)).loc i).rnd = m + 1) ∧
    (∀ m r i, 1 ≤ r → r ≤ m →
      (runc (4 * m)).view r i = (σc.rd (r - 1)).view i ∧ (runc (4 * m)).out r i = outc (r - 1) i) ∧
    σc.SC = {0} ∧ ¬ IsSigmaStar σc outc := by
  refine ⟨Hc_sigma, schedc_fair, fun m i => by simp [runc_four_mul, cfgAt],
    fun m r i h1 h2 => ?_, σc_SC, ?_⟩
  · rw [runc_four_mul]
    refine ⟨by simp [cfgAt, σc, h1, h2], ?_⟩
    simp only [cfgAt, outc, h1, h2, and_self, ite_true]
    congr 1; omega
  · rintro ⟨-, R, hR⟩
    have h := hR (2 * R) (by omega) 0 (Finset.mem_univ _) 1
      (by simp [outc, fdc])
    rw [σc_SC] at h
    simp at h

end Podc.IteratedSnapshotFD.Fig3
