import Papers.PODC2014.EventualLinParadox.Theorem12

/-!
# Proposition 14: trivial deterministic types

A deterministic type `T` is **trivial** (Definition 13) if there is a function `r` such that
`r q₀ op` is the correct response to `op` in every state reachable from the initial state `q₀`.
(The paper asks `r` to be computable, matching its Turing-machine programmes; our programmes
are arbitrary functions, so computability is dropped on both sides.)

* `delayLab`, `elStep_delay`, `delayRel_run` — delaying an execution by `T` steps (operation
  names shift by `T`, responses and local states are unchanged).
* `prop14` — **Proposition 14**: for at least two processes, a deterministic type has a
  linearizable obstruction-free implementation from some collection of eventually linearizable
  objects iff it is trivial.
-/

namespace Podc.EventualLinParadox

/-! ### Delaying an execution -/

section Delay

variable {P HOp HRes X BOp BRes L : Type} [DecidableEq P] (I : Impl P HOp HRes X BOp BRes L)

/-- The execution `lab` started `T` steps later. -/
def delayLab (lab : ℕ → Option (ELab P HOp BRes)) (T : ℕ) : ℕ → Option (ELab P HOp BRes) :=
  fun n => if n < T then none else lab (n - T)

/-- Configurations of a delayed execution (time `T + n`) and of the original (time `n`). -/
structure DelayRel (T : ℕ) (c c' : ECfg P L) : Prop where
  loc : c.loc = c'.loc
  pend : ∀ p, c.pend p = (c'.pend p).map (T + ·)
  bpend : ∀ p, c.bpend p = (c'.bpend p).map (T + ·)

/-- Shift the operation named by a response by `T`. -/
def shiftEv {Y Op Res : Type} (T : ℕ) : Option (Ev P Y Op Res) → Option (Ev P Y Op Res)
  | some (.res a r) => some (.res (T + a) r)
  | e => e

lemma elStep_delay {T : ℕ} {c c' : ECfg P L} (h : DelayRel T c c') (n : ℕ) (l : ELab P HOp BRes) :
    Option.Rel (fun o o' => DelayRel T o.1 o'.1 ∧ o.2.1 = shiftEv T o'.2.1 ∧
        o.2.2 = shiftEv T o'.2.2)
      (elStep I (T + n) c l) (elStep I n c' l) := by
  obtain ⟨c1, c2, c3⟩ := c
  obtain ⟨c1', c2', c3'⟩ := c'
  obtain ⟨hl, hp, hb⟩ := h
  simp only at hl hp hb
  subst hl
  have upd : ∀ (f g : P → Option ℕ), (∀ q, f q = (g q).map (T + ·)) → ∀ (p : P) (v : Option ℕ),
      ∀ q, Function.update f p (v.map (T + ·)) q = (Function.update g p v q).map (T + ·) := by
    intro f g hfg p v q
    by_cases hq : q = p
    · subst hq; simp
    · simp [Function.update_of_ne hq, hfg q]
  cases l with
  | inv p op =>
    simp only [elStep, hp p]
    rcases hq : c2' p with _ | a
    · simp only [Option.map_none, if_true]
      refine Option.Rel.some ⟨⟨rfl, fun q => ?_, hb⟩, rfl, rfl⟩
      simpa using upd c2 c2' hp p (some n) q
    · simp only [Option.map_some, reduceCtorEq, if_false]; exact Option.Rel.none
  | step p =>
    simp only [elStep, hp p, hb p]
    rcases c2' p with _ | a
    · exact Option.Rel.none
    rcases c3' p with _ | b
    · simp only [Option.map_some, Option.map_none]
      cases c1 p |> I.act p with
      | call x o k =>
        refine Option.Rel.some ⟨⟨rfl, hp, fun q => ?_⟩, rfl, rfl⟩
        simpa using upd c3 c3' hb p (some n) q
      | loc l => exact Option.Rel.some ⟨⟨rfl, hp, hb⟩, rfl, rfl⟩
      | ret r l =>
        refine Option.Rel.some ⟨⟨rfl, fun q => ?_, hb⟩, rfl, rfl⟩
        simpa using upd c2 c2' hp p none q
    · simp only [Option.map_some]; exact Option.Rel.none
  | bres p r =>
    simp only [elStep, hb p]
    rcases c3' p with _ | b
    · exact Option.Rel.none
    · simp only [Option.map_some]
      cases c1 p |> I.act p with
      | call x o k =>
        refine Option.Rel.some ⟨⟨rfl, hp, fun q => ?_⟩, rfl, rfl⟩
        simpa using upd c3 c3' hb p none q
      | loc l => exact Option.Rel.none
      | ret r' l => exact Option.Rel.none

variable (lab : ℕ → Option (ELab P HOp BRes)) (T : ℕ)

lemma cfg_delay_le : ∀ n ≤ T, (elSys I).cfg (delayLab lab T) n = (elSys I).init := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [elSys_cfg_succ, show delayLab lab T n = none from if_pos (by omega)]
    exact ih (by omega)

lemma delayRel_run : ∀ n, DelayRel T ((elSys I).cfg (delayLab lab T) (T + n)) ((elSys I).cfg lab n) := by
  intro n
  induction n with
  | zero =>
    rw [Nat.add_zero, cfg_delay_le I lab T T le_rfl]
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    rw [← Nat.add_assoc, elSys_cfg_succ, elSys_cfg_succ,
      show delayLab lab T (T + n) = lab n by simp [delayLab]]
    rcases lab n with _ | l
    · exact ih
    · simp only [Option.bind_some]
      have := elStep_delay I ih n l
      revert this
      generalize elStep I (T + n) _ l = o1
      generalize elStep I n _ l = o2
      intro this
      cases this with
      | some h => exact h.1
      | none => exact ih

lemma out_delay (n : ℕ) :
    Option.Rel (fun o o' => DelayRel T o.1 o'.1 ∧ o.2.1 = shiftEv T o'.2.1 ∧
        o.2.2 = shiftEv T o'.2.2)
      ((elSys I).out (delayLab lab T) (T + n)) ((elSys I).out lab n) := by
  rw [LSys.out_eq, LSys.out_eq, show delayLab lab T (T + n) = lab n by simp [delayLab]]
  rcases lab n with _ | l
  · exact Option.Rel.none
  · exact elStep_delay I (delayRel_run I lab T n) n l

lemma hist_delay (n : ℕ) :
    (elSys I).hist (delayLab lab T) (T + n) = shiftEv T ((elSys I).hist lab n) := by
  have := out_delay I lab T n
  simp only [LSys.hist]
  revert this
  generalize (elSys I).out (delayLab lab T) (T + n) = o1
  generalize (elSys I).out lab n = o2
  intro this
  cases this with
  | some h => simp [h.2.1]
  | none => rfl

lemma hist_delay_lt {n : ℕ} (hn : n < T) : (elSys I).hist (delayLab lab T) n = none := by
  have : delayLab lab T n = none := if_pos hn
  simp [LSys.hist, (elSys I).out_none_of_lab this]

lemma proper_delay (h : (elSys I).Proper lab) : (elSys I).Proper (delayLab lab T) := by
  intro n l hl
  by_cases hn : n < T
  · simp [delayLab, hn] at hl
  obtain ⟨m, rfl⟩ : ∃ m, n = T + m := ⟨n - T, by omega⟩
  rw [show delayLab lab T (T + m) = lab m by simp [delayLab]] at hl
  have h2 := h m l hl
  have := elStep_delay I (delayRel_run I lab T m) m l
  change elStep I _ _ l ≠ none
  change elStep I m _ l ≠ none at h2
  revert this h2
  generalize elStep I (T + m) _ l = o1
  generalize elStep I m _ l = o2
  intro this h2
  cases this with
  | some _ => simp
  | none => exact absurd rfl h2

end Delay

/-! ### Solo runs in implementations without shared objects -/

section NoShared

variable {P HOp HRes L : Type} [DecidableEq P] (I : Impl P HOp HRes Empty Empty Empty L)

lemma ns_bpend (lab : ℕ → Option (ELab P HOp Empty)) (n : ℕ) (p : P) :
    ((elSys I).cfg lab n).bpend p = none := by
  rcases h : ((elSys I).cfg lab n).bpend p with _ | b
  · rfl
  · obtain ⟨-, x, -, -, -, -⟩ := el_bpend_inv I lab n p b h
    exact x.elim

lemma ns_step_enabled (lab : ℕ → Option (ELab P HOp Empty)) (n : ℕ) {p : P}
    (hp : ((elSys I).cfg lab n).pend p ≠ none) :
    elStep I n ((elSys I).cfg lab n) (.step p) ≠ none := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hp
  simp only [elStep, ha, ns_bpend I lab n p]
  cases I.act p (((elSys I).cfg lab n).loc p) with
  | call x _ _ => exact x.elim
  | loc l => simp
  | ret r l => simp

lemma ns_step_out (lab : ℕ → Option (ELab P HOp Empty)) (k : ℕ) {p : P} {a : ℕ}
    (hl : lab k = some (.step p)) (ha : ((elSys I).cfg lab k).pend p = some a) :
    ((elSys I).hist lab k = none ∧ ((elSys I).cfg lab (k + 1)).pend = ((elSys I).cfg lab k).pend) ∨
    (∃ r, (elSys I).hist lab k = some (.res a r) ∧
      ((elSys I).cfg lab (k + 1)).pend = Function.update ((elSys I).cfg lab k).pend p none) := by
  rw [elSys_hist, elSys_cfg_succ, hl]
  have hb := ns_bpend I lab k p
  generalize (elSys I).cfg lab k = c at ha hb ⊢
  simp only [Option.bind_some, elStep, ha, hb]
  cases I.act p (c.loc p) with
  | call x _ _ => exact x.elim
  | loc l => left; simp
  | ret r l => right; exact ⟨r, by simp, by simp⟩

/-- The scheduler of a solo run of `p` performing `op`, invoked at time `n`. -/
def soloSched (p : P) (op : HOp) (n k : ℕ) (c : ECfg P L) : Option (ELab P HOp Empty) :=
  if k = n then some (.inv p op) else if (c.pend p).isSome then some (.step p) else none

/-- `p` runs `op` alone from time `n` (after the prefix `pre`). -/
def soloRun (pre : ℕ → Option (ELab P HOp Empty)) (p : P) (op : HOp) (n : ℕ) :
    ℕ → Option (ELab P HOp Empty) :=
  (elSys I).sched pre n (soloSched p op n)

variable {I}

/-- A solo run of a wait-free implementation without shared objects: `p` invokes `op` at `n`,
takes steps until it responds at some `j > n`, and then the execution stops; the other
processes are unaffected. -/
theorem soloRun_spec
    (hwf : (elSys I).WaitFree ELab.proc (ELAdm I noBase))
    {pre : ℕ → Option (ELab P HOp Empty)} (hpre : (elSys I).Proper pre) {n : ℕ} {p : P}
    (hidle : ((elSys I).cfg pre n).pend p = none) (op : HOp) :
    let E := soloRun I pre p op n
    (elSys I).Proper E ∧ (∀ k < n, E k = pre k) ∧ (∀ k l, n ≤ k → E k = some l → l.proc = p) ∧
    (elSys I).hist E n = some (.inv p () op) ∧
    ∃ j r, n < j ∧ (elSys I).hist E j = some (.res n r) ∧
      (∀ k, n < k → k ≤ j → ∀ q x o, (elSys I).hist E k ≠ some (.inv q x o)) ∧
      (∀ k, j < k → E k = none) ∧
      (∀ q, ((elSys I).cfg E (j + 1)).pend q = ((elSys I).cfg E n).pend q) := by
  intro E
  have hagree : ∀ k < n, E k = pre k := fun k hk => (elSys I).sched_of_lt pre _ hk
  have hcfgn : (elSys I).cfg E n = (elSys I).cfg pre n := (elSys I).cfg_congr hagree n le_rfl
  have hEge : ∀ k, n ≤ k → E k = soloSched p op n k ((elSys I).cfg E k) :=
    fun k hk => (elSys I).sched_of_ge pre _ hk
  have hEn : E n = some (.inv p op) := by rw [hEge n le_rfl]; simp [soloSched]
  have hproper : (elSys I).Proper E := by
    intro k l hl
    rcases lt_trichotomy k n with hk | rfl | hk
    · rw [hagree k hk] at hl
      rw [(elSys I).cfg_congr (fun i hi => hagree i (lt_trans hi hk)) k le_rfl]
      exact hpre k l hl
    · rw [hEn] at hl
      obtain rfl := Option.some_injective _ hl
      have : elStep I k ((elSys I).cfg pre k) (.inv p op) ≠ none := by simp [elStep, hidle]
      rw [hcfgn]; exact this
    · rw [hEge k hk.le] at hl
      simp only [soloSched, show k ≠ n by omega, if_false] at hl
      split_ifs at hl with hs
      cases hl
      exact ns_step_enabled I E k (by simpa [Option.isSome_iff_ne_none] using hs)
  have hprocs : ∀ k l, n ≤ k → E k = some l → l.proc = p := by
    intro k l hk hl
    rw [hEge k hk] at hl
    simp only [soloSched] at hl
    split_ifs at hl <;> cases hl <;> rfl
  have hWF := el_wellFormed_hist I E
  have hstep := el_pendStep I E
  have hHn : (elSys I).hist E n = some (.inv p () op) := by
    rw [elSys_hist, hEn]; simp [elStep, hcfgn, hidle]
  have hPn1 : ((elSys I).cfg E (n + 1)).pend = Function.update ((elSys I).cfg E n).pend p (some n) := by
    rcases hstep n with ⟨h1, -⟩ | ⟨q, x, o, h2, -, h3⟩ | ⟨q, a, r, h2, -⟩
    · rw [hHn] at h1; cases h1
    · rw [hHn] at h2; cases h2; exact h3
    · rw [hHn] at h2; cases h2
  -- some response to `n`
  have hex : ∃ j r, (elSys I).hist E j = some (.res n r) := by
    by_contra hno
    push_neg at hno
    have hpend : ∀ k, n < k → ((elSys I).cfg E k).pend p = some n := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rw [hPn1]; simp
      | succ k hk ih =>
        rcases hstep k with ⟨-, h1⟩ | ⟨q, x, o, h2, h3, h4⟩ | ⟨q, a, r, h2, h3, h4⟩
        · beta_reduce at h1; rw [h1]; exact ih
        · beta_reduce at h3 h4
          have hq : q ≠ p := fun h => by subst h; rw [ih] at h3; cases h3
          rw [h4, Function.update_of_ne (Ne.symm hq)]; exact ih
        · beta_reduce at h3 h4
          by_cases hq : q = p
          · subst hq; rw [ih] at h3; cases h3; exact absurd h2 (hno k r)
          · rw [h4, Function.update_of_ne (Ne.symm hq)]; exact ih
    have := hwf E ((elAdm_noBase I).2 hproper) n p op hHn (fun N => by
      refine ⟨max N (n + 1), le_max_left _ _, .step p, ?_, rfl⟩
      rw [hEge _ (by omega)]
      simp [soloSched, show max N (n + 1) ≠ n by omega, hpend (max N (n + 1)) (by omega)])
    obtain ⟨j, r, hj⟩ := this
    exact hno j r hj
  classical
  let j := Nat.find hex
  obtain ⟨r, hjr⟩ := Nat.find_spec hex
  have hjmin : ∀ k < j, ∀ r, (elSys I).hist E k ≠ some (.res n r) := fun k hk r h =>
    Nat.find_min hex hk ⟨r, h⟩
  have hnj : n < j := (hWF.res_inv n j r hjr).1
  -- before `j`, only `p`'s operation `n` is pending among `p`'s, others unchanged
  have hmid : ∀ k, n < k → k ≤ j →
      ((elSys I).cfg E k).pend = Function.update ((elSys I).cfg E n).pend p (some n) := by
    intro k hk hkj
    induction k, hk using Nat.le_induction with
    | base => exact hPn1
    | succ k hk ih =>
      have ih := ih (by omega)
      have hk' : E k = some (.step p) := by
        rw [hEge k (by omega)]; simp [soloSched, show k ≠ n by omega, ih]
      rcases ns_step_out I E k hk' (a := n) (by rw [ih]; simp) with ⟨-, h1⟩ | ⟨r', h2, -⟩
      · rw [h1, ih]
      · exact absurd h2 (hjmin k (by omega) r')
  have hj' : E j = some (.step p) := by
    rw [hEge j (by omega)]; simp [soloSched, show j ≠ n by omega, hmid j hnj le_rfl]
  have hPj1 : ((elSys I).cfg E (j + 1)).pend = ((elSys I).cfg E n).pend := by
    rcases ns_step_out I E j hj' (a := n) (by rw [hmid j hnj le_rfl]; simp) with ⟨h1, -⟩ | ⟨r', -, h2⟩
    · rw [h1] at hjr; cases hjr
    · rw [h2, hmid j hnj le_rfl]
      funext q
      by_cases hq : q = p
      · subst hq; simp [hcfgn, hidle]
      · simp [Function.update_of_ne hq]
  have hafter : ∀ k, j < k → E k = none ∧ ((elSys I).cfg E k).pend = ((elSys I).cfg E n).pend := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      refine ⟨?_, hPj1⟩
      rw [hEge _ (by omega)]; simp [soloSched, show j + 1 ≠ n by omega, hPj1, hcfgn, hidle]
    | succ k hk ih =>
      have hcfg : ((elSys I).cfg E (k + 1)).pend = ((elSys I).cfg E n).pend := by
        rw [elSys_cfg_succ, ih.1]; exact ih.2
      refine ⟨?_, hcfg⟩
      rw [hEge _ (by omega)]; simp [soloSched, show k + 1 ≠ n by omega, hcfg, hcfgn, hidle]
  refine ⟨hproper, hagree, hprocs, hHn, j, r, hnj, hjr, fun k hk hkj q x o h => ?_,
    fun k hk => (hafter k hk).1, fun q => by rw [hPj1]⟩
  have hk' : E k = some (.step p) := by
    rw [hEge k (by omega)]; simp [soloSched, show k ≠ n by omega, hmid k hk hkj]
  rcases ns_step_out I E k hk' (a := n) (by rw [hmid k hk hkj]; simp) with ⟨h1, -⟩ | ⟨r', h2, -⟩
  · rw [h1] at h; cases h
  · rw [h2] at h; cases h

end NoShared

/-! ### Driving the implemented object into a reachable state -/

section Drive

variable {P HOp HRes Q L : Type} [DecidableEq P] {I : Impl P HOp HRes Empty Empty Empty L}

/-- `lab` is a run of process `p₂` alone, stopped at `T₀` with every process idle. -/
structure SoloPrefix (I : Impl P HOp HRes Empty Empty Empty L) (p₂ : P)
    (lab : ℕ → Option (ELab P HOp Empty)) (T₀ : ℕ) : Prop where
  proper : (elSys I).Proper lab
  none_ge : ∀ k, T₀ ≤ k → lab k = none
  procs : ∀ k l, lab k = some l → l.proc = p₂
  idle : ∀ q, ((elSys I).cfg lab T₀).pend q = none

/-- In every linearization of every extension of `lab`, the object is in state `q` once all the
operations invoked before `T₀` (and only those) have been linearized. -/
def Leads (I : Impl P HOp HRes Empty Empty Empty L) (T : ObjType Q HOp HRes) (q₀ : Q)
    (lab : ℕ → Option (ELab P HOp Empty)) (T₀ : ℕ) (q : Q) : Prop :=
  ∀ E, (elSys I).Proper E → (∀ k < T₀, E k = lab k) →
    ∀ S, IsTLin (fun _ => T.initAt q₀) ((elSys I).hist E) 0 S →
    ∀ qs : ℕ → Q, qs 0 = q₀ →
    (∀ k, SeqStep (T.initAt q₀) ((elSys I).hist E) () (S k) (qs k) (qs (k + 1))) →
    ∀ k, (∀ i < k, ∀ a r, S i = some (a, r) → a < T₀) →
      (∀ a, a < T₀ → Invoked ((elSys I).hist E) a → ∃ i < k, ∃ r, S i = some (a, r)) → qs k = q

lemma leads_zero (T : ObjType Q HOp HRes) (q₀ : Q) : Leads I T q₀ (fun _ => none) 0 q₀ := by
  intro E _ _ S _ qs hq0 hqs k hk _
  clear * - hq0 hqs hk
  induction k with
  | zero => exact hq0
  | succ k ih =>
    have h := hqs k
    rcases hSk : S k with _ | ⟨a, r⟩
    · rw [hSk] at h; simp only [SeqStep] at h; rw [h]; exact ih (fun i hi => hk i (by omega))
    · exact absurd (hk k (by omega) a r hSk) (Nat.not_lt_zero _)

lemma soloPrefix_zero (p₂ : P) : SoloPrefix I p₂ (fun _ => none) 0 :=
  ⟨fun _ _ h => (by cases h), fun _ _ => rfl, fun _ _ h => (by cases h), fun _ => rfl⟩

/-- Operations invoked before an idle point complete before it. -/
lemma completed_before_idle {lab E : ℕ → Option (ELab P HOp Empty)} {T₀ : ℕ}
    (hidle : ∀ q, ((elSys I).cfg lab T₀).pend q = none) (hE : ∀ k < T₀, E k = lab k)
    {a : ℕ} (ha : a < T₀) (hinv : Invoked ((elSys I).hist E) a) :
    ∃ j < T₀, ∃ r, (elSys I).hist E j = some (.res a r) := by
  obtain ⟨p, x, op, hp⟩ := hinv
  have hcfg := (elSys I).cfg_congr hE T₀ le_rfl
  have hne : ((elSys I).cfg E T₀).pend p ≠ some a := by rw [hcfg, hidle p]; simp
  exact (pendInv_all (fun _ => rfl) (el_pendStep I E) T₀).done p a x op ha hp hne

/-- If every operation invoked before `T₀` completes before the operation `c ≥ T₀` is invoked,
they all precede `c` in a linearization. -/
lemma early_before {H : History P Unit HOp HRes} {spec : Unit → ObjType Q HOp HRes} {S : SeqHist HRes}
    (hS : IsTLin spec H 0 S) {T₀ c kc : ℕ} {rc : HRes} (hc : T₀ ≤ c) (hkc : S kc = some (c, rc))
    (hdone : ∀ a, a < T₀ → Invoked H a → ∃ j < T₀, ∃ r, H j = some (.res a r)) :
    ∀ a, a < T₀ → Invoked H a → ∃ i < kc, ∃ r, S i = some (a, r) := by
  intro a ha hinv
  obtain ⟨j, hj, r, hjr⟩ := hdone a ha hinv
  obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ :=
    hS.rt a c j r hjr (Nat.zero_le _) (by omega) (hS.legal.1 kc c rc hkc) ⟨kc, rc, hkc⟩
  have := hS.nodup k2 kc c r2 rc h2 hkc
  exact ⟨k1, by omega, r1, h1⟩

lemma qs_const {T : ObjType Q HOp HRes} {H : History P Unit HOp HRes} {S : SeqHist HRes}
    {qs : ℕ → Q} (hqs : ∀ k, SeqStep T H () (S k) (qs k) (qs (k + 1))) {a b : ℕ} (hab : a ≤ b)
    (hnone : ∀ i, a ≤ i → i < b → S i = none) : qs b = qs a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have h := hqs b
    rw [hnone b hab (by omega)] at h
    simp only [SeqStep] at h
    rw [h, ih (fun i h1 h2 => hnone i h1 (by omega))]

/-- One more solo operation of `p₂` drives the object from `q` to `q'`. -/
theorem leads_step {T : ObjType Q HOp HRes} {q₀ : Q} (hdet : T.Deterministic)
    (hwf : (elSys I).WaitFree ELab.proc (ELAdm I noBase)) {p₂ : P}
    {lab : ℕ → Option (ELab P HOp Empty)} {T₀ : ℕ} (hpre : SoloPrefix I p₂ lab T₀)
    {q : Q} (hq : Leads I T q₀ lab T₀ q) {op : HOp} {r : HRes} {q' : Q} (hδ : T.δ q op r q') :
    ∃ lab' T₀', SoloPrefix I p₂ lab' T₀' ∧ Leads I T q₀ lab' T₀' q' := by
  obtain ⟨hprop, hagr, hprocs, hinvT, j, rb, hTj, hjr, hnoinv, hafter, hpendj⟩ :=
    soloRun_spec hwf hpre.proper (hpre.idle p₂) op
  set E0 := soloRun I lab p₂ op T₀
  refine ⟨E0, j + 1, ⟨hprop, fun k hk => hafter k (by omega), fun k l hl => ?_, fun q => ?_⟩, ?_⟩
  · by_cases hk : k < T₀
    · rw [hagr k hk] at hl; exact hpre.procs k l hl
    · exact hprocs k l (by omega) hl
  · rw [hpendj q, (elSys I).cfg_congr hagr T₀ le_rfl]; exact hpre.idle q
  intro E hE hEagr S hS qs hq0 hqs k hk1 hk2
  have hEagr0 : ∀ k < T₀, E k = lab k := fun k hk => (hEagr k (by omega)).trans (hagr k hk)
  have hH : ∀ i < j + 1, (elSys I).hist E i = (elSys I).hist E0 i := fun i hi =>
    (elSys I).hist_congr hEagr hi
  have hTinv : (elSys I).hist E T₀ = some (.inv p₂ () op) := by rw [hH T₀ (by omega)]; exact hinvT
  have hjres : (elSys I).hist E j = some (.res T₀ rb) := by rw [hH j (by omega)]; exact hjr
  obtain ⟨kc, hkck, rc, hSkc⟩ := hk2 T₀ (by omega) ⟨p₂, (), op, hTinv⟩
  obtain ⟨kc', hkc'⟩ := hS.resp T₀ j rb hjres (Nat.zero_le _)
  have := hS.nodup kc kc' T₀ rc rb hSkc hkc'
  subst this
  have hkc := hkc'
  rw [hkc] at hSkc; cases hSkc
  have hdone : ∀ a, a < T₀ → Invoked ((elSys I).hist E) a →
      ∃ j' < T₀, ∃ r, (elSys I).hist E j' = some (.res a r) :=
    fun a ha hinv => completed_before_idle hpre.idle hEagr0 ha hinv
  have hbefore := early_before hS le_rfl hkc hdone
  -- entries of `S` are operations invoked before `j + 1`, i.e. before `T₀` or `T₀` itself
  have hentry : ∀ i < k, ∀ a r, S i = some (a, r) → a < T₀ ∨ a = T₀ := by
    intro i hi a r hia
    have ha := hk1 i hi a r hia
    by_contra hcon; push_neg at hcon
    obtain ⟨p, x, o, hp⟩ := hS.legal.1 i a r hia
    rw [hH a ha] at hp
    exact hnoinv a (by omega) (by omega) p x o hp
  have hqkc : qs kc = q := hq E hE hEagr0 S hS qs hq0 hqs kc
    (fun i hi a r hia => by
      rcases hentry i (by omega) a r hia with h | rfl
      · exact h
      · have := hS.nodup i kc _ r rb hia hkc; omega) hbefore
  have hstep := hqs kc
  rw [hkc] at hstep
  obtain ⟨p, op', hop, hδ'⟩ := hstep.onObj ⟨p₂, op, hTinv⟩
  rw [hTinv] at hop; cases hop
  rw [hqkc] at hδ'
  have hq' : qs (kc + 1) = q' := by
    obtain ⟨⟨r0, q0⟩, -, huniq⟩ := hdet q op
    have e1 := huniq (rb, qs (kc + 1)) hδ'
    have e2 := huniq (r, q') hδ
    simp only [Prod.ext_iff] at e1 e2
    rw [e1.2, e2.2]
  rw [← hq']
  apply qs_const hqs (by omega)
  intro i hi1 hi2
  rcases hSi : S i with _ | ⟨a, r'⟩
  · rfl
  · exfalso
    rcases hentry i hi2 a r' hSi with h | rfl
    · obtain ⟨i', hi', r'', hi''⟩ := hbefore a h (hS.legal.1 i a r' hSi)
      have := hS.nodup i i' a r' r'' hSi hi''; omega
    · have := hS.nodup i kc _ r' rb hSi hkc; omega

/-- After driving the object into state `q` with `p₂` alone, a solo run of `p₁` (with the same
behaviour as from the initial configuration) must return a correct response for state `q`. -/
theorem leads_final {T : ObjType Q HOp HRes} {q₀ : Q}
    (hlin : (elSys I).IsLinearizable (ELAdm I noBase) (T.initAt q₀))
    (hwf : (elSys I).WaitFree ELab.proc (ELAdm I noBase)) {p₁ p₂ : P} (hne : p₁ ≠ p₂)
    {lab : ℕ → Option (ELab P HOp Empty)} {T₀ : ℕ} (hpre : SoloPrefix I p₂ lab T₀)
    {q : Q} (hq : Leads I T q₀ lab T₀ q) (op : HOp) {jα : ℕ} {rα : HRes}
    (hα : (elSys I).hist (soloRun I (fun _ => none) p₁ op 0) jα = some (.res 0 rα)) :
    ∃ q', T.δ q op rα q' := by
  set α := soloRun I (fun _ => none) p₁ op 0 with hαdef
  obtain ⟨hαprop, -, hαprocs, hαinv, jα', rα', h0j, hαres, hαnoinv, hαafter, -⟩ :=
    soloRun_spec (I := I) (pre := fun _ => none) hwf (fun _ _ h => by cases h) (n := 0) (p := p₁)
      rfl op
  have hjj := (el_wellFormed_hist I α).res_unique 0 jα jα' rα rα' hα hαres
  subst hjj
  rw [hα] at hαres; cases hαres
  let E : ℕ → Option (ELab P HOp Empty) := fun k => if k < T₀ then lab k else α (k - T₀)
  have hEagr : ∀ k < T₀, E k = lab k := fun k hk => if_pos hk
  have hEge : ∀ k, T₀ ≤ k → E k = α (k - T₀) := fun k hk => if_neg (by omega)
  have hproj : projLab E p₁ = delayLab α T₀ := by
    funext k
    simp only [projLab, delayLab]
    by_cases hk : k < T₀
    · rw [if_pos hk, hEagr k hk]
      rcases hl : lab k with _ | l
      · rfl
      · simp [hpre.procs k l hl, Ne.symm hne]
    · rw [if_neg hk, hEge k (by omega)]
      rcases hl : α (k - T₀) with _ | l
      · rfl
      · simp [hαprocs _ l (Nat.zero_le _) hl]
  have hprop : (elSys I).Proper E := by
    intro k l hl
    by_cases hk : k < T₀
    · rw [hEagr k hk] at hl
      rw [(elSys I).cfg_congr (fun i hi => hEagr i (lt_trans hi hk)) k le_rfl]
      exact hpre.proper k l hl
    · have hlp : l.proc = p₁ := by rw [hEge k (by omega)] at hl; exact hαprocs _ l (Nat.zero_le _) hl
      have hpl : delayLab α T₀ k = some l := by rw [← hproj]; simp [projLab, hl, hlp]
      have h2 := proper_delay I α T₀ hαprop k l hpl
      have hag := agreeP_proj I E p₁ k
      rw [hproj] at hag
      have := elStep_agree I k l (hlp ▸ hag)
      change elStep I k _ l ≠ none at h2
      change elStep I k _ l ≠ none
      revert this h2
      generalize elStep I k ((elSys I).cfg (delayLab α T₀) k) l = o1
      generalize elStep I k ((elSys I).cfg E k) l = o2
      intro this h2
      cases this with
      | some _ => simp
      | none => exact absurd rfl h2
  have hhistE : ∀ k, T₀ ≤ k → (elSys I).hist E k = shiftEv T₀ ((elSys I).hist α (k - T₀)) := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = T₀ + m := ⟨k - T₀, by omega⟩
    rw [Nat.add_sub_cancel_left, ← hist_delay I α T₀ m]
    rcases hl : E (T₀ + m) with _ | l
    · have h1 : (elSys I).hist E (T₀ + m) = none := by
        simp [LSys.hist, (elSys I).out_none_of_lab hl]
      have h2 : delayLab α T₀ (T₀ + m) = none := by rw [← hproj]; simp [projLab, hl]
      rw [h1]; simp [LSys.hist, (elSys I).out_none_of_lab h2]
    · have hlp : l.proc = p₁ := by
        rw [hEge _ (by omega)] at hl; exact hαprocs _ l (Nat.zero_le _) hl
      rw [← (hist_proj I hl hlp).1, hproj]
  have hEinv : ∀ k, T₀ ≤ k → ∀ p x o, (elSys I).hist E k = some (.inv p x o) → k = T₀ := by
    intro k hk p x o h
    rw [hhistE k hk] at h
    rcases hh : (elSys I).hist α (k - T₀) with _ | (⟨p', x', o'⟩ | ⟨a', r'⟩) <;>
      rw [hh] at h <;> simp [shiftEv] at h
    by_contra hkT
    by_cases hkj : k - T₀ ≤ jα
    · exact hαnoinv (k - T₀) (by omega) hkj p' x' o' hh
    · have h0 : (elSys I).out α (k - T₀) = none :=
        (elSys I).out_none_of_lab (hαafter (k - T₀) (by omega))
      rw [show (elSys I).hist α (k - T₀) = none by simp [LSys.hist, h0]] at hh
      cases hh
  have hET : (elSys I).hist E T₀ = some (.inv p₁ () op) := by
    rw [hhistE T₀ le_rfl, Nat.sub_self, hαinv]; rfl
  have hEres : (elSys I).hist E (T₀ + jα) = some (.res T₀ rα) := by
    rw [hhistE _ (by omega), Nat.add_sub_cancel_left, hα]; rfl
  obtain ⟨S, hS⟩ := hlin E ((elAdm_noBase I).2 hprop)
  obtain ⟨qs, hqs0, hqs⟩ := hS.legal.2 ()
  obtain ⟨kc, hkc⟩ := hS.resp T₀ (T₀ + jα) rα hEres (Nat.zero_le _)
  have hdone : ∀ a, a < T₀ → Invoked ((elSys I).hist E) a →
      ∃ j' < T₀, ∃ r, (elSys I).hist E j' = some (.res a r) :=
    fun a ha hinv => completed_before_idle hpre.idle hEagr ha hinv
  have hqkc : qs kc = q := hq E hprop hEagr S hS qs hqs0 hqs kc
    (fun i hi a r hia => by
      by_contra hge; push_neg at hge
      obtain ⟨p, x, o, hp⟩ := hS.legal.1 i a r hia
      have := hEinv a hge p x o hp
      subst this
      have := hS.nodup i kc _ r rα hia hkc; omega)
    (early_before hS le_rfl hkc hdone)
  have hstep := hqs kc
  rw [hkc] at hstep
  obtain ⟨p, op', hop, hδ⟩ := hstep.onObj ⟨p₁, op, hET⟩
  rw [hET] at hop; cases hop
  rw [hqkc] at hδ
  exact ⟨_, hδ⟩

end Drive

/-! ### Trivial types and their implementation -/

section Trivial

variable {P HOp HRes Q : Type} [DecidableEq P]

/-- `q` is reachable from `q₀` by a sequence of operations. -/
def Reach (T : ObjType Q HOp HRes) : Q → Q → Prop :=
  Relation.ReflTransGen fun q q' => ∃ op r, T.δ q op r q'

/-- **Definition 13** (without computability): `T` is **trivial** if some `r q₀ op` is a correct
response to `op` in every state reachable from the initial state `q₀`. -/
def Trivial (T : ObjType Q HOp HRes) : Prop :=
  ∃ r : Q → HOp → HRes, ∀ q₀ ∈ T.init, ∀ op q, Reach T q₀ q → ∃ q', T.δ q op (r q₀ op) q'

/-- The implementation of a trivial type: answer `rf op` at once. -/
def trivImpl (rf : HOp → HRes) : Impl P HOp HRes Empty Empty Empty (Option HOp) where
  locInit _ := none
  invoke _ _ op := some op
  act _ l := match l with
    | some op => .ret (rf op) none
    | none => .loc none

variable (rf : HOp → HRes)

lemma trivImpl_inv (lab : ℕ → Option (ELab P HOp Empty)) :
    ∀ n p a, ((elSys (trivImpl (P := P) rf)).cfg lab n).pend p = some a →
      ∃ op, ((elSys (trivImpl rf)).cfg lab n).loc p = some op ∧
        (elSys (trivImpl rf)).hist lab a = some (.inv p () op) := by
  intro n
  induction n with
  | zero => intro p a h; simp [LSys.cfg_zero, elSys] at h
  | succ n ih =>
    intro p a h
    have hh : (elSys (trivImpl (P := P) rf)).hist lab n =
        ((lab n).bind (elStep (trivImpl rf) n ((elSys (trivImpl rf)).cfg lab n))).bind (·.2.1) :=
      elSys_hist _ lab n
    rw [elSys_cfg_succ] at h ⊢
    revert h hh
    generalize (elSys (trivImpl (P := P) rf)).cfg lab n = c at ih
    intro h hh
    rcases hl : lab n with _ | l
    · rw [hl] at h; simpa [hl] using ih p a h
    rw [hl] at h hh
    simp only [Option.bind_some] at h hh ⊢
    cases l with
    | bres q r => exact r.elim
    | inv q op =>
      simp only [elStep] at h hh ⊢
      split_ifs at h hh ⊢ with hq
      · simp only [Option.elim_some] at h ⊢
        by_cases hpq : p = q
        · subst hpq
          simp at h; subst h
          exact ⟨op, by simp [trivImpl], by simpa using hh⟩
        · simp only [Function.update_of_ne hpq] at h ⊢; exact ih p a h
      · exact ih p a h
    | step q =>
      simp only [elStep] at h hh ⊢
      rcases hpq : c.pend q with _ | a' <;> rcases hbq : c.bpend q with _ | b' <;>
        simp only [hpq, hbq] at h hh ⊢
      all_goals try exact ih p a h
      rcases hlq : c.loc q with _ | op
      · obtain ⟨op, hop, -⟩ := ih q a' hpq; rw [hlq] at hop; cases hop
      · simp only [trivImpl, hlq, Option.elim_some] at h ⊢
        by_cases hpq' : p = q
        · subst hpq'; simp at h
        · simp only [Function.update_of_ne hpq'] at h ⊢; exact ih p a h

lemma trivImpl_res {lab : ℕ → Option (ELab P HOp Empty)} {j a : ℕ} {r : HRes}
    (h : (elSys (trivImpl (P := P) rf)).hist lab j = some (.res a r)) :
    ∃ p op, (elSys (trivImpl rf)).hist lab a = some (.inv p () op) ∧ r = rf op := by
  have hh := h
  rw [elSys_hist] at hh
  have hinv := trivImpl_inv rf lab j
  generalize (elSys (trivImpl (P := P) rf)).cfg lab j = c at hh hinv
  rcases hl : lab j with _ | l
  · rw [hl] at hh; simp at hh
  rw [hl] at hh
  simp only [Option.bind_some] at hh
  cases l with
  | bres q r => exact r.elim
  | inv q op => simp only [elStep] at hh; split_ifs at hh <;> simp at hh
  | step q =>
    simp only [elStep] at hh
    rcases hpq : c.pend q with _ | a' <;> rcases hbq : c.bpend q with _ | b' <;>
      simp only [hpq, hbq] at hh
    all_goals try simp at hh
    obtain ⟨op, hop, hinva⟩ := hinv q a' hpq
    simp [trivImpl, hop] at hh
    obtain ⟨rfl, rfl⟩ := hh
    exact ⟨q, op, hinva, rfl⟩

/-- The operation invoked at position `a`. -/
def opAt (H : History P Unit HOp HRes) (a : ℕ) : Option HOp :=
  match H a with
  | some (.inv _ _ op) => some op
  | _ => none

/-- The sequential history of a trivial implementation: operations at their response positions. -/
def respSeq (H : History P Unit HOp HRes) : SeqHist HRes := fun j =>
  match H j with
  | some (.res a r) => some (a, r)
  | _ => none

/-- The states of a trivial object along `respSeq`, kept reachable. -/
noncomputable def trivTraj (T : ObjType Q HOp HRes) (q₀ : Q)
    (htriv : ∀ op q, Reach T q₀ q → ∃ q', T.δ q op (rf op) q') (H : History P Unit HOp HRes) :
    ℕ → {q // Reach T q₀ q}
  | 0 => ⟨q₀, Relation.ReflTransGen.refl⟩
  | j + 1 =>
    let c := trivTraj T q₀ htriv H j
    match respSeq H j with
    | some (a, _) =>
      match opAt H a with
      | some op => ⟨Classical.choose (htriv op c.1 c.2),
          c.2.tail ⟨op, rf op, Classical.choose_spec (htriv op c.1 c.2)⟩⟩
      | none => c
    | none => c

lemma trivImpl_lin (T : ObjType Q HOp HRes) (q₀ : Q)
    (htriv : ∀ op q, Reach T q₀ q → ∃ q', T.δ q op (rf op) q') :
    (elSys (trivImpl (P := P) rf)).IsLinearizable (ELAdm (trivImpl rf) noBase) (T.initAt q₀) := by
  intro lab _
  set H := (elSys (trivImpl (P := P) rf)).hist lab
  have hWF : WellFormed H := el_wellFormed_hist _ lab
  have hS : ∀ j a r, respSeq H j = some (a, r) ↔ H j = some (.res a r) := by
    intro j a r
    simp only [respSeq]
    rcases H j with _ | (⟨p, x, op⟩ | ⟨a', r'⟩) <;> simp
  refine ⟨respSeq H, fun k k' a r r' hk hk' => hWF.res_unique a k k' r r' ((hS _ _ _).1 hk)
    ((hS _ _ _).1 hk'), ⟨fun k a r hk => ?_, fun x => ⟨fun j => (trivTraj rf T q₀ htriv H j).1,
    rfl, fun j => ?_⟩⟩, fun a j r hj => ⟨j, r, (hS _ _ _).2 hj⟩,
    fun a b j r hj _ hjb _ ⟨i, rb, hi⟩ => ?_, fun a j r hj _ => ⟨j, (hS _ _ _).2 hj⟩⟩
  · exact (hWF.res_inv a k r ((hS _ _ _).1 hk)).2
  · rcases hj : respSeq H j with _ | ⟨a, r⟩
    · show (trivTraj rf T q₀ htriv H (j + 1)).1 = _
      simp only [trivTraj, hj]
    · obtain ⟨p, op, ha, rfl⟩ := trivImpl_res rf ((hS _ _ _).1 hj)
      have hop : opAt H a = some op := by
        have ha' : H a = some (.inv p () op) := ha
        simp only [opAt, ha']
      left
      refine ⟨p, op, by cases x; exact ha, ?_⟩
      show T.δ _ op (rf op) (trivTraj rf T q₀ htriv H (j + 1)).1
      simp only [trivTraj, hj, hop]
      exact Classical.choose_spec (htriv op _ (trivTraj rf T q₀ htriv H j).2)
  · have := (hWF.res_inv b i rb ((hS _ _ _).1 hi)).1
    exact ⟨j, i, r, rb, by omega, (hS _ _ _).2 hj, hi⟩

lemma agreeP_of_no_steps {HOp' HRes' X' BOp' BRes' L' : Type}
    (I : Impl P HOp' HRes' X' BOp' BRes' L') (lab : ℕ → Option (ELab P HOp' BRes')) (p : P)
    {m n : ℕ} (hmn : m ≤ n) (hno : ∀ k, m ≤ k → k < n → ∀ l, lab k = some l → l.proc ≠ p) :
    AgreeP p ((elSys I).cfg lab m) ((elSys I).cfg lab n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl⟩
  | succ n hmn ih =>
    have ih := ih (fun k h1 h2 => hno k h1 (by omega))
    rw [elSys_cfg_succ]
    rcases hl : lab n with _ | l
    · exact ih
    · simp only [Option.bind_some]
      rcases ho : elStep I n ((elSys I).cfg lab n) l with _ | o
      · exact ih
      · have := elStep_other I ho (hno n hmn (by omega) l hl)
        exact ⟨ih.loc.trans this.loc, ih.pend.trans this.pend, ih.bpend.trans this.bpend⟩

lemma trivImpl_waitFree :
    (elSys (trivImpl (P := P) rf)).WaitFree ELab.proc (ELAdm (trivImpl rf) noBase) := by
  classical
  intro lab hadm a p op ha hinf
  have hp := hadm.1
  have hpa : ((elSys (trivImpl (P := P) rf)).cfg lab (a + 1)).pend p = some a := by
    rcases el_pendStep (trivImpl (P := P) rf) lab a with ⟨h1, -⟩ | ⟨q, x, o, h2, -, h3⟩ | ⟨q, b, r, h2, -⟩
    · rw [ha] at h1; cases h1
    · rw [ha] at h2; cases h2; simp only at h3; rw [h3]; simp
    · rw [ha] at h2; cases h2
  have hex : ∃ n, a < n ∧ LSys.StepBy ELab.proc lab n p := by
    obtain ⟨n, hn, h⟩ := hinf (a + 1); exact ⟨n, by omega, h⟩
  set n₀ := Nat.find hex
  obtain ⟨han, l, hl, hlp⟩ := Nat.find_spec hex
  have hag := agreeP_of_no_steps (trivImpl (P := P) rf) lab p (m := a + 1) (n := n₀) (by omega)
    (fun k h1 h2 l' hl' hlp' => Nat.find_min hex h2 ⟨by omega, l', hl', hlp'⟩)
  have hpn : ((elSys (trivImpl (P := P) rf)).cfg lab n₀).pend p = some a := hag.pend ▸ hpa
  obtain ⟨op', hop', -⟩ := trivImpl_inv rf lab n₀ p a hpn
  have hen := hp n₀ l hl
  have hb := ns_bpend (trivImpl (P := P) rf) lab n₀ p
  cases l with
  | bres q r => exact r.elim
  | inv q o =>
    simp only [ELab.proc] at hlp; subst hlp
    exfalso
    have : elStep (trivImpl (P := P) rf) n₀ ((elSys (trivImpl rf)).cfg lab n₀) (.inv q o) = none := by
      simp [elStep, hpn]
    exact hen this
  | step q =>
    simp only [ELab.proc] at hlp; subst hlp
    refine ⟨n₀, rf op', ?_⟩
    rw [elSys_hist, hl]
    simp only [Option.bind_some, elStep, hpn, hb, hop']
    simp [trivImpl]

end Trivial

/-! ### Proposition 14 -/

section Prop14

variable {P HOp HRes Q : Type} [DecidableEq P]

/-- **Proposition 14** of [Guerraoui–Ruppert, PODC 2014]. For at least two processes, a
deterministic type `T` has (for every initial state) a linearizable obstruction-free
implementation from some collection of eventually linearizable (wait-free) objects if and only
if `T` is trivial. -/
theorem prop14 [Finite P] [Nontrivial P] (T : ObjType Q HOp HRes) (hdet : T.Deterministic) :
    (∀ q₀ ∈ T.init, ∃ (X BOp BRes Q' L : Type) (B : X → ObjType Q' BOp BRes),
      (∀ x, (B x).init.Nonempty ∧ (B x).Total) ∧ ∃ I : Impl P HOp HRes X BOp BRes L,
      (elSys I).IsLinearizable (ELAdm I B) (T.initAt q₀) ∧
      (elSys I).ObstructionFree ELab.proc (ELAdm I B)) ↔ Trivial T := by
  constructor
  · intro h
    have hfin : T.FiniteNondet := fun q op => by
      obtain ⟨rq, -, huniq⟩ := hdet q op
      exact Set.Subsingleton.finite fun a ha b hb => (huniq a ha).trans (huniq b hb).symm
    obtain ⟨p₁, p₂, hne⟩ := exists_pair_ne P
    have key : ∀ q₀ op, ∃ ρ : HRes, q₀ ∈ T.init → ∀ q, Reach T q₀ q → ∃ q', T.δ q op ρ q' := by
      intro q₀ op
      by_cases hq₀ : q₀ ∈ T.init
      · obtain ⟨L, I, hlin, hwf⟩ := ((theorem12 T q₀ hfin).out 4 1).1 (h q₀ hq₀)
        obtain ⟨-, -, -, -, j, r, -, hjr, -⟩ :=
          soloRun_spec (I := I) (pre := fun _ => none) hwf (fun _ _ h => by cases h) (n := 0)
            (p := p₁) rfl op
        refine ⟨r, fun _ q hq => ?_⟩
        have hdrive : ∃ lab T₀, SoloPrefix I p₂ lab T₀ ∧ Leads I T q₀ lab T₀ q := by
          induction hq with
          | refl => exact ⟨_, _, soloPrefix_zero p₂, leads_zero T q₀⟩
          | tail _ hstep ih =>
            obtain ⟨op', r', hδ⟩ := hstep
            obtain ⟨lab, T₀, hpre, hq'⟩ := ih
            exact leads_step hdet hwf hpre hq' hδ
        obtain ⟨lab, T₀, hpre, hq'⟩ := hdrive
        exact leads_final hlin hwf hne hpre hq' op hjr
      · obtain ⟨⟨r, _⟩, _⟩ := hdet q₀ op
        exact ⟨r, fun h' => absurd h' hq₀⟩
    choose r hr using key
    exact ⟨r, fun q₀ hq₀ op q hq => hr q₀ op hq₀ q hq⟩
  · rintro ⟨r, hr⟩ q₀ hq₀
    exact ⟨Empty, Empty, Empty, PUnit, Option HOp, noBase, fun e => e.elim, trivImpl (r q₀),
      trivImpl_lin (r q₀) T q₀ (fun op q hq => hr q₀ hq₀ op q hq),
      (trivImpl_waitFree (r q₀)).obstructionFree⟩

end Prop14


end Podc.EventualLinParadox
