import Papers.PODC2013.MessageAdversariesVsFD.ArwOmega
import Papers.PODC2013.MessageAdversariesVsFD.Counterexample

/-!
# `Tcons` is solvable in `ARW_{3,2}[fd : Ω]`; Lemma 2 and Theorem 2 fail

Raynal–Stainer (PODC 2013) claim (Lemma 2) that every task solvable in `ARW_{n,n-1}[fd : Ω]` is
solvable in `SMP_n[adv : SOURCE, TOUR]` (one half of Theorem 2,
`ARW_{n,n-1}[fd : Ω] ≃ SMP_n[adv : SOURCE, TOUR]`). We give a wait-free `ARW[Ω]` algorithm
(`ArwCons.alg`) for `Tcons` (consensus between `p₁` and `p₂`, with `p₃` a helper whose output is
free) and prove it correct (`tcons_solvable_arw_omega`); together with
`tcons_not_solvable` (`Tcons ∉ SMP_3[adv : SOURCE, TOUR, QUORUM]`) this refutes Lemma 2, hence
Theorem 2, under the paper's semantics where every process of `SMP_n` must output
(`lemma2_false`).

## The algorithm

Processes `p₁`, `p₂` (`0`, `1`) write their input; `p₃` (`2`) decides `false` (its output is
unconstrained) and reads the input registers of `p₁`, `p₂` until it finds an input, its estimate.
Then every process loops: read the decision registers `DEC_0..2` (decide if one is set), query
`Ω`, and if `Ω` designates itself, run the next commit-adopt round `r` (rounds are run in order by
every process) on its estimate:

* write `A[r] := est`, read `A_0[r], A_1[r], A_2[r]`;
* write `B[r] := (est, values read)` (a *commit pair* if every value read is `⊥` or `est`), read
  `B_0[r], B_1[r], B_2[r]`;
* write `E[r] := (est, values read)` (a record used only by the proof, so that every invariant is
  a statement about the current configuration);
* commit `est` if every pair read is a commit pair, else adopt the value of a commit pair read if
  any, else keep `est`; on commit write `DEC := est` and decide.

## Proof

* Safety (`valid_conf`): an inductive invariant `Inv` (`inv_conf`) relating local states and
  registers; the commit-adopt properties follow from it by the usual "write then read" argument
  (`commit_pairs`, `ca_agree`, `ca_valid`), and all committed values coincide (`lock`,
  `committed_eq`) and are inputs of `p₁` or `p₂` (`committed_valid`).
* Liveness (`live`): if a correct `p₁`/`p₂` never decides, no decision register is ever written
  (`dec_none`); after `Ω` has stabilized on a correct leader `ℓ` and faulty processes stopped,
  the other processes start no new round (`others_bounded`), while `ℓ` runs rounds forever
  (`leader_progress`); a round above all rounds touched by others is run solo and commits
  (`solo_commit`), and `ℓ` writes its decision register: contradiction.
-/

namespace Podc.MessageAdversariesVsFD

namespace ArwCons

open ARW

/-! ## The algorithm -/

/-- Content of a `B` register: estimate and the vector of `A` values read. -/
abbrev BV := Bool × (Fin 3 → Option Bool)

/-- Content of an `E` register: estimate and the vector of `B` values read. -/
abbrev EV := Bool × (Fin 3 → Option BV)

/-- Registers of each process: input, decision, and per round `r` the commit-adopt registers
`A[r]`, `B[r]` and the record `E[r]` of the second collect. -/
inductive Reg where
  | inR
  | dec
  | a (r : ℕ)
  | b (r : ℕ)
  | e (r : ℕ)
  deriving DecidableEq

/-- Payload type of a register. -/
abbrev Pay : Reg → Type
  | .inR => Bool
  | .dec => Bool
  | .a _ => Bool
  | .b _ => BV
  | .e _ => EV

/-- Register values (`none` = initial value `⊥`). -/
abbrev RV (k : Reg) : Type := Option (Pay k)

/-- Program counter. -/
inductive PC where
  | start
  | getIn (b : Bool)
  | readDec (j : Fin 3)
  | query
  | writeA
  | readA (j : Fin 3)
  | writeB
  | readB (j : Fin 3)
  | writeE
  | writeDec
  | done
  deriving DecidableEq

/-- Local state. -/
structure St where
  /-- Program counter. -/
  pc : PC
  /-- Current round. -/
  r : ℕ
  /-- Current estimate. -/
  est : Bool
  /-- Decision value. -/
  dv : Bool
  /-- `A` values read in the current round. -/
  ca : Fin 3 → Option Bool
  /-- `B` values read in the current round. -/
  cb : Fin 3 → Option BV

/-- The first collect of commit-adopt allows to commit `v`: every value read is `⊥` or `v`. -/
def Flag (v : Bool) (ca : Fin 3 → Option Bool) : Prop := ∀ j, ca j = none ∨ ca j = some v

instance (v : Bool) (ca : Fin 3 → Option Bool) : Decidable (Flag v ca) := by
  unfold Flag; infer_instance

/-- The value of a "commit" pair `(v, ca)` (with `Flag v ca`) read in the second collect. -/
def cVal : Option BV → Option Bool
  | some (u, ca) => if Flag u ca then some u else none
  | none => none

/-- Every pair read in the second collect is a commit pair. -/
def AllC (cb : Fin 3 → Option BV) : Prop := ∀ j, cb j = none ∨ cVal (cb j) ≠ none

instance (cb : Fin 3 → Option BV) : Decidable (AllC cb) := by
  unfold AllC; infer_instance

/-- The value of the first commit pair read, if any. -/
def firstC (cb : Fin 3 → Option BV) : Option Bool :=
  (cVal (cb 0)).or ((cVal (cb 1)).or (cVal (cb 2)))

/-- Outcome of commit-adopt: `(true, est)` (commit) if all pairs read are commit pairs, else
adopt the value of a commit pair if any, else keep `est`. -/
def outcome (est : Bool) (cb : Fin 3 → Option BV) : Bool × Bool :=
  if AllC cb then (true, est) else (false, (firstC cb).getD est)

/-- Transition function. Processes `0`, `1` write their input; process `2` (the helper) decides
`false` and waits for an input of `0` or `1` as its estimate. Then every process loops: read the
decision registers (decide if one is set), query `Ω`, and if it is the leader run the next
commit-adopt round on its estimate; on commit, write the decision register and decide. -/
def nxt (p : Fin 3) (s : St) : Act (Fin 3) Reg RV Bool St :=
  match s.pc with
  | .start =>
    if p = 2 then .decide false { s with pc := .getIn false }
    else .write .inR (some s.est) { s with pc := .readDec 0 }
  | .getIn b => .read (if b then 1 else 0) .inR fun v =>
    match v with
    | some u => { s with est := u, pc := .readDec 0 }
    | none => { s with pc := .getIn (!b) }
  | .readDec j => .read j .dec fun v =>
    match v with
    | some u => { s with dv := u, pc := .done }
    | none => { s with pc := if j = 2 then .query else .readDec (j + 1) }
  | .query => .query fun ℓ => { s with pc := if ℓ = p then .writeA else .readDec 0 }
  | .writeA => .write (.a s.r) (some s.est) { s with pc := .readA 0 }
  | .readA j => .read j (.a s.r) fun v =>
    { s with ca := Function.update s.ca j v, pc := if j = 2 then .writeB else .readA (j + 1) }
  | .writeB => .write (.b s.r) (some (s.est, s.ca)) { s with pc := .readB 0 }
  | .readB j => .read j (.b s.r) fun v =>
    { s with cb := Function.update s.cb j v, pc := if j = 2 then .writeE else .readB (j + 1) }
  | .writeE => .write (.e s.r) (some (s.est, s.cb))
    { s with r := s.r + 1, est := (outcome s.est s.cb).2, dv := (outcome s.est s.cb).2,
             pc := if (outcome s.est s.cb).1 then .writeDec else .readDec 0 }
  | .writeDec => .write .dec (some s.dv) { s with pc := .done }
  | .done => .decide s.dv s

/-- Initial state. -/
def init (_ : Fin 3) (x : Bool) : St :=
  { pc := .start, r := 0, est := x, dv := x, ca := fun _ => none, cb := fun _ => none }

/-- The `ARW[Ω]` algorithm for `Tcons`. -/
def alg : ARW.Alg (Fin 3) Bool Bool Reg RV St where
  v₀ _ := none
  init := init
  next := nxt

/-! ## Invariants -/

/-- Configurations of the algorithm. -/
abbrev Cfg := Config (Fin 3) Reg RV Bool St

/-- Memory of one process. -/
abbrev Mem := (k : Reg) → RV k

/-- Phase within a round: `1` after writing `A`, `2` after writing `B`. -/
def ph : PC → ℕ
  | .readA _ | .writeB => 1
  | .readB _ | .writeE => 2
  | _ => 0

/-- The result of the read of `A_j[r]` by a process with state `s` and registers `m`
(`none`: not read yet; read results of completed rounds are recorded in `B[r]`). -/
def rdA (s : St) (m : Mem) (r : ℕ) (j : Fin 3) : Option (Option Bool) :=
  if r < s.r then (m (.b r)).map (fun bv => bv.2 j)
  else if r = s.r then
    match s.pc with
    | .readA i => if j < i then some (s.ca j) else none
    | .writeB | .readB _ | .writeE => some (s.ca j)
    | _ => none
  else none

/-- The result of the read of `B_j[r]` (recorded in `E[r]` for completed rounds). -/
def rdB (s : St) (m : Mem) (r : ℕ) (j : Fin 3) : Option (Option BV) :=
  if r < s.r then (m (.e r)).map (fun ev => ev.2 j)
  else if r = s.r then
    match s.pc with
    | .readB i => if j < i then some (s.cb j) else none
    | .writeE => some (s.cb j)
    | _ => none
  else none

/-- Local invariant of process `p` (state `s`, own registers `m`). -/
structure Loc (x : Fin 3 → Bool) (p : Fin 3) (s : St) (m : Mem) : Prop where
  future : ∀ r, s.r < r → m (.a r) = none ∧ m (.b r) = none ∧ m (.e r) = none
  curA : m (.a s.r) = if 1 ≤ ph s.pc then some s.est else none
  curB : m (.b s.r) = if ph s.pc = 2 then some (s.est, s.ca) else none
  curE : m (.e s.r) = none
  past : ∀ r < s.r, ∃ v ca cb, m (.a r) = some v ∧ m (.b r) = some (v, ca) ∧
    m (.e r) = some (v, cb) ∧ (r + 1 < s.r → m (.a (r + 1)) = some (outcome v cb).2) ∧
    (r + 1 = s.r → s.est = (outcome v cb).2)
  dec : m .dec ≠ none → s.pc = .done ∧ m .dec = some s.dv
  decC : (s.pc = .writeDec ∨ m .dec ≠ none) →
    ∃ r < s.r, ∃ v cb, m (.e r) = some (v, cb) ∧ outcome v cb = (true, s.dv)
  inp : m .inR = if p = 2 ∨ s.pc = .start then none else some (x p)
  r0 : (s.pc = .start ∨ ∃ b, s.pc = .getIn b) → s.r = 0
  est0 : s.pc = .start → s.est = x p

/-- A valid decision value for the input vector `x`. -/
def VV (x : Fin 3 → Bool) (u : Bool) : Prop := u = x 0 ∨ u = x 1

/-- Some process committed `u` in some round. -/
def Committed (C : Cfg) (u : Bool) : Prop :=
  ∃ q r v cb, C.mem q (.e r) = some (v, cb) ∧ outcome v cb = (true, u)

/-- The global invariant. -/
structure Inv (x : Fin 3 → Bool) (C : Cfg) : Prop where
  loc : ∀ p, Loc x p (C.loc p) (C.mem p)
  ra : ∀ p r j u, rdA (C.loc p) (C.mem p) r j = some (some u) → C.mem j (.a r) = some u
  xa : ∀ p q r res, rdA (C.loc p) (C.mem p) r q = some none →
    rdA (C.loc q) (C.mem q) r p = some res → res ≠ none
  rb : ∀ p r j u, rdB (C.loc p) (C.mem p) r j = some (some u) → C.mem j (.b r) = some u
  xb : ∀ p q r res, rdB (C.loc p) (C.mem p) r q = some none →
    rdB (C.loc q) (C.mem q) r p = some res → res ≠ none
  vest : ∀ p, (p ≠ 2 ∨ ((C.loc p).pc ≠ .start ∧ ∀ b, (C.loc p).pc ≠ .getIn b)) →
    VV x (C.loc p).est
  va : ∀ p r u, C.mem p (.a r) = some u → VV x u
  done : ∀ p, (C.loc p).pc = .done → Committed C (C.loc p).dv
  out : ∀ p u, C.out p = some u → p = 2 ∨ Committed C u

/-! ### Consequences of the local invariant -/

section LocLemmas

variable {x : Fin 3 → Bool} {p : Fin 3} {s : St} {m : Mem}

theorem Loc.a_of_rdA (h : Loc x p s m) {r : ℕ} {j : Fin 3} (hr : rdA s m r j ≠ none) :
    ∃ v, m (.a r) = some v := by
  unfold rdA at hr
  split_ifs at hr with h1 h2
  · obtain ⟨v, -, -, ha, -⟩ := h.past r h1; exact ⟨v, ha⟩
  · subst h2; rw [h.curA]
    split at hr <;> simp_all [ph]
  · exact absurd rfl hr

theorem Loc.b_of_rdB (h : Loc x p s m) {r : ℕ} {j : Fin 3} (hr : rdB s m r j ≠ none) :
    ∃ bv, m (.b r) = some bv := by
  unfold rdB at hr
  split_ifs at hr with h1 h2
  · obtain ⟨v, ca, -, -, hb, -⟩ := h.past r h1; exact ⟨_, hb⟩
  · subst h2; rw [h.curB]
    split at hr <;> simp_all [ph]
  · exact absurd rfl hr

theorem Loc.of_b (h : Loc x p s m) {r : ℕ} {v : Bool} {ca : Fin 3 → Option Bool}
    (hb : m (.b r) = some (v, ca)) : (∀ j, rdA s m r j = some (ca j)) ∧ m (.a r) = some v := by
  rcases lt_trichotomy r s.r with h1 | rfl | h1
  · obtain ⟨v', ca', cb', ha, hb', -⟩ := h.past r h1
    rw [hb] at hb'; cases hb'
    exact ⟨fun j => by simp [rdA, h1, hb], ha⟩
  · rw [h.curB] at hb
    split_ifs at hb with hph; cases hb
    refine ⟨fun j => ?_, by rw [h.curA]; simp [hph]⟩
    simp only [rdA, lt_irrefl, ite_false, ite_true]
    revert hph; cases s.pc <;> simp [ph]
  · simp [(h.future r h1).2.1] at hb

theorem Loc.of_e (h : Loc x p s m) {r : ℕ} {v : Bool} {cb : Fin 3 → Option BV}
    (he : m (.e r) = some (v, cb)) :
    r < s.r ∧ (∀ j, rdB s m r j = some (cb j)) ∧ m (.a r) = some v := by
  rcases lt_trichotomy r s.r with h1 | rfl | h1
  · obtain ⟨v', ca', cb', ha, -, he', -⟩ := h.past r h1
    rw [he] at he'; cases he'
    exact ⟨h1, fun j => by simp [rdB, h1, he], ha⟩
  · simp [h.curE] at he
  · simp [(h.future r h1).2.2] at he

/-- The chain of estimates: the `A` value of round `r + 1` is the outcome of round `r`. -/
theorem Loc.chain (h : Loc x p s m) {r : ℕ} {u : Bool} (ha : m (.a (r + 1)) = some u) :
    ∃ v cb, m (.e r) = some (v, cb) ∧ u = (outcome v cb).2 := by
  rcases lt_trichotomy (r + 1) s.r with h1 | h1 | h1
  · obtain ⟨v, ca, cb, -, -, he, hc, -⟩ := h.past r (by omega)
    rw [hc h1] at ha; cases ha; exact ⟨v, cb, he, rfl⟩
  · obtain ⟨v, ca, cb, -, -, he, -, hc⟩ := h.past r (by omega)
    have := h.curA; rw [← h1, ha] at this
    split_ifs at this; cases this
    exact ⟨v, cb, he, hc h1⟩
  · simp [(h.future _ h1).1] at ha

end LocLemmas

/-! ### Commit-adopt properties -/

theorem firstC_spec {cb : Fin 3 → Option BV} {u : Bool} (h : firstC cb = some u) :
    ∃ j, cVal (cb j) = some u := by
  unfold firstC at h
  rcases h0 : cVal (cb 0) with _ | a
  · rcases h1 : cVal (cb 1) with _ | b
    · rw [h0, h1] at h; exact ⟨2, by simpa using h⟩
    · rw [h0, h1] at h; exact ⟨1, by simpa [h1] using h⟩
  · rw [h0] at h; exact ⟨0, by simpa [h0] using h⟩

theorem firstC_ne_none {cb : Fin 3 → Option BV} {j : Fin 3} (h : cVal (cb j) ≠ none) :
    firstC cb ≠ none := by
  intro hf
  unfold firstC at hf
  simp only [Option.or_eq_none_iff] at hf
  fin_cases j <;> simp_all

/-- The decided value of commit-adopt is the estimate or the value of a commit pair read. -/
theorem outcome_val (est : Bool) (cb : Fin 3 → Option BV) :
    (outcome est cb).2 = est ∨ ∃ j, cVal (cb j) = some (outcome est cb).2 := by
  unfold outcome
  split_ifs
  · exact Or.inl rfl
  · rcases h : firstC cb with _ | u
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using firstC_spec h)

theorem cVal_some {b : Option BV} {u : Bool} (h : cVal b = some u) :
    ∃ ca, b = some (u, ca) ∧ Flag u ca := by
  rcases b with _ | ⟨w, ca⟩
  · simp [cVal] at h
  · simp only [cVal] at h; split_ifs at h with hf; cases h; exact ⟨ca, rfl, hf⟩

section CA

variable {x : Fin 3 → Bool} {C : Cfg} (I : Inv x C)
include I

/-- Two commit pairs written in the same round carry the same value. -/
theorem commit_pairs {p q : Fin 3} {r : ℕ} {v w : Bool} {ca ca' : Fin 3 → Option Bool}
    (hp : C.mem p (.b r) = some (v, ca)) (hfp : Flag v ca)
    (hq : C.mem q (.b r) = some (w, ca')) (hfq : Flag w ca') : v = w := by
  obtain ⟨hrp, hap⟩ := (I.loc p).of_b hp
  obtain ⟨hrq, haq⟩ := (I.loc q).of_b hq
  rcases hc : ca q with _ | u
  · have hne := I.xa p q r (ca' p) (by rw [hrp, hc]) (hrq p)
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hne
    have := I.ra q r p u (by rw [hrq, hu])
    rw [hap] at this; cases this
    rcases hfq p with h | h <;> rw [hu] at h <;> simp_all
  · have := I.ra p r q u (by rw [hrp, hc])
    rw [haq] at this; cases this
    rcases hfp q with h | h <;> rw [hc] at h <;> simp_all

/-- A commit pair read in the second collect of round `r` is a commit pair written in round
`r`. -/
theorem cVal_read {p : Fin 3} {r : ℕ} {v : Bool} {cb : Fin 3 → Option BV}
    (he : C.mem p (.e r) = some (v, cb)) {j : Fin 3} {u : Bool} (hu : cVal (cb j) = some u) :
    ∃ ca, C.mem j (.b r) = some (u, ca) ∧ Flag u ca := by
  obtain ⟨ca, hcb, hf⟩ := cVal_some hu
  obtain ⟨-, hrd, -⟩ := (I.loc p).of_e he
  exact ⟨ca, I.rb p r j _ (by rw [hrd, hcb]), hf⟩

/-- The own entry of the second collect is the own `B` value. -/
theorem own_read {p : Fin 3} {r : ℕ} {v : Bool} {cb : Fin 3 → Option BV}
    (he : C.mem p (.e r) = some (v, cb)) : ∃ ca, cb p = some (v, ca) ∧
      C.mem p (.b r) = some (v, ca) := by
  obtain ⟨-, hrd, ha⟩ := (I.loc p).of_e he
  rcases hc : cb p with _ | ⟨w, ca⟩
  · exact absurd rfl (I.xb p p r none (by rw [hrd, hc]) (by rw [hrd, hc]))
  · have hb := I.rb p r p _ (by rw [hrd, hc])
    have := ((I.loc p).of_b hb).2
    rw [ha] at this; cases this
    exact ⟨ca, rfl, hb⟩

/-- **Commit-adopt agreement.** If some process commits `c` in round `r`, every process
completing round `r` leaves it with value `c`. -/
theorem ca_agree {p q : Fin 3} {r : ℕ} {vp vq c : Bool} {cbp cbq : Fin 3 → Option BV}
    (hp : C.mem p (.e r) = some (vp, cbp)) (hc : outcome vp cbp = (true, c))
    (hq : C.mem q (.e r) = some (vq, cbq)) : (outcome vq cbq).2 = c := by
  have hall : AllC cbp ∧ vp = c := by
    unfold outcome at hc; split_ifs at hc with h
    · cases hc; exact ⟨h, rfl⟩
    · simp at hc
  obtain ⟨hall, rfl⟩ := hall
  -- every commit pair of round `r` has value `vp`
  obtain ⟨cap, hcbp, hbp⟩ := own_read I hp
  have hfp : Flag vp cap := by
    rcases hall p with h | h
    · simp [hcbp] at h
    · rw [hcbp] at h; simp only [cVal] at h; split_ifs at h with hf
      · exact hf
      · simp at h
  have hcp : ∀ j u, cVal (cbq j) = some u → u = vp := fun j u hu => by
    obtain ⟨ca, hb, hf⟩ := cVal_read I hq hu
    exact commit_pairs I hb hf hbp hfp
  obtain ⟨caq, hcbq, hbq⟩ := own_read I hq
  -- `q` read a commit pair
  have hex : ∃ j, cVal (cbq j) ≠ none := by
    obtain ⟨-, hrdp, -⟩ := (I.loc p).of_e hp
    obtain ⟨-, hrdq, -⟩ := (I.loc q).of_e hq
    rcases h1 : cbp q with _ | bv
    · have hne := I.xb p q r (cbq p) (by rw [hrdp, h1]) (hrdq p)
      obtain ⟨bv, hbv⟩ := Option.ne_none_iff_exists'.1 hne
      have hb := I.rb q r p bv (by rw [hrdq, hbv])
      rw [hbp] at hb; cases hb
      exact ⟨p, by rw [hbv]; simp [cVal, hfp]⟩
    · have hb := I.rb p r q bv (by rw [hrdp, h1])
      rw [hbq] at hb; cases hb
      rcases hall q with h | h
      · simp [h1] at h
      · refine ⟨q, ?_⟩
        rw [h1] at h; rw [hcbq]; exact h
  unfold outcome
  split_ifs with hq'
  · obtain ⟨j, hj⟩ := hex
    rcases hq' q with h | h
    · simp [hcbq] at h
    · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 h
      have := hcp q u hu
      rw [hcbq] at hu; simp only [cVal] at hu; split_ifs at hu; cases hu; exact this
  · obtain ⟨j, hj⟩ := hex
    rcases hf : firstC cbq with _ | u
    · exact absurd hf (firstC_ne_none hj)
    · obtain ⟨j', hj'⟩ := firstC_spec hf
      exact hcp j' u hj'

/-- **Commit-adopt validity.** If all `A` values of round `r` are `c`, every process completing
round `r` leaves it with value `c`. -/
theorem ca_valid {r : ℕ} {c : Bool} (hA : ∀ q u, C.mem q (.a r) = some u → u = c) {p : Fin 3}
    {v : Bool} {cb : Fin 3 → Option BV} (hp : C.mem p (.e r) = some (v, cb)) :
    (outcome v cb).2 = c := by
  rcases outcome_val v cb with h | ⟨j, hj⟩
  · rw [h]; exact hA p v ((I.loc p).of_e hp).2.2
  · obtain ⟨ca, hb, -⟩ := cVal_read I hp hj
    exact hA j _ ((I.loc j).of_b hb).2

/-- After a commit of `c` in round `r`, all later `A` values are `c`. -/
theorem lock {p : Fin 3} {r : ℕ} {v c : Bool} {cb : Fin 3 → Option BV}
    (hp : C.mem p (.e r) = some (v, cb)) (hc : outcome v cb = (true, c)) :
    ∀ n q u, C.mem q (.a (r + 1 + n)) = some u → u = c := by
  intro n
  induction n with
  | zero =>
    intro q u hu
    obtain ⟨v', cb', he, rfl⟩ := (I.loc q).chain hu
    exact ca_agree I hp hc he
  | succ n ih =>
    intro q u hu
    obtain ⟨v', cb', he, rfl⟩ := (I.loc q).chain (r := r + 1 + n) hu
    exact ca_valid I ih he

/-- **Agreement**: all committed values are equal. -/
theorem committed_eq {u u' : Bool} (h : Committed C u) (h' : Committed C u') : u = u' := by
  obtain ⟨p, r, v, cb, hp, hc⟩ := h
  obtain ⟨q, r', v', cb', hq, hc'⟩ := h'
  have key : ∀ {p q r r' v v' cb cb' u u'}, C.mem p (.e r) = some (v, cb) →
      outcome v cb = (true, u) → C.mem q (.e r') = some (v', cb') →
      outcome v' cb' = (true, u') → r ≤ r' → u = u' := by
    intro p q r r' v v' cb cb' u u' hp hc hq hc' hrr
    have h2 : (outcome v' cb').2 = u' := by rw [hc']
    rcases Nat.eq_or_lt_of_le hrr with rfl | hlt
    · rw [← h2]; exact (ca_agree I hp hc hq).symm
    · obtain ⟨n, rfl⟩ : ∃ n, r' = r + 1 + n := ⟨r' - r - 1, by omega⟩
      rw [← h2]; exact (ca_valid I (lock I hp hc n) hq).symm
  rcases le_total r r' with hrr | hrr
  · exact key hp hc hq hc' hrr
  · exact (key hq hc' hp hc hrr).symm

/-- Committed values are inputs of `p₁` or `p₂`. -/
theorem committed_valid {u : Bool} (h : Committed C u) : VV x u := by
  obtain ⟨p, r, v, cb, hp, hc⟩ := h
  have h2 : (outcome v cb).2 = u := by rw [hc]
  rcases outcome_val v cb with h | ⟨j, hj⟩
  · rw [← h2, h]; exact I.va p r v ((I.loc p).of_e hp).2.2
  · obtain ⟨ca, hb, -⟩ := cVal_read I hp hj
    rw [← h2]; exact I.va j r _ ((I.loc j).of_b hb).2

end CA

/-! ### Preservation of the invariant -/

/-- The configuration `C` where process `z` gets state `s'`, registers `m'` and decision `o'`. -/
def upd (C : Cfg) (z : Fin 3) (s' : St) (m' : Mem) (o' : Option Bool) : Cfg :=
  ⟨Function.update C.loc z s', Function.update C.mem z m', Function.update C.out z o'⟩

/-- Sufficient conditions on the new state/registers/decision of the stepping process `z` for
the invariant to be preserved. -/
theorem inv_upd {x : Fin 3 → Bool} {C : Cfg} (I : Inv x C) {z : Fin 3} {s' : St} {m' : Mem}
    {o' : Option Bool}
    (hL : Loc x z s' m')
    (hA : ∀ r, m' (.a r) = C.mem z (.a r) ∨ C.mem z (.a r) = none)
    (hB : ∀ r, m' (.b r) = C.mem z (.b r) ∨ C.mem z (.b r) = none)
    (hE : ∀ r, m' (.e r) = C.mem z (.e r) ∨ C.mem z (.e r) = none)
    (hrdA : ∀ r j, rdA s' m' r j = rdA (C.loc z) (C.mem z) r j ∨
      (m' = C.mem z ∧ rdA s' m' r j = some (C.mem j (.a r))))
    (hrdB : ∀ r j, rdB s' m' r j = rdB (C.loc z) (C.mem z) r j ∨
      (m' = C.mem z ∧ rdB s' m' r j = some (C.mem j (.b r))))
    (hvest : (z ≠ 2 ∨ (s'.pc ≠ .start ∧ ∀ b, s'.pc ≠ .getIn b)) → VV x s'.est)
    (hva : ∀ r u, m' (.a r) = some u → VV x u)
    (hdone : s'.pc = .done → Committed C s'.dv)
    (hout : ∀ u, o' = some u → z = 2 ∨ Committed C u) :
    Inv x (upd C z s' m' o') := by
  set C' := upd C z s' m' o' with hC'
  have hloc : ∀ p, C'.loc p = if p = z then s' else C.loc p := fun p => by
    by_cases h : p = z
    · subst h; simp [C', upd]
    · simp [C', upd, h]
  have hmem : ∀ p, C'.mem p = if p = z then m' else C.mem p := fun p => by
    by_cases h : p = z
    · subst h; simp [C', upd]
    · simp [C', upd, h]
  have hmonoA : ∀ j r u, C.mem j (.a r) = some u → C'.mem j (.a r) = some u := by
    intro j r u h
    rw [hmem]; split_ifs with hj
    · subst hj; rcases hA r with h' | h' <;> simp_all
    · exact h
  have hmonoB : ∀ j r u, C.mem j (.b r) = some u → C'.mem j (.b r) = some u := by
    intro j r u h
    rw [hmem]; split_ifs with hj
    · subst hj; rcases hB r with h' | h' <;> simp_all
    · exact h
  have hcomm : ∀ u, Committed C u → Committed C' u := by
    rintro u ⟨q, r, v, cb, he, hc⟩
    refine ⟨q, r, v, cb, ?_, hc⟩
    rw [hmem]; split_ifs with hq
    · subst hq; rcases hE r with h' | h' <;> simp_all
    · exact he
  -- read results of the other processes are unchanged
  have hrA : ∀ p, p ≠ z → rdA (C'.loc p) (C'.mem p) = rdA (C.loc p) (C.mem p) := fun p hp => by
    rw [hloc, hmem]; simp [hp]
  have hrB : ∀ p, p ≠ z → rdB (C'.loc p) (C'.mem p) = rdB (C.loc p) (C.mem p) := fun p hp => by
    rw [hloc, hmem]; simp [hp]
  have hzA : rdA (C'.loc z) (C'.mem z) = rdA s' m' := by rw [hloc, hmem]; simp
  have hzB : rdB (C'.loc z) (C'.mem z) = rdB s' m' := by rw [hloc, hmem]; simp
  refine ⟨fun p => ?_, ?_, ?_, ?_, ?_, fun p => ?_, fun p r u => ?_, fun p => ?_, fun p u => ?_⟩
  · rw [hloc, hmem]; split_ifs with hp
    · subst hp; exact hL
    · exact I.loc p
  · intro p r j u h
    by_cases hp : p = z
    · subst hp; rw [hzA] at h
      rcases hrdA r j with h' | ⟨-, h'⟩
      · exact hmonoA _ _ _ (I.ra p r j u (h' ▸ h))
      · rw [h'] at h; exact hmonoA _ _ _ (Option.some_injective _ h)
    · rw [hrA p hp] at h; exact hmonoA _ _ _ (I.ra p r j u h)
  · intro p q r res hpq hqp
    by_cases hp : p = z <;> by_cases hq : q = z
    · subst hp; subst hq; rw [hzA] at hpq hqp
      rw [hpq] at hqp; cases hqp
      rcases hrdA r q with h' | ⟨hm, h'⟩
      · exact I.xa q q r none (h' ▸ hpq) (h' ▸ hpq)
      · intro _
        rw [h'] at hpq
        obtain ⟨v, hv⟩ := hL.a_of_rdA (j := q) (r := r) (by rw [h']; simp)
        rw [hm] at hv; simp_all
    · subst hp; rw [hzA] at hpq; rw [hrA q hq] at hqp
      rcases hrdA r q with h' | ⟨-, h'⟩
      · exact I.xa p q r res (h' ▸ hpq) hqp
      · rw [h'] at hpq
        obtain ⟨v, hv⟩ := (I.loc q).a_of_rdA (j := p) (r := r) (by rw [hqp]; simp)
        simp_all
    · subst hq; rw [hrA p hp] at hpq; rw [hzA] at hqp
      rcases hrdA r p with h' | ⟨-, h'⟩
      · exact I.xa p q r res hpq (h' ▸ hqp)
      · rw [h'] at hqp; cases hqp
        obtain ⟨v, hv⟩ := (I.loc p).a_of_rdA (j := q) (r := r) (by rw [hpq]; simp)
        simp_all
    · rw [hrA p hp] at hpq; rw [hrA q hq] at hqp; exact I.xa p q r res hpq hqp
  · intro p r j u h
    by_cases hp : p = z
    · subst hp; rw [hzB] at h
      rcases hrdB r j with h' | ⟨-, h'⟩
      · exact hmonoB _ _ _ (I.rb p r j u (h' ▸ h))
      · rw [h'] at h; exact hmonoB _ _ _ (Option.some_injective _ h)
    · rw [hrB p hp] at h; exact hmonoB _ _ _ (I.rb p r j u h)
  · intro p q r res hpq hqp
    by_cases hp : p = z <;> by_cases hq : q = z
    · subst hp; subst hq; rw [hzB] at hpq hqp
      rw [hpq] at hqp; cases hqp
      rcases hrdB r q with h' | ⟨hm, h'⟩
      · exact I.xb q q r none (h' ▸ hpq) (h' ▸ hpq)
      · intro _
        rw [h'] at hpq
        obtain ⟨v, hv⟩ := hL.b_of_rdB (j := q) (r := r) (by rw [h']; simp)
        rw [hm] at hv; simp_all
    · subst hp; rw [hzB] at hpq; rw [hrB q hq] at hqp
      rcases hrdB r q with h' | ⟨-, h'⟩
      · exact I.xb p q r res (h' ▸ hpq) hqp
      · rw [h'] at hpq
        obtain ⟨v, hv⟩ := (I.loc q).b_of_rdB (j := p) (r := r) (by rw [hqp]; simp)
        simp_all
    · subst hq; rw [hrB p hp] at hpq; rw [hzB] at hqp
      rcases hrdB r p with h' | ⟨-, h'⟩
      · exact I.xb p q r res hpq (h' ▸ hqp)
      · rw [h'] at hqp; cases hqp
        obtain ⟨v, hv⟩ := (I.loc p).b_of_rdB (j := q) (r := r) (by rw [hpq]; simp)
        simp_all
    · rw [hrB p hp] at hpq; rw [hrB q hq] at hqp; exact I.xb p q r res hpq hqp
  · rw [hloc]; split_ifs with hp
    · subst hp; exact hvest
    · exact I.vest p
  · rw [hmem]; split_ifs with hp
    · exact hva r u
    · exact I.va p r u
  · rw [hloc]; split_ifs with hp
    · intro h; exact hcomm _ (hdone h)
    · intro h; exact hcomm _ (I.done p h)
  · simp only [C', upd]
    by_cases hp : p = z
    · subst hp; rw [Function.update_self]; intro h
      rcases hout u h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (hcomm _ h')
    · rw [Function.update_of_ne hp]; intro h
      rcases I.out p u h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (hcomm _ h')

/-- The local invariant is preserved by steps that keep the round, the estimate and the phase,
and do not touch the round registers. -/
theorem Loc.same {x : Fin 3 → Bool} {z : Fin 3} {s s' : St} {m m' : Mem} (h : Loc x z s m)
    (hr : s'.r = s.r) (hest : s'.est = s.est ∨ (ph s.pc = 0 ∧ s.r = 0))
    (hph : ph s'.pc = ph s.pc)
    (hca : ph s.pc = 2 → s'.ca = s.ca)
    (hm : ∀ r, m' (.a r) = m (.a r) ∧ m' (.b r) = m (.b r) ∧ m' (.e r) = m (.e r))
    (hdec : m' .dec ≠ none → s'.pc = .done ∧ m' .dec = some s'.dv)
    (hdecC : (s'.pc = .writeDec ∨ m' .dec ≠ none) →
      ∃ r < s'.r, ∃ v cb, m' (.e r) = some (v, cb) ∧ outcome v cb = (true, s'.dv))
    (hinp : m' .inR = if z = 2 ∨ s'.pc = .start then none else some (x z))
    (hr0 : (s'.pc = .start ∨ ∃ b, s'.pc = .getIn b) → s'.r = 0)
    (hest0 : s'.pc = .start → s'.est = x z) : Loc x z s' m' := by
  refine ⟨fun r hr' => ?_, ?_, ?_, ?_, fun r hr' => ?_, hdec, hdecC, hinp, hr0, hest0⟩
  · rw [(hm r).1, (hm r).2.1, (hm r).2.2]; exact h.future r (hr ▸ hr')
  · rw [(hm _).1, hr, h.curA, hph]
    rcases hest with hest | ⟨h0, -⟩
    · rw [hest]
    · simp [h0]
  · rw [(hm _).2.1, hr, h.curB, hph]
    split_ifs with h2
    · rcases hest with hest | ⟨h0, -⟩
      · rw [hca h2, hest]
      · omega
    · rfl
  · rw [(hm _).2.2, hr, h.curE]
  · rw [hr] at hr' ⊢
    obtain ⟨v, ca, cb, ha, hb, he, h1, h2⟩ := h.past r hr'
    refine ⟨v, ca, cb, by rw [(hm r).1, ha], by rw [(hm r).2.1, hb], by rw [(hm r).2.2, he],
      fun h' => by rw [(hm _).1, h1 h'], fun h' => ?_⟩
    rcases hest with hest | ⟨-, h0⟩
    · rw [hest, h2 h']
    · omega

section Steps

variable {x : Fin 3 → Bool} {C : Cfg} (I : Inv x C) {z : Fin 3} (ℓ : Fin 3)
include I

omit I in
theorem step_upd : alg.step z ℓ C = upd C z ((nxt z (C.loc z)).post C.mem ℓ)
    ((nxt z (C.loc z)).memUpd (C.mem z)) ((nxt z (C.loc z)).outUpd (C.out z)) :=
  alg.step_eq z ℓ C

omit I in
theorem rdA_ph0 {s s' : St} {m m' : Mem} (hr : s'.r = s.r) (h0 : ph s.pc = 0) (h0' : ph s'.pc = 0)
    (hb : ∀ r, m' (.b r) = m (.b r)) (r : ℕ) (j : Fin 3) : rdA s' m' r j = rdA s m r j := by
  unfold rdA; rw [hr, hb]
  split_ifs <;> try rfl
  revert h0 h0'; cases s.pc <;> cases s'.pc <;> simp [ph]

omit I in
theorem rdB_ph0 {s s' : St} {m m' : Mem} (hr : s'.r = s.r) (h0 : ph s.pc ≠ 2)
    (h0' : ph s'.pc ≠ 2) (he : ∀ r, m' (.e r) = m (.e r)) (r : ℕ) (j : Fin 3) :
    rdB s' m' r j = rdB s m r j := by
  unfold rdB; rw [hr, he]
  split_ifs <;> try rfl
  revert h0 h0'; cases s.pc <;> cases s'.pc <;> simp [ph]

theorem inv_step_start (hpc : (C.loc z).pc = .start) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  by_cases hz : z = 2
  · have hn : nxt z (C.loc z) = .decide false { C.loc z with pc := .getIn false } := by
      unfold nxt; rw [hpc]; simp [hz]
    rw [hn]; simp only [Act.post, Act.memUpd, Act.outUpd]
    apply inv_upd I
    · exact hL.same rfl (Or.inl rfl) (by simp [ph, hpc]) (by simp [ph, hpc])
        (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h) (by simp [hdec])
        (by rw [hL.inp]; simp [hz]) (fun _ => hL.r0 (Or.inl hpc)) (by simp)
    all_goals try (intro r; left; rfl)
    · intro r j; left; apply rdA_ph0 <;> first | rfl | simp [ph, hpc]
    · intro r j; left; apply rdB_ph0 <;> first | rfl | simp [ph, hpc]
    · simp [hz]
    · exact I.va z
    · simp
    · intro _ _; exact Or.inl hz
  · have hn : nxt z (C.loc z) =
        .write .inR (some (C.loc z).est) { C.loc z with pc := .readDec 0 } := by
      unfold nxt; rw [hpc]; simp [hz]
    rw [hn]; simp only [Act.post, Act.memUpd, Act.outUpd]
    have hest := hL.est0 hpc
    apply inv_upd I
    · exact hL.same rfl (Or.inl rfl) (by simp [ph, hpc]) (by simp [ph, hpc])
        (fun r => by simp) (by simp [hdec]) (by simp [hdec])
        (by simp [hz, hest]) (by simp) (by simp)
    all_goals try (intro r; left; simp; done)
    · intro r j; left; apply rdA_ph0 <;> first | rfl | simp [ph, hpc]
    · intro r j; left; apply rdB_ph0 <;> first | rfl | simp [ph, hpc]
    · intro _; simp only [hest]; unfold VV; fin_cases z <;> simp_all
    · intro r u h; exact I.va z r u (by simpa using h)
    · simp
    · exact I.out z

theorem inv_step_getIn {b : Bool} (hpc : (C.loc z).pc = .getIn b) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  have hr0 := hL.r0 (Or.inr ⟨b, hpc⟩)
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  rcases hv : C.mem (if b then 1 else 0) Reg.inR with _ | u
  · apply inv_upd I
    · exact hL.same rfl (Or.inl rfl) (by simp [ph, hpc]) (by simp [ph, hpc])
        (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h) (by simp [hdec])
        (by rw [hL.inp]; simp [hpc]) (fun _ => hr0) (by simp)
    all_goals try (intro r; left; rfl)
    · intro r j; left; apply rdA_ph0 <;> first | rfl | simp [ph, hpc]
    · intro r j; left; apply rdB_ph0 <;> first | rfl | simp [ph, hpc]
    · intro h; apply I.vest; left; simpa using h
    · exact I.va z
    · simp
    · exact I.out z
  · have hj := (I.loc (if b then 1 else 0)).inp
    rw [hv] at hj
    have hu : VV x u := by
      unfold VV; cases b <;> simp at hj <;> simp [hj.2]
    apply inv_upd I
    · exact hL.same rfl (Or.inr ⟨by simp [ph, hpc], hr0⟩) (by simp [ph, hpc]) (by simp [ph, hpc])
        (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h) (by simp [hdec])
        (by rw [hL.inp]; simp [hpc]) (by simp) (by simp)
    all_goals try (intro r; left; rfl)
    · intro r j; left; apply rdA_ph0 <;> first | rfl | simp [ph, hpc]
    · intro r j; left; apply rdB_ph0 <;> first | rfl | simp [ph, hpc]
    · intro _; exact hu
    · exact I.va z
    · simp
    · exact I.out z

theorem inv_step_readDec {j : Fin 3} (hpc : (C.loc z).pc = .readDec j) :
    Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  rcases hv : C.mem j Reg.dec with _ | u
  · apply inv_upd I
    · exact hL.same rfl (Or.inl rfl) (by split_ifs <;> simp [ph, hpc])
        (by simp [ph, hpc]) (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h)
        (by split_ifs <;> simp [hdec])
        (by rw [hL.inp]; split_ifs <;> simp_all) (by split_ifs <;> simp) (by split_ifs <;> simp)
    all_goals try (intro r; left; rfl)
    · intro r j; left; apply rdA_ph0 <;> first | rfl | (simp [ph, hpc]; done) | (split_ifs <;> simp [ph])
    · intro r j; left; apply rdB_ph0 <;> first | rfl | (simp [ph, hpc]; done) | (split_ifs <;> simp [ph])
    · intro _; exact I.vest z hvest
    · exact I.va z
    · split_ifs <;> simp
    · exact I.out z
  · have hj := (I.loc j).dec (by rw [hv]; simp)
    obtain ⟨r, -, v, cb, he, hc⟩ := (I.loc j).decC (Or.inr (by rw [hv]; simp))
    rw [hv, hj.2] at *
    apply inv_upd I
    · exact hL.same rfl (Or.inl rfl) (by simp [ph, hpc])
        (by simp [ph, hpc]) (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h)
        (by simp [hdec]) (by rw [hL.inp]; simp_all) (by simp) (by simp)
    all_goals try (intro r; left; rfl)
    · intro r j; left; apply rdA_ph0 <;> first | rfl | simp [ph, hpc]
    · intro r j; left; apply rdB_ph0 <;> first | rfl | simp [ph, hpc]
    · intro _; exact I.vest z hvest
    · exact I.va z
    · intro _; exact ⟨j, r, v, cb, he, hc⟩
    · exact I.out z

theorem inv_step_query (hpc : (C.loc z).pc = .query) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  apply inv_upd I
  · exact hL.same rfl (Or.inl rfl) (by split_ifs <;> simp [ph, hpc])
      (by simp [ph, hpc]) (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h)
      (by split_ifs <;> simp [hdec])
      (by rw [hL.inp]; split_ifs <;> simp_all) (by split_ifs <;> simp) (by split_ifs <;> simp)
  all_goals try (intro r; left; rfl)
  · intro r j; left; apply rdA_ph0 <;> first | rfl | (simp [ph, hpc]; done) | (split_ifs <;> simp [ph])
  · intro r j; left; apply rdB_ph0 <;> first | rfl | (simp [ph, hpc]; done) | (split_ifs <;> simp [ph])
  · intro _; exact I.vest z hvest
  · exact I.va z
  · split_ifs <;> simp
  · exact I.out z

theorem inv_step_writeDec (hpc : (C.loc z).pc = .writeDec) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  obtain ⟨r, hr, v, cb, he, hc⟩ := hL.decC (Or.inl hpc)
  apply inv_upd I
  · exact hL.same rfl (Or.inl rfl) (by simp [ph, hpc])
      (by simp [ph, hpc]) (fun r => by simp) (by simp)
      (fun _ => ⟨r, hr, v, cb, by simpa using he, hc⟩)
      (by rw [Function.update_of_ne (by simp), hL.inp]; simp [hpc]) (by simp) (by simp)
  all_goals try (intro r; left; simp; done)
  · intro r j; left; apply rdA_ph0 <;> first | rfl | simp [ph, hpc]
  · intro r j; left; apply rdB_ph0 <;> first | rfl | simp [ph, hpc]
  · intro _; exact I.vest z hvest
  · intro r u h; exact I.va z r u (by simpa using h)
  · intro _; exact ⟨z, r, v, cb, he, hc⟩
  · exact I.out z

theorem inv_step_done (hpc : (C.loc z).pc = .done) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  apply inv_upd I hL
  all_goals try (intro r; left; rfl)
  · intro r j; left; rfl
  · intro r j; left; rfl
  · exact I.vest z
  · exact I.va z
  · exact I.done z
  · intro u h
    rcases ho : C.out z with _ | w
    · rw [ho] at h; simp at h; subst h; exact Or.inr (I.done z hpc)
    · rw [ho] at h; simp at h; subst h; exact I.out z w ho

theorem inv_step_writeA (hpc : (C.loc z).pc = .writeA) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  have hA0 : C.mem z (.a (C.loc z).r) = none := by rw [hL.curA]; simp [ph, hpc]
  have hB0 : C.mem z (.b (C.loc z).r) = none := by rw [hL.curB]; simp [ph, hpc]
  apply inv_upd I
  · refine ⟨fun r hr => ?_, by simp [ph], by simpa [ph] using hB0, by simpa using hL.curE,
      fun r hr => ?_, by simp [hdec], by simp [hdec], ?_, by simp, by simp⟩
    · dsimp only at hr
      have := hL.future r hr
      rw [Function.update_of_ne (by simp; omega)]; simpa using this
    · dsimp only at hr ⊢
      obtain ⟨v, ca, cb, ha, hb, he, h1, h2⟩ := hL.past r hr
      refine ⟨v, ca, cb, by rw [Function.update_of_ne (by simp; omega), ha], by simpa using hb,
        by simpa using he, fun h => ?_, h2⟩
      rw [Function.update_of_ne (by simp; omega), h1 h]
    · rw [Function.update_of_ne (by simp), hL.inp]; simp [hpc]
  · intro r
    by_cases hr : r = (C.loc z).r
    · subst hr; right; exact hA0
    · left; rw [Function.update_of_ne (by simpa using hr)]
  · intro r; left; simp
  · intro r; left; simp
  · intro r j; left; unfold rdA; simp [hpc]
  · intro r j; left; unfold rdB; simp [hpc]
  · intro _; exact I.vest z hvest
  · intro r u h
    by_cases hr : r = (C.loc z).r
    · subst hr; simp at h; rw [← h]; exact I.vest z hvest
    · rw [Function.update_of_ne (by simpa using hr)] at h; exact I.va z r u h
  · simp
  · exact I.out z

/-- State after the read of `A_i` (value `v`). -/
def afterReadA (s : St) (i : Fin 3) (v : Option Bool) : St :=
  { s with ca := Function.update s.ca i v, pc := if i = 2 then .writeB else .readA (i + 1) }

/-- State after the read of `B_i` (value `v`). -/
def afterReadB (s : St) (i : Fin 3) (v : Option BV) : St :=
  { s with cb := Function.update s.cb i v, pc := if i = 2 then .writeE else .readB (i + 1) }

omit I in
theorem rdA_readA {s : St} {m : Mem} {i : Fin 3} (hpc : s.pc = .readA i) (v : Option Bool)
    (r : ℕ) (j : Fin 3) :
    rdA (afterReadA s i v) m r j = rdA s m r j ∨
    (r = s.r ∧ j = i ∧ rdA (afterReadA s i v) m r j = some v) := by
  unfold rdA afterReadA
  by_cases h1 : r < s.r
  · left; simp [h1]
  by_cases h2 : r = s.r
  · subst h2; simp only [lt_irrefl, ite_false, ite_true, hpc]
    fin_cases i <;> fin_cases j <;> simp [Function.update]
  · left; simp [h1, h2]

omit I in
theorem rdB_readB {s : St} {m : Mem} {i : Fin 3} (hpc : s.pc = .readB i) (v : Option BV)
    (r : ℕ) (j : Fin 3) :
    rdB (afterReadB s i v) m r j = rdB s m r j ∨
    (r = s.r ∧ j = i ∧ rdB (afterReadB s i v) m r j = some v) := by
  unfold rdB afterReadB
  by_cases h1 : r < s.r
  · left; simp [h1]
  by_cases h2 : r = s.r
  · subst h2; simp only [lt_irrefl, ite_false, ite_true, hpc]
    fin_cases i <;> fin_cases j <;> simp [Function.update]
  · left; simp [h1, h2]

omit I in
theorem rdA_readB {s : St} {m : Mem} {i : Fin 3} (hpc : s.pc = .readB i) (v : Option BV)
    (r : ℕ) (j : Fin 3) :
    rdA (afterReadB s i v) m r j = rdA s m r j := by
  unfold rdA afterReadB
  simp only [hpc]
  split_ifs <;> rfl

theorem inv_step_readA {i : Fin 3} (hpc : (C.loc z).pc = .readA i) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  apply inv_upd I
  · exact hL.same rfl (Or.inl rfl) (by split_ifs <;> simp [ph, hpc]) (by simp [ph, hpc])
      (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h) (by split_ifs <;> simp [hdec])
      (by rw [hL.inp]; split_ifs <;> simp_all) (by split_ifs <;> simp) (by split_ifs <;> simp)
  all_goals try (intro r; left; rfl)
  · intro r j
    rcases rdA_readA hpc (C.mem i (.a (C.loc z).r)) r j with h | ⟨rfl, rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  · intro r j; left; apply rdB_ph0 <;> first | rfl | (simp [ph, hpc]; done) | (split_ifs <;> simp [ph])
  · intro _; exact I.vest z hvest
  · exact I.va z
  · split_ifs <;> simp
  · exact I.out z

theorem inv_step_readB {i : Fin 3} (hpc : (C.loc z).pc = .readB i) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  apply inv_upd I
  · exact hL.same rfl (Or.inl rfl) (by split_ifs <;> simp [ph, hpc]) (fun _ => rfl)
      (fun r => ⟨rfl, rfl, rfl⟩) (fun h => absurd hdec h) (by split_ifs <;> simp [hdec])
      (by rw [hL.inp]; split_ifs <;> simp_all) (by split_ifs <;> simp) (by split_ifs <;> simp)
  all_goals try (intro r; left; rfl)
  · intro r j; left; exact rdA_readB hpc _ r j
  · intro r j
    rcases rdB_readB hpc (C.mem i (.b (C.loc z).r)) r j with h | ⟨rfl, rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  · intro _; exact I.vest z hvest
  · exact I.va z
  · split_ifs <;> simp
  · exact I.out z

theorem inv_step_writeB (hpc : (C.loc z).pc = .writeB) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  have hA1 : C.mem z (.a (C.loc z).r) = some (C.loc z).est := by rw [hL.curA]; simp [ph, hpc]
  have hB0 : C.mem z (.b (C.loc z).r) = none := by rw [hL.curB]; simp [ph, hpc]
  apply inv_upd I
  · refine ⟨fun r hr => ?_, by simpa [ph] using hA1, by simp [ph], by simpa using hL.curE,
      fun r hr => ?_, by simp [hdec], by simp [hdec], ?_, by simp, by simp⟩
    · dsimp only at hr
      have := hL.future r hr
      simpa [Function.update_of_ne (show Reg.b r ≠ Reg.b (C.loc z).r by simp; omega)] using this
    · dsimp only at hr ⊢
      obtain ⟨v, ca, cb, ha, hb, he, h1, h2⟩ := hL.past r hr
      exact ⟨v, ca, cb, by simpa using ha,
        by rw [Function.update_of_ne (show Reg.b r ≠ Reg.b (C.loc z).r by simp; omega), hb],
        by simpa using he, fun h => by simpa using h1 h, h2⟩
    · rw [Function.update_of_ne (by simp), hL.inp]; simp [hpc]
  · intro r; left; simp
  · intro r
    by_cases hr : r = (C.loc z).r
    · subst hr; right; exact hB0
    · left; rw [Function.update_of_ne (by simpa using hr)]
  · intro r; left; simp
  · intro r j; left; unfold rdA
    by_cases h1 : r < (C.loc z).r
    · simp [h1, Function.update_of_ne (show Reg.b r ≠ Reg.b (C.loc z).r by simp; omega)]
    · simp [h1, hpc]
  · intro r j; left; unfold rdB; simp [hpc]
  · intro _; exact I.vest z hvest
  · intro r u h; exact I.va z r u (by simpa using h)
  · simp
  · exact I.out z

theorem inv_step_writeE (hpc : (C.loc z).pc = .writeE) : Inv x (alg.step z ℓ C) := by
  have hL := I.loc z
  rw [step_upd]
  have hdec : C.mem z .dec = none := by
    by_contra h; have := (hL.dec h).1; rw [hpc] at this; cases this
  unfold nxt; rw [hpc]; simp only [Act.post, Act.memUpd, Act.outUpd]
  have hvest : (z ≠ 2 ∨ ((C.loc z).pc ≠ .start ∧ ∀ b, (C.loc z).pc ≠ .getIn b)) :=
    Or.inr ⟨by simp [hpc], by simp [hpc]⟩
  set s := C.loc z with hs
  have hA2 : C.mem z (.a s.r) = some s.est := by rw [hL.curA]; simp [ph, hpc]
  have hB2 : C.mem z (.b s.r) = some (s.est, s.ca) := by rw [hL.curB]; simp [ph, hpc]
  have hE0 : C.mem z (.e s.r) = none := hL.curE
  have hne : ∀ r, r ≠ s.r → Reg.e r ≠ Reg.e s.r := fun r h => by simpa using h
  have hph0 : ph (if (outcome s.est s.cb).1 = true then PC.writeDec else PC.readDec 0) = 0 := by
    split_ifs <;> rfl
  apply inv_upd I
  all_goals try simp only [← hs]
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr => ?_, by simp [hdec], ?_, ?_,
      by split_ifs <;> simp, by split_ifs <;> simp⟩
    · dsimp only at hr
      have := hL.future r (by omega)
      rw [Function.update_of_ne (hne r (by omega))]; simpa using this
    · have := (hL.future (s.r + 1) (by omega)).1
      simpa [hph0] using this
    · have := (hL.future (s.r + 1) (by omega)).2.1
      simpa [hph0] using this
    · have := (hL.future (s.r + 1) (by omega)).2.2
      simp only; rw [Function.update_of_ne (hne _ (by omega))]; exact this
    · dsimp only at hr ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
      · obtain ⟨v, ca, cb, ha, hb, he, h1, h2⟩ := hL.past r hr
        refine ⟨v, ca, cb, by simpa using ha, by simpa using hb,
          by rw [Function.update_of_ne (hne r (by omega)), he], fun h => ?_, fun h => by omega⟩
        simp only [Function.update_of_ne (show Reg.a (r + 1) ≠ Reg.e s.r by simp)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
        · exact h1 h
        · rw [h, hA2, h2 h]
      · exact ⟨s.est, s.ca, s.cb, by simpa using hA2, by simpa using hB2, by simp,
          fun h => by omega, fun _ => rfl⟩
    · intro h
      have h' : (outcome s.est s.cb).1 = true := by
        rcases h with h | h
        · split_ifs at h with h1
          exact h1
        · simp [hdec] at h
      refine ⟨s.r, by simp, s.est, s.cb, by simp, ?_⟩
      ext
      · exact h'
      · rfl
    · rw [Function.update_of_ne (by simp), hL.inp]; split_ifs <;> simp_all
  · intro r; left; simp
  · intro r; left; simp
  · intro r
    by_cases hr : r = s.r
    · subst hr; right; exact hE0
    · left; rw [Function.update_of_ne (hne r hr)]
  · intro r j; left; unfold rdA
    simp only
    rcases lt_trichotomy r s.r with h1 | rfl | h1
    · simp [h1, show r < s.r + 1 by omega]
    · simp [hpc, hB2]
    · rcases Nat.lt_or_ge s.r (r - 1) with h2 | h2
      · simp [show ¬ r < s.r by omega, show r ≠ s.r by omega, show ¬ r < s.r + 1 by omega,
          show r ≠ s.r + 1 by omega]
      · obtain rfl : r = s.r + 1 := by omega
        simp; split_ifs <;> simp
  · intro r j; left; unfold rdB
    simp only
    rcases lt_trichotomy r s.r with h1 | rfl | h1
    · simp [h1, show r < s.r + 1 by omega, Function.update_of_ne (hne r (by omega))]
    · simp [hpc]
    · rcases Nat.lt_or_ge s.r (r - 1) with h2 | h2
      · simp [show ¬ r < s.r by omega, show r ≠ s.r by omega, show ¬ r < s.r + 1 by omega,
          show r ≠ s.r + 1 by omega]
      · obtain rfl : r = s.r + 1 := by omega
        simp; split_ifs <;> simp
  · intro _
    rcases outcome_val s.est s.cb with h | ⟨j, hj⟩
    · rw [h]; exact I.vest z hvest
    · obtain ⟨ca, hcb, -⟩ := cVal_some hj
      have hrd : rdB s (C.mem z) s.r j = some (s.cb j) := by simp [rdB, hpc]
      have hb := I.rb z s.r j _ (by rw [hrd, hcb])
      exact I.va j s.r _ ((I.loc j).of_b hb).2
  · intro r u h; exact I.va z r u (by simpa using h)
  · split_ifs <;> simp
  · exact I.out z

/-- The invariant is preserved by every step. -/
theorem inv_step : Inv x (alg.step z ℓ C) := by
  cases hpc : (C.loc z).pc with
  | start => exact inv_step_start I ℓ hpc
  | getIn b => exact inv_step_getIn I ℓ hpc
  | readDec j => exact inv_step_readDec I ℓ hpc
  | query => exact inv_step_query I ℓ hpc
  | writeA => exact inv_step_writeA I ℓ hpc
  | readA j => exact inv_step_readA I ℓ hpc
  | writeB => exact inv_step_writeB I ℓ hpc
  | readB j => exact inv_step_readB I ℓ hpc
  | writeE => exact inv_step_writeE I ℓ hpc
  | writeDec => exact inv_step_writeDec I ℓ hpc
  | done => exact inv_step_done I ℓ hpc

end Steps

theorem rdA_init (p : Fin 3) (v : Bool) (r : ℕ) (j : Fin 3) :
    rdA (init p v) (fun _ => none) r j = none := by
  unfold rdA init; split_ifs <;> rfl

theorem rdB_init (p : Fin 3) (v : Bool) (r : ℕ) (j : Fin 3) :
    rdB (init p v) (fun _ => none) r j = none := by
  unfold rdB init; split_ifs <;> rfl

/-- The invariant holds initially. -/
theorem inv_init (x : Fin 3 → Bool) : Inv x (alg.initCfg x) := by
  refine ⟨fun p => ⟨fun r _ => ⟨rfl, rfl, rfl⟩, by simp [alg, Alg.initCfg, init, ph],
    by simp [alg, Alg.initCfg, init, ph], rfl, fun r hr => by simp [alg, Alg.initCfg, init] at hr,
    fun h => absurd rfl h, ?_, by simp [alg, Alg.initCfg, init], fun _ => rfl,
    fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (h | h)
    · simp [alg, Alg.initCfg, init] at h
    · exact absurd rfl h
  · intro p r j u h; simp [alg, Alg.initCfg, rdA_init] at h
  · intro p q r res h; simp [alg, Alg.initCfg, rdA_init] at h
  · intro p r j u h; simp [alg, Alg.initCfg, rdB_init] at h
  · intro p q r res h; simp [alg, Alg.initCfg, rdB_init] at h
  · intro p hp
    simp only [alg, Alg.initCfg, init] at hp ⊢
    unfold VV; fin_cases p <;> simp_all
  · intro p r u h; simp [alg, Alg.initCfg] at h
  · intro p h; simp [alg, Alg.initCfg, init] at h
  · intro p u h; simp [alg, Alg.initCfg] at h

/-- The invariant holds in every reachable configuration. -/
theorem inv_conf (x : Fin 3 → Bool) (σ : ℕ → Fin 3) (H : Fin 3 → ℕ → Fin 3) (t : ℕ) :
    Inv x (alg.conf x σ H t) := by
  induction t with
  | zero => exact inv_init x
  | succ t ih => exact inv_step ih _

/-- **Safety**: at every time, the decided values are a valid output of `Tcons`. -/
theorem valid_conf (x : Fin 3 → Bool) (σ : ℕ → Fin 3) (H : Fin 3 → ℕ → Fin 3) (t : ℕ) :
    Tcons.Valid x (alg.conf x σ H t).out := by
  set C := alg.conf x σ H t
  have I := inv_conf x σ H t
  -- the common value of `p₁` and `p₂`
  let c : Bool := ((C.out 0).or (C.out 1)).getD (x 0)
  have hc : VV x c ∧ ∀ i u, i ≠ 2 → C.out i = some u → u = c := by
    rcases h0 : C.out 0 with _ | u0
    · rcases h1 : C.out 1 with _ | u1
      · refine ⟨by simp [c, h0, h1, VV], fun i u hi h => ?_⟩
        fin_cases i <;> simp_all
      · have hu1 := (I.out 1 u1 h1).resolve_left (by decide)
        refine ⟨by simpa [c, h0, h1] using committed_valid I hu1, fun i u hi h => ?_⟩
        fin_cases i <;> simp_all [c]
    · have hu0 := (I.out 0 u0 h0).resolve_left (by decide)
      refine ⟨by simpa [c, h0] using committed_valid I hu0, fun i u hi h => ?_⟩
      fin_cases i
      · simp_all [c]
      · have hu := (I.out 1 u h).resolve_left (by decide)
        simpa [c, h0] using committed_eq I hu hu0
      · exact absurd rfl hi
  refine ⟨fun i => if i = 2 then (C.out 2).getD false else c, ⟨by simp, by simpa [VV] using hc.1⟩,
    fun i u h => ?_⟩
  by_cases hi : i = 2
  · subst hi; simp [h]
  · simp [hi, hc.2 i u hi h]

/-! ## Liveness -/

section Basic

theorem loc_self (z ℓ : Fin 3) (C : Cfg) :
    (alg.step z ℓ C).loc z = (nxt z (C.loc z)).post C.mem ℓ := by
  rw [Alg.step_loc, Function.update_self]; rfl

theorem loc_ne {z ℓ q : Fin 3} (C : Cfg) (h : q ≠ z) : (alg.step z ℓ C).loc q = C.loc q := by
  rw [Alg.step_loc, Function.update_of_ne h]

/-- Registers are written only once. -/
theorem write_fresh {x : Fin 3 → Bool} {C : Cfg} (I : Inv x C) {z : Fin 3} {k : Reg} {v : RV k}
    {s' : St} (h : nxt z (C.loc z) = .write k v s') : C.mem z k = none := by
  have hL := I.loc z
  unfold nxt at h
  split at h
  · split at h
    · cases h
    · cases h; rename_i hpc hz; rw [hL.inp]; simp [hpc]
  all_goals (try cases h)
  all_goals rename_i hpc
  · rw [hL.curA]; simp [ph, hpc]
  · rw [hL.curB]; simp [ph, hpc]
  · exact hL.curE
  · by_contra h'; have := (hL.dec h').1; rw [hpc] at this; cases this

/-- Written values persist. -/
theorem mem_step {x : Fin 3 → Bool} {C : Cfg} (I : Inv x C) (z ℓ q : Fin 3) {k : Reg}
    {v : Pay k} (h : C.mem q k = some v) : (alg.step z ℓ C).mem q k = some v := by
  rw [Alg.step_mem]
  by_cases hq : q = z
  · subst hq; rw [Function.update_self]
    rcases hn : alg.next q (C.loc q) with ⟨k', v', s'⟩ | _ | _ | _
    · simp only [Act.memUpd]
      by_cases hk : k = k'
      · subst hk; have := write_fresh I hn; simp_all
      · rw [Function.update_of_ne hk]; exact h
    all_goals exact h
  · rw [Function.update_of_ne hq]; exact h

/-- The round counter never decreases. -/
theorem r_step (z ℓ q : Fin 3) (C : Cfg) : (C.loc q).r ≤ ((alg.step z ℓ C).loc q).r := by
  by_cases hq : q = z
  · subst hq; rw [loc_self]
    unfold nxt; split <;> (try split) <;> simp [Act.post] <;> (try split) <;> simp
  · rw [loc_ne C hq]

/-- The decision of a process at `done` is set by its next step. -/
theorem out_done {z ℓ : Fin 3} {C : Cfg} (h : (C.loc z).pc = .done) :
    ((alg.step z ℓ C).out z).isSome := by
  rw [Alg.step_out, Function.update_self]
  simp [alg, nxt, h, Act.outUpd]

end Basic

section Exec

variable (x : Fin 3 → Bool) (σ : ℕ → Fin 3) (H : Fin 3 → ℕ → Fin 3)

/-- Configuration at time `t`. -/
local notation "𝒞" t => alg.conf x σ H t

theorem conf_step {t : ℕ} {z : Fin 3} (h : σ t = z) :
    (𝒞 (t + 1)) = alg.step z (H z t) (𝒞 t) := by
  rw [Alg.conf_succ, h]

theorem loc_at {t : ℕ} {z : Fin 3} (h : σ t = z) :
    (𝒞 (t + 1)).loc z = (nxt z ((𝒞 t).loc z)).post (𝒞 t).mem (H z t) := by
  rw [conf_step x σ H h, loc_self]

theorem mem_time {q : Fin 3} {k : Reg} {v : Pay k} {t t' : ℕ} (h : (𝒞 t).mem q k = some v)
    (ht : t ≤ t') : (𝒞 t').mem q k = some v := by
  induction ht with
  | refl => exact h
  | @step m _ ih => rw [Alg.conf_succ]; exact mem_step (inv_conf x σ H m) _ _ _ ih

theorem r_time {q : Fin 3} {t t' : ℕ} (ht : t ≤ t') : ((𝒞 t).loc q).r ≤ ((𝒞 t').loc q).r := by
  induction ht with
  | refl => exact le_rfl
  | @step m _ ih => rw [Alg.conf_succ]; exact ih.trans (r_step _ _ _ _)

/-- Only the helper `p₃` waits for an input. -/
theorem getIn_two (t : ℕ) (p : Fin 3) (b : Bool) (h : ((𝒞 t).loc p).pc = .getIn b) : p = 2 := by
  induction t generalizing b with
  | zero => simp [Alg.conf, Alg.initCfg, alg, init] at h
  | succ t ih =>
    by_cases hp : σ t = p
    · rw [loc_at x σ H hp] at h
      revert h
      unfold nxt
      split
      · split
        · rename_i hp2; intro; exact hp2
        · simp [Act.post]
      · rename_i b' hpc; intro _; exact ih b' hpc
      all_goals simp only [Act.post]
      all_goals first | (intro h; exact ih _ h) | ((try split) <;> (try split) <;> simp)
    · rw [Alg.conf_succ, loc_ne _ (Ne.symm hp)] at h; exact ih b h

/-- Measure of the distance to the loop head `readDec 0` (for `p₁`, `p₂`). -/
def μ₁ : PC → ℕ
  | .start => 14
  | .getIn _ => 0
  | .readDec j => 14 - j.val
  | .query => 11
  | .writeA => 10
  | .readA i => 9 - i.val
  | .writeB => 6
  | .readB i => 5 - i.val
  | .writeE => 2
  | .writeDec => 1
  | .done => 0

variable {x σ H}

/-- A correct process that never decides is never at `done`. -/
theorem not_done {p : Fin 3} (hp : Correct σ p) (hnd : ∀ t, (𝒞 t).out p = none) (t : ℕ) :
    ((𝒞 t).loc p).pc ≠ .done := by
  intro h
  obtain ⟨t', -, ht', hs⟩ := alg.exists_step x σ H hp t
  have := out_done (ℓ := H p t') (C := 𝒞 t') (by rw [hs]; exact h)
  rw [← conf_step x σ H ht', hnd] at this
  simp at this

/-- A correct process `p₁` or `p₂` that never decides keeps coming back to the loop head. -/
theorem reach_head {p : Fin 3} (hp : Correct σ p) (hp2 : p ≠ 2)
    (hnd : ∀ t, (𝒞 t).out p = none) (t : ℕ) : ∃ t' ≥ t, ((𝒞 t').loc p).pc = .readDec 0 := by
  refine alg.reach x σ H hp (fun s => s.pc = .readDec 0) (fun s => μ₁ s.pc) 0 ?_ t (Nat.zero_le _)
  intro t _ hσ hG
  rw [loc_at x σ H hσ]
  have hnd' := not_done hp hnd t
  have hgi : ∀ b, ((𝒞 t).loc p).pc ≠ .getIn b := fun b h => hp2 (getIn_two x σ H t p b h)
  generalize (𝒞 t).loc p = s at hG hnd' hgi ⊢
  unfold nxt
  cases hpc : s.pc with
  | start => simp [hp2, Act.post]
  | getIn b => exact absurd hpc (hgi b)
  | readDec j =>
    simp only [Act.post]; split
    · simp [μ₁]; have := j.isLt; omega
    · rw [hpc] at hG; simp only [μ₁]; right
      split_ifs with hj
      · subst hj; simp
      · revert hG hj; fin_cases j <;> simp
  | query => simp only [Act.post]; split_ifs <;> simp [μ₁]
  | writeA => simp [Act.post, μ₁]
  | readA i => simp only [Act.post]; right; split_ifs with hi <;> simp [μ₁] <;> omega
  | writeB => simp [Act.post, μ₁]
  | readB i => simp only [Act.post]; right; split_ifs with hi <;> simp [μ₁] <;> omega
  | writeE => simp only [Act.post]; split_ifs <;> simp [μ₁]
  | writeDec => simp [Act.post, μ₁]
  | done => exact absurd hpc hnd'

/-- If a correct `p₁` or `p₂` never decides, no decision register is ever written. -/
theorem dec_none {p : Fin 3} (hp : Correct σ p) (hp2 : p ≠ 2)
    (hnd : ∀ t, (𝒞 t).out p = none) (t : ℕ) (j : Fin 3) : (𝒞 t).mem j .dec = none := by
  by_contra hne
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hne
  -- after time `t`, reading `DEC_j` makes `p` decide
  have key : ∀ n, ∀ i : Fin 3, i.val + n = j.val → ∀ t' ≥ t,
      ((𝒞 t').loc p).pc = .readDec i → False := by
    intro n
    induction n with
    | zero =>
      intro i hi t' ht' hpc
      obtain rfl : i = j := Fin.ext (by omega)
      obtain ⟨t'', ht'', hσ, hs⟩ := alg.exists_step x σ H hp t'
      apply not_done hp hnd (t'' + 1)
      rw [loc_at x σ H hσ, hs]; unfold nxt; rw [hpc]
      simp [Act.post, mem_time x σ H hu (by omega : t ≤ t'')]
    | succ n ih =>
      intro i hi t' ht' hpc
      obtain ⟨t'', ht'', hσ, hs⟩ := alg.exists_step x σ H hp t'
      rcases hv : (𝒞 t'').mem i .dec with _ | v
      · apply ih (i + 1) (by revert hi; fin_cases i <;> fin_cases j <;> simp <;> omega)
          (t'' + 1) (by omega)
        rw [loc_at x σ H hσ, hs]; unfold nxt; rw [hpc]
        simp only [Act.post, hv]
        have : i ≠ 2 := by intro h; subst h; revert hi; fin_cases j <;> (simp; try omega)
        simp [this]
      · apply not_done hp hnd (t'' + 1)
        rw [loc_at x σ H hσ, hs]; unfold nxt; rw [hpc]
        simp [Act.post, hv]
  obtain ⟨t', ht', hpc⟩ := reach_head hp hp2 hnd t
  exact key j.val 0 (by simp) t' ht' hpc

theorem writeDec_writes {t : ℕ} {q : Fin 3} (hσ : σ t = q)
    (hpc : ((𝒞 t).loc q).pc = .writeDec) :
    (𝒞 (t + 1)).mem q .dec = some ((𝒞 t).loc q).dv := by
  rw [conf_step x σ H hσ, Alg.step_mem, Function.update_self]
  show (nxt q ((𝒞 t).loc q)).memUpd _ .dec = _
  unfold nxt; rw [hpc]; simp [Act.memUpd]

/-- If no decision register is ever written, nobody reaches `done`. -/
theorem no_done (hdn : ∀ t j, (𝒞 t).mem j .dec = none) (t : ℕ) (q : Fin 3) :
    ((𝒞 t).loc q).pc ≠ .done := by
  induction t with
  | zero => simp [Alg.conf, Alg.initCfg, alg, init]
  | succ t ih =>
    by_cases hσ : σ t = q
    · rw [loc_at x σ H hσ]
      unfold nxt
      cases hpc : ((𝒞 t).loc q).pc with
      | readDec j => simp only [Act.post, hdn t j]; split_ifs <;> simp
      | writeDec =>
        have := writeDec_writes hσ hpc
        rw [hdn] at this; simp at this
      | done => exact absurd hpc ih
      | start => split_ifs <;> simp [Act.post]
      | getIn b => simp only [Act.post]; split <;> simp
      | query => simp only [Act.post]; split_ifs <;> simp
      | readA i => simp only [Act.post]; split_ifs <;> simp
      | readB i => simp only [Act.post]; split_ifs <;> simp
      | writeE => simp only [Act.post]; split_ifs <;> simp
      | writeA => simp [Act.post]
      | writeB => simp [Act.post]
    · rw [Alg.conf_succ, loc_ne _ (Ne.symm hσ)]; exact ih

/-- A correct process never stays at `writeDec` if no decision register is ever written. -/
theorem not_writeDec (hdn : ∀ t j, (𝒞 t).mem j .dec = none) {q : Fin 3} (hq : Correct σ q)
    (t : ℕ) : ((𝒞 t).loc q).pc ≠ .writeDec := by
  intro hpc
  obtain ⟨t', -, hσ, hs⟩ := alg.exists_step x σ H hq t
  have := writeDec_writes hσ (by rw [hs]; exact hpc)
  rw [hdn] at this; simp at this

/-- After some time, only correct processes take steps and they see the final leader `ℓ`. -/
theorem exists_stable (hΩ : OmegaValid σ H) :
    ∃ ℓ, Correct σ ℓ ∧ ∃ T, ∀ t ≥ T, Correct σ (σ t) ∧ H (σ t) t = ℓ := by
  obtain ⟨ℓ, hℓ, T₀, hT₀⟩ := hΩ
  have hf : ∀ q : Fin 3, ∃ T, ∀ t ≥ T, σ t = q → Correct σ q := by
    intro q
    by_cases hq : Correct σ q
    · exact ⟨0, fun _ _ _ => hq⟩
    · unfold Correct at hq; push Not at hq
      obtain ⟨T, hT⟩ := hq
      exact ⟨T, fun t ht h => absurd h (hT t ht)⟩
  choose f hf using hf
  refine ⟨ℓ, hℓ, T₀ + f 0 + f 1 + f 2, fun t ht => ?_⟩
  have hc : Correct σ (σ t) := by
    have : ∀ q : Fin 3, f q ≤ t := by intro q; fin_cases q <;> simp <;> omega
    exact hf (σ t) t (this _) rfl
  exact ⟨hc, hT₀ t (by omega) _ hc⟩

/-- After the stabilization time `T`, a process `q ≠ ℓ` starts no new round: its round counter
stays `≤ R + 1` (`R` its round at time `T`), and in round `R + 1` it never writes. -/
theorem others_bounded {ℓ : Fin 3} {T : ℕ}
    (hT : ∀ t ≥ T, Correct σ (σ t) ∧ H (σ t) t = ℓ) {q : Fin 3} (hq : q ≠ ℓ) :
    ∀ t ≥ T, ((𝒞 t).loc q).r ≤ ((𝒞 T).loc q).r + 1 ∧
      (((𝒞 t).loc q).r = ((𝒞 T).loc q).r + 1 →
        ph ((𝒞 t).loc q).pc = 0 ∧ ((𝒞 t).loc q).pc ≠ .writeA) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨by omega, fun h => by omega⟩
  | succ t ht ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hσ : σ t = q
    · have hH : H q t = ℓ := by rw [← hσ]; exact (hT t ht).2
      rw [loc_at x σ H hσ, hH]
      generalize hs : (𝒞 t).loc q = s at h1 h2
      generalize ((𝒞 T).loc q).r = R at h1 h2 ⊢
      unfold nxt
      cases hpc : s.pc with
      | start => rw [hpc] at h2; split_ifs <;> simp_all [Act.post, ph]
      | getIn b => rw [hpc] at h2; simp only [Act.post]; split <;> simp_all [ph]
      | readDec j =>
        rw [hpc] at h2; simp only [Act.post]; split <;> (try split_ifs) <;> simp_all [ph]
      | query => rw [hpc] at h2; simp [Act.post, Ne.symm hq, ph]; simp_all [ph]
      | writeA =>
        rw [hpc] at h2; simp only [Act.post]
        have : s.r ≠ R + 1 := fun h => (h2 h).2 rfl
        exact ⟨h1, fun h => absurd h this⟩
      | readA i =>
        rw [hpc] at h2; simp only [Act.post]
        have : s.r ≠ R + 1 := fun h => by simpa [ph] using (h2 h).1
        exact ⟨h1, fun h => absurd h this⟩
      | writeB =>
        rw [hpc] at h2; simp only [Act.post]
        have : s.r ≠ R + 1 := fun h => by simpa [ph] using (h2 h).1
        exact ⟨h1, fun h => absurd h this⟩
      | readB i =>
        rw [hpc] at h2; simp only [Act.post]
        have : s.r ≠ R + 1 := fun h => by simpa [ph] using (h2 h).1
        exact ⟨h1, fun h => absurd h this⟩
      | writeE =>
        rw [hpc] at h2; simp only [Act.post]
        have : s.r ≠ R + 1 := fun h => by simpa [ph] using (h2 h).1
        refine ⟨by omega, fun _ => ?_⟩
        split_ifs <;> simp [ph]
      | writeDec => rw [hpc] at h2; simp_all [Act.post, ph]
      | done => rw [hpc] at h2; simp_all [Act.post, ph]
    · rw [Alg.conf_succ, loc_ne _ (Ne.symm hσ)]; exact ⟨h1, h2⟩

/-- Consequently, `q ≠ ℓ` never writes `A[r]` or `B[r]` for `r` above its round at time `T`. -/
theorem others_silent {ℓ : Fin 3} {T : ℕ}
    (hT : ∀ t ≥ T, Correct σ (σ t) ∧ H (σ t) t = ℓ) {q : Fin 3} (hq : q ≠ ℓ) {t : ℕ}
    (ht : T ≤ t) {r : ℕ} (hr : ((𝒞 T).loc q).r + 1 ≤ r) :
    (𝒞 t).mem q (.a r) = none ∧ (𝒞 t).mem q (.b r) = none := by
  obtain ⟨h1, h2⟩ := others_bounded (x := x) hT hq t ht
  have hL := (inv_conf x σ H t).loc q
  rcases Nat.lt_or_ge ((𝒞 t).loc q).r r with h | h
  · exact ⟨(hL.future r h).1, (hL.future r h).2.1⟩
  · obtain rfl : r = ((𝒞 t).loc q).r := by omega
    have := (h2 (by omega)).1
    rw [hL.curA, hL.curB]; simp [this]

end Exec

/-- A leader running a round alone commits. -/
theorem solo_commit {x : Fin 3 → Bool} {C : Cfg} (I : Inv x C) {ℓ : Fin 3}
    (hpc : (C.loc ℓ).pc = .writeE)
    (hsolo : ∀ j, j ≠ ℓ → C.mem j (.a (C.loc ℓ).r) = none ∧ C.mem j (.b (C.loc ℓ).r) = none) :
    (outcome (C.loc ℓ).est (C.loc ℓ).cb).1 = true := by
  have hL := I.loc ℓ
  set s := C.loc ℓ with hs
  have hrdA : ∀ j, rdA (C.loc ℓ) (C.mem ℓ) s.r j = some (s.ca j) := fun j => by
    simp [rdA, ← hs, hpc]
  have hrdB : ∀ j, rdB (C.loc ℓ) (C.mem ℓ) s.r j = some (s.cb j) := fun j => by
    simp [rdB, ← hs, hpc]
  have hA : C.mem ℓ (.a s.r) = some s.est := by rw [hL.curA]; simp [ph, hpc]
  have hB : C.mem ℓ (.b s.r) = some (s.est, s.ca) := by rw [hL.curB]; simp [ph, hpc]
  have hca : Flag s.est s.ca := by
    intro j
    by_cases hj : j = ℓ
    · subst hj
      rcases hc : s.ca j with _ | u
      · exact absurd rfl (I.xa j j s.r none (by rw [hrdA, hc]) (by rw [hrdA, hc]))
      · have := I.ra j s.r j u (by rw [hrdA, hc]); rw [hA] at this; cases this; simp
    · left
      rcases hc : s.ca j with _ | u
      · rfl
      · have := I.ra ℓ s.r j u (by rw [hrdA, hc]); rw [(hsolo j hj).1] at this; cases this
  have hcb : AllC s.cb := by
    intro j
    by_cases hj : j = ℓ
    · subst hj
      rcases hc : s.cb j with _ | bv
      · exact absurd rfl (I.xb j j s.r none (by rw [hrdB, hc]) (by rw [hrdB, hc]))
      · have := I.rb j s.r j bv (by rw [hrdB, hc]); rw [hB] at this; cases this
        right; simp [cVal, hca]
    · left
      rcases hc : s.cb j with _ | bv
      · rfl
      · have := I.rb ℓ s.r j bv (by rw [hrdB, hc]); rw [(hsolo j hj).2] at this; cases this
  simp [outcome, hcb]


/-- Measure of the distance to `writeE` for the eventual leader (`p` is a correct process among
`p₁`, `p₂`, whose input the helper eventually reads). -/
def ν (p : Fin 3) : PC → ℕ
  | .start => 16
  | .getIn b => if (if b then (1 : Fin 3) else 0) = p then 14 else 15
  | .readDec j => 12 - j.val
  | .query => 9
  | .writeA => 8
  | .readA i => 7 - i.val
  | .writeB => 4
  | .readB i => 3 - i.val
  | .writeE => 0
  | .writeDec => 0
  | .done => 0

section Exec2

variable {x : Fin 3 → Bool} {σ : ℕ → Fin 3} {H : Fin 3 → ℕ → Fin 3}

/-- Configuration at time `t`. -/
local notation "𝒞" t => alg.conf x σ H t

/-- After stabilization, the leader keeps reaching the end of a commit-adopt round. -/
theorem leader_progress (hdn : ∀ t j, (𝒞 t).mem j .dec = none) {ℓ : Fin 3} (hℓ : Correct σ ℓ)
    {T : ℕ} (hT : ∀ t ≥ T, Correct σ (σ t) ∧ H (σ t) t = ℓ) {p : Fin 3} (hp2 : p ≠ 2)
    (hin : ∀ t ≥ T, (𝒞 t).mem p .inR ≠ none) :
    ∀ t ≥ T, ∃ t' ≥ t, ((𝒞 t').loc ℓ).pc = .writeE := by
  refine alg.reach x σ H hℓ (fun s => s.pc = .writeE) (fun s => ν p s.pc) T ?_
  intro t ht hσ hG
  have hH : H ℓ t = ℓ := by have := (hT t ht).2; rwa [hσ] at this
  have hnd := no_done hdn t ℓ
  have hnw := not_writeDec hdn hℓ t
  rw [loc_at x σ H hσ, hH]
  generalize hs : (𝒞 t).loc ℓ = s at hG hnd hnw
  unfold nxt
  cases hpc : s.pc with
  | start => simp only [Act.post]; split_ifs <;> simp [ν]; split_ifs <;> simp
  | getIn b =>
    simp only [Act.post]; right
    have hp01 : p = 0 ∨ p = 1 := by fin_cases p <;> simp_all
    split
    · rename_i v u hv; simp [ν]; split_ifs <;> simp
    · rename_i v hv
      have hne : (if b then (1 : Fin 3) else 0) ≠ p := by
        intro h; rw [h] at hv; exact hin t ht hv
      simp only [ν, hne, ite_false]
      rcases hp01 with rfl | rfl <;> cases b <;> simp_all
  | readDec j =>
    simp only [Act.post, hdn t j]; right
    split_ifs with hj
    · subst hj; simp [ν]
    · fin_cases j <;> simp_all [ν]
  | query => simp [Act.post, ν]
  | writeA => simp [Act.post, ν]
  | readA i => simp only [Act.post]; right; split_ifs with hi <;> simp [ν] <;> (try fin_cases i) <;> simp_all
  | writeB => simp [Act.post, ν]
  | readB i =>
    simp only [Act.post]
    split_ifs with hi
    · left; rfl
    · right; simp [ν]; fin_cases i <;> simp_all
  | writeE => exact absurd hpc hG
  | writeDec => exact absurd hpc hnw
  | done => exact absurd hpc hnd

/-- **Liveness**: every correct process decides. -/
theorem live (hΩ : OmegaValid σ H) (p : Fin 3) (hp : Correct σ p) :
    ∃ t, ((𝒞 t).out p).isSome := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨t', -, hσ, hs⟩ := alg.exists_step x σ H hp 0
    refine ⟨t' + 1, ?_⟩
    rw [conf_step x σ H hσ, Alg.step_out, Function.update_self]
    show ((nxt 2 ((𝒞 t').loc 2)).outUpd _).isSome
    rw [hs]; simp [Alg.conf, Alg.initCfg, alg, init, nxt, Act.outUpd]
  by_contra hno
  have hnd : ∀ t, (𝒞 t).out p = none := fun t => by
    by_contra h; exact hno ⟨t, Option.ne_none_iff_isSome.1 h⟩
  have hdn := dec_none hp hp2 hnd
  obtain ⟨ℓ, hℓ, T₁, hT₁⟩ := exists_stable hΩ
  -- the input of `p` is written at its first step
  obtain ⟨t₀, -, hσ₀, hs₀⟩ := alg.exists_step x σ H hp 0
  have hin0 : (𝒞 (t₀ + 1)).mem p .inR = some (x p) := by
    rw [((inv_conf x σ H (t₀ + 1)).loc p).inp, loc_at x σ H hσ₀, hs₀]
    simp [Alg.conf, Alg.initCfg, alg, init, nxt, hp2, Act.post]
  set T := T₁ + t₀ + 1 with hTdef
  have hT : ∀ t ≥ T, Correct σ (σ t) ∧ H (σ t) t = ℓ := fun t ht => hT₁ t (by omega)
  have hin : ∀ t ≥ T, (𝒞 t).mem p .inR ≠ none := fun t ht => by
    rw [mem_time x σ H hin0 (by omega : t₀ + 1 ≤ t)]; simp
  -- the leader runs arbitrarily high rounds
  have rounds : ∀ n, ∃ t ≥ T, ((𝒞 t).loc ℓ).pc = .writeE ∧ n ≤ ((𝒞 t).loc ℓ).r := by
    intro n
    induction n with
    | zero =>
      obtain ⟨t, ht, hpc⟩ := leader_progress hdn hℓ hT hp2 hin T le_rfl
      exact ⟨t, ht, hpc, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨t, ht, hpc, hn⟩ := ih
      obtain ⟨t', ht', hσ, hs⟩ := alg.exists_step x σ H hℓ t
      have hr : ((𝒞 (t' + 1)).loc ℓ).r = ((𝒞 t).loc ℓ).r + 1 := by
        rw [loc_at x σ H hσ, hs]; unfold nxt; rw [hpc]; simp [Act.post]
      obtain ⟨t'', ht'', hpc''⟩ := leader_progress hdn hℓ hT hp2 hin (t' + 1) (by omega)
      exact ⟨t'', by omega, hpc'', by have := r_time x σ H (q := ℓ) ht''; omega⟩
  let R : Fin 3 → ℕ := fun q => ((𝒞 T).loc q).r
  obtain ⟨t, ht, hpc, hr⟩ := rounds (R 0 + R 1 + R 2 + 1)
  have hsolo : ∀ j, j ≠ ℓ → (𝒞 t).mem j (.a ((𝒞 t).loc ℓ).r) = none ∧
      (𝒞 t).mem j (.b ((𝒞 t).loc ℓ).r) = none := fun j hj =>
    others_silent (x := x) hT hj ht (by fin_cases j <;> simp [R] at hr ⊢ <;> omega)
  have hc := solo_commit (inv_conf x σ H t) hpc hsolo
  obtain ⟨t', -, hσ, hs⟩ := alg.exists_step x σ H hℓ t
  apply not_writeDec hdn hℓ (t' + 1)
  rw [loc_at x σ H hσ, hs]; unfold nxt; rw [hpc]; simp [Act.post, hc]

end Exec2

/-- The algorithm solves `Tcons` in `ARW_{3,2}[fd : Ω]`. -/
theorem alg_solves : alg.Solves Tcons :=
  fun x _ σ H hΩ => ⟨fun p hp => live hΩ p hp, valid_conf x σ H⟩

end ArwCons

/-- **`Tcons` is solvable in `ARW_{3,2}[fd : Ω]`** (wait-free, with the helper `p₃`): commit-adopt
rounds run by the processes that `Ω` designates as leader. -/
theorem tcons_solvable_arw_omega : SolvableARWOmega Tcons :=
  ⟨ArwCons.Reg, inferInstance, ArwCons.RV, ArwCons.St, ArwCons.alg, ArwCons.alg_solves⟩

/-- **Lemma 2 of the paper is false** (for `n = 3`, under the paper's semantics where every
process of `SMP_n` must output): some task solvable in `ARW_{n,n-1}[fd : Ω]` is not solvable in
`SMP_n[adv : SOURCE, TOUR]`. Hence the equivalence `ARW_{n,n-1}[fd : Ω] ≃ SMP_n[adv : SOURCE,
TOUR]` of Theorem 2 fails too. -/
theorem lemma2_false :
    ∃ T : Task (Fin 3) Bool Bool, SolvableARWOmega T ∧ ¬ Solvable (SOURCE ∩ TOUR) T :=
  ⟨Tcons, tcons_solvable_arw_omega,
    fun h => tcons_not_solvable (h.mono Set.inter_subset_left)⟩

end Podc.MessageAdversariesVsFD
