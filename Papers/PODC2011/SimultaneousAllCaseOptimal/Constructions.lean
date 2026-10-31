import Papers.PODC2011.SimultaneousAllCaseOptimal.Model

/-!
# Protocol constructions of §3: `Delay(A, k)`, `A else B`, `ConCon(A)` and `Opt(A, k̂)`

* `Delay A k` (Lemma 1): `A`'s messages, decisions postponed to time `k`.
* `Else A B` (Moses–Raynal's parallel composition, used in Theorem 3): run both, decide at the
  first time one of them decides, preferring `A`.
* `ConCon C A T` (Theorem 2): a continuous-consensus protocol `C` is run until its core becomes
  nonempty; then the process simulates the run of `A` in which the processes of the core start with
  their core values and are correct, and all other processes crash silently in round 1, and decides
  as in that run. The ConCon protocol of Mizrahi–Moses is *not* formalized: `C` is any protocol
  with the properties the paper lists in §2.3 (`IsConCon`).
* `Opt C A T k = Else (Delay A k) (ConCon C A T)` (Theorem 3, §4).
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I M O : Type} [Fintype P]

/-! ### `Delay(A, k)` -/

/-- The first nonempty register content among the prefixes `h.take 0, …, h.take n`. -/
def firstDecUpTo (A : Protocol P I M O) (p : P) (x : I) (h : History P M) : ℕ → Option O
  | 0 => A.decide p x (h.take 0)
  | n + 1 => match firstDecUpTo A p x h n with
    | some d => some d
    | none => A.decide p x (h.take (n + 1))

/-- The first decision of `A` along the history `h`. -/
def firstDec (A : Protocol P I M O) (p : P) (x : I) (h : History P M) : Option O :=
  firstDecUpTo A p x h h.length

/-- `Delay(A, k)` (§3): same messages as `A`; the first decision of `A` is written to the output
register only at time `k` (decisions after time `k` are unchanged). -/
def Delay (A : Protocol P I M O) (k : ℕ) : Protocol P I M O where
  send := A.send
  decide p x h := if h.length < k then none else firstDec A p x h

lemma firstDecUpTo_hist {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} :
    ∀ n ≤ m, ∀ d, firstDecUpTo A p (r.input p) (hist A r m p) n = some d ↔
      ∃ j ≤ n, raw A r p j = some d ∧ ∀ i < j, raw A r p i = none := by
  intro n
  induction n with
  | zero =>
    intro hn d
    simp only [firstDecUpTo, hist_take A r (Nat.zero_le m)]
    constructor
    · intro h; exact ⟨0, le_rfl, h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rintro ⟨j, hj, h, -⟩
      have : j = 0 := by omega
      subst this; exact h
  | succ n ih =>
    intro hn d
    simp only [firstDecUpTo]
    cases h1 : firstDecUpTo A p (r.input p) (hist A r m p) n with
    | some d1 =>
      obtain ⟨j, hj, hjd, hjl⟩ := (ih (by omega) d1).1 h1
      simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨j, by omega, hjd, hjl⟩
      · rintro ⟨j', hj', hj'd, hj'l⟩
        have hjj : j = j' := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := hj'l j h; rw [hjd] at this; simp at this
          · have := hjl j' h; rw [hj'd] at this; simp at this
        subst hjj; rw [hjd] at hj'd; exact Option.some_injective _ hj'd
    | none =>
      simp only [hist_take A r hn]
      have hnone : ∀ j ≤ n, raw A r p j = none := by
        intro j hj
        by_contra hc
        obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 hc
        -- the first nonempty one before `j`
        classical
        have hex : ∃ j', j' ≤ n ∧ (raw A r p j').isSome := ⟨j, hj, by simp [hd']⟩
        let j0 := Nat.find hex
        obtain ⟨hj0, hj0s⟩ := Nat.find_spec hex
        obtain ⟨d0, hd0⟩ := Option.isSome_iff_exists.1 hj0s
        have := (ih (by omega) d0).2 ⟨j0, hj0, hd0, fun i hi => by
          have := Nat.find_min hex hi
          simp only [not_and, Option.isSome_iff_ne_none, ne_eq, not_not] at this
          exact this (by omega)⟩
        rw [h1] at this; simp at this
      constructor
      · intro h; exact ⟨n + 1, le_rfl, h, fun i hi => hnone i (by omega)⟩
      · rintro ⟨j, hj, hjd, hjl⟩
        rcases Nat.lt_or_ge j (n + 1) with hlt | hge
        · rw [hnone j (by omega)] at hjd; simp at hjd
        · have : j = n + 1 := by omega
          subst this; exact hjd

lemma firstDec_hist {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} {d : O} :
    firstDec A p (r.input p) (hist A r m p) = some d ↔
      ∃ j ≤ m, raw A r p j = some d ∧ ∀ i < j, raw A r p i = none := by
  unfold firstDec; rw [Cslib.SyncCrash.length_hist]; exact firstDecUpTo_hist m le_rfl d

lemma hist_delay (A : Protocol P I M O) (k : ℕ) (r : Run P I) (m : ℕ) (p : P) :
    hist (Delay A k) r m p = hist A r m p := hist_eq_of_send (A := Delay A k) (B := A) rfl r m p

lemma raw_delay {A : Protocol P I M O} {k : ℕ} {r : Run P I} {p : P} {m : ℕ} :
    raw (Delay A k) r p m = if m < k then none else firstDec A p (r.input p) (hist A r m p) := by
  rw [raw, hist_delay]; simp only [Delay, Cslib.SyncCrash.length_hist]

/-- Decisions of `Delay(A, k)`: `p` decides at time `max k m` the value `A` has it decide at time
`m`. -/
lemma decides_delay_iff {A : Protocol P I M O} {k : ℕ} {r : Run P I} {p : P} {m : ℕ} {d : O} :
    Decides (Delay A k) r p m d ↔ r.Alive p m ∧ ∃ mA, Decides A r p mA d ∧ m = max k mA := by
  rw [decides_iff]
  simp only [raw_delay]
  constructor
  · rintro ⟨ha, h1, h2⟩
    split_ifs at h1 with hmk
    obtain ⟨j, hj, hjd, hjl⟩ := firstDec_hist.1 h1
    refine ⟨ha, j, decides_iff.2 ⟨ha.mono hj, hjd, hjl⟩, ?_⟩
    by_contra hne
    have hlt : k < m ∧ j < m := by omega
    have := h2 (m - 1) (by omega)
    rw [if_neg (by omega), firstDec_hist.2 ⟨j, by omega, hjd, hjl⟩] at this
    simp at this
  · rintro ⟨ha, mA, hA, rfl⟩
    refine ⟨ha, ?_, fun m' hm' => ?_⟩
    · rw [if_neg (by omega)]
      exact firstDec_hist.2 ⟨mA, by omega, hA.raw_eq, fun i hi => hA.raw_lt hi⟩
    · split_ifs with h
      · rfl
      · cases hf : firstDec A p (r.input p) (hist A r m' p) with
        | none => rfl
        | some d' =>
          obtain ⟨j, hj, hjd, hjl⟩ := firstDec_hist.1 hf
          have := (Decides.unique hA (decides_iff.2 ⟨ha.mono (by omega), hjd, hjl⟩)).1
          omega

/-- Before time `k`, `Delay(A, k)` has written nothing. -/
lemma raw_delay_lt {A : Protocol P I M O} {k : ℕ} {r : Run P I} {p : P} {m : ℕ} (hm : m < k) :
    raw (Delay A k) r p m = none := by
  rw [raw_delay, if_pos hm]

/-- `Delay(B, k)` solves `sim(T)` whenever `B` does. -/
theorem delay_solvesSim {B : Protocol P I M O} {T : Task P I O} {t : ℕ} (hB : SolvesSim B T t)
    (k : ℕ) : SolvesSim (Delay B k) T t where
  complete r hr p hp := by
    obtain ⟨m, d, hd⟩ := hB.complete r hr p hp
    exact ⟨max k m, d, decides_delay_iff.2 ⟨Run.alive_of_not_faulty hp _, m, hd, rfl⟩⟩
  correct r hr := by
    obtain ⟨o, ho, hdec⟩ := hB.correct r hr
    refine ⟨o, ho, fun p m d hd => ?_⟩
    obtain ⟨-, mA, hA, -⟩ := decides_delay_iff.1 hd
    exact hdec p mA d hA
  simultaneous r hr p q m m' d d' hp hq := by
    obtain ⟨-, mA, hA, rfl⟩ := decides_delay_iff.1 hp
    obtain ⟨-, mB, hB', rfl⟩ := decides_delay_iff.1 hq
    rw [hB.simultaneous r hr p q mA mB d d' hA hB']

/-- **Lemma 1.** If `A` solves `T` and every nonfaulty process decides by time `k̂`, then
`Delay(A, k̂)` solves `sim(T)`, and every decision happens at time exactly `k̂`. -/
theorem lemma1 {A : Protocol P I M O} {T : Task P I O} {t k : ℕ} (hA : SolvesWithin A T t k) :
    SolvesSim (Delay A k) T t ∧
      (∀ r, T.IsRun t r → ∀ p m d, Decides (Delay A k) r p m d → m = k) ∧
      (∀ r, T.IsRun t r → ∀ p, r.Alive p k → ∃ d, Decides (Delay A k) r p k d) := by
  have htime : ∀ r, T.IsRun t r → ∀ p m d, Decides (Delay A k) r p m d → m = k := by
    intro r hr p m d hd
    obtain ⟨ha, mA, hmA, rfl⟩ := decides_delay_iff.1 hd
    obtain ⟨m1, hm1, d1, hd1⟩ := hA.decides_of_alive hr (ha.mono (le_max_left _ _))
    have := (Decides.unique hmA hd1).1
    omega
  have halive : ∀ r, T.IsRun t r → ∀ p, r.Alive p k → ∃ d, Decides (Delay A k) r p k d := by
    intro r hr p hp
    obtain ⟨m1, hm1, d1, hd1⟩ := hA.decides_of_alive hr hp
    exact ⟨d1, decides_delay_iff.2 ⟨hp, m1, hd1, by omega⟩⟩
  refine ⟨{ complete := ?_, correct := ?_, simultaneous := ?_ }, htime, halive⟩
  · intro r hr p hp
    obtain ⟨d, hd⟩ := halive r hr p (Run.alive_of_not_faulty hp k)
    exact ⟨k, d, hd⟩
  · intro r hr
    obtain ⟨o, ho, hdec⟩ := hA.correct r hr
    refine ⟨o, ho, fun p m d hd => ?_⟩
    obtain ⟨-, mA, hmA, -⟩ := decides_delay_iff.1 hd
    exact hdec p mA d hmA
  · intro r hr p q m m' d d' hp hq
    rw [htime r hr p m d hp, htime r hr q m' d' hq]

/-! ### Parallel composition `A else B` -/

-- CSLib candidate (`Delay`, `Else`, `hist_else`, `else_solvesSim`)

/-- Project a history of the composed protocol to the first component. -/
def projL {MA MB : Type} (h : History P (Option MA × Option MB)) : History P MA :=
  h.map fun inbox q => (inbox q).bind Prod.fst

/-- Project a history of the composed protocol to the second component. -/
def projR {MA MB : Type} (h : History P (Option MA × Option MB)) : History P MB :=
  h.map fun inbox q => (inbox q).bind Prod.snd

/-- `A else B` (Moses–Raynal, §3): both protocols run in parallel (each message carries both
components); a process decides at the first time one of them has it decide, preferring `A`. -/
def Else {MA MB : Type} (A : Protocol P I MA O) (B : Protocol P I MB O) :
    Protocol P I (Option MA × Option MB) O where
  send p x h q := some (A.send p x (projL h) q, B.send p x (projR h) q)
  decide p x h := match A.decide p x (projL h) with
    | some d => some d
    | none => B.decide p x (projR h)

lemma else_send {MA MB : Type} (A : Protocol P I MA O) (B : Protocol P I MB O) (p : P) (x : I)
    (h : History P (Option MA × Option MB)) (q : P) :
    (Else A B).send p x h q = some (A.send p x (projL h) q, B.send p x (projR h) q) := rfl

lemma else_decide {MA MB : Type} (A : Protocol P I MA O) (B : Protocol P I MB O) (p : P) (x : I)
    (h : History P (Option MA × Option MB)) :
    (Else A B).decide p x h = match A.decide p x (projL h) with
      | some d => some d
      | none => B.decide p x (projR h) := rfl

variable {MA MB : Type} {A : Protocol P I MA O} {B : Protocol P I MB O}

lemma hist_else (r : Run P I) (m : ℕ) (p : P) :
    projL (hist (Else A B) r m p) = hist A r m p ∧ projR (hist (Else A B) r m p) = hist B r m p := by
  induction m generalizing p with
  | zero => simp [projL, projR]
  | succ m ih =>
    rw [Cslib.SyncCrash.hist_succ, Cslib.SyncCrash.hist_succ, Cslib.SyncCrash.hist_succ]
    simp only [projL, projR, List.map_append, List.map_cons, List.map_nil]
    refine ⟨?_, ?_⟩
    · rw [show List.map _ (hist (Else A B) r m p) = projL (hist (Else A B) r m p) from rfl,
        (ih p).1]
      congr 2
      funext q
      rw [msg_eq_deliv, msg_eq_deliv]
      split_ifs <;> simp only [else_send, Option.bind_some, (ih q).1, Option.bind_none]
    · rw [show List.map _ (hist (Else A B) r m p) = projR (hist (Else A B) r m p) from rfl,
        (ih p).2]
      congr 2
      funext q
      rw [msg_eq_deliv, msg_eq_deliv]
      split_ifs <;> simp only [else_send, Option.bind_some, (ih q).2, Option.bind_none]

lemma raw_else (r : Run P I) (p : P) (m : ℕ) :
    raw (Else A B) r p m = match raw A r p m with
      | some d => some d
      | none => raw B r p m := by
  simp only [raw, else_decide, (hist_else r m p).1, (hist_else r m p).2]

lemma raw_else_eq_none {r : Run P I} {p : P} {m : ℕ} :
    raw (Else A B) r p m = none ↔ raw A r p m = none ∧ raw B r p m = none := by
  rw [raw_else]; cases raw A r p m <;> simp

/-- Decisions of `A else B`. -/
lemma decides_else_iff {r : Run P I} {p : P} {m : ℕ} {d : O} :
    Decides (Else A B) r p m d ↔ r.Alive p m ∧
      (∀ m' < m, raw A r p m' = none ∧ raw B r p m' = none) ∧
      (raw A r p m = some d ∨ (raw A r p m = none ∧ raw B r p m = some d)) := by
  rw [decides_iff]
  simp only [raw_else_eq_none]
  rw [raw_else]
  cases raw A r p m with
  | none => simp only [reduceCtorEq, false_or, true_and]; tauto
  | some a => simp only [Option.some.injEq, true_or, reduceCtorEq, false_and, or_false]; aesop

/-- A decision of `A else B` is a decision of `A` or of `B` at the same time, with the same
value. -/
lemma Decides.else_cases {r : Run P I} {p : P} {m : ℕ} {d : O} (h : Decides (Else A B) r p m d) :
    Decides A r p m d ∨ (raw A r p m = none ∧ Decides B r p m d) := by
  obtain ⟨ha, hlt, h1 | ⟨h1, h2⟩⟩ := decides_else_iff.1 h
  · exact Or.inl (decides_iff.2 ⟨ha, h1, fun m' hm' => (hlt m' hm').1⟩)
  · exact Or.inr ⟨h1, decides_iff.2 ⟨ha, h2, fun m' hm' => (hlt m' hm').2⟩⟩

lemma decides_else_of_left {r : Run P I} {p : P} {m : ℕ} {d : O} (h : Decides A r p m d)
    (hB : ∀ m' < m, raw B r p m' = none) : Decides (Else A B) r p m d :=
  decides_else_iff.2 ⟨h.alive, fun m' hm' => ⟨h.raw_lt hm', hB m' hm'⟩, Or.inl h.raw_eq⟩

lemma decides_else_of_right {r : Run P I} {p : P} {m : ℕ} {d : O} (h : Decides B r p m d)
    (hA : ∀ m' ≤ m, raw A r p m' = none) : Decides (Else A B) r p m d :=
  decides_else_iff.2 ⟨h.alive, fun m' hm' => ⟨hA m' hm'.le, h.raw_lt hm'⟩,
    Or.inr ⟨hA m le_rfl, h.raw_eq⟩⟩

/-- If `A` (or `B`) has `p` decide at time `m`, then `A else B` has `p` decide by time `m`. -/
lemma exists_decides_else_le_left {r : Run P I} {p : P} {m : ℕ} {d : O} (h : Decides A r p m d) :
    ∃ m' ≤ m, ∃ d', Decides (Else A B) r p m' d' := by
  apply exists_decides_of_raw h.alive (d := d)
  rw [raw_else, h.raw_eq]

lemma exists_decides_else_le_right {r : Run P I} {p : P} {m : ℕ} {d : O}
    (h : Decides B r p m d) : ∃ m' ≤ m, ∃ d', Decides (Else A B) r p m' d' := by
  cases hA : raw A r p m with
  | some dA => exact exists_decides_of_raw h.alive (d := dA) (by rw [raw_else, hA])
  | none => exact exists_decides_of_raw h.alive (d := d) (by rw [raw_else, hA, h.raw_eq])

/-- **Composition (proof of Theorem 3).** If `A` and `B` solve `sim(T)`, so does `A else B`; in
every run either all deciding processes decide according to `A` or all according to `B`.
The paper's proof uses, without justification, that a simultaneous protocol that has some process
decide at time `k` has *every process alive at time `k`* decide then (not only the nonfaulty ones);
this is `SolvesSim.decides_of_alive`. -/
theorem else_solvesSim {T : Task P I O} {t : ℕ} (hA : SolvesSim A T t) (hB : SolvesSim B T t) :
    SolvesSim (Else A B) T t := by
  -- a decision of the composition by component `X` at time `m` forces every process alive at
  -- time `m` to decide by `m` in the composition
  have key : ∀ r, T.IsRun t r → ∀ p q m d, Decides (Else A B) r p m d → r.Alive q m →
      ∃ m' ≤ m, ∃ d', Decides (Else A B) r q m' d' := by
    intro r hr p q m d hp hq
    rcases hp.else_cases with hpA | ⟨-, hpB⟩
    · obtain ⟨d', hd'⟩ := hA.decides_of_alive hr hpA hq
      exact exists_decides_else_le_left hd'
    · obtain ⟨d', hd'⟩ := hB.decides_of_alive hr hpB hq
      exact exists_decides_else_le_right hd'
  have hsim : ∀ r, T.IsRun t r → ∀ p q m m' d d', Decides (Else A B) r p m d →
      Decides (Else A B) r q m' d' → m = m' := by
    intro r hr p q m m' d d' hp hq
    rcases le_total m m' with hle | hle
    · obtain ⟨m'', hm'', d'', h''⟩ := key r hr p q m d hp (hq.alive.mono hle)
      have := (Decides.unique hq h'').1; omega
    · obtain ⟨m'', hm'', d'', h''⟩ := key r hr q p m' d' hq (hp.alive.mono hle)
      have := (Decides.unique hp h'').1; omega
  refine { complete := ?_, correct := ?_, simultaneous := hsim }
  · intro r hr p hp
    obtain ⟨m, d, hd⟩ := hA.complete r hr p hp
    obtain ⟨m', -, d', h'⟩ := exists_decides_else_le_left (B := B) hd
    exact ⟨m', d', h'⟩
  · intro r hr
    obtain ⟨oA, hoA, hdA⟩ := hA.correct r hr
    obtain ⟨oB, hoB, hdB⟩ := hB.correct r hr
    by_cases hex : ∃ p m d, Decides (Else A B) r p m d ∧ raw A r p m = some d
    · -- some process decides according to `A`: all do
      obtain ⟨p, m, d, hp, hpA⟩ := hex
      have hpA' : Decides A r p m d := by
        rcases hp.else_cases with h | ⟨h, -⟩
        · exact h
        · rw [h] at hpA; simp at hpA
      refine ⟨oA, hoA, fun q m' d' hq => ?_⟩
      have hm := hsim r hr p q m m' d d' hp hq
      subst hm
      obtain ⟨dq, hdq⟩ := hA.decides_of_alive hr hpA' hq.alive
      rcases hq.else_cases with h | ⟨h, -⟩
      · exact hdA q m d' h
      · rw [hdq.raw_eq] at h; simp at h
    · push Not at hex
      refine ⟨oB, hoB, fun q m d hq => ?_⟩
      rcases hq.else_cases with h | ⟨-, h⟩
      · exact absurd h.raw_eq (hex q m d hq)
      · exact hdB q m d h

/-! ### Continuous consensus and `ConCon(A)` -/

/-- A continuous-consensus protocol for initial values: a sending function and, for each local
state, a core `core p x h : P → Option I` (a partial input vector; `core … q = some v` means
`(q, v)` is in the core). -/
structure CCProtocol (P I M : Type) where
  /-- The message `p` sends to `q` in the next round. -/
  send : P → I → History P M → P → Option M
  /-- The core of `p`'s state. -/
  core : P → I → History P M → P → Option I

namespace CCProtocol

/-- The protocol (without decisions) underlying a CC protocol. -/
def toProtocol {MC : Type} (C : CCProtocol P I MC) : Protocol P I MC Unit :=
  ⟨C.send, fun _ _ _ => none⟩

/-- `M_p[m]`: the core of `p` at time `m` of the run `r`. -/
noncomputable def coreAt {MC : Type} (C : CCProtocol P I MC) (r : Run P I) (p : P) (m : ℕ) :
    P → Option I :=
  C.core p (r.input p) (hist C.toProtocol r m p)

end CCProtocol

/-- The properties of the ConCon protocol of Mizrahi–Moses that the paper uses (§2.3), for runs
with at most `t` crashes and inputs in `T.inputs`:
* accuracy: the core only contains actual input values;
* consistency: processes alive at time `m` have the same core;
* (ii) the core is empty before time `t + 1 − W(F)`;
* (i) at time `t + 1 − W(F)` the core contains the input values of all active processes.
The maximality property of ConCon (iii) is not needed for Theorems 2–8. -/
structure IsConCon {MC : Type} (C : CCProtocol P I MC) (T : Task P I O) (t : ℕ) : Prop where
  accurate : ∀ r, T.IsRun t r → ∀ p m q v, r.Alive p m → C.coreAt r p m q = some v →
    r.input q = v
  consistent : ∀ r, T.IsRun t r → ∀ p q m, r.Alive p m → r.Alive q m →
    C.coreAt r p m = C.coreAt r q m
  empty : ∀ r, T.IsRun t r → ∀ p m, r.Alive p m → m + r.waste < t + 1 → ∀ q,
    C.coreAt r p m q = none
  full : ∀ r, T.IsRun t r → ∀ p q, r.Alive p (t + 1 - r.waste) → r.Alive q (t + 1 - r.waste) →
    C.coreAt r p (t + 1 - r.waste) q = some (r.input q)

/-- The simulated failure pattern: the processes outside the core crash in round 1 and send
nothing. -/
def silentCrash (c : P → Option I) (q : P) : Option ℕ := if c q = none then some 1 else none

/-- The run `A[ı', F_c]` simulated in `ConCon(A)`: inputs `ı'`, the processes outside the core `c`
are silent from the outset. -/
def simRun (c : P → Option I) (ι : P → I) : Run P I := ⟨ι, silentCrash c, fun _ => ∅⟩

/-- An allowed input vector extending the core `c` (if any). -/
def Extends (T : Task P I O) (c : P → Option I) (ι : P → I) : Prop :=
  ι ∈ T.inputs ∧ ∀ q v, c q = some v → ι q = v

open Classical in
/-- The decision of `p` in the run `r` of `A` (if it decides). -/
noncomputable def decisionOf {M : Type} (A : Protocol P I M O) (r : Run P I) (p : P) : Option O :=
  if h : ∃ m d, Decides A r p m d then some (Classical.choose (Classical.choose_spec h)) else none

lemma decisionOf_eq {M : Type} {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} {d : O}
    (h : Decides A r p m d) : decisionOf A r p = some d := by
  have hex : ∃ m d, Decides A r p m d := ⟨m, d, h⟩
  rw [decisionOf, dif_pos hex]
  have := Classical.choose_spec (Classical.choose_spec hex)
  rw [(Decides.unique this h).2]

lemma decisionOf_spec {M : Type} {A : Protocol P I M O} {r : Run P I} {p : P} {d : O}
    (h : decisionOf A r p = some d) : ∃ m, Decides A r p m d := by
  by_cases hex : ∃ m d, Decides A r p m d
  · obtain ⟨m, d', hd⟩ := hex
    rw [decisionOf_eq hd] at h; cases h; exact ⟨m, hd⟩
  · rw [decisionOf, dif_neg hex] at h; simp at h

open Classical in
/-- The decision of `p` in the simulated run for the core `c`. -/
noncomputable def simDecision {M : Type} (A : Protocol P I M O) (T : Task P I O) (c : P → Option I)
    (p : P) : Option O :=
  if h : ∃ ι, Extends T c ι then decisionOf A (simRun c (Classical.choose h)) p else none

open Classical in
/-- `ConCon(A)` (§3): run the CC protocol `C`; once the core is nonempty, decide as `p` decides in
the simulated run of `A` in which the processes of the core are correct (with their core values)
and the other processes crash silently at the outset. -/
noncomputable def ConCon {MC M : Type} (C : CCProtocol P I MC) (A : Protocol P I M O)
    (T : Task P I O) : Protocol P I MC O where
  send := C.send
  decide p x h := if ∃ q, C.core p x h q ≠ none then simDecision A T (C.core p x h) p else none

/-- `Opt(A, k̂) = Delay(A, k̂) else ConCon(A)` (§4). -/
noncomputable def Opt {MC M : Type} (C : CCProtocol P I MC) (A : Protocol P I M O)
    (T : Task P I O) (k : ℕ) : Protocol P I (Option M × Option MC) O :=
  Else (Delay A k) (ConCon C A T)

end Podc.SimultaneousAllCaseOptimal
