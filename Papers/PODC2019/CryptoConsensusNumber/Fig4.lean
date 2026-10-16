import Mathlib

/-!
# Figure 4 (message passing): a correct process's transfer can block forever

Section 5.2, Figure 4 of the paper: the consensus-less asset-transfer algorithm on top of secure
broadcast. Lemma 3 claims that every operation of a correct process eventually completes. We show
that the pseudocode **as written** violates this, already with two correct processes, no
Byzantine process and a perfectly behaved broadcast.

The problem: a process `p` decides whether it may spend using `balance(a, hist[p] ∪ deps)`
(line 2), i.e. including the incoming transfers `deps` it has received since its last outgoing
transfer, and ships `deps` with the transfer (`h`, line 4). But the validation predicate (line 25)
checks `balance(c, hist[q]) ≥ y` **without** `h`, and incoming transfers are only ever added to
`hist[q]` (line 15) when a later transfer of `q` itself is validated. So a process that spends
money it has just received can never get its transfer validated — at any process, including
itself — and the operation never returns. Intended fix: `balance(c, hist[q] ∪ h) ≥ y`.

## Model (only what is needed for the counterexample)
* processes `Fin 2`, all correct; account of process `q` is `q` (`μ(q) = {q}`); initial balances
  `q₀` (Figure 4's `balance` omits initial balances; we add `q₀`, otherwise no transfer of a positive
  amount could ever succeed);
* secure broadcast: each process's broadcasts form a list `sent q`; process `p` delivers the
  messages of `q` one by one in that order (`dlv p q` = number delivered), each exactly once —
  integrity and source order hold by construction; agreement/validity are liveness properties and
  are irrelevant for a claim about *all* extensions;
* events: `inv p b x` (`transfer(p, b, x)` by an idle `p`, lines 1–5), `dlv p q` (`p` delivers the
  next message of `q`, lines 8–12), `val p q m` (`p` validates `(q, m) ∈ toValidate`, lines 13–20).
  Reads do not change the state and are omitted. The flag `fixed` selects line 25 as written
  (`false`) or with `hist[q] ∪ h` (`true`).
-/

namespace CryptoCons.Fig4

/-- A transfer `(c, d, y, s)`: source `c`, destination `d`, amount `y`, sequence number `s`. -/
structure Tr where
  src : Fin 2
  dst : Fin 2
  amt : ℕ
  sn : ℕ
  deriving DecidableEq

/-- A broadcast message `[t, h]`. -/
structure Msg where
  t : Tr
  h : Finset Tr
  deriving DecidableEq

/-- Local state of a process (Figure 4's local variables, plus "a transfer is pending"). -/
structure Loc where
  sq : Fin 2 → ℕ
  rc : Fin 2 → ℕ
  hist : Fin 2 → Finset Tr
  deps : Finset Tr
  toVal : Finset (Fin 2 × Msg)
  pend : Bool

/-- Global state: local states and the broadcast/delivery bookkeeping. -/
structure St where
  loc : Fin 2 → Loc
  sent : Fin 2 → List Msg
  dlv : Fin 2 → Fin 2 → ℕ

/-- Initial balances: process `0` has `5`, process `1` has `0`. -/
def q₀ : Fin 2 → ℤ := ![5, 0]

/-- `balance(a, h)`: initial balance plus incoming minus outgoing transfers in `h`. -/
def balance (a : Fin 2) (h : Finset Tr) : ℤ :=
  q₀ a + (∑ t ∈ h.filter (·.dst = a), (t.amt : ℤ)) - ∑ t ∈ h.filter (·.src = a), (t.amt : ℤ)

/-- `Valid(q, t, h)` (lines 21–26); `fixed` adds `h` in line 25. -/
def Valid (fixed : Bool) (l : Loc) (q : Fin 2) (m : Msg) : Prop :=
  q = m.t.src ∧ m.t.sn = l.sq q + 1 ∧
    (m.t.amt : ℤ) ≤ balance m.t.src (if fixed then l.hist q ∪ m.h else l.hist q) ∧
    ∀ t' ∈ m.h, t' ∈ l.hist t'.src

instance (fixed : Bool) (l : Loc) (q : Fin 2) (m : Msg) : Decidable (Valid fixed l q m) := by
  unfold Valid; infer_instance

/-- Events. -/
inductive Ev where
  | inv (p b : Fin 2) (x : ℕ)
  | dlv (p q : Fin 2)
  | val (p q : Fin 2) (m : Msg)

/-- Replace the local state of `p`. -/
def St.setLoc (S : St) (p : Fin 2) (l : Loc) : St := { S with loc := Function.update S.loc p l }

/-- `p` delivers the message of `q` (lines 9–12). -/
def onDeliver (l : Loc) (q : Fin 2) (m : Msg) : Loc :=
  if m.t.sn = l.rc q + 1 then
    { l with rc := Function.update l.rc q (l.rc q + 1), toVal := insert (q, m) l.toVal }
  else l

/-- `p` applies the validated message `m` of `q` (lines 14–20). -/
def onValid (p : Fin 2) (l : Loc) (q : Fin 2) (m : Msg) : Loc :=
  { l with
    hist := Function.update l.hist q (l.hist q ∪ m.h ∪ {m.t})
    sq := Function.update l.sq q m.t.sn
    deps := if m.t.dst = p then insert m.t l.deps else l.deps
    pend := if q = p then false else l.pend }

/-- One event (`none` if not enabled). -/
def step (fixed : Bool) (S : St) : Ev → Option St
  | .inv p b x =>
    if (S.loc p).pend then none
    else if balance p ((S.loc p).hist p ∪ (S.loc p).deps) < x then some S  -- returns `false`
    else some { (S.setLoc p { S.loc p with deps := ∅, pend := true }) with
      sent := Function.update S.sent p
        (S.sent p ++ [⟨⟨p, b, x, (S.loc p).sq p + 1⟩, (S.loc p).deps⟩]) }
  | .dlv p q =>
    match (S.sent q)[S.dlv p q]? with
    | none => none
    | some m =>
      some { (S.setLoc p (onDeliver (S.loc p) q m)) with
        dlv := Function.update S.dlv p (Function.update (S.dlv p) q (S.dlv p q + 1)) }
  | .val p q m =>
    if (q, m) ∈ (S.loc p).toVal ∧ Valid fixed (S.loc p) q m then
      some (S.setLoc p (onValid p (S.loc p) q m))
    else none

/-- Run a list of events. -/
def run (fixed : Bool) : St → List Ev → Option St
  | S, [] => some S
  | S, e :: es => (step fixed S e).bind (fun S' => run fixed S' es)

/-- The initial state. -/
def init : St where
  loc _ := ⟨fun _ => 0, fun _ => 0, fun _ => ∅, ∅, ∅, false⟩
  sent _ := []
  dlv _ _ := 0

/-- Process `0` pays `5` to process `1`; both deliver and validate it; then process `1` spends the
`5` it received, paying them back to `0`. -/
def scenario : List Ev :=
  let t₁ : Tr := ⟨0, 1, 5, 1⟩
  [.inv 0 1 5, .dlv 0 0, .val 0 0 ⟨t₁, ∅⟩, .dlv 1 0, .val 1 0 ⟨t₁, ∅⟩, .inv 1 0 5]

/-- The message broadcast by process `1`. -/
def m₂ : Msg := ⟨⟨1, 0, 5, 1⟩, {⟨0, 1, 5, 1⟩}⟩

/-- The message broadcast by process `0`. -/
def m₁ : Msg := ⟨⟨0, 1, 5, 1⟩, ∅⟩

/-- The state after the scenario (computed). -/
def S₁ (fixed : Bool) : St := ((run fixed init scenario).getD init)

lemma scenario_run (fixed : Bool) : run fixed init scenario = some (S₁ fixed) ∧
    ((S₁ fixed).loc 1).pend = true ∧ (S₁ fixed).sent 1 = [m₂] ∧ (S₁ fixed).sent 0 = [m₁] ∧
    (∀ z, ((S₁ fixed).loc z).hist 1 = ∅) ∧ (∀ z, ((S₁ fixed).loc z).toVal = {(0, m₁)}) := by
  cases fixed <;> exact ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The literal Figure 4: process `1`'s transfer never completes -/

/-- The invariant: `1` is pending with its only broadcast `m₂`, nobody has a transfer in
`hist[1]`, and every message awaiting validation was broadcast by its claimed sender. -/
def J (S : St) : Prop :=
  (S.loc 1).pend = true ∧ S.sent 1 = [m₂] ∧ (∀ z, (S.loc z).hist 1 = ∅) ∧
    ∀ z q m, (q, m) ∈ (S.loc z).toVal → m ∈ S.sent q

lemma setLoc_loc (S : St) (p z : Fin 2) (l : Loc) :
    (S.setLoc p l).loc z = if z = p then l else S.loc z := by
  by_cases h : z = p
  · subst h; simp [St.setLoc]
  · simp [St.setLoc, h]

lemma J_step {S S' : St} {e : Ev} (hJ : J S) (h : step false S e = some S') : J S' := by
  obtain ⟨hpend, hsent, hhist, htv⟩ := hJ
  cases e with
  | inv p b x =>
    simp only [step] at h
    split_ifs at h with h1 h2
    · cases h; exact ⟨hpend, hsent, hhist, htv⟩
    · cases h
      have hp : p ≠ 1 := by rintro rfl; simp [hpend] at h1
      have hp0 : p = 0 := by fin_cases p <;> simp_all
      subst hp0
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [setLoc_loc, hpend]
      · simp [hsent]
      · intro z; rw [setLoc_loc]; split_ifs <;> simp [hhist]
      · intro z q m hm
        rw [setLoc_loc] at hm
        have : m ∈ S.sent q := by
          split_ifs at hm with hz
          · subst hz; exact htv 0 q m hm
          · exact htv z q m hm
        by_cases hq : q = 0
        · subst hq; simp [this]
        · simp [Function.update, hq, this]
  | dlv p q =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i m hm
      cases h
      have hmq : m ∈ S.sent q := List.mem_of_getElem? hm
      refine ⟨?_, hsent, ?_, ?_⟩
      · rw [setLoc_loc]; split_ifs with hz
        · subst hz; unfold onDeliver; split_ifs <;> exact hpend
        · exact hpend
      · intro z; rw [setLoc_loc]; split_ifs with hz
        · subst hz; unfold onDeliver; split_ifs <;> exact hhist z
        · exact hhist z
      · intro z q' m' hm'
        rw [setLoc_loc] at hm'
        split_ifs at hm' with hz
        · subst hz
          unfold onDeliver at hm'
          split_ifs at hm'
          · simp only [Finset.mem_insert, Prod.mk.injEq] at hm'
            rcases hm' with ⟨rfl, rfl⟩ | hm'
            · exact hmq
            · exact htv z q' m' hm'
          · exact htv z q' m' hm'
        · exact htv z q' m' hm'
  | val p q m =>
    simp only [step] at h
    split_ifs at h with h1
    cases h
    obtain ⟨hmem, hsrc, -, hbal, -⟩ := h1
    have hq : q = 0 := by
      by_contra hq
      have hq1 : q = 1 := by fin_cases q <;> simp_all
      subst hq1
      have hm : m = m₂ := by simpa [hsent] using htv p 1 m hmem
      subst hm
      simp [hhist, balance, q₀, m₂] at hbal
    subst hq
    refine ⟨?_, hsent, ?_, ?_⟩
    · rw [setLoc_loc]; split_ifs with hz
      · subst hz; simp [onValid, hpend]
      · exact hpend
    · intro z; rw [setLoc_loc]; split_ifs with hz
      · subst hz; simp [onValid, Function.update, hhist]
      · exact hhist z
    · intro z q' m' hm'
      rw [setLoc_loc] at hm'
      split_ifs at hm' with hz
      · subst hz; exact htv _ q' m' hm'
      · exact htv z q' m' hm'

lemma J_run {S S' : St} (hJ : J S) (es : List Ev) (h : run false S es = some S') : J S' := by
  induction es generalizing S with
  | nil => simp only [run, Option.some.injEq] at h; subst h; exact hJ
  | cons e es ih =>
    simp only [run] at h
    cases hs : step false S e with
    | none => simp [hs] at h
    | some S'' => rw [hs] at h; exact ih (J_step hJ hs) h

/-- **Lemma 3 is false for the literal Figure 4.** There is a finite execution with two correct
processes after which process `1` has a pending `transfer` (it spends the `5` it has just
received from process `0`), and in **every** extension that transfer is still pending: it is
never validated, at any process, so `transfer` never returns. -/
theorem lemma_3_false : ∃ S, run false init scenario = some S ∧ (S.loc 1).pend = true ∧
    ∀ es S', run false S es = some S' → (S'.loc 1).pend = true := by
  obtain ⟨hrun, hpend, hs1, -, hhist, htv⟩ := scenario_run false
  refine ⟨S₁ false, hrun, hpend, fun es S' h => (J_run ?_ es h).1⟩
  refine ⟨hpend, hs1, hhist, fun z q m hm => ?_⟩
  rw [htv z] at hm
  simp only [Finset.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  rw [(scenario_run false).2.2.2.1]; simp

/-- With the intended line 25 (`balance(c, hist[q] ∪ h) ≥ y`), the same transfer completes as
soon as process `1` delivers and validates its own message. -/
theorem fixed_completes : ∃ S', run true (S₁ true) [.dlv 1 1, .val 1 1 m₂] = some S' ∧
    (S'.loc 1).pend = false :=
  ⟨_, rfl, by decide⟩

end CryptoCons.Fig4
