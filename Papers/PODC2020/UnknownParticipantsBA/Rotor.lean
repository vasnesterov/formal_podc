import Papers.PODC2020.UnknownParticipantsBA.Model

/-!
# The rotor-coordinator (Algorithm 1 of the BA = Algorithm 2 of the full version)

```
 1: C_v ← ∅                                  ⊲ candidate coordinators (ordered by id)
 2: S_v ← ∅                                  ⊲ selected coordinators
 3: Broadcast init                                                     ⊲ Round 1
 4: Broadcast echo(p) if received init from p                           ⊲ Round 2
 5: for r ← 0 → ∞ do                                    ⊲ Rounds 3 up to termination
 6:   B_v ← ∅
 7:   Let n_v be the number of nodes that sent at least one message to v until round r
 8:   if received at least n_v/3 echo(p) and p ∉ C_v then B_v ← B_v ∪ {echo(p)}
11:   if received at least 2n_v/3 echo(p) and p ∉ C_v then C_v ← C_v ∪ {p}
14:   p ← C_v[r mod |C_v|]                     ⊲ select the next coordinator
15:   Let p' be the coordinator selected in the previous round
16:   if received opinion(x) from p' then accept x as the coordinator's opinion
19:   if p ∈ S_v then break
22:   S_v ← S_v ∪ {p}
23:   if v = p then B_v ← B_v ∪ {opinion(o_v)}
27:   Broadcast B_v if it is non-empty
```

The candidate-set mechanism (lines 1–13) is factored out as a *layer* (`Core`, `withRotor`) that is
shared with the consensus algorithm; the rest (lines 14–27) is an `Ext`ension. The termination
test of line 19 is a parameter `rule` of `rotorExt`: the paper's rule is `paperRule`
(`p ∈ S_v`), our repaired rule is `fixedRule` (stop once `2r > n_v`).

Indexing: the state after step `0` is the initial state (it broadcasts `init`, round 1); step `1`
receives the `init`s and broadcasts the echoes (round 2); step `r + 2` is loop iteration `r`
(round `r + 3`).
-/

namespace UnknownBA

/-- Messages: the rotor layer's `init` and `echo p`, and application messages. -/
inductive Msg (I A : Type*) where
  | init : Msg I A
  | echo (p : I) : Msg I A
  | app (a : A) : Msg I A
  deriving DecidableEq

variable {I X A T : Type*} [DecidableEq I] [DecidableEq A] [DecidableEq X]

/-- The identifier mentioned by an echo message. -/
def Msg.echoId : Msg I A → Option I
  | .echo p => some p
  | _ => none

/-- The payload of an application message. -/
def Msg.appVal : Msg I A → Option A
  | .app a => some a
  | _ => none

/-- Identifiers mentioned in echo messages of a received set. -/
def echoIds (B : Finset (I × Msg I A)) : Finset I := B.biUnion fun e => e.2.echoId.toFinset

omit [DecidableEq A] in
lemma mem_echoIds {B : Finset (I × Msg I A)} {p : I} :
    p ∈ echoIds B ↔ ∃ q, (q, Msg.echo p) ∈ B := by
  simp only [echoIds, Finset.mem_biUnion, Option.mem_toFinset]
  constructor
  · rintro ⟨⟨q, m⟩, hm, h⟩
    cases m <;> simp_all [Msg.echoId]
    exact ⟨q, hm⟩
  · rintro ⟨q, hq⟩; exact ⟨_, hq, rfl⟩

lemma echoIds_of_cnt_pos {B : Finset (I × Msg I A)} {p : I} (h : 0 < cnt B (Msg.echo p)) :
    p ∈ echoIds B := by
  rw [cnt, Finset.card_pos] at h
  obtain ⟨⟨q, m⟩, hm⟩ := h
  simp only [Finset.mem_filter] at hm
  obtain ⟨hm, rfl⟩ := hm
  exact mem_echoIds.mpr ⟨q, hm⟩

/-- The state of the candidate-set layer: nodes heard of so far (`n_v = |heard|`), candidate
coordinators `C`, and the echoes `E` to broadcast at the end of the step. -/
structure Core (I : Type*) where
  heard : Finset I
  C : Finset I
  E : Finset I

/-- Step 1 (round 2): receive the `init`s, prepare `echo(p)` for every `init` sender `p`. -/
def Core.recvInit (c : Core I) (B : Finset (I × Msg I A)) : Core I where
  heard := c.heard ∪ senders B
  C := c.C
  E := senders (B.filter fun e => e.2 = Msg.init)

/-- One loop iteration of lines 6–13. -/
def Core.update (c : Core I) (B : Finset (I × Msg I A)) : Core I :=
  let H := c.heard ∪ senders B
  { heard := H
    C := c.C ∪ (echoIds B).filter fun p => 2 * H.card ≤ 3 * cnt B (Msg.echo p)
    E := (echoIds B).filter fun p => p ∉ c.C ∧ H.card ≤ 3 * cnt B (Msg.echo p) }

/-- `selSet C r` is `{C[r mod |C|]}` (empty iff `C` is empty): the element of `C` with exactly
`r mod |C|` smaller elements. -/
def selSet [LinearOrder I] (C : Finset I) (r : ℕ) : Finset I :=
  C.filter fun x => (C.filter (· < x)).card = r % C.card

/-- An extension of the rotor layer by application logic. `step t c x B` is the application step
taken from a state with step counter `t`, where `c` is the *updated* layer state. -/
structure Ext (I X A T : Type*) where
  init : I → X → T
  halted : T → Bool
  out : T → Finset A
  step : ℕ → Core I → T → Finset (I × Msg I A) → T

/-- Full node state of a protocol built on the rotor layer. -/
structure St (I T : Type*) where
  t : ℕ
  core : Core I
  ext : T

/-- The protocol: rotor layer + extension. A halted node is frozen and silent. -/
def withRotor (Ex : Ext I X A T) : Protocol I X (Msg I A) (St I T) where
  init v x := ⟨0, ⟨∅, ∅, ∅⟩, Ex.init v x⟩
  out st := if Ex.halted st.ext then ∅ else
    ((if st.t = 0 then {Msg.init} else ∅) ∪ st.core.E.image Msg.echo) ∪
      (Ex.out st.ext).image Msg.app
  step st B := if Ex.halted st.ext then st else
    let c' := if st.t = 0 then st.core.recvInit B else st.core.update B
    ⟨st.t + 1, c', Ex.step st.t c' st.ext B⟩

omit [DecidableEq X] in
lemma withRotor_step_of_halted (Ex : Ext I X A T) {st : St I T} (h : Ex.halted st.ext = true)
    (B : Finset (I × Msg I A)) : (withRotor Ex).step st B = st := by
  simp [withRotor, h]

omit [DecidableEq X] in
/-- A halted node stays frozen forever. -/
lemma run_add_of_halted (Ex : Ext I X A T) (E : Env I X (Msg I A)) {s : ℕ} {v : I}
    (h : Ex.halted (run (withRotor Ex) E s v).ext = true) (k : ℕ) :
    run (withRotor Ex) E (s + k) v = run (withRotor Ex) E s v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, run_succ, ih, withRotor_step_of_halted _ h]

/-! ### Lines 14–27: selection, acceptance, termination -/

/-- Application state of the rotor-coordinator. -/
structure RState (I X : Type*) where
  id : I
  op : X
  /-- selected coordinators `S_v` -/
  S : Finset I
  /-- the coordinator selected in the latest iteration (`{p}`) -/
  sel : Finset I
  /-- opinions accepted in the latest iteration (from the previous coordinator `p'`) -/
  acc : Finset X
  halted : Bool
  /-- opinion to broadcast at the end of the step -/
  out : Finset X

/-- Opinions received from senders in `P`. -/
def opinionsFrom (P : Finset I) (B : Finset (I × Msg I X)) : Finset X :=
  B.biUnion fun e => if e.1 ∈ P then e.2.appVal.toFinset else ∅

/-- A termination rule: given the iteration `r`, the layer state, `S_v` and the selection
`{p}`, decide whether to `break` (line 19). -/
abbrev Rule (I : Type*) := ℕ → Core I → Finset I → Finset I → Bool

/-- The paper's rule: break when the selected coordinator was selected before (`p ∈ S_v`). -/
def paperRule : Rule I := fun _ _ S sel => decide (sel ∩ S).Nonempty

/-- Repaired rule: break at the first iteration `r` with `2r > n_v`. Since `n_v ≥ g > 2f`, no
correct node breaks before iteration `f + 1`, and every correct node breaks by iteration
`⌊n/2⌋ + 1`. -/
def fixedRule : Rule I := fun r c _ _ => decide (c.heard.card < 2 * r)

variable [LinearOrder I]

/-- Lines 14–27 with termination rule `rule`. -/
def rotorExt (rule : Rule I) : Ext I X X (RState I X) where
  init v x := ⟨v, x, ∅, ∅, ∅, false, ∅⟩
  halted st := st.halted
  out st := st.out
  step t c st B :=
    match t with
    | 0 => st
    | r + 1 =>
      let p := selSet c.C r
      let acc := opinionsFrom st.sel B
      if rule r c st.S p then { st with sel := p, acc := acc, halted := true, out := ∅ }
      else { st with S := st.S ∪ p, sel := p, acc := acc,
                     out := if st.id ∈ p then {st.op} else ∅ }

/-- Algorithm 1 of the BA with termination rule `rule`. -/
def rotor (rule : Rule I) : Protocol I X (Msg I X) (St I (RState I X)) :=
  withRotor (rotorExt rule)

variable (rule : Rule I) (E : Env I X (Msg I X))

/-- Node `v` is still running at the start of iteration `r` and selects `p` in it (line 14). -/
def Selects (v : I) (r : ℕ) (p : I) : Prop :=
  (run (rotor rule) E (r + 1) v).ext.halted = false ∧ (run (rotor rule) E (r + 2) v).ext.sel = {p}

/-- A *good round* (iteration): every correct node selects the same correct coordinator. -/
def GoodIter (r : ℕ) : Prop := ∃ p ∈ E.G, ∀ v ∈ E.G, Selects rule E v r p

/-- Node `v` executes `break` (terminates) in iteration `r`. -/
def HaltsAt (v : I) (r : ℕ) : Prop :=
  (run (rotor rule) E (r + 1) v).ext.halted = false ∧ (run (rotor rule) E (r + 2) v).ext.halted = true

/-- Node `v` is running at the start of iteration `r` and accepts opinion `x` in it (line 16). -/
def Accepts (v : I) (r : ℕ) (x : X) : Prop :=
  (run (rotor rule) E (r + 1) v).ext.halted = false ∧ x ∈ (run (rotor rule) E (r + 2) v).ext.acc

end UnknownBA
