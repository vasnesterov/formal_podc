import Papers.PODC2018.BeepingLeaderElection.Words

/-!
# Algorithm 1: the information diffusion algorithm, phase level (Section 3.1.1)

A *diffusion phase* consists of a communication phase, after which every node knows the set of
`(prefix, suspicious)` pairs of its neighbours (neither the senders nor the multiplicities), followed by
an update of `prefix`, `suspicious` and `candidate` by rules 1–5, in order of priority:

1. if a suspicious neighbour `u` has `prefix_u` a proper prefix of `prefix_v`, remove
   `min(|prefix_v| - |prefix_u|, 3)` letters from the end of `prefix_v`;
2. if `prefix_v = z‖0‖w` with `w ≠ ε` and a neighbour has `prefix_u = z‖1‖y`, delete `|w|` letters;
3. if `prefix_v = z‖0` and a neighbour has `prefix_u = z‖1‖y`, change `prefix_v` to `z‖1`;
4. if a neighbour has `prefix_u = prefix_v‖1‖w`, append `1`;
5. if a neighbour has `prefix_u = prefix_v‖0‖w`, append `0`.

If a rule fires the node becomes a follower (`candidate := false`) and it is suspicious in the next
phase iff it removed letters (rules 1, 2). Otherwise a candidate appends the next bit of its own
`α(id)` (if `prefix` is a proper prefix of it).

When several neighbours trigger rule 1 (or rule 2) we delete the largest amount, as in
[Casteigts et al., rule R1]. The paper evaluates rule 1 *before* rule 2 (`Priority.paper`), whereas
[Casteigts et al.] apply whichever of R1.1/R1.2 deletes more letters (`Priority.maxDelete`); the
printed priority breaks Lemma 1 (see `Counterexample.lean`), the second one is our repair.

`run pr G ident t v` is the state of node `v` after `t` diffusion phases.
-/

namespace Podc.BeepingLeaderElection

/-- How rules 1 and 2 are combined. -/
inductive Priority
  /-- The paper: rule 1 has priority over rule 2. -/
  | paper
  /-- [Casteigts et al.]: among rules 1 and 2, delete the largest number of letters. -/
  | maxDelete
  deriving DecidableEq, Repr

/-- Local state of a node (the outputs `leader`, `leaderId` are functions of it, see `leader`). -/
structure NState where
  /-- The variable `prefix` (called `Z` in [Casteigts et al.]). -/
  pre : Word
  /-- The variable `suspicious`: the node removed letters in the last phase. -/
  susp : Bool
  /-- The variable `candidate`. -/
  cand : Bool
  deriving DecidableEq, Repr

/-- Initial state: `prefix = ε`, `suspicious = false`, `candidate = true`. -/
def NState.init : NState := ⟨[], false, true⟩

/-- Length of the longest common prefix. -/
def lcpLen : Word → Word → ℕ
  | a :: x, b :: y => if a = b then lcpLen x y + 1 else 0
  | _, _ => 0

/-- `x` *branches low* w.r.t. `y`: at the first position where they differ, `x` has `0` and `y`
has `1` (so `x = z‖0‖w` and `y = z‖1‖y'`). -/
def branchLow (x y : Word) : Bool :=
  x[lcpLen x y]? == some false && y[lcpLen x y]? == some true

/-- Number of letters rule 1 deletes from `x` because of a received pair `m`. -/
def amt1 (x : Word) (m : Word × Bool) : ℕ :=
  if m.2 = true ∧ m.1 <+: x ∧ m.1.length < x.length then min (x.length - m.1.length) 3 else 0

/-- Number of letters rule 2 deletes from `x` because of a received word `y`
(`x = z‖0‖w`, `y = z‖1‖y'`: delete `|w|`). `0` if rule 2 is not triggered. -/
def amt2 (x y : Word) : ℕ :=
  if branchLow x y then x.length - lcpLen x y - 1 else 0

/-- Rule 3 is triggered by `y`: `x = z‖0` and `y = z‖1‖y'`. -/
def chgBy (x y : Word) : Bool :=
  branchLow x y && (lcpLen x y + 1 == x.length)

/-- The amount deleted by rules 1–2 on the set `R` of received pairs (`0`: no deletion). -/
def delAmount (pr : Priority) (x : Word) (R : Finset (Word × Bool)) : ℕ :=
  let d1 := R.sup (amt1 x)
  let d2 := R.sup (fun m => amt2 x m.1)
  match pr with
  | .paper => if 0 < d1 then d1 else d2
  | .maxDelete => max d1 d2

/-- One local update (line 8 of Algorithm 1): node with own α-word `Y`, state `s`, received set `R`. -/
def ruleStep (pr : Priority) (Y : Word) (s : NState) (R : Finset (Word × Bool)) : NState :=
  let x := s.pre
  let d := delAmount pr x R
  if 0 < d then ⟨x.take (x.length - d), true, false⟩
  else if ∃ m ∈ R, chgBy x m.1 = true then ⟨x.dropLast ++ [true], false, false⟩
  else if ∃ m ∈ R, x ++ [true] <+: m.1 then ⟨x ++ [true], false, false⟩
  else if ∃ m ∈ R, x ++ [false] <+: m.1 then ⟨x ++ [false], false, false⟩
  else if s.cand = true ∧ x.length < Y.length then ⟨x ++ [Y.getD x.length false], false, true⟩
  else ⟨x, false, s.cand⟩

section Network

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The set of `(prefix, suspicious)` pairs received by `v` in a communication phase. -/
def received (C : V → NState) (v : V) : Finset (Word × Bool) :=
  (Finset.univ.filter (G.Adj v)).image fun u => ((C u).pre, (C u).susp)

/-- One diffusion phase of the whole network. -/
def phase (pr : Priority) (ident : V → ℕ) (C : V → NState) : V → NState :=
  fun v => ruleStep pr (alpha (ident v)) (C v) (received G C v)

/-- The execution of Algorithm 1 (phase level): `run pr G ident t` is the configuration after `t`
diffusion phases. -/
def run (pr : Priority) (ident : V → ℕ) : ℕ → V → NState
  | 0 => fun _ => NState.init
  | t + 1 => phase G pr ident (run pr ident t)

/-- Output `leader` of node `v` (lines 9–10): a candidate whose prefix is its own α-id. -/
def leader (ident : V → ℕ) (C : V → NState) (v : V) : Prop :=
  (C v).cand = true ∧ (C v).pre = alpha (ident v)

end Network

/-- The relation of Lemma 1 for two words with `|x| ≤ |y|`: `x` and `y` are identical except in at
most 6 least significant bits, from the `|x|`-th bit (possibly included) to the `|y|`-th bit; and if
the `|x|`-th bit differs, then `|y| - |x| < 6`. -/
def Lemma1Rel (x y : Word) : Prop :=
  x.dropLast <+: y ∧ y.length ≤ x.length + 6 ∧ (¬ x <+: y → y.length < x.length + 6)

instance (x y : Word) : Decidable (Lemma1Rel x y) := by unfold Lemma1Rel; infer_instance

/-- The conclusion of Lemma 1 for the prefixes `x`, `y` of two neighbours (without loss of generality
`|x| ≤ |y|`). -/
def Lemma1Holds (x y : Word) : Prop :=
  (x.length ≤ y.length → Lemma1Rel x y) ∧ (y.length ≤ x.length → Lemma1Rel y x)

instance (x y : Word) : Decidable (Lemma1Holds x y) := by unfold Lemma1Holds; infer_instance

end Podc.BeepingLeaderElection
