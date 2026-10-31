import Podc.Computability.Distributed.PopulationProtocols.Multiset.Basic
import Cslib.Computability.Distributed.PopulationProtocols.Basic

/-!
# Four-state exact majority protocols: the model of Appendix B (Theorem B.1)

The four states are `S0`, `S1` (the initial states for inputs `B`, `A`; the paper's `S0`, `S1`)
and `X`, `Y`. A protocol is a CSLib deterministic protocol `P : Protocol Q4`
(`δ p q = (p', q')`, Section 2 of the paper). Agents are anonymous, so we work with configurations
as multisets of states (`Multiset Q4`); a step fires `P.δ p q` on two agents in states `p`, `q`
(either can be the initiator). This is the Podc multiset model (`MStep`) for the transition set
`trans P`.

The output map is `γ : Q4 → Bool` (`false` = output `0`, `true` = output `1`); `S i` is the
initial state for output `i` (`S false = S0`, `S true = S1`), and `cfg i a b` is the initial
configuration with `a` agents in `S i` and `b` agents in `S (!i)`.

The three correctness properties of Theorem B.1 (`Correct`), for every population size:
* `nonempty`: for each output `i` and each `n ≥ 1`, the set `C_i` of absorbing configurations of
  size `n` (every reachable configuration has all outputs equal to `i`) is non-empty;
* `safe`: from an initial configuration with a majority of `S i`, no configuration of
  `C_{1-i}` is reachable;
* `live`: from every configuration reachable from an initial configuration with a majority of
  `S i`, some configuration of `C_i` is reachable.

The proof of Theorem B.1 treats interactions as *unordered* ("`[S0, X]` is the same as
`[X, S0]`", Appendix B); we make this explicit as the hypothesis `Symmetric P`: both orientations
of a pair produce the same multiset of states.
-/

namespace Podc.ExactMajorityAVC.Four

-- CSLib candidate (tactic)
/-- Prove an equality of multisets by comparing all counts. -/
macro "ms_eq" : tactic => `(tactic| (
  ext a
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_add,
    Multiset.count_replicate, Multiset.count_singleton, Multiset.count_zero]
  all_goals (split_ifs <;> subst_vars <;> (try simp_all) <;> omega)))

open Cslib.PopulationProtocol

/-- The four states. -/
inductive Q4
  | S0
  | S1
  | X
  | Y
  deriving DecidableEq, Repr

open Q4

instance : Fintype Q4 := ⟨{S0, S1, X, Y}, fun x => by cases x <;> simp⟩

/-- The initial state for output `i`. -/
def S : Bool → Q4
  | false => S0
  | true => S1

@[simp] lemma S_false : S false = S0 := rfl
@[simp] lemma S_true : S true = S1 := rfl

/-- The transitions of a deterministic protocol, as multiset transitions. -/
def trans (P : Protocol Q4) : Set (Transition Q4) := {t | P.δ t.p t.q = (t.p', t.q')}

/-- Reachability between multiset configurations. -/
abbrev Reach (P : Protocol Q4) : Multiset Q4 → Multiset Q4 → Prop := MReach (trans P)

/-- The initial configuration with `a` agents in `S i` and `b` agents in `S (!i)`. -/
def cfg (i : Bool) (a b : ℕ) : Multiset Q4 :=
  Multiset.replicate a (S i) + Multiset.replicate b (S (!i))

/-- `c ∈ C_i`: every configuration reachable from `c` has all outputs equal to `i`. -/
def Absorbing (P : Protocol Q4) (γ : Q4 → Bool) (i : Bool) (c : Multiset Q4) : Prop :=
  ∀ c', Reach P c c' → ∀ q ∈ c', γ q = i

/-- The three correctness properties of Theorem B.1. -/
structure Correct (P : Protocol Q4) (γ : Q4 → Bool) : Prop where
  /-- For each outcome `i` and each population size `n ≥ 1`, `C_i` is non-empty. -/
  nonempty : ∀ n, 1 ≤ n → ∀ i, ∃ c : Multiset Q4, Multiset.card c = n ∧ Absorbing P γ i c
  /-- The system never converges to the wrong decision. -/
  safe : ∀ i a b, b < a → ∀ c, Reach P (cfg i a b) c → ¬ Absorbing P γ (!i) c
  /-- It is always possible to converge to the correct decision. -/
  live : ∀ i a b, b < a → ∀ c, Reach P (cfg i a b) c → ∃ c', Reach P c c' ∧ Absorbing P γ i c'

/-- The multiset `{p, q}` of a pair of states. -/
def pair (z : Q4 × Q4) : Multiset Q4 := {z.1, z.2}

/-- Interactions are unordered: both orientations give the same multiset of states. -/
def Symmetric (P : Protocol Q4) : Prop := ∀ p q, pair (P.δ q p) = pair (P.δ p q)

/-- `#S0 − #S1`. -/
def diff (c : Multiset Q4) : ℤ := (c.count S0 : ℤ) - c.count S1

/-- Every interaction preserves `#S0 − #S1` (the hypothesis of Claim B.8). -/
def Invariant (P : Protocol Q4) : Prop := ∀ p q, diff (pair (P.δ p q)) = diff {p, q}

/-! ### Basic facts about steps -/

variable {P : Protocol Q4}

lemma mem_trans (p q : Q4) : (⟨p, q, (P.δ p q).1, (P.δ p q).2⟩ : Transition Q4) ∈ trans P := rfl

/-- One interaction of two agents in states `p`, `q`. -/
lemma step_of (p q : Q4) (r : Multiset Q4) :
    MStep (trans P) (p ::ₘ q ::ₘ r) ((P.δ p q).1 ::ₘ (P.δ p q).2 ::ₘ r) := by
  refine ⟨_, mem_trans p q, ?_, ?_⟩
  · simp [Transition.pre, Multiset.insert_eq_cons]
  · have : p ::ₘ q ::ₘ r - ({p, q} : Multiset Q4) = r := by simp [Multiset.insert_eq_cons]
    simp only [Transition.pre, Transition.post]
    rw [this, add_comm]
    simp [Multiset.insert_eq_cons]

/-- Every step is the interaction of two agents. -/
lemma exists_of_step {c c' : Multiset Q4} (h : MStep (trans P) c c') :
    ∃ p q r, c = p ::ₘ q ::ₘ r ∧ c' = (P.δ p q).1 ::ₘ (P.δ p q).2 ::ₘ r := by
  obtain ⟨t, ht, hle, rfl⟩ := h
  refine ⟨t.p, t.q, c - t.pre, ?_, ?_⟩
  · have : c = t.pre + (c - t.pre) := (add_tsub_cancel_of_le hle).symm
    conv_lhs => rw [this]
    simp [Transition.pre, Multiset.insert_eq_cons]
  · have ht' : P.δ t.p t.q = (t.p', t.q') := ht
    rw [ht', add_comm]
    simp [Transition.post, Multiset.insert_eq_cons]

/-- Steps can be performed inside a larger population. -/
lemma MStep.add_right' {c c' : Multiset Q4} (h : MStep (trans P) c c') (e : Multiset Q4) :
    MStep (trans P) (c + e) (c' + e) := by
  obtain ⟨p, q, r, rfl, rfl⟩ := exists_of_step h
  simpa [Multiset.cons_add] using step_of (P := P) p q (r + e)

-- CSLib candidate (`PopulationProtocols/Multiset/Basic.lean`, for any transition set)
/-- Runs can be performed inside a larger population (the other agents stay idle). -/
lemma Reach.add_right {c c' : Multiset Q4} (h : Reach P c c') (e : Multiset Q4) :
    Reach P (c + e) (c' + e) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (MStep.add_right' hs e)

lemma Reach.add_left {c c' : Multiset Q4} (h : Reach P c c') (e : Multiset Q4) :
    Reach P (e + c) (e + c') := by
  simpa [add_comm] using h.add_right e

lemma Reach.card_eq {c c' : Multiset Q4} (h : Reach P c c') :
    Multiset.card c' = Multiset.card c := MReach.card_eq h

lemma Absorbing.mem {γ : Q4 → Bool} {i : Bool} {c : Multiset Q4} (h : Absorbing P γ i c) :
    ∀ q ∈ c, γ q = i := h c .refl

lemma Absorbing.reach {γ : Q4 → Bool} {i : Bool} {c c' : Multiset Q4} (h : Absorbing P γ i c)
    (hr : Reach P c c') : Absorbing P γ i c' := fun _ hr' => h _ (hr.trans hr')

end Podc.ExactMajorityAVC.Four
