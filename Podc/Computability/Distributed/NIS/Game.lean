import Podc.Computability.Distributed.NIS.Model

-- CSLib candidate: Cslib/Computability/Distributed/NIS/Game.lean (staged by Papers/PODC2021/ExtensionBasedReductions)
/-!
# (Augmented) extension-based proofs: the prover–protocol game

Brusse–Ellen, PODC 2021, Section 4 (following Alistarh, Aspnes, Ellen, Gelashvili, Zhu).

The interaction proceeds in phases. In phase `φ` the prover has reached
* all configurations `C₀' α(φ)`, where `C₀'` is an initial configuration in which every process
  appearing in `α(φ)` has the same input as in the configuration chosen at the end of the previous
  phase (`GState.base`); since a configuration determines the states of the processes that took a step,
  these are exactly the configurations `reinit base u`;
* the responses to its queries in this phase (`GState.resp`).

Moves:
* `query C q` (`C` reached, `q` active in `C`): the protocol answers with `C q` and the outputs of all
  processes in `C q` (a full-information configuration is given by the states and the values of the
  decision function on them);
* `oracle C o`: an output query (extension-based proofs) or an assignment query (augmented proofs),
  described by an `OracleSpec`;
* `endPhase C` (`C` reached in this phase by a query, i.e. `C = C₀ α(φ) β` with `β ≠ []`).

The prover wins an (infinite) play if all its moves are legal and
* (W1) it reaches a configuration whose outputs violate the task specification, or
* (W2) there are infinitely many phases, or
* (W3) from some point on, every move is a query from the configuration returned by the previous
  query (an infinite chain of queries).

Since a phase may contain only finitely many chains and finitely many output/assignment queries, an
infinite last phase that is not eventually a single chain is a loss for the prover. A task has an
(augmented) extension-based impossibility proof if some prover wins against every protocol.
-/

namespace Cslib.NIS

variable {P X Y Q O : Type} [DecidableEq P]

/-- Extra query types: when a query is legal and which answers are correct. -/
structure OracleSpec (P X Y Q O : Type) where
  legal : Config P X → Q → Prop
  valid : Protocol P X Y → Config P X → Q → O → Prop

/-- Moves of the prover. -/
inductive Move (P X Q : Type) where
  | query (C : Config P X) (q : P)
  | oracle (C : Config P X) (o : Q)
  | endPhase (C : Config P X)

/-- Responses of the protocol. -/
inductive Resp (P X Y O : Type) where
  | config (C : Config P X) (out : P → Option Y)
  | answer (a : O)
  | ack

/-- What the prover has reached: the base configuration of the phase and the query responses. -/
structure GState (P X : Type) where
  base : Config P X
  resp : Set (Config P X)

namespace GState

/-- The configurations reached in the current phase. -/
def Reached (gs : GState P X) (C : Config P X) : Prop :=
  (∃ u, C = reinit gs.base u) ∨ C ∈ gs.resp

/-- The game state after a move (it does not depend on the protocol). -/
def next (gs : GState P X) : Move P X Q → GState P X
  | .query C q => ⟨gs.base, insert (step C q) gs.resp⟩
  | .oracle _ _ => gs
  | .endPhase C => ⟨C, ∅⟩

/-- At the start the prover has reached the initial configurations. -/
def start [Inhabited X] : GState P X := ⟨initC default, ∅⟩

end GState

variable (spec : OracleSpec P X Y Q O)

/-- Legal moves. -/
def Legal (δ : Protocol P X Y) (gs : GState P X) : Move P X Q → Prop
  | .query C q => gs.Reached C ∧ Active δ C q
  | .oracle C o => gs.Reached C ∧ spec.legal C o
  | .endPhase C => C ∈ gs.resp

/-- Correct responses. -/
def ValidResp (δ : Protocol P X Y) : Move P X Q → Resp P X Y O → Prop
  | .query C q, r => r = .config (step C q) (outs δ (step C q))
  | .oracle C o, r => ∃ a, r = .answer a ∧ spec.valid δ C o a
  | .endPhase _, r => r = .ack

/-- A prover strategy: the next move as a function of the history. -/
abbrev Prover (P X Y Q O : Type) := List (Move P X Q × Resp P X Y O) → Move P X Q

/-- The first `k` entries of a sequence. -/
def hist {α : Type} (pl : ℕ → α) (k : ℕ) : List α := (List.range k).map pl

lemma hist_succ {α : Type} (pl : ℕ → α) (k : ℕ) : hist pl (k + 1) = hist pl k ++ [pl k] := by
  simp [hist, List.range_succ]

@[simp] lemma hist_zero {α : Type} (pl : ℕ → α) : hist pl 0 = [] := rfl

@[simp] lemma length_hist {α : Type} (pl : ℕ → α) (k : ℕ) : (hist pl k).length = k := by simp [hist]

/-- The game states along a play. -/
def states [Inhabited X] (pl : ℕ → Move P X Q × Resp P X Y O) : ℕ → GState P X
  | 0 => GState.start
  | k + 1 => (states pl k).next (pl k).1

/-- `m'` is a query from the configuration returned by the query `m`. -/
def ChainLink (m m' : Move P X Q) : Prop :=
  ∃ C q q', m = .query C q ∧ m' = .query (step C q) q'

/-- `m` ends a phase. -/
def IsEnd (m : Move P X Q) : Prop := ∃ C, m = .endPhase C

/-- The prover wins the play. -/
def Wins [Inhabited X] (T : Task P X Y) (δ : Protocol P X Y)
    (pl : ℕ → Move P X Q × Resp P X Y O) : Prop :=
  (∀ k, Legal spec δ (states pl k) (pl k).1) ∧
  ((∃ k C, (states pl k).Reached C ∧ Violates T δ C) ∨
   (∀ N, ∃ k ≥ N, IsEnd (pl k).1) ∨
   (∃ K, ∀ k ≥ K, ChainLink (pl k).1 (pl (k + 1)).1))

/-- The play follows the strategy. -/
def Consistent (σ : Prover P X Y Q O) (pl : ℕ → Move P X Q × Resp P X Y O) : Prop :=
  ∀ k, (pl k).1 = σ (hist pl k)

/-- The protocol answers every move correctly. -/
def ValidPlay (δ : Protocol P X Y) (pl : ℕ → Move P X Q × Resp P X Y O) : Prop :=
  ∀ k, ValidResp spec δ (pl k).1 (pl k).2

/-- The prover `σ` wins against the protocol `δ` (whatever correct answers the protocol chooses). -/
def ProverWins [Inhabited X] (σ : Prover P X Y Q O) (T : Task P X Y) (δ : Protocol P X Y) : Prop :=
  ∀ pl, Consistent σ pl → ValidPlay spec δ pl → Wins spec T δ pl

/-- An impossibility proof in the game `spec`: a prover that wins against every protocol. -/
def HasProof [Inhabited X] (T : Task P X Y) : Prop :=
  ∃ σ : Prover P X Y Q O, ∀ δ, ProverWins spec σ T δ

/-- A `Ps`-only schedule from `C` reaching a configuration with property `φ`. -/
def GoodSched (δ : Protocol P X Y) (C : Config P X) (Ps : Finset P) (φ : Config P X → Prop)
    (μ : List P) : Prop :=
  (∀ p ∈ μ, p ∈ Ps) ∧ IsSched δ C μ ∧ φ (exec C μ)

/-- Correct answer to "is there a `Ps`-only schedule from `C` reaching `φ`?": such a schedule, or
`none` if there is none. -/
def ExAnswer (δ : Protocol P X Y) (C : Config P X) (Ps : Finset P) (φ : Config P X → Prop) :
    Option (List P) → Prop
  | some μ => GoodSched δ C Ps φ μ
  | none => ¬ ∃ μ, GoodSched δ C Ps φ μ

/-- Output queries `(C, P, y)` of extension-based proofs: is there a `P`-only schedule from `C` in
which some process in `P` outputs `y`? -/
def outputSpec : OracleSpec P X Y (Finset P × Y) (Option (List P)) where
  legal _ _ := True
  valid δ C o a := ExAnswer δ C o.1 (fun D => ∃ p ∈ o.1, outs δ D p = some o.2) a

/-- `D` satisfies the assignment `f` (defined on `{q | f q ≠ none}`). -/
def Satisfies (δ : Protocol P X Y) (D : Config P X) (f : P → Option Y) : Prop :=
  ∀ q y, f q = some y → outs δ D q = some y

/-- Assignment queries `(C, P, f)` of augmented extension-based proofs, `f` an assignment of outputs to
a set `Q ⊆ P` of processes: is there a `P`-only schedule from `C` to a configuration in which every
`q ∈ Q` is terminated with output `f q`? -/
def assignSpec : OracleSpec P X Y (Finset P × (P → Option Y)) (Option (List P)) where
  legal _ o := ∀ q, (o.2 q).isSome → q ∈ o.1
  valid δ C o a := ExAnswer δ C o.1 (fun D => Satisfies δ D o.2) a

/-- `T` has an extension-based impossibility proof (in the NIS model). -/
def HasEBProof [Inhabited X] (T : Task P X Y) : Prop := HasProof (outputSpec (P := P)) T

/-- `T` has an augmented extension-based impossibility proof (in the NIS model). -/
def HasAugEBProof [Inhabited X] (T : Task P X Y) : Prop := HasProof (assignSpec (P := P)) T

/-! ## Basic facts about the game -/

section Facts
variable {spec} {δ : Protocol P X Y}

/-- Invariant of the game states along legal plays: the base is reachable, and every response is
reached from a configuration `reinit base u` by a non-empty schedule. -/
def GInv (δ : Protocol P X Y) (gs : GState P X) : Prop :=
  Reach δ gs.base ∧ ∀ C ∈ gs.resp, ∃ u α, α ≠ [] ∧ IsSched δ (reinit gs.base u) α ∧
    C = exec (reinit gs.base u) α

lemma GInv.reached {gs : GState P X} (hg : GInv δ gs) {C : Config P X} (hC : gs.Reached C) :
    ∃ u α, IsSched δ (reinit gs.base u) α ∧ C = exec (reinit gs.base u) α := by
  rcases hC with ⟨u, rfl⟩ | hC
  · exact ⟨u, [], trivial, rfl⟩
  · obtain ⟨u, α, -, h1, h2⟩ := hg.2 C hC; exact ⟨u, α, h1, h2⟩

lemma GInv.reach {gs : GState P X} (hg : GInv δ gs) {C : Config P X} (hC : gs.Reached C) :
    Reach δ C := by
  obtain ⟨u, α, h1, rfl⟩ := hg.reached hC
  exact (reach_reinit hg.1 u).run h1

lemma GInv.next {gs : GState P X} (hg : GInv δ gs) {m : Move P X Q} (hm : Legal spec δ gs m) :
    GInv δ (gs.next m) := by
  cases m with
  | query C q =>
    obtain ⟨hC, hq⟩ := hm
    refine ⟨hg.1, fun D hD => ?_⟩
    rcases hD with rfl | hD
    · obtain ⟨u, α, h1, rfl⟩ := hg.reached hC
      refine ⟨u, α ++ [q], by simp, (isSched_concat _ _ _).2 ⟨h1, hq⟩, ?_⟩
      rw [exec_append]; rfl
    · exact hg.2 D hD
  | oracle C o => exact hg
  | endPhase C =>
    refine ⟨hg.reach (Or.inr hm), fun D hD => ?_⟩
    simp [GState.next] at hD

lemma GInv.start [Inhabited X] : GInv δ (GState.start : GState P X) :=
  ⟨reach_initC _, fun C hC => by simp [GState.start] at hC⟩

lemma ginv_states [Inhabited X] {pl : ℕ → Move P X Q × Resp P X Y O}
    (hl : ∀ k, Legal spec δ (states pl k) (pl k).1) (k : ℕ) : GInv δ (states pl k) := by
  induction k with
  | zero => exact GInv.start
  | succ k ih => exact ih.next (hl k)

lemma measure_lt_of_mem_resp [Fintype P] {gs : GState P X} (hg : GInv δ gs) {C : Config P X}
    (hC : C ∈ gs.resp) : totalDepth gs.base < totalDepth C := by
  obtain ⟨u, α, hα, -, rfl⟩ := hg.2 C hC
  rw [measure_exec, measure_reinit]
  have := List.length_pos_of_ne_nil hα
  omega

end Facts

end Cslib.NIS
