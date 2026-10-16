import Podc.AtomicState.Digraph

/-!
# The atomic-state model (Dijkstra) on directed networks

-- CSLib candidate

Deterministic algorithms in the atomic-state (locally shared memory) model. A configuration is
`γ : V → Q`; `next γ p` is the state that `p` takes if it is activated in `γ` (each process has a
single deterministic action, enabled iff it changes the state — trivial actions are excluded, as in
the paper). Several guarded actions with pairwise exclusive guards (e.g. hierarchical collateral
compositions) are folded into one `next`.

* `Enabled`, `Terminal`.
* `IsRun next e S` : `e : ℕ → V → Q` is an execution under the **distributed unfair daemon** with
  activated sets `S t`: a nonempty set of enabled processes is activated at every non-terminal
  configuration, and a terminal configuration repeats forever. This is the paper's *infinite
  extension* `Ext∞` of a maximal execution (a finite maximal execution ends in a terminal
  configuration), so finite executions are the eventually-terminal ones.
* `IsSyncExec next e` : synchronous daemon (all enabled processes move): `e (t+1) = next (e t)`.
* Rounds: `RoundDone e S s s'` (every process enabled at `s` executes an action or is neutralized
  during `[s, s']`), `RoundBounds e S r` (`r 0 = 0` and each `[r i, r (i+1)]` contains a complete
  round), `PaperRounds e S r` (the paper's rounds: `r (i+1)` is the *least* such bound).
  Upper bounds "within `k` rounds" are stated for all `RoundBounds`, which covers `PaperRounds`.
* `SelfStab Exec SP` (Definition 1 of Altisen et al., PODC'24) and `SilentSelfStab` (Definition 2).
* `IsLocal G next` : the next state of `p` depends only on the inputs and states of `p` and its
  predecessors. Lemma 12 of the paper (`syncExec_agree`): synchronous executions agree forever on a
  predecessor-closed set on which they agree initially.
-/

namespace Podc.AtomicState

variable {V Q : Type*}

section Exec

variable (next : (V → Q) → V → Q)

/-- `p` is enabled in `γ`: its action would change its state. -/
def Enabled (γ : V → Q) (p : V) : Prop := next γ p ≠ γ p

/-- `γ` is terminal: no process is enabled. -/
def Terminal (γ : V → Q) : Prop := ∀ p, next γ p = γ p

/-- An execution under the distributed unfair daemon, with activated sets `S t` (Ext∞ form). -/
structure IsRun (e : ℕ → V → Q) (S : ℕ → Set V) : Prop where
  enabled : ∀ t p, p ∈ S t → Enabled next (e t) p
  move : ∀ t p, p ∈ S t → e (t + 1) p = next (e t) p
  stay : ∀ t p, p ∉ S t → e (t + 1) p = e t p
  progress : ∀ t, (S t).Nonempty ∨ Terminal next (e t)

/-- An execution under the distributed unfair daemon. -/
def IsExec (e : ℕ → V → Q) : Prop := ∃ S, IsRun next e S

/-- An execution under the synchronous daemon. -/
def IsSyncExec (e : ℕ → V → Q) : Prop := ∀ t, e (t + 1) = next (e t)

/-- Every process enabled at `s` executes an action or is neutralized during `[s, s']`. -/
def RoundDone (e : ℕ → V → Q) (S : ℕ → Set V) (s s' : ℕ) : Prop :=
  ∀ p, Enabled next (e s) p → ∃ u, s ≤ u ∧ u < s' ∧ (p ∈ S u ∨ ¬ Enabled next (e (u + 1)) p)

/-- `r` is a sequence of times starting at `0` such that each `[r i, r (i+1)]` contains a complete
round. In particular `r` dominates the paper's round boundaries (see `PaperRounds`). -/
def RoundBounds (e : ℕ → V → Q) (S : ℕ → Set V) (r : ℕ → ℕ) : Prop :=
  r 0 = 0 ∧ ∀ i, r i ≤ r (i + 1) ∧ RoundDone next e S (r i) (r (i + 1))

/-- The paper's rounds: `r (i+1)` is the end of the minimal prefix of the suffix starting at `r i`
in which every process enabled at `r i` executes or is neutralized. -/
def PaperRounds (e : ℕ → V → Q) (S : ℕ → Set V) (r : ℕ → ℕ) : Prop :=
  RoundBounds next e S r ∧
    ∀ i s', r i ≤ s' → RoundDone next e S (r i) s' → r (i + 1) ≤ s'

/-- Definition 1 (self-stabilization) for a class of executions `Exec` and a specification `SP`
(a predicate on executions in Ext∞ form). -/
def SelfStab (Exec : (ℕ → V → Q) → Prop) (SP : (ℕ → V → Q) → Prop) : Prop :=
  ∃ L : Set (V → Q), L.Nonempty ∧ (∀ e, Exec e → ∃ t, e t ∈ L) ∧ (∀ e, Exec e → e 0 ∈ L → SP e)

/-- Definition 2 (silent self-stabilization) for a class of executions and a predicate on
configurations: every execution is finite (reaches a terminal configuration) and every terminal
configuration satisfies `P`. -/
def SilentSelfStab (Exec : (ℕ → V → Q) → Prop) (P : (V → Q) → Prop) : Prop :=
  (∀ e, Exec e → ∃ t, Terminal next (e t)) ∧ ∀ γ, Terminal next γ → P γ

variable {next}

theorem IsRun.not_mem_of_terminal {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsRun next e S) {t : ℕ}
    (ht : Terminal next (e t)) (p : V) : p ∉ S t := fun hp => h.enabled t p hp (ht p)

theorem IsRun.succ_eq_of_terminal {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsRun next e S) {t : ℕ}
    (ht : Terminal next (e t)) : e (t + 1) = e t :=
  funext fun p => h.stay t p (h.not_mem_of_terminal ht p)

theorem IsRun.eq_of_terminal {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsRun next e S) {t : ℕ}
    (ht : Terminal next (e t)) : ∀ u, t ≤ u → e u = e t := by
  intro u hu
  induction hu with
  | refl => rfl
  | step _ ih => rw [h.succ_eq_of_terminal (ih ▸ ht), ih]

/-- The suffix of a run is a run. -/
theorem IsRun.shift {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsRun next e S) (k : ℕ) :
    IsRun next (fun t => e (k + t)) (fun t => S (k + t)) where
  enabled t p hp := h.enabled (k + t) p hp
  move t p hp := h.move (k + t) p hp
  stay t p hp := h.stay (k + t) p hp
  progress t := h.progress (k + t)

/-- If a run is eventually constant, it reaches a terminal configuration. -/
theorem IsRun.terminal_of_const {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsRun next e S) {T : ℕ}
    (hT : ∀ t, T ≤ t → e t = e T) : Terminal next (e T) := by
  rcases h.progress T with ⟨p, hp⟩ | ht
  · exact absurd (by rw [← h.move T p hp, hT (T + 1) (by omega)]) (h.enabled T p hp)
  · exact ht

/-- The activated sets of a synchronous execution. -/
def syncSet (e : ℕ → V → Q) (t : ℕ) : Set V := {p | Enabled next (e t) p}

theorem IsSyncExec.isRun {e : ℕ → V → Q} (h : IsSyncExec next e) :
    IsRun next e (syncSet (next := next) e) where
  enabled _ _ hp := hp
  move t p _ := by rw [h t]
  stay t p hp := by
    rw [h t]; simpa [syncSet, Enabled] using hp
  progress t := by
    by_cases ht : Terminal next (e t)
    · exact Or.inr ht
    · simp only [Terminal, not_forall] at ht
      exact Or.inl ht

/-- The synchronous daemon is a special case of the distributed unfair daemon. -/
theorem IsSyncExec.isExec {e : ℕ → V → Q} (h : IsSyncExec next e) : IsExec next e :=
  ⟨_, h.isRun⟩

theorem IsSyncExec.shift {e : ℕ → V → Q} (h : IsSyncExec next e) (k : ℕ) :
    IsSyncExec next (fun t => e (k + t)) := fun t => h (k + t)

theorem isSyncExec_iterate (γ : V → Q) : IsSyncExec next (fun t => next^[t] γ) := fun t => by
  simp only [Function.iterate_succ_apply']

theorem IsSyncExec.eq_iterate {e : ℕ → V → Q} (h : IsSyncExec next e) (t : ℕ) :
    e t = next^[t] (e 0) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [h t, ih, Function.iterate_succ_apply']

/-- Under the synchronous daemon, every step is a round. -/
theorem IsSyncExec.roundBounds {e : ℕ → V → Q} (_h : IsSyncExec next e) :
    RoundBounds next e (syncSet (next := next) e) id :=
  ⟨rfl, fun i => ⟨Nat.le_succ i, fun _ hp => ⟨i, le_rfl, Nat.lt_succ_self i, Or.inl hp⟩⟩⟩

theorem RoundDone.mono_right {e : ℕ → V → Q} {S : ℕ → Set V} {s s' s'' : ℕ}
    (h : RoundDone next e S s s') (hs : s' ≤ s'') : RoundDone next e S s s'' := fun p hp =>
  let ⟨u, h1, h2, h3⟩ := h p hp; ⟨u, h1, by omega, h3⟩

theorem RoundBounds.mono {e : ℕ → V → Q} {S : ℕ → Set V} {r : ℕ → ℕ}
    (h : RoundBounds next e S r) : Monotone r :=
  monotone_nat_of_le_succ fun i => (h.2 i).1

/-- Paper rounds are round bounds. -/
theorem PaperRounds.roundBounds {e : ℕ → V → Q} {S : ℕ → Set V} {r : ℕ → ℕ}
    (h : PaperRounds next e S r) : RoundBounds next e S r := h.1

/-- In an eventually terminal run, the paper's round boundaries exist. -/
theorem IsRun.exists_paperRounds {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsRun next e S) {T : ℕ}
    (hT : Terminal next (e T)) : ∃ r, PaperRounds next e S r := by
  classical
  have hex : ∀ s, ∃ s', s ≤ s' ∧ RoundDone next e S s s' := by
    intro s
    refine ⟨max s T + 1, by omega, fun p _ => ⟨max s T, le_max_left _ _, by omega, Or.inr ?_⟩⟩
    have := h.eq_of_terminal hT (max s T + 1) (by omega)
    rw [this]; exact fun hp => hp (hT p)
  let f : ℕ → ℕ := fun s => Nat.find (hex s)
  let r : ℕ → ℕ := fun i => f^[i] 0
  refine ⟨r, ⟨rfl, fun i => ?_⟩, fun i s' hs' hd => ?_⟩
  · have := Nat.find_spec (hex (r i))
    simp only [r, Function.iterate_succ_apply']
    exact this
  · simp only [r, Function.iterate_succ_apply']
    exact Nat.find_min' (hex _) ⟨hs', hd⟩

/-- A silent self-stabilizing algorithm (with at least one configuration) is self-stabilizing for
any specification that holds on all executions starting in a terminal configuration satisfying
`P`, the legitimate configurations being the terminal ones. Executions must be suffix-closed and
exist from every configuration (true for both daemons). -/
theorem SilentSelfStab.selfStab [Nonempty (V → Q)] {Exec : (ℕ → V → Q) → Prop}
    {P : (V → Q) → Prop} {SP : (ℕ → V → Q) → Prop} (h : SilentSelfStab next Exec P)
    (hex : ∀ γ, ∃ e, Exec e ∧ e 0 = γ)
    (hSP : ∀ e, Exec e → Terminal next (e 0) → P (e 0) → SP e) : SelfStab Exec SP := by
  refine ⟨{γ | Terminal next γ}, ?_, h.1, fun e he h0 => hSP e he h0 (h.2 _ h0)⟩
  obtain ⟨e, he, -⟩ := hex (Classical.arbitrary _)
  obtain ⟨t, ht⟩ := h.1 e he
  exact ⟨_, ht⟩

theorem SilentSelfStab.mono {Exec Exec' : (ℕ → V → Q) → Prop} {P : (V → Q) → Prop}
    (h : SilentSelfStab next Exec P) (hE : ∀ e, Exec' e → Exec e) :
    SilentSelfStab next Exec' P :=
  ⟨fun e he => h.1 e (hE e he), h.2⟩

end Exec

section Local

variable {I : Type*}

/-- Locality of an algorithm on the digraph `G`, parameterised by the input assignment `ι`
(identifiers): the next state of `p` only depends on the inputs and states of `p` and of its
predecessors. -/
def IsLocal (G : Digraph V) (next : (V → I) → (V → Q) → V → Q) : Prop :=
  ∀ ι ι' γ γ' p, (∀ q, (q = p ∨ G.Adj q p) → ι q = ι' q ∧ γ q = γ' q) →
    next ι γ p = next ι' γ' p

/-- Lemma 12 of the paper (generalised to different input assignments): two synchronous executions
whose inputs and initial configurations agree on a predecessor-closed set `S` agree on `S`
forever. -/
theorem syncExec_agree {G : Digraph V} {next : (V → I) → (V → Q) → V → Q} (hloc : IsLocal G next)
    {S : Set V} (hS : ∀ p ∈ S, ∀ q, G.Adj q p → q ∈ S) {ι ι' : V → I} (hι : ∀ p ∈ S, ι p = ι' p)
    {e e' : ℕ → V → Q} (he : IsSyncExec (next ι) e) (he' : IsSyncExec (next ι') e')
    (h0 : ∀ p ∈ S, e 0 p = e' 0 p) : ∀ t, ∀ p ∈ S, e t p = e' t p := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro p hp
    rw [he t, he' t]
    apply hloc
    rintro q (rfl | hq)
    · exact ⟨hι _ hp, ih _ hp⟩
    · exact ⟨hι _ (hS p hp q hq), ih _ (hS p hp q hq)⟩

end Local

end Podc.AtomicState
