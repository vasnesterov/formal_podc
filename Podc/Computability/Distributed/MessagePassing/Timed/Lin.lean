import Podc.Computability.Distributed.MessagePassing.Timed.Basic

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/Timed/Lin.lean

/-!
# Linearizable implementations in the timed message-passing model

Shared objects implemented by an `Algorithm` in the timed model of
`Podc.Computability.Distributed.MessagePassing.Timed.Basic`.

* A sequential specification is a predicate `legal` on finite sequences of operation instances
  `(argument, return value)`.
* `RespAt A s H c σ r`: in the run `H` of `s`, the invoking process of `c` responds `r` to `c` at
  real time `σ`.
* `WF A s H` (application constraint): ids and invocation times are unique per process and each
  operation of a process responds before the next one is invoked.
* `Correct A legal d u ε`: in every admissible well-formed run, every operation has exactly one
  response, not before its invocation, and the history is linearizable: some permutation of the
  operations is legal and respects the real-time order ("`c` responds before `c'` is invoked").
* `TimeBound A d u ε OP B`: every operation whose argument satisfies `OP` responds within `B`.
* `FiniteRuns`, `HistoryOblivious`: the bounded-quiescence and history-obliviousness assumptions
  of Wang–Welch–Lee (finite runs; the residual behaviour of every process after a run in which one
  process alone executes a given sequence of operations does not depend on the timing).
* `agree_of_calls_ge`, `WF.snoc`: adding later invocations does not change the past; extending a
  well-formed scenario by an invocation after the previous responses keeps it well formed.
-/

namespace Cslib.TimedMP

variable {P I R M : Type*} (A : Algorithm P I R M)

/-- The invoking process of `c` responds `r` to `c` at real time `σ`. -/
def RespAt (s : Scenario P I) (H : P → Set (ℝ × InEv P I M)) (c : Call P I) (σ : ℝ) (r : R) :
    Prop :=
  (σ + s.off c.p, OutEv.resp c.k r) ∈ A.beh c.p (H c.p)

/-- Well-formedness of the application: ids and invocation times unique per process, each
operation responds before the next operation of its process is invoked. -/
def WF (s : Scenario P I) (H : P → Set (ℝ × InEv P I M)) : Prop :=
  s.calls.Nodup ∧
  (∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.k = c'.k → c = c') ∧
  (∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.t = c'.t → c = c') ∧
  ∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.t < c'.t →
    ∃ σ r, RespAt A s H c σ r ∧ c.t ≤ σ ∧ σ < c'.t

/-- Linearizability of the operations `calls` with response times `rt` and return values `ret`:
a legal permutation respecting the real-time order. -/
def Linearizable (legal : List (I × R) → Prop) (calls : List (Call P I)) (rt : Call P I → ℝ)
    (ret : Call P I → R) : Prop :=
  ∃ L : List (Call P I), L.Perm calls ∧ legal (L.map fun c => (c.a, ret c)) ∧
    ∀ c ∈ calls, ∀ c' ∈ calls, rt c < c'.t → [c, c'].Sublist L

/-- Correctness of an implementation of the object `legal` in the `(d, u, ε)` model. -/
def Correct (legal : List (I × R) → Prop) (d u ε : ℝ) : Prop :=
  ∀ s H, s.Admissible d u ε → IsRun A s H → WF A s H →
    ∃ rt : Call P I → ℝ, ∃ ret : Call P I → R,
      (∀ c ∈ s.calls, c.t ≤ rt c ∧ RespAt A s H c (rt c) (ret c) ∧
        ∀ σ r, RespAt A s H c σ r → σ = rt c ∧ r = ret c) ∧
      Linearizable legal s.calls rt ret

/-- Every operation with argument in `OP` responds within time `B` of its invocation. -/
def TimeBound (d u ε : ℝ) (OP : I → Prop) (B : ℝ) : Prop :=
  ∀ s H, s.Admissible d u ε → IsRun A s H → WF A s H →
    ∀ c ∈ s.calls, OP c.a → ∀ σ r, RespAt A s H c σ r → σ ≤ c.t + B

/-- Bounded quiescence (weak form): every admissible well-formed run (finitely many invocations)
is finite: it has no event after some time. -/
def FiniteRuns (d u ε : ℝ) : Prop :=
  ∀ s H, s.Admissible d u ε → IsRun A s H → WF A s H →
    ∃ T, ∀ p, (∀ e ∈ H p, e.1 - s.off p < T) ∧ ∀ o ∈ A.beh p (H p), o.1 - s.off p < T

/-- In the run, `p₀` alone executes operations, namely the sequence `ops` (arguments and return
values, in the order of invocation). -/
def SoloOps (s : Scenario P I) (H : P → Set (ℝ × InEv P I M)) (p₀ : P) (ops : List (I × R)) :
    Prop :=
  (∀ c ∈ s.calls, c.p = p₀) ∧ ∃ L : List (Call P I), L.Perm s.calls ∧
    L.Pairwise (fun c c' => c.t < c'.t) ∧
    List.Forall₂ (fun c o => c.a = o.1 ∧ ∃ σ, RespAt A s H c σ o.2) L ops

/-- History-obliviousness: if in two admissible well-formed runs the same process alone executes
the same sequence of operations, then every process has the same residual behaviour after both
runs (the same "final state"). -/
def HistoryOblivious (d u ε : ℝ) : Prop :=
  ∀ s₁ s₂ H₁ H₂ (p₀ : P) (ops : List (I × R)), s₁.Admissible d u ε → s₂.Admissible d u ε →
    IsRun A s₁ H₁ → IsRun A s₂ H₂ → WF A s₁ H₁ → WF A s₂ H₂ →
    SoloOps A s₁ H₁ p₀ ops → SoloOps A s₂ H₂ p₀ ops →
    ∀ p κ, (∀ e ∈ H₁ p, e.1 < κ) → (∀ e ∈ H₂ p, e.1 < κ) →
      (∀ o ∈ A.beh p (H₁ p), o.1 < κ) → (∀ o ∈ A.beh p (H₂ p), o.1 < κ) →
      SameResidual (A.beh p) (H₁ p) (H₂ p) κ

/-- Truncation of a scenario before time `τ` (invocations at times `< τ` only). -/
noncomputable def Scenario.trunc (s : Scenario P I) (τ : ℝ) : Scenario P I :=
  { s with calls := s.calls.filter fun c => decide (c.t < τ) }

section Lemmas

variable {A}

/-- Responses transfer between runs (same offsets) whose inputs at the responding process agree
before the response. -/
theorem respAt_congr {s s' : Scenario P I} (hoff : s.off = s'.off)
    {H H' : P → Set (ℝ × InEv P I M)} {c : Call P I} {σ T : ℝ} {r : R}
    (h : ∀ e : ℝ × InEv P I M, e.1 - s.off c.p < T → (e ∈ H c.p ↔ e ∈ H' c.p)) (hσ : σ < T) :
    RespAt A s H c σ r ↔ RespAt A s' H' c σ r := by
  unfold RespAt
  rw [← hoff]
  exact A.causal_lt c.p (τ := T + s.off c.p) (fun e he => h e (by linarith)) _
    (by simp only; linarith)

/-- Responses in a shifted scenario. -/
theorem respAt_shift {s : Scenario P I} {H : P → Set (ℝ × InEv P I M)} (x : P → ℝ)
    (c : Call P I) (σ : ℝ) (r : R) :
    RespAt A (s.shift x) H { c with t := c.t + x c.p } (σ + x c.p) r ↔ RespAt A s H c σ r := by
  unfold RespAt Scenario.shift
  simp only
  ring_nf

variable [Finite P]

/-- Adding or removing invocations at times `≥ τ` does not change the runs before `τ`. -/
theorem agree_of_calls_ge {s s' : Scenario P I} (hoff : s.off = s'.off)
    (hdel : s.delay = s'.delay) {H H' : P → Set (ℝ × InEv P I M)} (hH : IsRun A s H)
    (hH' : IsRun A s' H') {γ : ℝ} (hγ : s.MinDelay γ) (τ : ℝ)
    (h1 : ∀ c ∈ s.calls, c ∉ s'.calls → τ ≤ c.t) (h2 : ∀ c ∈ s'.calls, c ∉ s.calls → τ ≤ c.t) :
    ∀ p (e : ℝ × InEv P I M), e.1 - s.off p < τ → (e ∈ H p ↔ e ∈ H' p) := by
  refine agree_of_cut A s s' hoff hH hH' hγ (fun _ => τ) ?_ (fun _ _ _ _ => Or.inl (by rw [hdel]))
    (fun q r σ hσ => by
      have := hγ.2 q r σ; have := hγ.1; rw [← hdel]; constructor <;> linarith)
  intro p e he
  simp only [Scenario.callEv, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc, rfl, rfl⟩
    refine ⟨c, ?_, rfl, by rw [hoff]⟩
    by_contra hn
    have := h1 c hc hn
    simp at he; linarith
  · rintro ⟨c, hc, rfl, rfl⟩
    refine ⟨c, ?_, rfl, by rw [hoff]⟩
    by_contra hn
    have := h2 c hc hn
    simp [hoff] at he; linarith

/-- Extending a well-formed scenario by an invocation later than all others, after the previous
operations of its process responded, keeps it well formed. -/
theorem WF.snoc {s : Scenario P I} {H H' : P → Set (ℝ × InEv P I M)} (hwf : WF A s H)
    (hH : IsRun A s H) {c : Call P I}
    (hH' : IsRun A { s with calls := s.calls ++ [c] } H') {γ : ℝ} (hγ : s.MinDelay γ)
    (hlate : ∀ c' ∈ s.calls, c'.t < c.t) (hk : ∀ c' ∈ s.calls, c'.p = c.p → c'.k ≠ c.k)
    (hresp : ∀ c' ∈ s.calls, c'.p = c.p → ∃ σ r, RespAt A s H c' σ r ∧ c'.t ≤ σ ∧ σ < c.t) :
    WF A { s with calls := s.calls ++ [c] } H' := by
  have hag := agree_of_calls_ge (A := A) (s := s) (s' := { s with calls := s.calls ++ [c] })
    rfl rfl hH hH' hγ c.t (fun c' hc' hn => absurd (List.mem_append_left _ hc') hn)
    (fun c' hc' hn => by
      rcases List.mem_append.mp hc' with h | h
      · exact absurd h hn
      · simp at h; subst h; exact le_rfl)
  have tr : ∀ c' σ r, σ < c.t → RespAt A s H c' σ r →
      RespAt A { s with calls := s.calls ++ [c] } H' c' σ r := fun c' σ r hσ h =>
    (respAt_congr (s := s) rfl (fun e he => hag c'.p e he) hσ).mp h
  have hcn : c ∉ s.calls := fun h => lt_irrefl _ (hlate c h)
  obtain ⟨hnd, hid, htm, hrs⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton c,
      fun a ha b hb => by simp at hb; subst hb; rintro rfl; exact hcn ha⟩
  · intro c1 h1 c2 h2 hp hkk
    simp only [List.mem_append, List.mem_singleton] at h1 h2
    rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
    · exact hid c1 h1 c2 h2 hp hkk
    · exact absurd hkk (hk c1 h1 hp)
    · exact absurd hkk.symm (hk c2 h2 hp.symm)
    · rfl
  · intro c1 h1 c2 h2 hp ht
    simp only [List.mem_append, List.mem_singleton] at h1 h2
    rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
    · exact htm c1 h1 c2 h2 hp ht
    · exact absurd ht (ne_of_lt (hlate c1 h1))
    · exact absurd ht.symm (ne_of_lt (hlate c2 h2))
    · rfl
  · intro c1 h1 c2 h2 hp ht
    simp only [List.mem_append, List.mem_singleton] at h1 h2
    rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
    · obtain ⟨σ, r, hr, h1', h2'⟩ := hrs c1 h1 c2 h2 hp ht
      exact ⟨σ, r, tr c1 σ r (by linarith [hlate c2 h2]) hr, h1', h2'⟩
    · obtain ⟨σ, r, hr, h1', h2'⟩ := hresp c1 h1 hp
      exact ⟨σ, r, tr c1 σ r h2' hr, h1', h2'⟩
    · exact absurd ht (not_lt.mpr (le_of_lt (hlate c2 h2)))
    · exact absurd ht (lt_irrefl _)

end Lemmas

end Cslib.TimedMP
