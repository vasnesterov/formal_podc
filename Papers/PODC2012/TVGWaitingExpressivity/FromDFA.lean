import Papers.PODC2012.TVGWaitingExpressivity.Basic

/-!
# A finite automaton as a static TVG (Theorem 4.1, easy inclusion)

A DFA is a TVG-automaton whose edges are always present with latency `0`. Whatever the pause rule
(as long as departing immediately is allowed), it accepts exactly the language of the DFA.
-/

namespace Podc.TVGWaitingExpressivity

open TVG TVGAutomaton

variable {α σ : Type*}

/-- The static TVG-automaton of a DFA: edge `(u, a, v)` is always present iff `δ(u, a) = v`, with
latency `0`. -/
def ofDFA (M : DFA α σ) : TVGAutomaton σ α where
  present e _ := M.step e.1 e.2.1 = e.2.2
  latency _ _ := 0
  init := {M.start}
  accept := M.accept
  start := 0

theorem ofDFA_journey {M : DFA α σ} {P : PauseRule} {u : σ} {t : ℕ} {w : List α} {v : σ} {t' : ℕ}
    (h : (ofDFA M).Journey P u t w v t') : v = M.evalFrom u w := by
  induction h with
  | nil => rfl
  | cons _ hpres _ ih =>
    rw [ih]
    change M.step _ _ = _ at hpres
    simp [DFA.evalFrom, hpres]

theorem journey_ofDFA (M : DFA α σ) {P : PauseRule} (hP : ∀ t, P t t) (u : σ) (t : ℕ)
    (w : List α) : (ofDFA M).Journey P u t w (M.evalFrom u w) t := by
  induction w generalizing u with
  | nil => exact .nil _ _
  | cons a w ih =>
    refine .cons (v := M.step u a) (hP t) rfl ?_
    simpa [ofDFA, DFA.evalFrom] using ih (M.step u a)

/-- The static TVG of a DFA accepts the DFA's language, for any pause rule that allows leaving at
once (in particular with and without waiting). -/
theorem ofDFA_lang (M : DFA α σ) {P : PauseRule} (hP : ∀ t, P t t) :
    (ofDFA M).lang P = M.accepts := by
  ext w
  constructor
  · rintro ⟨s, rfl, f, hf, t', h⟩
    rw [ofDFA_journey h] at hf
    exact hf
  · intro hw
    exact ⟨M.start, rfl, M.eval w, hw, 0, journey_ofDFA M hP M.start 0 w⟩

theorem ofDFA_Lwait (M : DFA α σ) : (ofDFA M).Lwait = M.accepts :=
  ofDFA_lang M fun t => le_refl t

/-- Regular languages are in `𝓛_wait` (first inclusion of Theorem 4.1). -/
theorem isRegular_mem_LwaitFamily {α : Type} {L : Language α} (hL : L.IsRegular) :
    L ∈ LwaitFamily α := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, inferInstance, ofDFA M, ofDFA_Lwait M⟩

end Podc.TVGWaitingExpressivity
