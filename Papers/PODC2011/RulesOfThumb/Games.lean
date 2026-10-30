import Papers.PODC2011.RulesOfThumb.Examples

/-!
# Game dynamics: Corollary 5.2 / Theorem B.2

Appendix B.1: players `i : ι` with strategy sets `A i` and utilities `u i : Profile A → ℝ`.
Best-response dynamics with *consistent tie-breaking*: every player has a fixed best-response
function `br i`, a best reply to the others' current strategies that depends only on them
(`BRRule`); as a reaction function it is deterministic, historyless and self-independent
(`BRRule.sys`).

* `corollary_5_2_false`: Corollary 5.2 (and Theorem B.2) are **false** as stated: in a `2 × 2`
  game with the two pure Nash equilibria `(x,x)` and `(y,y)`, where `(y,y)` is weakly dominated and
  ties are broken towards `x`, asynchronous best-response dynamics always converges. The pure
  equilibrium `(y,y)` is not a fixed point of the tie-breaking best-response map, so it is not a
  stable state of the dynamics, and Theorem 4.1 does not apply.
* `theorem_5_1_false`: the same example refutes Theorem 5.1 as stated.
* `corollary_5_2`: the corrected statement: two distinct pure Nash equilibria that are fixed points
  of the best-response map (`corollary_5_2_of_unique`: automatically so if best responses are
  unique) imply that best-response dynamics is not convergent.
-/

namespace Podc.RulesOfThumb

open Filter Podc.RulesOfThumb.System

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι]

/-- A game in normal form: a utility function for every player. -/
structure Game (A : ι → Type v) where
  /-- The utility of player `i`. -/
  u : ι → Profile A → ℝ

/-- A pure Nash equilibrium (Definition B.1). -/
def Game.IsNash (G : Game A) (s : Profile A) : Prop :=
  ∀ i (a : A i), G.u i (Function.update s i a) ≤ G.u i s

/-- Best response with consistent tie-breaking: a fixed best reply `br i s` of player `i` to the
other players' strategies in `s`, depending only on them. -/
structure BRRule (G : Game A) where
  /-- The best response of player `i` to the profile `s`. -/
  br : (i : ι) → Profile A → A i
  /-- `br i s` depends only on the other players' strategies. -/
  others : ∀ i (s s' : Profile A), (∀ j, j ≠ i → s j = s' j) → br i s = br i s'
  /-- `br i s` is a best response. -/
  best : ∀ i (s : Profile A) (a : A i),
    G.u i (Function.update s i a) ≤ G.u i (Function.update s i (br i s))

/-- Best-response dynamics: each activated player best-replies to the current profile. -/
def BRRule.sys {G : Game A} (R : BRRule G) : System A := ⟨fun i _ h => R.br i h.cur⟩

namespace BRRule

variable {G : Game A} (R : BRRule G)

lemma sys_selfIndependent : R.sys.SelfIndependent := fun i _ _ he =>
  R.others i _ _ (List.forall₂_cons.mp he).1

lemma sys_historyless (i : ι) (s₀ : Profile A) : R.sys.Stationary i 1 :=
  ⟨fun l => (l.head?.map (R.br i)).getD (s₀ i), fun h _ => by simp [sys, Hist.toList]⟩

lemma isStableState_of_fixed {s : Profile A} (hs : ∀ i, R.br i s = s i) [Fintype ι]
    [Nonempty ι] : R.sys.IsStableState s := by
  refine ⟨⟨s, []⟩, _, isSchedule_univ, fair_univ, Eventually.of_forall fun m => ?_⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [run_succ]
    funext i
    rw [step_cur_of_mem _ (Finset.mem_univ _)]
    show R.br i (R.sys.run _ _ m).cur = s i
    rw [ih, hs]

/-- With unique best responses, every pure Nash equilibrium is a fixed point of `br`. -/
lemma fixed_of_isNash (huniq : ∀ i (s : Profile A) (a : A i),
      G.u i (Function.update s i a) = G.u i (Function.update s i (R.br i s)) → a = R.br i s)
    {s : Profile A} (hs : G.IsNash s) (i : ι) : R.br i s = s i := by
  have h1 := hs i (R.br i s)
  have h2 := R.best i s (s i)
  rw [Function.update_eq_self] at h2
  exact (huniq i s (s i) (by rw [Function.update_eq_self]; linarith)).symm

end BRRule

/-- **Corollary 5.2 / Theorem B.2, corrected**: if two distinct pure Nash equilibria are fixed
points of the best-response map, then asynchronous best-response dynamics (with consistent
tie-breaking) is not convergent. -/
theorem corollary_5_2 [Fintype ι] {G : Game A} (R : BRRule G) {s s' : Profile A} (hss' : s ≠ s')
    (hs : ∀ i, R.br i s = s i) (hs' : ∀ i, R.br i s' = s' i) : ¬ R.sys.Convergent := by
  have : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hss' (funext fun i => isEmptyElim i)
  exact theorem_4_1 (fun i => ⟨1, R.sys_historyless i s⟩) R.sys_selfIndependent
    ⟨s, s', hss', R.isStableState_of_fixed hs, R.isStableState_of_fixed hs'⟩

/-- **Corollary 5.2** for games with unique best responses: two distinct pure Nash equilibria imply
that asynchronous best-response dynamics is not convergent. -/
theorem corollary_5_2_of_unique [Fintype ι] {G : Game A} (R : BRRule G)
    (huniq : ∀ i (s : Profile A) (a : A i),
      G.u i (Function.update s i a) = G.u i (Function.update s i (R.br i s)) → a = R.br i s)
    {s s' : Profile A} (hss' : s ≠ s') (hs : G.IsNash s) (hs' : G.IsNash s') :
    ¬ R.sys.Convergent :=
  corollary_5_2 R hss' (R.fixed_of_isNash huniq hs) (R.fixed_of_isNash huniq hs')

/-! ### The counterexample -/

/-- Player `0` gets `1` unless it plays `y` against `x` (so `x` weakly dominates `y`); player `1`
gets `1` iff it matches player `0`. -/
noncomputable def cexGame : Game (fun _ : Fin 2 => Bool) where
  u i s := if i = 0 then (if s 0 = false ∨ s 1 = true then 1 else 0) else
    (if s 1 = s 0 then 1 else 0)

/-- Tie-breaking towards `x = false`: player `0` always plays `x`, player `1` copies player `0`. -/
noncomputable def cexRule : BRRule cexGame where
  br i s := if i = 0 then false else s 0
  others i s s' h := by
    fin_cases i
    · simp
    · simp only [Fin.mk_one, one_ne_zero, if_false]; exact h 0 (by decide)
  best i s a := by
    fin_cases i <;> cases a <;> simp [cexGame, Function.update_apply] <;> split_ifs <;> norm_num

lemma cexGame_isNash (b : Bool) : cexGame.IsNash (pr b b) := by
  intro i a
  fin_cases i <;> cases a <;> cases b <;> simp [cexGame, pr, Function.update_apply]

theorem cexRule_convergent : cexRule.sys.Convergent := by
  intro s₀ σ _ hf
  have h0 : ∀ᶠ m in atTop, (cexRule.sys.run s₀ σ m).cur 0 = false :=
    eventually_cur_eq_of (m₀ := 0) (fun m _ _ => by simp [BRRule.sys, cexRule]) (hf 0)
  obtain ⟨M, hM⟩ := eventually_atTop.mp h0
  have h1 : ∀ᶠ m in atTop, (cexRule.sys.run s₀ σ m).cur 1 = false :=
    eventually_cur_eq_of (m₀ := M) (fun m hm _ => by
      simp only [BRRule.sys, cexRule, Fin.isValue, one_ne_zero, if_false]; exact hM m hm) (hf 1)
  refine ⟨pr false false, convergesTo_of_forall fun j => ?_⟩
  fin_cases j
  · simpa [pr] using h0
  · simpa [pr] using h1

/-- **Corollary 5.2 (and Theorem B.2) are false as stated**: a game with two pure Nash equilibria
in which best-response dynamics with consistent tie-breaking always converges. -/
theorem corollary_5_2_false : ∃ (G : Game (fun _ : Fin 2 => Bool)) (R : BRRule G) (s s' : P2),
    s ≠ s' ∧ G.IsNash s ∧ G.IsNash s' ∧ R.sys.Convergent :=
  ⟨cexGame, cexRule, pr false false, pr true true, by simp [pr_eq_iff, pr], cexGame_isNash _,
    cexGame_isNash _, cexRule_convergent⟩

/-- **Theorem 5.1 is false as stated** ("if there are two pure Nash equilibria, then all
bounded-recall self-independent dynamics can oscillate indefinitely"): the best-response
dynamics of the counterexample game is historyless and self-independent, and it always
converges. -/
theorem theorem_5_1_false : ∃ (G : Game (fun _ : Fin 2 => Bool)) (s s' : P2)
    (F : System (fun _ : Fin 2 => Bool)),
    s ≠ s' ∧ G.IsNash s ∧ G.IsNash s' ∧ (∀ i, F.Historyless i) ∧ F.SelfIndependent ∧
      F.Convergent :=
  ⟨cexGame, pr false false, pr true true, cexRule.sys, by simp [pr_eq_iff, pr], cexGame_isNash _,
    cexGame_isNash _, fun i => cexRule.sys_historyless i (pr false false),
    cexRule.sys_selfIndependent, cexRule_convergent⟩

end Podc.RulesOfThumb
