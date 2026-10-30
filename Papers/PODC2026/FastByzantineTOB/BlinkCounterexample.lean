import Papers.PODC2026.FastByzantineTOB.Blink

/-!
# Blink with the paper's thresholds is not safe for `n = 5f + 2`

The abstract and introduction say that Flutter (and Blink) assume "at least `5f + 1` servers"; the
model (§2.1) fixes `n = 5f + 1`. Blink's thresholds `4f + 1` / `2f + 1` are tied to `n = 5f + 1`:
with `n = 5f + 2` Agreement fails, even though `dep` satisfies Validity, Agreement and Integrity.

Run for `f = 1`, `n = 7`, Byzantine server `6`:
* servers `0–3` propose `true`, servers `4, 5` propose `false`;
* server `0` receives `true` from `0, 1, 2, 3` and from the Byzantine `6`: `5 = 4f + 1` matching
  suggestions, so it fast-decides `true`;
* server `4` receives `false` from `4, 5, 6` and `true` from `0, 1`: `5 = 4f + 1` suggestions with
  `3 = 2f + 1` for `false`, so it proposes `false` to `dep`;
* `dep` decides `false` at server `4` (a correct server proposed `false` to `dep`), and server `4`
  decides `false`.
* To show that the run is a prefix of a run where `dep` also terminates, we complete it: every
  correct server proposes to `dep` and `dep` decides `false` at every correct server
  (`cexRun_complete`).

With the thresholds `n − f`, `2f + 1`, `n − f` Blink is safe for every `n ≥ 5f + 1`
(`blink_safe_general`).
-/

namespace Podc.FastByzantineTOB.Blink

/-- The actions of the counterexample run. -/
def cexActs : List (Fin 7 × Act (Fin 7)) :=
  [(0, .propose true), (1, .propose true), (2, .propose true), (3, .propose true),
   (4, .propose false), (5, .propose false),
   (0, .recv 0 true), (0, .recv 1 true), (0, .recv 2 true), (0, .recv 3 true), (0, .recv 6 true),
   (0, .fast true),
   (4, .recv 4 false), (4, .recv 5 false), (4, .recv 6 false), (4, .recv 0 true),
   (4, .recv 1 true), (4, .depPropose false), (4, .depDecide false),
   -- completing the run: every correct server proposes to `dep`, `dep` decides `false` everywhere
   (0, .recv 4 false), (0, .depPropose true), (0, .depDecide false),
   (1, .recv 0 true), (1, .recv 1 true), (1, .recv 2 true), (1, .recv 3 true), (1, .recv 4 false),
   (1, .depPropose true), (1, .depDecide false),
   (2, .recv 0 true), (2, .recv 1 true), (2, .recv 2 true), (2, .recv 3 true), (2, .recv 4 false),
   (2, .depPropose true), (2, .depDecide false),
   (3, .recv 0 true), (3, .recv 1 true), (3, .recv 2 true), (3, .recv 3 true), (3, .recv 4 false),
   (3, .depPropose true), (3, .depDecide false),
   (5, .recv 0 true), (5, .recv 1 true), (5, .recv 2 true), (5, .recv 3 true), (5, .recv 4 false),
   (5, .depPropose true), (5, .depDecide false)]

lemma cexActs_valid : ValidList {6} (paperThresholds 1) cexActs := by decide

/-- The counterexample run. -/
def cexRun : Run ({6} : Finset (Fin 7)) (paperThresholds 1) :=
  Run.ofList _ _ cexActs cexActs_valid

lemma cexRun_final : ∀ k, cexActs.length ≤ k → cexRun.st k = listState cexActs cexActs.length := by
  intro k hk
  simp [cexRun, Run.ofList, listState, List.take_of_length_le hk]

lemma cexRun_depDecs (k : ℕ) (p : Fin 7) (v : Bool) (h : v ∈ (cexRun.st k p).depDecs) :
    v = false := by
  have h' := cexRun.depDecs_mono (le_max_left k cexActs.length) p h
  rw [cexRun_final _ (le_max_right _ _)] at h'
  clear h
  revert h'
  revert p v
  decide

lemma cexRun_depValidity : DepValidity cexRun := by
  intro k p v hp h
  obtain rfl := cexRun_depDecs k p v h
  refine ⟨cexActs.length, 4, by decide, ?_⟩
  rw [cexRun_final _ le_rfl]
  decide

lemma cexRun_depAgreement : DepAgreement cexRun := by
  intro k k' p q v w _ _ hv hw
  rw [cexRun_depDecs k p v hv, cexRun_depDecs k' q w hw]

lemma cexRun_depIntegrity : DepIntegrity cexRun := by
  intro k p _
  have h := (cexRun.depDecs_prefix (le_max_left k cexActs.length) p).length_le
  rw [cexRun_final _ (le_max_right _ _)] at h
  refine h.trans ?_
  clear h
  revert p
  decide

/-- In the final state every correct server has proposed to `dep`, received `dep`'s decision
`false`, and decided. -/
lemma cexRun_complete : ∀ p : Fin 7, p ≠ 6 →
    (listState cexActs cexActs.length p).depProp.isSome ∧
    (listState cexActs cexActs.length p).depDecs = [false] ∧
    (listState cexActs cexActs.length p).decs ≠ [] := by
  decide

/-- **Blink is not safe for `n = 5f + 2`** with the paper's thresholds: for `f = 1`, `n = 7`, one
Byzantine server, and a `dep` satisfying Validity, Agreement and Integrity, two correct servers
decide differently. -/
theorem blink_agreement_fails_5f2 :
    Fintype.card (Fin 7) = 5 * 1 + 2 ∧ ({6} : Finset (Fin 7)).card ≤ 1 ∧
      DepValidity cexRun ∧ DepAgreement cexRun ∧ DepIntegrity cexRun ∧ ¬ Agreement cexRun := by
  refine ⟨rfl, by decide, cexRun_depValidity, cexRun_depAgreement, cexRun_depIntegrity, ?_⟩
  intro h
  have := h cexActs.length cexActs.length 0 4 true false (by decide) (by decide)
    (by rw [cexRun_final _ le_rfl]; decide) (by rw [cexRun_final _ le_rfl]; decide)
  exact absurd this (by decide)

end Podc.FastByzantineTOB.Blink
