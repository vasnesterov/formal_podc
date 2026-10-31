import Podc.Computability.Distributed.MessagePassing.FailureDetectors.Model

/-!
# Tools for constructing runs: adaptive schedules and local indistinguishability

Two generic facts about the CHT-style model of `Cslib.FailureDetectors`:

* `policyRun`: a run whose schedule is chosen *adaptively*, by a policy that looks at the current
  configuration (e.g. "receive the message sent at time `s`, if there is one"). Its
  configurations are computed by `policyCfg` (`cfg_policyRun`).
* `sim`: if a process `p` takes the same steps (same scheduler choices, same failure-detector
  values) in two runs up to time `T`, and receives only its own messages, then it has the same
  local states, broadcasts the same messages and produces the same outputs in both runs up to `T`.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

variable {P R M I O S : Type*} [DecidableEq P]

-- Model candidate
/-- The configurations of a run with an adaptive schedule `π t C` (the step at time `t` as a
function of the configuration `C` before it). -/
def policyCfg (A : Algorithm P R M I O S) (H : P → ℕ → R)
    (π : ℕ → Config P M S → Option (P × Choice P I)) : ℕ → Config P M S
  | 0 => A.initCfg
  | t + 1 => (A.next H t (policyCfg A H π t) (π t (policyCfg A H π t))).1

-- Model candidate
/-- The run with failure pattern `F`, history `H` and the adaptive schedule `π`. -/
def policyRun (A : Algorithm P R M I O S) (F : FailurePattern P) (H : P → ℕ → R)
    (π : ℕ → Config P M S → Option (P × Choice P I)) : Run P R I :=
  ⟨F, H, fun t => π t (policyCfg A H π t)⟩

variable {A : Algorithm P R M I O S}

lemma cfg_policyRun (F : FailurePattern P) (H : P → ℕ → R)
    (π : ℕ → Config P M S → Option (P × Choice P I)) (t : ℕ) :
    A.cfg (policyRun A F H π) t = policyCfg A H π t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Algorithm.cfg_succ, ih]; rfl

lemma σ_policyRun (F : FailurePattern P) (H : P → ℕ → R)
    (π : ℕ → Config P M S → Option (P × Choice P I)) (t : ℕ) :
    (policyRun A F H π).σ t = π t (A.cfg (policyRun A F H π) t) := by
  rw [cfg_policyRun]; rfl

/-- Receptions of `p`'s own message resolve identically in two configurations that agree on the
messages broadcast by `p`. -/
lemma event_recv_eq {C₁ C₂ : Config P M S} {p : P} {s : ℕ}
    (h : ∀ m, C₁.msg s = some (p, m) ↔ C₂.msg s = some (p, m)) :
    C₁.event (.recv p s : Choice P I) = C₂.event (.recv p s : Choice P I) := by
  simp only [Config.event]
  rcases h₁ : C₁.msg s with _ | ⟨y₁, m₁⟩ <;> rcases h₂ : C₂.msg s with _ | ⟨y₂, m₂⟩
  · rfl
  · by_cases hy : y₂ = p
    · subst hy; exact absurd ((h m₂).2 h₂) (by simp [h₁])
    · simp [hy]
  · by_cases hy : y₁ = p
    · subst hy; exact absurd ((h m₁).1 h₁) (by simp [h₂])
    · simp [hy]
  · by_cases hy₁ : y₁ = p
    · subst hy₁
      have := (h m₁).1 h₁; rw [h₂] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this; rfl
    · by_cases hy₂ : y₂ = p
      · subst hy₂
        have := (h m₂).2 h₂; rw [h₁] at this
        simp only [Option.some.injEq, Prod.mk.injEq] at this
        exact absurd this.1 hy₁
      · simp [hy₁, hy₂]

/-- A stored message from `p` at time `t` comes from a step of `p` at time `t`. -/
lemma msg_succ_self_of_ne {r : Run P R I} {t : ℕ} {p : P} (h : ∀ c, r.σ t ≠ some (p, c)) (m : M) :
    (A.cfg r (t + 1)).msg t ≠ some (p, m) := by
  intro hm
  obtain ⟨c, -, hσ, -⟩ := Algorithm.msg_spec r hm
  exact h c hσ

-- Model candidate
/-- **Local indistinguishability.** If `p` takes the same steps (same scheduler choices and the
same failure-detector values) in two runs before time `T` and receives only its own messages,
then up to time `T` its local states coincide, and so do the messages it has broadcast. -/
lemma sim (r₁ r₂ : Run P R I) (p : P) (T : ℕ)
    (hσ : ∀ t < T, ∀ c, r₁.σ t = some (p, c) ↔ r₂.σ t = some (p, c))
    (hH : ∀ t < T, r₁.H p t = r₂.H p t)
    (hrecv : ∀ t < T, ∀ q s, r₁.σ t = some (p, .recv q s) → q = p) :
    ∀ t ≤ T, A.st r₁ p t = A.st r₂ p t ∧
      ∀ s m, (A.cfg r₁ t).msg s = some (p, m) ↔ (A.cfg r₂ t).msg s = some (p, m) := by
  intro t ht
  induction t with
  | zero => exact ⟨rfl, fun s m => by simp [Algorithm.initCfg]⟩
  | succ t ih =>
    obtain ⟨hst, hmsg⟩ := ih (by omega)
    have htT : t < T := by omega
    by_cases hstep : ∃ c, r₁.σ t = some (p, c)
    · obtain ⟨c, hc₁⟩ := hstep
      have hc₂ := (hσ t htT c).1 hc₁
      have hev : (A.cfg r₁ t).event c = (A.cfg r₂ t).event c := by
        cases c with
        | recv q s =>
          obtain rfl := hrecv t htT q s hc₁
          exact event_recv_eq (hmsg s)
        | tick => rfl
        | input i => rfl
      rcases he : (A.cfg r₁ t).event c with _ | e
      · have he₂ : (A.cfg r₂ t).event c = none := hev ▸ he
        obtain ⟨h₁, -⟩ := Algorithm.cfg_succ_of_event_none r₁ t p c hc₁ he
        obtain ⟨h₂, -⟩ := Algorithm.cfg_succ_of_event_none r₂ t p c hc₂ he₂
        simp only [Algorithm.st, h₁, h₂]
        exact ⟨hst, hmsg⟩
      · have he₂ : (A.cfg r₂ t).event c = some e := hev ▸ he
        obtain ⟨h₁, hm₁, -⟩ := Algorithm.cfg_succ_of_event r₁ t p c e hc₁ he
        obtain ⟨h₂, hm₂, -⟩ := Algorithm.cfg_succ_of_event r₂ t p c e hc₂ he₂
        rw [hH t htT, hst] at h₁ hm₁
        refine ⟨h₁.trans h₂.symm, fun s m => ?_⟩
        by_cases hs : s = t
        · subst hs; rw [hm₁, hm₂]
        · rw [Algorithm.msg_succ r₁ t s hs, Algorithm.msg_succ r₂ t s hs]; exact hmsg s m
    · push Not at hstep
      have hstep₂ : ∀ c, r₂.σ t ≠ some (p, c) := fun c h => hstep c ((hσ t htT c).2 h)
      refine ⟨?_, fun s m => ?_⟩
      · rw [Algorithm.loc_succ_of_ne r₁ t p hstep, Algorithm.loc_succ_of_ne r₂ t p hstep₂]
        exact hst
      · by_cases hs : s = t
        · subst hs
          exact iff_of_false (msg_succ_self_of_ne hstep m) (msg_succ_self_of_ne hstep₂ m)
        · rw [Algorithm.msg_succ r₁ t s hs, Algorithm.msg_succ r₂ t s hs]; exact hmsg s m

/-- Under the hypotheses of `sim`, `p` produces the same outputs in both runs before `T`. -/
lemma sim_out (r₁ r₂ : Run P R I) (p : P) (T : ℕ)
    (hσ : ∀ t < T, ∀ c, r₁.σ t = some (p, c) ↔ r₂.σ t = some (p, c))
    (hH : ∀ t < T, r₁.H p t = r₂.H p t)
    (hrecv : ∀ t < T, ∀ q s, r₁.σ t = some (p, .recv q s) → q = p) :
    ∀ t < T, ∀ o, A.Out r₁ p o t ↔ A.Out r₂ p o t := by
  intro t ht o
  obtain ⟨hst, hmsg⟩ := sim (A := A) r₁ r₂ p T hσ hH hrecv t ht.le
  have hev : ∀ c, r₁.σ t = some (p, c) → (A.cfg r₁ t).event c = (A.cfg r₂ t).event c := by
    intro c hc
    cases c with
    | recv q s =>
      obtain rfl := hrecv t ht q s hc
      exact event_recv_eq (hmsg s)
    | tick => rfl
    | input i => rfl
  rw [Algorithm.out_iff, Algorithm.out_iff]
  constructor
  · rintro ⟨c, e, hc, he, ho⟩
    refine ⟨c, e, (hσ t ht c).1 hc, (hev c hc) ▸ he, ?_⟩
    rw [← hH t ht, ← hst]; exact ho
  · rintro ⟨c, e, hc, he, ho⟩
    have hc₁ := (hσ t ht c).2 hc
    refine ⟨c, e, hc₁, (hev c hc₁).symm ▸ he, ?_⟩
    rw [hH t ht, hst]; exact ho

end Podc.WeakestFDEventualConsistency
