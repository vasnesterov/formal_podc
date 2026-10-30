import Papers.PODC2019.RDMAAgreement.RB.Sig

/-!
# Algorithm 2 — contents of the `Value` slots of correct processes

A correct process `j` only ever writes to `Value[j,k,q]` endorsements of one signed pair (its
broadcast if `q = j`, or the pair it echoed). This replaces the paper's (false) Observation 1
("no slot of a correct process is written more than once"): when `q = j` the slot is written
twice (lines 12 and 40), but both writes carry the same pair.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

lemma canon_unique {s : St P M} (I : InvB F s) {j q : P} {k : ℕ} {b b' : Base P M} (hj : j ∉ F)
    (h : canon s j q k b) (h' : canon s j q k b') : b = b' := by
  obtain ⟨hs, hk, h | h⟩ := h <;> obtain ⟨hs', hk', h' | h'⟩ := h'
  · obtain ⟨rfl, h⟩ := h; obtain ⟨-, h'⟩ := h'
    rw [h] at h'; cases b; cases b'; simp_all
  · obtain ⟨rfl, h⟩ := h
    obtain ⟨-, -, e⟩ := I.echo _ hj _ _ _ h'
    rw [e hj] at h; cases b; cases b'; simp_all
  · obtain ⟨rfl, h'⟩ := h'
    obtain ⟨-, -, e⟩ := I.echo _ hj _ _ _ h
    rw [e hj] at h'; cases b; cases b'; simp_all
  · rw [h] at h'; cases h'; rfl

/-- The possible contents of the slot `Value[j,k,q]` of a correct process `j`. -/
def GoodV (s : St P M) (j q : P) (k : ℕ) (v : Val P M) : Prop :=
  v = .bot ∨ ∃ b, v = .cp ⟨j, b⟩ ∧ canon s j q k b

lemma PC.wr_spec {c : PC P M} {p q : P} {k : ℕ} {r : Reg P} {x : Val P M}
    (h : c.wr p q k = some (r, x)) : x ≠ .bot ∧ r.owner = p := by
  cases c <;> simp [PC.wr] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

lemma bot_not_mem_pendW (s : St P M) (r : Reg P) : (.bot : Val P M) ∉ s.pendW r := by
  rintro (⟨p, q, h⟩ | ⟨p, b, -, -, h⟩)
  · exact (PC.wr_spec h).1 rfl
  · cases h

/-- Correct processes never write `⊥`, and Byzantine processes cannot write to their registers. -/
lemma Step.mem_ne_bot {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {r : Reg P}
    (hr : r.owner ∉ F) (hm : s.mem r ≠ .bot) : s'.mem r ≠ .bot := by
  by_cases hℓ : ∃ p q, ℓ = .thr p q
  · obtain ⟨p, q, rfl⟩ := hℓ
    rcases h.thrEffect.mem r with e | e
    · rwa [e]
    · exact (PC.wr_spec e).1
  · push_neg at hℓ
    cases h with
    | bret hp hb =>
      rename_i p b
      simp only [St.tick, St.write]
      by_cases e : r = ⟨.val, p, b.key, p⟩
      · subst e; simp
      · rwa [Function.update_of_ne e]
    | byz hp hr' =>
      rename_i p r0 v
      simp only [St.tick, St.write]
      rw [Function.update_of_ne]; exact hm
      rintro rfl; exact hr (hr' ▸ hp)
    | bcast => simpa [St.tick, St.doBcast] using hm
    | bretIdle => simpa [St.tick] using hm
    | _ => exact absurd rfl (hℓ _ _)

/-- Goodness of correct processes' `Value` slots. -/
structure InvC (F : Finset P) (s : St P M) : Prop where
  good : RegInv s (fun r v => r.kind = .val → r.owner ∉ F → GoodV s r.owner r.sender r.key v)
  nb : ∀ j ∉ F, ∀ q k e, s.echoT j q k = some e → s.mem ⟨.val, j, k, q⟩ ≠ .bot

lemma InvC.init [Inhabited P] : InvC F (St.init : St P M) := by
  refine ⟨⟨fun r _ _ => Or.inl rfl, fun r x hx => ?_, fun p q r _ x hx => ?_⟩, ?_⟩
  · rcases hx with ⟨p, q, h⟩ | ⟨p, b, h, _⟩ <;> simp [St.init, PC.start, PC.wr] at h
  · simp only [St.init, Set.mem_singleton_iff] at hx; subst hx; exact fun _ _ => Or.inl rfl
  · intro j _ q k e h; simp [St.init] at h

lemma InvC.step {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (IB : InvB F s) (I : InvC F s)
    (h : Step F f s ℓ s') : InvC F s' := by
  have G := h.grows IA
  refine ⟨?_, ?_⟩
  · refine I.good.step h ?_ ?_ ?_ ?_
    · intro r x hx hk ho
      rcases hx hk ho with hx | ⟨b, hb, hc⟩
      · exact Or.inl hx
      · exact Or.inr ⟨b, hb, G.canon ho hc⟩
    · rintro p q rfl r x hx hk ho
      cases h with
      | @sndOk _ _ v c hp hpc hv hc hs hk' =>
        simp [St.tick, St.sign, PC.wr] at hx; obtain ⟨rfl, rfl⟩ := hx
        exact Or.inr ⟨c.base, rfl, hs, by simpa [St.key] using hk',
          Or.inr (by simp [St.tick, St.sign, St.key])⟩
      | _ =>
        simp [St.tick, St.sign, St.write, St.deliver, St.setPhase, PC.wr, PC.start] at hx
        all_goals (obtain ⟨rfl, -⟩ := hx; simp at hk)
    · rintro p m rfl _ _
      cases h with
      | bcast => exact Or.inr ⟨_, rfl, rfl, rfl, Or.inl ⟨rfl, by simp [St.tick, St.doBcast]⟩⟩
    · rintro p r v rfl _ ho
      cases h with
      | byz hp hr => exact absurd (hr ▸ hp) ho
  · intro j hj q k e he
    by_cases hnew : s.echoT j q k = some e
    · exact h.mem_ne_bot hj (I.nb j hj q k e hnew)
    · cases h with
      | @echoDone p q' j' b hp hpc =>
        simp only [St.tick, St.write, St.setPhase, go_echoT, upd3_apply2, upd2_apply] at he
        split_ifs at he with hjq
        · obtain ⟨rfl, rfl⟩ := hjq
          by_cases hk : k = s.key j q
          · subst hk; simp [St.tick, St.write, St.setPhase]
          · rw [Function.update_of_ne hk] at he; exact absurd he hnew
        · exact absurd he hnew
      | _ => exact absurd (by simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase,
          St.doBcast] using he) hnew

lemma InvC.reach [Inhabited P] {s : St P M} (h : Reachable F f s) : InvC F s := by
  induction h with
  | init => exact InvC.init
  | step hr hs ih => exact ih.step (InvA.reach hr) (InvB.reach hr) hs

end Podc.RDMAAgreement.RB
