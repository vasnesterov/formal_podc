import Papers.PODC2014.DistributedUniversality.InvDStep

/-!
# An operation committed in round `ρ` is never proposed again from round `ρ + 2` on

This is the fact behind "at most one operation committed per round, and every operation is
committed in at most two consecutive rounds", used to show that an object with commits in
infinitely many rounds executes infinitely many operations (Lemma 6).
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

/-- Proposals of round `ρ'` differ from the value of every uniform round `ρ ≤ ρ' - 2`. -/
def NoRepeat (s : St n k) : Prop :=
  ∀ ρ' m j W, s.opRec ρ' m j = some W → ∀ ρ V, ρ + 2 ≤ ρ' → Unif s ρ m V → W ≠ V

theorem noRepeat_init : NoRepeat (init : St n k) := by
  intro ρ' m j W h; simp [init] at h

theorem NoRepeat.step (N : NoRepeat s) (hI : Inv M s) (hM : M.Good)
    (h : stepFn M s a = some s') : NoRepeat s' := by
  intro ρ' y j W hW ρ V hρ hU
  obtain ⟨I, B, C, D⟩ := hI
  have I' := I.step h
  by_cases hold : s.opRec ρ' y j = some W
  · have hle := (I.opRec_le _ _ _ _ hold).2
    have hlt : ρ < (s'.loc j).r := lt_of_lt_of_le (by omega)
      (le_trans hle (r_mono h (fun i => (I.init_r i).1) j))
    exact N ρ' y j W hold ρ V hρ (I.unif_pre_of_lt h hU hlt)
  · obtain ⟨rfl, hc⟩ := I.opRec_new h hW hold
    rcases hc with ⟨-, h1, -⟩ | ⟨hpc, h1, rfl⟩
    · omega
    · -- recorded at the end of round `ρ' - 1 ≥ ρ + 1`
      have hlt : ρ < (s.loc a.proc).r := by omega
      have hUp := I.unif_pre_of_lt (p := a.proc) h hU (by
        have := r_mono h (fun i => (I.init_r i).1) a.proc; omega)
      have hV : V ∈ (s.loc a.proc).hist y := by
        refine B.know a.proc ρ y V hUp ?_
        rcases Nat.lt_or_ge (ρ + 1) (s.loc a.proc).r with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨by omega, by simp [hpc]⟩
      intro e
      subst e
      exact D.oper_nin a.proc y (by simp [hpc]) hV

theorem Reachable.noRepeat (hM : M.Good) (hs : Reachable M s) : NoRepeat s := by
  induction hs with
  | refl => exact noRepeat_init
  | tail hr hst ih =>
    obtain ⟨a, ha⟩ := hst
    exact ih.step (Reachable.invAll hM hr) hM ha

end Podc.DistributedUniversality
