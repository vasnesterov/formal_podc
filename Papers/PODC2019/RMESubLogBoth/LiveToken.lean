import Papers.PODC2019.RMESubLogBoth.Safety
import Papers.PODC2019.RMESubLogBoth.LivePre

/-!
# Liveness, part 3: the right to the CS travels along the queue

Once no process is in the recovery code or in `RLock` any more (and no crash happens), the unique
holder of the right to the CS (`InH`) is an ancestor (or the node itself) of every waiting node;
it progresses, and when it releases its node the next node becomes the holder.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

/-- Nobody is in the recovery code, waiting for `RLock`, or in the CS of `RLock`. -/
def NoRec (c : Cfg k) : Prop :=
  ∀ q, preW c q = 0 ∧ (∀ x v, c.pc q ≠ .l24 x v) ∧ ¬ (c.pc q).InR

/-- The program counters outside the recovery code and `RLock`. -/
def PC.Plain : PC k → Prop
  | .rem | .l11 | .l13 _ | .l14 _ _ | .l15 _ _ | .l25 _ _ | .l26 _ | .cs _ | .l28 _ | .l29 => True
  | _ => False

lemma NoRec.plain {c : Cfg k} (h : NoRec c) (q : Fin k) : (c.pc q).Plain := by
  obtain ⟨h1, h2, h3⟩ := h q
  cases hq : c.pc q <;> simp_all [preW, PC.Plain, PC.InR]
  split_ifs at h1

section
variable {c : Cfg k} {own : ℕ → ℕ}

/-- Under `NoRec`, a node that is behind a node is behind a node that is behind ... until it
reaches a holder of the right to the CS. -/
lemma exists_holder (hG : Glob c own) (hL : ∀ q, LI c own q) (hNR : NoRec c) :
    ∀ y z, c.Bh y z → ∃ h, c.InH h ∧ ReflTransGen c.Bh y h := by
  intro y
  induction y using hG.wf.induction with
  | _ y ih =>
    intro z hyz
    by_cases hz : c.Rel z
    · exact ⟨y, ⟨(by obtain ⟨q, hq, -⟩ := hyz; exact ⟨q, hq⟩), .inr (.inl ⟨z, hyz, hz⟩)⟩, .refl⟩
    · -- `z` is the node of some port
      have hzlt := hG.bhLt y z hyz
      have hzact : c.Act z := by
        rcases Nat.eq_zero_or_pos z with h0 | h0
        · exact absurd (h0 ▸ rel_special hG) hz
        · rcases hG.table z h0 hzlt with h1 | h1
          · exact h1
          · exact absurd h1 hz
      obtain ⟨q, hq⟩ := hzact
      have hLq := hL q
      unfold LI at hLq
      have hpl := hNR.plain q
      cases hpc : c.pc q with
      | l13 a =>
        rw [hpc] at hLq; rw [hLq.1] at hq; cases hq
        exact absurd hyz (hLq.2.2.2.2.1 y)
      | l14 a m =>
        rw [hpc] at hLq; rw [hLq.1] at hq; cases hq
        have hb : c.Bh z m := ⟨q, hLq.1, Cfg.vp_of_ovr_some (by simp [hpc])⟩
        obtain ⟨h, hh, hr⟩ := ih z hyz m hb
        exact ⟨h, hh, .head hyz hr⟩
      | l15 a m =>
        rw [hpc] at hLq; rw [hLq.1] at hq; cases hq
        obtain ⟨h, hh, hr⟩ := ih z hyz m (bh_of_pred hG hL hLq.2.1)
        exact ⟨h, hh, .head hyz hr⟩
      | l25 a v =>
        rw [hpc] at hLq; rw [hLq.1] at hq; cases hq
        obtain ⟨-, h2, ⟨m, rfl⟩, -⟩ := hLq
        obtain ⟨h, hh, hr⟩ := ih z hyz m (bh_of_pred hG hL h2)
        exact ⟨h, hh, .head hyz hr⟩
      | l26 a =>
        rw [hpc] at hLq; rw [hLq.1] at hq; cases hq
        obtain ⟨-, ⟨m, h2, -⟩, -⟩ := hLq
        obtain ⟨h, hh, hr⟩ := ih z hyz m (bh_of_pred hG hL h2)
        exact ⟨h, hh, .head hyz hr⟩
      | cs a =>
        rw [hpc] at hLq; rw [hLq.1] at hq; cases hq
        exact ⟨z, ⟨⟨q, hLq.1⟩, .inl hLq.2.1⟩, .single hyz⟩
      | l28 a =>
        rw [hpc] at hLq; rw [hLq.1] at hq; cases hq
        exact ⟨z, ⟨⟨q, hLq.1⟩, .inr (.inr ⟨hLq.2.1, hLq.2.2.1, .inl ⟨y, hyz⟩⟩)⟩, .single hyz⟩
      | l29 =>
        rw [hpc] at hLq; obtain ⟨a, ha, hr⟩ := hLq
        rw [ha] at hq; cases hq; exact absurd hr hz
      | rem => rw [hpc] at hLq; rw [hLq] at hq; cases hq
      | l11 => rw [hpc] at hLq; rw [hLq] at hq; cases hq
      | _ => rw [hpc] at hpl; exact absurd hpl (by simp [PC.Plain])

end

end Podc.RMESubLogBoth
