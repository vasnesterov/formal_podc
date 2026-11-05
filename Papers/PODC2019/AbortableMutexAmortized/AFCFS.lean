import Papers.PODC2019.AbortableMutexAmortized.PaperInv
import Papers.PODC2019.AbortableMutexAmortized.Starvation

/-!
# Theorem 4.2 (Airline FCFS)

The paper's AFCFS: "If passage `π` by `p` A-precedes passage `π'` by `p'` (`p` completes the
doorway in the last attempt of `π` before `p'` begins `π'`), then `p'` does not enter the CS in `π'`
before `p` enters the CS in `π`."

* **As stated it is false** (`afcfs_literal_false`): if the last attempt of `π` is aborted and
  `p` makes no further attempt, `p` never enters the CS in `π`, yet `p'` (behind `p` in the queue)
  splices `p`'s node out and enters the CS. No starvation-free abortable lock can satisfy the
  literal definition (a process that aborts after its doorway and never returns would block
  everybody who starts later forever).
* **Corrected version** (`theorem_4_2`): `p'` does not enter the CS (line 7) before `p` enters the
  CS *or the Abort section* (lines 9–11). With the doorway = lines 1–2 (`p` is at line 3 right after
  completing it), this holds for every execution. This is what the paper's proof shows (while `p` is
  in `Q` ahead of `p'`, only `q₁` can be at line 7).
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

/-! ## The literal property fails -/

/-- A run with `r = 0`, `p = 1`, `p' = 2`: `r` enters the CS; `p` completes its doorway, waits,
aborts (lines 9, 10) and returns to the Remainder; `p'` starts its first attempt, splices out `p`'s
node, and enters the CS when `r` exits. -/
def afcfsRun : List (Fin 3 × Bool) :=
  [(0, false), (0, false), (0, false),               -- r: lines 1, 2, 3 → CS
   (1, false), (1, false), (1, false),               -- p: lines 1, 2 (doorway), 3 → wait
   (1, true), (1, false),                            -- p aborts: lines 9, 10 → Remainder
   (2, false), (2, false), (2, false),               -- p': lines 1, 2, 3 (splices p's node)
   (0, false),                                       -- r: line 7 (exit)
   (2, false)]                                       -- p': line 6 → CS

/-- Configuration after the first `k` steps of `afcfsRun`. -/
def afcfsCfg (k : ℕ) : State 3 := run init (afcfsRun.take k)

/-- **Theorem 4.2 as stated is false.** In `afcfsRun`: `p = 1` makes exactly one attempt (one step at
line 1), which ends by an abort (line 10 back to the Remainder) and contains no CS; `p` completes the
doorway of this (last) attempt (it is at line 3 after step 5) before `p' = 2` begins its first
attempt (step 9); then `p'` enters the CS while `p` is never at line 7. So `p`'s passage `π` (its
single attempt) A-precedes `p'`'s first passage `π'`, and `p'` enters the CS in `π'` although `p`
never enters the CS in `π`. -/
theorem afcfs_literal_false :
    -- `p` makes exactly one attempt in the run
    ((List.range 13).filter (fun k => (afcfsRun[k]!).1 = 1 ∧ (afcfsCfg k).pc 1 = .l1)).length = 1 ∧
    -- it completes the doorway (lines 1, 2) after 5 steps
    (afcfsCfg 5).pc 1 = .l3 ∧
    -- `p'` takes no step before step 9, and begins its first attempt then
    (∀ k < 8, (afcfsRun[k]!).1 ≠ 2) ∧ (afcfsCfg 8).pc 2 = .l1 ∧
    -- `p`'s attempt ends by an abort: line 10 back to the Remainder
    (afcfsCfg 7).pc 1 = .l10 ∧ (afcfsCfg 8).pc 1 = .l1 ∧
    -- `p` is never in the CS, `p'` ends in the CS
    (∀ k ≤ 13, (afcfsCfg k).pc 1 ≠ .l7) ∧ (afcfsCfg 13).pc 2 = .l7 := by
  decide +kernel

/-! ## The corrected property holds -/

/-- `p'` begins a passage at time `t'`: it is in the Remainder section, and either it has never taken a
step, or its last step completed an attempt through the Exit section (a step at line 7 or 8). -/
def PassageStart (σ : ℕ → Fin n × Bool) (q : Fin n) (t' : ℕ) : Prop :=
  (exec σ t').pc q = .l1 ∧
    ((∀ s < t', (σ s).1 ≠ q) ∨
      ∃ s < t', (σ s).1 = q ∧ ((exec σ s).pc q = .l7 ∨ (exec σ s).pc q = .l8) ∧
        ∀ s', s < s' → s' < t' → (σ s').1 ≠ q)

theorem Qof_init : Qof (init : State n) = [] := by
  obtain ⟨Q, a0, hs, -⟩ := (inv_init : Inv (init : State n))
  have hQ : Q = [] := by
    cases Q with
    | nil => rfl
    | cons q R =>
      have := (hs.mem q).1 (by simp)
      simp [InQ, init, PC.act, PC.ab] at this
  subst hQ; exact hs.Qof_eq.1

/-- A step of another process does not put `q` into the queue. -/
theorem not_mem_step {s : State n} (h : Inv s) {q π : Fin n} (hq : q ≠ π) (ab : Bool)
    (hm : q ∉ Qof s) : q ∉ Qof (step s π ab) := by
  have hqs := h.qstep π ab
  revert hm
  generalize Qof s = Q at hqs
  generalize Qof (step s π ab) = Q' at hqs
  intro hm
  cases hqs with
  | same => exact hm
  | enq => simp [hm, hq]
  | splice L x R => simp_all
  | deq R => simp_all

/-- After a step at line 7 or 8 (completing the Exit section) a process is not in the queue. -/
theorem not_InQ_after_exit {s : State n} (h : Inv s) {q : Fin n} (ab : Bool)
    (hq : s.pc q = .l7 ∨ s.pc q = .l8) : ¬ InQ (step s q ab) q := by
  have hl := h.loc
  have hs := h.struct
  rcases hq with hq | hq
  · have e : step s q ab = l7Upd s q := by unfold step; rw [hq]; rfl
    rw [e]
    have hpa := hl.i10 q hq
    have ha0 := hl.i9b q hpa hq
    simp only [InQ, l7Upd_pc, Function.update_self]
    split_ifs with ho
    · simp only [PC.act_l1, PC.ab_l1, Bool.false_eq_true, true_and, false_or]
      simp only [l7Upd_node, l7Upd_mynode, Function.update_self, l7Upd_pred]
      rw [hpa, Function.update_of_ne (hs.a0_ne q).symm]
      rcases ha0 with h' | h' <;> rw [h'] <;> simp
    · simp
  · have e : step s q ab = wake s q := by unfold step; rw [hq]
    rw [e]
    simp only [InQ, wake, Function.update_self, PC.act_l1, PC.ab_l1, Bool.false_eq_true,
      true_and, false_or]
    rcases hl.i6b q hq with h' | h' <;> rw [h'] <;> simp

theorem not_mem_of_passageStart (σ : ℕ → Fin n × Bool) {q : Fin n} {t' : ℕ}
    (h : PassageStart σ q t') : q ∉ Qof (exec σ t') := by
  -- `q` stays out of the queue while it takes no step
  have stay : ∀ s k, q ∉ Qof (exec σ s) → (∀ j < k, (σ (s + j)).1 ≠ q) →
      q ∉ Qof (exec σ (s + k)) := by
    intro s k hs hk
    induction k with
    | zero => exact hs
    | succ k ih =>
      have := not_mem_step (reachable_exec σ (s + k)).inv (Ne.symm (hk k (by omega)))
        (σ (s + k)).2 (ih (fun j hj => hk j (by omega)))
      exact this
  rcases h.2 with h0 | ⟨s, hs, hsq, hpc, hlast⟩
  · have := stay 0 t' (by rw [show exec σ 0 = init from rfl, Qof_init]; simp)
      (fun j hj => by simpa using h0 j (by omega))
    simpa using this
  · have h1 : q ∉ Qof (exec σ (s + 1)) := by
      intro hm
      have hinv := (reachable_exec σ (s + 1)).inv
      have := (hinv.mem_Qof).1 hm
      change InQ (step (exec σ s) (σ s).1 (σ s).2) q at this
      rw [hsq] at this
      exact not_InQ_after_exit (reachable_exec σ s).inv _ hpc this
    have := stay (s + 1) (t' - (s + 1)) h1 (fun j hj => hlast (s + 1 + j) (by omega) (by omega))
    rwa [Nat.add_sub_cancel' (by omega)] at this

/-- One step of `p` from the Try section: it stays in the Try section, enters the CS, or (aborting)
reaches line 10. -/
theorem try_step_any {s : State n} {p : Fin n} (hp : InTry (s.pc p)) (ab : Bool) :
    InTry ((step s p ab).pc p) ∨ (step s p ab).pc p = .l7 ∨ (step s p ab).pc p = .l10 := by
  unfold InTry at hp ⊢
  rcases hp with h | h | h | h <;> cases ab <;>
    simp [step, h, fasPred, loopPC, line9] <;> (try split) <;> (try split) <;> simp_all

/-- "`a` is before `b` in `Q`". -/
def Before (Q : List (Fin n)) (a b : Fin n) : Prop := [a, b].Sublist Q

theorem before_step {π p p' : Fin n} {Q Q' : List (Fin n)} (h : QStep π Q Q') (hnd : Q.Nodup)
    (hnd' : Q'.Nodup) (hp : p ∈ Q) (hp' : p ∈ Q') (hne : p ≠ p')
    (hb : p' ∉ Q ∨ Before Q p p') : p' ∉ Q' ∨ Before Q' p p' := by
  have keep : ∀ x, x ≠ p → x ≠ p' → Before Q p p' → Before (Q.erase x) p p' := by
    intro x h1 h2 hb
    have := hb.erase x
    rwa [List.erase_of_not_mem (by simp; exact ⟨h1, h2⟩)] at this
  cases h with
  | same => exact hb
  | enq =>
    rcases hb with hb | hb
    · by_cases e : π = p'
      · subst e; right
        exact List.Sublist.append (List.singleton_sublist.2 hp) (List.Sublist.refl _)
      · left; simp [hb, Ne.symm e]
    · exact Or.inr (hb.trans (List.sublist_append_left _ _))
  | splice L x R =>
    have hxL : x ∉ L := fun hx => by
      have := (List.nodup_append.1 hnd).2.2 x hx x (by simp); exact this rfl
    have he : (L ++ x :: π :: R).erase x = L ++ π :: R := by
      rw [List.erase_append_right _ hxL, List.erase_cons_head]
    rcases hb with hb | hb
    · left; intro hm; apply hb; simp at hm ⊢; tauto
    · by_cases e : x = p'
      · subst e; left
        intro hm
        have hR : x ∉ π :: R := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
        simp at hm; rcases hm with hm | hm
        · exact hxL hm
        · exact hR (by simpa using hm)
      · have exp : x ≠ p := by
          rintro rfl
          have hR : x ∉ π :: R := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
          simp at hp'; rcases hp' with hm | hm
          · exact hxL hm
          · exact hR (by simpa using hm)
        right; rw [← he]; exact keep x exp e hb
  | deq _ =>
    have hπR : π ∉ Q' := (List.nodup_cons.1 hnd).1
    rcases hb with hb | hb
    · left; intro hm; exact hb (by simp [hm])
    · by_cases e : π = p'
      · subst e; exact Or.inl hπR
      · have exp : π ≠ p := fun e' => hπR (e' ▸ hp')
        right
        have := keep π exp e hb
        rwa [List.erase_cons_head] at this

/-- **Theorem 4.2 (AFCFS), corrected.** If `p` completes its doorway (lines 1–2; it is then at
line 3) at time `T`, and `p'` begins a passage at a later time `t'`, then `p'` does not enter the CS
(line 7) before `p` enters the CS or the Abort section (lines 9–11). -/
theorem theorem_4_2 (σ : ℕ → Fin n × Bool) {p p' : Fin n} (hne : p ≠ p') {T t' u : ℕ}
    (hT : (exec σ T).pc p = .l3) (hTt : T ≤ t') (hstart : PassageStart σ p' t') (htu : t' ≤ u)
    (hu : (exec σ u).pc p' = .l7) :
    ∃ w, T ≤ w ∧ w ≤ u ∧ ((exec σ w).pc p = .l7 ∨ (exec σ w).pc p = .l9 ∨
      (exec σ w).pc p = .l10 ∨ (exec σ w).pc p = .l11) := by
  by_contra hno
  push_neg at hno
  -- `p` stays in the Try section during `[T, u]`
  have htry : ∀ k, T + k ≤ u → InTry ((exec σ (T + k)).pc p) := by
    intro k
    induction k with
    | zero => intro _; simp [hT, InTry]
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      change InTry ((step (exec σ (T + k)) (σ (T + k)).1 (σ (T + k)).2).pc p)
      by_cases hπ : (σ (T + k)).1 = p
      · rw [hπ]
        rcases try_step_any hprev (σ (T + k)).2 with h | h | h
        · exact h
        · exfalso
          have := (hno (T + k + 1) (by omega) hk).1
          apply this; change (step (exec σ (T + k)) (σ (T + k)).1 (σ (T + k)).2).pc p = _
          rw [hπ]; exact h
        · exfalso
          have := (hno (T + k + 1) (by omega) hk).2.2.1
          apply this; change (step (exec σ (T + k)) (σ (T + k)).1 (σ (T + k)).2).pc p = _
          rw [hπ]; exact h
      · rw [sf_pc_ne (Ne.symm hπ)]; exact hprev
  have hmemp : ∀ v, T ≤ v → v ≤ u → p ∈ Qof (exec σ v) := by
    intro v hv hvu
    have := htry (v - T) (by omega)
    rw [Nat.add_sub_cancel' hv] at this
    refine ((reachable_exec σ v).inv.mem_Qof).2 (Or.inl ?_)
    unfold InTry at this; rcases this with h | h | h | h <;> simp [h]
  -- `p'` is never ahead of `p` during `[t', u]`
  have hord : ∀ k, t' + k ≤ u →
      p' ∉ Qof (exec σ (t' + k)) ∨ Before (Qof (exec σ (t' + k))) p p' := by
    intro k
    induction k with
    | zero => intro _; exact Or.inl (not_mem_of_passageStart σ hstart)
    | succ k ih =>
      intro hk
      have hinv := (reachable_exec σ (t' + k)).inv
      have hinv' := (reachable_exec σ (t' + k + 1)).inv
      exact before_step (hinv.qstep (σ (t' + k)).1 (σ (t' + k)).2) hinv.struct.ok.nodup
        hinv'.struct.ok.nodup (hmemp _ (by omega) (by omega)) (hmemp _ (by omega) (by omega))
        hne (ih (by omega))
  have hfin := hord (u - t') (by omega)
  rw [Nat.add_sub_cancel' htu] at hfin
  have hinv := (reachable_exec σ u).inv
  have hp'Q : p' ∈ Qof (exec σ u) := (hinv.mem_Qof).2 (InQ.of_pc hu rfl)
  rcases hfin with hfin | hfin
  · exact hfin hp'Q
  · -- `p'` at line 7 is the head of the queue
    obtain ⟨R, hR⟩ := hinv.struct.ok.head hp'Q (hinv.loc.i10 p' hu)
    have hnd := hinv.struct.ok.nodup
    rw [hR] at hfin hnd
    unfold Before at hfin
    cases hfin with
    | cons _ h => exact (List.nodup_cons.1 hnd).1 (h.subset (by simp))
    | cons_cons _ h => exact hne rfl

end Podc.AbortableMutexAmortized
