import Papers.PODC2019.RecoverableHierarchy.Fig1Inv

/-!
# Figure 1 of Golab (PODC 2019): Theorem 1 (= Theorem 11) and Lemma 8

The algorithm of Figure 1 (`Fig1Alg.lean`) solves 2-process recoverable consensus with
arbitrarily many simultaneous crash-recovery failures (`theorem1`), and accesses the consensus
object `C` at most once per process in every execution (`lemma8`).
-/

namespace Podc.RecoverableHierarchy.Fig1

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable PC

/-! ## Access counts in the simultaneous-failure model -/

section General

variable {ι : Type} [DecidableEq ι] {T' : ι → ObjSpec} {n : ℕ} {A : Alg n T'}

/-- Number of operations applied by process `p` to object `i` along the execution `α` from `C`
in the simultaneous-failure model (the analogue of CSLib's `accCount`).
-- CSLib candidate (together with `SEv`/`srun`). -/
def saccCount : Cfg A → List (SEv n) → Fin n → ι → ℕ
  | _, [], _, _ => 0
  | C, e :: α, p, i =>
    (if e = .step p ∧ objOf C p = some i then 1 else 0) + saccCount (snext C e) α p i

/-- Embedding of crash-free simultaneous-model events into CSLib's events (`crashAll` is sent
to an arbitrary crash; it never occurs where this is used). -/
def toEv (p : Fin n) : SEv n → Ev n
  | .step q => .step q
  | .crashAll => .crash p

lemma run_map_toEv (p : Fin n) (C : Cfg A) (l : List (SEv n)) (hl : ∀ e ∈ l, e ≠ .crashAll) :
    run C (l.map (toEv p)) = srun C l := by
  induction l generalizing C with
  | nil => rfl
  | cons e l ih =>
    rcases e with q | _
    · exact ih _ (fun e he => hl e (by simp [he]))
    · exact absurd rfl (hl _ (by simp))

lemma spre_succ (e : ℕ → SEv n) (t : ℕ) : spre e (t + 1) = spre e t ++ [e t] := by
  simp [spre, List.range_succ]

lemma spre_add (e : ℕ → SEv n) (a b : ℕ) :
    spre e (a + b) = spre e a ++ spre (fun i => e (a + i)) b := by
  induction b with
  | zero => simp [spre]
  | succ b ih => rw [← Nat.add_assoc, spre_succ, ih, spre_succ, List.append_assoc]

end General

/-! ## Bridging lemmas -/

lemma astep_x (s : St) (m : Fin 2) : (astep s m).x = s.x := by
  unfold astep; split <;> rfl

lemma foldl_x (s : St) (α : List (SEv 2)) : (α.foldl sstep s).x = s.x := by
  induction α generalizing s with
  | nil => rfl
  | cons e α ih =>
    rw [List.foldl_cons, ih]
    cases e <;> simp [sstep, astep_x]

lemma astep_other (s : St) {m k : Fin 2} (hk : k ≠ m) :
    (astep s m).pc k = s.pc k ∧ (astep s m).P k = s.P k := by
  unfold astep; split <;> simp [Function.update_of_ne hk]

lemma objOf_eq {C : Cfg alg} (hC : WF C) (p : Fin 2) :
    objOf C p = some Obj.C ↔ (view C).pc p = .l4 := by
  unfold objOf
  rw [loc_eq hC p]
  cases (view C).pc p <;> simp [act]

/-- Is `p` at line 4 (about to access `C`)? -/
def at4 (s : St) (p : Fin 2) : ℕ := if s.pc p = .l4 then 1 else 0

/-- Has `p` recorded its proposal? -/
def recd (s : St) (p : Fin 2) : ℕ := if s.P p = none then 0 else 1

/-- Does event `e` make `p` access `C`? -/
def acc (e : SEv 2) (s : St) (p : Fin 2) : ℕ := if e = .step p ∧ s.pc p = .l4 then 1 else 0

lemma recd_le (s : St) (p : Fin 2) : recd s p ≤ 1 := by unfold recd; split_ifs <;> simp

/-- One step of the potential argument for Lemma 8: the potential `recd - at4` increases by at
least the number of accesses to `C`. -/
lemma count_step {s : St} (h : Inv s) (p : Fin 2) (e : SEv 2) :
    acc e s p + at4 (sstep s e) p + recd s p ≤ recd (sstep s e) p + at4 s p := by
  unfold acc at4 recd
  rcases e with m | _
  · by_cases hm : p = m
    · subst hm
      rcases hpc : s.pc p with _ | a | _ | _ | d | _ | _ | a | _ | a | _ | d | d | d | d | d <;>
        simp only [sstep, astep, hpc]
      · simp
      · simp [k2]; split_ifs <;> simp
      · have hPm : s.P p = none := h.loc' hpc
        simp [hPm]
      · have hPm : s.P p ≠ none := h.loc' hpc
        simp [hPm]
      all_goals first
        | (simp; done)
        | (simp [k7]; cases s.D <;> simp)
        | (simp [k9]; split_ifs <;> cases a <;> simp)
        | (simp [k11]; split_ifs <;> cases s.P (oth p) <;> simp)
        | (simp [k13])
    · obtain ⟨h1, h2⟩ := astep_other s hm
      simp only [sstep, h1, h2]
      have : (SEv.step m = SEv.step p) = False := by simp [Ne.symm hm]
      simp only [this, false_and, ite_false]
      omega
  · simp only [sstep, reduceCtorEq, false_and, ite_false]
    split_ifs <;> simp_all

/-! ## Main results -/

/-- **Lemma 8** of [Golab, PODC 2019] (Appendix A): in any execution (with arbitrarily many
simultaneous crash-recovery failures), the consensus object `C` is accessed at most once by
each process. -/
theorem lemma8 (x : Fin 2 → Bool) (α : List (SEv 2)) (p : Fin 2) :
    saccCount (initCfg alg x) α p Obj.C ≤ 1 := by
  -- potential: `recd - at4` bounds the number of accesses so far
  have key : ∀ (α : List (SEv 2)) (C : Cfg alg), WF C → Inv (view C) →
      saccCount C α p Obj.C + at4 (view (srun C α)) p + recd (view C) p ≤
        recd (view (srun C α)) p + at4 (view C) p := by
    intro α
    induction α with
    | nil => intro C _ _; rw [srun_nil]; simp only [saccCount]; omega
    | cons e α ih =>
      intro C hC hI
      have hC' := wf_snext hC e
      have hI' : Inv (view (snext C e)) := by rw [view_snext hC]; exact hI.sstep e
      have h1 := ih _ hC' hI'
      have h2 := count_step hI p e
      rw [← view_snext hC] at h2
      have h3 : (if e = .step p ∧ objOf C p = some Obj.C then 1 else 0) = acc e (view C) p := by
        unfold acc; simp only [objOf_eq hC]
      rw [srun_cons]
      simp only [saccCount, h3]
      omega
  have := key α (initCfg alg x) (wf_init x) (by rw [view_init]; exact inv_s0 x)
  have h0 : recd (view (initCfg alg x)) p = 0 := rfl
  have h0' : at4 (view (initCfg alg x)) p = 0 := rfl
  have h1 := recd_le (view (srun (initCfg alg x) α)) p
  omega

lemma view_srun_init (x : Fin 2 → Bool) (γ : List (SEv 2)) :
    WF (srun (initCfg alg x) γ) ∧ view (srun (initCfg alg x) γ) = γ.foldl sstep (s0 x) := by
  have := wf_view_srun (wf_init x) γ
  rw [view_init] at this
  exact this

lemma inv_srun (x : Fin 2 → Bool) (γ : List (SEv 2)) : Inv (view (srun (initCfg alg x) γ)) := by
  rw [(view_srun_init x γ).2]; exact (inv_s0 x).foldl γ

/-- The fallback of `k13` (reading `P[1] = ⊥` at line 14) never happens: in every reachable
configuration, a process at lines 13–14 sees both proposals recorded and `D = ⊥`. -/
lemma l13_recorded (x : Fin 2 → Bool) (γ : List (SEv 2)) (k : Fin 2)
    (hk : (view (srun (initCfg alg x) γ)).pc k = .l13) :
    (view (srun (initCfg alg x) γ)).P 0 ≠ none ∧ (view (srun (initCfg alg x) γ)).P 1 ≠ none := by
  have h : LP _ k .l13 := (inv_srun x γ).loc' hk
  simp only [LP] at h
  fin_cases k <;> simp_all

/-- Every value output at some point of an execution is the forced value at its end. -/
lemma good_of_out {x : Fin 2 → Bool} {γ : List (SEv 2)} {k : ℕ} {p : Fin 2} {v : Bool}
    (hk : (srun (initCfg alg x) (γ.take k)).Out p v) : Good (view (srun (initCfg alg x) γ)) v := by
  have hwf := (view_srun_init x (γ.take k)).1
  have hg : Good (view (srun (initCfg alg x) (γ.take k))) v :=
    good_of_ret (inv_srun x _) ((out_iff hwf p v).mp hk)
  have hsplit : srun (initCfg alg x) γ = srun (srun (initCfg alg x) (γ.take k)) (γ.drop k) := by
    rw [← srun_append, List.take_append_drop]
  rw [hsplit, (wf_view_srun hwf _).2]
  exact hg.foldl (inv_srun x _) _

lemma rank_lt (l : Loc) (i : Obj) (o : (T i).Op) (κ : (T i).Resp → Loc) (r : (T i).Resp)
    (h : act l = .access i o κ) : (κ r).2.2.rank < l.2.2.rank := by
  obtain ⟨k, v, pc⟩ := l
  cases pc <;> simp only [act, reduceCtorEq] at h <;> cases h <;> simp [PC.rank]
  · unfold k2; split_ifs <;> simp
  · unfold k7; cases r <;> simp
  · rename_i a; unfold k9; split_ifs <;> cases a <;> simp
  · unfold k11; split_ifs <;> cases r <;> simp
  · simp [k13]

/-- **Theorem 1** (= Theorem 11) of [Golab, PODC 2019]: the algorithm of Figure 1 (with `C` an
atomic consensus object) solves 2-process recoverable consensus with arbitrarily many
simultaneous crash-recovery failures: agreement (all outputs of an execution are equal, also
outputs of different incarnations of one process), validity, and recoverable wait-freedom. -/
theorem theorem1 : SolvesS alg where
  agree x γ v w := by
    rintro ⟨k, -, p, hp⟩ ⟨k', -, p', hp'⟩
    exact Good.unique (inv_srun x γ) (good_of_out hp) (good_of_out hp')
  valid x γ v := by
    rintro ⟨k, -, p, hp⟩
    obtain ⟨q, hq⟩ := Good.valid (inv_srun x γ) (good_of_out hp)
    refine ⟨q, ?_⟩
    rw [(view_srun_init x γ).2, foldl_x] at hq
    exact hq
  prog x e p N hinf hN := by
    set C0 := srun (initCfg alg x) (spre e N)
    have hinf' : ∀ M, ∃ t ≥ M, toEv p (e (N + t)) = .step p := by
      intro M
      obtain ⟨t, ht, he⟩ := hinf (N + M)
      exact ⟨t - N, by omega, by rw [show N + (t - N) = t by omega, he]; rfl⟩
    have hN' : ∀ t ≥ 0, toEv p (e (N + t)) ≠ .crash p := by
      intro t _
      rcases he : e (N + t) with q | _
      · simp [toEv]
      · exact absurd he (hN _ (by omega))
    obtain ⟨t, -, v, hv⟩ := prog_of_rank (A := alg) (fun l => l.2.2.rank)
      (fun l i o κ r h => rank_lt l i o κ r h) C0 (fun t => toEv p (e (N + t))) p 0 hinf' hN'
    refine ⟨N + t, by omega, v, ?_⟩
    have hpre : pre (fun t => toEv p (e (N + t))) t = (spre (fun i => e (N + i)) t).map (toEv p) := by
      simp [pre, spre]
    rw [hpre, run_map_toEv] at hv
    · rw [spre_add, srun_append]; exact hv
    · intro e' he'
      simp only [spre, List.mem_map, List.mem_range] at he'
      obtain ⟨i, -, rfl⟩ := he'
      exact hN _ (by omega)

end Podc.RecoverableHierarchy.Fig1
