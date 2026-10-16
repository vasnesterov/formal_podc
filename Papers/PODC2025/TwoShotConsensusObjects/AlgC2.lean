import Papers.PODC2025.TwoShotConsensusObjects.AlgC2Step

/-!
# Class `C₂`, sufficiency: objects of class `C₂` solve two-shot two-process consensus

**Theorem 2** of the paper for class `C₂` (Section 5.3): Algorithm 3 (with line 30 corrected,
see `AlgC2Alg.lean`) is a wait-free consensus algorithm using one two-shot copy of `O`, accessed
according to `m`, and read/write registers.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

variable {O : ObjSpec} {m : Fin 2 → Set O.Op} {s : O.State} {f g : O.Op} {c : ℕ → O.Op}
  {k : ℕ}

lemma act_out {l : LS O.Resp} (hl : 10 ≤ l.pc) :
    (algC2 s f g c k).act l = .out l.out := by
  obtain ⟨n, hn⟩ : ∃ n, l.pc = n + 10 := ⟨l.pc - 10, by omega⟩
  simp only [algC2, actC2, hn]

/-- The invariant is preserved by every (crash-free) event. -/
lemma inv_next (hk : 1 ≤ k) (hC : C2At O m s f g (3 ^ k) c) {C : Cfg (algC2 s f g c k)}
    {h : List (Fin 2 × O.Op)} (hI : Inv s f g c k C h) (q : Fin 2) :
    ∃ h', Inv s f g c k (C.next (.step q)) h' := by
  simp only [Cfg.next]
  have hpc := hI.1.pc q
  obtain ⟨n, hn⟩ : ∃ n, (C.loc q).pc = n := ⟨_, rfl⟩
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · interval_cases n
    · exact ⟨_, step0 hI q hn⟩
    · exact ⟨_, step1 hI q hn⟩
    · exact ⟨_, step2 hI q hn⟩
    · exact ⟨_, step3 hI q hn⟩
    · exact ⟨_, step4 hI q hn⟩
    · exact ⟨_, step5 hI q hn⟩
    · exact ⟨_, step6 hI q hn⟩
    · exact ⟨_, step7 hI q hn⟩
    · exact ⟨_, step8 hk hC hI q hn⟩
    · exact ⟨_, step9 hI q hn⟩
  · refine ⟨h, ?_⟩
    rw [stepP_of_out C (show C.Out q (C.loc q).out from act_out (by omega))]
    exact hI

lemma inv_run (hk : 1 ≤ k) (hC : C2At O m s f g (3 ^ k) c) (α : List (Ev 2)) (hα : CrashFree α)
    (C : Cfg (algC2 s f g c k)) (h : List (Fin 2 × O.Op)) (hI : Inv s f g c k C h) :
    ∃ h', Inv s f g c k (run C α) h' := by
  induction α generalizing C h with
  | nil => exact ⟨h, hI⟩
  | cons e α ih =>
    have hα' : CrashFree α := fun p hp => hα p (by simp [hp])
    rcases e with q | q
    · obtain ⟨h', hI'⟩ := inv_next hk hC hI q
      exact ih hα' _ _ hI'
    · exact absurd (by simp) (hα q)

lemma inv_reach (hk : 1 ≤ k) (hC : C2At O m s f g (3 ^ k) c) (x : Fin 2 → Bool)
    (α : List (Ev 2)) (hα : CrashFree α) :
    ∃ h, Inv s f g c k (run (initCfg (algC2 s f g c k) x) α) h :=
  inv_run hk hC α hα _ _ (inv_init hk x)

/-- An output state is reached only at `pc = 10`, with the output stored in the local state. -/
lemma out_spec {C : Cfg (algC2 s f g c k)} {h : List (Fin 2 × O.Op)} (hI : Inv s f g c k C h)
    {p : Fin 2} {v : Bool} (hout : C.Out p v) :
    h.head?.map Prod.fst = some (C.loc p).dec ∧ v = C.inp (C.loc p).dec := by
  have hpc := hI.1.pc p
  have h10 : (C.loc p).pc = 10 := by
    by_contra hne
    obtain ⟨n, hn⟩ : ∃ n, (C.loc p).pc = n := ⟨_, rfl⟩
    have hlt : n < 10 := by omega
    unfold Cfg.Out at hout
    interval_cases n <;> simp [algC2, actC2, hn] at hout
  have hact := act_out (s := s) (f := f) (g := g) (c := c) (k := k) (le_of_eq h10.symm)
  unfold Cfg.Out at hout
  rw [hact] at hout
  cases hout
  exact ⟨hI.1.dec p (by omega), hI.1.out p h10⟩

/-- Output states persist along crash-free executions. -/
lemma out_run {C : Cfg (algC2 s f g c k)} {p : Fin 2} {v : Bool} (hout : C.Out p v)
    (α : List (Ev 2)) (hα : CrashFree α) : (run C α).Out p v := by
  induction α generalizing C with
  | nil => exact hout
  | cons e α ih =>
    have hα' : CrashFree α := fun p hp => hα p (by simp [hp])
    rcases e with q | q
    · apply ih _ hα'
      by_cases hq : q = p
      · subst hq; simp only [Cfg.next]; rwa [stepP_of_out C hout]
      · unfold Cfg.Out; simp only [Cfg.next]; rw [stepP_loc_other C (Ne.symm hq)]; exact hout
    · exact absurd (by simp) (hα q)

lemma dec_final {C : Cfg (algC2 s f g c k)} {γ : List (Ev 2)} {v : Bool} (hγ : CrashFree γ)
    (hd : Dec C γ v) : ∃ p, (run C γ).Out p v := by
  obtain ⟨n, hn, p, hp⟩ := hd
  refine ⟨p, ?_⟩
  have := out_run hp (γ.drop n) (fun q hq => hγ q (List.mem_of_mem_drop hq))
  rwa [← run_append, List.take_append_drop] at this

set_option linter.unnecessarySeqFocus false in
/-- **Correctness of Algorithm 3** (Lemma 4 and Theorem 2 for class `C₂`). -/
theorem algC2_wf (hk : 1 ≤ k) (hC : C2At O m s f g (3 ^ k) c) :
    WFConsensus (algC2 s f g c k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x γ hγ v w hv hw
    obtain ⟨h, hI⟩ := inv_reach hk hC x γ hγ
    obtain ⟨p, hp⟩ := dec_final hγ hv
    obtain ⟨p', hp'⟩ := dec_final hγ hw
    obtain ⟨h1, hv1⟩ := out_spec hI hp
    obtain ⟨h2, hw1⟩ := out_spec hI hp'
    rw [hv1, hw1, Option.some.inj (h1.symm.trans h2)]
  · intro x γ hγ v hv
    obtain ⟨h, hI⟩ := inv_reach hk hC x γ hγ
    obtain ⟨p, hp⟩ := dec_final hγ hv
    obtain ⟨-, hv1⟩ := out_spec hI hp
    exact ⟨_, by rw [hv1, run_inp]; rfl⟩
  · intro x e p N hcf hinf _
    refine prog_of_rank (fun l : LS O.Resp => 10 - l.pc + 2 * (k - l.rs.length)) ?_ x e p N hcf hinf
    intro l i o κ r hact
    obtain ⟨n, hn⟩ : ∃ n, l.pc = n := ⟨_, rfl⟩
    rcases Nat.lt_or_ge n 10 with hlt | hge
    · interval_cases n <;> simp only [algC2, actC2, hn] at hact <;> cases hact <;>
        simp [hn] <;> split_ifs <;> simp <;> omega
    · have := hact.symm.trans (act_out (l := l) (by omega)); cases this

set_option linter.unnecessarySeqFocus false in
theorem algC2_twoShot : TwoShot (algC2 s f g c k) := by
  refine twoShot_of_budget (fun l _ => (if l.pc ≤ 1 then 1 else 0) + (if l.pc ≤ 6 then 1 else 0))
    (by intro p b k; simp [algC2]) ?_
  intro l i o κ r u hact
  obtain ⟨n, hn⟩ : ∃ n, l.pc = n := ⟨_, rfl⟩
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · interval_cases n <;> simp only [algC2, actC2, hn] at hact <;> cases hact <;>
      simp [hn] <;> split_ifs <;> simp <;> omega
  · have := hact.symm.trans (act_out (l := l) (by omega)); cases this

theorem algC2_allowed (hk : 1 ≤ k) (hC : C2At O m s f g (3 ^ k) c) :
    Allowed m (algC2 s f g c k) := by
  intro x α hα p u o κ hact
  obtain ⟨h, hI⟩ := inv_reach hk hC x α hα
  set C := run (initCfg (algC2 s f g c k) x) α
  have hid := hI.1.id p
  obtain ⟨n, hn⟩ : ∃ n, (C.loc p).pc = n := ⟨_, rfl⟩
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · interval_cases n <;> simp only [algC2, actC2, hn] at hact <;> cases hact
    · rw [hid]
      obtain ⟨-, hf, hg, -⟩ := hC
      fin_cases p <;> simp [hf, hg]
    · have hlen := hI.1.len2 p (by omega)
      have hb := hI.1.bnd p k
      rw [List.take_of_length_le (by omega)] at hb
      have := hC.2.2.2.1 _ hb
      rw [hid]; rwa [own_opOf] at this
  · have := hact.symm.trans (act_out (l := C.loc p) (by omega)); cases this

/-- **Sufficiency for class `C₂`** (Lemma 2, Algorithm 3, Lemmas 3–4, Theorem 2): if the
properties of class `C₂` hold, objects of type `(O, m)` solve two-shot two-process consensus. -/
theorem solvable_of_C2Cond (h : C2Cond O m) : Solvable O m := by
  obtain ⟨s, f, g, n, c, hc⟩ := c2Cond_iff.1 h
  obtain ⟨k, hk, c', hC⟩ := hc.pad
  exact ⟨Reg, Unit, inferInstance, inferInstance, inferInstance, RegS O.Resp,
    fun _ => isRW_register _ _, algC2 s f g c' k, algC2_wf hk hC, algC2_twoShot,
    algC2_allowed hk hC⟩

end TwoShotCons
