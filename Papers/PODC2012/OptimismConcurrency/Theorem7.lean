import Papers.PODC2012.OptimismConcurrency.Lookahead

/-!
# Theorem 7 (part 2 of Theorem 2) is false

`lookahead_classP`: the lookahead reader–writer-lock implementation `I_LA` (`Lookahead.lean`) is
in the class `P`: it is an implementation of `(LL, set)` run by `LL` clients, every history is
LS-linearizable, it is pessimistic (never returns `⊥`), deadlock-free (strong form) and honest.
`lookahead_accepts`: it accepts the schedule `σ` of Figure 2(a).
`theorem_7_false`: hence the first half of Theorem 7 ("no implementation in `P` accepts `σ`")
is false.
-/

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

lemma step_of_mem {H : LHist ℕ} {e : LEv ℕ} (h : H ++ [e] ∈ I_LA) :
    ∃ c c', laRun LACfg.init H = some c ∧ laStep c e = some c' := by
  obtain ⟨c', h⟩ := mem_I_LA.1 h
  rw [laRun_concat] at h
  cases hH : laRun LACfg.init H with
  | none => rw [hH] at h; cases h
  | some c => rw [hH, Option.bind_some] at h; exact ⟨c, c', rfl, h⟩

lemma mem_of_step {H : LHist ℕ} {e : LEv ℕ} {c : LACfg} (hc : laRun LACfg.init H = some c)
    (h : (laStep c e).isSome) : H ++ [e] ∈ I_LA := by
  obtain ⟨c', h⟩ := Option.isSome_iff_exists.1 h
  exact mem_I_LA.2 ⟨c', by rw [laRun_concat, hc, Option.bind_some, h]⟩

lemma fresh_iff {H : LHist ℕ} {c : LACfg} (hI : LAInv H c) (y : Loc) :
    Fresh H y ↔ y ≠ headL ∧ y ≠ tailL ∧ y ∉ c.used := by
  unfold Fresh
  rw [hI.used]
  simp

/-! ## `I_LA` is an implementation -/

theorem lookahead_isImpl : IsImpl I_LA where
  nil_mem := rfl
  prefix_closed H e h := by
    obtain ⟨c, -, hc, -⟩ := step_of_mem h
    exact mem_I_LA.2 ⟨c, hc⟩
  moves H e h := by
    obtain ⟨c, c', hc, h⟩ := step_of_mem h
    have hI := laRun_inv H c hc
    rcases laStep_some h with ⟨p, o, rfl, hcl, rfl⟩ | ⟨p, y, o, s, rfl, hcl, ha, rfl⟩ |
      ⟨p, y, n, o, s, rfl, hcl, ha, rfl⟩ | ⟨p, r, o, s, rfl, hcl, ha, rfl⟩ |
      ⟨p, n, o, s, y, rfl, hcl, -, -, rfl⟩ | ⟨p, n, o, s, y, rfl, hcl, -, -, -, -, rfl⟩ |
      ⟨p, n, o, s, y, rfl, hcl, -, -, -, -, -, rfl⟩ | ⟨p, y, n, o, s, rfl, hcl, rfl⟩
    · left; show clientSt H p = .idle; rw [← hI.cl]; exact hcl
    · left; exact ⟨o, s, by rw [← hI.cl]; exact hcl, ha⟩
    · left; refine ⟨o, s, by rw [← hI.cl]; exact hcl, ?_⟩
      rcases ha with ha | ⟨ha, h1, h2, h3⟩
      · exact Or.inl ha
      · exact Or.inr ⟨ha, (fresh_iff hI y).2 ⟨h1, h2, h3⟩⟩
    · left; exact ⟨o, s, by rw [← hI.cl]; exact hcl, ha⟩
    · right; exact ⟨o, s, y, by rw [← hI.cl]; exact hcl⟩
    · right; exact ⟨o, s, y, by rw [← hI.cl]; exact hcl⟩
    · right; exact ⟨o, s, y, by rw [← hI.cl]; exact hcl⟩
    · right; exact ⟨o, s, y, n, by rw [← hI.cl]; exact hcl⟩
  receptive H hH e hm := by
    obtain ⟨c, hc⟩ := mem_I_LA.1 hH
    have hI := laRun_inv H c hc
    refine mem_of_step hc ?_
    cases e with
    | inv p x o =>
      have hcl : c.cl p = .idle := by rw [hI.cl]; exact hm
      simp [laStep, hcl]
    | rinv p x y =>
      obtain ⟨o, s, h1, h2⟩ := hm
      rw [← hI.cl] at h1
      simp [laStep, h1, h2]
    | winv p x y n =>
      obtain ⟨o, s, h1, h2⟩ := hm
      rw [← hI.cl] at h1
      have h2' : act o s = .write y n ∨
          (act o s = .alloc n ∧ y ≠ headL ∧ y ≠ tailL ∧ y ∉ c.used) :=
        h2.imp_right (fun h => ⟨h.1, (fresh_iff hI y).1 h.2⟩)
      simp only [laStep, h1]
      rw [ite_eq_left h2']; rfl
    | res p x r =>
      obtain ⟨o, s, h1, h2⟩ := hm
      rw [← hI.cl] at h1
      simp [laStep, h1, h2]
    | rres => exact hm.elim
    | wres => exact hm.elim

/-! ## LS-linearizability -/

lemma getD_pred_eq_curOp (H : LHist ℕ) (p : ℕ) (h : opsP H p ≠ []) :
    (opsP H p).getD ((opsP H p).length - 1) [] = curOp H p := by
  unfold curOp
  rcases List.eq_nil_or_concat (opsP H p) with h' | ⟨L, x, h'⟩
  · exact absurd h' h
  · rw [h', List.concat_eq_append]
    simp

/-- Every history of `I_LA` is LS-linearizable. -/
theorem lookahead_lsl (H : LHist ℕ) (hH : H ∈ I_LA) : LSL_LL H := by
  obtain ⟨c, hc⟩ := mem_I_LA.1 hH
  have hI := laRun_inv H c hc
  refine ⟨?_, ?_⟩
  · intro p x k hk
    cases x
    rw [numOps_eq] at hk
    rw [localView_eq]
    suffices ∃ S₀, S₀ ++ (opsP H p).getD k [] ∈ (SigLL : Set (LHist ℕ)) by
      obtain ⟨S₀, hS⟩ := this
      exact ⟨S₀, sigLL_of_prefix ((List.prefix_append_right_inj S₀).2 (dropAbort_prefix _)) hS⟩
    by_cases h : k + 1 < (opsP H p).length ∨ c.cl p = .idle
    · exact hI.done p k hk h
    · push Not at h
      have hk' : k = (opsP H p).length - 1 := by omega
      rw [hk', getD_pred_eq_curOp H p (hI.opsNe p h.2)]
      by_cases hh : c.holds p
      · obtain ⟨log, -, h2⟩ := hI.log
        exact ⟨log, by simp [SigLL, h2 p hh]⟩
      · rcases hI.nonHolder p hh with h' | ⟨o, h' | h'⟩
        · exact absurd h' h.2
        · rw [(hI.nonHolderOp p o hh).1 h']
          exact ⟨[], by simp [SigLL, seqRun, seqStep, scfg0]⟩
        · rw [(hI.nonHolderOp p o hh).2 h']
          exact ⟨[], by simp [SigLL, seqRun, seqStep, scfg0, act]⟩
  · obtain ⟨ann, hrun, herase⟩ := hI.lin
    exact hwLinearizable_of_lpRun hrun herase

/-! ## Deadlock-freedom -/

/-- A location that is not mentioned in `c.used`. -/
lemma fresh_loc (c : LACfg) : c.used.sup id + 2 ≠ headL ∧ c.used.sup id + 2 ≠ tailL ∧
    c.used.sup id + 2 ∉ c.used := by
  refine ⟨by simp [headL], by simp [tailL], fun h => ?_⟩
  have h1 : c.used.sup id + 2 ≤ c.used.sup id := Finset.le_sup (f := id) h
  exact absurd h1 (Nat.not_le.2 (Nat.lt_add_of_pos_right (by norm_num)))

/-- Some event other than an invocation is always possible while an operation is in progress. -/
theorem lookahead_df1 (H : LHist ℕ) (hH : H ∈ I_LA) (hp : ∃ p, InProgress H p) :
    ∃ e : LEv ℕ, e.isInv = false ∧ H ++ [e] ∈ I_LA := by
  obtain ⟨c, hc⟩ := mem_I_LA.1 hH
  have hI := laRun_inv H c hc
  suffices ∃ e : LEv ℕ, e.isInv = false ∧ (laStep c e).isSome by
    obtain ⟨e, he, h'⟩ := this
    exact ⟨e, he, mem_of_step hc h'⟩
  by_cases hh : ∃ q, c.holds q
  · obtain ⟨q, hq⟩ := hh
    have hbusy := hI.holderBusy q hq
    rcases hcl : c.cl q with _ | ⟨o, s⟩ | ⟨o, s, ⟨y⟩ | ⟨y, n⟩⟩
    · exact absurd hcl hbusy
    · cases ha : act o s with
      | read y => exact ⟨.rinv q () y, rfl, by simp [laStep, hcl, ha]⟩
      | write y n => exact ⟨.winv q () y n, rfl, by simp [laStep, hcl, ha]⟩
      | alloc n =>
        refine ⟨.winv q () (c.used.sup id + 2) n, rfl, ?_⟩
        have hf := fresh_loc c
        simp [laStep, hcl, ha, hf.1, hf.2.1, hf.2.2]
      | ret r => exact ⟨.res q () r, rfl, by simp [laStep, hcl, ha]⟩
    · obtain ⟨⟨zs, -, -, hL⟩, -⟩ := hI.holder q o s hq (Or.inr ⟨_, hcl⟩)
      obtain ⟨n, hn⟩ := hL.act_read (hI.pendRd q o s y hcl)
      refine ⟨.rres q () (some n), rfl, ?_⟩
      simp [laStep, hcl, hn, hq]
    · exact ⟨.wres q () true, rfl, by simp [laStep, hcl]⟩
  · push Not at hh
    obtain ⟨p, hp⟩ := hp
    have hcp : c.cl p ≠ .idle := by rw [hI.cl]; exact hp
    have hw : c.wr = none := by
      cases hw : c.wr with
      | none => rfl
      | some w => exact absurd (Or.inr hw) (hh w)
    have hrd : c.rd = ∅ := by
      ext q; simp only [Finset.notMem_empty, iff_false]; exact fun h => hh q (Or.inl h)
    rcases hI.nonHolder p (hh p) with h | ⟨o, h | h⟩
    · exact absurd h hcp
    · exact ⟨.rinv p () headL, rfl, by simp [laStep, h, act]⟩
    · obtain ⟨zs, -, -, b, cc, ⟨a, ha, -⟩, -⟩ := hI.rep hw
      refine ⟨.rres p () (some ⟨.ninf, a⟩), rfl, ?_⟩
      by_cases hro : (setδ c.q o).1 = c.q
      · simp [laStep, h, ha, hh p, hro, hw]
      · simp [laStep, h, ha, hh p, hro, hw, hrd]

/-- The potential of a client state: twice the remaining actions of `LL` (plus one if no read
or write is pending). -/
def phi1 (q : Finset ℤ) : CSt → ℕ
  | .idle => 0
  | .run _ s => 2 * rank q s + 1
  | .pend _ s _ => 2 * rank q s

/-- The potential of a configuration. -/
def Phi (c : LACfg) : ℕ := ∑ p ∈ c.procs, phi1 c.q (c.cl p)

lemma Phi_lt_of {c c' : LACfg} {p : ℕ} (hq : c'.q = c.q) (hpr : c'.procs = c.procs)
    (hp : p ∈ c.procs) (hcl : ∀ q, q ≠ p → c'.cl q = c.cl q)
    (hlt : phi1 c.q (c'.cl p) < phi1 c.q (c.cl p)) : Phi c' < Phi c := by
  unfold Phi; rw [hpr, hq]
  refine Finset.sum_lt_sum (fun q _ => ?_) ⟨p, hp, hlt⟩
  by_cases h : q = p
  · subst h; exact hlt.le
  · rw [hcl q h]

/-- Every event other than an invocation or a response decreases the potential. -/
lemma Phi_step {H : LHist ℕ} {c c' : LACfg} {e : LEv ℕ} (hI : LAInv H c)
    (h : laStep c e = some c') (hi : e.isInv = false) (hr : e.isRes = false) : Phi c' < Phi c := by
  have hb := laStep_basic h
  have hpr : ∀ x, c.cl e.proc = x → x ≠ .idle → c'.procs = c.procs := fun x hx hne => by
    rw [hb.2.2.1]; exact Finset.insert_eq_of_mem (hI.procs _ (by rw [hx]; exact hne))
  have hother : ∀ q, q ≠ e.proc → c'.cl q = c.cl q := fun q hq => by
    rw [hb.1, Function.update_of_ne hq]
  rcases laStep_some h with ⟨p, o, rfl, hcl, rfl⟩ | ⟨p, y, o, s, rfl, hcl, ha, rfl⟩ |
    ⟨p, y, n, o, s, rfl, hcl, ha, rfl⟩ | ⟨p, r, o, s, rfl, hcl, ha, rfl⟩ |
    ⟨p, n, o, s, y, rfl, hcl, hm, hh, rfl⟩ | ⟨p, n, o, s, y, rfl, hcl, hm, hh, hro, hw, rfl⟩ |
    ⟨p, n, o, s, y, rfl, hcl, hm, hh, hro, hrd, hw, rfl⟩ | ⟨p, y, n, o, s, rfl, hcl, rfl⟩
  · simp [Ev.isInv] at hi
  · refine Phi_lt_of rfl (hpr _ hcl (by simp)) (hI.procs p (by rw [hcl]; simp)) hother ?_
    simp [hcl, cstep, phi1]
  · refine Phi_lt_of rfl (hpr _ hcl (by simp)) (hI.procs p (by rw [hcl]; simp)) hother ?_
    simp [hcl, cstep, phi1]
  · simp [Ev.isRes] at hr
  · refine Phi_lt_of rfl (hpr _ hcl (by simp)) (hI.procs p (by rw [hcl]; simp)) hother ?_
    obtain ⟨⟨zs, hzs, hq, hL⟩, -⟩ := hI.holder p o s hh (Or.inr ⟨_, hcl⟩)
    have := (hL.read hzs (hI.pendRd p o s y hcl) hm).2
    rw [hq] at this
    simp [hcl, cstep, phi1]; omega
  · refine Phi_lt_of rfl (hpr _ hcl (by simp)) (hI.procs p (by rw [hcl]; simp)) hother ?_
    obtain ⟨rfl, rfl, -⟩ := acquire_facts hI hcl hm hh hw
    have := rank_trav_le c.q headL n
    simp [hcl, cstep, phi1, onRead, rank] at this ⊢; omega
  · refine Phi_lt_of rfl (hpr _ hcl (by simp)) (hI.procs p (by rw [hcl]; simp)) hother ?_
    obtain ⟨rfl, rfl, -⟩ := acquire_facts hI hcl hm hh hw
    have := rank_trav_le c.q headL n
    simp [hcl, cstep, phi1, onRead, rank] at this ⊢; omega
  · refine Phi_lt_of rfl (hpr _ hcl (by simp)) (hI.procs p (by rw [hcl]; simp)) hother ?_
    have hw := hI.writer_of_pendWr hcl
    obtain ⟨⟨zs, hzs, hq, hL⟩, -⟩ := hI.holder p o s (Or.inr hw) (Or.inr ⟨_, hcl⟩)
    have hlt : rank c.q (onWrite s y) < rank c.q s := by
      rw [← hq]
      rcases (hI.pendWr p o s y n hcl).1 with ha | ha
      · exact (hL.write ha).2
      · exact (hL.alloc hzs ha.1 ha.2).2
    simp [hcl, cstep, phi1]; omega

lemma length_le_Phi (E : LHist ℕ) : ∀ (H : LHist ℕ) (c c'' : LACfg), LAInv H c →
    laRun c E = some c'' → (∀ e ∈ E, e.isInv = false ∧ e.isRes = false) → E.length ≤ Phi c := by
  induction E with
  | nil => intros; simp
  | cons e E ih =>
    intro H c c'' hI hrun hE
    simp only [laRun] at hrun
    cases hs : laStep c e with
    | none => rw [hs] at hrun; cases hrun
    | some c₁ =>
      rw [hs, Option.bind_some] at hrun
      have h1 := Phi_step hI hs (hE e (by simp)).1 (hE e (by simp)).2
      have h2 := ih (H ++ [e]) c₁ c'' (hI.step hs) hrun (fun e' he' => hE e' (by simp [he']))
      simp only [List.length_cons]; omega

/-- `I_LA` is deadlock-free (strong form). -/
theorem lookahead_deadlockFree : DeadlockFree I_LA := by
  refine ⟨lookahead_df1, fun H hH => ?_⟩
  obtain ⟨c, hc⟩ := mem_I_LA.1 hH
  refine ⟨Phi c, fun E hE hE' => ?_⟩
  obtain ⟨c'', h⟩ := mem_I_LA.1 hE
  rw [laRun_append, hc, Option.bind_some] at h
  exact length_le_Phi E H c c'' (laRun_inv H c hc) h hE'

/-! ## The main results -/

/-- **`I_LA` belongs to the class `P`**: a deadlock-free pessimistic LS-linearizable (and
honest) implementation of `(LL, set)`. -/
theorem lookahead_classP : ClassP I_LA := by
  refine ⟨lookahead_isImpl, lookahead_lsl, ?_, lookahead_deadlockFree, ?_⟩
  · intro H hH e he
    obtain ⟨c, hc⟩ := mem_I_LA.1 hH
    exact (laRun_inv H c hc).noAbort e he
  · intro H hH
    obtain ⟨c, hc⟩ := mem_I_LA.1 hH
    simp [Honest, (laRun_inv H c hc).hon]

lemma hist2a_mem : hist2a ∈ I_LA := by decide

/-- **`I_LA` accepts the schedule `σ` of Figure 2(a).** -/
theorem lookahead_accepts : Accepts I_LA sigma2a := by
  refine ⟨hist2a, hist2a_mem, ?_⟩
  show (complete hist2a).map Ev.erase = hist2a.map Ev.erase
  rw [show complete hist2a = hist2a by decide]

/-- **Theorem 7 of the paper (part 2 of Theorem 2) is false**: some deadlock-free pessimistic
LS-linearizable implementation of `(LL, set)` accepts the schedule `σ` of Figure 2(a). -/
theorem theorem_7_false : ¬ Theorem7Claim :=
  fun h => h I_LA lookahead_classP lookahead_accepts

end Podc.OptimismConcurrency
