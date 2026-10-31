import Papers.PODC2018.NestingSafeRecoverable.Thm4Valency

/-!
# Theorem 4 of [ABH18]: no wait-free recoverable test&set from read/write and test&set

> **Theorem 4.** There exists no recoverable non-resettable TAS algorithm satisfying NRL, from
> read/write and (non-recoverable) non-resettable TAS base objects only, such that both the T&S
> operation and the T&S.RECOVER function are wait-free.

Proof structure (the paper's valency argument):

* `val_C0`: the configuration `C0` where `p` and `q` have invoked `T&S` is bivalent;
* `round`: from a reachable bivalent configuration, a crash-free extension reaches a critical
  configuration `D`; both processes are poised on the same base object with operations that do
  not absorb each other, so the object state after `p;q` and `q;p` is the same; crashing `p`
  after both steps makes `D·p·q·crash_p` and `D·q·p·crash_p` indistinguishable to `p`, and one
  of them is bivalent. Each round contains a step of `q`, and only `p` crashes;
* `theorem4`: iterating rounds forever gives an infinite execution in which `q` never crashes,
  takes infinitely many steps and never returns, contradicting wait-freedom.

Unlike the paper we never rename `p` and `q` ("assume w.l.o.g. that `C₁∘p` is `p`-valent"): the
renaming could make the crashing process change from round to round, and then no process is
crash-free in the infinite execution. The case analysis in `round` works with `p` always the
crashing process, whichever of `D·p`, `D·q` is `p`-valent.
-/

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL Cslib.SharedMemory.NRL.Alg

variable {P : Type} [DecidableEq P] {A : Alg P tasObj} {p q : P}

lemma biv_of {C : A.Cfg} {a b : P} (hab : a ≠ b) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (h1 : Val C a) (h2 : Val C b) : Biv p q C := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩
  · exact absurd rfl hab

section Hyp

variable (H : Hyp A p q)
include H

open Classical in
/-- One round of the construction: a crash-free extension to a critical configuration, the two
critical steps (in one of the two orders) and a crash of `p`, ending in a bivalent
configuration. -/
lemma round {E : A.Cfg} (hE : Reach A p q E) (hb : Biv p q E) :
    ∃ es : List (Ev P tasObj), (∀ e ∈ es, GEv p e) ∧ Ev.step q ∈ es ∧ Biv p q (E.run es) := by
  have hpq := H.ne
  obtain ⟨xs, hD, hDp, hDq⟩ := exists_crit H hE hb
  have hRD := hE.steps xs
  have hrp := hD.running H hRD (Or.inl rfl)
  have hrq := hD.running H hRD (Or.inr rfl)
  obtain ⟨⟨op, pcp, vp⟩, hsp⟩ := Option.isSome_iff_exists.1 hrp
  obtain ⟨⟨oq, pcq, vq⟩, hsq⟩ := Option.isSome_iff_exists.1 hrq
  have eDp : E.run (steps (xs ++ [p])) = (E.run (steps xs)).ev (.step p) := by
    simp [steps, Cfg.run_append]
  have eDq : E.run (steps (xs ++ [q])) = (E.run (steps xs)).ev (.step q) := by
    simp [steps, Cfg.run_append]
  rw [eDp] at hDp; rw [eDq] at hDq
  generalize hDdef : E.run (steps xs) = D at hD hRD hrp hrq hsp hsq hDp hDq
  have hRDp : Reach A p q (D.ev (.step p)) := hRD.ev (Or.inl ⟨p, rfl⟩)
  have hRDq : Reach A p q (D.ev (.step q)) := hRD.ev (Or.inl ⟨q, rfl⟩)
  have hRDpq : Reach A p q ((D.ev (.step p)).ev (.step q)) := hRDp.ev (Or.inl ⟨q, rfl⟩)
  have hRDqp : Reach A p q ((D.ev (.step q)).ev (.step p)) := hRDq.ev (Or.inl ⟨p, rfl⟩)
  -- the two successors have no common valency
  have noC : ∀ v, (v = p ∨ v = q) → Val (D.ev (.step p)) v → Val (D.ev (.step q)) v → False := by
    intro v hv h1 h2
    obtain ⟨w, hwv, hw, hwV⟩ : ∃ w, w ≠ v ∧ (w = p ∨ w = q) ∧ Val D w := by
      rcases hv with rfl | rfl
      · exact ⟨q, Ne.symm hpq, Or.inr rfl, hD.2⟩
      · exact ⟨p, hpq, Or.inl rfl, hD.1⟩
    rcases val_first H hRD hrp hrq hw hwV with h | h
    · exact hDp (biv_of hwv hw hv h h1)
    · exact hDq (biv_of hwv hw hv h h2)
  have hesp : ∀ (l : List (Ev P tasObj)), (∀ e ∈ l, GEv p e) →
      (∀ e ∈ steps xs ++ l, GEv p e) := by
    intro l hl e he
    rcases List.mem_append.1 he with he | he
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 he; exact Or.inl ⟨y, rfl⟩
    · exact hl e he
  have hrun : ∀ l, E.run (steps xs ++ l) = D.run l := by
    intro l; rw [Cfg.run_append, hDdef]
  by_cases hsame : ∃ i, (A.act p op pcp vp).obj = some i ∧ (A.act q oq pcq vq).obj = some i
  swap
  · -- the steps commute
    exfalso
    have heq := step_comm hpq D hsp hsq (fun i h1 h2 => hsame ⟨i, h1, h2⟩)
    rcases val_or H hRDpq with h | h
    · exact noC p (Or.inl rfl) (val_ext1 h) (val_ext1 (val_of_equiv heq h))
    · exact noC q (Or.inr rfl) (val_ext1 h) (val_ext1 (val_of_equiv heq h))
  obtain ⟨i, hi1, hi2⟩ := hsame
  obtain ⟨a, pc₁, k₁, hap⟩ : ∃ a pc₁ k₁, A.act p op pcp vp = .access i a pc₁ k₁ := by
    revert hi1
    cases A.act p op pcp vp with
    | access j a pc k => intro h; simp only [Act.obj, Option.some.injEq] at h; subst h; exact ⟨_, _, _, rfl⟩
    | internal => simp [Act.obj]
    | ret => simp [Act.obj]
  obtain ⟨b, pc₂, k₂, haq⟩ : ∃ b pc₂ k₂, A.act q oq pcq vq = .access i b pc₂ k₂ := by
    revert hi2
    cases A.act q oq pcq vq with
    | access j a pc k => intro h; simp only [Act.obj, Option.some.injEq] at h; subst h; exact ⟨_, _, _, rfl⟩
    | internal => simp [Act.obj]
    | ret => simp [Act.obj]
  set s := D.mem i with hs
  -- the four configurations after the critical steps
  have eDp' := ev_step_access D hsp hap
  have eDq' := ev_step_access D hsq haq
  have hsq1 : (D.ev (.step p)).st q = some (oq, pcq, vq) := by
    rw [ev_step_st_ne (Ne.symm hpq), hsq]
  have hsp1 : (D.ev (.step q)).st p = some (op, pcp, vp) := by
    rw [ev_step_st_ne hpq, hsp]
  have eDpq := ev_step_access _ hsq1 haq
  have eDqp := ev_step_access _ hsp1 hap
  have mDp : (D.ev (.step p)).mem i = ((A.T i).δ s a).1 := by rw [eDp']; simp [hs]
  have mDq : (D.ev (.step q)).mem i = ((A.T i).δ s b).1 := by rw [eDq']; simp [hs]
  have mDpq : ((D.ev (.step p)).ev (.step q)).mem =
      Function.update D.mem i ((A.T i).δ ((A.T i).δ s a).1 b).1 := by
    rw [eDpq]; simp only; rw [mDp, eDp']; simp
  have mDqp : ((D.ev (.step q)).ev (.step p)).mem =
      Function.update D.mem i ((A.T i).δ ((A.T i).δ s b).1 a).1 := by
    rw [eDqp]; simp only; rw [mDq, eDq']; simp
  have sDpq_q : ((D.ev (.step p)).ev (.step q)).st q =
      some (oq, pc₂, k₂ ((A.T i).δ ((A.T i).δ s a).1 b).2) := by
    rw [eDpq]; simp [mDp]
  have sDqp_p : ((D.ev (.step q)).ev (.step p)).st p =
      some (op, pc₁, k₁ ((A.T i).δ ((A.T i).δ s b).1 a).2) := by
    rw [eDqp]; simp [mDq]
  have sDpq_p : ((D.ev (.step p)).ev (.step q)).st p =
      some (op, pc₁, k₁ ((A.T i).δ s a).2) := by
    rw [ev_step_st_ne hpq, eDp']; simp [hs]
  have sDqp_q : ((D.ev (.step q)).ev (.step p)).st q =
      some (oq, pc₂, k₂ ((A.T i).δ s b).2) := by
    rw [ev_step_st_ne (Ne.symm hpq), eDq']; simp [hs]
  have sDq_q : (D.ev (.step q)).st q = some (oq, pc₂, k₂ ((A.T i).δ s b).2) := by
    rw [eDq']; simp [hs]
  have sDp_p : (D.ev (.step p)).st p = some (op, pc₁, k₁ ((A.T i).δ s a).2) := by
    rw [eDp']; simp [hs]
  rcases H.crit i s a b with habs | habs | hcomm
  · -- `q`'s operation absorbs `p`'s: `D·p·q` and `D·q` look the same to `q`
    exfalso
    have hag : Agree q ((D.ev (.step p)).ev (.step q)) (D.ev (.step q)) := by
      refine ⟨?_, ?_⟩
      · rw [mDpq, eDq', habs]
      · rw [sDpq_q, sDq_q, habs]
    obtain ⟨w, hw, h1, h2⟩ := agree_val H hRDpq hRDq hpq (Or.inl rfl) (Or.inr rfl) hag
      (by rw [sDpq_p]; rfl) (by rw [hsp1]; rfl) (by rw [sDpq_q]; rfl) (by rw [sDq_q]; rfl)
    exact noC w hw (val_ext1 h1) h2
  · -- `p`'s operation absorbs `q`'s
    exfalso
    have hag : Agree p ((D.ev (.step q)).ev (.step p)) (D.ev (.step p)) := by
      refine ⟨?_, ?_⟩
      · rw [mDqp, eDp', habs]
      · rw [sDqp_p, sDp_p, habs]
    obtain ⟨w, hw, h1, h2⟩ := agree_val H hRDqp hRDp (Ne.symm hpq) (Or.inr rfl) (Or.inl rfl) hag
      (by rw [sDqp_q]; rfl) (by rw [hsq1]; rfl) (by rw [sDqp_p]; rfl) (by rw [sDp_p]; rfl)
    exact noC w hw h2 (val_ext1 h1)
  · -- same object state in both orders: crash `p`
    set E1 := ((D.ev (.step p)).ev (.step q)).ev (.crash p) with hE1
    set E2 := ((D.ev (.step q)).ev (.step p)).ev (.crash p) with hE2
    have hRE1 : Reach A p q E1 := hRDpq.ev (Or.inr rfl)
    have hRE2 : Reach A p q E2 := hRDqp.ev (Or.inr rfl)
    have sE1 : E1.st p = some (op, A.recover p op pc₁) := by
      rw [hE1, ev_crash_of_some _ sDpq_p]; simp
    have sE2 : E2.st p = some (op, A.recover p op pc₁) := by
      rw [hE2, ev_crash_of_some _ sDqp_p]; simp
    have hag12 : Agree p E1 E2 := by
      refine ⟨?_, by rw [sE1, sE2]⟩
      rw [hE1, hE2, ev_crash_mem, ev_crash_mem, mDpq, mDqp, hcomm]
    have hag1 : Agree q E1 ((D.ev (.step p)).ev (.step q)) := agree_ev_crash_ne (Ne.symm hpq) _
    have hag2 : Agree q E2 ((D.ev (.step q)).ev (.step p)) := agree_ev_crash_ne (Ne.symm hpq) _
    have rE1q : (E1.st q).isSome := by rw [hag1.2, sDpq_q]; rfl
    have rE2q : (E2.st q).isSome := by rw [hag2.2, sDqp_q]; rfl
    have rE1p : (E1.st p).isSome := by rw [sE1]; rfl
    have rE2p : (E2.st p).isSome := by rw [sE2]; rfl
    obtain ⟨w, hw, hw1, hw2⟩ := agree_val H hRE1 hRE2 (Ne.symm hpq) (Or.inr rfl) (Or.inl rfl)
      hag12 rE1q rE2q rE1p rE2p
    obtain ⟨w₁, hw₁, h11, h12⟩ := agree_val H hRE1 hRDpq hpq (Or.inl rfl) (Or.inr rfl) hag1
      rE1p (by rw [sDpq_p]; rfl) rE1q (by rw [sDpq_q]; rfl)
    obtain ⟨w₂, hw₂, h21, h22⟩ := agree_val H hRE2 hRDqp hpq (Or.inl rfl) (Or.inr rfl) hag2
      rE2p (by rw [sDqp_p]; rfl) rE2q (by rw [sDqp_q]; rfl)
    have h12' := val_ext1 h12
    have h22' := val_ext1 h22
    have hne : w₁ ≠ w₂ := by rintro rfl; exact noC w₁ hw₁ h12' h22'
    have hww : w = w₁ ∨ w = w₂ := by
      rcases hw with rfl | rfl <;> rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl <;>
        simp_all
    rcases hww with rfl | rfl
    · refine ⟨steps xs ++ [.step q, .step p, .crash p], hesp _ ?_, by simp, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro e (rfl | rfl | rfl)
        exacts [Or.inl ⟨q, rfl⟩, Or.inl ⟨p, rfl⟩, Or.inr rfl]
      · rw [hrun]; exact biv_of hne hw hw₂ hw2 h21
    · refine ⟨steps xs ++ [.step p, .step q, .crash p], hesp _ ?_, by simp, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro e (rfl | rfl | rfl)
        exacts [Or.inl ⟨p, rfl⟩, Or.inl ⟨q, rfl⟩, Or.inr rfl]
      · rw [hrun]; exact biv_of hne.symm hw hw₁ hw1 h11

/-- `C0` is bivalent: running `x` solo from `C0` looks to `x` like running it alone in the system,
where it must return `0`. -/
lemma val_C0 {x : P} (hx : x = p ∨ x = q) : Val (C0 A p q) x := by
  have hpq := H.ne
  obtain ⟨hh0, hm0, hp0, hq0, -⟩ := C0_hist (A := A) hpq
  set D1 := A.init.ev (.inv x ()) with hD1
  have eD1 := ev_inv_of_none (p := x) A.init () rfl
  have hsx : (C0 A p q).st x = some ((), A.start x ()) := by rcases hx with rfl | rfl <;> assumption
  have hag : Agree x (C0 A p q) D1 := ⟨by rw [hm0, hD1, eD1], by rw [hsx, hD1, eD1]; simp⟩
  have hops : ∀ (n : ℕ) z, opsOf (N (D1.run (List.replicate n (.step x))).hist) z =
      if z = x then [()] else [] := by
    intro n z
    rw [ops_run_of_not_inv _ (by intro e he y o; rw [List.eq_of_mem_replicate he]; simp)]
    rw [hD1, eD1]
    by_cases hz : z = x
    · subst hz; simp [init, opsOf, N, HStep.toLabel]
    · simp [init, opsOf, N, HStep.toLabel, hz, Ne.symm hz]
  have hos : ∀ n, OneShot (N (D1.run (List.replicate n (.step x))).hist) := by
    intro n z; rw [hops]; split_ifs <;> simp
  obtain ⟨n, hn⟩ := H.wf [.inv x ()] (fun _ => .step x) x
    (fun n => by rw [pre_const]; exact hos n) (by simp [hD1, eD1]) (fun n => by simp)
    (fun m => ⟨m, le_refl _, rfl⟩)
  rw [pre_const] at hn
  change (D1.run (List.replicate n (.step x))).st x = none at hn
  -- `x` has returned in the solo run; its response is `0`
  have hpend := (wfInv_run (A := A) ([.inv x ()] ++ List.replicate n (.step x))).pend x
  rw [Cfg.run_append] at hpend
  change (opsOf (N (D1.run (List.replicate n (.step x))).hist) x).length = _ + _ at hpend
  rw [hops] at hpend
  simp only [↓reduceIte, List.length_singleton] at hpend
  change 1 = (respsOf (N (D1.run (List.replicate n (.step x))).hist) x).length +
    (if ((D1.run (List.replicate n (.step x))).st x).isSome = true then 1 else 0) at hpend
  rw [hn] at hpend
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero] at hpend
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hpend.symm
  obtain ⟨-, L, hL⟩ := H.nrl ([.inv x ()] ++ List.replicate n (.step x))
    (by rw [Cfg.run_append]; exact hos n)
  rw [Cfg.run_append] at hL
  have hb0 := lin_single hL (hops n) hb
  subst hb0
  -- transfer to `C0`
  obtain ⟨-, hs, h1, h2⟩ := run_agree hag n
  refine ⟨List.replicate n x, ?_⟩
  rw [steps_replicate]
  unfold Ret resps
  rw [h1, N_append, respsOf_append, hh0]
  change respsOf (N (D1.run (List.replicate n (.step x))).hist) x = _ at hb
  rw [h2, N_append, respsOf_append, hD1, eD1] at hb
  have e1 : List.filterMap (Label.retOf x) [Label.inv (A := tasObj) x ()] = [] := rfl
  have e2 : List.filterMap (Label.retOf x) [Label.inv (A := tasObj) p (), Label.inv q ()] = [] :=
    rfl
  simp only [init, respsOf, N, HStep.toLabel, List.nil_append, List.filterMap_cons,
    List.filterMap_nil, List.filterMap_append] at hb ⊢
  simpa [e1, e2] using hb

end Hyp

/-- A prefix-monotone chain of lists of unbounded length has a limit. -/
lemma exists_seq_of_chain {α : Type} (F : ℕ → List α) (hmono : ∀ k, F k <+: F (k + 1))
    (hlen : ∀ k, k ≤ (F k).length) :
    ∃ e : ℕ → α, ∀ k n (hn : n < (F k).length), e n = (F k)[n] := by
  have hmono' : ∀ k m, k ≤ m → F k <+: F m := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ m _ ih => exact ih.trans (hmono m)
  refine ⟨fun n => (F (n + 1))[n]'(by have := hlen (n + 1); omega), fun k n hn => ?_⟩
  rcases le_total (n + 1) k with h | h
  · exact (hmono' _ _ h).getElem _
  · exact ((hmono' _ _ h).getElem hn).symm

/-- **Theorem 4 of [ABH18].** There is no recoverable non-resettable test&set implementation
satisfying NRL from read/write registers and (non-recoverable) non-resettable test&set objects
such that both `T&S` and `T&S.Recover` are wait-free. Here: for any algorithm `A` of the model
whose base objects are read/write-like or test&set-like, and any two processes `p ≠ q`, NRL
(for histories in which every process invokes `T&S` at most once) and wait-freedom (of the
operation together with its recovery function) are contradictory. -/
theorem theorem4 (A : Alg P tasObj) (hT : ∀ i, (A.T i).RWLike ∨ (A.T i).TASLike) {p q : P}
    (hpq : p ≠ q) (hnrl : A.NRL OneShot) (hwf : A.WaitFree OneShot) : False := by
  classical
  have H : Hyp A p q := ⟨hpq, hnrl, hwf, critOK_of_rw_tas hT⟩
  have hround : ∀ E : A.Cfg, Reach A p q E ∧ Biv p q E → ∃ es : List (Ev P tasObj),
      (∀ e ∈ es, GEv p e) ∧ Ev.step q ∈ es ∧ Biv p q (E.run es) :=
    fun E h => round H h.1 h.2
  let rd : A.Cfg → List (Ev P tasObj) := fun E =>
    if h : Reach A p q E ∧ Biv p q E then Classical.choose (hround E h) else []
  have hrd : ∀ E, Reach A p q E ∧ Biv p q E → (∀ e ∈ rd E, GEv p e) ∧ Ev.step q ∈ rd E ∧
      Biv p q (E.run (rd E)) := by
    intro E h; simp only [rd, h, and_self, ↓reduceDIte]; exact Classical.choose_spec (hround E h)
  let Es : ℕ → A.Cfg := fun k => Nat.rec (C0 A p q) (fun _ E => E.run (rd E)) k
  let F : ℕ → List (Ev P tasObj) := fun k => Nat.rec [] (fun k l => l ++ rd (Es k)) k
  have hEs : ∀ k, Es (k + 1) = (Es k).run (rd (Es k)) := fun k => rfl
  have hF : ∀ k, F (k + 1) = F k ++ rd (Es k) := fun k => rfl
  have inv : ∀ k, Reach A p q (Es k) ∧ Biv p q (Es k) ∧ (C0 A p q).run (F k) = Es k ∧
      k ≤ (F k).length ∧ ∀ e ∈ F k, GEv p e := by
    intro k
    induction k with
    | zero => exact ⟨Reach.c0, ⟨val_C0 H (Or.inl rfl), val_C0 H (Or.inr rfl)⟩, rfl, le_refl _,
        by simp [F]⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      obtain ⟨g1, g2, g3⟩ := hrd _ ⟨h1, h2⟩
      refine ⟨by rw [hEs]; exact h1.run g1, by rw [hEs]; exact g3, ?_, ?_, ?_⟩
      · rw [hF, Cfg.run_append, h3, hEs]
      · rw [hF, List.length_append]
        have : 0 < (rd (Es k)).length := List.length_pos_of_mem g2
        omega
      · rw [hF]; intro e he
        rcases List.mem_append.1 he with he | he
        exacts [h5 e he, g1 e he]
  obtain ⟨e, he⟩ := exists_seq_of_chain F (fun k => by rw [hF]; exact List.prefix_append _ _)
    (fun k => (inv k).2.2.2.1)
  have hpre : ∀ k n, n ≤ (F k).length → pre e n = (F k).take n := by
    intro k n hn
    apply List.ext_getElem
    · simp [pre]; omega
    · intro j h1 h2
      simp only [pre, List.getElem_map, List.getElem_range, List.getElem_take]
      exact he k j (by simp [pre] at h1; omega)
  have hG : ∀ n, ∀ e' ∈ pre e n, GEv p e' := by
    intro n e' h'
    rw [hpre n n (inv n).2.2.2.1] at h'
    exact (inv n).2.2.2.2 e' (List.mem_of_mem_take h')
  have hGe : ∀ n, GEv p (e n) := by
    intro n
    have h := he (n + 1) n (by have := (inv (n + 1)).2.2.2.1; omega)
    rw [h]; exact (inv (n + 1)).2.2.2.2 _ (List.getElem_mem _)
  obtain ⟨n, hn⟩ := hwf [.inv p (), .inv q ()] e q
    (fun n => (Reach.c0.run (hG n)).oneShot hpq)
    (by change ((C0 A p q).st q).isSome = true; rw [(C0_hist (A := A) hpq).2.2.2.1]; rfl)
    (fun n h => by
      rcases hGe n with ⟨y, hy⟩ | hy <;> rw [h] at hy
      · cases hy
      · cases hy; exact hpq rfl)
    (fun m => by
      obtain ⟨-, g2, -⟩ := hrd _ ⟨(inv m).1, (inv m).2.1⟩
      obtain ⟨j, hj, hjq⟩ := List.getElem_of_mem g2
      refine ⟨(F m).length + j, by have := (inv m).2.2.2.1; omega, ?_⟩
      rw [he (m + 1) _ (by rw [hF, List.length_append]; omega)]
      simp only [hF]
      rw [List.getElem_append_right (by omega)]
      simpa using hjq)
  -- `q` has completed, but the bivalent configuration `Es n` comes later
  change ((C0 A p q).run (pre e n)).st q = none at hn
  have hlen := (inv n).2.2.2.1
  have hsplit : (C0 A p q).run (F n) = ((C0 A p q).run (pre e n)).run ((F n).drop n) := by
    rw [← Cfg.run_append, hpre n n hlen, List.take_append_drop]
  have hq : (Es n).st q = none := by
    rw [← (inv n).2.2.1, hsplit]
    exact st_none_run _ hn (fun e' h' o => (((inv n).2.2.2.2 e'
      (List.mem_of_mem_drop h')).not_inv q o))
  have := (inv n).2.1.running H (inv n).1 (Or.inr rfl)
  rw [hq] at this; simp at this

end Podc.NestingSafeRecoverable
