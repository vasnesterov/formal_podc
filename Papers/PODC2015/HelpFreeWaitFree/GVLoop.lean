import Papers.PODC2015.HelpFreeWaitFree.GVCas

/-!
# The construction of Figure 4.2 (one iteration of the main loop)

* `exit_of_chain` — a loop that keeps extending a history by steps of `p` or `q` while their
  numbers of responses stay fixed terminates (wait-freedom; Claim 4.6.5).
* `first_loop` — lines 6–13 (Claims 4.6.2, 4.6.3, 4.6.5): `p₁` and `p₂` take steps that decide
  nothing before `op₃`.
* `u_next` — Claim 4.6.2: at the end of the first loop, `op₁` and `op₂` are not decided before the
  view after `op₃` either.
* `second_loop` — lines 14–15 (Claims 4.6.4, 4.6.5, 4.6.6): `p₃` runs while both `p₁` and `p₂`
  could decide their operation before `op₃` with their next step; `op₃` does not complete.
* `exit_cases` — lines 16–27, with the repaired case analysis: a good step of `p₁`/`p₂`
  (`good_move`), Claim 4.6.8 (`caseA`, `cas_move`), or the case missed by Claim 4.6.12 (`race`,
  `bbad`, `cas_move`).
* `iteration` — one iteration of the main loop: the invariant holds for the next view, `p₁` or
  `p₂` took a step, and if `p₂` completed an operation then `p₁` took a base-object step.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {P L : Type} [DecidableEq P]

/-! ### Termination of the inner loops -/

/-- **Termination of a loop by wait-freedom.** If the loop extends the history by one step of `p`
or `q` while the numbers of responses of `p` and `q` and the number of their invocations stay
bounded, it exits. -/
theorem exit_of_chain {B : ι → ObjSpec} {I : Impl A B P L} (hwf : I.WaitFree)
    (J Ex : List (Label P A) → Prop) (p q : P) (Rp Rq Bd : ℕ) (hval : ∀ h, J h → I.Valid h)
    (hrp : ∀ h, J h → (respsOf h p).length = Rp) (hrq : ∀ h, J h → (respsOf h q).length = Rq)
    (hops : ∀ h, J h → (opsOf h p).length + (opsOf h q).length ≤ Bd)
    (hstep : ∀ h, J h → Ex h ∨ ∃ γ, (γ.proc = p ∨ γ.proc = q) ∧ J (h ++ [γ]))
    {h₀ : List (Label P A)} (h0 : J h₀) : ∃ h, J h ∧ Ex h ∧ h₀ <+: h := by
  classical
  by_contra hcon
  push Not at hcon
  have hstep' : ∀ h, J h → h₀ <+: h → ∃ γ, (γ.proc = p ∨ γ.proc = q) ∧ J (h ++ [γ]) := by
    intro h hJ hpre
    rcases hstep h hJ with hc | hc
    · exact absurd hpre (hcon h hJ hc)
    · exact hc
  let G := {h : List (Label P A) // J h ∧ h₀ <+: h}
  have hnext : ∀ g : G, ∃ γ, (γ.proc = p ∨ γ.proc = q) ∧ J (g.1 ++ [γ]) :=
    fun g => hstep' g.1 g.2.1 g.2.2
  choose γf hγf hJf using hnext
  let nxt : G → G := fun g => ⟨g.1 ++ [γf g], hJf g, g.2.2.trans (List.prefix_append _ _)⟩
  let g₀ : G := ⟨h₀, h0, List.prefix_refl _⟩
  let E : ℕ → List (Label P A) := fun k => (nxt^[k] g₀).1
  have hE : ∀ k, E (k + 1) = E k ++ [γf (nxt^[k] g₀)] := by
    intro k; simp only [E, Function.iterate_succ_apply']; rfl
  have hEJ : ∀ k, J (E k) := fun k => (nxt^[k] g₀).2.1
  have hlen : ∀ k, (E k).length = h₀.length + k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [hE, List.length_append, ih]; simp; omega
  have hmono : ∀ k, E k <+: E (k + 1) := fun k => by rw [hE]; exact List.prefix_append _ _
  have hcount : ∀ k, k ≤ (E k).countP (Label.isTauOf p) + (E k).countP (Label.isTauOf q) +
      (opsOf (E k) p).length + (opsOf (E k) q).length := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      have hγ := hγf (nxt^[k] g₀)
      have hnr : ∀ p' r, γf (nxt^[k] g₀) ≠ .ret p' r := by
        intro p' r he
        have h1p := hrp _ (hEJ (k + 1))
        have h2p := hrp _ (hEJ k)
        have h1q := hrq _ (hEJ (k + 1))
        have h2q := hrq _ (hEJ k)
        rw [hE, he] at h1p h1q
        rcases hγ with hp | hp <;> rw [he] at hp <;> simp only [Label.proc] at hp <;> subst hp
        · simp [respsOf_append] at h1p; omega
        · simp [respsOf_append] at h1q; omega
      have := Ctx.count_le (l := [γf (nxt^[k] g₀)]) (p := p) (q := q) (by simpa using hγ)
        (by simpa using hnr)
      rw [hE, List.countP_append, List.countP_append, opsOf_append, opsOf_append]
      simp only [List.length_append, List.length_singleton] at this ⊢
      omega
  have hval' : ∀ k, I.Valid (E k) := fun k => hval _ (hEJ k)
  have hlen' : ∀ k, k ≤ (E k).length := fun k => by rw [hlen]; omega
  by_cases hb : ∀ N, ∃ k, N ≤ (E k).countP (Label.isTauOf p)
  · exact false_of_starving_chain hwf E hmono hlen' hval' p
      (fun k => by rw [hrp _ (hEJ k), hrp _ (hEJ 0)]) hb
  · push Not at hb
    obtain ⟨N₁, hN₁⟩ := hb
    apply false_of_starving_chain hwf E hmono hlen' hval' q
      (fun k => by rw [hrq _ (hEJ k), hrq _ (hEJ 0)])
    intro N
    refine ⟨N + N₁ + Bd, ?_⟩
    have := hcount (N + N₁ + Bd)
    have := hN₁ (N + N₁ + Bd)
    have := hops _ (hEJ (N + N₁ + Bd))
    omega

/-- Labels of `p` or `q` are base-object steps, invocations or responses. -/
lemma count_steps_le (l : List (Label P A)) (p q : P) :
    l.countP (fun γ => decide (γ.proc = p ∨ γ.proc = q)) ≤ l.countP (Label.isTauOf p) +
      l.countP (Label.isTauOf q) + (opsOf l p).length + (opsOf l q).length +
        (respsOf l p).length + (respsOf l q).length := by
  induction l with
  | nil => simp
  | cons γ l ih =>
    simp only [List.countP_cons, opsOf_cons, respsOf_cons, List.length_append]
    cases γ with
    | inv p' o =>
      by_cases h1 : p' = p <;> by_cases h2 : p' = q <;> simp [Label.proc, h1, h2] at ih ⊢ <;> omega
    | tau p' =>
      by_cases h1 : p' = p <;> by_cases h2 : p' = q <;> simp [Label.proc, h1, h2] at ih ⊢ <;> omega
    | ret p' r =>
      by_cases h1 : p' = p <;> by_cases h2 : p' = q <;> simp [Label.proc, h1, h2] at ih ⊢ <;> omega

namespace Ctx

section Generic

variable {B : ι → ObjSpec} {I : Impl A B P L} (X : Ctx I)

/-- Number of labels of `p₁` and `p₂`. -/
def steps12 (h : List (Label P A)) : ℕ := h.countP (fun γ => decide (γ.proc = X.p₁ ∨ γ.proc = X.p₂))

lemma steps12_mono {l₁ l₂ : List (Label P A)} (h : l₁ <+: l₂) : X.steps12 l₁ ≤ X.steps12 l₂ :=
  List.IsPrefix.countP_le h

lemma steps12_append (l₁ l₂ : List (Label P A)) :
    X.steps12 (l₁ ++ l₂) = X.steps12 l₁ + X.steps12 l₂ := List.countP_append ..

/-! ### The first inner loop (lines 6–13) -/

/-- The exit condition of the first inner loop: the next step of `p₁` decides `op₁` before `op₃`,
and the next step of `p₂` decides `op₂` before `op₃`. -/
def E1 (i j : ℕ) (h : List (Label P A)) : Prop :=
  ∀ C, I.run h = some C → X.DB (h ++ [labOf I C X.p₁ X.op]) (X.p₁, 0) (X.p₃, j) ∧
    X.DB (h ++ [labOf I C X.p₂ (X.W i)]) (X.p₂, i) (X.p₃, j)

/-- At line 5, `op₂` has not completed. -/
lemma resp2_of_not_db {i j : ℕ} {h : List (Label P A)}
    (h3 : ¬ Invoked h (X.p₃, j)) (hr : i ≤ (respsOf h X.p₂).length)
    (hu : ¬ X.DB h (X.p₂, i) (X.p₃, j)) : (respsOf h X.p₂).length = i := by
  by_contra hne
  exact hu (decidedBefore_of_completed X.lin (by simp only [Completed]; omega) h3)

/-- **Lines 6–13** (Claims 4.6.2, 4.6.3, 4.6.5): the first inner loop terminates. -/
theorem first_loop {i j : ℕ} {h₀ : List (Label P A)} (hi : X.GInv i j h₀) :
    ∃ h, X.GInv i j h ∧ X.E1 i j h ∧ h₀ <+: h := by
  refine exit_of_chain X.wf (X.GInv i j) (X.E1 i j) X.p₁ X.p₂ 0 i (1 + (i + 1))
    (fun h hh => hh.str.valid) (fun h hh => by rw [hh.resp1]; rfl) (fun h hh => hh.resp2)
    (fun h hh => by
      have h1 : (opsOf h X.p₁).length ≤ 1 := by rcases hh.str.ops1 with e | e <;> rw [e] <;> simp
      have h2 : (opsOf h X.p₂).length ≤ i + 1 := by
        rcases hh.str.ops2 with e | e <;> rw [e] <;> simp [pre]
      omega) (fun h hh => ?_) hi
  obtain ⟨C, hC⟩ := hh.str.valid
  obtain ⟨C1, hs1⟩ := step_labOf (I := I) C X.p₁ X.op (X.allowed _ _)
  obtain ⟨C2, hs2⟩ := step_labOf (I := I) C X.p₂ (X.W i) (X.allowed _ _)
  have hv1 : I.Valid (h ++ [labOf I C X.p₁ X.op]) := ⟨C1, run_snoc hC hs1⟩
  have hv2 : I.Valid (h ++ [labOf I C X.p₂ (X.W i)]) := ⟨C2, run_snoc hC hs2⟩
  have hp1 : (labOf I C X.p₁ X.op).proc = X.p₁ := labOf_proc _ _ _ _
  have hp2 : (labOf I C X.p₂ (X.W i)).proc = X.p₂ := labOf_proc _ _ _ _
  by_cases d1 : X.DB (h ++ [labOf I C X.p₁ X.op]) (X.p₁, 0) (X.p₃, j)
  · by_cases d2 : X.DB (h ++ [labOf I C X.p₂ (X.W i)]) (X.p₂, i) (X.p₃, j)
    · left
      intro C' hC'
      rw [hC] at hC'; cases hC'
      exact ⟨d1, d2⟩
    · right
      refine ⟨_, Or.inr hp2, ?_⟩
      have hs := hh.str.append_lab2 X hC hh.resp2 hs2
      have hn3 : ¬ Invoked (h ++ [labOf I C X.p₂ (X.W i)]) (X.p₃, j) := by
        rw [Invoked, opsOf_concat, invOf_labOf]; simp [X.h23, hh.ops3, pre]
      refine ⟨hs, by rw [opsOf_concat, invOf_labOf]; simp [X.h23, hh.ops3], ?_, fun hd => ?_, d2⟩
      · exact X.resp2_of_not_db hn3 (by simp [respsOf_append, hh.resp2]) d2
      · exact hh.u1 (X.owner.decidedBefore_of_append hv2 (fun γ hγ => by
          simp only [List.mem_singleton] at hγ; rw [hγ, hp2]; exact X.h12.symm) hd)
  · right
    refine ⟨_, Or.inl hp1, ?_⟩
    have hs := hh.str.append_lab1 X hC hh.resp1 hs1
    refine ⟨hs, by rw [opsOf_concat, invOf_labOf]; simp [X.h13, hh.ops3], ?_, d1, fun hd => ?_⟩
    · rw [respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [hp1]; exact X.h12)]
      simpa using hh.resp2
    · exact hh.u2 (X.owner.decidedBefore_of_append hv1 (fun γ hγ => by
        simp only [List.mem_singleton] at hγ; rw [hγ, hp1]; exact X.h12) hd)

/-- **Claim 4.6.2** (for the next view): at line 5 (or 14), `op₁` and `op₂` are not decided before
the view `(p₃, j+1)` after `op₃` either (Claim 4.4.5 twice). -/
theorem u_next {i j : ℕ} {h : List (Label P A)} (hi : X.GInv i j h) :
    ¬ X.DB h (X.p₁, 0) (X.p₃, j + 1) ∧ ¬ X.DB h (X.p₂, i) (X.p₃, j + 1) := by
  have hv := hi.str.valid
  have hr3 := hi.resp3
  have hr1 := hi.resp1
  have hn22 : ¬ Invoked h (X.p₂, i + 1) := by
    simp only [Invoked]; rcases hi.str.ops2 with e | e <;> rw [e] <;> simp [pre]
  have hn11 : ¬ Invoked h (X.p₁, 1) := by
    simp only [Invoked]; rcases hi.str.ops1 with e | e <;> rw [e] <;> simp
  constructor
  · intro hd
    have h1 := X.claim_4_4_5' hv (a := (X.p₁, 0)) (q := X.p₃) X.h13 1 (j + 1) (by rw [hr3]) hd
      (X.p₂, i + 1) hn22 X.h23
    exact hi.u1 (X.claim_4_4_5' hv (a := (X.p₁, 0)) (q := X.p₂) X.h12 1 (i + 1)
      (by rw [hi.resp2]) h1 (X.p₃, j) hi.not_inv3 X.h23.symm)
  · intro hd
    have h1 := X.claim_4_4_5' hv (a := (X.p₂, i)) (q := X.p₃) X.h23 1 (j + 1) (by rw [hr3]) hd
      (X.p₁, 1) hn11 X.h13
    exact hi.u2 (X.claim_4_4_5' hv (a := (X.p₂, i)) (q := X.p₁) X.h12.symm 1 1
      (by rw [hr1]; rfl) h1 (X.p₃, j) hi.not_inv3 X.h13.symm)

/-! ### The second inner loop (lines 14–15) -/

/-- The invariant of the second inner loop. -/
structure GJ2 (i j : ℕ) (h : List (Label P A)) : Prop where
  str : X.Str i j h
  resp1 : respsOf h X.p₁ = []
  resp2 : (respsOf h X.p₂).length = i
  resp3 : (respsOf h X.p₃).length = j
  u1 : ¬ X.DB h (X.p₁, 0) (X.p₃, j + 1)
  u2 : ¬ X.DB h (X.p₂, i) (X.p₃, j + 1)
  e1 : X.E1 i j h

lemma not_db_cur {h : List (Label P A)} {a : OpId P} {j : ℕ}
    (hu : ¬ X.DB h a (X.p₃, j + 1)) : ¬ X.DB h a (X.p₃, j) :=
  fun hd => hu (hd.trans (X.db_program_order h (Nat.le_succ j)))

/-- The condition of line 14: after `p₃`'s next step, the next steps of `p₁` and `p₂` still decide
their operations before `op₃`. -/
def Cond2 (i j : ℕ) (h : List (Label P A)) : Prop :=
  ∀ C, I.run h = some C → ∀ C3, I.step C (labOf I C X.p₃ (X.R j)) = some C3 →
    X.DB (h ++ [labOf I C X.p₃ (X.R j), labOf I C3 X.p₁ X.op]) (X.p₁, 0) (X.p₃, j) ∧
      X.DB (h ++ [labOf I C X.p₃ (X.R j), labOf I C3 X.p₂ (X.W i)]) (X.p₂, i) (X.p₃, j)

/-- **Lines 14–15** (Claims 4.6.4, 4.6.5): the second inner loop terminates, and `op₃` does not
complete in it. -/
theorem second_loop (hsep : X.GVSep) {i j : ℕ} {h₀ : List (Label P A)} (hJ : X.GJ2 i j h₀) :
    ∃ h, X.GJ2 i j h ∧ ¬ X.Cond2 i j h ∧ h₀ <+: h := by
  refine exit_of_chain X.wf (X.GJ2 i j) (fun h => ¬ X.Cond2 i j h) X.p₃ X.p₃ j j (2 * (j + 1))
    (fun h hh => hh.str.valid) (fun h hh => hh.resp3) (fun h hh => hh.resp3)
    (fun h hh => by
      have : (opsOf h X.p₃).length ≤ j + 1 := by
        rcases hh.str.ops3 with e | e <;> rw [e] <;> simp [pre]
      omega) (fun h hh => ?_) hJ
  by_cases hc : X.Cond2 i j h
  swap
  · left; exact hc
  right
  obtain ⟨C, hC⟩ := hh.str.valid
  obtain ⟨C3, hs3⟩ := step_labOf (I := I) C X.p₃ (X.R j) (X.allowed _ _)
  set σ₃ := labOf I C X.p₃ (X.R j) with hσ₃
  have hp3 : σ₃.proc = X.p₃ := labOf_proc _ _ _ _
  have hrun3 : I.run (h ++ [σ₃]) = some C3 := run_snoc hC hs3
  have hv3 : I.Valid (h ++ [σ₃]) := ⟨C3, hrun3⟩
  have hs := hh.str.append_lab3 X hC hh.resp3 hs3
  have hback : ∀ a : OpId P, a.1 ≠ X.p₃ → ∀ x, ¬ X.DB h a x → ¬ X.DB (h ++ [σ₃]) a x :=
    fun a ha x hn hd => hn (X.owner.decidedBefore_of_append hv3 (fun γ hγ => by
      simp only [List.mem_singleton] at hγ; rw [hγ, hp3]; exact Ne.symm ha) hd)
  have hc' := hc C hC C3 hs3
  refine ⟨_, Or.inl hp3, hs, ?_, ?_, ?_, hback _ X.h13 _ hh.u1, hback _ X.h23 _ hh.u2, ?_⟩
  · rw [respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [hp3]; exact X.h13.symm)]
    simpa using hh.resp1
  · rw [respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [hp3]; exact X.h23.symm)]
    simpa using hh.resp2
  · -- Claim 4.6.4: `op₃` does not complete
    show (respsOf (h ++ [σ₃]) X.p₃).length = j
    rw [respsOf_concat]
    cases hσ : σ₃.retOf X.p₃ with
    | none => simpa using hh.resp3
    | some r =>
    exfalso
    have hr : (respsOf (h ++ [σ₃]) X.p₃).length = j + 1 := by
      rw [respsOf_concat, hσ]; simp [hh.resp3]
    have ho : opsOf (h ++ [σ₃]) X.p₃ = pre X.R (j + 1) := by
      have hle := I.run_resps_le_ops hrun3 X.p₃
      rcases hs.ops3 with e | e
      · rw [e, hr] at hle; simp [pre] at hle
      · exact e
    have hcs : X.CStr i j (h ++ [σ₃]) := by
      simpa using hs.cstr X le_rfl (t := []) (by simp) (by simpa using ho) (by simpa using hr)
    obtain ⟨C31, hs31⟩ := step_labOf (I := I) C3 X.p₁ X.op (X.allowed _ _)
    have hv31 : I.Valid (h ++ [σ₃] ++ [labOf I C3 X.p₁ X.op]) := ⟨C31, run_snoc hrun3 hs31⟩
    rcases X.gvDecided hsep hcs (Or.inl rfl) with hd | hd
    · exact hback _ X.h13 _ (X.not_db_cur hh.u1) hd
    · have h1 : X.DB (h ++ [σ₃] ++ [labOf I C3 X.p₁ X.op]) (X.p₁, 0) (X.p₃, j) := by
        simpa using hc'.1
      have := X.eq_of_db_both hv31 (Completed.mono (by simp only [Completed, hr]; omega)) h1
        (hd.append _)
      exact X.h13 (Prod.ext_iff.1 this).1
  · intro C' hC'
    rw [hrun3] at hC'; cases hC'
    simpa using hc'

/-! ### Lines 16–27 -/

/-- **Lines 16–27** (Claims 4.6.8–4.6.13, repaired). At the exit of the second inner loop, one of
three moves restores the main-loop invariant for the next view: a step of `p₁` or `p₂` that
decides nothing (`good_move`), or a race of `cas` operations (`caseA` or `race`, then
`cas_move`). -/
theorem exit_cases {V : ι → Type} [∀ i, DecidableEq (V i)] {v₀ : ∀ i, V i}
    {I : Impl A (fun i => casObject (V i) (v₀ i)) P L} (X : Ctx I) (hsep : X.GVSep) {i j : ℕ}
    {h : List (Label P A)} (hJ : X.GJ2 i j h) (hnc : ¬ X.Cond2 i j h) :
    ∃ i' y, X.GInv i' (j + 1) y ∧ h <+: y ∧ X.steps12 h < X.steps12 y ∧
      (i' = i ∨ (i' = i + 1 ∧ h.countP (Label.isTauOf X.p₁) < y.countP (Label.isTauOf X.p₁))) := by
  simp only [Cond2, not_forall] at hnc
  obtain ⟨C, hC, C3, hs3, hnot⟩ := hnc
  set σ₃ := labOf I C X.p₃ (X.R j) with hσ₃
  set H3 := h ++ [σ₃] with hH3
  have hp3 : σ₃.proc = X.p₃ := labOf_proc _ _ _ _
  have hrun3 : I.run H3 = some C3 := run_snoc hC hs3
  have hv3 : I.Valid H3 := ⟨C3, hrun3⟩
  have hs3' : X.Str i j H3 := hJ.str.append_lab3 X hC hJ.resp3 hs3
  have hback : ∀ a : OpId P, a.1 ≠ X.p₃ → ∀ x, ¬ X.DB h a x → ¬ X.DB H3 a x :=
    fun a ha x hn hd => hn (X.owner.decidedBefore_of_append hv3 (fun γ hγ => by
      simp only [List.mem_singleton] at hγ; rw [hγ, hp3]; exact Ne.symm ha) hd)
  have u1 : ¬ X.DB H3 (X.p₁, 0) (X.p₃, j + 1) := hback _ X.h13 _ hJ.u1
  have u2 : ¬ X.DB H3 (X.p₂, i) (X.p₃, j + 1) := hback _ X.h23 _ hJ.u2
  have hr1 : respsOf H3 X.p₁ = [] := by
    rw [hH3, respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [hp3]; exact X.h13.symm)]
    simpa using hJ.resp1
  have hr2 : (respsOf H3 X.p₂).length = i := by
    rw [hH3, respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [hp3]; exact X.h23.symm)]
    simpa using hJ.resp2
  obtain ⟨C31, hs31⟩ := step_labOf (I := I) C3 X.p₁ X.op (X.allowed _ _)
  obtain ⟨C32, hs32⟩ := step_labOf (I := I) C3 X.p₂ (X.W i) (X.allowed _ _)
  set σ₁ := labOf I C3 X.p₁ X.op with hσ₁
  set σ₂ := labOf I C3 X.p₂ (X.W i) with hσ₂
  have hp1 : σ₁.proc = X.p₁ := labOf_proc _ _ _ _
  have hp2 : σ₂.proc = X.p₂ := labOf_proc _ _ _ _
  have hs31' : X.Str i j (H3 ++ [σ₁]) := hs3'.append_lab1 X hrun3 hr1 hs31
  have hs32' : X.Str i j (H3 ++ [σ₂]) := hs3'.append_lab2 X hrun3 hr2 hs32
  have hv31 : I.Valid (H3 ++ [σ₁]) := hs31'.valid
  have hv32 : I.Valid (H3 ++ [σ₂]) := hs32'.valid
  have hσ3s : X.steps12 [σ₃] = 0 := by simp [steps12, hp3, X.h13.symm, X.h23.symm]
  -- the good moves
  by_cases g1 : X.DB (H3 ++ [σ₁]) (X.p₁, 0) (X.p₃, j + 1)
  swap
  · obtain ⟨y, hy, hpre⟩ := X.good_move hs31' (by
      rw [respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [hp1]; exact X.h12)]; simpa using hr2)
      g1 (fun hd => u2 (X.owner.decidedBefore_of_append hv31 (fun γ hγ => by
        simp only [List.mem_singleton] at hγ; rw [hγ, hp1]; exact X.h12) hd))
    refine ⟨i, y, hy, (List.prefix_append _ _).trans ((List.prefix_append _ _).trans hpre), ?_, Or.inl rfl⟩
    have h1 := X.steps12_mono hpre
    rw [hH3, X.steps12_append, X.steps12_append] at h1
    have : X.steps12 [σ₁] = 1 := by simp [steps12, hp1]
    omega
  by_cases g2 : X.DB (H3 ++ [σ₂]) (X.p₂, i) (X.p₃, j + 1)
  swap
  · have hr2' : (respsOf (H3 ++ [σ₂]) X.p₂).length = i := by
      rw [respsOf_concat]
      cases hσ : σ₂.retOf X.p₂ with
      | none => simpa using hr2
      | some r =>
        exfalso; apply g2
        apply decidedBefore_of_completed X.lin
        · simp only [Completed, respsOf_concat, hσ]; simp [hr2]
        · simp only [Invoked, opsOf_concat,
            Label.invOf_eq_none_of_proc_ne (show σ₂.proc ≠ X.p₃ by rw [hp2]; exact X.h23)]
          rcases hs3'.ops3 with e | e <;> rw [e] <;> simp [pre]
    obtain ⟨y, hy, hpre⟩ := X.good_move hs32' hr2'
      (fun hd => u1 (X.owner.decidedBefore_of_append hv32 (fun γ hγ => by
        simp only [List.mem_singleton] at hγ; rw [hγ, hp2]; exact X.h12.symm) hd)) g2
    refine ⟨i, y, hy, (List.prefix_append _ _).trans ((List.prefix_append _ _).trans hpre), ?_, Or.inl rfl⟩
    have h1 := X.steps12_mono hpre
    rw [hH3, X.steps12_append, X.steps12_append] at h1
    have : X.steps12 [σ₂] = 1 := by simp [steps12, hp2]
    omega
  -- the races
  have hcasDone : ∀ (Z : List (Label P A)) (D : Config A (fun i => casObject (V i) (v₀ i)) P L),
      h <+: Z → X.steps12 Z = X.steps12 h → Z.countP (Label.isTauOf X.p₁) = h.countP (Label.isTauOf X.p₁) →
      X.Str i j Z → I.run Z = some D → (respsOf Z X.p₂).length = i →
      ¬ X.DB Z (X.p₁, 0) (X.p₃, j + 1) → CasRace (I := I) D X.p₁ X.p₂ →
      ∃ i' y, X.GInv i' (j + 1) y ∧ h <+: y ∧ X.steps12 h < X.steps12 y ∧
        (i' = i ∨ (i' = i + 1 ∧ h.countP (Label.isTauOf X.p₁) < y.countP (Label.isTauOf X.p₁))) := by
    intro Z D hZ hZs hZt hsZ hD hrZ huZ hcas
    obtain ⟨y, hy, hpre⟩ := X.cas_move hsep hsZ hD hrZ huZ hcas
    have hs2 : X.steps12 (Z ++ [.tau X.p₂, .tau X.p₁]) = X.steps12 Z + 2 := by
      rw [X.steps12_append]; congr 1; simp [steps12, Label.proc]
    have ht2 : (Z ++ [Label.tau X.p₂, Label.tau X.p₁]).countP (Label.isTauOf X.p₁) =
        Z.countP (Label.isTauOf X.p₁) + 1 := by
      rw [List.countP_append]; congr 1; simp [X.h12.symm]
    have m1 := X.steps12_mono hpre
    have m2 : _ ≤ _ := List.IsPrefix.countP_le (p := Label.isTauOf X.p₁) hpre
    exact ⟨i + 1, y, hy, hZ.trans ((List.prefix_append _ _).trans hpre), by omega,
      Or.inr ⟨rfl, by omega⟩⟩
  have u13 : ¬ X.DB H3 (X.p₁, 0) (X.p₃, j) := X.not_db_cur u1
  have u23 : ¬ X.DB H3 (X.p₂, i) (X.p₃, j) := X.not_db_cur u2
  by_cases hA : ¬ X.DB (H3 ++ [σ₁]) (X.p₁, 0) (X.p₃, j) ∧ ¬ X.DB (H3 ++ [σ₂]) (X.p₂, i) (X.p₃, j)
  · -- line 16 true: Claim 4.6.8
    have he := hJ.e1 C hC
    have hcas := X.caseA hsep hJ.str hC hJ.resp1 hJ.resp2 hJ.resp3 he.1 he.2
      (X.not_db_cur hJ.u1) (X.not_db_cur hJ.u2) hs3 (by simpa [hH3] using hA.1)
      (by simpa [hH3] using hA.2)
    exact hcasDone h C (List.prefix_refl _) rfl rfl hJ.str hC hJ.resp2 hJ.u1 hcas
  -- line 16 false, and the step of `p_k` decides `op_k` before the next view
  have hZs : X.steps12 H3 = X.steps12 h := by
    simp [hH3, steps12, List.countP_append, hp3, X.h13.symm, X.h23.symm]
  have hZt : H3.countP (Label.isTauOf X.p₁) = h.countP (Label.isTauOf X.p₁) := by
    rw [hH3, List.countP_append]
    have : ([σ₃] : List (Label P A)).countP (Label.isTauOf X.p₁) = 0 := by
      have hf : σ₃.isTauOf X.p₁ = false := by
        rw [Bool.eq_false_iff]; intro ht
        rw [Label.isTauOf_eq_true_iff] at ht
        rw [ht] at hp3; exact X.h13 hp3
      simp [hf]
    omega
  have hnot' : ¬ (X.DB (H3 ++ [σ₁]) (X.p₁, 0) (X.p₃, j) ∧ X.DB (H3 ++ [σ₂]) (X.p₂, i) (X.p₃, j)) := by
    simpa [hH3] using hnot
  by_cases b1 : X.DB (H3 ++ [σ₁]) (X.p₁, 0) (X.p₃, j)
  · -- `k = 2`: `p₂`'s step decides `op₂` only before the next view
    have b2 : ¬ X.DB (H3 ++ [σ₂]) (X.p₂, i) (X.p₃, j) := fun h2 => hnot' ⟨b1, h2⟩
    have hcas := X.race hsep hs3' hrun3 (p := X.p₂) (q := X.p₁) (a := (X.p₂, i)) (b := (X.p₁, 0))
      X.h12.symm X.h23 X.h13 (Or.inr rfl) (Or.inl rfl) rfl (la := j + 1) (lb := j) (by omega) le_rfl
      hs32' hs31' g2 u2 b1 u13 (fun γ hγ hv => by
        have := X.bbad hsep hs32' (a := (X.p₂, i)) (b := (X.p₁, 0)) (Or.inr rfl) (Or.inl rfl)
          X.h12.symm g2 b2 (fun hd => u1 (X.owner.decidedBefore_of_append hv32 (fun γ' hγ' => by
            simp only [List.mem_singleton] at hγ'; rw [hγ', hp2]; exact X.h12.symm) hd))
          γ hγ (by simpa using hv)
        simpa using this)
    exact hcasDone H3 C3 (List.prefix_append _ _) hZs hZt hs3' hrun3 hr2 u1 hcas.symm
  · -- `k = 1`: `p₁`'s step decides `op₁` only before the next view
    have b2 : X.DB (H3 ++ [σ₂]) (X.p₂, i) (X.p₃, j) := by
      by_contra b2; exact hA ⟨b1, b2⟩
    have hcas := X.race hsep hs3' hrun3 (p := X.p₁) (q := X.p₂) (a := (X.p₁, 0)) (b := (X.p₂, i))
      X.h12 X.h13 X.h23 (Or.inl rfl) (Or.inr rfl) rfl (la := j + 1) (lb := j) (by omega) le_rfl
      hs31' hs32' g1 u1 b2 u23 (fun γ hγ hv => by
        have := X.bbad hsep hs31' (a := (X.p₁, 0)) (b := (X.p₂, i)) (Or.inl rfl) (Or.inr rfl)
          X.h12 g1 b1 (fun hd => u2 (X.owner.decidedBefore_of_append hv31 (fun γ' hγ' => by
            simp only [List.mem_singleton] at hγ'; rw [hγ', hp1]; exact X.h12) hd))
          γ hγ (by simpa using hv)
        simpa using this)
    exact hcasDone H3 C3 (List.prefix_append _ _) hZs hZt hs3' hrun3 hr2 u1 hcas

end Generic

end Ctx

end Podc.HelpFreeWaitFree
