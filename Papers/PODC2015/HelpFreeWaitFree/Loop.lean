import Papers.PODC2015.HelpFreeWaitFree.Claims
import Papers.PODC2015.HelpFreeWaitFree.Starvation

/-!
# The construction of Figure 4.1 (memory-independent part)

* `labOf I C p o` — the next label of `p` following its program: invoke `o` if idle, otherwise
  the next step of the pending operation (paper: `h ∘ p`).
* `X.J n h` — the inner-loop invariant (lines 5–12): situation `Std n h` and the order of `op₁`
  and `op₂ = (p₂, n)` is not decided (Claim 4.5.4, Observation 4.5.5).
* `X.Crit n h` — the inner loop exits: the next step of `p₁` decides `op₁` before `op₂`, the
  next step of `p₂` decides `op₂` before `op₁` (Observation 4.5.9).
* `Std.undecided` — **Claim 4.5.7**: while undecided, neither `op₁` nor `op₂` is completed.
* `loop_terminates` — **Claim 4.5.8**: the inner loop is finite (by wait-freedom).
* `X.Inv n h` — the main-loop invariant at line 4 of iteration `n + 1` (Claim 4.5.4).
* `critical_step` — lines 13–16 and Claims 4.5.11–4.5.14, given the outcome of Claim 4.5.10
  (which depends on the primitives and is proved in `Theorem43.lean`): if after `p₂`'s step `p₁`'s
  step is invisible to `p₂` and `p₃`, then after `p₂` completes `op₂` the invariant holds for
  `n + 1`, and `p₁` took one more step.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]

/-- The next label of `p` following its program: invoke `o` if idle, else take the next step. -/
noncomputable def labOf (I : Impl A B P L) (C : Config A B P L) (p : P) (o : A.Op) : Label P A :=
  if C.pend p = none then .inv p o else I.nextLabel C p

lemma labOf_proc (I : Impl A B P L) (C : Config A B P L) (p : P) (o : A.Op) :
    (labOf I C p o).proc = p := by
  unfold labOf; split_ifs
  · rfl
  · exact I.nextLabel_proc C p

lemma step_labOf {I : Impl A B P L} (C : Config A B P L) (p : P) (o : A.Op) (ho : I.allowed p o) :
    ∃ C', I.step C (labOf I C p o) = some C' := by
  unfold labOf
  split_ifs with h
  · exact ⟨_, Impl.step_inv_eq_some h ho⟩
  · exact Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p h)

lemma invOf_labOf (I : Impl A B P L) (C : Config A B P L) (p q : P) (o : A.Op) :
    (labOf I C p o).invOf q = if C.pend p = none ∧ p = q then some o else none := by
  unfold labOf
  by_cases h : C.pend p = none
  · by_cases hq : p = q
    · subst hq; simp [h]
    · simp [h, hq]
  · simp [h, I.nextLabel_invOf]

namespace Ctx

variable {I : Impl A B P L} (X : Ctx I)

/-! ### The inner loop -/

/-- **Claim 4.5.7**: while the order of `op₁` and `op₂` is undecided, neither is completed. -/
lemma Std.undecided {n m : ℕ} {h : List (Label P A)} (hstd : X.Std n h) (hsep : X.Sep n m)
    (h1 : ¬ X.DB h (X.p₁, 0) (X.p₂, n)) (h2 : ¬ X.DB h (X.p₂, n) (X.p₁, 0)) :
    respsOf h X.p₁ = [] ∧ (respsOf h X.p₂).length = n := by
  have hno3 : ¬ Invoked h (X.p₃, 0) := by simp [Invoked, hstd.ops3]
  constructor
  · by_contra hne
    have hc : Completed h (X.p₁, 0) := by
      simp only [Completed]; exact List.length_pos_iff.2 hne
    rcases X.claim_4_5_2 hstd hsep (Or.inl (decidedBefore_of_completed X.lin hc hno3)) with h' | h'
    · exact h1 h'
    · exact h2 h'
  · by_contra hne
    have hc : Completed h (X.p₂, n) := by
      simp only [Completed]; have := hstd.resp2; omega
    rcases X.claim_4_5_2 hstd hsep (Or.inr (decidedBefore_of_completed X.lin hc hno3)) with h' | h'
    · exact h1 h'
    · exact h2 h'

/-- The inner-loop invariant. -/
structure J (n : ℕ) (h : List (Label P A)) : Prop where
  std : X.Std n h
  und12 : ¬ X.DB h (X.p₁, 0) (X.p₂, n)
  und21 : ¬ X.DB h (X.p₂, n) (X.p₁, 0)

/-- The exit condition of the inner loop. -/
def Crit (n : ℕ) (h : List (Label P A)) : Prop :=
  ∀ C, I.run h = some C → X.DB (h ++ [labOf I C X.p₁ X.op]) (X.p₁, 0) (X.p₂, n) ∧
    X.DB (h ++ [labOf I C X.p₂ (X.W n)]) (X.p₂, n) (X.p₁, 0)

/-- A step of `p₁` following its program preserves `Std` (while `op₁` is not completed). -/
lemma Std.append_lab1 {n : ℕ} {h : List (Label P A)} {C C' : Config A B P L} (hstd : X.Std n h)
    (hC : I.run h = some C) (hr : respsOf h X.p₁ = [])
    (hs : I.step C (labOf I C X.p₁ X.op) = some C') :
    X.Std n (h ++ [labOf I C X.p₁ X.op]) := by
  have hv : I.Valid (h ++ [labOf I C X.p₁ X.op]) := ⟨C', by rw [I.run_concat, hC]; exact hs⟩
  refine Std.append X hstd hv (fun γ hγ => by simp at hγ; subst hγ; left; exact labOf_proc _ _ _ _) ?_ ?_
  · rw [opsOf_concat, invOf_labOf]
    by_cases hp : C.pend X.p₁ = none
    · have hl := I.run_idle_counts hC hp
      rw [hr] at hl
      simp [List.eq_nil_of_length_eq_zero hl, hp]
    · simp only [hp, false_and, ↓reduceIte, Option.toList_none, List.append_nil]; exact hstd.ops1
  · rw [opsOf_concat, invOf_labOf]; simp only [X.h12, and_false, ↓reduceIte, Option.toList_none,
      List.append_nil]; exact hstd.ops2

/-- A step of `p₂` following its program preserves `Std` (while `op₂` is not completed). -/
lemma Std.append_lab2 {n : ℕ} {h : List (Label P A)} {C C' : Config A B P L} (hstd : X.Std n h)
    (hC : I.run h = some C) (hr : (respsOf h X.p₂).length = n)
    (hs : I.step C (labOf I C X.p₂ (X.W n)) = some C') :
    X.Std n (h ++ [labOf I C X.p₂ (X.W n)]) := by
  have hv : I.Valid (h ++ [labOf I C X.p₂ (X.W n)]) := ⟨C', by rw [I.run_concat, hC]; exact hs⟩
  refine Std.append X hstd hv (fun γ hγ => by simp at hγ; subst hγ; right; exact labOf_proc _ _ _ _) ?_ ?_
  · rw [opsOf_concat, invOf_labOf]; simp only [Ne.symm X.h12, and_false, ↓reduceIte,
      Option.toList_none, List.append_nil]; exact hstd.ops1
  · rw [opsOf_concat, invOf_labOf]
    by_cases hp : C.pend X.p₂ = none
    · have hl := I.run_idle_counts hC hp
      rw [hr] at hl
      have : opsOf h X.p₂ = pre X.W n := by
        rcases hstd.ops2 with e | e
        · exact e
        · rw [e] at hl; simp [pre] at hl
      right; simp [this, hp, pre_succ']
    · simp only [hp, false_and, ↓reduceIte, Option.toList_none, List.append_nil]; exact hstd.ops2

/-- One iteration of the inner loop: either the loop exits, or `p₁` or `p₂` takes a step that
keeps the order of `op₁` and `op₂` undecided (Observation 4.5.5). -/
lemma loop_step {n m : ℕ} {h : List (Label P A)} (hJ : X.J n h) (hsep : X.Sep n m) :
    X.Crit n h ∨ ∃ γ, (γ.proc = X.p₁ ∨ γ.proc = X.p₂) ∧ X.J n (h ++ [γ]) := by
  obtain ⟨hr1, hr2⟩ := Std.undecided X hJ.std hsep hJ.und12 hJ.und21
  obtain ⟨C, hC⟩ := hJ.std.valid
  obtain ⟨C1, hs1⟩ := step_labOf (I := I) C X.p₁ X.op (X.allowed _ _)
  obtain ⟨C2, hs2⟩ := step_labOf (I := I) C X.p₂ (X.W n) (X.allowed _ _)
  by_cases d1 : X.DB (h ++ [labOf I C X.p₁ X.op]) (X.p₁, 0) (X.p₂, n)
  · by_cases d2 : X.DB (h ++ [labOf I C X.p₂ (X.W n)]) (X.p₂, n) (X.p₁, 0)
    · left
      intro C' hC'
      rw [hC] at hC'; cases hC'
      exact ⟨d1, d2⟩
    · right
      refine ⟨_, Or.inr (labOf_proc _ _ _ _), Std.append_lab2 X hJ.std hC hr2 hs2, fun hd => ?_, d2⟩
      have := X.owner h _ _ _ ⟨C2, by rw [I.run_concat, hC]; exact hs2⟩ hd hJ.und12
      rw [labOf_proc] at this; exact X.h12 this.symm
  · right
    refine ⟨_, Or.inl (labOf_proc _ _ _ _), Std.append_lab1 X hJ.std hC hr1 hs1, d1, fun hd => ?_⟩
    have := X.owner h _ _ _ ⟨C1, by rw [I.run_concat, hC]; exact hs1⟩ hd hJ.und21
    rw [labOf_proc] at this; exact X.h12 this

/-- Counting labels: every label of `p₁`, `p₂` that is not a response is a step or an
invocation. -/
lemma count_le {l : List (Label P A)} {p q : P} (hl : ∀ γ ∈ l, γ.proc = p ∨ γ.proc = q)
    (hret : ∀ γ ∈ l, ∀ p' r, γ ≠ .ret p' r) :
    l.length ≤ l.countP (Label.isTauOf p) + l.countP (Label.isTauOf q) + (opsOf l p).length +
      (opsOf l q).length := by
  induction l with
  | nil => simp
  | cons γ l ih =>
    have ih' := ih (fun γ' h' => hl γ' (List.mem_cons_of_mem _ h'))
      (fun γ' h' => hret γ' (List.mem_cons_of_mem _ h'))
    have hγ := hl γ (by simp)
    have hγr := hret γ (by simp)
    simp only [List.length_cons, List.countP_cons, opsOf_cons, List.length_append]
    cases γ with
    | inv p' o =>
      simp only [Label.proc] at hγ
      rcases hγ with rfl | rfl <;> simp <;> omega
    | tau p' =>
      simp only [Label.proc] at hγ
      rcases hγ with rfl | rfl <;> simp <;> omega
    | ret p' r => exact absurd rfl (hγr p' r)

/-- **Claim 4.5.8**: the inner loop is finite. -/
theorem loop_terminates {n m : ℕ} {h₀ : List (Label P A)} (hJ : X.J n h₀) (hsep : X.Sep n m) :
    ∃ h, X.J n h ∧ X.Crit n h ∧ h₀ <+: h := by
  classical
  by_contra hcon
  push Not at hcon
  -- one step of the loop
  have hstep : ∀ h, X.J n h → h₀ <+: h →
      ∃ γ, (γ.proc = X.p₁ ∨ γ.proc = X.p₂) ∧ X.J n (h ++ [γ]) := by
    intro h hJ' hpre
    rcases X.loop_step hJ' hsep with hc | hc
    · exact absurd hpre (hcon h hJ' hc)
    · exact hc
  let G := {h : List (Label P A) // X.J n h ∧ h₀ <+: h}
  have hnext : ∀ g : G, ∃ γ, (γ.proc = X.p₁ ∨ γ.proc = X.p₂) ∧ X.J n (g.1 ++ [γ]) :=
    fun g => hstep g.1 g.2.1 g.2.2
  choose γf hγf hJf using hnext
  let nxt : G → G := fun g => ⟨g.1 ++ [γf g], hJf g, g.2.2.trans (List.prefix_append _ _)⟩
  let E : ℕ → List (Label P A) := fun k => (nxt^[k] ⟨h₀, hJ, List.prefix_refl _⟩).1
  have hE : ∀ k, E (k + 1) = E k ++ [γf (nxt^[k] ⟨h₀, hJ, List.prefix_refl _⟩)] := by
    intro k; simp only [E, Function.iterate_succ_apply']; rfl
  have hEJ : ∀ k, X.J n (E k) := fun k => (nxt^[k] ⟨h₀, hJ, List.prefix_refl _⟩).2.1
  have hlen : ∀ k, (E k).length = h₀.length + k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [hE, List.length_append, ih]; simp; omega
  have hresp : ∀ k, respsOf (E k) X.p₁ = [] ∧ (respsOf (E k) X.p₂).length = n :=
    fun k => Std.undecided X (hEJ k).std hsep (hEJ k).und12 (hEJ k).und21
  have hmono : ∀ k, E k <+: E (k + 1) := fun k => by rw [hE]; exact List.prefix_append _ _
  -- the labels after `h₀`
  have hcount : ∀ k, k ≤ (E k).countP (Label.isTauOf X.p₁) + (E k).countP (Label.isTauOf X.p₂) +
      (opsOf (E k) X.p₁).length + (opsOf (E k) X.p₂).length := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      have hγ := hγf (nxt^[k] ⟨h₀, hJ, List.prefix_refl _⟩)
      have hnr : ∀ p' r, γf (nxt^[k] ⟨h₀, hJ, List.prefix_refl _⟩) ≠ .ret p' r := by
        intro p' r he
        have h1 := hresp (k + 1)
        have h2 := hresp k
        rw [hE, he] at h1
        rcases hγ with hp | hp <;> rw [he] at hp <;> simp only [Label.proc] at hp <;> subst hp
        · simp [respsOf_append] at h1
        · simp only [respsOf_append, respsOf_cons, Label.retOf_ret, ↓reduceIte,
            Option.toList_some, respsOf_nil, List.append_nil, List.length_append,
            List.length_singleton] at h1
          omega
      have := count_le (l := [γf (nxt^[k] ⟨h₀, hJ, List.prefix_refl _⟩)]) (p := X.p₁) (q := X.p₂)
        (by simpa using hγ) (by simpa using hnr)
      rw [hE, List.countP_append, List.countP_append, opsOf_append, opsOf_append]
      simp only [List.length_append, List.length_singleton] at this ⊢
      omega
  have hops1 : ∀ k, (opsOf (E k) X.p₁).length ≤ 1 := fun k => by
    rcases (hEJ k).std.ops1 with e | e <;> rw [e] <;> simp
  have hops2 : ∀ k, (opsOf (E k) X.p₂).length ≤ n + 1 := fun k => by
    rcases (hEJ k).std.ops2 with e | e <;> rw [e] <;> simp [pre]
  have hval : ∀ k, I.Valid (E k) := fun k => (hEJ k).std.valid
  have hlen' : ∀ k, k ≤ (E k).length := fun k => by rw [hlen]; omega
  -- one of `p₁`, `p₂` takes unboundedly many steps without returning
  by_cases hb : ∀ N, ∃ k, N ≤ (E k).countP (Label.isTauOf X.p₁)
  · exact false_of_starving_chain X.wf E hmono hlen' hval X.p₁
      (fun k => by rw [(hresp k).1, (hresp 0).1]) hb
  · push Not at hb
    obtain ⟨N₁, hN₁⟩ := hb
    apply false_of_starving_chain X.wf E hmono hlen' hval X.p₂
      (fun k => by rw [(hresp k).2, (hresp 0).2])
    intro N
    refine ⟨N + N₁ + n + 2, ?_⟩
    have := hcount (N + N₁ + n + 2)
    have := hN₁ (N + N₁ + n + 2)
    have := hops1 (N + N₁ + n + 2)
    have := hops2 (N + N₁ + n + 2)
    omega

/-! ### The main loop -/

/-- The main-loop invariant at line 4 of iteration `n + 1` (Claim 4.5.4): `p₂` completed exactly
`W(n)`, decided before `op₁`; `op₁` is not completed and not decided before `op₂ = (p₂, n)`. -/
structure Inv (n : ℕ) (h : List (Label P A)) : Prop where
  std : X.Std n h
  ops2 : opsOf h X.p₂ = pre X.W n
  resp2 : (respsOf h X.p₂).length = n
  resp1 : respsOf h X.p₁ = []
  und12 : ¬ X.DB h (X.p₁, 0) (X.p₂, n)

/-- At line 4 the inner-loop invariant holds (`op₂` has not started, so it is not decided before
`op₁`: Observation 4.4.4 (2)). -/
lemma Inv.j {n : ℕ} {h : List (Label P A)} (hi : X.Inv n h) : X.J n h := by
  refine ⟨hi.std, hi.und12, ?_⟩
  have hcur : curOp h X.p₁ = (X.p₁, 0) := by simp [curOp, hi.resp1]
  rw [← hcur]
  exact X.not_decidedBefore_cur hi.std.valid (by simp [Invoked, hi.ops2, pre]) X.h12.symm

/-- The invariant holds initially. -/
lemma inv_zero : X.Inv 0 [] := by
  refine ⟨⟨⟨I.initCfg, rfl⟩, Or.inl rfl, Or.inl rfl, by simp, rfl, fun _ _ _ _ => rfl,
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩, rfl, rfl, rfl, ?_⟩
  have hcur : curOp ([] : List (Label P A)) X.p₂ = (X.p₂, 0) := rfl
  rw [← hcur]
  exact X.not_decidedBefore_cur ⟨I.initCfg, rfl⟩ (by simp [Invoked]) X.h12

/-- **Lines 13–16 and Claims 4.5.11–4.5.14.** Suppose the inner loop exited at `h` and (Claim
4.5.10, Corollary 4.1) the next steps of `p₂` and then `p₁` are base-object steps, `p₂`'s step
decides `op₂` before `op₁`, and `p₁`'s following step does not change the memory (a failed
`cas`), so that after it `p₂` and `p₃` cannot tell the difference. Then after `p₂` completes
`op₂`, the main-loop invariant holds for `n + 1`, and `p₁` took one more step. -/
theorem critical_step {n m m' : ℕ} {h : List (Label P A)} (hJ : X.J n h) (hsep : X.Sep n m)
    (hsep' : X.Sep (n + 1) m') {Cx Cy : Config A B P L}
    (hx : I.run (h ++ [.tau X.p₂]) = some Cx) (hy : I.run (h ++ [.tau X.p₂, .tau X.p₁]) = some Cy)
    (hag : Impl.AgreeOn {X.p₂, X.p₃} Cx Cy)
    (hdx : X.DB (h ++ [.tau X.p₂]) (X.p₂, n) (X.p₁, 0)) :
    ∃ y, X.Inv (n + 1) y ∧ h <+: y ∧
      h.countP (Label.isTauOf X.p₁) < y.countP (Label.isTauOf X.p₁) := by
  obtain ⟨hr1, hr2⟩ := Std.undecided X hJ.std hsep hJ.und12 hJ.und21
  set x := h ++ [.tau X.p₂] with hxdef
  set y := h ++ [.tau X.p₂, .tau X.p₁] with hydef
  have hyx : y = x ++ [.tau X.p₁] := by simp [hxdef, hydef]
  -- `p₂` was pending at `h` (it took a step), so `op₂` was invoked
  obtain ⟨C, hC⟩ := hJ.std.valid
  have hstep2 : I.step C (.tau X.p₂) = some Cx := by
    rw [hxdef, I.run_concat, hC] at hx; exact hx
  have hpend2 : C.pend X.p₂ ≠ none := (Impl.step_tau hstep2).1
  have hops2h : opsOf h X.p₂ = pre X.W (n + 1) := by
    have hl := I.run_pend_counts hC hpend2
    rcases hJ.std.ops2 with e | e
    · rw [e, hr2] at hl; simp [pre] at hl
    · exact e
  -- `p₂` completes `op₂` after `x`
  obtain ⟨s, Ex, h1, h2, -, h4, h5, h6⟩ := X.exists_finish hx X.p₂ (X.W n)
  have hpx : Cx.pend X.p₂ ≠ none := by rw [(Impl.step_tau hstep2).2.1]; exact hpend2
  have hs0 : opsOf s X.p₂ = [] := h5 hpx
  have hrunx : I.run (x ++ s) = some Ex := by rw [I.run_append_of_eq hx, h1]
  obtain ⟨Ey, hruny, hagE⟩ := transport (Q := {X.p₂, X.p₃}) hx hy hag
    (fun γ hγ => by simp [h2 γ hγ]) hrunx
  rw [hyx] at hruny
  set x' := x ++ s with hx'
  set y' := x ++ [.tau X.p₁] ++ s with hy'
  have hs1 : ∀ q, q ≠ X.p₂ → opsOf s q = [] ∧ respsOf s q = [] := fun q hq => opsOf_of_proc h2 hq
  -- facts on `x'` and `y'`
  have hopsP2 : ∀ u : List (Label P A), (∀ γ ∈ u, γ.proc = X.p₁) →
      opsOf (x ++ u ++ s) X.p₂ = pre X.W (n + 1) ∧ (respsOf (x ++ u ++ s) X.p₂).length = n + 1 := by
    intro u hu
    have hu2 := opsOf_of_proc hu X.h12.symm
    simp [hxdef, hops2h, hu2.1, hu2.2, hs0, hr2, h6]
  have hopsP1 : ∀ u : List (Label P A), (∀ γ ∈ u, γ.proc = X.p₁ ∧ ∀ o, γ ≠ .inv X.p₁ o) →
      opsOf (x ++ u ++ s) X.p₁ = opsOf h X.p₁ := by
    intro u hu
    have : opsOf u X.p₁ = [] := by
      simp only [opsOf, List.filterMap_eq_nil_iff]
      intro γ hγ
      cases γ with
      | inv q o =>
        obtain ⟨hq1, hq2⟩ := hu _ hγ; simp only [Label.proc] at hq1; subst hq1
        exact absurd rfl (hq2 o)
      | _ => rfl
    simp [hxdef, this, (hs1 X.p₁ X.h12).1]
  have hno3 : ∀ u : List (Label P A), (∀ γ ∈ u, γ.proc = X.p₁) → opsOf (x ++ u ++ s) X.p₃ = [] := by
    intro u hu
    have := opsOf_of_proc hu X.h13.symm
    simp [hxdef, hJ.std.ops3, this.1, (hs1 X.p₃ X.h23.symm).1]
  have hother : ∀ u : List (Label P A), (∀ γ ∈ u, γ.proc = X.p₁) → ∀ q, q ≠ X.p₁ → q ≠ X.p₂ →
      q ≠ X.p₃ → opsOf (x ++ u ++ s) q = [] := by
    intro u hu q hq1 hq2 hq3
    have := opsOf_of_proc hu hq1
    simp [hxdef, hJ.std.other q hq1 hq2 hq3, this.1, (hs1 q hq2).1]
  have hstd' : ∀ u : List (Label P A), (∀ γ ∈ u, γ.proc = X.p₁ ∧ ∀ o, γ ≠ .inv X.p₁ o) →
      I.Valid (x ++ u ++ s) → X.Std (n + 1) (x ++ u ++ s) := by
    intro u hu hv
    have hu' : ∀ γ ∈ u, γ.proc = X.p₁ := fun γ hγ => (hu γ hγ).1
    refine ⟨hv, by rw [hopsP1 u hu]; exact hJ.std.ops1, Or.inl (hopsP2 u hu').1,
      (hopsP2 u hu').2.ge, hno3 u hu', hother u hu', fun i hi => ?_⟩
    have happ : x ++ u ++ s = x ++ (u ++ s) := by simp
    rw [happ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact (((hJ.std.dec i hi).append [.tau X.p₂]).append (u ++ s))
    · exact hdx.append (u ++ s)
  have hvx : I.Valid x' := ⟨Ex, hrunx⟩
  have hsx' : X.Std (n + 1) x' := by
    have := hstd' [] (by simp) (by simpa using hvx); simpa using this
  have hsy' : X.Std (n + 1) y' := hstd' [.tau X.p₁] (by simp [Label.proc]) ⟨Ey, hruny⟩
  have hy2 := hopsP2 [.tau X.p₁] (by simp [Label.proc])
  have hx2 := hopsP2 [] (by simp)
  simp only [List.append_nil] at hx2
  rw [← hx'] at hx2
  rw [← hy'] at hy2
  -- Claim 4.5.13: `op₁` is not decided before `op₃` after `x'`
  have hnd13 : ¬ X.DB x' (X.p₁, 0) (X.p₃, 0) := by
    intro hd
    have e : x' = h ++ ([.tau X.p₂] ++ s) := by simp [hx', hxdef]
    have hvx' := hvx
    rw [e] at hd hvx'
    have hback : X.DB h (X.p₁, 0) (X.p₃, 0) := by
      refine X.owner.decidedBefore_of_append (s := [.tau X.p₂] ++ s) hvx' (fun γ hγ => ?_) hd
      rcases List.mem_append.1 hγ with hγ | hγ
      · simp at hγ; subst hγ; exact X.h12.symm
      · rw [h2 γ hγ]; exact X.h12.symm
    rcases X.claim_4_5_2 hJ.std hsep (Or.inl hback) with h' | h'
    · exact hJ.und12 h'
    · exact hJ.und21 h'
  -- Claim 4.5.14 (for `x'`): `op₁` is not decided before the next operation of `p₂`
  have hcurx : curOp x' X.p₂ = (X.p₂, n + 1) := by
    simp only [curOp, hx2.2]
  have hnd12x : ¬ X.DB x' (X.p₁, 0) (X.p₂, n + 1) := by
    intro hd
    rw [← hcurx] at hd
    exact hnd13 (X.claim_4_4_5 hsx'.valid X.h12 hd (by simp [Invoked, hsx'.ops3])
      (by rw [hcurx]; exact fun e => X.h23 (Prod.ext_iff.1 e).1.symm))
  -- Claim 4.5.3 (2) at level `n + 1`: the same holds after `y'`
  have hnd12y : ¬ X.DB y' (X.p₁, 0) (X.p₂, n + 1) := by
    intro hd
    exact X.claim_4_5_3_2 hsx' hsy' hrunx hruny hagE.symm hsep' hx2.2 hy2.2 hnd12x hd
  have hr1y : respsOf y' X.p₁ = [] := by
    by_contra hne
    have hc : Completed y' (X.p₁, 0) := by simp only [Completed]; exact List.length_pos_iff.2 hne
    exact hnd12y (decidedBefore_of_completed X.lin hc
      (by simp [Invoked, hy2.1, pre]))
  refine ⟨y', ⟨hsy', hy2.1, hy2.2, hr1y, hnd12y⟩, ?_, ?_⟩
  · rw [hy', hxdef]; simp only [List.append_assoc]; exact List.prefix_append _ _
  · rw [hy', hxdef]; simp [List.countP_append]

end Ctx

end Podc.HelpFreeWaitFree
