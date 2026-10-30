import Papers.PODC2011.RulesOfThumb.NonStationary

/-!
# Examples 4.2 and 4.3: neither hypothesis of Theorem 4.1 can be dropped

Two nodes (`Fin 2`; the paper's nodes 1 and 2 are `0` and `1`), action space `Bool` with
`x = false`, `y = true`.

* **Example 4.2** (`ex42`): node `1` copies node `0`'s action; node `0` chooses `y` iff node `1`'s
  action changed from `x` to `y` at some point of the history. Self-independent, not bounded-recall,
  convergent, with the two stable states `(x,x)` and `(y,y)`.
* **Example 4.3** (`ex43`): `fᵢ(x,x) = y`, otherwise node `i` keeps its action. Historyless (so
  bounded-recall), not self-independent, convergent, with the three stable states other than
  `(x,x)`.

We also include a sanity check that the hypotheses of Theorem 4.1 are satisfiable (`copySys`: each
node copies the other one) and a generic lemma `eventually_cur_eq_of` used for convergence proofs.
-/

namespace Podc.RulesOfThumb

open Filter

namespace System

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι] {F : System A}

/-- If from step `m₀` on node `j` always reacts with `v`, and `j` is activated infinitely often,
then node `j`'s action is eventually `v`. -/
lemma eventually_cur_eq_of {s₀ : Hist A} {σ : ℕ → Finset ι} {j : ι} {v : A j} {m₀ : ℕ}
    (hv : ∀ m, m₀ ≤ m → j ∈ σ ((F.run s₀ σ m).time + 1) →
      F.f j ((F.run s₀ σ m).time + 1) (F.run s₀ σ m) = v)
    (hf : ∃ᶠ t in atTop, j ∈ σ t) : ∀ᶠ m in atTop, (F.run s₀ σ m).cur j = v := by
  obtain ⟨t, hj, ht⟩ := (hf.and_eventually (eventually_gt_atTop (s₀.time + m₀))).exists
  set m₁ := t - s₀.time - 1
  have htm : (F.run s₀ σ m₁).time + 1 = t := by simp [m₁]; omega
  rw [eventually_atTop]
  refine ⟨m₁ + 1, fun m hm => ?_⟩
  induction m, hm using Nat.le_induction with
  | base =>
    have hj' : j ∈ σ ((F.run s₀ σ m₁).time + 1) := htm ▸ hj
    rw [run_succ, step_cur_of_mem _ hj']; exact hv _ (by omega) hj'
  | succ m hm ih =>
    rw [run_succ]
    by_cases hjm : j ∈ σ ((F.run s₀ σ m).time + 1)
    · rw [step_cur_of_mem _ hjm]; exact hv _ (by omega) hjm
    · rw [step_cur_of_not_mem _ hjm, ih]

lemma convergesTo_of_forall {s₀ : Hist A} {σ : ℕ → Finset ι} {a : Profile A} [Finite ι]
    (h : ∀ j, ∀ᶠ m in atTop, (F.run s₀ σ m).cur j = a j) : F.ConvergesTo s₀ σ a :=
  (eventually_all.mpr h).mono fun _ hm => funext hm

lemma isSchedule_univ [Fintype ι] [Nonempty ι] : IsSchedule (fun _ : ℕ => (Finset.univ : Finset ι)) :=
  fun _ => Finset.univ_nonempty

lemma fair_univ [Fintype ι] : Fair (fun _ : ℕ => (Finset.univ : Finset ι)) :=
  fun i => Frequently.of_forall fun _ => Finset.mem_univ i

end System

/-- Bool-valued profiles of two nodes. -/
abbrev P2 := Profile (fun _ : Fin 2 => Bool)

/-- The profile `(a, b)`. -/
def pr (a b : Bool) : P2 := ![a, b]

lemma pr_eq_iff (a b : Bool) (p : P2) : p = pr a b ↔ p 0 = a ∧ p 1 = b := by
  constructor
  · rintro rfl; simp [pr]
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp [pr, h0, h1]

open Podc.RulesOfThumb.System

/-! ### Example 4.2 -/

/-- Node `1`'s action changed from `x = false` to `y = true` somewhere in the history (the list
is most recent first, so `true` immediately precedes `false`). -/
def ChangedXY (l : List Bool) : Prop := ∃ l₁ l₂, l = l₁ ++ true :: false :: l₂

open Classical in
/-- Example 4.2. -/
noncomputable def ex42 : System (fun _ : Fin 2 => Bool) where
  f i _ h := if i = 0 then decide (ChangedXY (h.toList.map (· 1))) else h.cur 0

open Classical in
lemma ex42_f0 (t : ℕ) (h : Hist (fun _ : Fin 2 => Bool)) :
    ex42.f 0 t h = decide (ChangedXY (h.toList.map (· 1))) := by simp [ex42]

lemma ex42_f1 (t : ℕ) (h : Hist (fun _ : Fin 2 => Bool)) : ex42.f 1 t h = h.cur 0 := by
  simp [ex42]

lemma map_eq_of_forall₂ {l l' : List P2}
    (he : List.Forall₂ (fun a b : P2 => ∀ j, j ≠ 0 → a j = b j) l l') :
    l.map (· 1) = l'.map (· 1) := by
  induction he with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hab 1 (by decide), ih]

lemma map_eq_of_othersEq {h h' : Hist (fun _ : Fin 2 => Bool)} (he : OthersEq 0 h h') :
    h.toList.map (· 1) = h'.toList.map (· 1) := map_eq_of_forall₂ he

theorem ex42_selfIndependent : ex42.SelfIndependent := by
  intro i h h' he
  fin_cases i
  · have he' : OthersEq 0 h h' := he
    simp only [Fin.zero_eta, ex42_f0]
    rw [map_eq_of_othersEq he']
  · simp only [Fin.mk_one, ex42_f1]
    exact (List.forall₂_cons.mp he).1 0 (by decide)

/-- Node `0`'s reaction function in Example 4.2 does not have bounded recall. -/
theorem ex42_not_hasRecall (k : ℕ) : ¬ ex42.HasRecall 0 k := by
  intro hrec
  set h₁ : Hist (fun _ : Fin 2 => Bool) := ⟨pr true true, List.replicate k (pr true true) ++ [pr false false]⟩
  set h₂ : Hist (fun _ : Fin 2 => Bool) := ⟨pr true true, List.replicate (k + 1) (pr true true)⟩
  have ht : h₁.time = h₂.time := by simp [h₁, h₂, Hist.time]
  have e1 : h₁.toList = List.replicate (k + 1) (pr true true) ++ [pr false false] := by
    simp [h₁, Hist.toList, List.replicate_succ]
  have e2 : h₂.toList = List.replicate (k + 1) (pr true true) ++ [pr true true] := by
    simp only [h₂, Hist.toList]
    rw [← List.replicate_succ, List.replicate_succ']
  have htake : h₁.toList.take k = h₂.toList.take k := by
    rw [e1, e2, List.take_append_of_le_length (by simp), List.take_append_of_le_length (by simp)]
  have := hrec h₁ h₂ ht (by simp [h₁, Hist.time]; omega) htake
  rw [ex42_f0, ex42_f0] at this
  have hc₁ : ChangedXY (h₁.toList.map (· 1)) := by
    refine ⟨List.replicate k true, [], ?_⟩
    rw [e1, List.map_append, List.map_replicate, List.replicate_succ', List.append_assoc]
    rfl
  have hc₂ : ¬ ChangedXY (h₂.toList.map (· 1)) := by
    rintro ⟨l₁, l₂, he⟩
    have : false ∈ h₂.toList.map (· 1) := by rw [he]; simp
    simp [h₂, Hist.toList, pr] at this
  simp [hc₁, hc₂] at this

lemma changedXY_cons {l : List Bool} (h : ChangedXY l) (b : Bool) : ChangedXY (b :: l) := by
  obtain ⟨l₁, l₂, rfl⟩ := h
  exact ⟨b :: l₁, l₂, rfl⟩

theorem ex42_convergent : ex42.Convergent := by
  intro s₀ σ hσ hf
  set C : ℕ → Prop := fun m => ChangedXY ((ex42.run s₀ σ m).toList.map (· 1))
  have hCmono : ∀ m m', m ≤ m' → C m → C m' := by
    intro m m' hmm' hm
    induction m', hmm' using Nat.le_induction with
    | base => exact hm
    | succ m' _ ih =>
      simp only [C, run_succ, step_toList, List.map_cons]
      exact changedXY_cons ih _
  by_cases hA : ∃ m₀, C m₀
  · obtain ⟨m₀, hm₀⟩ := hA
    have h0 : ∀ᶠ m in atTop, (ex42.run s₀ σ m).cur 0 = true := by
      refine eventually_cur_eq_of (m₀ := m₀) (fun m hm _ => ?_) (hf 0)
      rw [ex42_f0]; simpa using hCmono _ _ hm hm₀
    obtain ⟨M, hM⟩ := eventually_atTop.mp h0
    have h1 : ∀ᶠ m in atTop, (ex42.run s₀ σ m).cur 1 = true :=
      eventually_cur_eq_of (m₀ := M) (fun m hm _ => by rw [ex42_f1]; exact hM m hm) (hf 1)
    refine ⟨pr true true, convergesTo_of_forall fun j => ?_⟩
    fin_cases j
    · simpa [pr] using h0
    · simpa [pr] using h1
  · push Not at hA
    have h0 : ∀ᶠ m in atTop, (ex42.run s₀ σ m).cur 0 = false := by
      refine eventually_cur_eq_of (m₀ := 0) (fun m _ _ => ?_) (hf 0)
      rw [ex42_f0]; simpa using hA m
    obtain ⟨M, hM⟩ := eventually_atTop.mp h0
    have h1 : ∀ᶠ m in atTop, (ex42.run s₀ σ m).cur 1 = false :=
      eventually_cur_eq_of (m₀ := M) (fun m hm _ => by rw [ex42_f1]; exact hM m hm) (hf 1)
    refine ⟨pr false false, convergesTo_of_forall fun j => ?_⟩
    fin_cases j
    · simpa [pr] using h0
    · simpa [pr] using h1

lemma ex42_stable_xx : ex42.IsStableState (pr false false) := by
  refine ⟨⟨pr false false, []⟩, _, isSchedule_univ, fair_univ, ?_⟩
  have inv : ∀ m, ∀ p ∈ (ex42.run ⟨pr false false, []⟩ (fun _ => Finset.univ) m).toList,
      p = pr false false := by
    intro m
    induction m with
    | zero => simp [Hist.toList]
    | succ m ih =>
      intro p hp
      rw [run_succ, step_toList, List.mem_cons] at hp
      rcases hp with rfl | hp
      · have hnc : ¬ ChangedXY
            ((ex42.run ⟨pr false false, []⟩ (fun _ => Finset.univ) m).toList.map (· 1)) := by
          rintro ⟨l₁, l₂, he⟩
          have : true ∈ (ex42.run ⟨pr false false, []⟩ (fun _ => Finset.univ) m).toList.map
              (· 1) := by rw [he]; simp
          obtain ⟨q, hq, hq1⟩ := List.mem_map.mp this
          rw [ih q hq] at hq1
          simp [pr] at hq1
        rw [pr_eq_iff]
        refine ⟨?_, ?_⟩
        · rw [step_cur_of_mem _ (Finset.mem_univ _), ex42_f0]; simpa using hnc
        · rw [step_cur_of_mem _ (Finset.mem_univ _), ex42_f1]
          have := ih _ (List.mem_cons_self ..)
          rw [this]; rfl
      · exact ih p hp
  exact Eventually.of_forall fun m => inv m _ (List.mem_cons_self ..)

lemma ex42_stable_yy : ex42.IsStableState (pr true true) := by
  refine ⟨⟨pr true true, [pr false false]⟩, _, isSchedule_univ, fair_univ, ?_⟩
  have inv : ∀ m, (ex42.run ⟨pr true true, [pr false false]⟩ (fun _ => Finset.univ) m).cur =
      pr true true ∧ ChangedXY
        ((ex42.run ⟨pr true true, [pr false false]⟩ (fun _ => Finset.univ) m).toList.map (· 1)) := by
    intro m
    induction m with
    | zero => exact ⟨rfl, [], [], by simp [Hist.toList, pr]⟩
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [pr_eq_iff]
        refine ⟨?_, ?_⟩
        · rw [run_succ, step_cur_of_mem _ (Finset.mem_univ _), ex42_f0]; simpa using ih.2
        · rw [run_succ, step_cur_of_mem _ (Finset.mem_univ _), ex42_f1, ih.1]; rfl
      · rw [run_succ, step_toList, List.map_cons]; exact changedXY_cons ih.2 _
  exact Eventually.of_forall fun m => (inv m).1

/-- **Example 4.2**: the bounded-recall hypothesis of Theorem 4.1 cannot be dropped. The system is
self-independent, its node `0` does not have bounded recall, it has the two stable states `(x,x)`
and `(y,y)`, and it is convergent. -/
theorem example_4_2 : ex42.SelfIndependent ∧ (∀ k, ¬ ex42.HasRecall 0 k) ∧
    ex42.IsStableState (pr false false) ∧ ex42.IsStableState (pr true true) ∧ ex42.Convergent :=
  ⟨ex42_selfIndependent, ex42_not_hasRecall, ex42_stable_xx, ex42_stable_yy, ex42_convergent⟩

/-! ### Example 4.3 -/

/-- Example 4.3: `fᵢ(x,x) = y`; in all other cases node `i` keeps its action. -/
def ex43 : System (fun _ : Fin 2 => Bool) where
  f i _ h := if h.cur = pr false false then true else h.cur i

lemma ex43_historyless (i : Fin 2) : ex43.Historyless i := by
  refine ⟨fun l => match l with
    | [] => false
    | a :: _ => if a = pr false false then true else a i, fun h _ => ?_⟩
  simp [ex43, Hist.toList]

lemma ex43_step_ne {h : Hist (fun _ : Fin 2 => Bool)} {T : Finset (Fin 2)} (hT : T.Nonempty) :
    (ex43.step h T).cur ≠ pr false false := by
  by_cases hh : h.cur = pr false false
  · obtain ⟨i, hi⟩ := hT
    intro he
    have := congrFun he i
    rw [step_cur_of_mem _ hi] at this
    simp only [ex43, hh, if_true] at this
    fin_cases i <;> simp [pr] at this
  · have : (ex43.step h T).cur = h.cur := by
      funext i
      by_cases hi : i ∈ T
      · rw [step_cur_of_mem _ hi]; simp [ex43, hh]
      · rw [step_cur_of_not_mem _ hi]
    rwa [this]

lemma ex43_step_eq {h : Hist (fun _ : Fin 2 => Bool)} (hh : h.cur ≠ pr false false)
    (T : Finset (Fin 2)) : (ex43.step h T).cur = h.cur := by
  funext i
  by_cases hi : i ∈ T
  · rw [step_cur_of_mem _ hi]; simp [ex43, hh]
  · rw [step_cur_of_not_mem _ hi]

/-- In Example 4.3 the dynamics is constant after the first step. -/
lemma ex43_run (s₀ : Hist (fun _ : Fin 2 => Bool)) {σ : ℕ → Finset (Fin 2)} (hσ : IsSchedule σ)
    (m : ℕ) : (ex43.run s₀ σ (m + 1)).cur = (ex43.run s₀ σ 1).cur := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [run_succ (m := m + 1), ex43_step_eq (by rw [ih]; exact ex43_step_ne (hσ _)), ih]

theorem ex43_convergent : ex43.Convergent := fun s₀ σ hσ _ =>
  ⟨_, eventually_atTop.mpr ⟨1, fun m hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact ex43_run s₀ hσ m⟩⟩

theorem ex43_isStableState_iff (a : P2) : ex43.IsStableState a ↔ a ≠ pr false false := by
  constructor
  · rintro ⟨s₀, σ, hσ, -, hc⟩ rfl
    obtain ⟨m, hm⟩ := (hc.and (eventually_ge_atTop 1)).exists
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact ex43_step_ne (hσ _) hm.1
  · intro ha
    refine ⟨⟨a, []⟩, _, isSchedule_univ, fair_univ, Eventually.of_forall fun m => ?_⟩
    induction m with
    | zero => rfl
    | succ m ih => rw [run_succ, ex43_step_eq (by rw [ih]; exact ha), ih]

/-- Node `0` of Example 4.3 is not self-independent (it must not be, by Theorem 4.1). -/
theorem ex43_not_selfIndependent : ¬ ex43.SelfIndependent := fun hsi =>
  theorem_4_1 (fun i => ⟨1, ex43_historyless i⟩) hsi
    ⟨pr true true, pr false true, by simp [pr_eq_iff, pr],
      (ex43_isStableState_iff _).mpr (by simp [pr_eq_iff, pr]),
      (ex43_isStableState_iff _).mpr (by simp [pr_eq_iff, pr])⟩ ex43_convergent

/-- **Example 4.3**: the self-independence hypothesis of Theorem 4.1 cannot be dropped. The system
is historyless (stationary `1`-recall), not self-independent, has three stable states (all
profiles but `(x,x)`), and it is convergent. -/
theorem example_4_3 : (∀ i, ex43.Historyless i) ∧ ¬ ex43.SelfIndependent ∧
    (∀ a, ex43.IsStableState a ↔ a ≠ pr false false) ∧ ex43.Convergent :=
  ⟨ex43_historyless, ex43_not_selfIndependent, ex43_isStableState_iff, ex43_convergent⟩

/-! ### The hypotheses of Theorem 4.1 are satisfiable -/

/-- Each node copies the other node's action (historyless, self-independent). -/
def copySys : System (fun _ : Fin 2 => Bool) where
  f i _ h := h.cur (1 - i)

lemma copySys_stable (b : Bool) : copySys.IsStableState (pr b b) := by
  refine ⟨⟨pr b b, []⟩, _, isSchedule_univ, fair_univ, Eventually.of_forall fun m => ?_⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [run_succ]
    funext i
    rw [step_cur_of_mem _ (Finset.mem_univ _)]
    show (copySys.run _ _ m).cur (1 - i) = pr b b i
    rw [ih]
    fin_cases i <;> rfl

/-- The copy system satisfies all hypotheses of Theorem 4.1, which shows that it is not
convergent. -/
theorem copySys_not_convergent : ¬ copySys.Convergent := by
  refine theorem_4_1 (fun i => ⟨1, fun l => match l with | [] => false | a :: _ => a (1 - i),
    fun h _ => by simp [copySys, Hist.toList]⟩) ?_
    ⟨_, _, by simp [pr_eq_iff, pr], copySys_stable false, copySys_stable true⟩
  intro i h h' he
  have := (List.forall₂_cons.mp he).1 (1 - i) (by fin_cases i <;> decide)
  simpa [copySys] using this

/-! ### Stable states must be limits of *fair* dynamics -/

/-- The literal reading of "stable state" in Section 3: a limit of the `(s⁰, σ)`-dynamics for an
arbitrary (possibly unfair) schedule `σ`. -/
def System.IsStableStateAny {ι : Type*} {A : ι → Type*} [DecidableEq ι] (F : System A)
    (a : Profile A) : Prop :=
  ∃ s₀ σ, IsSchedule σ ∧ F.ConvergesTo s₀ σ a

/-- Every node always plays `x`. -/
def constSys : System (fun _ : Fin 2 => Bool) where
  f _ _ _ := false

/-- With the literal reading of "stable state" (unfair schedules allowed), Theorem 4.1 would be
false: this historyless, self-independent system is convergent, but the dynamics that only ever
activates node `0` converges to `(x,y)`, a second "stable state" besides `(x,x)`. Hence stable
states have to be read as limits of fair dynamics (`IsStableState`), as the paper's
characterization "stable states = fixed points" in the historyless case presumes. -/
theorem stableState_literal_reading :
    (∀ i, constSys.Historyless i) ∧ constSys.SelfIndependent ∧ constSys.Convergent ∧
      constSys.IsStableStateAny (pr false false) ∧ constSys.IsStableStateAny (pr false true) := by
  refine ⟨fun i => ⟨fun _ => false, fun _ _ => rfl⟩, fun _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro s₀ σ _ hf
    refine ⟨pr false false, convergesTo_of_forall fun j => ?_⟩
    have := eventually_cur_eq_of (F := constSys) (s₀ := s₀) (σ := σ) (j := j) (v := false) (m₀ := 0)
      (fun _ _ _ => rfl) (hf j)
    fin_cases j <;> simpa [pr] using this
  · refine ⟨⟨pr false false, []⟩, _, isSchedule_univ, Eventually.of_forall fun m => ?_⟩
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [run_succ]; funext i
      rw [step_cur_of_mem _ (Finset.mem_univ _)]
      fin_cases i <;> rfl
  · refine ⟨⟨pr false true, []⟩, fun _ => {0}, fun _ => Finset.singleton_nonempty _,
      Eventually.of_forall fun m => ?_⟩
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [run_succ]; funext i
      by_cases hi : i = 0
      · subst hi; rw [step_cur_of_mem _ (Finset.mem_singleton_self _)]; rfl
      · rw [step_cur_of_not_mem _ (by simpa using hi), ih]

end Podc.RulesOfThumb
