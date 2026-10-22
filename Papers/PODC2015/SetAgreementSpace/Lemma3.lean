import Papers.PODC2015.SetAgreementSpace.Algorithm

/-!
# Lemma 3 of [DFKR15]: pairs with the same identifier carry the same value

For the algorithm of Figure 3 (`fig3`, both with and without the `fix` guard) we prove a basic
inductive invariant `BasicInv` of all configurations reached by **one-shot** executions, and derive

* `lemma3` (Lemma 3 of [DFKR15]): if `A[j₁] = (v₁, p)` and `A[j₂] = (v₂, p)` then `v₁ = v₂`;
* `lemma3_injOn`: on the pairs present in `A`, the identifier determines the pair (the form used
  for counting distinct pairs).

The restriction to one-shot executions is necessary: in CSLib's model a process that has
returned may be invoked again, and a new invocation restarts `Propose` with a new `pref` and
`i = 0`, while old pairs of the process are still in `A` (Section 4.1 of the paper is about the
one-shot algorithm).

The key strengthening of the paper's statement: every pair `(v, p)` in `A` has `v = pref_p`,
unless `p` has just adopted a new value (it is about to update its current component `i_p`), in
which case all pairs of `p` are at `i_p` (line 11 checked that no other component holds
`(pref, p)`).

`step_cases` describes the steps of `fig3` and is used by the other files of this folder.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

variable {V : Type} [DecidableEq V] [Inhabited V] {n m r : ℕ} [NeZero r] {fix : Bool}

/-- Configurations of the algorithm of Figure 3. -/
abbrev Cfg (V : Type) [Inhabited V] (n r : ℕ) := Config (saObj V) (Mem V n r) (Fin n) (Loc V r)

/-- Executions of the algorithm of Figure 3. -/
abbrev Exec (V : Type) [Inhabited V] (n : ℕ) := List (Label (Fin n) (saObj V))

/-- The steps of `fig3`: an invocation, an update (line 7), a scan with the local computation of
lines 9–14, a response of a decided process, or a (spurious) response of an idle process with a
pending operation (impossible in reachable configurations). -/
lemma step_cases {C C' : Cfg V n r} {ℓ : Label (Fin n) (saObj V)}
    (h : (fig3 (V := V) fix n m r).step C ℓ = some C') :
    (∃ p v, ℓ = .inv p v ∧ C.pend p = none ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc p ⟨.upd, v, 0, none⟩ ∧
      C'.pend = Function.update C.pend p (some v)) ∨
    (∃ p, ℓ = .tau p ∧ C.pend p ≠ none ∧ (C.loc p).pc = .upd ∧
      C'.mem () = Function.update (C.mem ()) (C.loc p).i (some ((C.loc p).pref, p)) ∧
      C'.loc = Function.update C.loc p { C.loc p with pc := .scan } ∧ C'.pend = C.pend) ∨
    (∃ p, ℓ = .tau p ∧ C.pend p ≠ none ∧ (C.loc p).pc = .scan ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc p (afterScan fix m p (C.loc p) (C.mem ())) ∧
      C'.pend = C.pend) ∨
    (∃ p, ℓ = .ret p ((C.loc p).out.getD default) ∧ C.pend p ≠ none ∧ (C.loc p).pc = .ret ∧
      C'.mem = C.mem ∧ C'.loc = Function.update C.loc p { C.loc p with pc := .idle } ∧
      C'.pend = Function.update C.pend p none) ∨
    (∃ p, ℓ = .ret p default ∧ C.pend p ≠ none ∧ (C.loc p).pc = .idle ∧ C'.mem = C.mem ∧
      C'.loc = C.loc ∧ C'.pend = Function.update C.pend p none) := by
  cases ℓ with
  | inv p v =>
    obtain ⟨h1, -, h2, h3, h4⟩ := Impl.step_inv h
    exact Or.inl ⟨p, v, rfl, h1, h4, h3, h2⟩
  | tau p =>
    obtain ⟨h1, h2, i, o, k, hact, h3, h4⟩ := Impl.step_tau h
    simp only [fig3] at hact
    cases hpc : (C.loc p).pc <;> simp only [hpc] at hact
    · cases hact
    · cases hact
      refine Or.inr (Or.inl ⟨p, rfl, h1, hpc, ?_, h4, h2⟩)
      rw [h3]; simp
    · cases hact
      exact Or.inr (Or.inr (Or.inl ⟨p, rfl, h1, hpc, by rw [h3]; simp, h4, h2⟩))
    · cases hact
  | ret p w =>
    obtain ⟨h1, h2, h3, l, hact, h4⟩ := Impl.step_ret h
    simp only [fig3] at hact
    cases hpc : (C.loc p).pc <;> simp only [hpc] at hact
    · cases hact
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨p, rfl, h1, hpc, h3, ?_, h2⟩)))
      rw [h4]; simp
    · cases hact
    · cases hact
    · cases hact
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl, h1, hpc, h3, h4, h2⟩)))

omit [Inhabited V] in
/-- The three outcomes of lines 9–14. -/
lemma afterScan_cases (l : Loc V r) (s : Fin r → Cell V n) (id : Fin n) :
    (DecideCond m s ∧ afterScan fix m id l s =
        { l with pc := .ret, out := some ((dupVal s).getD l.pref) }) ∨
    (¬ DecideCond m s ∧ AdoptCond fix s l.i l.pref id ∧
      afterScan fix m id l s = { l with pc := .upd, pref := (dupVal s).getD l.pref }) ∨
    (¬ DecideCond m s ∧ ¬ AdoptCond fix s l.i l.pref id ∧
      afterScan fix m id l s = { l with pc := .upd, i := l.i + 1 }) := by
  unfold afterScan
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, rfl⟩)

omit [Inhabited V] in
lemma afterScan_pc_ne_idle (l : Loc V r) (s : Fin r → Cell V n) (id : Fin n) :
    (afterScan fix m id l s).pc ≠ .idle := by
  rcases afterScan_cases (fix := fix) (m := m) l s id with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
    rw [h] <;> simp

/-- The basic invariant of one-shot executions of Figure 3 (including the invariant behind
Lemma 3, field `pairs`). -/
structure BasicInv (α : Exec V n) (C : Cfg V n r) : Prop where
  /-- A process has a pending operation iff it is not idle. -/
  pend_none : ∀ p, C.pend p = none ↔ (C.loc p).pc = .idle
  /-- A process that has not been invoked is in its initial state and has no pair in `A`. -/
  fresh : ∀ p, opsOf α p = [] →
    C.loc p = ⟨.idle, default, 0, none⟩ ∧ ∀ j v, C.mem () j ≠ some (v, p)
  /-- A process about to return has decided. -/
  ret_out : ∀ p, (C.loc p).pc = .ret → (C.loc p).out ≠ none
  /-- A process that has decided is about to return or has returned. -/
  out_pc : ∀ p, (C.loc p).out ≠ none → (C.loc p).pc = .ret ∨ (C.loc p).pc = .idle
  /-- A process that has returned `w` is idle and has decided `w`. -/
  outputs_eq : ∀ p w, outputs α p = some w → (C.loc p).out = some w ∧ (C.loc p).pc = .idle
  /-- Pairs of `p` carry `pref_p`, except right after an adoption, when all pairs of `p` are in
  its current component. -/
  pairs : ∀ p j v, C.mem () j = some (v, p) → v = (C.loc p).pref ∨
    ((C.loc p).pc = .upd ∧ j = (C.loc p).i ∧
      ∀ j' w, C.mem () j' = some (w, p) → j' = (C.loc p).i)

lemma BasicInv.init : BasicInv (r := r) ([] : Exec V n)
    (fig3 (V := V) fix n m r).initCfg := by
  constructor <;> simp [Impl.initCfg, fig3, outputs]

omit [DecidableEq V] in
lemma opsOf_nil_of_oneShot {α : Exec V n} {p : Fin n} {v : V}
    (h : OneShot (α ++ [.inv p v])) : opsOf α p = [] := by
  have := h p
  simp only [opsOf_concat, Label.invOf_inv, ↓reduceIte, Option.toList_some,
    List.length_append, List.length_singleton] at this
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- `BasicInv` is preserved by the steps of one-shot executions. -/
lemma BasicInv.step {α : Exec V n} {C C' : Cfg V n r} {ℓ : Label (Fin n) (saObj V)}
    (hI : BasicInv α C) (h1 : OneShot (α ++ [ℓ]))
    (h : (fig3 (V := V) fix n m r).step C ℓ = some C') : BasicInv (α ++ [ℓ]) C' := by
  rcases step_cases h with
    ⟨p, v, rfl, hp, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, -, -, -⟩
  · -- invocation
    have hops := opsOf_nil_of_oneShot h1
    obtain ⟨hl0, hno⟩ := hI.fresh p hops
    constructor
    · intro q; by_cases hq : q = p
      · subst hq; simp [hloc, hpend]
      · simp [hloc, hpend, hq, hI.pend_none q]
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; simp at hq
      · have hq' : opsOf α q = [] := by
          simpa [opsOf_concat, Ne.symm hqp] using hq
        rw [hloc, hmem]; simpa [hqp] using hI.fresh q hq'
    · intro q; by_cases hq : q = p
      · subst hq; simp [hloc]
      · simpa [hloc, hq] using hI.ret_out q
    · intro q; by_cases hq : q = p
      · subst hq; simp [hloc]
      · simpa [hloc, hq] using hI.out_pc q
    · intro q w hw
      rw [outputs_append_inv] at hw
      obtain ⟨h2, h3⟩ := hI.outputs_eq q w hw
      by_cases hq : q = p
      · subst hq; rw [hl0] at h2; simp at h2
      · simpa [hloc, hq] using And.intro h2 h3
    · intro q j w hj
      rw [hmem] at hj
      by_cases hq : q = p
      · subst hq; exact absurd hj (hno j w)
      · simpa [hloc, hmem, hq] using hI.pairs q j w hj
  · -- update (line 7)
    set l := C.loc p with hl
    have hops : opsOf α p ≠ [] := fun h0 => by
      have := (hI.fresh p h0).1; rw [← hl] at this; rw [this] at hpc; cases hpc
    constructor
    · intro q; by_cases hq : q = p
      · subst hq; simpa [hloc, hpend] using hp
      · simpa [hloc, hpend, hq] using hI.pend_none q
    · intro q hq
      rw [opsOf_concat] at hq; simp only [Label.invOf_tau, Option.toList_none,
        List.append_nil] at hq
      by_cases hqp : q = p
      · subst hqp; exact absurd hq hops
      · obtain ⟨h2, h3⟩ := hI.fresh q hq
        refine ⟨by simpa [hloc, hqp] using h2, fun j w => ?_⟩
        rw [hmem]
        by_cases hj : j = l.i
        · subst hj; simp [Ne.symm hqp]
        · simpa [hj] using h3 j w
    · intro q; by_cases hq : q = p
      · subst hq; simp [hloc]
      · simpa [hloc, hq] using hI.ret_out q
    · intro q; by_cases hq : q = p
      · subst hq; simp only [hloc, Function.update_self]
        intro hout; rcases hI.out_pc q hout with h2 | h2 <;> rw [h2] at hpc <;> cases hpc
      · simpa [hloc, hq] using hI.out_pc q
    · intro q w hw
      rw [outputs_append_tau] at hw
      obtain ⟨h2, h3⟩ := hI.outputs_eq q w hw
      by_cases hq : q = p
      · subst hq; rw [h3] at hpc; cases hpc
      · simpa [hloc, hq] using And.intro h2 h3
    · intro q j w hj
      rw [hmem] at hj
      by_cases hq : q = p
      · subst hq
        left
        simp only [hloc, Function.update_self]
        by_cases hj' : j = l.i
        · subst hj'; simp at hj; exact hj.symm
        · rw [Function.update_of_ne hj'] at hj
          rcases hI.pairs q j w hj with h2 | ⟨-, h2, -⟩
          · exact h2
          · exact absurd h2 hj'
      · have hji : j ≠ l.i := by
          rintro rfl; simp at hj; exact hq hj.2.symm
        rw [Function.update_of_ne hji] at hj
        simp only [hloc, Function.update_of_ne hq]
        rcases hI.pairs q j w hj with h2 | ⟨h2, h3, h4⟩
        · exact Or.inl h2
        · refine Or.inr ⟨h2, h3, fun j' w' hj' => ?_⟩
          rw [hmem] at hj'
          by_cases hj'' : j' = l.i
          · subst hj''; simp at hj'; exact absurd hj'.2.symm hq
          · rw [Function.update_of_ne hj''] at hj'; exact h4 j' w' hj'
  · -- scan (lines 8–14)
    set l := C.loc p with hl
    have hops : opsOf α p ≠ [] := fun h0 => by
      have := (hI.fresh p h0).1; rw [← hl] at this; rw [this] at hpc; cases hpc
    have hout : l.out = none := by
      by_contra hc; rcases hI.out_pc p hc with h2 | h2 <;> rw [h2] at hpc <;> cases hpc
    constructor
    · intro q; by_cases hq : q = p
      · subst hq; simpa [hloc, hpend, hp] using afterScan_pc_ne_idle _ _ _
      · simpa [hloc, hpend, hq] using hI.pend_none q
    · intro q hq
      rw [opsOf_concat] at hq; simp only [Label.invOf_tau, Option.toList_none,
        List.append_nil] at hq
      by_cases hqp : q = p
      · subst hqp; exact absurd hq hops
      · obtain ⟨h2, h3⟩ := hI.fresh q hq
        exact ⟨by simpa [hloc, hqp] using h2, by simpa [hmem] using h3⟩
    · intro q; by_cases hq : q = p
      · subst hq; simp only [hloc, Function.update_self]
        rcases afterScan_cases (fix := fix) (m := m) l (C.mem ()) q with
          ⟨-, h2⟩ | ⟨-, -, h2⟩ | ⟨-, -, h2⟩ <;> rw [h2] <;> simp
      · simpa [hloc, hq] using hI.ret_out q
    · intro q; by_cases hq : q = p
      · subst hq; simp only [hloc, Function.update_self]
        rcases afterScan_cases (fix := fix) (m := m) l (C.mem ()) q with
          ⟨-, h2⟩ | ⟨-, -, h2⟩ | ⟨-, -, h2⟩ <;> rw [h2] <;> simp [hout]
      · simpa [hloc, hq] using hI.out_pc q
    · intro q w hw
      rw [outputs_append_tau] at hw
      obtain ⟨h2, h3⟩ := hI.outputs_eq q w hw
      by_cases hq : q = p
      · subst hq; rw [h3] at hpc; cases hpc
      · simpa [hloc, hq] using And.intro h2 h3
    · intro q j w hj
      rw [hmem] at hj
      by_cases hq : q = p
      · subst hq
        have hw : w = l.pref := by
          rcases hI.pairs q j w hj with h2 | ⟨h2, -⟩
          · exact h2
          · rw [h2] at hpc; cases hpc
        simp only [hloc, Function.update_self]
        rcases afterScan_cases (fix := fix) (m := m) l (C.mem ()) q with
          ⟨-, h2⟩ | ⟨-, hA, h2⟩ | ⟨-, -, h2⟩ <;> rw [h2]
        · exact Or.inl hw
        · right
          have key : ∀ j' w', C.mem () j' = some (w', q) → j' = l.i := by
            intro j' w' hj'
            have hw' : w' = l.pref := by
              rcases hI.pairs q j' w' hj' with h2 | ⟨h2, -⟩
              · exact h2
              · rw [h2] at hpc; cases hpc
            by_contra hne
            exact (hA.1 j' hne).2 (by rw [hj', hw'])
          exact ⟨rfl, key j w hj, fun j' w' hj' => key j' w' (by simpa [hmem] using hj')⟩
        · exact Or.inl hw
      · simpa [hloc, hmem, hq] using hI.pairs q j w hj
  · -- response of a decided process
    set l := C.loc p with hl
    have hops : opsOf α p ≠ [] := fun h0 => by
      have := (hI.fresh p h0).1; rw [← hl] at this; rw [this] at hpc; cases hpc
    constructor
    · intro q; by_cases hq : q = p
      · subst hq; simp [hloc, hpend]
      · simpa [hloc, hpend, hq] using hI.pend_none q
    · intro q hq
      rw [opsOf_concat] at hq; simp only [Label.invOf_ret, Option.toList_none,
        List.append_nil] at hq
      by_cases hqp : q = p
      · subst hqp; exact absurd hq hops
      · obtain ⟨h2, h3⟩ := hI.fresh q hq
        exact ⟨by simpa [hloc, hqp] using h2, by simpa [hmem] using h3⟩
    · intro q; by_cases hq : q = p
      · subst hq; simp [hloc]
      · simpa [hloc, hq] using hI.ret_out q
    · intro q; by_cases hq : q = p
      · subst hq; simp [hloc]
      · simpa [hloc, hq] using hI.out_pc q
    · intro q w hw
      rw [outputs_concat] at hw
      by_cases hq : q = p
      · subst hq
        cases ho : Cslib.SharedMemory.outputs α q with
        | some w' =>
          obtain ⟨-, h3⟩ := hI.outputs_eq q w' ho; rw [h3] at hpc; cases hpc
        | none =>
          rw [ho] at hw
          simp only [Label.retOf_ret, ↓reduceIte, Option.none_or, Option.some.injEq] at hw
          obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 (hI.ret_out q hpc)
          simp only [hloc, Function.update_self]
          rw [← hw, ho']; simp
      · have : (Label.ret p (l.out.getD default) : Label (Fin n) (saObj V)).retOf q = none := by
          simp [Ne.symm hq]
        rw [this, Option.or_none] at hw
        simpa [hloc, hq] using hI.outputs_eq q w hw
    · intro q j w hj
      rw [hmem] at hj
      by_cases hq : q = p
      · subst hq
        left
        simp only [hloc, Function.update_self]
        rcases hI.pairs q j w hj with h2 | ⟨h2, -⟩
        · exact h2
        · rw [h2] at hpc; cases hpc
      · simpa [hloc, hmem, hq] using hI.pairs q j w hj
  · -- spurious response: impossible
    exact absurd ((hI.pend_none p).2 hpc) hp

/-- `BasicInv` holds in every configuration reached by a one-shot execution. -/
theorem basicInv_of_run {α : Exec V n} {C : Cfg V n r}
    (h : (fig3 (V := V) fix n m r).run α = some C) (hα : OneShot α) : BasicInv α C :=
  Impl.run_induction (Q := fun α C => OneShot α → BasicInv α C)
    (fun _ => BasicInv.init) (fun _ _ _ _ _ ih hs h1 => (ih h1.of_append).step h1 hs) h hα

/-- Lemma 3 from the basic invariant. -/
lemma BasicInv.same_val {α : Exec V n} {C : Cfg V n r} (hI : BasicInv α C) {j₁ j₂ : Fin r}
    {v₁ v₂ : V} {p : Fin n} (h₁ : C.mem () j₁ = some (v₁, p)) (h₂ : C.mem () j₂ = some (v₂, p)) :
    v₁ = v₂ := by
  rcases hI.pairs p j₁ v₁ h₁ with e₁ | ⟨-, -, k₁⟩
  · rcases hI.pairs p j₂ v₂ h₂ with e₂ | ⟨-, -, k₂⟩
    · rw [e₁, e₂]
    · have := (k₂ j₁ v₁ h₁).trans (k₂ j₂ v₂ h₂).symm
      subst this; rw [h₁] at h₂; simpa using h₂
  · have := (k₁ j₁ v₁ h₁).trans (k₁ j₂ v₂ h₂).symm
    subst this; rw [h₁] at h₂; simpa using h₂

/-- **Lemma 3 of [DFKR15].** In every configuration reached by a one-shot execution of Figure 3
(with or without the `fix` guard), all pairs in `A` with the same identifier have the same
value. -/
theorem lemma3 {α : Exec V n} {C : Cfg V n r}
    (h : (fig3 (V := V) fix n m r).run α = some C) (hα : OneShot α) {j₁ j₂ : Fin r}
    {v₁ v₂ : V} {p : Fin n} (h₁ : C.mem () j₁ = some (v₁, p)) (h₂ : C.mem () j₂ = some (v₂, p)) :
    v₁ = v₂ :=
  (basicInv_of_run h hα).same_val h₁ h₂

/-- Lemma 3, counting form: on the pairs present in `A`, the identifier determines the pair. -/
theorem lemma3_injOn {α : Exec V n} {C : Cfg V n r}
    (h : (fig3 (V := V) fix n m r).run α = some C) (hα : OneShot α) :
    Set.InjOn (fun x : V × Fin n => x.2) {x | ∃ j, C.mem () j = some x} := by
  rintro ⟨v₁, p₁⟩ ⟨j₁, h₁⟩ ⟨v₂, p₂⟩ ⟨j₂, h₂⟩ (hp : p₁ = p₂)
  subst hp
  rw [lemma3 h hα h₁ h₂]

end Podc.SetAgreementSpace
