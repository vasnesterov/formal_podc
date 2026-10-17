import Papers.PODC2025.UniqueIDsBoundedRegisters.AlgInv
import Cslib.Computability.Distributed.SharedMemory.History

/-!
# Algorithms 1 and 2: correctness for at most `n · m` calls (Theorem 3.1)

* `alg_correct`: if `n ≤ d` and `d ∣ m`, every execution of `alg n d m` with at most `n · m`
  invocations of `get()` returns distinct identifiers.
* `alg_resp_lt`: all identifiers are in `[0, n · m)`.

Proof: on top of the basic invariant `Inv1`, the value invariant `Inv2` says that every
identifier held (returned by a completed operation, or about to be returned by a process in
state `done v`) is `v = i · m + j` with `i < n` and `j < faiCnt d U i` (the number of FAIs on
`R_{i+1}` so far), and that distinct holders hold distinct identifiers. A new FAI on `R_{i+1}`
returns `faiCnt d U i`, which is `< m` as long as at most `n · m` calls were made
(`count_residue_le`), so the new identifier is fresh.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-! ### Responses after one more label -/

lemma respOf_append_ret (α : List (Label P uidObj)) (p : P) (r : ℕ) (x : OpId P) :
    respOf (α ++ [.ret p r]) x =
      if x.1 = p ∧ x.2 = (respsOf α p).length then some r else respOf α x := by
  obtain ⟨q, k⟩ := x
  simp only [respOf, respsOf_append, respsOf_cons, Label.retOf_ret, respsOf_nil,
    List.append_nil]
  by_cases hq : q = p
  · subst hq
    simp only [ite_true, Option.toList_some, true_and]
    rw [List.getElem?_append]
    split_ifs with h1 h2 h2
    · omega
    · rfl
    · subst h2; simp
    · rw [List.getElem?_singleton, ite_eq_right (by omega), List.getElem?_eq_none (by omega)]
  · simp [hq, Ne.symm hq]

lemma completed_iff_respOf (α : List (Label P uidObj)) (x : OpId P) :
    Completed α x ↔ ∃ v, respOf α x = some v := by
  simp only [Completed, respOf]
  constructor
  · intro h; exact ⟨_, List.getElem?_eq_getElem h⟩
  · rintro ⟨v, hv⟩
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hv
    cases hv

/-! ### Identifiers are in `[0, n · m)` -/

/-- Range invariant (no assumption on `d`). -/
structure RInv (n m : ℕ) [NeZero m] (α : List (Label P uidObj)) (C : ACfg P n m) : Prop where
  pend : ∀ p, C.pend p ≠ none → C.loc p ≠ .idle
  done : ∀ p v, C.loc p = .done v → v < n * m
  resp : ∀ x v, respOf α x = some v → v < n * m

lemma value_lt {n m : ℕ} (i : Fin n) (j : Fin m) : i.val * m + j.val < n * m := by
  have h1 : i.val + 1 ≤ n := i.isLt
  have h2 := Nat.mul_le_mul_right m h1
  have h3 := j.isLt
  rw [add_mul, one_mul] at h2
  omega

lemma rInv_of_run {n d m : ℕ} [NeZero m] {α : List (Label P uidObj)} {C : ACfg P n m}
    (h : (alg (P := P) n d m).run α = some C) : RInv n m α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil, Option.some.injEq] at h
    subst h
    exact ⟨by simp [Impl.initCfg], by simp [Impl.initCfg, alg], by simp [respOf]⟩
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := alg_run_append_singleton h
    have hR := ih h₀
    cases ℓ with
    | inv p o =>
      obtain ⟨-, hpend, hloc, -⟩ := alg_step_inv hs
      refine ⟨fun q hq => ?_, fun q v hq => ?_, fun x v hx => ?_⟩
      · rw [hloc, Function.update_apply]; rw [hpend, Function.update_apply] at hq
        split_ifs at hq ⊢ with h1
        · simp
        · exact hR.pend q hq
      · rw [hloc, Function.update_apply] at hq
        split_ifs at hq
        exact hR.done q v hq
      · rw [respOf_append_of_not_ret (by simp)] at hx; exact hR.resp x v hx
    | tau p =>
      have hresp : ∀ x (v : ℕ), respOf (α ++ [.tau p]) x = some v → v < n * m := by
        intro x v hx
        rw [respOf_append_of_not_ret (by simp)] at hx; exact hR.resp x v hx
      cases hlp : C₀.loc p with
      | idle => exact (alg_step_tau_idle hs hlp).elim
      | done v => exact (alg_step_tau_done hs hlp).elim
      | start =>
        obtain ⟨-, hpend, -, hloc⟩ := alg_step_tau_start hs hlp
        refine ⟨fun q hq => ?_, fun q v hq => ?_, hresp⟩
        · rw [hloc, Function.update_apply]; rw [hpend] at hq
          split_ifs <;> first | exact hR.pend q hq | simp
        · rw [hloc, Function.update_apply] at hq
          split_ifs at hq; exact hR.done q v hq
      | got i =>
        obtain ⟨-, hpend, -, hloc⟩ := alg_step_tau_got hs hlp
        refine ⟨fun q hq => ?_, fun q v hq => ?_, hresp⟩
        · rw [hloc, Function.update_apply]; rw [hpend] at hq
          split_ifs with h1
          · simp
          · exact hR.pend q hq
        · rw [hloc, Function.update_apply] at hq
          split_ifs at hq with h1
          · cases hq; exact value_lt i _
          · exact hR.done q v hq
    | ret p r =>
      obtain ⟨hpe, hpend, -, hlr, hloc⟩ := alg_step_ret hs
      have hlp : C₀.loc p = .done r := hlr.resolve_right (fun h => hR.pend p hpe h.1)
      refine ⟨fun q hq => ?_, fun q v hq => ?_, fun x v hx => ?_⟩
      · rw [hloc, Function.update_apply]; rw [hpend, Function.update_apply] at hq
        split_ifs at hq ⊢ with h1
        · simp at hq
        · exact hR.pend q hq
      · rw [hloc, Function.update_apply] at hq
        split_ifs at hq
        exact hR.done q v hq
      · rw [respOf_append_ret] at hx
        split_ifs at hx
        · cases hx; exact hR.done p r hlp
        · exact hR.resp x v hx

/-- All identifiers returned by Algorithm 2 (and 1) are in `[0, n · m)`. -/
theorem alg_resp_lt (n d m : ℕ) [NeZero m] (α : List (Label P uidObj))
    (hα : (alg (P := P) n d m).Valid α) (x : OpId P) (v : ℕ) (h : respOf α x = some v) :
    v < n * m := by
  obtain ⟨C, hC⟩ := hα
  exact (rInv_of_run hC).resp x v h

/-! ### Uniqueness -/

/-- Value invariant: held identifiers are distinct and of the form `i · m + j` with `i < n`,
`j < faiCnt d U i`. -/
structure Inv2 (n d m : ℕ) [NeZero m] (α : List (Label P uidObj)) (C : ACfg P n m)
    (g : Gh P) : Prop where
  uniq : ∀ x y v, respOf α x = some v → respOf α y = some v → x = y
  doneResp : ∀ p v x, C.loc p = .done v → respOf α x ≠ some v
  doneInj : ∀ p q v, C.loc p = .done v → C.loc q = .done v → p = q
  respBd : ∀ x v, respOf α x = some v → v / m < n ∧ v % m < faiCnt d g.U (v / m)
  doneBd : ∀ p v, C.loc p = .done v → v / m < n ∧ v % m < faiCnt d g.U (v / m)

section Inv2Step

variable {n d m : ℕ} [NeZero m] {α : List (Label P uidObj)} {C C' : ACfg P n m} {g : Gh P}

lemma Inv2.step (hnd : n ≤ d) (hI : Inv1 n d m α C g) (hJ : Inv2 n d m α C g)
    {ℓ : Label P uidObj} (hs : (alg (P := P) n d m).step C ℓ = some C')
    (hN : invCount (α ++ [ℓ]) ≤ n * m) :
    Inv2 n d m (α ++ [ℓ]) C' (gstep n d g C ℓ) := by
  have hN' : invCount α ≤ n * m := by simp at hN; omega
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, hloc, -⟩ := alg_step_inv hs
    have hl : ∀ q v, C'.loc q = .done v → C.loc q = .done v := by
      intro q v h; rw [hloc, Function.update_apply] at h; split_ifs at h; exact h
    have hr : ∀ x, respOf (α ++ [.inv p o]) x = respOf α x :=
      respOf_append_of_not_ret (by simp)
    simp only [gstep]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y v; rw [hr, hr]; exact hJ.uniq x y v
    · intro q v x h; rw [hr]; exact hJ.doneResp q v x (hl q v h)
    · intro q q' v h h'; exact hJ.doneInj q q' v (hl q v h) (hl q' v h')
    · intro x v; rw [hr]; exact hJ.respBd x v
    · intro q v h; exact hJ.doneBd q v (hl q v h)
  | ret p r =>
    obtain ⟨hpe, -, -, hlr, hloc⟩ := alg_step_ret hs
    have hlp : C.loc p = .done r := hlr.resolve_right (fun h => hpe ((hI.pendIdle p).2 h.1))
    have hl : ∀ q v, C'.loc q = .done v → q ≠ p ∧ C.loc q = .done v := by
      intro q v h; rw [hloc, Function.update_apply] at h; split_ifs at h with hq; exact ⟨hq, h⟩
    simp only [gstep]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y v hx hy
      rw [respOf_append_ret] at hx hy
      split_ifs at hx hy with h1 h2 h2
      · exact Prod.ext (h1.1.trans h2.1.symm) (h1.2.trans h2.2.symm)
      · cases hx; exact absurd hy (hJ.doneResp p r y hlp)
      · cases hy; exact absurd hx (hJ.doneResp p r x hlp)
      · exact hJ.uniq x y v hx hy
    · intro q v x h hx
      obtain ⟨hq, h⟩ := hl q v h
      rw [respOf_append_ret] at hx
      split_ifs at hx
      · cases hx; exact hq (hJ.doneInj q p r h hlp)
      · exact hJ.doneResp q v x h hx
    · intro q q' v h h'; exact hJ.doneInj q q' v (hl q v h).2 (hl q' v h').2
    · intro x v hx
      rw [respOf_append_ret] at hx
      split_ifs at hx
      · cases hx; exact hJ.doneBd p r hlp
      · exact hJ.respBd x v hx
    · intro q v h; exact hJ.doneBd q v (hl q v h).2
  | tau p =>
    have hr : ∀ x, respOf (α ++ [.tau p]) x = respOf α x :=
      respOf_append_of_not_ret (by simp)
    cases hlp : C.loc p with
    | idle => exact (alg_step_tau_idle hs hlp).elim
    | done v => exact (alg_step_tau_done hs hlp).elim
    | start =>
      obtain ⟨-, -, -, hloc⟩ := alg_step_tau_start hs hlp
      have hl : ∀ q v, C'.loc q = .done v → C.loc q = .done v := by
        intro q v h; rw [hloc, Function.update_apply] at h
        split_ifs at h; exact h
      simp only [gstep, hlp]
      split_ifs <;>
      exact ⟨fun x y v => by rw [hr, hr]; exact hJ.uniq x y v,
        fun q v x h => by rw [hr]; exact hJ.doneResp q v x (hl q v h),
        fun q q' v h h' => hJ.doneInj q q' v (hl q v h) (hl q' v h'),
        fun x v => by rw [hr]; exact hJ.respBd x v,
        fun q v h => hJ.doneBd q v (hl q v h)⟩
    | got i =>
      obtain ⟨-, -, -, hloc⟩ := alg_step_tau_got hs hlp
      obtain ⟨htk, htkd, htkU⟩ := hI.got p i hlp
      set c := faiCnt d g.U i with hc
      -- the new FAI on `R_{i+1}` returns `c < m`
      have hcm : c < m := by
        have h1 : faiCnt d (insert (g.tk p) g.U) i ≤ Nat.count (fun s => s % d = i) g.t := by
          rw [Nat.count_eq_card_filter_range]
          apply Finset.card_le_card
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range] at hs ⊢
          rcases hs with ⟨rfl | hs, hd⟩
          · exact ⟨htk, hd⟩
          · exact ⟨hI.Usub s hs, hd⟩
        rw [faiCnt_insert htkU, ite_eq_left htkd] at h1
        have h2 := count_residue_le hnd i.isLt (hI.count_le.trans hN')
        omega
      have hval : (C.mem i.succ).val = c := by rw [hI.mi, Nat.mod_eq_of_lt hcm]
      set v₀ := i.val * m + c with hv₀
      have hv₀d : v₀ / m = i.val := by
        rw [hv₀, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero (NeZero.ne m)),
          Nat.div_eq_of_lt hcm, zero_add]
      have hv₀m : v₀ % m = c := by
        rw [hv₀, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcm]
      have hl : ∀ q v, C'.loc q = .done v → (q = p ∧ v = v₀) ∨ (q ≠ p ∧ C.loc q = .done v) := by
        intro q v h; rw [hloc, Function.update_apply, hval] at h
        split_ifs at h with hq
        · cases h; exact Or.inl ⟨hq, rfl⟩
        · exact Or.inr ⟨hq, h⟩
      -- counts only grow
      have hmono : ∀ j, faiCnt d g.U j ≤ faiCnt d (insert (g.tk p) g.U) j := by
        intro j; rw [faiCnt_insert htkU]; omega
      have hnew : faiCnt d (insert (g.tk p) g.U) i = c + 1 := by
        rw [faiCnt_insert htkU, ite_eq_left htkd]
      -- old holders do not hold `v₀`
      have hold : ∀ v, v / m < n ∧ v % m < faiCnt d g.U (v / m) → v ≠ v₀ := by
        rintro v ⟨-, h2⟩ rfl
        rw [hv₀d, hv₀m] at h2; exact lt_irrefl _ h2
      simp only [gstep, hlp]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x y v; rw [hr, hr]; exact hJ.uniq x y v
      · intro q v x h; rw [hr]
        rcases hl q v h with ⟨-, rfl⟩ | ⟨-, h⟩
        · intro hx; exact hold _ (hJ.respBd x _ hx) rfl
        · exact hJ.doneResp q v x h
      · intro q q' v h h'
        rcases hl q v h with ⟨hq, hv⟩ | ⟨hq, h⟩ <;>
          rcases hl q' v h' with ⟨hq', hv'⟩ | ⟨hq', h'⟩
        · rw [hq, hq']
        · exact absurd hv (hold _ (hJ.doneBd q' _ h'))
        · exact absurd hv' (hold _ (hJ.doneBd q _ h))
        · exact hJ.doneInj q q' v h h'
      · intro x v hx; rw [hr] at hx
        obtain ⟨h1, h2⟩ := hJ.respBd x v hx
        exact ⟨h1, h2.trans_le (hmono _)⟩
      · intro q v h
        rcases hl q v h with ⟨-, rfl⟩ | ⟨-, h⟩
        · rw [hv₀d, hv₀m, hnew]; exact ⟨i.isLt, Nat.lt_succ_self _⟩
        · obtain ⟨h1, h2⟩ := hJ.doneBd q v h
          exact ⟨h1, h2.trans_le (hmono _)⟩

end Inv2Step

theorem inv2_of_run {n d m : ℕ} [NeZero m] (hnd : n ≤ d) (hdm : d ∣ m)
    {α : List (Label P uidObj)} {C : ACfg P n m} (h : (alg (P := P) n d m).run α = some C)
    (hN : invCount α ≤ n * m) : Inv2 n d m α C (ghostOf n d m α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil, Option.some.injEq] at h
    subst h
    exact ⟨by simp [respOf], by simp [respOf], by simp [Impl.initCfg, alg],
      by simp [respOf], by simp [Impl.initCfg, alg]⟩
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := alg_run_append_singleton h
    rw [ghostOf_append h₀ hs]
    have hN' : invCount α ≤ n * m := by simp at hN; omega
    exact (ih h₀ hN').step hnd (inv1_of_run hdm h₀) hs hN

/-- **Theorem 3.1** (Algorithms 1 and 2): if `n ≤ d` and `d ∣ m`, the algorithm with `n + 1`
registers of `m` values returns distinct identifiers in every execution with at most `n · m`
calls of `get()`. -/
theorem alg_correct (n d m : ℕ) [NeZero m] (hnd : n ≤ d) (hdm : d ∣ m) :
    CorrectUpTo (alg (P := P) n d m) (n * m) := by
  intro α hα hN x y hx hy hxy he
  obtain ⟨C, hC⟩ := hα
  obtain ⟨v, hv⟩ := (completed_iff_respOf α x).1 hx
  exact hxy ((inv2_of_run hnd hdm hC hN).uniq x y v hv (he ▸ hv))

end Cslib.SharedMemory.UniqueIDs
