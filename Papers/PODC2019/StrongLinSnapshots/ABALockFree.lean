import Papers.PODC2019.StrongLinSnapshots.ABASim

/-!
# Algorithm 2: lock-freedom, and Theorem 1

Section 3.3 of the paper: a `DRead` can only be forced to repeat its loop by a `DWrite` that
writes `X` (Lemma 13), and a `DWrite` returns right after writing `X`. We prove lock-freedom by
a potential that strictly decreases at every step that is not a response:

* a pending `DRead` of `q` has weight `≤ 11`, the number of steps it still needs if `X` does not
  change (a function of its program counter, `X` and `A[q]`, which only `q` writes);
* a process that may still write `X` before its next response (idle, or in a `DWrite` before
  line 2) carries an extra weight `K = 11 n`, which pays for the increase of all `DRead`
  weights when it writes `X`.

`theorem1` collects strong linearizability, lock-freedom and the space bounds: `n + 1`
registers, each over `V × Option (Fin n × Fin (2n+2))`.
-/

namespace Podc.StrongLinSnapshots

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

set_option linter.unusedSectionVars false

variable {n : ℕ} {V : Type} [DecidableEq V] {v₀ : V} {pick : List (Seq n) → Seq n}

/-- Steps of a `DRead` iteration started at line 34, if `X` does not change. -/
def d34 (A : Tag n) (X : Val n V) : ℕ := if A = X.2 then 4 else 8

/-- Remaining steps of a `DRead` about to execute line 37. -/
def μ37 (v : Val n V) (a A : Tag n) (X : Val n V) : ℕ :=
  if a = v.2 ∧ v = X then 1 else 1 + d34 A X

/-- The weight of a process with program counter `pc`, given `X` and its announcement `A`. -/
def wt (K : ℕ) (X : Val n V) (A : Tag n) : PC n V → ℕ
  | .idle => K + 20
  | .wA _ => K + 2
  | .wX _ _ => K + 1
  | .wRet _ => 0
  | .rRet _ _ => 0
  | .r34 _ => d34 A X
  | .r35 _ v => 2 + μ37 v A v.2 X
  | .r36 _ v a => 1 + μ37 v a v.2 X
  | .r37 _ v a => μ37 v a A X

/-- The potential. -/
def pot (C : Cfg n V v₀) : ℕ :=
  ∑ q, wt (11 * n) (C.mem none) (C.mem (some q)).2 (C.loc q).pc

lemma d34_le (A : Tag n) (X : Val n V) : d34 A X ≤ 8 := by unfold d34; split_ifs <;> omega

lemma μ37_le (v : Val n V) (a A : Tag n) (X : Val n V) : μ37 v a A X ≤ 9 := by
  have := d34_le A X; unfold μ37; split_ifs <;> omega

/-- Every step that is not a response strictly decreases the potential. -/
lemma pot_lt (hpick : PickSpec pick) {α : Exec n V v₀} {C C' : Cfg n V v₀}
    {ℓ : Label (Fin n) (abaObj (Fin n) V v₀)} (hrun : (impl v₀ pick).run α = some C)
    (h : (impl v₀ pick).step C ℓ = some C') (hℓ : ∀ p r, ℓ ≠ .ret p r) : pot C' < pot C := by
  have hI := (impl v₀ pick).simLin_spec Inv (linSim hpick) α C hrun
  cases ℓ with
  | ret p r => exact absurd rfl (hℓ p r)
  | inv p o =>
    obtain ⟨h0, -, -, hloc, hmem⟩ := Impl.step_inv h
    have hidle : (C.loc p).pc = .idle := by
      have := hI.st p
      unfold St at this
      split at this <;> simp_all
    unfold pot
    rw [hmem]
    apply Fintype.sum_lt_sum_of_eq_off p
    · intro q hq; rw [hloc, Function.update_of_ne hq]
    · rw [hloc, Function.update_self, hidle]
      have := d34_le (C.mem (some p)).2 (C.mem none)
      cases o <;> simp only [impl, implG, wt] <;> omega
  | tau p =>
    have h0 := (Impl.step_tau h).1
    -- local steps: only `p`'s local state and possibly `A[p]` change
    have hloc_step : ∀ (m : (i : Obj n) → (B n V v₀ i).State) (pc' : PC n V)
        (hm : ∀ i, i ≠ some p → m i = C.mem i)
        (hlt : wt (11 * n) (C.mem none) (m (some p)).2 pc' <
          wt (11 * n) (C.mem none) (C.mem (some p)).2 (C.loc p).pc),
        pot (⟨Function.update C.loc p ⟨pc', (C.loc p).gs⟩, C.pend, m⟩ : Cfg n V v₀) < pot C := by
      intro m pc' hm hlt
      unfold pot
      simp only
      rw [hm none (by simp)]
      apply Fintype.sum_lt_sum_of_eq_off p
      · intro q hq; rw [Function.update_of_ne hq, hm (some q) (by simpa using hq)]
      · rw [Function.update_self]; exact hlt
    cases hpc : (C.loc p).pc with
    | idle | wRet _ | rRet _ _ =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      simp [impl, implG, actG, hpc] at hact
    | wA x =>
      have hact : (impl v₀ pick).act p (C.loc p) = .access (some (C.loc p).gs.c) .read
          (fun r => (⟨.wX x (getSeq pick p (C.loc p).gs r.2).1,
            (getSeq pick p (C.loc p).gs r.2).2⟩ : Loc n V)) := by
        simp [impl, implG, actG, hpc]
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      unfold pot
      simp only [Function.update_eq_self]
      apply Fintype.sum_lt_sum_of_eq_off p
      · intro q hq; rw [Function.update_of_ne hq]
      · rw [Function.update_self, hpc]; simp only [wt]; omega
    | wX x s =>
      have hact : (impl v₀ pick).act p (C.loc p) = .access none (.write (x, some (p, s)))
          (fun _ => (⟨.wRet x, (C.loc p).gs⟩ : Loc n V)) := by
        simp [impl, implG, actG, hpc]
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      unfold pot
      simp only
      apply Fintype.sum_lt_sum_of_le_add (c := 11) p
      · intro q hq
        rw [Function.update_of_ne hq]
        rw [Function.update_of_ne (show (some q : Obj n) ≠ none by simp)]
        -- processes that may write `X` are unaffected; the others weigh at most `11`
        cases (C.loc q).pc with
        | r34 _ =>
          have := d34_le (C.mem (some q)).2 (x, some (p, s)); simp only [wt, Function.update_self]; omega
        | r35 _ v =>
          have := μ37_le v (C.mem (some q)).2 v.2 (x, some (p, s)); simp only [wt, Function.update_self]; omega
        | r36 _ v a =>
          have := μ37_le v a v.2 (x, some (p, s)); simp only [wt, Function.update_self]; omega
        | r37 _ v a =>
          have := μ37_le v a (C.mem (some q)).2 (x, some (p, s)); simp only [wt, Function.update_self]; omega
        | _ => simp only [wt]; omega
      · simp only [Function.update_self, hpc, wt, Fintype.card_fin, smul_eq_mul]
        have : (n - 1) * 11 < 11 * n + 1 := by
          rcases n with _ | n
          · omega
          · rw [Nat.add_sub_cancel]; omega
        omega
    | r34 ch =>
      have hact : (impl v₀ pick).act p (C.loc p) = .access none .read
          (fun v => (⟨.r35 ch v, (C.loc p).gs⟩ : Loc n V)) := by
        simp [impl, implG, actG, hpc]
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      refine hloc_step _ _ (fun i _ => by
        by_cases hi : i = none
        · subst hi; simp
        · rw [Function.update_of_ne hi]) ?_
      rw [hpc, Function.update_of_ne (show (some p : Obj n) ≠ none by simp)]
      simp only [wt, μ37, d34, and_true]
      split_ifs <;> omega
    | r35 ch v =>
      have hact : (impl v₀ pick).act p (C.loc p) = .access (some p) .read
          (fun a => (⟨.r36 ch v a.2, (C.loc p).gs⟩ : Loc n V)) := by
        simp [impl, implG, actG, hpc]
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      refine hloc_step _ _ (fun i _ => by
        by_cases hi : i = some p
        · subst hi; simp
        · rw [Function.update_of_ne hi]) ?_
      rw [hpc]
      simp only [wt]
      omega
    | r36 ch v a =>
      have hact : (impl v₀ pick).act p (C.loc p) = .access (some p) (.write (v₀, v.2))
          (fun _ => (⟨.r37 ch v a, (C.loc p).gs⟩ : Loc n V)) := by
        simp [impl, implG, actG, hpc]
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      refine hloc_step _ _ (fun i hi => Function.update_of_ne hi _ _) ?_
      rw [hpc, Function.update_self]
      simp only [wt]
      show μ37 v a v.2 (C.mem none) < 1 + μ37 v a v.2 (C.mem none)
      omega
    | r37 ch v a =>
      have hact : (impl v₀ pick).act p (C.loc p) = .access none .read
          (fun v' => if a = v.2 ∧ v = v' then (⟨.rRet v'.1 ch, (C.loc p).gs⟩ : Loc n V)
            else ⟨.r34 true, (C.loc p).gs⟩) := by
        simp [impl, implG, actG, hpc]
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      simp only [Function.update_eq_self]
      by_cases hg : a = v.2 ∧ v = C.mem none
      · simp only [hg, and_self, ↓reduceIte]
        refine hloc_step _ _ (fun _ _ => rfl) ?_
        rw [hpc]; simp only [wt, μ37]; split_ifs; omega
      · simp only [hg, ↓reduceIte]
        refine hloc_step _ _ (fun _ _ => rfl) ?_
        rw [hpc]; simp only [wt, μ37, hg, ↓reduceIte]; omega

/-- **Lock-freedom** of Algorithm 2 (Theorem 14: in every infinite execution, infinitely many
operations return). -/
theorem lockFree (hpick : PickSpec pick) : (impl v₀ pick).LockFree :=
  (impl v₀ pick).lockFree_of_potential pot fun _ _ _ _ hrun h hℓ => pot_lt hpick hrun h hℓ

/-- **Theorem 1** (Ovens–Woelfel): there is a lock-free strongly linearizable implementation of
an ABA-detecting register from `n + 1` registers whose values range over
`V × Option (Fin n × Fin (2n+2))` (`|V| · (n(2n+2) + 1)` values, i.e. `O(log n + log |V|)` bits).
The implementation is Algorithm 2 with any admissible choice of fresh sequence numbers
(e.g. `pickMin`). -/
theorem theorem1 [Fintype V] (n : ℕ) (v₀ : V) :
    ∃ pick : List (Seq n) → Seq n,
      (impl v₀ pick).StronglyLinearizable ∧ (impl v₀ pick).LockFree ∧
      Fintype.card (Obj n) = n + 1 ∧
      (∀ i : Obj n, (B n V v₀ i).State = (V × Option (Fin n × Fin (2 * n + 2)))) ∧
      Fintype.card (V × Option (Fin n × Fin (2 * n + 2))) =
        Fintype.card V * (n * (2 * n + 2) + 1) :=
  ⟨pickMin, stronglyLinearizable pickMin_spec, lockFree pickMin_spec, by simp,
    fun _ => rfl, by simp [Fintype.card_prod, Fintype.card_option]⟩

end Podc.StrongLinSnapshots
