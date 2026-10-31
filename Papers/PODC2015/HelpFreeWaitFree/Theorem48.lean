import Papers.PODC2015.HelpFreeWaitFree.GVLoop

/-!
# Theorem 4.8: (strong) global view types have no wait-free help-free implementation

The base objects are registers supporting `read`, `write` and `cas` (CSLib `casObject`).

* `Ctx.iteration` — one iteration of the main loop of Figure 4.2.
* `theorem_4_8` — **Theorem 4.8** for strong global view types (`StrongGlobalView`), for the weak
  (owner-only) notion of help-freedom: with three distinct processes, no wait-free implementation
  from read/write/cas registers has a weakly help-free linearization function.
* `theorem_4_8_helpFree` — the paper's form: such an implementation is not help-free.

## Relation to the paper's proof

The paper states Theorem 4.8 for all global view types (`GlobalView`: the results of a view tell
how many of `op₁` and the next modifier `op₂` precede it). Its proof does not establish this:

* **Claim 4.6.8 (gap, not repaired for `GlobalView`).** From "`op₁` is decided before `op₃` in
  `h∘p₁∘p₃` but not in `h∘p₃∘p₁`" the paper infers that `p₃` running solo returns different
  results for `op₃` ("because each operation by `p₁` changes the return value of `op₃`"). With
  only three result classes this does not follow: in both histories the result may lie in `RS1`
  — `op₁ ≺ op₃ ≺ op₂` in the first, `op₂ ≺ op₃ ≺ op₁` in some extension of the second. The same
  inference is used to exclude reads and failed `cas`, and the elimination of writes asserts
  without justification that `op₂` is not before `op₃` in the `p₁`-first run. We therefore assume
  `StrongGlobalView` (a view also tells *which* of `op₁`, `op₂` precedes it — the distinction the
  paper says it avoids using). Then whether `op₁` (or `op₂`) is decided before a view depends only
  on the memory and on `p₃` (`Ctx.kl`), and Claim 4.6.8 follows (`Ctx.caseA`; reads and failed
  `cas` are excluded by comparing `h∘p₁` with `h`, writes by help-freedom).
* **Claim 4.6.12 (gap, repaired by changing the construction).** "`op_k` is not decided before
  `op_j` (because `op_j` may still be before `op₃`, which in turn may still be before `op_k`)" is
  unjustified: two different extensions do not give one with `op_j ≺ op₃ ≺ op_k`. When the step
  of `p_k` at line 25 would decide `op_k` before the next view, we show that the next steps of
  `p₁` and `p₂` are competing successful `cas` on one location (`Ctx.race`, `Ctx.bbad`) and
  perform the move of lines 17–20 instead (`Ctx.cas_move`); otherwise line 25 is harmless
  (`Ctx.good_move`). The final argument (Claim 4.6.15) is unchanged.

Fetch&increment is a global view type (`fetchInc_globalView`) but not a strong one
(`fetchInc_not_strongGlobalView`); the same holds for increment objects (views only count). For
them Theorem 4.8 is not established here. The snapshot is a strong global view type
(`snapshot_strongGlobalView`, `theorem_4_7`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {P L : Type} [DecidableEq P]

section CAS

variable {V : ι → Type} [∀ i, DecidableEq (V i)] {v₀ : ∀ i, V i}

namespace Ctx

variable {I : Impl A (fun i => casObject (V i) (v₀ i)) P L} (X : Ctx I)

/-- **One iteration of the main loop of Figure 4.2** (Claims 4.6.1–4.6.14): from the invariant at
line 5 for `op₂ = (p₂, i)` and `op₃ = (p₃, j)`, the construction reaches the invariant for the next
view `(p₃, j+1)` and either the same modifier, or the next one — and then `p₁` took a
base-object step. In both cases `p₁` or `p₂` took a step. -/
theorem iteration (hsep : X.GVSep) {i j : ℕ} {h : List (Label P A)} (hi : X.GInv i j h) :
    ∃ i' y, X.GInv i' (j + 1) y ∧ h <+: y ∧ X.steps12 h < X.steps12 y ∧
      (i' = i ∨ (i' = i + 1 ∧ h.countP (Label.isTauOf X.p₁) < y.countP (Label.isTauOf X.p₁))) := by
  obtain ⟨h₁, hi₁, he₁, hp₁⟩ := X.first_loop hi
  have hu := X.u_next hi₁
  have hJ : X.GJ2 i j h₁ := ⟨hi₁.str, hi₁.resp1, hi₁.resp2, hi₁.resp3, hu.1, hu.2, he₁⟩
  obtain ⟨h₂, hJ₂, hnc, hp₂⟩ := X.second_loop hsep hJ
  obtain ⟨i', y, hy, hpy, hst, hpr⟩ := X.exit_cases hsep hJ₂ hnc
  have hp := hp₁.trans hp₂
  refine ⟨i', y, hy, hp.trans hpy, lt_of_le_of_lt (X.steps12_mono hp) hst, ?_⟩
  rcases hpr with hpr | ⟨hpr, hlt⟩
  · exact Or.inl hpr
  · exact Or.inr ⟨hpr, lt_of_le_of_lt (List.IsPrefix.countP_le hp) hlt⟩

/-- The invariant holds initially. -/
lemma ginv_zero : X.GInv 0 0 [] := by
  have hv : I.Valid ([] : List (Label P A)) := ⟨I.initCfg, rfl⟩
  refine ⟨⟨hv, Or.inl rfl, Or.inl rfl, Or.inl rfl, le_refl _, fun _ _ _ _ => rfl,
    fun k hk => absurd hk (Nat.not_lt_zero _)⟩, rfl, rfl, ?_, ?_⟩
  · have hcur : curOp ([] : List (Label P A)) X.p₃ = (X.p₃, 0) := rfl
    rw [← hcur]; exact X.not_decidedBefore_cur hv (by simp [Invoked]) X.h13
  · have hcur : curOp ([] : List (Label P A)) X.p₃ = (X.p₃, 0) := rfl
    rw [← hcur]; exact X.not_decidedBefore_cur hv (by simp [Invoked]) X.h23

/-- **Claims 4.6.14–4.6.15**: the construction runs forever, and either `p₁` takes infinitely many
steps without completing `op₁`, or from some point on `p₂` takes infinitely many steps without
completing an operation. Both contradict wait-freedom. -/
theorem false_of_gvSep (hsep : X.GVSep) : False := by
  classical
  let G := {g : ℕ × ℕ × List (Label P A) //
    X.GInv g.1 g.2.1 g.2.2 ∧ g.1 ≤ g.2.2.countP (Label.isTauOf X.p₁)}
  have hiter : ∀ g : G, ∃ g' : G, g.1.2.2 <+: g'.1.2.2 ∧ X.steps12 g.1.2.2 < X.steps12 g'.1.2.2 ∧
      g.1.1 ≤ g'.1.1 := by
    intro g
    obtain ⟨i', y, hy, hpre, hst, hpr⟩ := X.iteration hsep g.2.1
    have hle := List.IsPrefix.countP_le (p := Label.isTauOf X.p₁) hpre
    have hb := g.2.2
    rcases hpr with rfl | ⟨rfl, hlt⟩
    · exact ⟨⟨(_, _, y), hy, hb.trans hle⟩, hpre, hst, le_rfl⟩
    · exact ⟨⟨(_, _, y), hy, Nat.succ_le_of_lt (lt_of_le_of_lt hb hlt)⟩, hpre, hst, by simp⟩
  choose nxt hpre hst hmi using hiter
  let g₀ : G := ⟨(0, 0, []), X.ginv_zero, le_refl _⟩
  let E : ℕ → List (Label P A) := fun k => (nxt^[k] g₀).1.2.2
  let Ix : ℕ → ℕ := fun k => (nxt^[k] g₀).1.1
  have hsucc : ∀ k, nxt^[k + 1] g₀ = nxt (nxt^[k] g₀) := fun k => Function.iterate_succ_apply' _ _ _
  have hinv : ∀ k, X.GInv (Ix k) _ (E k) := fun k => (nxt^[k] g₀).2.1
  have hbnd : ∀ k, Ix k ≤ (E k).countP (Label.isTauOf X.p₁) := fun k => (nxt^[k] g₀).2.2
  have hmono : ∀ k, E k <+: E (k + 1) := fun k => by
    simp only [E, hsucc]; exact hpre _
  have hmono' : ∀ k m, k ≤ m → E k <+: E m := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ m _ ih => exact ih.trans (hmono m)
  have hImono : ∀ k, Ix k ≤ Ix (k + 1) := fun k => by
    simp only [Ix, hsucc]; exact hmi _
  have hImono' : ∀ k m, k ≤ m → Ix k ≤ Ix m := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact ih.trans (hImono m)
  have hsteps : ∀ k, k ≤ X.steps12 (E k) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have := hst (nxt^[k] g₀)
      have e : E (k + 1) = (nxt (nxt^[k] g₀)).1.2.2 := by simp only [E, hsucc]
      rw [e]; exact lt_of_le_of_lt ih this
  have hlen : ∀ k, k ≤ (E k).length := fun k => (hsteps k).trans List.countP_le_length
  have hval : ∀ k, I.Valid (E k) := fun k => (hinv k).str.valid
  have hr1 : ∀ k, respsOf (E k) X.p₁ = [] := fun k => (hinv k).resp1
  have hr2 : ∀ k, (respsOf (E k) X.p₂).length = Ix k := fun k => (hinv k).resp2
  by_cases hb : ∀ N, ∃ k, N ≤ (E k).countP (Label.isTauOf X.p₁)
  · exact false_of_starving_chain X.wf E hmono hlen hval X.p₁
      (fun k => by rw [hr1 k, hr1 0]) hb
  push Not at hb
  obtain ⟨N₁, hN₁⟩ := hb
  have hIb : ∀ k, Ix k < N₁ := fun k => lt_of_le_of_lt (hbnd k) (hN₁ k)
  -- the modifier index is eventually constant
  obtain ⟨K, hK⟩ : ∃ K, ∀ k, K ≤ k → Ix k = Ix K := by
    by_contra hcon
    push Not at hcon
    have : ∀ n, ∃ k, n ≤ Ix k := by
      intro n
      induction n with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ n ih =>
        obtain ⟨k, hk⟩ := ih
        obtain ⟨k', hk', hne⟩ := hcon k
        exact ⟨k', by have := hImono' k k' hk'; omega⟩
    obtain ⟨k, hk⟩ := this N₁
    have := hIb k; omega
  -- `p₂` takes unboundedly many steps
  have htau2 : ∀ N, ∃ k, N ≤ (E k).countP (Label.isTauOf X.p₂) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨N₂, hN₂⟩ := hcon
    have hk := hsteps (N₁ + N₂ + 3 * N₁ + 3)
    have hc := count_steps_le (E (N₁ + N₂ + 3 * N₁ + 3)) X.p₁ X.p₂
    have h1 := hN₁ (N₁ + N₂ + 3 * N₁ + 3)
    have h2 := hN₂ (N₁ + N₂ + 3 * N₁ + 3)
    have h3 := hIb (N₁ + N₂ + 3 * N₁ + 3)
    have ho1 : (opsOf (E (N₁ + N₂ + 3 * N₁ + 3)) X.p₁).length ≤ 1 := by
      rcases (hinv (N₁ + N₂ + 3 * N₁ + 3)).str.ops1 with e | e <;> rw [e] <;> simp
    have ho2 : (opsOf (E (N₁ + N₂ + 3 * N₁ + 3)) X.p₂).length ≤ Ix (N₁ + N₂ + 3 * N₁ + 3) + 1 := by
      rcases (hinv (N₁ + N₂ + 3 * N₁ + 3)).str.ops2 with e | e <;> rw [e] <;> simp [pre]
    rw [hr1, hr2] at hc
    simp only [steps12] at hk
    simp only [List.length_nil] at hc
    omega
  -- starvation of `p₂` after `E K`
  refine false_of_starving_chain X.wf (fun m => E (K + m)) (fun m => hmono (K + m))
    (fun m => (hlen (K + m)).trans' (by omega)) (fun m => hval (K + m)) X.p₂
    (fun m => by rw [hr2, hr2, hK (K + m) (by omega), hK (K + 0) (by omega)]) (fun N => ?_)
  obtain ⟨k, hk⟩ := htau2 N
  exact ⟨k, hk.trans (List.IsPrefix.countP_le (hmono' k (K + k) (by omega)))⟩

end Ctx

/-- **Theorem 4.8** of [CPT15], for strong global view types, in the strong form (weak help-freedom).
Let `A` be a strong global view type and `I` a wait-free implementation of `A` from read/write/cas
registers, in a system with three distinct processes that may invoke any operation. Then no
linearization function of `I` is help-free, even in the weak sense that a step deciding `a` before
`b` must be taken by the owner of `a`. -/
theorem theorem_4_8 (I : Impl A (fun i => casObject (V i) (v₀ i)) P L) (hA : StrongGlobalView A)
    (p₁ p₂ p₃ : P) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hall : ∀ p o, I.allowed p o) (hwf : I.WaitFree) : ¬ WeaklyHelpFree I := by
  rintro ⟨f, hlin, hown⟩
  obtain ⟨op, M, W, hgv⟩ := hA
  let X : Ctx I := ⟨f, hlin, hown, hwf, hall, p₁, p₂, p₃, h12, h13, h23, op, M, W⟩
  exact X.false_of_gvSep hgv

/-- **Theorem 4.8** of [CPT15] (for strong global view types): a wait-free linearizable
implementation of such a type from read/write/cas registers, with at least three processes,
cannot be help-free. -/
theorem theorem_4_8_helpFree (I : Impl A (fun i => casObject (V i) (v₀ i)) P L)
    (hA : StrongGlobalView A) (p₁ p₂ p₃ : P) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hall : ∀ p o, I.allowed p o) (hwf : I.WaitFree) : ¬ HelpFree I :=
  fun h => theorem_4_8 I hA p₁ p₂ p₃ h12 h13 h23 hall hwf h.weaklyHelpFree

end CAS

end Podc.HelpFreeWaitFree
