import Papers.PODC2015.ABADetection.Lemma1
import Papers.PODC2015.ABADetection.Lemma3
import Papers.PODC2015.ABADetection.Observation

/-!
# Theorem 1 and Corollary 1 (Aghazadeh–Woelfel, PODC 2015)

* `theorem1a`: a linearizable, obstruction-free (deterministic) implementation of a single-writer
  ABA-detecting register from `m` bounded registers satisfies `m ≥ n - 1`.
* `theorem1b`: a linearizable, wait-free implementation with step complexity `≤ t` from `m`
  bounded registers and (non-writable) CAS objects satisfies `t · m ≥ n - 1`.
* `theorem1c`: the same from `m` bounded *writable* CAS objects satisfies `2 · t · m ≥ n - 1`.
* `corollary1a`, `corollary1b`: the same two tradeoffs for linearizable implementations of
  LL/SC objects (only `LL` and `SC` are used; `VL` need not be supported).

Registers and non-writable CAS objects are modelled as writable CAS objects (`wcasObj`) on which
the implementation only uses `Read`/`Write`, respectively `Read`/`CAS`: hypothesis `hkind` on the
poised accesses in reachable configurations (`RegOrCas`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

section Abstract

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}
  {I : Impl A (fun _ : ι => wcasObj V v₀) P L} {w0 : P} {rd : P → A.Op} {ws : List A.Op}

/-- The base objects in `isCas` are (non-writable) CAS objects, the others registers: in
reachable configurations, no pending process is poised to `Write` an object of `isCas` or to
`CAS` an object outside `isCas`. -/
def RegOrCas (I : Impl A (fun _ : ι => wcasObj V v₀) P L) (isCas : ι → Prop) : Prop :=
  ∀ C, I.Reachable C → ∀ q, C.pend q ≠ none → ∀ R,
    ((∃ v, poisedAcc I C q = some (R, .write v)) → ¬ isCas R) ∧
    ((∃ x y, poisedAcc I C q = some (R, .cas x y)) → isCas R)

/-- The configuration of Lemma 3 for all readers. -/
lemma exists_lemma3_cfg [Fintype P] [Finite ι] [Finite V] (t : ℕ)
    (hof : I.ObstructionFree) (hbound : StepBound I t) (hsep : Separates I w0 rd ws)
    (hrd : ∀ p, p ≠ w0 → I.allowed p (rd p)) (hws : ∀ o ∈ ws, I.allowed w0 o) :
    ∃ C β, I.Reachable C ∧ β.Nodup ∧ (∀ q, q ∈ β ↔ q ≠ w0) ∧ Succ I C β ∧
      ∀ R, (WCov I C R (Finset.univ.erase w0)).card ≤ t ∧
        (CCov I C R (Finset.univ.erase w0)).card ≤ t := by
  set ps := (Finset.univ.erase w0).toList
  obtain ⟨α, C, β, h1, -, -, -, h5, h6, h7⟩ := lemma3 t hof hbound hsep hrd hws ps
    (Finset.nodup_toList _) (by simp [ps]) [] I.initCfg rfl (fun _ => rfl)
    (fun _ _ h => by simp at h)
  refine ⟨C, β, ⟨α, h1⟩, h5.nodup_iff.2 (Finset.nodup_toList _), fun q => by
    rw [h5.mem_iff]; simp [ps], h6, fun R => ?_⟩
  simpa [ps] using h7 R

open Classical in
lemma card_le_sum_cov [Fintype P] [Fintype ι] {C : Config A (fun _ : ι => wcasObj V v₀) P L}
    {β : List P} (hnd : β.Nodup) (hmem : ∀ q, q ∈ β ↔ q ≠ w0) (hs : Succ I C β) :
    (Finset.univ.erase w0).card ≤ ∑ R, (WCov I C R (Finset.univ.erase w0) ∪
      CCov I C R (Finset.univ.erase w0)).card := by
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro q hq
  have hqβ : q ∈ β := (hmem q).2 (Finset.ne_of_mem_erase hq)
  obtain ⟨-, R, hR⟩ := hs.poised hnd q hqβ
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  refine ⟨R, ?_⟩
  rcases hR with h | h
  · left; simp only [WCov, Finset.mem_filter]; exact ⟨hq, h⟩
  · right; simp only [CCov, Finset.mem_filter]; exact ⟨hq, h⟩

/-- **Theorem 1(c), abstract form.** -/
theorem card_le_of_separates_wcas [Fintype P] [Fintype ι] [Finite V] (t : ℕ)
    (hof : I.ObstructionFree) (hbound : StepBound I t) (hsep : Separates I w0 rd ws)
    (hrd : ∀ p, p ≠ w0 → I.allowed p (rd p)) (hws : ∀ o ∈ ws, I.allowed w0 o) :
    Fintype.card P - 1 ≤ 2 * t * Fintype.card ι := by
  classical
  obtain ⟨C, β, -, hnd, hmem, hs, hcov⟩ := exists_lemma3_cfg t hof hbound hsep hrd hws
  have h := card_le_sum_cov hnd hmem hs
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h
  refine h.trans ((Finset.sum_le_sum fun R _ => (Finset.card_union_le _ _).trans
    (add_le_add (hcov R).1 (hcov R).2)).trans ?_)
  simp [Finset.sum_const, Finset.card_univ]; ring_nf; omega

/-- **Theorem 1(b), abstract form.** -/
theorem card_le_of_separates_regOrCas [Fintype P] [Fintype ι] [Finite V] (t : ℕ)
    (isCas : ι → Prop) (hkind : RegOrCas I isCas)
    (hof : I.ObstructionFree) (hbound : StepBound I t) (hsep : Separates I w0 rd ws)
    (hrd : ∀ p, p ≠ w0 → I.allowed p (rd p)) (hws : ∀ o ∈ ws, I.allowed w0 o) :
    Fintype.card P - 1 ≤ t * Fintype.card ι := by
  classical
  obtain ⟨C, β, hreach, hnd, hmem, hs, hcov⟩ := exists_lemma3_cfg t hof hbound hsep hrd hws
  have h := card_le_sum_cov hnd hmem hs
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h
  have hpend : ∀ q ∈ Finset.univ.erase w0, C.pend q ≠ none := fun q hq =>
    (hs.poised hnd q ((hmem q).2 (Finset.ne_of_mem_erase hq))).1
  refine h.trans ((Finset.sum_le_sum fun R _ => ?_).trans
    (by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]))
  by_cases hR : isCas R
  · have : WCov I C R (Finset.univ.erase w0) = ∅ := by
      ext q
      simp only [WCov, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hq hw
      exact (hkind C hreach q (hpend q hq) R).1 hw hR
    rw [this, Finset.empty_union]; exact (hcov R).2
  · have : CCov I C R (Finset.univ.erase w0) = ∅ := by
      ext q
      simp only [CCov, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hq hc
      exact hR ((hkind C hreach q (hpend q hq) R).2 hc)
    rw [this, Finset.union_empty]; exact (hcov R).1

end Abstract

/-! ## The theorems for ABA-detecting registers and LL/SC objects -/

variable {P W ι L : Type} [DecidableEq P] [DecidableEq ι] [Fintype P] [Fintype ι]

/-- **Theorem 1(a)** of [Aghazadeh–Woelfel, PODC 2015]: any linearizable, obstruction-free
implementation of a single-writer ABA-detecting register (writer `w0`) from `m` bounded registers
uses `m ≥ n - 1` registers. (The paper states it for 1-bit registers, `W = Bool`, and
nondeterministic solo-terminating implementations; here implementations are deterministic, for
which nondeterministic solo-termination is obstruction-freedom.) -/
theorem theorem1a {V : ι → Type} [∀ i, Finite (V i)] {v₀ : ∀ i, V i} {x₀ : W}
    (I : Impl (abaObj P W x₀) (fun i => register (V i) (v₀ i)) P L) (w0 : P) (x : W)
    (hlin : I.Linearizable) (hof : I.ObstructionFree)
    (hw : I.allowed w0 (.dwrite x)) (hrd : ∀ p, p ≠ w0 → I.allowed p (.dread p)) :
    Fintype.card P - 1 ≤ Fintype.card ι :=
  card_le_of_separates (ws := [ABAOp.dwrite x]) (rd := fun p => ABAOp.dread p)
    (fun i o => by
      cases o with
      | read => exact Or.inl (register_read_readOnly _)
      | write v => exact Or.inr (register_write_overwrites _ v))
    hof (separates_aba I w0 x hlin hof hrd) hrd (by simpa using hw)

/-- **Theorem 1(b)** of [Aghazadeh–Woelfel, PODC 2015]: any linearizable, wait-free implementation
of a single-writer ABA-detecting register with worst-case step complexity `≤ t` from `m` bounded
registers and CAS objects satisfies `t · m ≥ n - 1`. -/
theorem theorem1b {V : Type} [DecidableEq V] [Finite V] {v₀ : V} {x₀ : W}
    (I : Impl (abaObj P W x₀) (fun _ : ι => wcasObj V v₀) P L) (w0 : P) (x : W) (t : ℕ)
    (isCas : ι → Prop) (hkind : RegOrCas I isCas)
    (hlin : I.Linearizable) (hwf : I.WaitFree) (hbound : StepBound I t)
    (hw : I.allowed w0 (.dwrite x)) (hrd : ∀ p, p ≠ w0 → I.allowed p (.dread p)) :
    Fintype.card P - 1 ≤ t * Fintype.card ι :=
  card_le_of_separates_regOrCas (ws := [ABAOp.dwrite x]) (rd := fun p => ABAOp.dread p) t isCas hkind
    hwf.obstructionFree hbound (separates_aba I w0 x hlin hwf.obstructionFree hrd) hrd
    (by simpa using hw)

/-- **Theorem 1(c)** of [Aghazadeh–Woelfel, PODC 2015]: any linearizable, wait-free implementation
of a single-writer ABA-detecting register with worst-case step complexity `≤ t` from `m` bounded
writable CAS objects satisfies `2 · t · m ≥ n - 1`. -/
theorem theorem1c {V : Type} [DecidableEq V] [Finite V] {v₀ : V} {x₀ : W}
    (I : Impl (abaObj P W x₀) (fun _ : ι => wcasObj V v₀) P L) (w0 : P) (x : W) (t : ℕ)
    (hlin : I.Linearizable) (hwf : I.WaitFree) (hbound : StepBound I t)
    (hw : I.allowed w0 (.dwrite x)) (hrd : ∀ p, p ≠ w0 → I.allowed p (.dread p)) :
    Fintype.card P - 1 ≤ 2 * t * Fintype.card ι :=
  card_le_of_separates_wcas (ws := [ABAOp.dwrite x]) (rd := fun p => ABAOp.dread p) t
    hwf.obstructionFree hbound (separates_aba I w0 x hlin hwf.obstructionFree hrd) hrd
    (by simpa using hw)

/-- **Corollary 1(a)** of [Aghazadeh–Woelfel, PODC 2015]: any linearizable, wait-free
implementation of an LL/SC object (values `W`, e.g. a single bit) with worst-case step complexity
`≤ t` from `m` bounded registers and CAS objects satisfies `t · m ≥ n - 1`. Only `LL` and `SC`
are invoked (by `w0`: `LL(); SC(x)`, by the others: `LL()` and `SC(y)`). -/
theorem corollary1a {V : Type} [DecidableEq V] [Finite V] {v₀ : V} {x₀ : W}
    (I : Impl (llscObj W P x₀) (fun _ : ι => wcasObj V v₀) P L) (w0 : P) (x y : W) (t : ℕ)
    (isCas : ι → Prop) (hkind : RegOrCas I isCas)
    (hlin : I.Linearizable) (hwf : I.WaitFree) (hbound : StepBound I t)
    (hwll : I.allowed w0 (.ll w0)) (hwsc : I.allowed w0 (.sc w0 x))
    (hll : ∀ p, p ≠ w0 → I.allowed p (.ll p)) (hsc : ∀ p, p ≠ w0 → I.allowed p (.sc p y)) :
    Fintype.card P - 1 ≤ t * Fintype.card ι :=
  card_le_of_separates_regOrCas (ws := [LLOp.ll w0, LLOp.sc w0 x]) (rd := fun p => LLOp.ll p) t isCas hkind
    hwf.obstructionFree hbound (separates_llsc I w0 x y hlin hwf.obstructionFree hsc) hll
    (by simp [hwll, hwsc])

/-- **Corollary 1(b)** of [Aghazadeh–Woelfel, PODC 2015]: the same from `m` bounded writable CAS
objects gives `2 · t · m ≥ n - 1`. -/
theorem corollary1b {V : Type} [DecidableEq V] [Finite V] {v₀ : V} {x₀ : W}
    (I : Impl (llscObj W P x₀) (fun _ : ι => wcasObj V v₀) P L) (w0 : P) (x y : W) (t : ℕ)
    (hlin : I.Linearizable) (hwf : I.WaitFree) (hbound : StepBound I t)
    (hwll : I.allowed w0 (.ll w0)) (hwsc : I.allowed w0 (.sc w0 x))
    (hll : ∀ p, p ≠ w0 → I.allowed p (.ll p)) (hsc : ∀ p, p ≠ w0 → I.allowed p (.sc p y)) :
    Fintype.card P - 1 ≤ 2 * t * Fintype.card ι :=
  card_le_of_separates_wcas (ws := [LLOp.ll w0, LLOp.sc w0 x]) (rd := fun p => LLOp.ll p) t
    hwf.obstructionFree hbound (separates_llsc I w0 x y hlin hwf.obstructionFree hsc) hll
    (by simp [hwll, hwsc])

end Cslib.SharedMemory.ABADetection
