import Papers.PODC2012.LimitedUseSnapshots.Preservation
import Papers.PODC2012.LimitedUseSnapshots.Criterion

/-!
# The corrected Algorithm 2 is linearizable (Theorem 3.4 with the erratum)

From the invariant `Inv` we derive the hypotheses of the max-array linearizability criterion
`exists_isLinearization_maxArr` for every execution of `alg P T true`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] (T : Shape)

/-! ### History lemmas -/

lemma invoked_of_inv_prefix {α β γ : List (Label P maxArrObj)} {pU : P} {o : MAOp}
    (hpre : β ++ .inv pU o :: γ <+: α) :
    opOf α (pU, (opsOf β pU).length) = some o := by
  obtain ⟨δ, rfl⟩ := hpre
  simp [opOf, opsOf_append, List.append_assoc]

lemma completed_of_precedes_of_inv {α β γ : List (Label P maxArrObj)} {y z : OpId P} {o : MAOp}
    (hpre : β ++ .inv y.1 o :: γ <+: α) (hlen : (opsOf β y.1).length = y.2)
    (hp : Precedes α z y) : Completed β z := by
  obtain ⟨β₁, γ₁, rfl, hc, hni⟩ := hp
  have h1 : β ++ [Label.inv y.1 o] <+: β₁ ++ γ₁ := by
    refine List.IsPrefix.trans ?_ hpre; exact ⟨γ, by simp⟩
  by_cases hl : (β ++ [Label.inv y.1 o]).length ≤ β₁.length
  · exfalso; apply hni
    have := (opsOf_prefix (List.prefix_of_prefix_length_le h1 (List.prefix_append _ _) hl) y.1).length_le
    simp [Invoked, opsOf_append] at this ⊢; omega
  · have hb : β <+: β₁ ++ γ₁ := (List.prefix_append _ _).trans hpre
    have := List.prefix_of_prefix_length_le (List.prefix_append β₁ γ₁) hb
      (by simp at hl; omega)
    obtain ⟨δ, rfl⟩ := this
    exact hc.mono

lemma contribOf_of_prefix {α β : List (Label P maxArrObj)} (hwf : WellFormed α) (hp : β <+: α)
    {z : OpId P} (hz : Completed β z) : contribOf α z = contribOf β z := by
  obtain ⟨δ, rfl⟩ := hp
  have hi := (hwf.of_append).invoked_of_completed hz
  simp [contribOf, opOf_append_of_invoked hi, respOf_append_of_completed hz]

/-- From an `InvBefore` record to a witness of the criterion. -/
lemma witness_of_invBefore {α α' : List (Label P maxArrObj)} (hwf : WellFormed α)
    (hα' : α' <+: α) {x : OpId P} (hx : ¬ Completed α' x) {pU : P} {o : MAOp} {r : ℕ × ℕ}
    (h : InvBefore T α' pU o (fun β _ => SeenLE β r)) :
    ∃ u, opOf α u = some o ∧ ¬ Precedes α x u ∧ ∀ y, Precedes α y u → contribOf α y ≤ r := by
  obtain ⟨β, γ, D, rfl, -, hseen⟩ := h
  refine ⟨(pU, (opsOf β pU).length), invoked_of_inv_prefix hα', ?_, fun y hy => ?_⟩
  · obtain ⟨δ, rfl⟩ := hα'
    refine Precedes.not_of_invoked ?_ hx
    simp [Invoked, opsOf_append]
  · have hc := completed_of_precedes_of_inv hα' rfl hy
    rw [contribOf_of_prefix hwf ((List.prefix_append _ _).trans hα') hc]
    exact hseen y hc

/-! ### The criterion's hypotheses -/

/-- Results of completed scans are comparable (the chain property in the proof of
Theorem 3.4). -/
lemma compScan_comparable {C : Cfg P} (hg : ∀ a b, sc C (a ++ [b]) ≤ sc C a) {r s : ℕ × ℕ}
    (hr : CompScan T C r) (hs : CompScan T C s) : r ≤ s ∨ s ≤ r := by
  obtain ⟨hr1, -, hr2, hrg⟩ := hr
  obtain ⟨hs1, -, hs2, hsg⟩ := hs
  have hla := Shape.isAddr_addr T r.1
  have hlb := Shape.isAddr_addr T s.1
  have hra := Shape.subD_addr T r.1
  have hsa := Shape.subD_addr T s.1
  have hlr := Shape.lo_addr T r.1 hr1
  have hls := Shape.lo_addr T s.1 hs1
  rcases Shape.path_trichotomy (T.addr r.1) (T.addr s.1) with h | ⟨c, hc, h⟩ | ⟨c, hc, h⟩ |
      ⟨u, x, y, h1, h2⟩ | ⟨u, x, y, h1, h2⟩
  · have : r.1 = s.1 := by rw [← hlr, ← hls, h]
    rcases le_total r.2 s.2 with h' | h'
    · exact Or.inl (Prod.mk_le_mk.2 ⟨this.le, h'⟩)
    · exact Or.inr (Prod.mk_le_mk.2 ⟨this.ge, h'⟩)
  · exact absurd (h ▸ hlb) (Shape.not_isAddr_of_leaf hra hc)
  · exact absurd (h ▸ hla) (Shape.not_isAddr_of_leaf hsa hc)
  · left
    have hlt := Shape.lo_lt_of_diverge (h1 ▸ hla) (h2 ▸ hlb)
    rw [← h1, ← h2, hlr, hls] at hlt
    refine Prod.mk_le_mk.2 ⟨hlt.le, ?_⟩
    calc r.2 ≤ sc C (T.addr r.1) := hr2
      _ = sc C ((u ++ [false]) ++ x) := by rw [h1]; simp
      _ ≤ sc C (u ++ [false]) := sc_append_le hg _ _
      _ ≤ s.2 := (hsg u y h2).1
  · right
    have hlt := Shape.lo_lt_of_diverge (h2 ▸ hlb) (h1 ▸ hla)
    rw [← h1, ← h2, hlr, hls] at hlt
    refine Prod.mk_le_mk.2 ⟨hlt.le, ?_⟩
    calc s.2 ≤ sc C (T.addr s.1) := hs2
      _ = sc C ((u ++ [false]) ++ y) := by rw [h2]; simp
      _ ≤ sc C (u ++ [false]) := sc_append_le hg _ _
      _ ≤ r.2 := (hrg u x h1).1

/-- Lemma 3.2 of the paper, in the flattened tree: the `second` register of a child never exceeds
that of its parent (corrected algorithm, every reachable configuration). -/
theorem lemma_3_2 {α : List (Label P maxArrObj)} {C : Cfg P}
    (h : (alg P T true).run α = some C) (a : List Bool) (b : Bool) :
    sc C (a ++ [b]) ≤ sc C a :=
  (inv_of_run T h).g1 a b

/-- The chain property of the proof of Theorem 3.4: any two completed `MaxScan`s return
componentwise comparable pairs. -/
theorem maxScan_comparable {α : List (Label P maxArrObj)} {C : Cfg P}
    (h : (alg P T true).run α = some C) {x y : OpId P} {r s : ℕ × ℕ}
    (hx : opOf α x = some .scan) (hr : respOf α x = some r)
    (hy : opOf α y = some .scan) (hs : respOf α y = some s) : r ≤ s ∨ s ≤ r := by
  have hI := inv_of_run T h
  exact compScan_comparable T hI.g1 (hI.compScan x r hx hr) (hI.compScan y s hy hs)

/-- **Theorem 3.4, corrected (erratum).** With the embedded `MaxScan` in `MaxUpdate1`
(line 9.5 of the erratum), Algorithm 2 implements a linearizable `MaxArray_{k×h}`, for every tree
shape (every choice of the split points `m`) and any set of processes. -/
theorem alg2_fixed_linearizable : (alg P T true).Linearizable := by
  refine Impl.linearizable_of_run (fun α C hrun => ?_)
  have hI := inv_of_run T hrun
  have hwf : WellFormed α := Impl.Valid.wellFormed _ ⟨C, hrun⟩
  refine exists_isLinearization_maxArr α hwf ?_ ?_ ?_ ?_ hI.resp0
  · intro x y r s hx hr hy hs
    exact compScan_comparable T hI.g1 (hI.compScan x r hx hr) (hI.compScan y s hy hs)
  · intro x r y hx hr hp
    obtain ⟨⟨β, γ, hpre, hlen, hseen⟩, -⟩ := hI.hist x r hx hr
    have hc := completed_of_precedes_of_inv hpre hlen hp
    rw [contribOf_of_prefix hwf ((List.prefix_append _ _).trans hpre) hc]
    exact hseen y hc
  · intro x r hx hr h0
    obtain ⟨-, α', hα', hnc, h3a, -⟩ := hI.hist x r hx hr
    obtain ⟨pU, hpU⟩ := h3a h0
    exact witness_of_invBefore T hwf hα' hnc hpU
  · intro x r hx hr h0
    obtain ⟨-, α', hα', hnc, -, h3b⟩ := hI.hist x r hx hr
    obtain ⟨pU, hpU⟩ := h3b h0
    exact witness_of_invBefore T hwf hα' hnc hpU

end Podc.LimitedUseSnapshots
