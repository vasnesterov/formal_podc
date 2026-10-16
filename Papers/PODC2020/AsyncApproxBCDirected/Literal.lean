import Papers.PODC2020.AsyncApproxBCDirected.Round

/-!
# The algorithm as literally written does not work

1. **Covers containing the receiver.** In the paper, a message received by `v` carries a path
   ending at `v` (Definition 9), and an `f`-cover is any set of `≤ f` nodes meeting every path
   (Definition 4). Then `{v}` is an `f`-cover of every set of messages held by `v` (as soon as
   `f ≥ 1`), and
   * `Completeness(Mv, M^c, Fu)` (Algorithm 2) is **never** satisfied: choose `Fw` with
     `v ∈ Fu ∪ Fw`, so that `v ∉ S_{Fu,Fw}` and `H = {v} ⊆ V \ S_{Fu,Fw}`
     (`not_completenessLit`);
   * hence `Verify` (lines 20–26) never holds in any thread, because FIFO-Receive-All includes
     `v`'s own `COMPLETE(Fv)` (`never_verifyLit`): no correct node ever executes
     Filter-and-Average, contradicting Theorem 9;
   * Filter-and-Average trims the whole vector (`not_isFALit`).
   The intended reading (used in the rest of the formalization) never puts `v` in a cover.
2. **`(max − min)/2`.** Line 5 of Algorithm 3 sets `x_v[r+1] = (max O' − min O')/2`. With this
   update, validity fails as soon as the correct inputs are not all equal to `0`: in a
   fault-free round where every node has input `1`, the new value is `0`
   (`minus_update_invalid`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-- Algorithm 2 exactly as written: covers `H ⊆ V \ S_{Fu,Fw}` may contain `v`. -/
def CompletenessLit (G : Digraph V) (f : ℕ) (Mv Mc : Finset (Msg V)) (Fu : Finset V) : Prop :=
  ∀ Fw : Finset V, Fw.card ≤ f → Fw ≠ Fu → ∀ q ∈ srcComp G Fu Fw,
    ∃ m ∈ Mc, m.2.head? = some q ∧
      ¬ ∃ H : Finset V, H.card ≤ f ∧ (∀ h ∈ H, h ∉ srcComp G Fu Fw) ∧
        ∀ m' ∈ Mv, m'.2.head? = some q → m'.1 = m.1 → ¬ Avoids m'.2 H

/-- If `f ≥ 1`, all paths of `Mv` contain `v`, and the source components are non-empty, the
literal `Completeness` condition fails for every `Mc` and `Fu`. -/
theorem not_completenessLit (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) (hf : 1 ≤ f)
    {v : V} {Mv Mc : Finset (Msg V)} {Fu : Finset V} (hFu : Fu.card ≤ f)
    (hMv : ∀ m ∈ Mv, v ∈ m.2) : ¬ CompletenessLit G f Mv Mc Fu := by
  classical
  intro h
  set Fw : Finset V := if Fu = {v} then ∅ else {v}
  have hFw : Fw.card ≤ f := by by_cases hu : Fu = {v} <;> simp [Fw, hu, hf]
  have hne : Fw ≠ Fu := by
    by_cases hu : Fu = {v}
    · simp only [Fw, hu, ite_true]; exact fun h => by simp at h
    · simp only [Fw, hu, ite_false]; exact fun h => hu h.symm
  have hv : v ∈ Fu ∪ Fw := by
    by_cases hu : Fu = {v}
    · simp [hu]
    · simp [Fw, hu]
  obtain ⟨q, hq⟩ := hG.srcComp_nonempty hn hFu hFw
  obtain ⟨m, -, -, hno⟩ := h Fw hFw hne q hq
  refine hno ⟨{v}, by simpa using hf, fun h hh hhS => ?_, fun m' hm' _ _ hav => ?_⟩
  · rw [mem_singleton] at hh; subst hh
    exact notMem_of_mem_srcComp hn hhS hv
  · exact hav v (hMv m' hm') (mem_singleton_self v)

namespace RoundExec

variable (E : RoundExec G f)

/-- `Verify` with the literal Algorithm 2. -/
def VerifyLit (v : V) (Fv : Finset V) (t : ℕ) : Prop :=
  (∃ t' ≤ t, E.FIFORecAll v Fv t') ∧
  ∀ c p Mc Fu, (c, p, Mc, Fu) ∈ E.CR v t → (∀ y ∈ p, Reaches G Fv y v) → Consistent Mc →
    CompletenessLit G f (E.M v t) Mc Fu

/-- **Counterexample to Theorem 9 for the literal algorithm**: under 3-reach with `n ≥ 2` and
`f ≥ 1`, in *every* round execution, the literal `Verify` condition never holds, in any thread,
at any correct node: no correct node ever executes Filter-and-Average. -/
theorem never_verifyLit (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) (hf : 1 ≤ f) {v : V}
    (hv : v ∉ E.F) (Fv : Finset V) (hvF : v ∉ Fv) (t : ℕ) : ¬ E.VerifyLit v Fv t := by
  rintro ⟨⟨t', ht', hfifo⟩, hcomp⟩
  obtain ⟨Mc, hMc⟩ := hfifo v
  have hm := hMc [v] isSimplePath_singleton (by simpa using Reaches.refl (G := G) hvF)
  obtain ⟨-, hs, rfl, -⟩ := E.CR_honest v hv t' v [v] Mc Fv hm (by simpa [Avoids] using hv)
  refine not_completenessLit (v := v) hG hn hf hs.2.1 (fun m hm' => ?_)
    (hcomp v [v] _ Fv (E.CR_mono v ht' hm) (by simpa using Reaches.refl (G := G) hvF)
      (hs.consistent G f))
  exact List.mem_of_getLast? (E.M_last v hv t m hm')

end RoundExec

/-- Algorithm 3 with literal covers (which may contain `v`). -/
def IsFALit (f : ℕ) (Mv : Finset (Msg V)) (y : ℝ) : Prop :=
  ∃ (O : List (Msg V)) (i j : ℕ) (a b : ℝ),
    O.Perm Mv.toList ∧ O.Pairwise (fun m m' => m.1 ≤ m'.1) ∧
    IsGreatest {k | k ≤ O.length ∧ ∃ H : Finset V, H.card ≤ f ∧
      ∀ m ∈ O.take k, ¬ Avoids m.2 H} i ∧
    IsLeast {k | k ≤ O.length ∧ ∃ H : Finset V, H.card ≤ f ∧
      ∀ m ∈ O.drop k, ¬ Avoids m.2 H} j ∧
    IsLeast (windowVals O i j) a ∧ IsGreatest (windowVals O i j) b ∧ y = (a + b) / 2

/-- With literal covers, Filter-and-Average trims everything and has no output (`f ≥ 1`, all
paths contain `v`). -/
theorem not_isFALit (hf : 1 ≤ f) {v : V} {Mv : Finset (Msg V)} (hMv : ∀ m ∈ Mv, v ∈ m.2)
    (y : ℝ) : ¬ IsFALit f Mv y := by
  rintro ⟨O, i, j, a, b, hperm, -, hi, -, ha, -, -⟩
  have hO : O.length ∈ {k | k ≤ O.length ∧ ∃ H : Finset V, H.card ≤ f ∧
      ∀ m ∈ O.take k, ¬ Avoids m.2 H} := by
    refine ⟨le_rfl, {v}, by simpa using hf, fun m hm hav => ?_⟩
    have hmM : m ∈ Mv := Finset.mem_toList.mp (hperm.mem_iff.mp (List.mem_of_mem_take hm))
    exact hav v (hMv m hmM) (mem_singleton_self v)
  have := hi.2 hO
  obtain ⟨m, hm, -⟩ := ha.1
  obtain ⟨k, hk, hik, -, -⟩ := mem_window.mp hm
  omega

/-- Algorithm 3 with the literal update `(max − min)/2`. -/
def IsFAMinus (f : ℕ) (v : V) (Mv : Finset (Msg V)) (y : ℝ) : Prop :=
  ∃ (O : List (Msg V)) (i j : ℕ) (a b : ℝ),
    O.Perm Mv.toList ∧ O.Pairwise (fun m m' => m.1 ≤ m'.1) ∧
    IsGreatest {k | k ≤ O.length ∧ Coverable f v (O.take k)} i ∧
    IsLeast {k | k ≤ O.length ∧ Coverable f v (O.drop k)} j ∧
    IsLeast (windowVals O i j) a ∧ IsGreatest (windowVals O i j) b ∧ y = (b - a) / 2

/-- With the update `(max − min)/2`, a node whose messages all carry the value `1` (e.g. a
fault-free round in which every correct input is `1`) moves to `0`, violating validity. -/
theorem minus_update_invalid {v : V} {Mv : Finset (Msg V)} (hMv : ∀ m ∈ Mv, m.1 = 1) {y : ℝ}
    (hy : IsFAMinus f v Mv y) : y = 0 := by
  obtain ⟨O, i, j, a, b, hperm, -, -, -, ha, hb, rfl⟩ := hy
  have hval : ∀ z ∈ windowVals O i j, z = 1 := by
    rintro z ⟨m, hm, rfl⟩
    exact hMv m (Finset.mem_toList.mp (hperm.mem_iff.mp
      (List.mem_of_mem_take (List.mem_of_mem_drop hm))))
  rw [hval a ha.1, hval b hb.1]; norm_num

end AsyncApproxBCDirected
