import Mathlib
import Papers.PODC2023.RuntimeVerification.Theorems

/-!
# Self-enforced implementations (Theorem 8.2) and prefixes of executions

The self-enforced implementation `V_{O,A}` of Figure 11 has exactly the steps of `V_O` running
`A*`: its operation is invoked at step 0 and returns, after the test at step 7, either the response
`y` of `A` or `ERROR` (when `Reports`). Its history with responses `y` is `Exec.hVy`.

* `tauAt_cut`, `reports_cut_iff` — what the verifier reads depends only on the past.
* `hVy_mem_of_noReport` — if no operation returned `ERROR`, the history of `V_{O,A}` is in `O`.
* `hVy_cut_mem` — Theorem 8.2 (2): the history of `V_{O,A}` is correct up to the first `ERROR`.
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing Sketch

set_option linter.unusedSectionVars false

variable {n : ℕ} {Op Y : Type} [DecidableEq Op] [DecidableEq Y] [Inhabited Op] [Inhabited Y]

namespace Exec

variable {E : Exec n Op Y ℕ}

theorem view_cut (hw : E.WF) {t : ℕ} {q : Fin n} {j : ℕ} (h : E.T q (8 * j + 4) < t) :
    (E.cut t).view 8 q j = E.view 8 q j := by
  ext x
  rw [mem_view8, mem_view8]
  change 8 * x.2.1 + 1 < (E.cut t).len x.1 ∧ E.T x.1 (8 * x.2.1 + 1) < E.T q (8 * j + 4) ∧
      x.2.2 = E.op x.1 x.2.1 ↔ _
  rw [lt_cut_len hw]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, lt_trans h2 h⟩, h2, h3⟩

theorem tauAt_cut (hw : E.WF) {s t : ℕ} (hst : s ≤ t) : (E.cut t).tauAt s = E.tauAt s := by
  ext u
  rw [mem_tauAt, mem_tauAt]
  constructor
  · rintro ⟨q, j, h1, h2, rfl⟩
    have h1' := ((lt_cut_len hw t q _).1 h1).1
    refine ⟨q, j, h1', h2, ?_⟩
    simp only [tup]
    rw [view_cut hw (lt_of_lt_of_le (lt_trans (hw.mono q _ _ (by omega) h1') h2) hst)]
    rfl
  · rintro ⟨q, j, h1, h2, rfl⟩
    refine ⟨q, j, (lt_cut_len hw t q _).2 ⟨h1, by change E.T q (8 * j + 6) < t; omega⟩, h2, ?_⟩
    simp only [tup]
    rw [view_cut hw (lt_of_lt_of_le (lt_trans (hw.mono q _ _ (by omega) h1) h2) hst)]
    rfl

theorem reports_cut_iff (hw : E.WF) {O : Set (Hist (Fin n) Op Y)} {t : ℕ} {p : Fin n} {k : ℕ}
    (h1 : 8 * k + 7 < E.len p) (h2 : E.T p (8 * k + 7) < t) :
    (E.cut t).Reports O p k ↔ E.Reports O p k := by
  simp only [Reports, tau]
  rw [show (E.cut t).T = E.T from rfl, tauAt_cut hw h2.le, lt_cut_len hw]
  simp [h1, h2]

/-- **Theorem 8.2 (core).** If no operation of `V_{O,A}` returned `ERROR` in `E`, then the history
of `V_{O,A}` is in `O` (for `O ∈ GenLin` containing the empty history). -/
theorem hVy_mem_of_noReport {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hO₀ : [] ∈ O)
    (hw : E.WF) (hno : ∀ p k, ¬ E.Reports O p k) : E.hVy.toList ∈ O := by
  set D : Finset (Fin n × ℕ) := (Finset.univ : Finset (Fin n)).biUnion fun p =>
    (Finset.range (cnt 8 7 (E.len p))).image fun k => (p, k)
  have memD : ∀ p k, (p, k) ∈ D ↔ 8 * k + 7 < E.len p := by
    intro p k
    simp only [D, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨q, j, hj, rfl, rfl⟩; exact (lt_cnt (by norm_num)).1 hj
    · intro h; exact ⟨p, k, (lt_cnt (by norm_num)).2 h, rfl, rfl⟩
  -- the time of the last test
  obtain ⟨s, hsD, hX⟩ : ∃ s : ℕ, (∀ p k, 8 * k + 7 < E.len p → E.T p (8 * k + 7) ≤ s) ∧
      (XTHy (E.tauAt s)).toList ∈ O := by
    by_cases hD : D.Nonempty
    · obtain ⟨⟨z, kz⟩, hz, hmax⟩ := Finset.exists_max_image D (fun x => E.T x.1 (8 * x.2 + 7)) hD
      refine ⟨E.T z (8 * kz + 7), fun p k hk => hmax (p, k) ((memD p k).2 hk), ?_⟩
      by_contra hc
      exact hno z kz ⟨(memD z kz).1 hz, hc⟩
    · refine ⟨0, fun p k hk => absurd ⟨(p, k), (memD p k).2 hk⟩ hD, ?_⟩
      have h0 : E.tauAt 0 = ∅ := by
        ext u; simp [mem_tauAt]
      rw [h0, TH.toList_eq_nil]
      · exact hO₀
      · intro p; simp [XTHy, TH.mapRes, XTH, ids, allInv]
      · intro p; simp [XTHy, TH.mapRes, XTH, cids]
  have hv := valid_tauAt hw s
  have hsim : TH.SimTH E.hVy ((XTH (E.tauAt s)).mapRes Prod.fst) := by
    refine ⟨fun q => le_of_forall_lt fun j hj => ?_, fun q j hj => ?_,
      fun p => le_of_forall_lt fun k hk => ?_, fun p k hk => ?_, fun p k q j hk hj h => ?_⟩
    · obtain ⟨x, hx, rfl, rfl⟩ := (lt_m_iff hv).1 hj
      obtain ⟨-, -, -, -, h1, -⟩ := mem_allInv_tauAt.1 hx
      show x.2.1 < cnt 8 0 (E.len x.1)
      rw [lt_cnt (by norm_num)]; omega
    · obtain ⟨x, hx, rfl, rfl⟩ := (lt_m_iff hv).1 hj
      show E.op x.1 x.2.1 = (XTH (E.tauAt s)).op x.1 x.2.1
      rw [op_eq hv hx, op_of_mem_allInv hx]
    · have hk' : 8 * k + 7 < E.len p := (lt_cnt (by norm_num)).1 hk
      refine (lt_c_tauAt hw).2 ⟨by omega, ?_⟩
      exact lt_of_lt_of_le (hw.mono p _ _ (by omega) hk') (hsD p k hk')
    · have hk' : 8 * k + 7 < E.len p := (lt_cnt (by norm_num)).1 hk
      have hu := tup_mem_tauAt (s := s) (show 8 * k + 6 < E.len p by omega)
        (lt_of_lt_of_le (hw.mono p _ _ (by omega) hk') (hsD p k hk'))
      have := res_eq hv hu
      simp only [tup] at this
      show E.y p k = ((XTH (E.tauAt s)).res p k).1
      rw [this]
    · have hk' : 8 * k + 7 < E.len p := (lt_cnt (by norm_num)).1 hk
      have hu := tup_mem_tauAt (s := s) (show 8 * k + 6 < E.len p by omega)
        (lt_of_lt_of_le (hw.mono p _ _ (by omega) hk') (hsD p k hk'))
      obtain ⟨x, hx, rfl, rfl⟩ := (lt_m_iff hv).1 hj
      obtain ⟨-, -, -, -, hx1, -, hxo⟩ := mem_allInv_tauAt.1 hx
      have key := (tr_lt_ti_iff hv hu hx).2 (by
        simp only [tup]
        rw [mem_view8]
        intro hh
        have e1 : E.T x.1 (8 * x.2.1 + 0) < E.T x.1 (8 * x.2.1 + 1) :=
          hw.mono _ _ _ (by omega) hx1
        have e2 : E.T p (8 * k + 4) < E.T p (8 * k + 7) := hw.mono _ _ _ (by omega) hk'
        change E.T p (8 * k + 7) < E.T x.1 (8 * x.2.1 + 0) at h
        omega)
      exact key
  exact GenLin.mem_of_simTH hO (hVy_WF hw) ((XTH_WF hv).mapRes _) hsim hX

/-- **Theorem 8.2 (2), finite form.** The history of `V_{O,A}` up to any time `t` before which no
operation returned `ERROR` belongs to `O`: `V_{O,A}` is correct up to its first `ERROR`. -/
theorem hVy_cut_mem {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hO₀ : [] ∈ O) (hw : E.WF)
    {t : ℕ} (hno : ∀ p k, 8 * k + 7 < E.len p → E.T p (8 * k + 7) < t → ¬ E.Reports O p k) :
    (E.cut t).hVy.toList ∈ O := by
  refine hVy_mem_of_noReport hO hO₀ (hw.cut t) fun p k hr => ?_
  have h1 := hr.1
  rw [lt_cut_len hw] at h1
  exact hno p k h1.1 h1.2 ((reports_cut_iff hw h1.1 h1.2).1 hr)

end Exec

end Podc2023.RuntimeVerification
