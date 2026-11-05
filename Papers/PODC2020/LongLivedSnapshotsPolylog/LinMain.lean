import Papers.PODC2020.LongLivedSnapshotsPolylog.LinInv
import Papers.PODC2012.LimitedUseSnapshots.Criterion

/-!
# Algorithm 1 is linearizable (the linearizability part of Theorem 3.7)

Certificates are ordered by their scan times (`cert_le`); every completed operation has a
certificate inside its execution interval (`Inv`, `OpCert`); every nonzero component of a view
is the value of an invoked `MaxUpdate` (`WInv`). The max-array criterion
`Podc.LimitedUseSnapshots.exists_isLinearization_maxArr` then gives a linearization of every
finite execution (`alg1_linearizable`).

The paper's own linearization (rules 1–3 of Section 3.1, Definition 3.2 and Claim 4) is wrong,
see `Counterexample.lean`; the statement survives with the argument above.
-/

namespace Podc.LongLivedSnapshotsPolylog

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp contribOf exists_isLinearization_maxArr
  invoked_take_mono completed_take_mono)

variable {n m X : ℕ}

lemma pair_eq {a b a' b' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h : a + b = a' + b') :
    a = a' ∧ b = b' := by omega

/-- Two certified views are ordered like their scan times. -/
theorem cert_le {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {V V' : ℕ × ℕ}
    {t0 t1 t0' t1' : ℕ} (h : Cert m X α V t0 t1) (h' : Cert m X α V' t0' t1') (ht : t1 ≤ t1') :
    V ≤ V' := by
  obtain ⟨h01, h1l, ⟨a, b, hab, hV⟩, -, -, hV1, hV2, -, -⟩ := h
  obtain ⟨h01', h1l', ⟨a', b', hab', hV'⟩, hL0', hR0', -, -, -, -⟩ := h'
  obtain ⟨ha1, hb1⟩ := hab t1 h01 le_rfl
  obtain ⟨ha1', hb1'⟩ := hab' t1' h01' le_rfl
  by_cases he : a = a' ∧ b = b'
  · obtain ⟨rfl, rfl⟩ := he
    have := monoMA (X := X) hv ht h1l' (a + b)
    rw [hV, hV']
    exact Prod.mk_le_mk.2 ⟨by have := this.1; omega, by have := this.2; omega⟩
  · have ht01 : t1 < t0' := by
      by_contra hc
      obtain ⟨ha, hb⟩ := hab' t1 (by omega) ht
      exact he ⟨by omega, by omega⟩
    have hL := monoL (X := X) hv (le_of_lt ht01) (by omega)
    have hR := monoR (X := X) hv (le_of_lt ht01) (by omega)
    exact Prod.mk_le_mk.2 ⟨by omega, by omega⟩

/-- The invariant holds in every prefix. -/
lemma inv_take {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t : ℕ} (ht : t ≤ α.length) :
    Inv m X (α.take t) (cfgAt m X α t) :=
  inv_run (run_take_eq hv ht)

lemma lt_of_completed_not {α : List (Lbl n)} {x : OpId (Fin n)} {k t : ℕ}
    (hk : Completed (α.take k) x) (ht : ¬ Completed (α.take t) x) : t < k := by
  by_contra hc
  exact ht (completed_take_mono (by omega) hk)

lemma lt_of_invoked_not {α : List (Lbl n)} {x : OpId (Fin n)} {k t : ℕ}
    (ht : Invoked (α.take t) x) (hk : ¬ Invoked (α.take k) x) : k < t := by
  by_contra hc
  exact hk (invoked_take_mono (by omega) ht)

/-- `Precedes` in terms of a split position. -/
lemma precedes_take {α : List (Lbl n)} {x y : OpId (Fin n)} (h : Precedes α y x) :
    ∃ k, Completed (α.take k) y ∧ ¬ Invoked (α.take k) x := by
  obtain ⟨β, γ, rfl, hc, hi⟩ := h
  exact ⟨β.length, by simpa using hc, by simpa using hi⟩

/-- The contribution of an operation with a certificate is below its view. -/
lemma contrib_le {α : List (Lbl n)} {y : OpId (Fin n)} {V : ℕ × ℕ}
    (hc : (opOf α y = some .scan → respOf α y = some V) ∧
      (∀ v, opOf α y = some (.upd0 v) → v ≤ V.1 ∧ respOf α y = some (0, 0)) ∧
      (∀ v, opOf α y = some (.upd1 v) → v ≤ V.2 ∧ respOf α y = some (0, 0))) :
    contribOf α y ≤ V := by
  obtain ⟨h1, h2, h3⟩ := hc
  unfold contribOf
  rcases ho : opOf α y with _ | o
  · exact Prod.mk_le_mk.2 ⟨Nat.zero_le _, Nat.zero_le _⟩
  · cases o with
    | upd0 v => exact Prod.mk_le_mk.2 ⟨by simpa using (h2 v ho).1, Nat.zero_le _⟩
    | upd1 v => exact Prod.mk_le_mk.2 ⟨Nat.zero_le _, by simpa using (h3 v ho).1⟩
    | scan => simp [h1 ho]

/-- **Theorem 3.7 (linearizability).** Algorithm 1 is a linearizable implementation of a
2-component max array (in every execution, with atomic base objects; no bounded-increment
hypothesis is needed for linearizability). -/
theorem alg1_linearizable : (alg1 n m X).Linearizable := by
  refine Impl.linearizable_of_run (fun α C hC => ?_)
  have hv : (alg1 n m X).Valid α := ⟨C, hC⟩
  obtain ⟨-, -, -, -, hcomp, -⟩ := inv_run hC
  refine exists_isLinearization_maxArr α (Impl.Valid.wellFormed (I := alg1 n m X) hv) ?_ ?_ ?_ ?_ ?_
  · intro x y r s hx hr hy hs
    obtain ⟨V, t0, t1, hc, -, -, hsc, -, -⟩ := hcomp x (completed_iff_respOf.2 (by simp [hr]))
    obtain ⟨V', t0', t1', hc', -, -, hsc', -, -⟩ :=
      hcomp y (completed_iff_respOf.2 (by simp [hs]))
    rw [hsc hx] at hr; rw [hsc' hy] at hs
    cases hr; cases hs
    rcases le_total t1 t1' with h | h
    · exact Or.inl (cert_le hv hc hc' h)
    · exact Or.inr (cert_le hv hc' hc h)
  · intro x r y hx hr hp
    obtain ⟨V, t0, t1, hc, hi, -, hsc, -, -⟩ := hcomp x (completed_iff_respOf.2 (by simp [hr]))
    obtain ⟨V', t0', t1', hc', -, hnc', hy⟩ := hcomp y hp.completed
    rw [hsc hx] at hr; cases hr
    obtain ⟨k, hk1, hk2⟩ := precedes_take hp
    have := lt_of_completed_not hk1 hnc'
    have := lt_of_invoked_not hi hk2
    exact (contrib_le hy).trans
      (cert_le hv hc' hc (by have := hc.1; omega))
  · intro x r hx hr hpos
    obtain ⟨V, t0, t1, hc, hi, hnc, hsc, -, -⟩ :=
      hcomp x (completed_iff_respOf.2 (by simp [hr]))
    rw [hsc hx] at hr; cases hr
    obtain ⟨t', ht', hLt'⟩ := hc.2.2.2.2.2.2.2.1
    have hlen : t' ≤ α.length := by have := hc.2.1; omega
    obtain ⟨-, -, -, ⟨hw, -⟩, -, -⟩ := inv_take (X := X) hv hlen
    obtain ⟨u, hu, hiu⟩ := hw (by rw [hLt']; exact hpos)
    have hu' : opOf α u = some (.upd0 r.1) := by
      rw [← hLt', ← hu, ← opOf_append_of_invoked (β := α.drop t') hiu, List.take_append_drop]
    refine ⟨u, hu', fun hxu => ?_, fun y hyu => ?_⟩
    · obtain ⟨k, hk1, hk2⟩ := precedes_take hxu
      have := lt_of_completed_not hk1 hnc
      have := lt_of_invoked_not hiu hk2
      omega
    · obtain ⟨V', t0', t1', hc', -, hnc', hy⟩ := hcomp y hyu.completed
      obtain ⟨k, hk1, hk2⟩ := precedes_take hyu
      have := lt_of_completed_not hk1 hnc'
      have := lt_of_invoked_not hiu hk2
      exact (contrib_le hy).trans (cert_le hv hc' hc (by omega))
  · intro x r hx hr hpos
    obtain ⟨V, t0, t1, hc, hi, hnc, hsc, -, -⟩ :=
      hcomp x (completed_iff_respOf.2 (by simp [hr]))
    rw [hsc hx] at hr; cases hr
    obtain ⟨t', ht', hRt'⟩ := hc.2.2.2.2.2.2.2.2
    have hlen : t' ≤ α.length := by have := hc.2.1; omega
    obtain ⟨-, -, -, ⟨-, hw⟩, -, -⟩ := inv_take (X := X) hv hlen
    obtain ⟨u, hu, hiu⟩ := hw (by rw [hRt']; exact hpos)
    have hu' : opOf α u = some (.upd1 r.2) := by
      rw [← hRt', ← hu, ← opOf_append_of_invoked (β := α.drop t') hiu, List.take_append_drop]
    refine ⟨u, hu', fun hxu => ?_, fun y hyu => ?_⟩
    · obtain ⟨k, hk1, hk2⟩ := precedes_take hxu
      have := lt_of_completed_not hk1 hnc
      have := lt_of_invoked_not hiu hk2
      omega
    · obtain ⟨V', t0', t1', hc', -, hnc', hy⟩ := hcomp y hyu.completed
      obtain ⟨k, hk1, hk2⟩ := precedes_take hyu
      have := lt_of_completed_not hk1 hnc'
      have := lt_of_invoked_not hiu hk2
      exact (contrib_le hy).trans (cert_le hv hc' hc (by omega))
  · intro x o r hx hr hne
    obtain ⟨V, t0, t1, hc, hi, hnc, -, h0, h1⟩ :=
      hcomp x (completed_iff_respOf.2 (by simp [hr]))
    cases o with
    | upd0 v => rw [(h0 v hx).2] at hr; exact (Option.some.inj hr).symm
    | upd1 v => rw [(h1 v hx).2] at hr; exact (Option.some.inj hr).symm
    | scan => exact absurd rfl hne

end Podc.LongLivedSnapshotsPolylog
