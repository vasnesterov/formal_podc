import Papers.PODC2010.MultiVersionSTM.SmallSnapshot

/-!
# Theorem 3 is false under the literal reading of Definition 4

Perelman–Fan–Keidar, PODC 2010, Theorem 3: "an MV-permissive STM satisfying UP GC cannot have
read-only transactions that leave no trace". With UP GC read literally as Definition 4
(`STM.UPGC`: a version is kept only if some extension of the execution has a live transaction that
can read it and cannot read any later version), the statement is false.

The counterexample is `snapSmall` (`SmallSnapshot.lean`): the eager snapshot STM, with the history
stored without the events of committed read-only transactions. It is valid (`snapSmall_valid`),
every solo read-only transaction leaves the shared memory unchanged (`snapSmall_noTrace`), and it
satisfies the literal UP GC (`snapSmall_upgc`): every kept version is the snapshot version of a
live read-only transaction, or the latest version, which a fresh read-only transaction on a fresh
thread would read. In the extension in which that transaction reads the version, it cannot read
any later version, because it has already read this one.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

/-- Fresh read-only transactions on fresh threads always exist: for every finite set `s` of
transactions there is a read-only transaction outside `s` whose thread runs no transaction of
`s`. -/
def FreshRO (Tx P : Type) [TxSys Tx P] : Prop :=
  ∀ s : Finset Tx, ∃ T, ro T = true ∧ T ∉ s ∧ ∀ T' ∈ s, thr T' ≠ thr T

variable {Tx O P : Type} [TxSys Tx P]

/-- **`snapSmall` satisfies UP GC in the literal reading of Definition 4.** A kept version is the
snapshot version of a live read-only transaction `T` (which has begun), or the latest version
(read by a fresh read-only transaction `T` on a fresh thread). In the extension in which `T`
reads it, `T` is live, can read it, and cannot read any later version. -/
theorem snapSmall_upgc (hfresh : FreshRO Tx P) :
    (snapSmall (Tx := Tx) (O := O) (P := P)).UPGC keptSmall := by
  intro σ v hw hv
  obtain ⟨hh, hm⟩ := snapSmall_sim σ hw
  change v ∈ snapKept false (((snapSmall (P := P)).conf σ).mem ()) at hv
  rw [hm, snapKept_erase hw] at hv
  have hg : Gen false ((snapSmall (P := P)).hist σ) := hh ▸ gen_hist false σ
  generalize hhd : (snapSmall (Tx := Tx) (O := O) (P := P)).hist σ = h at hw hv hg hm
  -- the reader `T`
  obtain ⟨T, hro, hok, hx⟩ : ∃ T, ro T = true ∧ OKNext h (.read T v.1) ∧
      v.2 = latest (h.take (firstIdx h T)) v.1 := by
    have hin : ∀ T', Began h T' → T' ∈ (h.map (fun e => e.inv.tx)).toFinset :=
      fun T' ⟨e, he, heT⟩ => List.mem_toFinset.2 (List.mem_map.2 ⟨e, he, heT⟩)
    have fresh : v.2 = latest h v.1 → ∃ T, ro T = true ∧ OKNext h (.read T v.1) ∧
        v.2 = latest (h.take (firstIdx h T)) v.1 := by
      intro hl
      obtain ⟨T, hro, hTs, hthr⟩ := hfresh (h.map (fun e => e.inv.tx)).toFinset
      have hnb : ¬ Began h T := fun hb => hTs (hin T hb)
      refine ⟨T, hro, ⟨fun ht => hnb ht.began, ?_,
        fun _ T' _ hthr' hb => absurd hthr' (hthr T' (hin T' hb))⟩, ?_⟩
      · intro _ _ hi; cases hi
      · rw [firstIdx_eq_length hnb, List.take_length]; exact hl
    rcases mem_snapKept.1 hv with hl | ⟨T, hro, hnt, hx⟩
    · exact fresh hl
    · by_cases hb : Began h T
      · refine ⟨T, hro, ⟨hnt, ?_, fun hnb => absurd hb hnb⟩, by rwa [snap_false] at hx⟩
        intro _ _ hi; cases hi
      · apply fresh
        rwa [snap_false, firstIdx_eq_length hb, List.take_length] at hx
  -- the extension: `T` reads `v`
  refine ⟨[.read T v.1], T, ?_⟩
  have hhist : (snapSmall (P := P)).hist (σ ++ [.read T v.1]) = h ++ [⟨.read T v.1, some v.2⟩] := by
    rw [STM.hist_snoc, snapSmall_resp, hm, snapResp_erase hw hok, snapResp_read_ro hro, ← hx, hhd]
  rw [hhist]
  exact upgc_read hw hg hro hok hx

/-- **Theorem 3 of [Perelman–Fan–Keidar, PODC 2010] is false under the literal reading of
Definition 4** (`STM.UPGC`). Theorem 3 claims that an MV-permissive STM satisfying UP GC cannot
make read-only transactions invisible: a solo read-only transaction must change the configuration
external to it. Here, assuming only that fresh read-only transactions on fresh threads exist
(`FreshRO`), we exhibit a valid STM (strictly serializable, MV-permissive, reads return written
and kept versions, garbage collection is final) that satisfies Definition 4 literally and in which
*every* solo read-only transaction leaves the configuration external to it unchanged
(`STM.NoTrace`). This refutes both the paper's universal phrasing ("every solo read-only
transaction changes the external configuration") and the existential one proved in
`theorem_3` (under the potential-reader reading of UP GC). The STM is `snapSmall`, the eager
snapshot STM whose read-only transactions erase themselves from the shared memory at commit. -/
theorem theorem_3_false (hfresh : FreshRO Tx P) :
    ∃ (X : STM Tx O P) (kept : Config X → Set (Version Tx O)),
      X.Valid kept ∧ X.UPGC kept ∧ X.NoTrace :=
  ⟨snapSmall, keptSmall, snapSmall_valid, snapSmall_upgc hfresh, snapSmall_noTrace⟩

/-! ### Non-vacuity of `FreshRO` -/

/-- A concrete transaction system: transactions are natural numbers, transaction `n` runs on
thread `n`, and the even ones are read-only. -/
@[instance_reducible] def natTxSys : TxSys ℕ ℕ := ⟨fun T => T % 2 == 0, id⟩

/-- `natTxSys` has fresh read-only transactions on fresh threads. -/
theorem freshRO_natTxSys : @FreshRO ℕ ℕ natTxSys := by
  intro s
  refine ⟨2 * (s.sup id + 1), ?_, fun hm => ?_, fun T' hT' heq => ?_⟩
  · show (2 * (s.sup id + 1)) % 2 == 0
    simp
  · have := Finset.le_sup (f := id) hm
    simp only [id] at this
    omega
  · have := Finset.le_sup (f := id) hT'
    change T' = 2 * (s.sup id + 1) at heq
    simp only [id] at this
    omega

/-- Non-vacuity: `theorem_3_false` applies to `natTxSys` (with any type of objects). -/
example (O : Type) :
    letI := natTxSys
    ∃ (X : STM ℕ O ℕ) (kept : Config X → Set (Version ℕ O)),
      X.Valid kept ∧ X.UPGC kept ∧ X.NoTrace :=
  @theorem_3_false ℕ O ℕ natTxSys freshRO_natTxSys

end Podc.MultiVersionSTM
