import Papers.PODC2024.RecoverableConsensus.Theorem13

/-!
# Corollaries and sanity checks for Ovens (PODC'24)

* `not_recording_of_commute`: a type whose operations pairwise commute or overwrite each other
  (from every value) is not `n`-recording; read/write-like objects (`ObjSpec.RWLike`) and
  readable test-and-set (`rtasObj`) are such types.
* `rw_not_recSolvable`: read/write objects alone cannot solve recoverable consensus among `n ≥ 2`
  processes (sanity check of Theorem 13).
* `tas_not_recSolvable`: **Golab's theorem** (SPAA'20, cited in the introduction): test-and-set
  objects (consensus number 2) together with registers cannot solve recoverable consensus among
  2 or more processes with individual crashes — here derived from Theorem 13.
* Remarks on the readability of `T_{n,n'}` (Section 4): `T_{n,n'}` is not readable for
  `n' + 1 < n`, but for `n' = n - 1` its operation `opR` is a read (it never changes the value
  and its response determines the value), see `readable_Tnn_pred`.
-/

namespace Cslib.SharedMemory.Recoverable.Ovens

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

/-- If any two operations applied from any value commute, or one overwrites the other, the type
is not `n`-recording. -/
theorem not_recording_of_commute {S : ObjSpec}
    (h : ∀ u a b, (S.δ (S.δ u a).1 b).1 = (S.δ u b).1 ∨ (S.δ (S.δ u b).1 a).1 = (S.δ u a).1 ∨
      (S.δ u a).1 = (S.δ u b).1) (n : ℕ) : ¬ IsRecording n S := by
  rintro ⟨u, team, o, ⟨p, hp⟩, ⟨q, hq⟩, hdis, -⟩
  have hpq : p ≠ q := by rintro rfl; simp_all
  rcases h u (o p) (o q) with h1 | h1 | h1
  · exact hdis p [q] q [] (by simp [hpq]) (by simp) hp hq (by simpa using h1)
  · exact hdis p [] q [p] (by simp) (by simp [hpq.symm]) hp hq (by simpa using h1.symm)
  · exact hdis p [] q [] (by simp) (by simp) hp hq (by simpa using h1)

/-- In a read/write-like object, any two operations commute or one overwrites the other. -/
lemma rwLike_commute {S : ObjSpec} (hS : S.RWLike) (u : S.State) (a b : S.Op) :
    (S.δ (S.δ u a).1 b).1 = (S.δ u b).1 ∨ (S.δ (S.δ u b).1 a).1 = (S.δ u a).1 ∨
      (S.δ u a).1 = (S.δ u b).1 := by
  rcases hS a with ha | ha
  · left; rw [ha]
  rcases hS b with hb | hb
  · right; left; rw [hb]
  · left; rw [hb (S.δ u a).1 u]

/-- Read/write objects are not `n`-recording. -/
theorem not_recording_of_rwLike {S : ObjSpec} (hS : S.RWLike) (n : ℕ) : ¬ IsRecording n S :=
  not_recording_of_commute (rwLike_commute hS) n

/-- Readable test&set (`rtasObj`: `tas` sets the bit and returns its old value, `read`) is not
`n`-recording. -/
theorem tas_not_recording (n : ℕ) : ¬ IsRecording n rtasObj := by
  refine not_recording_of_commute (fun u a b => ?_) n
  cases a <;> cases b <;> simp

/-- With only read/write objects, recoverable consensus among `n ≥ 2` processes is impossible. -/
theorem rw_not_recSolvable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} (hT : ∀ i, (T i).RWLike)
    {n : ℕ} (hn : 2 ≤ n) (A : Alg n T) : ¬ RecConsensus A := by
  intro hA
  obtain ⟨i, hi⟩ := theorem13 hn hA
  exact not_recording_of_rwLike (hT i) n hi

/-- **Golab (SPAA'20)**, derived from Theorem 13: test-and-set objects and registers cannot solve
recoverable consensus among `n ≥ 2` processes with individual crashes. -/
theorem tas_not_recSolvable {n : ℕ} (hn : 2 ≤ n) : ¬ RecSolvable rtasObj n := by
  rintro ⟨ιR, ιS, _, _, R, hR, A, hA⟩
  obtain ⟨i, hi⟩ := theorem13 hn hA
  rcases i with j | j
  · exact not_recording_of_rwLike (hR j) n hi
  · exact tas_not_recording n hi

/-! ## Readability of `T_{n,n'}` -/

/-- `T_{n,n'}` is not readable when `n' + 1 < n` (Section 4). -/
theorem not_readable_Tnn {n n' : ℕ} (h : n' + 1 < n) : ¬ (Tnn n n').Readable := by
  rintro ⟨o, hro, -⟩
  cases o with
  | op x =>
    have := hro .s
    simp [tδ, show 0 < n - 1 by omega] at this
  | opR =>
    have := hro (.sv true ⟨n', by omega⟩)
    simp [tδ] at this

/-- For `n' = n - 1` the operation `opR` of `T_{n,n'}` is a read (it never changes the value and
its response determines the value, `⊥` standing for `s⊥`); so the type of Section 4 is readable
in this sense when `n' = n - 1`, contrary to the paper's description of `T_{n,n'}` as
non-readable (literally, `opR` returns `⊥` instead of the value `s⊥`). -/
theorem readable_Tnn_pred {n : ℕ} : (Tnn n (n - 1)).Readable := by
  refine ⟨.opR, fun u => ?_, fun u t hst => ?_⟩
  · cases u with
    | s => rfl
    | bot => rfl
    | sv x i => simp [tδ, show i.val + 1 ≤ n - 1 by omega]
  · cases u <;> cases t <;>
      simp_all [tδ, show ∀ i : Fin (n - 1), i.val + 1 ≤ n - 1 from fun i => by omega]

end Cslib.SharedMemory.Recoverable.Ovens
