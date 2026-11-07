import Papers.PODC2010.MultiVersionSTM.Scenario1

/-!
# Theorem 1: versions any MV-permissive STM must keep

For an arbitrary valid STM `X` (correct, MV-permissive, reads return written versions, with a
kept-version set satisfying `KeepsReads` and `GCFinal`):

* at `t₀` (end of `σH`) and at `t₁` (end of `σH1`), `X` keeps the initial versions that `T₁`
  may still read (`t0_keeps_initial`);
* if `X` does not keep `o₃¹` at `t₀`, then at `t₁` it keeps `o₄¹` and `o₅¹`, the versions of
  `T₄` that `T₃` must read (`t1_keeps_T4`).
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P] {t : Fin 5 → Tx} {ob : Fin 5 → O}

namespace Setup1

variable (S : Setup1 t ob)
include S

/-- The suffix of `σH1` after `σH`: `T₅` writes `o₁, o₄, o₅` and commits. -/
def τ5 (t : Fin 5 → Tx) (ob : Fin 5 → O) : List (Inv Tx O) :=
  [.write (t 4) (ob 0), .write (t 4) (ob 3), .write (t 4) (ob 4), .commit (t 4)]

lemma σH1_eq : σH1 t ob = σH t ob ++ τ5 t ob := rfl

/-- In any serialization of a good extension of `σH` in which `T₁` commits, `T₁` precedes `T₂`
and `T₄` (it read `o₂⁰` and `o₄⁰`). -/
lemma pos_T1 (X : STM Tx O P) (hm : X.MVPermissive) (hr : X.ReadsWrittenOnly)
    (τ : List (Inv Tx O)) (hs : AllSucc (X.hist (σH t ob ++ τ)))
    (h0 : Inv.commit (t 0) ∈ τ) (pos : Tx → ℕ) (hw : SerWitness (X.hist (σH t ob ++ τ)) pos) :
    pos (t 0) < pos (t 1) ∧ pos (t 0) < pos (t 3) := by
  have e := S.t_eq; have eo := S.ob_eq
  obtain ⟨rd0, rd1, -, -⟩ := S.reads X hm hr
  have hc0 : Committed (X.hist (σH t ob ++ τ)) (t 0) := by
    rw [X.committed_hist_iff hs]; simp [h0]
  constructor
  · obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σH t ob ++ τ) (σ₁ := [])
      (i := .read (t 0) (ob 1)) (σ₂ := (σH t ob).tail ++ τ) (by simp [σH])
    rw [rd0] at hh
    have := hw.ext hc0 hh (by simp)
    exact this (t 1) ((X.cwriter_hist_iff hs).2 (by simp [σH])) (by simp [e])
  · obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σH t ob ++ τ) (σ₁ := [.read (t 0) (ob 1)])
      (i := .read (t 0) (ob 3)) (σ₂ := ((σH t ob).drop 2) ++ τ) (by simp [σH])
    rw [rd1] at hh
    have := hw.ext hc0 hh (by simp [X.writes_hist_iff])
    exact this (t 3) ((X.cwriter_hist_iff hs).2 (by simp [σH])) (by simp [e])

lemma good_base (X : STM Tx O P) (hm : X.MVPermissive) (τ : List (Inv Tx O))
    (hτ : τ = [] ∨ τ = τ5 t ob) : X.Good (σH t ob ++ τ) := by
  rcases hτ with rfl | rfl
  · simpa using S.good_σH X hm
  · exact S.good_σH1 X hm

lemma tx_mem (τ : List (Inv Tx O)) (hτ : τ = [] ∨ τ = τ5 t ob) :
    ∀ j ∈ σH t ob ++ τ, ∃ a, Inv.tx j = t a := by
  rcases hτ with rfl | rfl <;> intro j hj <;> simp [σH, τ5] at hj <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- `T₁` reads `oₖ` and commits after `σH ++ τ`: the read returns the initial version, so this
version is kept (Theorem 1, the versions `T₁` may read). -/
lemma t1_keeps_initial (X : STM Tx O P) (kept : Config X → Set (Version Tx O)) (hv : X.Valid kept)
    (τ : List (Inv Tx O)) (hτ : τ = [] ∨ τ = τ5 t ob) (k : Fin 5) :
    (ob k, none) ∈ kept (X.conf (σH t ob ++ τ)) := by
  have e := S.t_eq; have eo := S.ob_eq
  have hm := hv.mvPermissive; have hr := hv.readsWritten
  set σ := σH t ob ++ τ with hσ
  have hg := S.good_base X hm τ hτ
  have hnc : Inv.commit (t 0) ∉ σ := by
    rcases hτ with rfl | rfl <;> simp [hσ, σH, τ5, e]
  have hg1 : X.Good (σ ++ [.read (t 0) (ob k)]) := by
    refine X.good_snoc_ro hm hg ⟨by simpa using hnc, by simp, ?_⟩ (by simpa using S.r0)
    exact okNextS_thr t S.hthr _ _ (S.tx_mem τ hτ) ⟨0, rfl⟩
  have hg2 : X.Good (σ ++ [.read (t 0) (ob k), .commit (t 0)]) := by
    have := X.good_snoc_ro hm hg1 (i := .commit (t 0)) ⟨by simpa using hnc, by simp, ?_⟩
      (by simpa using S.r0)
    · simpa using this
    · refine okNextS_thr t S.hthr _ _ ?_ ⟨0, rfl⟩
      intro j hj; simp only [List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact S.tx_mem τ hτ j hj
      · exact ⟨0, rfl⟩
  obtain ⟨v, hv1⟩ := X.resp_some_of_good hg1
  obtain ⟨pos, hw⟩ := hv.correct _ hg2.1
  have hs := hg2.2
  have hc0 : Committed (X.hist (σ ++ [.read (t 0) (ob k), .commit (t 0)])) (t 0) := by
    rw [X.committed_hist_iff hs]; simp
  obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σ ++ [.read (t 0) (ob k), .commit (t 0)]) (σ₁ := σ)
    (i := .read (t 0) (ob k)) (σ₂ := [.commit (t 0)]) rfl
  rw [hv1] at hh
  have hnw : ¬ Writes (X.hist σ) (t 0) (ob k) := by
    rw [X.writes_hist_iff]; rcases hτ with rfl | rfl <;> simp [hσ, σH, τ5, e]
  have hl := hw.ext hc0 hh hnw
  have hp := S.pos_T1 X hm hr (τ ++ [.read (t 0) (ob k), .commit (t 0)]) (by simpa [hσ] using hs)
    (by simp) pos (by simpa [hσ] using hw)
  have hkeep := hv.keepsReads σ (t 0) (ob k) v hg1.1 hv1 hnw
  cases v with
  | none => exact hkeep
  | some W =>
    exfalso
    obtain ⟨-, hW, hWlt, -⟩ := hl
    have hWw := ((X.cwriter_hist_iff hs).1 hW).2
    have hW' : W = t 1 ∨ W = t 3 ∨ (τ = τ5 t ob ∧ W = t 4) := by
      rcases hτ with rfl | rfl <;> simp [hσ, σH, τ5] at hWw
      · rcases hWw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
      · rcases hWw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
          ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    rcases hW' with rfl | rfl | ⟨rfl, rfl⟩
    · omega
    · omega
    · have hs' : AllSucc (X.hist (σH t ob ++ (τ5 t ob ++ [.read (t 0) (ob k), .commit (t 0)]))) := by
        simpa [hσ] using hs
      have hw' : SerWitness (X.hist (σH t ob ++ (τ5 t ob ++ [.read (t 0) (ob k), .commit (t 0)])))
          pos := by simpa [hσ] using hw
      have h34 := X.rt_hist _ _ hs' (A := t 3) (B := t 4) (by simp [σH]) (by simp [σH, e])
        (by simp [τ5])
      have := hw'.lt_of_rt ((X.committed_hist_iff hs').2 (by simp [σH]))
        ((X.committed_hist_iff hs').2 (by simp [τ5])) h34
      omega

lemma tx_mem1 : ∀ j ∈ σH1 t ob, ∃ a, Inv.tx j = t a := S.tx_mem (τ5 t ob) (Or.inr rfl)

/-- Case 2 of the proof of Theorem 1: if `o₃¹` (the version of `o₃` written by `T₂`) is not kept
at `t₀`, then at `t₁` the versions `o₄¹, o₅¹` written by `T₄` are kept, since `T₃` must read
`o₃²` and hence `o₄¹, o₅¹`. -/
lemma t1_keeps_T4 (X : STM Tx O P) (kept : Config X → Set (Version Tx O)) (hv : X.Valid kept)
    (hno : (ob 2, some (t 1)) ∉ kept (X.conf (σH t ob))) (m : Fin 5) (hm3 : m = 3 ∨ m = 4) :
    (ob m, some (t 3)) ∈ kept (X.conf (σH1 t ob)) := by
  have e := S.t_eq; have eo := S.ob_eq
  have hm := hv.mvPermissive; have hr := hv.readsWritten
  have r2 := S.r2
  obtain ⟨-, -, -, rd6⟩ := S.reads X hm hr
  have hg := S.good_σH1 X hm
  have hnc : Inv.commit (t 2) ∉ σH1 t ob := by simp [σH1, σH, e]
  have throk : ∀ τ : List (Inv Tx O), (∀ j ∈ τ, Inv.tx j = t 2) → ∀ j ∈ σH1 t ob ++ τ, ∃ a, Inv.tx j = t a := by
    intro τ hτ j hj
    rcases List.mem_append.1 hj with hj | hj
    · exact S.tx_mem1 j hj
    · exact ⟨2, hτ j hj⟩
  have hg1 : X.Good (σH1 t ob ++ [.read (t 2) (ob 2)]) :=
    X.good_snoc_ro hm hg ⟨by simpa using hnc, by simp,
      okNextS_thr t S.hthr _ _ S.tx_mem1 ⟨2, rfl⟩⟩ (by simpa using r2)
  have hg2 : X.Good (σH1 t ob ++ [.read (t 2) (ob 2), .read (t 2) (ob m)]) := by
    have := X.good_snoc_ro hm hg1 (i := .read (t 2) (ob m)) ⟨by simpa using hnc, by simp,
      okNextS_thr t S.hthr _ _ (throk _ (by simp)) ⟨2, rfl⟩⟩ (by simpa using r2)
    simpa using this
  have hg3 : X.Good (σH1 t ob ++ [.read (t 2) (ob 2), .read (t 2) (ob m), .commit (t 2)]) := by
    have := X.good_snoc_ro hm hg2 (i := .commit (t 2)) ⟨by simpa using hnc, by simp,
      okNextS_thr t S.hthr _ _ (throk _ (by simp)) ⟨2, rfl⟩⟩ (by simpa using r2)
    simpa using this
  obtain ⟨a, ha⟩ := X.resp_some_of_good hg1
  obtain ⟨b, hb⟩ := X.resp_some_of_good (σ := σH1 t ob ++ [.read (t 2) (ob 2)]) (by simpa using hg2)
  set σ := σH1 t ob ++ [.read (t 2) (ob 2), .read (t 2) (ob m), .commit (t 2)] with hσ
  obtain ⟨pos, hw⟩ := hv.correct _ hg3.1
  have hs := hg3.2
  have cm : ∀ T, Inv.commit T ∈ σ → Committed (X.hist σ) T := fun T h => (X.committed_hist_iff hs).2 h
  have cw : ∀ W o, Inv.commit W ∈ σ → Inv.write W o ∈ σ → CWriter (X.hist σ) o W :=
    fun W o h1 h2 => (X.cwriter_hist_iff hs).2 ⟨h1, h2⟩
  have hc2 : Committed (X.hist σ) (t 2) := cm _ (by simp [hσ])
  -- real-time order
  have rt12 : pos (t 1) < pos (t 2) :=
    hw.lt_split X hs (List.take 6 (σH1 t ob))
      ((List.drop 6 (σH1 t ob)) ++ [.read (t 2) (ob 2), .read (t 2) (ob m), .commit (t 2)])
      (by simp [hσ, σH1, σH]) (by simp [σH1, σH]) (by simp [σH1, σH, e]) (by simp [σH1, σH]) (by simp)
  have rt34 : pos (t 3) < pos (t 4) :=
    hw.lt_split X hs (σH t ob)
      (τ5 t ob ++ [.read (t 2) (ob 2), .read (t 2) (ob m), .commit (t 2)])
      (by simp [hσ, σH1, τ5]) (by simp [σH]) (by simp [σH, e]) (by simp [τ5]) (by simp [τ5])
  -- `T₃` read `o₁⁰`, and `T₅` overwrote it
  have h24 : pos (t 2) < pos (t 4) := by
    obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σ)
      (σ₁ := [.read (t 0) (ob 1), .read (t 0) (ob 3), .read (t 0) (ob 4),
        .write (t 1) (ob 1), .write (t 1) (ob 2), .commit (t 1)])
      (i := .read (t 2) (ob 0)) (σ₂ := (σH1 t ob).drop 7 ++ [.read (t 2) (ob 2), .read (t 2) (ob m), .commit (t 2)])
      (by simp [hσ, σH1, σH])
    rw [rd6] at hh
    exact hw.ext hc2 hh (by simp [X.writes_hist_iff, e]) (t 4)
      (cw _ _ (by simp [hσ, σH1, σH]) (by simp [hσ, σH1, σH, τ5])) (by simp [e])
  -- the read of `o₃` returns `o₃²`
  have hnw2 : ¬ Writes (X.hist (σH1 t ob)) (t 2) (ob 2) := by simp [X.writes_hist_iff, σH1, σH, e]
  obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σ) (σ₁ := σH1 t ob) (i := .read (t 2) (ob 2))
    (σ₂ := [.read (t 2) (ob m), .commit (t 2)]) (by simp [hσ])
  rw [ha] at hh
  have hla := hw.ext hc2 hh hnw2
  have h32 : pos (t 3) < pos (t 2) := by
    cases a with
    | none =>
      have := hla (t 1) (cw _ _ (by simp [hσ, σH1, σH]) (by simp [hσ, σH1, σH])) (by simp [e])
      omega
    | some W =>
      obtain ⟨-, hW, hWlt, -⟩ := hla
      have hWw := ((X.cwriter_hist_iff hs).1 hW).2
      have : W = t 1 ∨ W = t 3 := by
        simp [hσ, σH1, σH, τ5, eo] at hWw
        exact hWw
      rcases this with rfl | rfl
      · exfalso
        have hk := hv.keepsReads (σH1 t ob) (t 2) (ob 2) (some (t 1)) hg1.1 ha hnw2
        have hg' : WF (X.hist (σH t ob ++ τ5 t ob)) := by rw [← S.σH1_eq]; exact hg.1
        have hk' : (ob 2, some (t 1)) ∈ kept (X.conf (σH t ob ++ τ5 t ob)) := by
          rw [← S.σH1_eq]; exact hk
        refine hv.gcFinal (σH t ob) (τ5 t ob) (ob 2, some (t 1)) hg' ?_ hno hk'
        exact (X.cwriter_hist_iff (S.good_σH X hm).2).2 (by simp [σH])
      · exact hWlt
  -- the read of `oₘ` returns `T₄`'s version
  have hnwm : ¬ Writes (X.hist (σH1 t ob ++ [.read (t 2) (ob 2)])) (t 2) (ob m) := by
    simp [X.writes_hist_iff, σH1, σH, e]
  obtain ⟨h₂', hh'⟩ := X.hist_decomp' (σ := σ) (σ₁ := σH1 t ob ++ [.read (t 2) (ob 2)])
    (i := .read (t 2) (ob m)) (σ₂ := [.commit (t 2)]) (by simp [hσ])
  rw [hb] at hh'
  have hlb := hw.ext hc2 hh' hnwm
  have hbt : b = some (t 3) := by
    cases b with
    | none =>
      have := hlb (t 3) (cw _ _ (by simp [hσ, σH1, σH])
        (by rcases hm3 with rfl | rfl <;> simp [hσ, σH1, σH])) (by simp [e])
      omega
    | some W =>
      obtain ⟨-, hW, hWlt, -⟩ := hlb
      have hWw := ((X.cwriter_hist_iff hs).1 hW).2
      have : W = t 3 ∨ W = t 4 := by
        rcases hm3 with rfl | rfl <;> simp [hσ, σH1, σH, τ5, eo] at hWw <;> exact hWw
      rcases this with rfl | rfl
      · rfl
      · omega
  subst hbt
  have hwf2 : WF (X.hist ((σH1 t ob ++ [.read (t 2) (ob 2)]) ++ [.read (t 2) (ob m)])) := by
    simpa using hg2.1
  have hk : (ob m, some (t 3)) ∈ kept (X.conf (σH1 t ob ++ [.read (t 2) (ob 2)])) := by
    clear hh hh' hlb hla
    exact hv.keepsReads _ _ _ _ hwf2 hb hnwm
  clear hh hh' hlb hla
  by_contra hnot
  refine hv.gcFinal (σH1 t ob) [.read (t 2) (ob 2)] (ob m, some (t 3)) hg1.1 ?_ hnot hk
  show CWriter _ _ _
  rw [X.cwriter_hist_iff hg.2]
  have h3 : Inv.write (t 3) (ob m) ∈ σH1 t ob := by rcases hm3 with h | h <;> simp [h, σH1, σH]
  exact ⟨by simp [σH1, σH], h3⟩

end Setup1

end Podc.MultiVersionSTM
