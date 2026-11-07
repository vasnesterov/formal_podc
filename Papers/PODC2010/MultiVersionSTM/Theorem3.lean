import Papers.PODC2010.MultiVersionSTM.Scenario3
import Papers.PODC2010.MultiVersionSTM.Commute

/-!
# Theorem 3 (repaired): MV-permissiveness and UP GC force read-only transactions to leave a trace

Perelman–Fan–Keidar, PODC 2010, Section 6.2, with UP GC read as in Section 7: an overwritten
version is kept only if some live transaction precedes the transaction that overwrote it
(`STM.UPGCPrec`). The proof follows the paper, with the comparison made between `H₂` and `H₂`
without `T₂` (the paper compares `H₂` with `H₁`, which differs from `H₂` in more than `T₂`):

* in `H₂` without `T₂`, after `T₃` commits, no live transaction precedes `T₃`, so `o₂¹` is not
  kept and `T₄`'s read of `o₂` returns `o₂²`;
* if `T₂` leaves no trace, `T₄` cannot distinguish `H₂` from `H₂` without `T₂`, so it reads `o₂²`
  in `H₂` too, and `H₂` with `T₄` committing is not strictly serializable.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P]

namespace STM

variable (X : STM Tx O P)

/-- Steps of threads other than `p` from configurations that agree outside `p` are the same. -/
lemma run_eq_of_extEq {p : P} {C₁ C₂ : Config X} (hE : X.ExtEq p C₁ C₂) (τ : List (Inv Tx O))
    (hτ : ∀ i ∈ τ, thr i.tx ≠ p) : (X.run C₂ τ).2 = (X.run C₁ τ).2 :=
  (X.run_congr τ (fun i hi => (hE.2 _ (hτ i hi)).symm) (fun a _ => by rw [hE.1])).1

lemma resp_append (σ τ : List (Inv Tx O)) (i : Inv Tx O) :
    X.resp (σ ++ τ) i = (X.step (X.run (X.conf σ) τ).1 i).2.1 := by
  rw [resp, conf_append]

lemma step_resp_eq_of_run {C₁ C₂ : Config X} {τ : List (Inv Tx O)} {i : Inv Tx O}
    (h : (X.run C₂ (τ ++ [i])).2 = (X.run C₁ (τ ++ [i])).2) :
    (X.step (X.run C₂ τ).1 i).2.1 = (X.step (X.run C₁ τ).1 i).2.1 := by
  rw [run_snoc, run_snoc] at h
  have := congrArg List.getLast? h
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
    Prod.mk.injEq, Event.mk.injEq, true_and] at this
  exact this.1

end STM

end Podc.MultiVersionSTM

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P] {t : Fin 5 → Tx} {ob : Fin 2 → O}

/-- `H₂` without `T₂`, up to the commit of `T₃`. -/
def σA (t : Fin 5 → Tx) (ob : Fin 2 → O) : List (Inv Tx O) := σpre t ob ++ σpost t ob

namespace Setup3

variable (S : Setup3 t ob)
include S

lemma goodA (X : STM Tx O P) (hm : X.MVPermissive) : X.Good (σA t ob) := by
  have := S.good3' X hm 9 (by omega)
  simpa [σ3', σA, σpre, σpost, σend] using this

/-- The reads of `σA`. -/
lemma readsA (X : STM Tx O P) (hm : X.MVPermissive) (hr : X.ReadsWrittenOnly) :
    X.resp [.write (t 0) (ob 1), .commit (t 0)] (.read (t 3) (ob 0)) = some none ∧
    X.resp [.write (t 0) (ob 1), .commit (t 0), .read (t 3) (ob 0)] (.read (t 4) (ob 0)) =
      some none ∧
    ∃ v, X.resp [.write (t 0) (ob 1), .commit (t 0), .read (t 3) (ob 0), .read (t 4) (ob 0)]
      (.read (t 2) (ob 1)) = some v ∧ (v = none ∨ v = some (t 0)) := by
  have eo := S.ob_eq; have e := S.t_eq
  refine ⟨X.read_none hr ?_ ?_, X.read_none hr ?_ ?_, ?_⟩
  · simpa [σ3', σpre, σpost, σend] using S.good3' X hm 3 (by omega)
  · simp [eo]
  · simpa [σ3', σpre, σpost, σend] using S.good3' X hm 4 (by omega)
  · simp [eo]
  · have hg : X.Good ([.write (t 0) (ob 1), .commit (t 0), .read (t 3) (ob 0), .read (t 4) (ob 0)] ++
        [.read (t 2) (ob 1)]) := by
      simpa [σ3', σpre, σpost, σend] using S.good3' X hm 5 (by omega)
    obtain ⟨v, hv⟩ := X.resp_some_of_good hg
    refine ⟨v, hv, ?_⟩
    cases v with
    | none => exact Or.inl rfl
    | some W =>
      right
      have := hr _ hg.1 _ (t 2) (ob 1) W [] (by rw [STM.hist_snoc, hv])
      rw [X.writes_hist_iff] at this
      simp [eo] at this
      rw [this]

lemma histA (X : STM Tx O P) (hm : X.MVPermissive) (hr : X.ReadsWrittenOnly) :
    ∃ v r0 r1 r5 r6 r7 r8, (v = none ∨ v = some (t 0)) ∧ X.hist (σA t ob) =
      [⟨.write (t 0) (ob 1), r0⟩, ⟨.commit (t 0), r1⟩, ⟨.read (t 3) (ob 0), some none⟩,
       ⟨.read (t 4) (ob 0), some none⟩, ⟨.read (t 2) (ob 1), some v⟩, ⟨.write (t 4) (ob 0), r5⟩,
       ⟨.commit (t 4), r6⟩, ⟨.write (t 2) (ob 1), r7⟩, ⟨.commit (t 2), r8⟩] := by
  obtain ⟨rd2, rd3, v, hv, hv'⟩ := S.readsA X hm hr
  rw [X.hist_eq_histFrom]
  simp only [σA, σpre, σpost, List.cons_append, List.nil_append, STM.histFrom]
  simp only [List.cons_append, List.nil_append, rd2, rd3, hv]
  exact ⟨v, _, _, _, _, _, _, hv', rfl⟩

/-- In `H₂` without `T₂`, every transaction that `T₄` precedes is `T₅`. -/
lemma prec_T4 (X : STM Tx O P) (hm : X.MVPermissive) (hr : X.ReadsWrittenOnly) (B : Tx)
    (hp : Prec (X.hist (σA t ob)) (t 3) B) : B = t 4 := by
  have e := S.t_eq; have eo := S.ob_eq
  have hs := (S.goodA X hm).2
  obtain ⟨v, r0, r1, r5, r6, r7, r8, hv, hH⟩ := S.histA X hm hr
  have hcw : ∀ o W, CWriter (X.hist (σA t ob)) o W → (W = t 4 ∧ o = ob 0) ∨ (W = t 0 ∧ o = ob 1) ∨
      (W = t 2 ∧ o = ob 1) := by
    intro o W h
    rw [X.cwriter_hist_iff hs] at h
    simp [σA, σpre, σpost, e] at h
    obtain ⟨h1, h2⟩ := h
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hread : ∀ B o r, (⟨.read B o, some r⟩ : Event Tx O) ∈ X.hist (σA t ob) →
      (B = t 3 ∧ o = ob 0 ∧ r = none) ∨ (B = t 4 ∧ o = ob 0 ∧ r = none) ∨
      (B = t 2 ∧ o = ob 1 ∧ r = v) := by
    intro B o r h
    rw [hH] at h
    simp at h
    tauto
  -- edges out of `T₄` (`t 3`) and `T₅` (`t 4`)
  have hnext0 : ∀ B, NextWriter (X.hist (σA t ob)) (ob 0) none B → B = t 4 := by
    rintro B ⟨⟨-, W', hW', hcw', -⟩, -⟩
    cases hW'
    rcases hcw _ _ hcw' with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · rfl
    · exact absurd h (by simp [eo])
    · exact absurd h (by simp [eo])
  have hnc3 : ¬ Committed (X.hist (σA t ob)) (t 3) := by
    rw [X.committed_hist_iff hs]; simp [σA, σpre, σpost, e]
  have edge3 : ∀ B, PrecEdge (X.hist (σA t ob)) (t 3) B → B = t 4 := by
    intro B h
    rcases h with ⟨-, h₁, h₂, heq, hc, -⟩ | ⟨-, o, hrd⟩ | ⟨o, hc, -⟩ | ⟨-, o, v', hrd, hn⟩
    · exact absurd (by rw [heq]; exact hc.mono h₂) hnc3
    · rcases hread _ _ _ hrd with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
      · cases h
      · cases h
      · rcases hv with rfl | rfl
        · cases h
        · exact absurd (Option.some.inj h) (by simp [e])
    · exact absurd hc.1 hnc3
    · rcases hread _ _ _ hrd with ⟨-, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact hnext0 B hn
      · exact absurd h (by simp [e])
      · exact absurd h (by simp [e])
  have edge4 : ∀ B, ¬ PrecEdge (X.hist (σA t ob)) (t 4) B := by
    intro B h
    rcases h with ⟨hb, h₁, h₂, heq, hc, hnb⟩ | ⟨-, o, hrd⟩ | ⟨o, hc4, hcB, hbef⟩ | ⟨hne, o, v', hrd, hn⟩
    · -- `T₅` commits after every transaction of `σA` has begun
      have hmap := congrArg (List.map Event.inv) heq
      rw [X.map_inv_hist, List.map_append] at hmap
      have hpre : h₁.map Event.inv = (σA t ob).take h₁.length := by
        rw [hmap]; simp
      have hc' : Inv.commit (t 4) ∈ h₁.map Event.inv := by
        obtain ⟨r, hr⟩ := hc; exact List.mem_map.2 ⟨_, hr, rfl⟩
      rw [X.began_hist_iff] at hb
      rw [began_iff_map] at hnb
      obtain ⟨j, hj, rfl⟩ := hb
      have hlen : h₁.length ≤ 9 := by
        have := congrArg List.length hmap
        simp only [List.length_append, List.length_map] at this
        simp [σA, σpre, σpost] at this; omega
      rw [hpre] at hc' hnb
      generalize h₁.length = n at hc' hnb hlen
      apply hnb
      simp [σA, σpre, σpost] at hj
      interval_cases n <;> simp [σA, σpre, σpost, e] at hc' ⊢ <;>
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rcases hread _ _ _ hrd with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
      · cases h
      · cases h
      · rcases hv with rfl | rfl
        · cases h
        · exact absurd (Option.some.inj h) (by simp [e])
    · rcases hcw _ _ hc4 with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · rcases hcw _ _ hcB with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · obtain ⟨h₁, h₂, -, hc1, hc2⟩ := hbef; exact hc2 hc1
        · exact absurd h (by simp [eo])
        · exact absurd h (by simp [eo])
      · exact absurd h (by simp [e])
      · exact absurd h (by simp [e])
    · rcases hread _ _ _ hrd with ⟨h, -⟩ | ⟨-, rfl, rfl⟩ | ⟨h, -⟩
      · exact absurd h (by simp [e])
      · exact hne (hnext0 B hn).symm
      · exact absurd h (by simp [e])
  induction hp with
  | single h => exact edge3 _ h
  | tail _ h ih => subst ih; exact absurd h (edge4 _)

/-- In `H₂` without `T₂`, `T₄`'s read of `o₂` returns `o₂²`, the version of `T₃`: `o₂¹` is not
kept, since no live transaction precedes `T₃` (UP GC, potential-reader reading). -/
lemma read_T4_A (X : STM Tx O P) (kept : Config X → Set (Version Tx O)) (hc : X.Correct)
    (hm : X.MVPermissive) (hr : X.ReadsWrittenOnly) (hk : X.KeepsReads kept)
    (hu : X.UPGCPrec kept) : X.resp (σA t ob) (.read (t 3) (ob 1)) = some (some (t 2)) := by
  have e := S.t_eq; have eo := S.ob_eq
  have hgA := S.goodA X hm
  have hg10 : X.Good (σA t ob ++ [.read (t 3) (ob 1)]) := by
    simpa [σ3', σA, σpre, σpost, σend] using S.good3' X hm 10 (by omega)
  have hg11 : X.Good (σA t ob ++ [.read (t 3) (ob 1), .commit (t 3)]) := by
    simpa [σ3', σA, σpre, σpost, σend] using S.good3' X hm 11 (by omega)
  obtain ⟨w, hw⟩ := X.resp_some_of_good hg10
  rw [hw]
  have hnw : ¬ Writes (X.hist (σA t ob)) (t 3) (ob 1) := by
    rw [X.writes_hist_iff]; simp [σA, σpre, σpost, e]
  cases w with
  | none =>
    exfalso
    obtain ⟨pos, hpos⟩ := hc _ hg11.1
    have hs := hg11.2
    obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σA t ob ++ [.read (t 3) (ob 1), .commit (t 3)])
      (σ₁ := σA t ob) (i := .read (t 3) (ob 1)) (σ₂ := [.commit (t 3)]) rfl
    rw [hw] at hh
    have hl := hpos.ext ((X.committed_hist_iff hs).2 (by simp)) hh hnw (t 0)
      ((X.cwriter_hist_iff hs).2 (by simp [σA, σpre])) (by simp [e])
    have := hpos.lt_split X hs [.write (t 0) (ob 1), .commit (t 0)]
      ((σA t ob).drop 2 ++ [.read (t 3) (ob 1), .commit (t 3)])
      (by simp [σA, σpre, σpost]) (A := t 0) (B := t 3) (by simp) (by simp [e]) (by simp [σA, σpre])
      (by simp)
    omega
  | some W =>
    have hW : W = t 0 ∨ W = t 2 := by
      have := hr _ hg10.1 _ (t 3) (ob 1) W [] (by rw [STM.hist_snoc, hw])
      rw [X.writes_hist_iff] at this
      simp [σA, σpre, σpost, eo] at this
      tauto
    rcases hW with rfl | rfl
    · exfalso
      have hkept := hk (σA t ob) (t 3) (ob 1) (some (t 0)) hg10.1 hw hnw
      have hs := hgA.2
      have hold : Old (X.hist (σA t ob)) (ob 1, some (t 0)) :=
        ⟨(X.cwriter_hist_iff hs).2 (by simp [σA, σpre]), (ob 1, some (t 2)), rfl, t 2, rfl,
          (X.cwriter_hist_iff hs).2 (by simp [σA, σpost]), fun W hW => by
            cases hW
            have := X.commitBefore_hist [.write (t 0) (ob 1), .commit (t 0)] ((σA t ob).drop 2)
              (A := t 0) (B := t 2) (by simpa [σA, σpre] using hs) (by simp) (by simp [e])
            simpa [σA, σpre] using this⟩
      obtain ⟨T, W', hlive, hnext, hprec⟩ := hu _ _ _ hgA.1 hkept hold
      -- the live transaction is `T₄`
      have hT : T = t 3 := by
        obtain ⟨hb, hnt⟩ := hlive
        rw [X.began_hist_iff] at hb
        rw [terminated_iff_of_succ hs, X.map_inv_hist] at hnt
        obtain ⟨j, hj, rfl⟩ := hb
        simp [σA, σpre, σpost] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | rfl | exact absurd (by simp [σA, σpre, σpost]) hnt
      -- the overwriting transaction is `T₃`
      have hW' : W' = t 2 := by
        obtain ⟨⟨-, W'', hW'', hcw, hbef⟩, -⟩ := hnext
        cases hW''
        have := ((X.cwriter_hist_iff hs).1 hcw).2
        simp [σA, σpre, σpost, eo] at this
        rcases this with rfl | rfl
        · obtain ⟨h₁, h₂, -, hc1, hc2⟩ := hbef (t 0) rfl; exact absurd hc1 hc2
        · rfl
      subst hT hW'
      exact absurd (S.prec_T4 X hm hr _ hprec) (by simp [e])
    · rfl

end Setup3

end Podc.MultiVersionSTM

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P]

/-- **Theorem 3** of [Perelman–Fan–Keidar, PODC 2010], with UP GC in the potential-reader reading
of Section 7 (`STM.UPGCPrec`): an MV-permissive, strictly serializable STM whose reads return
written and kept versions, and which garbage-collects every overwritten version that no live
transaction precedes the overwriter of, cannot leave the configuration external to every solo
read-only transaction unchanged. The universe has two objects and five transactions on distinct
threads (`T₂`, `T₄` read-only; `Setup3`). See `theorem_3_false` for the literal reading of
Definition 4, under which the statement fails. -/
theorem theorem_3 {t : Fin 5 → Tx} {ob : Fin 2 → O} (S : Setup3 t ob) (X : STM Tx O P)
    (kept : Config X → Set (Version Tx O)) (hc : X.Correct) (hm : X.MVPermissive)
    (hr : X.ReadsWrittenOnly) (hk : X.KeepsReads kept) (hu : X.UPGCPrec kept) : ¬ X.NoTrace := by
  intro hnt
  have e := S.t_eq; have eo := S.ob_eq
  have hth : ∀ a b, thr (t a) = thr (t b) ↔ a = b := fun _ _ => S.hthr.eq_iff
  -- `T₄` reads `o₂²` in `H₂` without `T₂`
  have hA := S.read_T4_A X kept hc hm hr hk hu
  -- `T₂` leaves no trace
  have hg10 := S.good3 X hm 10 (by omega)
  have hext := hnt (σpre t ob) (σT2 t ob) (t 1)
    (by simpa [σ3, σpre, σT2, σpost, σend] using hg10.1) S.r1 (by simp [σT2])
    (by rw [X.began_hist_iff]; simp [σpre, e])
    (by
      have : X.Good (σpre t ob ++ σT2 t ob) := by simpa [σ3, σpre, σT2, σpost, σend] using hg10
      rw [X.committed_hist_iff this.2]; simp [σT2])
  -- hence `T₄` reads `o₂²` in `H₂` as well
  have hrun := X.run_eq_of_extEq hext (σpost t ob ++ [.read (t 3) (ob 1)])
    (by intro i hi; simp [σpost] at hi; rcases hi with rfl | rfl | rfl <;> simp [hth])
  have hH2 : X.resp (σpre t ob ++ σT2 t ob ++ σpost t ob) (.read (t 3) (ob 1)) =
      some (some (t 2)) := by
    rw [X.resp_append, X.step_resp_eq_of_run hrun, ← X.resp_append]
    simpa [σA] using hA
  -- `H₂` with `T₄` committing is not strictly serializable
  have hg := S.good3 X hm 14 le_rfl
  rw [List.take_of_length_le (by simp [σ3, σpre, σT2, σpost, σend])] at hg
  obtain ⟨pos, hpos⟩ := hc _ hg.1
  have hs := hg.2
  have cm : ∀ T, Inv.commit T ∈ σ3 t ob → Committed (X.hist (σ3 t ob)) T :=
    fun T h => (X.committed_hist_iff hs).2 h
  have cw : ∀ W o, Inv.commit W ∈ σ3 t ob → Inv.write W o ∈ σ3 t ob →
      CWriter (X.hist (σ3 t ob)) o W := fun W o h1 h2 => (X.cwriter_hist_iff hs).2 ⟨h1, h2⟩
  have sm : ∀ i : Inv Tx O, i ∈ σ3 t ob ↔ i ∈ σpre t ob ++ σT2 t ob ++ σpost t ob ++ σend t ob :=
    fun _ => Iff.rfl
  -- (i) `T₃ ≺ T₄`: `T₄` read `o₂²`
  have h1 : pos (t 2) < pos (t 3) := by
    obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σ3 t ob) (σ₁ := σpre t ob ++ σT2 t ob ++ σpost t ob)
      (i := .read (t 3) (ob 1)) (σ₂ := [.commit (t 3)]) (by simp [σ3, σend])
    rw [hH2] at hh
    exact (hpos.ext (cm _ (by simp [sm, σend])) hh
      (by rw [X.writes_hist_iff]; simp [σpre, σT2, σpost, e])).2.2.1
  -- (ii) `T₄ ≺ T₅`: `T₄` read `o₁⁰`, overwritten by `T₅`
  have h2 : pos (t 3) < pos (t 4) := by
    obtain ⟨rd2, -, -⟩ := S.readsA X hm hr
    obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σ3 t ob) (σ₁ := [.write (t 0) (ob 1), .commit (t 0)])
      (i := .read (t 3) (ob 0)) (σ₂ := ((σpre t ob).drop 3) ++ σT2 t ob ++ σpost t ob ++ σend t ob)
      (by simp [σ3, σpre])
    rw [rd2] at hh
    exact hpos.ext (cm _ (by simp [sm, σend])) hh (by simp [X.writes_hist_iff, e]) (t 4)
      (cw _ _ (by simp [sm, σpre]) (by simp [sm, σpre])) (by simp [e])
  -- (iii) `T₅ ≺ T₂`: real-time order
  have h3 : pos (t 4) < pos (t 1) :=
    hpos.lt_split X hs (σpre t ob) (σT2 t ob ++ σpost t ob ++ σend t ob) (by simp [σ3])
      (by simp [σpre]) (by simp [σpre, e]) (by simp [σT2]) (by simp [σT2])
  -- (iv) `T₂ ≺ T₃`: `T₂` read `o₂¹`, overwritten by `T₃`
  have h4 : pos (t 1) < pos (t 2) := by
    have hg8 : X.Good (σpre t ob ++ [.read (t 1) (ob 1)]) := by
      simpa [σ3, σpre, σT2, σpost, σend] using S.good3 X hm 8 (by omega)
    obtain ⟨a, ha⟩ := X.resp_some_of_good hg8
    obtain ⟨h₂, hh⟩ := X.hist_decomp' (σ := σ3 t ob) (σ₁ := σpre t ob) (i := .read (t 1) (ob 1))
      (σ₂ := (σT2 t ob).tail ++ σpost t ob ++ σend t ob) (by simp [σ3, σT2])
    rw [ha] at hh
    have hl := hpos.ext (cm _ (by simp [sm, σT2])) hh (by simp [X.writes_hist_iff, σpre, e])
    have h01 : pos (t 0) < pos (t 1) :=
      hpos.lt_split X hs [.write (t 0) (ob 1), .commit (t 0)]
        ((σpre t ob).drop 2 ++ σT2 t ob ++ σpost t ob ++ σend t ob) (by simp [σ3, σpre])
        (by simp) (by simp [e]) ⟨.commit (t 1), by simp [σT2], rfl⟩ (by simp [σT2])
    have h02 : pos (t 0) < pos (t 2) :=
      hpos.lt_split X hs [.write (t 0) (ob 1), .commit (t 0)]
        ((σpre t ob).drop 2 ++ σT2 t ob ++ σpost t ob ++ σend t ob) (by simp [σ3, σpre])
        (by simp) (by simp [e]) (by simp [σpre]) (by simp [σpost])
    cases a with
    | none =>
      have := hl (t 0) (cw _ _ (by simp [sm, σpre]) (by simp [sm, σpre])) (by simp [e])
      omega
    | some W =>
      obtain ⟨-, hW, hWlt, hmax⟩ := hl
      have hW0 : W = t 0 := by
        have := hr _ hg8.1 _ (t 1) (ob 1) W [] (by rw [STM.hist_snoc, ha])
        rw [X.writes_hist_iff] at this
        simpa [σpre, eo] using this
      subst hW0
      by_contra hlt
      have hne : pos (t 1) ≠ pos (t 2) :=
        hpos.inj (cm _ (by simp [sm, σT2])) (cm _ (by simp [sm, σpost])) (by simp [e])
      have := hmax (t 2) (cw _ _ (by simp [sm, σpost]) (by simp [sm, σpost])) (by simp [e])
        (by omega)
      omega
  omega

end Podc.MultiVersionSTM
