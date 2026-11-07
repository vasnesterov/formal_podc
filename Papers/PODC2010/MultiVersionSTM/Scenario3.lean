import Papers.PODC2010.MultiVersionSTM.Forced

/-!
# The histories of Figure 4 (Theorem 3)

Transactions `T₁ … T₅` are `t 0 … t 4` (`T₂`, `T₄` read-only), objects `o₁, o₂` are `ob 0, ob 1`.

`σ3` is the history `H₂` of Figure 4(b): `T₁` writes `o₂` and commits; `T₄` reads `o₁`; `T₅`
reads `o₁`; `T₃` reads `o₂`; `T₅` writes `o₁` and commits; then the read-only `T₂` runs alone
(reads `o₂`, `o₁`, commits); then `T₃` writes `o₂` and commits; finally `T₄` reads `o₂` and
commits. `σ3'` is the same history without `T₂`.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P]

/-- The assumptions on the transactions and objects of Figure 4. -/
structure Setup3 (t : Fin 5 → Tx) (ob : Fin 2 → O) : Prop where
  ht : Function.Injective t
  hob : Function.Injective ob
  hthr : Function.Injective (fun k => thr (t k))
  r0 : ro (t 0) = false
  r1 : ro (t 1) = true
  r2 : ro (t 2) = false
  r3 : ro (t 3) = true
  r4 : ro (t 4) = false

variable (t : Fin 5 → Tx) (ob : Fin 2 → O)

/-- The prefix common to `H₂` and to `H₂` without `T₂`. -/
def σpre : List (Inv Tx O) :=
  [.write (t 0) (ob 1), .commit (t 0), .read (t 3) (ob 0), .read (t 4) (ob 0), .read (t 2) (ob 1),
   .write (t 4) (ob 0), .commit (t 4)]

/-- The solo run of the read-only transaction `T₂`. -/
def σT2 : List (Inv Tx O) := [.read (t 1) (ob 1), .read (t 1) (ob 0), .commit (t 1)]

/-- `T₃` writes `o₂` and commits. -/
def σpost : List (Inv Tx O) := [.write (t 2) (ob 1), .commit (t 2)]

/-- `T₄` reads `o₂` and commits. -/
def σend : List (Inv Tx O) := [.read (t 3) (ob 1), .commit (t 3)]

/-- The history `H₂` of Figure 4(b). -/
def σ3 : List (Inv Tx O) := σpre t ob ++ σT2 t ob ++ σpost t ob ++ σend t ob

/-- `H₂` without `T₂`. -/
def σ3' : List (Inv Tx O) := σpre t ob ++ σpost t ob ++ σend t ob

variable {t ob}

lemma tx_mem3 : ∀ j ∈ σ3 t ob, ∃ a, Inv.tx j = t a := by
  intro j hj
  simp [σ3, σpre, σT2, σpost, σend] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl⟩

lemma tx_mem3' : ∀ j ∈ σ3' t ob, ∃ a, Inv.tx j = t a := by
  intro j hj
  simp [σ3', σpre, σpost, σend] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl⟩

namespace Setup3

variable (S : Setup3 t ob)
include S

lemma t_eq (a b : Fin 5) : t a = t b ↔ a = b := S.ht.eq_iff
lemma ob_eq (a b : Fin 2) : ob a = ob b ↔ a = b := S.hob.eq_iff

lemma good3 (X : STM Tx O P) (hm : X.MVPermissive) (k : ℕ) (hk : k ≤ 14) :
    X.Good ((σ3 t ob).take k) := by
  have e := S.t_eq; have eo := S.ob_eq
  have r0 := S.r0; have r1 := S.r1; have r2 := S.r2; have r3 := S.r3; have r4 := S.r4
  induction k with
  | zero => simpa using X.good_nil
  | succ k ih =>
    have hk' : k < 14 := by omega
    refine X.good_take_succ2 hm _ k (by simp [σ3, σpre, σT2, σpost, σend]; omega) (ih (by omega))
      ?_ ?_
    · refine ⟨?_, ?_, okNextS_thr t S.hthr _ _ ?_ ?_⟩ <;> interval_cases k <;>
        simp [σ3, σpre, σT2, σpost, σend, e, r0, r2, r4]
    · interval_cases k
      all_goals first
        | (left; simp [σ3, σpre, σT2, σpost, σend, r1, r3]; done)
        | (right
           intro T' hne hro hb
           obtain ⟨j, hj, rfl⟩ := hb
           obtain ⟨k', hk'⟩ := tx_mem3 j (List.mem_of_mem_take hj)
           rw [hk'] at hne hro ⊢
           simp [σ3, σpre, σT2, σpost, σend] at hne
           fin_cases k'
           all_goals first
             | (exfalso; simp_all; done)
             | (left
                refine ⟨_, _, (List.take_append_drop 2 _).symm, ?_, ?_⟩ <;>
                  simp [σ3, σpre, σT2, σpost, σend, e]
                done)
             | (right
                intro o h1 h2
                simp [σ3, σpre, σT2, σpost, σend, e] at h1 h2
                all_goals (subst h1; simp [eo] at h2)
                done))

lemma good3' (X : STM Tx O P) (hm : X.MVPermissive) (k : ℕ) (hk : k ≤ 11) :
    X.Good ((σ3' t ob).take k) := by
  have e := S.t_eq; have eo := S.ob_eq
  have r0 := S.r0; have r1 := S.r1; have r2 := S.r2; have r3 := S.r3; have r4 := S.r4
  induction k with
  | zero => simpa using X.good_nil
  | succ k ih =>
    have hk' : k < 11 := by omega
    refine X.good_take_succ2 hm _ k (by simp [σ3', σpre, σT2, σpost, σend]; omega) (ih (by omega))
      ?_ ?_
    · refine ⟨?_, ?_, okNextS_thr t S.hthr _ _ ?_ ?_⟩ <;> interval_cases k <;>
        simp [σ3', σpre, σT2, σpost, σend, e, r0, r2, r4]
    · interval_cases k
      all_goals first
        | (left; simp [σ3', σpre, σT2, σpost, σend, r1, r3]; done)
        | (right
           intro T' hne hro hb
           obtain ⟨j, hj, rfl⟩ := hb
           obtain ⟨k', hk'⟩ := tx_mem3' j (List.mem_of_mem_take hj)
           rw [hk'] at hne hro ⊢
           simp [σ3', σpre, σT2, σpost, σend] at hne
           fin_cases k'
           all_goals first
             | (exfalso; simp_all; done)
             | (left
                refine ⟨_, _, (List.take_append_drop 2 _).symm, ?_, ?_⟩ <;>
                  simp [σ3', σpre, σT2, σpost, σend, e]
                done)
             | (right
                intro o h1 h2
                simp [σ3', σpre, σT2, σpost, σend, e] at h1 h2
                all_goals (subst h1; simp [eo] at h2)
                done))

end Setup3

end Podc.MultiVersionSTM
