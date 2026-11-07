import Papers.PODC2010.MultiVersionSTM.Forced

/-!
# The histories of Figure 2 (Theorem 1)

Transactions `T₁ … T₅` are `t 0 … t 4` (`T₁`, `T₃` read-only), objects `o₁ … o₅` are
`ob 0 … ob 4`.

* `σH` (Figure 2(a)): `T₁` reads `o₂, o₄, o₅`; `T₂` writes `o₂, o₃` and commits; `T₃` reads `o₁`;
  `T₄` writes `o₃, o₄, o₅` and commits. Time `t₀` is the end of `σH`.
* `σH1` (Figure 2(b)): then `T₅` writes `o₁, o₄, o₅` and commits. Time `t₁` is its end.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P]

/-- The assumptions on the five transactions and five objects of Figure 2. -/
structure Setup1 (t : Fin 5 → Tx) (ob : Fin 5 → O) : Prop where
  ht : Function.Injective t
  hob : Function.Injective ob
  hthr : Function.Injective (fun k => thr (t k))
  r0 : ro (t 0) = true
  r1 : ro (t 1) = false
  r2 : ro (t 2) = true
  r3 : ro (t 3) = false
  r4 : ro (t 4) = false

variable (t : Fin 5 → Tx) (ob : Fin 5 → O)

/-- The schedule of Figure 2(a), up to time `t₀`. -/
def σH : List (Inv Tx O) :=
  [.read (t 0) (ob 1), .read (t 0) (ob 3), .read (t 0) (ob 4),
   .write (t 1) (ob 1), .write (t 1) (ob 2), .commit (t 1),
   .read (t 2) (ob 0),
   .write (t 3) (ob 2), .write (t 3) (ob 3), .write (t 3) (ob 4), .commit (t 3)]

/-- The schedule of Figure 2(b), up to time `t₁`. -/
def σH1 : List (Inv Tx O) :=
  σH t ob ++ [.write (t 4) (ob 0), .write (t 4) (ob 3), .write (t 4) (ob 4), .commit (t 4)]

variable {t ob}

namespace Setup1

variable (S : Setup1 t ob)
include S

lemma t_eq (a b : Fin 5) : t a = t b ↔ a = b := S.ht.eq_iff
lemma ob_eq (a b : Fin 5) : ob a = ob b ↔ a = b := S.hob.eq_iff

/-- Every prefix of `σH1` is executed by an MV-permissive STM without aborts. -/
lemma good (X : STM Tx O P) (hm : X.MVPermissive) (k : ℕ) (hk : k ≤ 15) :
    X.Good ((σH1 t ob).take k) := by
  have e := S.t_eq
  have r0 := S.r0; have r1 := S.r1; have r2 := S.r2; have r3 := S.r3; have r4 := S.r4
  induction k with
  | zero => simpa using X.good_nil
  | succ k ih =>
    have hk' : k < 15 := by omega
    refine X.good_take_succ hm _ k (by simp [σH1, σH]; omega) (ih (by omega)) ?_ ?_
    · refine ⟨?_, ?_, okNextS_thr t S.hthr _ _ ?_ ?_⟩ <;> interval_cases k <;>
        simp [σH1, σH, e, r1, r3, r4]
    · interval_cases k
      all_goals first
        | (left; simp [σH1, σH, r0, r2]; done)
        | (right
           intro T' hne hro hb
           first
           | (exfalso
              simp [σH1, σH] at hb hne
              rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp_all
              done)
           | (refine ⟨_, _, (List.take_append_drop 7 _).symm, ?_, ?_⟩
              · simp [σH1, σH] at hb hne ⊢
                rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp_all
              · simp [σH1, σH, e]
              done)
           | (refine ⟨_, _, (List.take_append_drop 11 _).symm, ?_, ?_⟩
              · simp [σH1, σH] at hb hne ⊢
                rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp_all
              · simp [σH1, σH, e]
              done))

lemma good_σH (X : STM Tx O P) (hm : X.MVPermissive) : X.Good (σH t ob) := by
  have := S.good X hm 11 (by omega)
  rwa [σH1, List.take_append_of_le_length (by simp [σH]), List.take_of_length_le (by simp [σH])] at this

lemma good_σH1 (X : STM Tx O P) (hm : X.MVPermissive) : X.Good (σH1 t ob) := by
  simpa [σH1, σH] using S.good X hm 15 le_rfl

/-- The reads of `σH` return initial versions. -/
lemma reads (X : STM Tx O P) (hm : X.MVPermissive) (hr : X.ReadsWrittenOnly) :
    X.resp [] (.read (t 0) (ob 1)) = some none ∧
    X.resp [.read (t 0) (ob 1)] (.read (t 0) (ob 3)) = some none ∧
    X.resp [.read (t 0) (ob 1), .read (t 0) (ob 3)] (.read (t 0) (ob 4)) = some none ∧
    X.resp [.read (t 0) (ob 1), .read (t 0) (ob 3), .read (t 0) (ob 4),
      .write (t 1) (ob 1), .write (t 1) (ob 2), .commit (t 1)] (.read (t 2) (ob 0)) = some none := by
  have eo := S.ob_eq
  refine ⟨X.read_none hr ?_ ?_, X.read_none hr ?_ ?_, X.read_none hr ?_ ?_, X.read_none hr ?_ ?_⟩
  · simpa [σH1, σH] using S.good X hm 1 (by omega)
  · simp
  · simpa [σH1, σH] using S.good X hm 2 (by omega)
  · simp
  · simpa [σH1, σH] using S.good X hm 3 (by omega)
  · simp
  · simpa [σH1, σH] using S.good X hm 7 (by omega)
  · simp [eo]

end Setup1

end Podc.MultiVersionSTM
