import Papers.PODC2024.RecoverableConsensus.Defs

/-!
# Section 4 of Ovens (PODC'24): common lemmas

Shared infrastructure for the proofs of Lemma 15 and Lemma 16 (type `T_{n,n'}`):

* `idx u` — how many `op₀`/`op₁` operations the value `u` has absorbed (`s ↦ 0`,
  `s_{x,i} ↦ i`, `s⊥ ↦ n`); `op_y` maps `idx` to `min (idx + 1) n` (`idx_op`), and `opR` breaks
  the object iff `n' < idx` (`tδ_opR_of_lt`, `tδ_opR_cases`);
* the absorption contradiction (`Team.false_of_absorb`) and the "standard argument" for
  read/write objects (`Crit.not_forall_poised_of_rwLike`) are shared
  (`Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`);
* `all_ops` — if they are all poised on a `T_{n,n'}` object, nobody is poised to apply `opR`
  (first part of the proofs of Lemmas 15 and 16);
* `run_ops` — running distinct processes poised to apply `op₀`/`op₁`;
* `bitOf`, `T1`, `mem0` — the single-object setting of the two algorithms of Section 4.
-/

namespace Cslib.SharedMemory.Recoverable.Ovens.Sec4

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

set_option linter.unusedSectionVars false

/-- Number of `op₀`/`op₁` operations "absorbed" by a value of `T_{n,n'}`: `s ↦ 0`,
`s_{x,i} ↦ i`, `s⊥ ↦ n`. -/
def idx {n : ℕ} : TVal n → ℕ
  | .s => 0
  | .bot => n
  | .sv _ i => i.val + 1

lemma idx_le {n : ℕ} (u : TVal n) : idx u ≤ n := by
  cases u with
  | s => simp [idx]
  | bot => simp [idx]
  | sv x i => simp only [idx]; have := i.isLt; omega

lemma idx_op {n n' : ℕ} (u : TVal n) (y : Bool) :
    idx (tδ n n' u (.op y)).1 = min (idx u + 1) n := by
  cases u with
  | s =>
    simp only [tδ]
    split <;> simp [idx] <;> omega
  | bot => simp [tδ, idx]
  | sv x i =>
    simp only [tδ]
    split <;> simp [idx] <;> omega

lemma eq_bot_of_idx {n : ℕ} (hn : 0 < n) {u : TVal n} (h : n ≤ idx u) : u = .bot := by
  cases u with
  | s => simp [idx] at h; omega
  | bot => rfl
  | sv x i => simp only [idx] at h; have := i.isLt; omega

lemma tδ_opR_of_lt {n n' : ℕ} {u : TVal n} (h : n' < idx u) : tδ n n' u .opR = (.bot, .bot) := by
  cases u with
  | s => simp [idx] at h
  | bot => simp [tδ]
  | sv x i => simp only [idx] at h; simp [tδ, show ¬ i.val + 1 ≤ n' by omega]

lemma lt_idx_tδ {n n' : ℕ} {u : TVal n} (h : n' < idx u) (o : TOp) : n' < idx (tδ n n' u o).1 := by
  cases o with
  | op y => rw [idx_op]; have := idx_le u; omega
  | opR => rw [tδ_opR_of_lt h]; have := idx_le u; simp only [idx]; omega

lemma tδ_opR_cases {n n' : ℕ} (u : TVal n) : (tδ n n' u .opR).1 = u ∨ n' < idx u := by
  cases u with
  | s => left; rfl
  | bot => left; rfl
  | sv x i =>
    by_cases h : i.val + 1 ≤ n'
    · left; simp [tδ, h]
    · right; simp only [idx]; omega

lemma tδ_op_spec {n n' : ℕ} (u : TVal n) (y : Bool) (hu : u ≠ .bot) :
    ∃ w, (tδ n n' u (.op y)).2 = .bit w ∧ (u = .s → w = y) ∧ (∀ v i, u = .sv v i → w = v) ∧
      ∀ v i, (tδ n n' u (.op y)).1 = .sv v i → v = w := by
  cases u with
  | s =>
    refine ⟨y, ?_, fun _ => rfl, fun v i h => (by cases h), fun v i h => ?_⟩
    · simp only [tδ]; split <;> rfl
    · simp only [tδ] at h; split at h <;> simp_all
  | bot => exact absurd rfl hu
  | sv x i =>
    refine ⟨x, ?_, fun h => (by cases h), fun v i h => (by cases h; rfl), fun v i' h => ?_⟩
    · simp only [tδ]; split <;> rfl
    · simp only [tδ] at h; split at h <;> simp_all

lemma tδ_s_op {n n' : ℕ} (y : Bool) (h : 0 < n - 1) :
    tδ n n' .s (.op y) = (.sv y ⟨0, h⟩, .bit y) := by simp [tδ, h]

lemma tδ_sv_op {n n' : ℕ} (v y : Bool) (i : Fin (n - 1)) (h : i.val + 1 < n - 1) :
    tδ n n' (.sv v i) (.op y) = (.sv v ⟨i.val + 1, h⟩, .bit v) := by simp [tδ, h]

lemma tδ_sv_opR {n n' : ℕ} (v : Bool) (i : Fin (n - 1)) (h : i.val + 1 ≤ n') :
    tδ n n' (.sv v i) .opR = (.sv v i, .val (.sv v i)) := by simp [tδ, h]

/-- Responses to bits (`⊥` and values are mapped to `0`). -/
def bitOf {n : ℕ} : TResp n → Bool
  | .bit b => b
  | _ => false

/-- No read/write objects. -/
abbrev noRW : Empty → ObjSpec := fun e => e.elim

/-- The objects of the algorithms of Section 4: a single object of type `T_{n,n'}`. -/
abbrev T1 (n n' : ℕ) : Empty ⊕ Unit → ObjSpec := withRW (ιS := Unit) noRW (Tnn n n')

/-- Initial values: the object `O` starts with value `s`. -/
def mem0 {n n' : ℕ} : (i : Empty ⊕ Unit) → (T1 n n' i).State
  | .inl e => e.elim
  | .inr _ => (TVal.s : TVal n)

/-! ## Algorithms using `T_{n,n'}` and read/write objects -/

section Tnn

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {n n' m : ℕ}
  {A : Alg m (withRW (ιS := ιS) R (Tnn n n'))}

/-- Running distinct processes, all poised to apply `op₀`/`op₁` to the `T_{n,n'}` object `j`:
the other objects and the other processes are unaffected and `idx` grows by the number of
operations (capped at `n`). -/
lemma run_ops (j : ιS) : ∀ (σ : List (Fin m)) (D : Cfg A), σ.Nodup →
    (∀ r ∈ σ, ∃ y kk, A.act (D.loc r) = .access (Sum.inr j) (TOp.op y) kk) →
    (∀ i, i ≠ Sum.inr j → (run D (σ.map Ev.step)).mem i = D.mem i) ∧
    (∀ r, r ∉ σ → (run D (σ.map Ev.step)).loc r = D.loc r) ∧
    idx (n := n) ((run D (σ.map Ev.step)).mem (Sum.inr j)) =
      min (idx (n := n) (D.mem (Sum.inr j)) + σ.length) n := by
  intro σ
  induction σ with
  | nil =>
    intro D _ _
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    have := idx_le (n := n) (D.mem (Sum.inr j))
    simp only [List.length_nil, Nat.add_zero, List.map_nil, run_nil]
    omega
  | cons r σ ih =>
    intro D hnd hpo
    obtain ⟨y, kk, hr⟩ := hpo r (by simp)
    have hD' := stepP_of_access D hr
    have hnd' := List.nodup_cons.1 hnd
    have hpo' : ∀ r' ∈ σ, ∃ y kk, A.act ((D.stepP r).loc r') =
        .access (Sum.inr j) (TOp.op y) kk := by
      intro r' hr'
      have hne : r' ≠ r := by rintro rfl; exact hnd'.1 hr'
      rw [stepP_loc_other D hne]
      exact hpo r' (by simp [hr'])
    obtain ⟨h1, h2, h3⟩ := ih (D.stepP r) hnd'.2 hpo'
    simp only [List.map_cons, run_cons, Cfg.next]
    refine ⟨fun i hi => ?_, fun r' hr' => ?_, ?_⟩
    · rw [h1 i hi, hD']
      exact Function.update_of_ne hi _ _
    · have hne : r' ≠ r := by rintro rfl; simp at hr'
      rw [h2 r' (fun h => hr' (by simp [h])), stepP_loc_other D hne]
    · rw [h3, hD']
      simp only [Function.update_self, List.length_cons]
      have := idx_op (n' := n') (D.mem (Sum.inr j)) y
      erw [this]
      omega

variable {Adm : List (Ev m) → Prop} {z : ℕ} {C : Cfg A}

/-- At a critical execution where all processes are poised on the `T_{n,n'}` object `j`, no
process is poised to apply `opR` (first part of the proofs of Lemmas 15 and 16; for the case
`value(O, Cαpᵢ) = s⊥` we compare `Cαpᵢ` with `Cαpⱼpᵢ`, which are indistinguishable to `pᵢ`). -/
lemma all_ops (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C) (hm : 0 < m)
    {α : List (Ev m)} (hc : Crit z C α) {j : ιS} (hpo : ∀ p, (run C α).Poised p (Sum.inr j)) :
    ∀ p, ∃ y kk, A.act ((run C α).loc p) = .access (Sum.inr j) (TOp.op y) kk := by
  obtain ⟨⟨p0, hp0⟩, ⟨p1, hp1⟩⟩ := hc.teams hA hAdm hC hm
  intro p
  obtain ⟨o, kk, ho⟩ := hpo p
  cases o with
  | op y => exact ⟨y, kk, ho⟩
  | opR =>
    exfalso
    obtain ⟨v, hv⟩ := hc.team p
    obtain ⟨q, hq⟩ : ∃ q, Team z C α q (!v) := by cases v; exacts [⟨p1, hp1⟩, ⟨p0, hp0⟩]
    obtain ⟨oq, kq, hoq⟩ := hpo q
    rcases tδ_opR_cases (n' := n') ((run C α).mem (Sum.inr j)) with h | h
    · exact hv.false_of_absorb hA hAdm hC hc.1 hq (by cases v <;> simp) ho hoq (by erw [h])
    · refine hq.false_of_absorb hA hAdm hC hc.1 hv (by cases v <;> simp) hoq ho ?_
      show tδ n n' (tδ n n' _ oq).1 .opR = tδ n n' _ .opR
      rw [tδ_opR_of_lt h, tδ_opR_of_lt (lt_idx_tδ h oq)]

end Tnn

end Cslib.SharedMemory.Recoverable.Ovens.Sec4
