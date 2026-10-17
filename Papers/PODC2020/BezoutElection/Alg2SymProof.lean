import Papers.PODC2020.BezoutElection.Alg2Sym

/-!
# Algorithm 2 commutes with identifier renamings

Equivariance of the local computation (`procReg_smul`, `loopFrom_smul`, `afterCollect_smul`),
hence `alg2_symmetric'`; and `alg2_readWrite'` (every access is a plain read or a plain write).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ}

attribute [ext] St

lemma map_update_fun (σ : Equiv.Perm Id) (d : Fin m → Finset Id) (x : Fin m) (D : Finset Id) :
    (fun y => (Function.update d x D y).map σ.toEmbedding) =
      Function.update (fun y => (d y).map σ.toEmbedding) x (D.map σ.toEmbedding) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · simp [Function.update_of_ne hy]

lemma st_smul_disc_fun (σ : Equiv.Perm Id) (s : St Id m) :
    (σ • s).disc = fun x => (s.disc x).map σ.toEmbedding := rfl

lemma finset_map_sup (σ : Equiv.Perm Id) (f : Fin m → Finset Id) :
    Finset.univ.sup (fun x => (f x).map σ.toEmbedding) =
      (Finset.univ.sup f).map σ.toEmbedding := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => rw [Finset.sup_insert, Finset.sup_insert, ih, Finset.sup_eq_union, Finset.sup_eq_union,
      Finset.map_union]

lemma procReg_smul (p : Params) (σ : Equiv.Perm Id) (s : St Id m) (x : Fin m) :
    procReg p (σ • s) x = (σ • (procReg p s x).1, (procReg p s x).2.map (σ • ·)) := by
  have hme : ∀ D : Finset Id, (σ s.me ∉ D.map σ.toEmbedding) ↔ s.me ∉ D := by
    intro D; simp
  unfold procReg
  simp only [st_smul_regs, smul_level, smul_phase, st_smul_level, st_smul_phase, smul_disc,
    Finset.card_map, smul_id, ne_eq, Option.map_eq_none_iff, st_smul_me, hme, st_smul_loser,
    st_smul_cand, st_smul_toWin, st_smul_finishing, map_ne_some_iff, st_smul_disc]
  split_ifs <;>
  · refine Prod.ext ?_ ?_
    · apply St.ext <;> first | rfl | (simp [*, st_smul_disc_fun, map_update_fun, Finset.map_insert,
        Finset.map_union] <;> rfl)
    · simp [*, reg_smul_mk, Finset.map_insert, Finset.map_union]


lemma loopFrom_smul (p : Params) (σ : Equiv.Perm Id) (s : St Id m) (k : ℕ) :
    loopFrom p (σ • s) k = σ • loopFrom p s k := by
  rw [loopFrom, loopFrom]
  by_cases h : k < m
  · rw [dite_eq_left h, dite_eq_left h, procReg_smul]
    rcases procReg p s ⟨k, h⟩ with ⟨s', _ | w⟩
    · exact loopFrom_smul p σ s' (k + 1)
    · rfl
  · rw [dite_eq_right h, dite_eq_right h]; rfl
termination_by m - k

lemma afterCollect_smul (p : Params) (σ : Equiv.Perm Id) (s : St Id m) :
    afterCollect p (σ • s) = σ • afterCollect p s := by
  have hsum : ∑ x, ((σ • s).regs x).level = ∑ x, (s.regs x).level := rfl
  have hsup : Finset.univ.sup (fun x => ((σ • s).regs x).leaders) =
      (Finset.univ.sup (fun x => (s.regs x).leaders)).map σ.toEmbedding := by
    simp only [st_smul_regs, smul_leaders]; exact finset_map_sup σ _
  unfold afterCollect
  simp only [hsum, hsup, st_smul_finishing]
  split_ifs with h1 h2
  · rfl
  · exact loopFrom_smul p σ { s with finishing := true, toWin := 1 } 0
  · exact loopFrom_smul p σ s 0

variable {R : Type} [Inhabited R]

/-- **Algorithm 2 is symmetric** (with equality). -/
theorem alg2_symmetric' (p : Params) (out : Id → Finset Id → R)
    (hout : ∀ (σ : Equiv.Perm Id) a L, out (σ a) (L.map σ.toEmbedding) = out a L) :
    (alg2 Id m p out).Symmetric where
  bot σ := by
    change Reg.smul σ Reg.init = Reg.init
    simp [Reg.smul, Reg.init]
  init σ a := by
    change _ = St.smul σ _
    simp only [alg2, St.smul, PC.smul]
    congr 1
  invoke σ s o := by
    simp only [alg2, st_smul_pc]
    cases s.pc <;> rfl
  act σ s := by
    simp only [alg2, st_smul_pc]
    cases hpc : s.pc with
    | collect k =>
      simp only [PC.smul]
      by_cases hk : k < m
      · rw [dite_eq_left hk, dite_eq_left hk]
        simp only [SymAction.smul, SymAction.rmw.injEq, true_and, smul_inv_smul]
        funext v
        have hreg : Function.update (σ • s).regs ⟨k, hk⟩ v =
            (σ • { s with regs := Function.update s.regs ⟨k, hk⟩ (σ⁻¹ • v) }).regs := by
          funext y
          by_cases hy : y = ⟨k, hk⟩
          · subst hy; simp
          · simp [Function.update_of_ne hy]
        split_ifs
        · apply St.ext <;> first | rfl | exact hreg
        · rw [← afterCollect_smul]; congr 1
          apply St.ext <;> first | rfl | exact hreg
      · rw [dite_eq_right hk, dite_eq_right hk]; rfl
    | write k w =>
      simp only [PC.smul]
      by_cases hk : k < m
      · rw [dite_eq_left hk, dite_eq_left hk]
        simp only [SymAction.smul, SymAction.rmw.injEq, true_and]
        funext _; exact loopFrom_smul p σ s (k + 1)
      · rw [dite_eq_right hk, dite_eq_right hk]; rfl
    | ret L =>
      simp only [PC.smul, SymAction.smul, st_smul_me, hout]
      rfl
    | idle => rfl
    | fin => rfl

/-- Algorithm 2 only uses plain reads and writes. -/
theorem alg2_readWrite' (p : Params) (out : Id → Finset Id → R) :
    (alg2 Id m p out).ReadWrite := by
  intro s x f k h
  simp only [alg2] at h
  split at h
  · split at h
    · simp only [SymAction.rmw.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact Or.inl fun _ => rfl
    · cases h
  · split at h
    · simp only [SymAction.rmw.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact Or.inr ⟨_, _, fun _ => rfl, fun _ => rfl⟩
    · cases h
  · cases h
  · cases h

end BezoutElection.Alg2
