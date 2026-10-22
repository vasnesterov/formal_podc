import Papers.PODC2016.ReliableStorageSpace.SafeAlgorithm

/-!
# Line 16 of Algorithm 2 needs the largest timestamp

Line 16 of Algorithm 2 lets a reader decode *any* timestamp of which it has read at least `k`
pieces. We show that a legitimate resolution of this choice — the **smallest** such timestamp
(`algMin`) — is not strongly safe (nor weakly regular), already for replication with `n = 3`, `f = 1`,
`k = 1`: write `w₁` stores on objects `0, 1` and returns; write `w₂` then reads objects `0, 1`,
stores on objects `1, 2` and returns; a read invoked afterwards hears from objects `0, 1`, sees one
piece of each write, and returns the value of `w₁`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Podc.ReliableStorageSpace.Safe

open Finset Classical
open Podc.ReliableStorageSpace.Alg (Precedes IsWrite Completed lastVal)

variable {C V : Type} [LinearOrder C] {n : ℕ}

/-- The read output when decoding the **smallest** timestamp with at least `k` pieces. -/
def rdoutMin (k ℓ : ℕ) (enc : Fin n → V → Fin (2 ^ ℓ)) (v₀ : V) (l : Loc C n)
    (g : (b : Blk C (Fin n)) → Fin (2 ^ ℓ)) : V :=
  if h : (good k l).Nonempty then
    decodeP v₀ (fun v => ∀ j ∈ pcs l ((good k l).min' h),
      enc j v = g (((good k l).min' h).w, j))
  else v₀

variable (f k ℓ : ℕ) (enc : Fin n → V → Fin (2 ^ ℓ)) (v₀ : V) (hℓ : 0 < ℓ) (hn : 0 < n)

/-- Algorithm 2 with line 16 resolved by the smallest timestamp. -/
@[reducible] def algMin : Alg C (Fin n) (Fin n) V :=
  { alg f k ℓ enc v₀ hℓ hn with
    rdout := fun _ l g => rdoutMin k ℓ enc v₀ l g
    rdout_congr := by
      intro c l g g' h
      simp only [rdoutMin]
      split_ifs with hne
      · congr 1
        funext v
        apply propext
        apply forall_congr'; intro j; apply imp_congr_right; intro hj
        rw [h]
        simp only [pcs, mem_filter, mem_univ, true_and] at hj
        obtain ⟨o, ch, h1, h2, h3⟩ := hj
        exact mem_lblkF.2 ⟨o, ch, h1, by rw [← h2, ← h3]; rfl⟩
      · rfl }

/-! ### The concrete run -/

/-- Replication of a bit over three objects. -/
abbrev M : Alg (Fin 3) (Fin 3) (Fin 3) (Fin 2) :=
  algMin (C := Fin 3) (n := 3) (V := Fin 2) 1 1 1 (fun _ v => v) 0 (by decide) (by decide)

/-- The events of the run: `w₁ = (0, 0)`, then `w₂ = (1, 0)`, then the read `(2, 0)`. -/
def evs : List (Event (Fin 3)) :=
  [-- `w₁`: read objects 0, 1, then update objects 0, 1 (its RMWs on object 2 stay pending)
   .inv 0 .write, .step 0, .step 0, .step 0, .exec 0 0, .exec 0 1, .step 0, .step 0, .step 0,
   .exec 0 3, .exec 0 4, .step 0,
   -- `w₂`: read objects 0, 1, then update objects 1, 2
   .inv 1 .write, .step 1, .step 1, .step 1, .exec 1 0, .exec 1 1, .step 1, .step 1, .step 1,
   .exec 1 4, .exec 1 5, .step 1,
   -- the read: hears from objects 0, 1
   .inv 2 .read, .step 2, .step 2, .step 2, .exec 2 0, .exec 2 1, .step 2]

theorem nresp3 (l : Loc C 3) : nresp l =
    (if (l.resp 0).isSome then 1 else 0) + (if (l.resp 1).isSome then 1 else 0) +
      (if (l.resp 2).isSome then 1 else 0) := by
  unfold nresp
  rw [Finset.card_filter, Fin.sum_univ_three]

theorem sup_univ_fin3 (g : Fin 3 → ℕ) : univ.sup g = g 0 ⊔ (g 1 ⊔ g 2) := by
  rw [show (univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  simp [Finset.sup_insert]

theorem runFrom_cons' {A : Alg (Fin 3) (Fin 3) (Fin 3) (Fin 2)} (X : A.Config) (e : Event (Fin 3))
    (es : List (Event (Fin 3))) : A.runFrom X (e :: es) = A.runFrom (A.step X e) es := rfl

theorem runFrom_nil' {A : Alg (Fin 3) (Fin 3) (Fin 3) (Fin 2)} (X : A.Config) :
    A.runFrom X [] = X := rfl

/-- The reader's local state just before it returns. -/
def Lr : Loc (Fin 3) 3 := (M.runFrom M.init (evs.take 30)).loc 2

theorem Lr_resp : Lr.resp 0 = some (some ⟨1, (0, 0), 0⟩) ∧ Lr.resp 1 = some (some ⟨2, (1, 0), 1⟩) ∧
    Lr.resp 2 = none := by
  simp [Lr, evs, runFrom_cons', runFrom_nil', Alg.step, Alg.init, actF, rmwOf, Alg.findP, applyF,
    recvF, nresp3, maxNum, sup_univ_fin3, upd_apply', ots, Chunk.key,
    WithBot.coe_lt_coe, Prod.Lex.toLex_lt_toLex]

/-- The history of the run. -/
theorem run_hist : (M.runFrom M.init evs).hist =
    [.inv 0 0 .write, .ret 0 0 none, .inv 1 0 .write, .ret 1 0 none, .inv 2 0 .read,
     .ret 2 0 (some (M.rdout 2 Lr))] := by
  simp [Lr, evs, runFrom_cons', runFrom_nil', Alg.step, Alg.init, actF, rmwOf, Alg.findP, applyF,
    recvF, nresp3, maxNum, sup_univ_fin3, upd_apply', ots, Chunk.key,
    WithBot.coe_lt_coe, Prod.Lex.toLex_lt_toLex]

theorem mem_pcs {l : Loc C n} {o : Fin n} {ch : Chunk C n} (h : l.resp o = some (some ch)) :
    ch.j ∈ pcs l ch.key := by
  simp only [pcs, mem_filter, mem_univ, true_and]
  exact ⟨o, ch, h, rfl, rfl⟩

/-- The read returns the value of `w₁ = (0, 0)` (it decodes the smallest timestamp, that of `w₁`). -/
theorem out_val (val : OpId (Fin 3) → Fin 2) : M.rdout 2 Lr (M.contents val) = val (0, 0) := by
  obtain ⟨h0, h1, h2⟩ := Lr_resp
  change rdoutMin 1 1 (fun _ v => v) 0 Lr (M.contents val) = _
  have hgood : ∀ o ch, Lr.resp o = some (some ch) → ch.key ∈ good 1 Lr := by
    intro o ch h
    simp only [good, mem_biUnion, mem_univ, true_and]
    refine ⟨o, ?_⟩
    rw [h]
    have : 1 ≤ (pcs Lr ch.key).card := Finset.card_pos.2 ⟨_, mem_pcs h⟩
    simp [this]
  have hmem := hgood 0 _ h0
  have hle : ∀ κ ∈ good 1 Lr, (Chunk.key ⟨1, (0, 0), (0 : Fin 3)⟩ : Key (Fin 3)) ≤ κ := by
    intro κ hκ
    simp only [good, mem_biUnion, mem_univ, true_and] at hκ
    obtain ⟨o, ho⟩ := hκ
    fin_cases o
    · simp only [Fin.zero_eta, Fin.isValue, h0] at ho
      split_ifs at ho
      · rw [mem_singleton] at ho; rw [ho]
      · simp at ho
    · simp only [Fin.mk_one, Fin.isValue, h1] at ho
      split_ifs at ho
      · rw [mem_singleton] at ho; rw [ho]
        simp [Chunk.key, Prod.Lex.toLex_le_toLex]
      · simp at ho
    · simp only [Fin.reduceFinMk, Fin.isValue, h2] at ho
      simp at ho
  have hne : (good 1 Lr).Nonempty := ⟨_, hmem⟩
  have hmin : (good 1 Lr).min' hne = Chunk.key ⟨1, (0, 0), (0 : Fin 3)⟩ :=
    le_antisymm (min'_le _ _ hmem) (le_min' _ _ _ hle)
  unfold rdoutMin
  rw [dif_pos hne, hmin]
  unfold decodeP
  beta_reduce
  split_ifs with hh
  · exact hh.choose_spec 0 (mem_pcs h0)
  · exact (hh ⟨val (0, 0), fun _ _ => rfl⟩).elim

/-- The history of the run, abbreviated. -/
abbrev H := (M.runFrom M.init evs).hist

theorem H_eq : H = [.inv 0 0 .write, .ret 0 0 none, .inv 1 0 .write, .ret 1 0 none, .inv 2 0 .read,
     .ret 2 0 (some (M.rdout 2 Lr))] := run_hist

theorem isWrite_H (w : OpId (Fin 3)) : IsWrite H w ↔ w = (0, 0) ∨ w = (1, 0) := by
  obtain ⟨c, i⟩ := w
  unfold IsWrite
  rw [H_eq]
  simp [and_comm]

theorem completed_w₁ : Completed H (0, 0) := ⟨none, by rw [H_eq]; simp⟩
theorem completed_w₂ : Completed H (1, 0) := ⟨none, by rw [H_eq]; simp⟩

theorem prec_12 : Precedes H (0, 0) (1, 0) :=
  ⟨1, 2, by omega, ⟨none, by rw [H_eq]; rfl⟩, ⟨.write, by rw [H_eq]; rfl⟩⟩
theorem prec_1r : Precedes H (0, 0) (2, 0) :=
  ⟨1, 4, by omega, ⟨none, by rw [H_eq]; rfl⟩, ⟨.read, by rw [H_eq]; rfl⟩⟩
theorem prec_2r : Precedes H (1, 0) (2, 0) :=
  ⟨3, 4, by omega, ⟨none, by rw [H_eq]; rfl⟩, ⟨.read, by rw [H_eq]; rfl⟩⟩

theorem ret_rd : Label.ret 2 0 (some (M.rdout 2 Lr)) ∈ H := by
  rw [H_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))

/-- The value assignment distinguishing the two writes. -/
def val₁₂ : OpId (Fin 3) → Fin 2 := fun w => if w = (1, 0) then 1 else 0

/-- **Line 16 of Algorithm 2 is not enough**: resolving its choice by the smallest timestamp gives an
algorithm that is not strongly safe (`n = 3`, `f = 1`, `k = 1`, replication). The read `(2, 0)` has no
concurrent write, both writes precede it and `w₁` precedes `w₂`, yet it returns `w₁`'s value. -/
theorem not_stronglySafe : ¬ StronglySafe M 0 := by
  intro hS
  obtain ⟨σ, hnd, hw, hc, hpw, hrd⟩ := hS evs
  have key := hrd val₁₂ (2, 0) (M.rdout 2 Lr) ret_rd (by
    intro w hw'
    rcases (isWrite_H w).1 hw' with rfl | rfl
    · exact Or.inl prec_1r
    · exact Or.inl prec_2r)
  rw [out_val] at key
  have ha : ((0 : Fin 3), 0) ∈ σ := hc _ ((isWrite_H _).2 (Or.inl rfl)) completed_w₁
  have hb : ((1 : Fin 3), 0) ∈ σ := hc _ ((isWrite_H _).2 (Or.inr rfl)) completed_w₂
  have hsub : ∀ w ∈ σ, w = (0, 0) ∨ w = (1, 0) := fun w h => (isWrite_H w).1 (hw w h)
  have hfilt : σ.filter (fun w => decide (Precedes H w (2, 0))) = σ := by
    rw [List.filter_eq_self]
    intro w h
    rcases hsub w h with rfl | rfl
    · simpa using prec_1r
    · simpa using prec_2r
  change val₁₂ (0, 0) = lastVal 0 val₁₂ (σ.filter (fun w => decide (Precedes H w (2, 0)))) at key
  rw [hfilt] at key
  have hσ : σ = [(0, 0), (1, 0)] := by
    rcases σ with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
    · simp at ha
    · simp at ha hb; rw [← hb] at ha; simp at ha
    · rcases hsub x (by simp) with rfl | rfl <;> rcases hsub y (by simp) with rfl | rfl
      · simp at hnd
      · rfl
      · simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
          forall_eq] at hpw
        exact absurd prec_12 hpw.1.1
      · simp at hnd
    · rcases hsub x (by simp) with rfl | rfl <;> rcases hsub y (by simp) with rfl | rfl <;>
        rcases hsub z (by simp) with rfl | rfl <;> simp at hnd
  rw [hσ] at key
  simp [lastVal, val₁₂] at key

/-- The same run also violates weak regularity (the read has no concurrent write). -/
theorem not_weakRegular : ¬ M.WeakRegular 0 := by
  intro hW
  obtain ⟨L, hnd, hrdL, hwL, hcL, hord, key⟩ := hW evs val₁₂ (2, 0) (M.rdout 2 Lr) ret_rd
  rw [out_val] at key
  have ha := hcL _ ((isWrite_H _).2 (Or.inl rfl)) completed_w₁
  have hb := hcL _ ((isWrite_H _).2 (Or.inr rfl)) completed_w₂
  have hsub : ∀ w ∈ L, w = (0, 0) ∨ w = (1, 0) ∨ w = (2, 0) := by
    intro w h
    by_cases hr : w = (2, 0)
    · exact Or.inr (Or.inr hr)
    · rcases (isWrite_H w).1 (hwL w h hr) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  have o12 := hord _ ha _ hb prec_12
  have o1r := hord _ ha _ hrdL prec_1r
  have o2r := hord _ hb _ hrdL prec_2r
  rcases L with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, t⟩⟩⟩⟩
  · simp at ha
  · simp at ha hb; rw [← hb] at ha; simp at ha
  · simp at ha hb hrdL
    rcases ha with rfl | rfl <;> rcases hb with h | h <;> rcases hrdL with h' | h' <;>
      simp_all
  · rcases hsub x (by simp) with rfl | rfl | rfl <;> rcases hsub y (by simp) with rfl | rfl | rfl <;>
      rcases hsub z (by simp) with rfl | rfl | rfl <;> simp_all [lastVal, val₁₂]
  · rcases hsub x (by simp) with rfl | rfl | rfl <;> rcases hsub y (by simp) with rfl | rfl | rfl <;>
      rcases hsub z (by simp) with rfl | rfl | rfl <;> rcases hsub u (by simp) with rfl | rfl | rfl <;>
      simp at hnd

end Podc.ReliableStorageSpace.Safe
