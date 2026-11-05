import Papers.PODC2024.NoBroadcastKSA.RunFacts

/-!
# Theorem 1 (repaired proof): no compositional broadcast abstraction is equivalent to k-SA

Assume `1 < k < n`, a compositional broadcast abstraction `S`, a well-formed algorithm `A`
solving k-set agreement on top of `S` (using broadcasts only), and an algorithm `B`
implementing `S` in `CAMP_n[k-SA]`. We build the adversarial executions of the paper, with the
upper layer of each process running copies of `A` instead of the paper's `sync-broadcast(synch)`
loop, and derive a contradiction.

Processes `p_0, …, p_k` (`pr i`); `kk = k - 1` is the paper's `p_k`, `z = k` is `p_{k+1}`.

1. Each early process `p_i` (`i < k - 1`) runs alone (`solo`): its copy decides (`Tf`), and
   decides its own proposal `f i` (`fin_copy`).
2. `Ok` = the objects decided by all early processes during their phase. `p_kk` runs alone;
   proposing to an object of `Ok` while its copy has not decided discards the copy (a *reset*:
   in the paper's execution, `p_{k+1}` will have to adopt `p_k`'s value on such an object, so
   it must hear from `p_k`). Resets are finitely many (`Ok` is finite, proposals are one-shot);
   the copy started after the last reset (at `Wk`) decides `f kk`.
3. `gZ`: `p_kk` until its last reset, then `p_z` forever, receiving the messages `p_kk` sent it
   before (`Rγ`); on objects of `Ok` decided by `p_kk` the k-SA objects answer `p_kk`'s value.
   `p_z`'s copy decides `f z`.
4. `αS`: the phases of `p_0, …, p_kk` one after the other, then `p_z` forever; `p_z` receives
   the messages of `p_kk` sent before its last reset at once, and the others after its copy
   decided. It is admissible, so `B` produces an execution of `S`; restricted to the messages of
   the final copies, it is (by compositionality) an execution of `A` on top of `S` in which
   `p_0, …, p_k` decide `f 0, …, f k`: k-SA-Agreement fails.
-/

namespace Podc.NoBroadcastKSA.Camp

open Classical

set_option linter.unusedSectionVars false

/-! ## A process alone -/

section SoloCopy

variable {P C V X O W : Type} [DecidableEq P] [DecidableEq C]
variable {A : Algo P C V} {B : BAlgo P (Msg C) X O W} {S : Set (BExec P (Msg C))} {k : ℕ}

lemma simView_nil (p : P) (v : V) (R : Set O) (F : P → Msg C → Prop) :
    simView A p v R F ([] : List (FLEv P (Msg C) X O W)) = [] := rfl

/-- **The copy of a process running alone decides its own proposal.** -/
theorem solo_copy (hSb : IsBroadcastAbstraction S) (hS : Compositional S)
    (hA : SolvesKSA k A S) (hAwf : A.WellFormed) (hB : Implements B k S) (hk : 1 ≤ k)
    (hB1 : B.OneShot) (par : RunPar P C V X O W) (hresp : ∀ o w, par.resp o w = w)
    (hnow : par.pendNow = []) (hlater : par.pendLater = []) (w0 : ℕ)
    (hw0 : simView A par.p par.v par.R par.F (lst A B par w0).h = [])
    (hnr : ∀ j ≥ w0, ∀ o w, prun A B par 0 j = some (.act par.p (.propose o w)) →
      ¬ (o ∈ par.R ∧ ¬ Decd A B par j))
    (hF : ∀ q m, ¬ par.F q m) :
    (∃ j, Decd A B par j) ∧ ∀ j ≥ w0, ∀ w, j % 4 = 0 →
      A.act par.p par.v (simView A par.p par.v par.R par.F (lst A B par j).h) =
        some (.decide w) → w = par.v := by
  have hd := distinct_solo par
  have hadm := solo_adm A B hk hB1 par hresp hnow hlater
  have hE : segEnd (Fin.elim0 : Fin 0 → ℕ) = 0 := by simp [segEnd]
  have := fin_copy hSb hS hA hAwf hB hd hadm w0 hw0 ?_ ?_
  · exact this
  · intro t ht o w h hc
    rw [hE] at ht
    have h' : prun A B par 0 t = some (.act par.p (.propose o w)) := by
      rw [← solo_eq A B par t]; exact h
    have hfh := fhist_catRun_fin A B Fin.elim0 Fin.elim0 par hd t
    rw [hE, zero_add] at hfh
    refine hnr t (by omega) o w h' ⟨hc.1, ?_⟩
    unfold Decd
    have := hc.2
    rw [hfh] at this
    simp [this]
  · intro t q m _ _; exact hF q m

end SoloCopy

/-- The data of the proof. -/
structure Ctx (n k : ℕ) (C V X O W : Type) where
  hk : 1 < k
  hkn : k + 1 ≤ n
  A : Algo (Fin n) C V
  B : BAlgo (Fin n) (Msg C) X O W
  f : Fin (k + 1) → V
  hf : Function.Injective f

namespace Ctx

variable {n k : ℕ} {C V X O W : Type} [DecidableEq C] (c : Ctx n k C V X O W)

/-- The process `p_i`. -/
def pr (i : Fin (k + 1)) : Fin n := Fin.castLE c.hkn i

lemma pr_injective : Function.Injective c.pr := Fin.castLE_injective c.hkn

/-- The paper's `p_k` (0-indexed `k - 1`). -/
def kk (_c : Ctx n k C V X O W) : Fin (k + 1) := ⟨k - 1, by omega⟩

/-- The paper's `p_{k+1}` (0-indexed `k`). -/
def z (_c : Ctx n k C V X O W) : Fin (k + 1) := Fin.last k

/-- The run of an early process `p_i` (`i < k - 1`). -/
def parE (i : Fin (k + 1)) : RunPar (Fin n) C V X O W :=
  ⟨c.pr i, c.f i, ∅, fun _ _ => False, fun _ w => w, [], []⟩

/-- The length of the phase of a run: until its copy has decided. -/
noncomputable def Tf (par : RunPar (Fin n) C V X O W) : ℕ :=
  if h : ∃ j, Decd c.A c.B par j then Nat.find h else 0

/-- The objects decided by every early process during its phase. -/
def Ok : Set O :=
  {o | ∀ i : Fin (k + 1), i.val + 1 < k → ∃ t < c.Tf (c.parE i), ∃ w,
    prun c.A c.B (c.parE i) 0 t = some (.dec (c.pr i) o w)}

/-- The run of `p_kk`: its copy is discarded when it proposes to an object of `Ok`. -/
def parK : RunPar (Fin n) C V X O W :=
  ⟨c.pr c.kk, c.f c.kk, c.Ok, fun _ _ => False, fun _ w => w, [], []⟩

/-- A reset of the copy of `p_kk` at slot `j`. -/
def IsReset (j : ℕ) : Prop :=
  ∃ o w, prun c.A c.B c.parK 0 j = some (.act (c.pr c.kk) (.propose o w)) ∧ o ∈ c.Ok ∧
    ¬ Decd c.A c.B c.parK j

/-- The start of the last copy of `p_kk` (after its last reset). -/
noncomputable def Wk : ℕ :=
  if h : ∃ W, ∀ j ≥ W, ¬ c.IsReset j then Nat.find h else 0

/-- The length of the phase of `p_kk`. -/
noncomputable def TK : ℕ := c.Tf c.parK

/-- `p_kk` decides `w` on `o` during its phase. -/
def KDec (o : O) (w : W) : Prop :=
  ∃ t < c.TK, prun c.A c.B c.parK 0 t = some (.dec (c.pr c.kk) o w)

/-- The answer of the k-SA objects to `p_z`: the value of `p_kk` on the objects of `Ok`
decided by `p_kk`, its own proposal otherwise. -/
noncomputable def respZ (o : O) (w : W) : W :=
  if h : o ∈ c.Ok ∧ ∃ w', c.KDec o w' then h.2.choose else w

/-- The messages of the final copies of the other processes, seen by the copy of `p_z`. -/
def Fz (q : Fin n) (m : Msg C) : Prop :=
  (∃ i : Fin (k + 1), i.val + 1 < k ∧ q = c.pr i ∧ ∃ t < c.Tf (c.parE i),
    prun c.A c.B (c.parE i) 0 t = some (.inv (c.pr i) m)) ∨
  (q = c.pr c.kk ∧ ∃ t, c.Wk ≤ t ∧ t < c.TK ∧ prun c.A c.B c.parK 0 t = some (.inv (c.pr c.kk) m))

/-- The messages sent to `p_z` in `β` at the times `s < hi` satisfying `pred`. -/
noncomputable def sendsZ (β : CExec (Fin n) (Msg C) X O W) (hi : ℕ) (pred : ℕ → Bool) :
    List (Fin n × X × ℕ) :=
  ((List.range hi).filter pred).filterMap fun s =>
    match β s with
    | some (.act q (.send d x)) => if d = c.pr c.z then some (q, x, s) else none
    | _ => none

/-- The messages `p_kk` sends to `p_z` before its last reset. -/
noncomputable def Rγ : List (Fin n × X × ℕ) := c.sendsZ (solo c.A c.B c.parK) c.Wk fun _ => true

/-- The run of `p_z` in `gZ`. -/
noncomputable def parZ' : RunPar (Fin n) C V X O W :=
  ⟨c.pr c.z, c.f c.z, ∅, c.Fz, c.respZ, c.Rγ, []⟩

/-- `p_kk` until its last reset, then `p_z` forever. -/
noncomputable def gZ : CExec (Fin n) (Msg C) X O W :=
  catRun c.A c.B (m := 1) (fun _ => c.parK) (fun _ => c.Wk) c.parZ'

/-- The runs of the phases of `αS`. -/
def segPar (j : Fin k) : RunPar (Fin n) C V X O W :=
  if j.val + 1 < k then c.parE (Fin.castSucc j) else c.parK

/-- The lengths of the phases. -/
noncomputable def segL (j : Fin k) : ℕ := c.Tf (c.segPar j)

/-- The phase of `p_kk`. -/
def lastSeg : Fin k := ⟨k - 1, by have := c.hk; omega⟩

/-- The start of the phase of `p_kk`. -/
noncomputable def offK : ℕ := segOff c.segL c.lastSeg

/-- The end of the phases. -/
noncomputable def E : ℕ := segEnd c.segL

/-- The phases (with any final run). -/
noncomputable def β : CExec (Fin n) (Msg C) X O W := catRun c.A c.B c.segPar c.segL c.parK

/-- The messages `p_kk` sends to `p_z` before its last reset, in `αS`. -/
noncomputable def Rα : List (Fin n × X × ℕ) :=
  c.sendsZ c.β c.E fun s => decide (c.offK ≤ s ∧ s < c.offK + c.Wk)

/-- The other messages sent to `p_z` during the phases. -/
noncomputable def Lrest : List (Fin n × X × ℕ) :=
  c.sendsZ c.β c.E fun s => !decide (c.offK ≤ s ∧ s < c.offK + c.Wk)

/-- The run of `p_z` in `αS`. -/
noncomputable def parZ : RunPar (Fin n) C V X O W :=
  ⟨c.pr c.z, c.f c.z, ∅, c.Fz, c.respZ, c.Rα, c.Lrest⟩

/-- The adversarial execution. -/
noncomputable def αS : CExec (Fin n) (Msg C) X O W := catRun c.A c.B c.segPar c.segL c.parZ

/-! ## Basic facts -/

lemma pr_val (i : Fin (k + 1)) : (c.pr i).val = i.val := rfl

lemma pr_kk_ne_z : c.pr c.kk ≠ c.pr c.z := by
  intro h; have := congrArg Fin.val h; simp [pr, kk, z] at this; have := c.hk; omega

lemma pr_early_ne_kk {i : Fin (k + 1)} (hi : i.val + 1 < k) : c.pr i ≠ c.pr c.kk := by
  intro h; have := congrArg Fin.val h; simp [pr, kk] at this; omega

lemma pr_early_ne_z {i : Fin (k + 1)} (hi : i.val + 1 < k) : c.pr i ≠ c.pr c.z := by
  intro h; have := congrArg Fin.val h; simp [pr, z] at this; omega

lemma not_decd_zero (par : RunPar (Fin n) C V X O W) : ¬ Decd c.A c.B par 0 := by
  simp [Decd, lst, LSt.init, simView]

/-- The phase length: the copy has decided after `Tf par` slots, not before. -/
lemma Tf_spec {par : RunPar (Fin n) C V X O W} (h : ∃ j, Decd c.A c.B par j) :
    Decd c.A c.B par (c.Tf par) ∧ (∀ j < c.Tf par, ¬ Decd c.A c.B par j) ∧ 0 < c.Tf par := by
  have e : c.Tf par = Nat.find h := by simp [Tf, h]
  rw [e]
  refine ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj, ?_⟩
  by_contra h0
  have : Nat.find h = 0 := by omega
  have h1 := Nat.find_spec h
  rw [this] at h1
  exact c.not_decd_zero par h1

/-- The copy decides at slot `Tf par - 1`, an `up` step. -/
lemma Tf_step {par : RunPar (Fin n) C V X O W} (h : ∃ j, Decd c.A c.B par j) :
    (c.Tf par - 1) % 4 = 0 ∧ ∃ w, c.A.act par.p par.v
      (simView c.A par.p par.v par.R par.F (lst c.A c.B par (c.Tf par - 1)).h) =
        some (.decide w) := by
  obtain ⟨h1, h2, h3⟩ := c.Tf_spec h
  refine decd_step c.A c.B par (h2 _ (by omega)) ?_
  rw [show c.Tf par - 1 + 1 = c.Tf par by omega]; exact h1

/-! ## Messages sent to `p_z` -/

lemma mem_sendsZ {β : CExec (Fin n) (Msg C) X O W} {hi : ℕ} {pred : ℕ → Bool} {q : Fin n} {x : X}
    {s : ℕ} : (q, x, s) ∈ c.sendsZ β hi pred ↔
      s < hi ∧ pred s = true ∧ β s = some (.act q (.send (c.pr c.z) x)) := by
  simp only [sendsZ, List.mem_filterMap, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨s', ⟨hs', hp⟩, h⟩
    split at h
    · rename_i q' d x' hβ
      split_ifs at h with hd
      cases h; subst hd; exact ⟨hs', hp, hβ⟩
    · cases h
  · rintro ⟨hs, hp, hβ⟩
    exact ⟨s, ⟨hs, hp⟩, by rw [hβ]; simp⟩

lemma sendsZ_time {β : CExec (Fin n) (Msg C) X O W} {hi : ℕ} {pred : ℕ → Bool}
    {e : Fin n × X × ℕ} (he : e ∈ c.sendsZ β hi pred) : e.2.2 < hi ∧ pred e.2.2 = true := by
  obtain ⟨q, x, s⟩ := e
  obtain ⟨h1, h2, -⟩ := c.mem_sendsZ.1 he
  exact ⟨h1, h2⟩

lemma filterMap_self_sublist {F : ℕ → Option ℕ} (hF : ∀ s y, F s = some y → y = s)
    (l : List ℕ) : (l.filterMap F).Sublist l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filterMap_cons]
    cases h : F a with
    | none => exact ih.cons a
    | some y => rw [hF a y h]; exact ih.cons_cons a

lemma sendsZ_nodup (β : CExec (Fin n) (Msg C) X O W) (hi : ℕ) (pred : ℕ → Bool) :
    ((c.sendsZ β hi pred).map fun e => e.2.2).Nodup := by
  unfold sendsZ
  rw [List.map_filterMap]
  refine (filterMap_self_sublist ?_ _).nodup (List.nodup_range.filter _)
  intro s y h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  split at he
  · split_ifs at he; cases he; rfl
  · cases he

/-! ## Step 2 (combinatorics): the resets of `p_kk` -/

lemma i0_early : (⟨0, by have := c.hk; omega⟩ : Fin (k + 1)).val + 1 < k := by
  have := c.hk; simp; omega

lemma Ok_finite : c.Ok.Finite := by
  set i0 : Fin (k + 1) := ⟨0, by have := c.hk; omega⟩
  have hsub : c.Ok ⊆ ⋃ t ∈ (Finset.range (c.Tf (c.parE i0)) : Set ℕ),
      {o | ∃ w, prun c.A c.B (c.parE i0) 0 t = some (.dec (c.pr i0) o w)} := by
    intro o ho
    obtain ⟨t, ht, w, h⟩ := ho i0 c.i0_early
    simp only [Set.mem_iUnion]
    exact ⟨t, by simpa using ht, w, h⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) ?_) hsub
  intro t _
  apply Set.Subsingleton.finite
  rintro o ⟨w, h⟩ o' ⟨w', h'⟩
  rw [h] at h'; cases h'; rfl

lemma reset_finite (hB1 : c.B.OneShot) : {j | c.IsReset j}.Finite := by
  have hsub : {j | c.IsReset j} ⊆ ⋃ o ∈ c.Ok,
      {j | ∃ w, prun c.A c.B c.parK 0 j = some (.act (c.pr c.kk) (.propose o w))} := by
    rintro j ⟨o, w, h, ho, -⟩
    simp only [Set.mem_iUnion]
    exact ⟨o, ho, w, h⟩
  refine Set.Finite.subset (Set.Finite.biUnion c.Ok_finite ?_) hsub
  intro o _
  apply Set.Subsingleton.finite
  rintro j ⟨w, h⟩ j' ⟨w', h'⟩
  exact propose_once c.A c.B c.parK hB1 h h'

lemma exists_W (hB1 : c.B.OneShot) : ∃ W, ∀ j ≥ W, ¬ c.IsReset j := by
  obtain ⟨M, hM⟩ := (c.reset_finite hB1).bddAbove
  exact ⟨M + 1, fun j hj h => by have := hM h; omega⟩

lemma Wk_eq (hB1 : c.B.OneShot) : c.Wk = Nat.find (c.exists_W hB1) := by simp [Wk, c.exists_W hB1]

lemma Wk_spec (hB1 : c.B.OneShot) : ∀ j ≥ c.Wk, ¬ c.IsReset j := by
  rw [c.Wk_eq hB1]; exact Nat.find_spec (c.exists_W hB1)

lemma Wk_reset (hB1 : c.B.OneShot) (h : 0 < c.Wk) : c.IsReset (c.Wk - 1) := by
  have hmin := Nat.find_min (c.exists_W hB1) (m := c.Wk - 1) (by rw [← c.Wk_eq hB1]; omega)
  push Not at hmin
  obtain ⟨j, hj, hr⟩ := hmin
  by_cases hjW : c.Wk ≤ j
  · exact absurd hr (c.Wk_spec hB1 j hjW)
  · rwa [show j = c.Wk - 1 by omega] at hr

lemma Wk_view (hB1 : c.B.OneShot) : simView c.A c.parK.p c.parK.v c.parK.R c.parK.F (lst c.A c.B c.parK c.Wk).h = [] := by
  by_cases h0 : c.Wk = 0
  · rw [h0]; rfl
  · obtain ⟨o, w, hp, ho, hnd⟩ := c.Wk_reset hB1 (by omega)
    rw [show c.Wk = c.Wk - 1 + 1 by omega, lst_h_succ c.A c.B c.parK 0 (c.Wk - 1), hp]
    simp only [Option.map_some, Option.toList_some]
    rw [simView_append]
    simp only [CStep.floc, CStep.bloc, simStep]
    rw [ite_eq_left ⟨ho, by simpa [Decd] using hnd⟩]

lemma distinct_gZ : Distinct (fun _ : Fin 1 => c.parK) c.parZ' :=
  ⟨fun i j _ => Subsingleton.elim i j, fun _ => c.pr_kk_ne_z⟩

lemma segEnd_gZ : segEnd (fun _ : Fin 1 => c.Wk) = c.Wk := by simp [segEnd]

lemma segOff_gZ (i : Fin 1) : segOff (fun _ : Fin 1 => c.Wk) i = 0 := by
  simp [segOff, Fin.lt_def, Fin.val_eq_zero]

lemma gZ_seg {s : ℕ} (hs : s < c.Wk) : c.gZ s = solo c.A c.B c.parK s := by
  unfold gZ
  rw [catRun_seg c.A c.B _ _ c.parZ' (i := 0) (by rw [c.segOff_gZ]; omega)
    (by rw [c.segOff_gZ]; omega), c.segOff_gZ, Nat.sub_zero, solo_eq]

/-! ## The phases of `αS` -/

lemma segPar_early {j : Fin k} (h : j.val + 1 < k) : c.segPar j = c.parE (Fin.castSucc j) := by
  simp [segPar, h]

lemma lastSeg_val : c.lastSeg.val = k - 1 := rfl

lemma segPar_last : c.segPar c.lastSeg = c.parK := by
  unfold segPar; rw [ite_eq_right]; simp only [lastSeg]; have := c.hk; omega

lemma castSucc_lastSeg : Fin.castSucc c.lastSeg = c.kk := by
  ext; simp [lastSeg, kk]

lemma eq_lastSeg {j : Fin k} (h : ¬ j.val + 1 < k) : j = c.lastSeg := by
  ext; simp [lastSeg]; omega

lemma segPar_p (j : Fin k) : (c.segPar j).p = c.pr (Fin.castSucc j) := by
  by_cases h : j.val + 1 < k
  · rw [c.segPar_early h]; rfl
  · rw [c.eq_lastSeg h, c.segPar_last, c.castSucc_lastSeg]; rfl

lemma segPar_resp (j : Fin k) (o : O) (w : W) : (c.segPar j).resp o w = w := by
  unfold segPar; split_ifs <;> rfl

lemma segPar_pend (j : Fin k) : (c.segPar j).pendNow = [] ∧ (c.segPar j).pendLater = [] := by
  unfold segPar; split_ifs <;> exact ⟨rfl, rfl⟩

lemma segPar_F (j : Fin k) (q : Fin n) (m : Msg C) : ¬ (c.segPar j).F q m := by
  unfold segPar; split_ifs <;> exact id

lemma pr_castSucc_ne_z (j : Fin k) : c.pr (Fin.castSucc j) ≠ c.pr c.z := by
  intro h; have := congrArg Fin.val h; simp [pr, z] at this; omega

lemma distinct_αS : Distinct c.segPar c.parZ := by
  refine ⟨fun i j h => ?_, fun j => ?_⟩
  · have h' : c.pr (Fin.castSucc i) = c.pr (Fin.castSucc j) := by
      rw [← c.segPar_p, ← c.segPar_p]; exact h
    exact Fin.castSucc_injective _ (c.pr_injective h')
  · rw [c.segPar_p]; exact c.pr_castSucc_ne_z j

lemma segL_last : c.segL c.lastSeg = c.TK := by simp [segL, c.segPar_last, TK]

lemma offK_add_TK_le : c.offK + c.TK ≤ c.E := by
  rw [← c.segL_last]; exact segOff_add_le_end c.segL c.lastSeg

lemma αS_eq_β {s : ℕ} (hs : s < c.E) : c.αS s = c.β s := by
  obtain ⟨i, h1, h2⟩ := exists_seg_of_lt_end c.segL hs
  unfold αS β
  rw [catRun_seg c.A c.B _ _ _ h1 h2, catRun_seg c.A c.B _ _ _ h1 h2]

lemma αS_K {s : ℕ} (hs : s < c.TK) : c.αS (c.offK + s) = prun c.A c.B c.parK c.offK s := by
  unfold αS
  rw [catRun_seg c.A c.B _ _ _ (i := c.lastSeg) (by unfold offK; omega)
    (by rw [c.segL_last]; unfold offK; omega), c.segPar_last]
  unfold offK; congr 1; omega

/-- The message `p_z` receives from a step, if it is a send to `p_z`. -/
def sendOf (o : Option (CStep (Fin n) (Msg C) X O W)) : Option (Fin n × X) :=
  match o with
  | some (.act q (.send d x)) => if d = c.pr c.z then some (q, x) else none
  | _ => none

lemma sendOf_off (par : RunPar (Fin n) C V X O W) (off s : ℕ) :
    c.sendOf (prun c.A c.B par off s) = c.sendOf (prun c.A c.B par 0 s) := by
  cases h0 : prun c.A c.B par 0 s with
  | none =>
    cases h1 : prun c.A c.B par off s with
    | none => rfl
    | some st =>
      by_cases hr : ∃ p q x t, st = .recv p q x t
      · obtain ⟨p, q, x, t, rfl⟩ := hr; rfl
      · push Not at hr
        rw [prun_off c.A c.B par h1 hr] at h0; cases h0
  | some st =>
    by_cases hr : ∃ p q x t, st = .recv p q x t
    · obtain ⟨p, q, x, t, rfl⟩ := hr
      cases h1 : prun c.A c.B par off s with
      | none => rfl
      | some st' =>
        by_cases hr' : ∃ p q x t, st' = .recv p q x t
        · obtain ⟨p', q', x', t', rfl⟩ := hr'; rfl
        · push Not at hr'
          have := prun_off c.A c.B par (off' := 0) h1 hr'
          rw [h0] at this; cases this; exact absurd rfl (hr' _ _ _ _)
    · push Not at hr
      rw [prun_off c.A c.B par h0 hr]

lemma sendsZ_map (β : CExec (Fin n) (Msg C) X O W) (hi : ℕ) (pred : ℕ → Bool) :
    (c.sendsZ β hi pred).map (fun e => (e.1, e.2.1)) =
      ((List.range hi).filter pred).filterMap fun s => c.sendOf (β s) := by
  unfold sendsZ
  rw [List.map_filterMap]
  congr 1
  funext s
  unfold sendOf
  split <;> (try split_ifs) <;> (try rfl)

lemma range_filter_window {a b hi : ℕ} (h : a + b ≤ hi) {Q : ℕ → Prop} {inst : DecidablePred Q}
    (hQ : ∀ s, Q s ↔ a ≤ s ∧ s < a + b) :
    (List.range hi).filter (fun s => @decide (Q s) (inst s)) = (List.range b).map (a + ·) := by
  obtain ⟨d, rfl⟩ : ∃ d, hi = a + b + d := ⟨hi - (a + b), by omega⟩
  rw [List.range_add, List.range_add]
  simp only [List.filter_append, List.filter_map]
  have h1 : (List.range a).filter (fun s => @decide (Q s) (inst s)) = [] := by
    rw [List.filter_eq_nil_iff]; intro s hs; simp only [List.mem_range] at hs
    simp only [decide_eq_true_eq, hQ]; omega
  have h2 : (List.range b).filter ((fun s => @decide (Q s) (inst s)) ∘ (a + ·)) =
      List.range b := by
    rw [List.filter_eq_self]; intro s hs; simp only [List.mem_range] at hs
    simp only [Function.comp, decide_eq_true_eq, hQ]; omega
  have h3 : (List.range d).filter ((fun s => @decide (Q s) (inst s)) ∘ (a + b + ·)) = [] := by
    rw [List.filter_eq_nil_iff]; intro s hs
    simp only [Function.comp, decide_eq_true_eq, hQ]; omega
  rw [h1, h2, h3]; simp

lemma β_K {s : ℕ} (hs : s < c.TK) : c.β (c.offK + s) = prun c.A c.B c.parK c.offK s := by
  unfold β
  rw [catRun_seg c.A c.B _ _ _ (i := c.lastSeg) (by unfold offK; omega)
    (by rw [c.segL_last]; unfold offK; omega), c.segPar_last]
  unfold offK; congr 1; omega

lemma αS_dec {t : ℕ} {p : Fin n} {o : O} {w : W} (h : c.αS t = some (.dec p o w)) :
    (∃ j : Fin k, p = c.pr (Fin.castSucc j) ∧ ∃ t' < c.segL j,
      prun c.A c.B (c.segPar j) 0 t' = some (.dec p o w)) ∨
    (p = c.pr c.z ∧ ∃ w0, w = c.respZ o w0) := by
  rcases catRun_step c.A c.B _ _ _ c.distinct_αS h with ⟨j, hp, h1, h2, h3⟩ | ⟨hp, -, h3⟩
  · simp only [CStep.proc] at hp
    left
    refine ⟨j, by rw [hp, c.segPar_p], t - segOff c.segL j, by omega, ?_⟩
    exact prun_off c.A c.B _ h3 (by intro _ _ _ _ h; cases h)
  · simp only [CStep.proc] at hp
    obtain ⟨-, -, w0, -, hw⟩ := prun_dec c.A c.B _ h3
    exact Or.inr ⟨hp, w0, hw⟩

lemma card_segProcs : (Finset.univ.image fun j : Fin k => c.pr (Fin.castSucc j)).card ≤ k :=
  Finset.card_image_le.trans (by simp)

/-- A phase in which the object `o` is not decided, when `p_z` does not adopt `p_kk`'s value. -/
noncomputable def missing (o : O) : Fin k :=
  if h : ∃ i : Fin (k + 1), i.val + 1 < k ∧ ∀ t < c.Tf (c.parE i), ∀ w,
      prun c.A c.B (c.parE i) 0 t ≠ some (.dec (c.pr i) o w) then
    ⟨h.choose.val, by have := h.choose_spec.1; omega⟩
  else c.lastSeg

lemma missing_spec {o : O} (h : ¬ (o ∈ c.Ok ∧ ∃ w', c.KDec o w')) :
    ∀ t < c.segL (c.missing o), ∀ w,
      prun c.A c.B (c.segPar (c.missing o)) 0 t ≠
        some (.dec (c.pr (Fin.castSucc (c.missing o))) o w) := by
  unfold missing
  split_ifs with hex
  · obtain ⟨hi, hall⟩ := hex.choose_spec
    have e : Fin.castSucc (⟨hex.choose.val, by omega⟩ : Fin k) = hex.choose := by ext; rfl
    have hj : (⟨hex.choose.val, by omega⟩ : Fin k).val + 1 < k := hi
    simp only [segL, c.segPar_early hj, e]
    exact hall
  · have ho : o ∈ c.Ok := by
      intro i hi
      by_contra hno
      apply hex
      refine ⟨i, hi, fun t ht w hw => hno ⟨t, ht, w, hw⟩⟩
    have hk : ¬ ∃ w', c.KDec o w' := fun hk => h ⟨ho, hk⟩
    simp only [segL, c.segPar_last, c.castSucc_lastSeg]
    intro t ht w hw
    exact hk ⟨w, t, ht, hw⟩

/-! ## The derived execution of `A` -/

/-- The start of the copy of the process of phase `j`, relative to the phase. -/
noncomputable def wsLoc (j : Fin k) : ℕ := if j.val + 1 = k then c.Wk else 0

/-- The start of the final copies. -/
noncomputable def wsS (p : Fin n) : ℕ :=
  if h : p.val < k then segOff c.segL ⟨p.val, h⟩ + c.wsLoc ⟨p.val, h⟩ else c.E

/-- The messages of the final copies. -/
def MsS : Set (Fin n × Msg C) :=
  {x | (x.1 = c.pr c.z ∧ ∃ t ≥ c.E, c.αS t = some (.inv x.1 x.2)) ∨
    ∃ j : Fin k, x.1 = c.pr (Fin.castSucc j) ∧ ∃ t, c.wsLoc j ≤ t ∧ t < c.segL j ∧
      prun c.A c.B (c.segPar j) 0 t = some (.inv x.1 x.2)}

/-- The parameters of the copies. -/
noncomputable def cpS : CopyPar (Fin n) C V O :=
  ⟨fun p => if h : p.val < k + 1 then c.f ⟨p.val, h⟩ else c.f 0,
   fun p => if p = c.pr c.kk then c.Ok else ∅,
   fun p => if p = c.pr c.z then c.Fz else fun _ _ => False⟩

lemma wsLoc_last : c.wsLoc c.lastSeg = c.Wk := by
  unfold wsLoc; rw [ite_eq_left]; simp [lastSeg]; have := c.hk; omega

lemma wsLoc_early {j : Fin k} (h : j.val + 1 < k) : c.wsLoc j = 0 := by
  unfold wsLoc; rw [ite_eq_right]; omega

lemma wsS_seg (j : Fin k) : c.wsS (c.pr (Fin.castSucc j)) = segOff c.segL j + c.wsLoc j := by
  simp [wsS, pr]

lemma wsS_z : c.wsS (c.pr c.z) = c.E := by simp [wsS, pr, z]

lemma cpS_seg (j : Fin k) : c.cpS.v (c.pr (Fin.castSucc j)) = (c.segPar j).v ∧
    c.cpS.R (c.pr (Fin.castSucc j)) = (c.segPar j).R ∧
    c.cpS.F (c.pr (Fin.castSucc j)) = (c.segPar j).F := by
  by_cases h : j.val + 1 < k
  · rw [c.segPar_early h]
    have hne : c.pr (Fin.castSucc j) ≠ c.pr c.kk := c.pr_early_ne_kk (i := Fin.castSucc j) h
    refine ⟨?_, ?_, ?_⟩
    · simp only [cpS, parE, pr, Fin.val_castLE, Fin.val_castSucc]
      rw [dite_eq_left (by omega)]; rfl
    · simp [cpS, parE, hne]
    · simp [cpS, parE, c.pr_castSucc_ne_z j]
  · rw [c.eq_lastSeg h, c.segPar_last, c.castSucc_lastSeg]
    refine ⟨?_, ?_, ?_⟩
    · simp [cpS, parK, pr, kk]
    · simp [cpS, parK]
    · simp [cpS, parK, c.pr_kk_ne_z]

lemma cpS_z : c.cpS.v (c.pr c.z) = c.parZ.v ∧ c.cpS.R (c.pr c.z) = c.parZ.R ∧
    c.cpS.F (c.pr c.z) = c.parZ.F := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cpS, parZ, pr, z, Fin.last]
  · simp [cpS, parZ, Ne.symm c.pr_kk_ne_z]
  · simp [cpS, parZ]

lemma copyView_seg (j : Fin k) (t : ℕ) :
    copyView c.A c.cpS c.αS (c.pr (Fin.castSucc j)) t =
      simView c.A (c.segPar j).p (c.segPar j).v (c.segPar j).R (c.segPar j).F
        (fhist c.αS (c.pr (Fin.castSucc j)) t) := by
  obtain ⟨h1, h2, h3⟩ := c.cpS_seg j
  unfold copyView; rw [h1, h2, h3, c.segPar_p]

lemma copyView_z (t : ℕ) : copyView c.A c.cpS c.αS (c.pr c.z) t =
    simView c.A c.parZ.p c.parZ.v c.parZ.R c.parZ.F (fhist c.αS (c.pr c.z) t) := by
  obtain ⟨h1, h2, h3⟩ := c.cpS_z
  unfold copyView; rw [h1, h2, h3]; rfl

lemma fhist_seg (j : Fin k) {t : ℕ} (ht : t ≤ c.segL j) :
    fhist c.αS (c.pr (Fin.castSucc j)) (segOff c.segL j + t) = (lst c.A c.B (c.segPar j) t).h := by
  rw [← c.segPar_p]; exact fhist_catRun_seg c.A c.B _ _ _ c.distinct_αS j ht

lemma fhist_z (t : ℕ) : fhist c.αS (c.pr c.z) (c.E + t) = (lst c.A c.B c.parZ t).h :=
  fhist_catRun_fin c.A c.B _ _ c.parZ c.distinct_αS t

/-- A step of the process of phase `j` in `αS` is a step of its run, in its phase. -/
lemma αS_seg_step {j : Fin k} {t : ℕ} {s : CStep (Fin n) (Msg C) X O W}
    (h : c.αS t = some s) (hp : s.proc = c.pr (Fin.castSucc j)) :
    segOff c.segL j ≤ t ∧ t < segOff c.segL j + c.segL j ∧
      prun c.A c.B (c.segPar j) (segOff c.segL j) (t - segOff c.segL j) = some s := by
  have := catRun_proc_seg c.A c.B _ _ _ c.distinct_αS h (by rw [c.segPar_p]; exact hp)
  refine ⟨this.1, this.2, ?_⟩
  rw [← catRun_seg c.A c.B _ _ c.parZ this.1 this.2]; exact h

lemma αS_z_step {t : ℕ} {s : CStep (Fin n) (Msg C) X O W} (h : c.αS t = some s)
    (hp : s.proc = c.pr c.z) :
    c.E ≤ t ∧ prun c.A c.B c.parZ c.E (t - c.E) = some s := by
  have := catRun_proc_fin c.A c.B _ _ _ c.distinct_αS h hp
  refine ⟨this, ?_⟩
  unfold E
  rw [← catRun_fin c.A c.B _ _ c.parZ this]; exact h

lemma pr_cases (i : Fin (k + 1)) : i = c.z ∨ ∃ j : Fin k, i = Fin.castSucc j := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact Or.inr ⟨j, rfl⟩
  · exact Or.inl rfl

/-- The derived execution of `A`. -/
noncomputable def DS : AExec (Fin n) (Msg C) V :=
  derive c.A c.cpS c.αS c.MsS (Set.range c.pr) c.wsS {c.parZ.p}

lemma DS_dec {t : ℕ} {p : Fin n} {w : V} (hα : c.αS t = some (.up p))
    (hp : p ∈ Set.range c.pr) (hws : c.wsS p ≤ t)
    (hact : c.A.act p (c.cpS.v p) (copyView c.A c.cpS c.αS p t) = some (.decide w)) :
    c.DS.st t = some (.dec p w) := by
  simp only [DS, derive, hα]
  rw [ite_eq_left ⟨hp, hws⟩, hact]

section Proof

variable {S : Set (BExec (Fin n) (Msg C))} (hSb : IsBroadcastAbstraction S)
  (hS : Compositional S) (hA : SolvesKSA k c.A S) (hAwf : c.A.WellFormed) (hB1 : c.B.OneShot)
  (hB : Implements c.B k S)

include hSb hS hA hAwf hB1 hB

/-! ## Step 1: the early processes -/

/-- An early process alone: its copy decides, and decides its own proposal. -/
lemma early_copy {i : Fin (k + 1)} (_hi : i.val + 1 < k) :
    (∃ j, Decd c.A c.B (c.parE i) j) ∧ ∀ j, ∀ w, j % 4 = 0 →
      c.A.act (c.parE i).p (c.parE i).v (simView c.A (c.parE i).p (c.parE i).v (c.parE i).R
        (c.parE i).F (lst c.A c.B (c.parE i) j).h) = some (.decide w) → w = c.f i := by
  have := solo_copy hSb hS hA hAwf hB (by have := c.hk; omega) hB1 (c.parE i)
    (fun _ _ => rfl) rfl rfl 0 rfl (fun _ _ _ _ _ h => h.1) (fun _ _ h => h)
  exact ⟨this.1, fun j w hj h => this.2 j (Nat.zero_le _) w hj h⟩

/-! ## Step 2: the resetting process `p_kk` -/

/-- `p_kk` alone: the copy started after the last reset decides its own proposal. -/
lemma kk_copy : (∃ j, Decd c.A c.B c.parK j) ∧ ∀ j ≥ c.Wk, ∀ w, j % 4 = 0 →
    c.A.act c.parK.p c.parK.v (simView c.A c.parK.p c.parK.v c.parK.R c.parK.F
      (lst c.A c.B c.parK j).h) = some (.decide w) → w = c.f c.kk :=
  solo_copy hSb hS hA hAwf hB (by have := c.hk; omega) hB1 c.parK (fun _ _ => rfl) rfl rfl c.Wk
    (c.Wk_view hB1) (fun j hj o w h hc => c.Wk_spec hB1 j hj ⟨o, w, h, hc.1, hc.2⟩)
    (fun _ _ h => h)

lemma reset_lt_TK {j : ℕ} (h : c.IsReset j) : j < c.TK := by
  obtain ⟨-, -, -, -, hnd⟩ := h
  by_contra hj
  exact hnd (decd_mono c.A c.B c.parK (show c.TK ≤ j by omega)
    (c.Tf_spec (c.kk_copy hSb hS hA hAwf hB1 hB).1).1)

lemma Wk_le : c.Wk ≤ c.TK - 1 := by
  by_cases h0 : c.Wk = 0
  · omega
  · have hr := c.Wk_reset hB1 (by omega)
    have h1 := c.reset_lt_TK hSb hS hA hAwf hB1 hB hr
    obtain ⟨o, w, hp, -, -⟩ := hr
    have h2 := (prun_actR c.A c.B c.parK hp).1
    have h3 := (c.Tf_step (c.kk_copy hSb hS hA hAwf hB1 hB).1).1
    unfold TK at h1 ⊢
    omega

/-! ## Step 3: `p_kk` until its last reset, then `p_z` -/

/-- A value `p_z` adopts was proposed by `p_kk` before its last reset. -/
lemma respZ_prop {o : O} (h : o ∈ c.Ok ∧ ∃ w', c.KDec o w') :
    ∃ t < c.Wk, prun c.A c.B c.parK 0 t = some (.act (c.pr c.kk) (.propose o h.2.choose)) := by
  obtain ⟨t, ht, hdec⟩ := h.2.choose_spec
  obtain ⟨hj, -, w0, hprop, hw⟩ := prun_dec c.A c.B c.parK hdec
  have hw' : h.2.choose = w0 := hw
  rw [hw']
  refine ⟨t - 1, ?_, hprop⟩
  by_contra hlt
  have hkd := c.kk_copy hSb hS hA hAwf hB1 hB
  exact c.Wk_spec hB1 (t - 1) (by omega)
    ⟨o, w0, hprop, h.1, (c.Tf_spec hkd.1).2.1 (t - 1) (by unfold TK at ht; omega)⟩

lemma gZ_adm : Adm c.B k {c.parZ'.p} c.gZ := by
  have hd := c.distinct_gZ
  refine catRun_adm c.A c.B _ _ c.parZ' (by have := c.hk; omega) hB1 hd (fun _ _ _ => rfl)
    (fun _ => ⟨rfl, rfl⟩) ?_ ?_ ?_ ?_ ?_
  · intro o w
    by_cases h : o ∈ c.Ok ∧ ∃ w', c.KDec o w'
    · right
      have e : c.parZ'.resp o w = h.2.choose := by
        show c.respZ o w = _; unfold respZ; rw [dite_eq_left h]
      rw [e]
      obtain ⟨t, ht, hp⟩ := c.respZ_prop hSb hS hA hAwf hB1 hB h
      refine ⟨t, by rw [c.segEnd_gZ]; exact ht, c.pr c.kk, ?_⟩
      show c.gZ t = _
      rw [c.gZ_seg ht, solo_eq]; exact hp
    · left; show c.respZ o w = w; unfold respZ; rw [dite_eq_right h]
  · intro q x s
    show (q, x, s) ∈ c.Rγ ++ [] ↔ s < segEnd (fun _ : Fin 1 => c.Wk) ∧ c.gZ s = _
    rw [List.append_nil, Rγ, c.mem_sendsZ, c.segEnd_gZ]
    constructor
    · rintro ⟨hs, -, h⟩; exact ⟨hs, by rw [c.gZ_seg hs]; exact h⟩
    · rintro ⟨hs, h⟩; exact ⟨hs, rfl, by rw [← c.gZ_seg hs]; exact h⟩
  · show ((c.Rγ ++ []).map fun (e : Fin n × X × ℕ) => e.2.2).Nodup
    rw [List.append_nil]
    exact c.sendsZ_nodup _ _ _
  · intro h; exact absurd rfl h
  · intro o f hf
    refine agree_of_bound o (fun q t t' w w' h h' =>
      catRun_dec_uniq c.A c.B _ _ c.parZ' hB1 hd h h') {c.pr c.kk, c.pr c.z}
      (by have := c.hk; exact (Finset.card_le_two).trans (by omega)) ?_ f hf
    intro t p w h
    refine ⟨p, ?_, t, h⟩
    rcases catRun_step c.A c.B _ _ c.parZ' hd h with ⟨i, hp, -⟩ | ⟨hp, -⟩ <;>
      simp only [CStep.proc] at hp
    · simp [hp, parK]
    · simp [hp, parZ']

/-- `p_z` in `gZ`: its copy decides, and decides its own proposal. -/
lemma z_copy : (∃ j, Decd c.A c.B c.parZ' j) ∧ ∀ j, ∀ w, j % 4 = 0 →
    c.A.act c.parZ'.p c.parZ'.v (simView c.A c.parZ'.p c.parZ'.v c.parZ'.R c.parZ'.F
      (lst c.A c.B c.parZ' j).h) = some (.decide w) → w = c.f c.z := by
  have hd := c.distinct_gZ
  have hadm := c.gZ_adm hSb hS hA hAwf hB1 hB
  have hbc := hSb _ (hB _ _ hadm)
  have := fin_copy hSb hS hA hAwf hB hd hadm 0 rfl ?_ ?_
  · exact ⟨this.1, fun j w hj h => this.2 j (Nat.zero_le _) w hj h⟩
  · intro t _ o w _ hc; exact hc.1
  · intro t q m hq hdl hFz
    obtain ⟨t', -, h'⟩ := hbc.validity t _ q m (proj_ev_eq_some.2 ⟨_, hdl, rfl⟩)
    obtain ⟨st, hst, htoB⟩ := proj_ev_eq_some.1 h'
    rw [CStep.toB_eq_bc] at htoB
    subst htoB
    rcases catRun_step c.A c.B _ _ c.parZ' hd hst with ⟨i, hp, -, h2, h3⟩ | ⟨hp, -⟩
    · simp only [CStep.proc] at hp
      rw [c.segOff_gZ, Nat.sub_zero] at h3
      rw [c.segOff_gZ, zero_add] at h2
      rcases hFz with ⟨i', hi', hq', -⟩ | ⟨-, t'', h1, -, h4⟩
      · exact c.pr_early_ne_kk hi' (hq'.symm.trans hp)
      · subst hp
        have := inv_once c.A c.B c.parK h3 h4
        omega
    · simp only [CStep.proc] at hp
      exact hq hp

lemma Rα_map : c.Rα.map (fun e => (e.1, e.2.1)) = c.Rγ.map (fun e => (e.1, e.2.1)) := by
  have hWT : c.Wk ≤ c.TK := by have := c.Wk_le hSb hS hA hAwf hB1 hB; omega
  unfold Rα Rγ
  rw [c.sendsZ_map, c.sendsZ_map,
    range_filter_window (Q := fun s => c.offK ≤ s ∧ s < c.offK + c.Wk)
      (by have := c.offK_add_TK_le; omega) (fun _ => Iff.rfl),
    List.filter_eq_self.2 (by simp), List.filterMap_map]
  apply List.filterMap_congr
  intro s hs
  simp only [List.mem_range] at hs
  simp only [Function.comp, c.β_K (show s < c.TK by omega), solo_eq, c.sendOf_off]

/-! ## Step 4: the adversarial execution `αS` -/

/-- Until its copy decides, `p_z` behaves in `αS` as in `gZ`. -/
lemma parZ_agree : ∀ j ≤ c.Tf c.parZ', lst c.A c.B c.parZ j = lst c.A c.B c.parZ' j :=
  lst_agree c.A c.B c.parZ c.parZ' rfl rfl rfl rfl rfl (c.Rα_map hSb hS hA hAwf hB1 hB)
    (c.Tf_spec (c.z_copy hSb hS hA hAwf hB1 hB).1).2.1

lemma parZ_decd : Decd c.A c.B c.parZ (c.Tf c.parZ') := by
  have h := (c.Tf_spec (c.z_copy hSb hS hA hAwf hB1 hB).1).1
  unfold Decd at h ⊢
  rw [c.parZ_agree hSb hS hA hAwf hB1 hB _ le_rfl]
  exact h

lemma αS_adm : Adm c.B k {c.parZ.p} c.αS := by
  have hd := c.distinct_αS
  have hWT : c.Wk ≤ c.TK := by have := c.Wk_le hSb hS hA hAwf hB1 hB; omega
  have hKE := c.offK_add_TK_le
  refine catRun_adm c.A c.B _ _ c.parZ (by have := c.hk; omega) hB1 hd c.segPar_resp
    c.segPar_pend ?_ ?_ ?_ ?_ ?_
  · intro o w
    by_cases h : o ∈ c.Ok ∧ ∃ w', c.KDec o w'
    · right
      have e : c.parZ.resp o w = h.2.choose := by
        show c.respZ o w = _; unfold respZ; rw [dite_eq_left h]
      rw [e]
      obtain ⟨t, ht, hp⟩ := c.respZ_prop hSb hS hA hAwf hB1 hB h
      refine ⟨c.offK + t, by unfold E at hKE; omega, c.pr c.kk, ?_⟩
      show c.αS _ = _
      rw [c.αS_K (by omega)]
      exact prun_off c.A c.B c.parK hp (by intro _ _ _ _ h; cases h)
    · left; show c.respZ o w = w; unfold respZ; rw [dite_eq_right h]
  · intro q x s
    show (q, x, s) ∈ c.Rα ++ c.Lrest ↔ s < c.E ∧ c.αS s = _
    rw [List.mem_append, Rα, Lrest, c.mem_sendsZ, c.mem_sendsZ]
    constructor
    · rintro (⟨hs, -, h⟩ | ⟨hs, -, h⟩) <;> exact ⟨hs, by rw [c.αS_eq_β hs]; exact h⟩
    · rintro ⟨hs, h⟩
      rw [c.αS_eq_β hs] at h
      by_cases hw : c.offK ≤ s ∧ s < c.offK + c.Wk
      · exact Or.inl ⟨hs, by simp [hw], h⟩
      · exact Or.inr ⟨hs, by simp [hw], h⟩
  · show ((c.Rα ++ c.Lrest).map fun (e : Fin n × X × ℕ) => e.2.2).Nodup
    rw [List.map_append]
    refine (c.sendsZ_nodup _ _ _).append (c.sendsZ_nodup _ _ _) ?_
    intro a ha hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨e', he', hee⟩ := List.mem_map.1 hb
    have h1 := (c.sendsZ_time he).2
    have h2 := (c.sendsZ_time he').2
    rw [hee] at h2
    simp at h1 h2
    omega
  · intro _; exact ⟨_, c.parZ_decd hSb hS hA hAwf hB1 hB⟩
  · intro o f hf
    refine agree_of_bound o (fun q t t' w w' h h' =>
      catRun_dec_uniq c.A c.B _ _ c.parZ hB1 hd h h') ?_ ?_ ?_ f hf
    · exact if h : o ∈ c.Ok ∧ ∃ w', c.KDec o w' then
        Finset.univ.image fun j : Fin k => c.pr (Fin.castSucc j)
      else insert (c.pr c.z) ((Finset.univ.image fun j : Fin k => c.pr (Fin.castSucc j)).erase
        (c.pr (Fin.castSucc (c.missing o))))
    · split_ifs with h
      · exact c.card_segProcs
      · refine (Finset.card_insert_le _ _).trans ?_
        have hmem : c.pr (Fin.castSucc (c.missing o)) ∈
            Finset.univ.image fun j : Fin k => c.pr (Fin.castSucc j) := by simp
        rw [Finset.card_erase_of_mem hmem]
        have := c.card_segProcs
        have h0 : 0 < (Finset.univ.image fun j : Fin k => c.pr (Fin.castSucc j)).card :=
          Finset.card_pos.2 ⟨_, hmem⟩
        omega
    · intro t p w hdec
      split_ifs with h
      · rcases c.αS_dec hdec with ⟨j, rfl, -⟩ | ⟨rfl, w0, hw⟩
        · exact ⟨_, by simp, t, hdec⟩
        · have e : c.respZ o w0 = h.2.choose := by unfold respZ; rw [dite_eq_left h]
          obtain ⟨t1, ht1, h1⟩ := h.2.choose_spec
          refine ⟨c.pr c.kk, ?_, c.offK + t1, ?_⟩
          · rw [← c.castSucc_lastSeg]; simp
          · show c.αS _ = _
            rw [c.αS_K ht1, hw, e]
            exact prun_off c.A c.B c.parK h1 (by intro _ _ _ _ h; cases h)
      · refine ⟨p, ?_, t, hdec⟩
        rcases c.αS_dec hdec with ⟨j, rfl, t', ht', h'⟩ | ⟨rfl, -⟩
        · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, by simp⟩)
          intro hjj
          have hj : j = c.missing o :=
            Fin.castSucc_injective _ (c.pr_injective hjj)
          subst hj
          exact c.missing_spec h t' ht' w h'
        · exact Finset.mem_insert_self _ _

/-! ## Step 4 (end): the derived execution violates k-SA-Agreement -/

/-- The process of a phase delivers only its own messages (it runs as if alone). -/
lemma seg_deliver_own {j : Fin k} {t : ℕ} {q : Fin n} {m : Msg C}
    (h : c.αS t = some (.act (c.pr (Fin.castSucc j)) (.deliver q m))) :
    q = c.pr (Fin.castSucc j) := by
  obtain ⟨-, -, h3⟩ := c.αS_seg_step h rfl
  have h4 := prun_off c.A c.B _ (off' := 0) h3 (by intro _ _ _ _ h; cases h)
  have hadm := solo_adm c.A c.B (k := k) (by have := c.hk; omega) hB1 (c.segPar j)
    (c.segPar_resp j) (c.segPar_pend j).1 (c.segPar_pend j).2
  have hbc := hSb _ (hB _ _ hadm)
  have h5 : solo c.A c.B (c.segPar j) (t - segOff c.segL j) =
      some (.act (c.pr (Fin.castSucc j)) (.deliver q m)) := by rw [solo_eq]; exact h4
  obtain ⟨t', -, h'⟩ := hbc.validity _ _ q m (proj_ev_eq_some.2 ⟨_, h5, rfl⟩)
  obtain ⟨st, hst, htoB⟩ := proj_ev_eq_some.1 h'
  rw [CStep.toB_eq_bc] at htoB
  subst htoB
  rw [solo_eq] at hst
  have := prun_proc c.A c.B _ hst
  simp only [CStep.proc] at this
  rw [this, c.segPar_p]

/-- The final messages are invoked after the start of the final copy. -/
lemma MsS_inv_late {p : Fin n} {m : Msg C} (hm : (p, m) ∈ c.MsS) {t : ℕ}
    (h : c.αS t = some (.inv p m)) : c.wsS p ≤ t := by
  rcases hm with ⟨hp, -⟩ | ⟨j, hp, t'', h1, h2, h3⟩
  · simp only at hp; subst hp
    rw [c.wsS_z]; exact (c.αS_z_step h rfl).1
  · simp only at hp h3; subst hp
    obtain ⟨h4, h5, h6⟩ := c.αS_seg_step h rfl
    have h7 := prun_off c.A c.B _ (off' := 0) h6 (by intro _ _ _ _ h; cases h)
    have := inv_once c.A c.B _ h7 h3
    rw [c.wsS_seg]; omega

lemma hDH : DeriveHyp c.A c.cpS c.αS c.MsS (Set.range c.pr) c.wsS := by
  have hadm := c.αS_adm hSb hS hA hAwf hB1 hB
  have hbc := hSb _ (hB _ _ hadm)
  -- the steps of any process belong to `p_0, …, p_k`
  have hproc : ∀ t (s : CStep (Fin n) (Msg C) X O W), c.αS t = some s → s.proc ∈ Set.range c.pr := by
    intro t s h
    rcases catRun_step c.A c.B _ _ _ c.distinct_αS h with ⟨j, hp, -⟩ | ⟨hp, -⟩
    · rw [hp, c.segPar_p]; exact ⟨_, rfl⟩
    · rw [hp]; exact ⟨_, rfl⟩
  refine ⟨isBroadcast_proj_empty hbc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp t m
    refine ⟨fun _ h => hp (hproc t _ h), fun _ h => hp (hproc t _ h),
      fun q _ h => hp (hproc t _ h)⟩
  · rintro p ⟨i, rfl⟩ t ht m
    refine ⟨fun hm h => absurd (c.MsS_inv_late hSb hS hA hAwf hB1 hB hm h) (by omega),
      fun hm h => ?_, fun q hm h => ?_⟩
    · obtain ⟨t'', ht'', h''⟩ := hbc.wf.ret_bc t _ m (proj_ev_eq_some.2 ⟨_, h, rfl⟩)
      obtain ⟨st, hst, htoB⟩ := proj_ev_eq_some.1 h''
      rw [CStep.toB_eq_bc] at htoB
      subst htoB
      have := c.MsS_inv_late hSb hS hA hAwf hB1 hB hm hst
      omega
    · rcases c.pr_cases i with rfl | ⟨j, rfl⟩
      · have := (c.αS_z_step h rfl).1
        rw [c.wsS_z] at ht; omega
      · have hq := c.seg_deliver_own hSb hS hA hAwf hB1 hB h
        subst hq
        obtain ⟨t'', ht'', h''⟩ := hbc.validity t _ _ m (proj_ev_eq_some.2 ⟨_, h, rfl⟩)
        obtain ⟨st, hst, htoB⟩ := proj_ev_eq_some.1 h''
        rw [CStep.toB_eq_bc] at htoB
        subst htoB
        have := c.MsS_inv_late hSb hS hA hAwf hB1 hB hm hst
        omega
  · rintro p ⟨i, rfl⟩
    rcases c.pr_cases i with rfl | ⟨j, rfl⟩
    · rw [c.copyView_z, c.wsS_z, ← add_zero c.E, c.fhist_z]; rfl
    · rw [c.copyView_seg, c.wsS_seg, c.fhist_seg j (by
        unfold wsLoc; split_ifs with h
        · rw [show j = c.lastSeg from c.eq_lastSeg (by omega), c.segL_last]
          have := c.Wk_le hSb hS hA hAwf hB1 hB; omega
        · omega)]
      unfold wsLoc
      split_ifs with h
      · rw [show j = c.lastSeg from c.eq_lastSeg (by omega), c.segPar_last]
        exact c.Wk_view hB1
      · rfl
  · rintro p ⟨i, rfl⟩ t ht o w h ⟨hR, hund⟩
    rcases c.pr_cases i with rfl | ⟨j, rfl⟩
    · simp [cpS, Ne.symm c.pr_kk_ne_z] at hR
    · obtain ⟨h1, h2, h3⟩ := c.αS_seg_step h rfl
      by_cases hj : j.val + 1 < k
      · simp [cpS, c.pr_early_ne_kk (i := Fin.castSucc j) hj] at hR
      · have hjl := c.eq_lastSeg hj
        subst hjl
        rw [c.segPar_last] at h3
        have h4 := prun_off c.A c.B _ (off' := 0) h3 (by intro _ _ _ _ h; cases h)
        rw [c.wsS_seg] at ht
        have hR' : o ∈ c.Ok := by simpa [cpS, c.castSucc_lastSeg] using hR
        rw [c.wsLoc_last] at ht
        refine c.Wk_spec hB1 (t - segOff c.segL c.lastSeg) (by omega)
          ⟨o, w, by rw [c.castSucc_lastSeg] at h4; exact h4, hR', ?_⟩
        unfold Decd
        rw [c.copyView_seg, c.segPar_last,
          show t = segOff c.segL c.lastSeg + (t - segOff c.segL c.lastSeg) by omega,
          c.fhist_seg _ (by omega), c.segPar_last] at hund
        simpa using hund
  · rintro p ⟨i, rfl⟩ m
    constructor
    · intro hm
      rcases hm with ⟨hp, t, ht, h⟩ | ⟨j, hp, t, h1, h2, h3⟩
      · simp only at hp h
        exact ⟨t, by rw [hp, c.wsS_z]; exact ht, h⟩
      · simp only at hp h3
        rw [hp] at h3 ⊢
        refine ⟨segOff c.segL j + t, by rw [c.wsS_seg]; omega, ?_⟩
        unfold αS
        rw [catRun_seg c.A c.B _ _ _ (i := j) (by omega) (by omega),
          show segOff c.segL j + t - segOff c.segL j = t by omega]
        exact prun_off c.A c.B _ h3 (by intro _ _ _ _ h; cases h)
    · rintro ⟨t, ht, h⟩
      rcases c.pr_cases i with rfl | ⟨j, rfl⟩
      · exact Or.inl ⟨rfl, t, by rw [c.wsS_z] at ht; exact ht, h⟩
      · right
        obtain ⟨h1, h2, h3⟩ := c.αS_seg_step h rfl
        rw [c.wsS_seg] at ht
        refine ⟨j, rfl, t - segOff c.segL j, by omega, by omega, ?_⟩
        exact prun_off c.A c.B _ h3 (by intro _ _ _ _ h; cases h)
  · rintro p ⟨i, rfl⟩ t ht q m hq h
    rcases c.pr_cases i with rfl | ⟨j, rfl⟩
    · obtain ⟨-, -, hF⟩ := c.cpS_z
      rw [hF]
      show (q, m) ∈ c.MsS ↔ c.Fz q m
      constructor
      · rintro (⟨hp, -⟩ | ⟨j, hp, t, h1, h2, h3⟩)
        · exact absurd hp hq
        · simp only at hp h3
          by_cases hj : j.val + 1 < k
          · left
            refine ⟨Fin.castSucc j, hj, hp, t, ?_, ?_⟩
            · unfold segL at h2; rwa [c.segPar_early hj] at h2
            · rw [c.segPar_early hj] at h3; rw [hp] at h3; exact h3
          · right
            have hjl := c.eq_lastSeg hj
            subst hjl
            rw [c.castSucc_lastSeg] at hp
            refine ⟨hp, t, ?_, ?_, ?_⟩
            · rw [c.wsLoc_last] at h1; exact h1
            · rwa [c.segL_last] at h2
            · rw [c.segPar_last] at h3; rw [hp] at h3; exact h3
      · rintro (⟨i, hi, hp, t, ht, h3⟩ | ⟨hp, t, h1, h2, h3⟩)
        · right
          have e : Fin.castSucc (⟨i.val, by omega⟩ : Fin k) = i := by ext; rfl
          have hj : (⟨i.val, by omega⟩ : Fin k).val + 1 < k := hi
          refine ⟨⟨i.val, by omega⟩, by rw [e]; exact hp, t, by rw [c.wsLoc_early hj]; omega, ?_, ?_⟩
          · unfold segL; rw [c.segPar_early hj, e]; exact ht
          · rw [c.segPar_early hj, e]; simp only; rw [hp]; exact h3
        · right
          refine ⟨c.lastSeg, by rw [c.castSucc_lastSeg]; exact hp, t, ?_, by rw [c.segL_last]; exact h2, ?_⟩
          · rw [c.wsLoc_last]; exact h1
          · rw [c.segPar_last]; simp only; rw [hp]; exact h3
    · exact absurd (c.seg_deliver_own hSb hS hA hAwf hB1 hB h) hq
  · rintro p ⟨i, rfl⟩ t ht m h
    rcases c.pr_cases i with rfl | ⟨j, rfl⟩
    · obtain ⟨hEt, h3⟩ := c.αS_z_step h rfl
      obtain ⟨-, -, hact⟩ := prun_inv h3
      rw [c.copyView_z, show t = c.E + (t - c.E) by omega, c.fhist_z]
      obtain ⟨hv, -⟩ := c.cpS_z
      rw [hv]; exact hact
    · obtain ⟨h1, h2, h3⟩ := c.αS_seg_step h rfl
      obtain ⟨-, -, hact⟩ := prun_inv h3
      rw [c.copyView_seg, show t = segOff c.segL j + (t - segOff c.segL j) by omega,
        c.fhist_seg j (by omega)]
      obtain ⟨hv, -⟩ := c.cpS_seg j
      rw [hv]; rw [c.segPar_p] at hact ⊢; exact hact

lemma DS_adm : Admissible c.A S c.DS := by
  have hadm := c.αS_adm hSb hS hA hAwf hB1 hB
  have hbc := hSb _ (hB _ _ hadm)
  have hDH := c.hDH hSb hS hA hAwf hB1 hB
  refine derive_admissible c.A c.cpS hS hB hadm hDH ?_
  rintro p rfl
  refine ⟨⟨_, rfl⟩, fin_fair hAwf c.distinct_αS hbc hDH ⟨_, rfl⟩ 0
    (by show c.wsS (c.pr c.z) = _; rw [c.wsS_z]; rfl) (fun t => c.copyView_z t) c.cpS_z.1 ?_⟩
  intro t ht m h
  exact Or.inl ⟨rfl, t, by simpa [E] using ht, h⟩

lemma decided_z : c.DS.Decided (c.f c.z) := by
  have hz := c.z_copy hSb hS hA hAwf hB1 hB
  have hdz := c.parZ_decd hSb hS hA hAwf hB1 hB
  have hex : ∃ j, Decd c.A c.B c.parZ j := ⟨_, hdz⟩
  obtain ⟨hj4, w, hw⟩ := c.Tf_step hex
  obtain ⟨-, hmin, hpos⟩ := c.Tf_spec hex
  have hle : c.Tf c.parZ ≤ c.Tf c.parZ' := by
    by_contra h; exact hmin _ (by omega) hdz
  have hag := c.parZ_agree hSb hS hA hAwf hB1 hB (c.Tf c.parZ - 1) (by omega)
  have hwz : w = c.f c.z := hz.2 _ w hj4 (by rw [← hag]; exact hw)
  subst hwz
  have hup : upperStep c.A c.parZ (lst c.A c.B c.parZ (c.Tf c.parZ - 1)).h = .up c.parZ.p :=
    upperStep_of_not_bcast c.A c.parZ (by intro c'; rw [hw]; simp)
  refine ⟨c.E + (c.Tf c.parZ - 1), c.pr c.z, c.DS_dec ?_ ⟨_, rfl⟩ (by rw [c.wsS_z]; omega) ?_⟩
  · unfold αS
    rw [catRun_fin c.A c.B _ _ _ (by unfold E; omega), show c.E + (c.Tf c.parZ - 1) - segEnd c.segL =
      c.Tf c.parZ - 1 by unfold E; omega, prun_slot0 c.A c.B _ _ _ hj4, hup]
    rfl
  · rw [c.copyView_z, c.fhist_z, c.cpS_z.1]; exact hw

lemma decided_seg (j : Fin k) : c.DS.Decided (c.f (Fin.castSucc j)) := by
  have hex : ∃ i, Decd c.A c.B (c.segPar j) i := by
    by_cases hj : j.val + 1 < k
    · rw [c.segPar_early hj]; exact (c.early_copy hSb hS hA hAwf hB1 hB hj).1
    · rw [c.eq_lastSeg hj, c.segPar_last]; exact (c.kk_copy hSb hS hA hAwf hB1 hB).1
  obtain ⟨hj4, w, hw⟩ := c.Tf_step hex
  obtain ⟨-, -, hpos⟩ := c.Tf_spec hex
  have hWT := c.Wk_le hSb hS hA hAwf hB1 hB
  have hval : w = c.f (Fin.castSucc j) := by
    by_cases hj : j.val + 1 < k
    · rw [c.segPar_early hj] at hw hj4
      exact (c.early_copy hSb hS hA hAwf hB1 hB hj).2 _ w hj4 hw
    · have hjl := c.eq_lastSeg hj
      subst hjl
      rw [c.segPar_last] at hw hj4
      rw [c.castSucc_lastSeg]
      exact (c.kk_copy hSb hS hA hAwf hB1 hB).2 _ (by unfold TK at hWT; omega) w hj4 hw
  subst hval
  have hup : upperStep c.A (c.segPar j) (lst c.A c.B (c.segPar j) (c.Tf (c.segPar j) - 1)).h =
      .up (c.segPar j).p :=
    upperStep_of_not_bcast c.A _ (by intro c'; rw [hw]; simp)
  have hT : c.segL j = c.Tf (c.segPar j) := rfl
  refine ⟨segOff c.segL j + (c.Tf (c.segPar j) - 1), c.pr (Fin.castSucc j),
    c.DS_dec ?_ ⟨_, rfl⟩ ?_ ?_⟩
  · unfold αS
    rw [catRun_seg c.A c.B _ _ _ (i := j) (by omega) (by omega),
      show segOff c.segL j + (c.Tf (c.segPar j) - 1) - segOff c.segL j =
        c.Tf (c.segPar j) - 1 by omega, prun_slot0 c.A c.B _ _ _ hj4, hup, c.segPar_p]
  · rw [c.wsS_seg]
    by_cases hj : j.val + 1 < k
    · rw [c.wsLoc_early hj]; omega
    · have hjl := c.eq_lastSeg hj
      subst hjl
      rw [c.wsLoc_last]
      have : c.Tf (c.segPar c.lastSeg) = c.TK := by rw [c.segPar_last]; rfl
      omega
  · rw [c.copyView_seg, c.fhist_seg j (by omega), (c.cpS_seg j).1]
    rw [c.segPar_p] at hw ⊢
    exact hw

/-- **The contradiction.** -/
theorem false_of : False := by
  have hksa := hA _ (c.DS_adm hSb hS hA hAwf hB1 hB)
  refine hksa.agreement c.f c.hf (fun i => ?_)
  rcases c.pr_cases i with rfl | ⟨j, rfl⟩
  · exact c.decided_z hSb hS hA hAwf hB1 hB
  · exact c.decided_seg hSb hS hA hAwf hB1 hB j

end Proof

end Ctx

/-! ## Theorem 1 -/

/-- **Theorem 1** (repaired proof). For `1 < k < n`, there is no compositional broadcast
abstraction `S` such that a (well-formed, broadcast-only) algorithm `A` solves k-set agreement
(on a value domain with at least `k + 1` values) on top of `S` in `CAMP_n[S]`, and an algorithm
`B` (proposing at most once to each k-SA object) implements `S` in `CAMP_n[k-SA]`.
Content-neutrality is not needed. -/
theorem theorem1 {n k : ℕ} (hk : 1 < k) (hkn : k < n) {C V X O W : Type} [DecidableEq C]
    (S : Set (BExec (Fin n) (Msg C))) (hSb : IsBroadcastAbstraction S) (hS : Compositional S)
    (A : Algo (Fin n) C V) (hA : SolvesKSA k A S) (hAwf : A.WellFormed)
    (hV : ∃ f : Fin (k + 1) → V, Function.Injective f)
    (B : BAlgo (Fin n) (Msg C) X O W) (hB1 : B.OneShot) (hB : Implements B k S) : False := by
  obtain ⟨f, hf⟩ := hV
  exact (⟨hk, by omega, A, B, f, hf⟩ : Ctx n k C V X O W).false_of hSb hS hA hAwf hB1 hB

/-- A broadcast abstraction is computationally equivalent to k-set agreement in `CAMP_n[∅]`:
some algorithm solves k-SA on top of it (with at least `k + 1` possible proposals), and some
algorithm implements it in `CAMP_n[k-SA]`. -/
def EquivalentToKSA {n : ℕ} {C : Type} (k : ℕ) (S : Set (BExec (Fin n) (Msg C))) : Prop :=
  (∃ (V : Type) (A : Algo (Fin n) C V), A.WellFormed ∧
    (∃ f : Fin (k + 1) → V, Function.Injective f) ∧ SolvesKSA k A S) ∧
  ∃ (X O W : Type) (B : BAlgo (Fin n) (Msg C) X O W), B.OneShot ∧ Implements B k S

/-- **Theorem 1** of the paper: for `1 < k < n`, no content-neutral and compositional broadcast
abstraction is equivalent to k-set agreement in `CAMP_n[∅]` (true; content-neutrality is not
even needed, see `theorem1`). -/
theorem theorem1_paper {n k : ℕ} (hk : 1 < k) (hkn : k < n) {C : Type} [DecidableEq C]
    (S : Set (BExec (Fin n) (Msg C))) (hSb : IsBroadcastAbstraction S)
    (_hCN : ContentNeutral S) (hS : Compositional S) : ¬ EquivalentToKSA k S := by
  rintro ⟨⟨V, A, hAwf, hV, hA⟩, X, O, W, B, hB1, hB⟩
  exact theorem1 hk hkn S hSb hS A hA hAwf hV B hB1 hB

end Podc.NoBroadcastKSA.Camp
