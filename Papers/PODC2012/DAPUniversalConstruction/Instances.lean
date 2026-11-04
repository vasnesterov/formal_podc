import Papers.PODC2012.DAPUniversalConstruction.List
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Executions in which one process appends to the list

Setting of the proof of Theorem 5: process `q` performs `Append(f 0)`, `Append(f 1)`, … solo
from the initial configuration (`cfg f n` is the configuration after `n` appends, `seg f n` the
steps of the `n`-th append); then process `p` invokes `Search(0)` (`dcfg f n`).

* `run_pre`: these are executions of the implementation, ending in quiescent configurations;
* `representsState_pre`: they represent the list `[f 0, …, f (n-1)]`;
* `search_resp`: a `Search(0)` run solo after them returns whether `0` is in the list
  (linearizability);
* `mem_cfg_eq`: two such executions whose values agree on the first `j` appends differ only on
  base objects written by the later appends.
-/

namespace Podc.DAPUniversalConstruction

open Cslib.SharedMemory Impl

variable {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

section Defs

variable (I : Impl listSpec B P L) (q : P)

/-- The configuration after `q` performs `Append(f 0)`, …, `Append(f (n-1))` solo from the
initial configuration (paper: `Cₙ`, or `Cₙʲ` when one value is replaced by `0`). -/
noncomputable abbrev cfg (f : ℕ → ℤ) (n : ℕ) : Config listSpec B P L :=
  instCfg I I.initCfg q LOp.append f n

/-- The steps of the `n`-th append (from `0`) (paper: `α_{n+1}`). -/
noncomputable abbrev seg (f : ℕ → ℤ) (n : ℕ) : List (Label P listSpec) :=
  instSeg I I.initCfg q LOp.append f n

/-- The labels of the first `n` appends. -/
noncomputable def pre (f : ℕ → ℤ) : ℕ → List (Label P listSpec)
  | 0 => []
  | n + 1 => pre f n ++ seg I q f n

/-- The list after the first `n` appends. -/
def vals (f : ℕ → ℤ) (n : ℕ) : List ℤ := (List.range n).map f

end Defs

variable {I : Impl listSpec B P L} {q : P}

lemma cfg_succ (f : ℕ → ℤ) (n : ℕ) :
    cfg I q f (n + 1) = (I.runFrom (cfg I q f n) (seg I q f n)).getD (cfg I q f n) := rfl

/-- The appends terminate (obstruction-freedom) and the executions are as expected. -/
lemma run_pre (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (f : ℕ → ℤ) (n : ℕ) :
    I.run (pre I q f n) = some (cfg I q f n) ∧ (cfg I q f n).Quiescent ∧
      (∀ x, x ≠ q → (cfg I q f n).loc x = I.locInit x) ∧
      (∀ ℓ ∈ pre I q f n, ℓ.proc = q) ∧
      opsOf (pre I q f n) q = (vals f n).map LOp.append ∧
      (respsOf (pre I q f n) q).length = n := by
  induction n with
  | zero =>
    refine ⟨rfl, fun _ => rfl, fun _ _ => rfl, by simp [pre], by simp [pre, vals], by simp [pre]⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    obtain ⟨C', g1, g2, g3, g4, g5⟩ :=
      I.soloOp_spec hOF q (LOp.append (f n)) (hall _ _) h1 (h2 q)
    have hseg : seg I q f n = I.soloOp q (LOp.append (f n)) (cfg I q f n) := rfl
    have hcfg : cfg I q f (n + 1) = C' := by rw [cfg_succ, hseg, g1]; rfl
    rw [← hseg] at g1 g3 g4 g5
    have ho : ∀ x, x ≠ q → C'.loc x = (cfg I q f n).loc x ∧ C'.pend x = (cfg I q f n).pend x :=
      fun x hx => I.runFrom_other g1 (q := x) (fun ℓ h => by rw [g3 ℓ h]; exact Ne.symm hx)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [pre]; rw [run_append_of_eq I h1, g1, hcfg]
    · intro x
      by_cases hx : x = q
      · subst hx; rw [hcfg]; exact g2
      · rw [hcfg, (ho x hx).2]; exact h2 x
    · intro x hx
      rw [hcfg, (ho x hx).1]; exact h3 x hx
    · intro ℓ h
      simp only [pre, List.mem_append] at h
      rcases h with h | h
      · exact h4 ℓ h
      · exact g3 ℓ h
    · simp only [pre, opsOf_append, h5, g4, vals, List.range_succ, List.map_append]
      rfl
    · simp only [pre, respsOf_append, List.length_append, h6, g5]

lemma run_seg (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (f : ℕ → ℤ) (n : ℕ) :
    I.runFrom (cfg I q f n) (seg I q f n) = some (cfg I q f (n + 1)) ∧
      (∀ ℓ ∈ seg I q f n, ℓ.proc = q) ∧ opsOf (seg I q f n) q = [LOp.append (f n)] := by
  obtain ⟨h1, h2, -⟩ := run_pre (q := q) hall hOF f n
  obtain ⟨C', g1, -, g3, g4, -⟩ := I.soloOp_spec hOF q (LOp.append (f n)) (hall _ _) h1 (h2 q)
  have hseg : seg I q f n = I.soloOp q (LOp.append (f n)) (cfg I q f n) := rfl
  refine ⟨?_, by rw [hseg]; exact g3, by rw [hseg]; exact g4⟩
  rw [cfg_succ, hseg, g1]; rfl

lemma reachable_cfg (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (f : ℕ → ℤ)
    (n : ℕ) : I.Reachable (cfg I q f n) :=
  ⟨_, (run_pre (q := q) hall hOF f n).1⟩

lemma runOps_vals (f : ℕ → ℤ) (n : ℕ) :
    listSpec.runOps listSpec.init ((vals f n).map LOp.append) = vals f n := by
  rw [runOps_append_map]; rfl

/-- The execution of the first `n` appends represents the list `[f 0, …, f (n-1)]`. -/
lemma representsState_pre (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree)
    (hlin : I.Linearizable) (f : ℕ → ℤ) (n : ℕ) :
    RepresentsState (pre I q f n) (vals f n) := by
  obtain ⟨h1, -, -, h4, h5, h6⟩ := run_pre (q := q) hall hOF f n
  obtain ⟨h, hh⟩ := hlin
  refine ⟨⟨_, hh _ ⟨_, h1⟩⟩, fun Lz hLz => ?_⟩
  have hro : ∀ x, x ≠ q → ∀ o ∈ opsOf (pre I q f n) x, listSpec.ReadOnly o := by
    intro x hx o ho
    rw [opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [h4 ℓ hℓ]; exact Ne.symm hx)] at ho
    simp at ho
  rw [hLz.linState_of_changer (Impl.Valid.wellFormed (I := I) ⟨_, h1⟩) q hro (by rw [h6, h5]; simp [vals]),
    h5, runOps_vals]

/-- The configuration after `p` invokes `Search(0)` after the first `n` appends. -/
noncomputable def dcfg (I : Impl listSpec B P L) (q p : P) (f : ℕ → ℤ) (n : ℕ) :
    Config listSpec B P L :=
  (I.step (cfg I q f n) (.inv p (LOp.search 0))).getD (cfg I q f n)

lemma step_dcfg (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (p : P) (f : ℕ → ℤ)
    (n : ℕ) : I.step (cfg I q f n) (.inv p (LOp.search 0)) = some (dcfg I q p f n) := by
  obtain ⟨-, h2, -⟩ := run_pre (q := q) hall hOF f n
  unfold dcfg; rw [step_inv_eq_some (h2 p) (hall _ _)]; rfl

lemma dcfg_loc_pend (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) {p : P}
    (hpq : p ≠ q) (f : ℕ → ℤ) (n : ℕ) :
    (dcfg I q p f n).loc p = I.invoke p (I.locInit p) (LOp.search 0) ∧
      (dcfg I q p f n).pend p = some (LOp.search 0) ∧ (dcfg I q p f n).mem = (cfg I q f n).mem := by
  obtain ⟨-, h2, h3, -⟩ := run_pre (q := q) hall hOF f n
  obtain ⟨-, -, e1, e2, e3⟩ := step_inv (step_dcfg (q := q) hall hOF p f n)
  refine ⟨?_, ?_, e3⟩
  · rw [e2]; simp [h3 p hpq]
  · rw [e1]; simp

lemma reachable_dcfg (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (p : P)
    (f : ℕ → ℤ) (n : ℕ) : I.Reachable (dcfg I q p f n) :=
  ⟨_, by rw [run_append_of_eq I (run_pre (q := q) hall hOF f n).1, runFrom_singleton,
    step_dcfg hall hOF p f n]⟩

/-- `cfg` only depends on the values of the appends performed so far. -/
lemma cfg_congr {f g : ℕ → ℤ} {n : ℕ} (h : ∀ k < n, f k = g k) : cfg I q f n = cfg I q g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cfg_succ, cfg_succ, ih (fun k hk => h k (by omega))]
    simp only [seg, instSeg, ih (fun k hk => h k (by omega)), h n (by omega)]

/-- Objects not written by the appends `j, …, n-1` keep their values from `cfg f j`. -/
lemma mem_cfg_eq (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (f : ℕ → ℤ)
    {j n : ℕ} (hjn : j ≤ n) {i : ι}
    (hi : ∀ k, j ≤ k → k < n → i ∉ I.written (cfg I q f k) (seg I q f k)) :
    (cfg I q f n).mem i = (cfg I q f j).mem i := by
  induction n, hjn using Nat.le_induction with
  | base => rfl
  | succ n hjn ih =>
    rw [mem_eq_of_not_written (run_seg (q := q) hall hOF f n).1 (hi n hjn (by omega)),
      ih (fun k h1 h2 => hi k h1 (by omega))]

/-- A `Search(0)` that returns, run solo after the first `n` appends, returns whether `0` is in
the list (linearizability). -/
lemma search_resp (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (hlin : I.Linearizable)
    {p : P} (hpq : p ≠ q) (f : ℕ → ℤ) (n t : ℕ) {r : Bool}
    (hr : .ret p r ∈ I.soloLabels p (dcfg I q p f n) t) :
    r = decide (0 ∈ vals f n) := by
  obtain ⟨h1, -, -, h4, h5, h6⟩ := run_pre (q := q) hall hOF f n
  set α := pre I q f n ++ .inv p (LOp.search 0) :: I.soloLabels p (dcfg I q p f n) t with hα
  have hrun : I.run α = some ((I.soloStep p)^[t] (dcfg I q p f n)) := by
    rw [hα, run_append_of_eq I h1, runFrom_cons, step_dcfg hall hOF p f n, Option.bind_some,
      runFrom_soloLabels]
  have hsp := I.soloLabels_proc p (dcfg I q p f n) t
  have hpre_p : ∀ ℓ ∈ pre I q f n, ℓ.proc ≠ p := fun ℓ h => by rw [h4 ℓ h]; exact Ne.symm hpq
  have hops_p : opsOf α p = [LOp.search 0] := by
    rw [hα, opsOf_append, opsOf_eq_nil_of_proc_ne hpre_p, opsOf_cons, opsOf_soloLabels]; simp
  have hops_q : opsOf α q = (vals f n).map LOp.append := by
    rw [hα, opsOf_append, h5, opsOf_cons, opsOf_soloLabels]; simp [hpq]
  have hresp_p : r ∈ respsOf α p := by
    rw [hα, respsOf_append, respsOf_cons]
    simp only [respsOf, List.mem_append, List.mem_filterMap]
    exact Or.inr (Or.inr ⟨_, hr, by simp⟩)
  have hle := I.run_resps_le_ops hrun p
  rw [hops_p] at hle
  have hresp : respsOf α p = [r] := by
    match h : respsOf α p, hle with
    | [], _ => rw [h] at hresp_p; simp at hresp_p
    | [r'], _ => rw [h] at hresp_p; simp at hresp_p; rw [hresp_p]
  obtain ⟨h, hh⟩ := hlin
  have hL := hh α ⟨_, hrun⟩
  have hro : ∀ y ∈ h α, y.1.1 ≠ q → listSpec.ReadOnly y.2 := by
    intro y hy hyq
    have hm := hL.op_mem hy
    by_cases hyp : y.1.1 = p
    · rw [hyp, hops_p] at hm
      simp only [List.mem_singleton] at hm
      rw [hm]; intro s; rfl
    · rw [opsOf_eq_nil_of_proc_ne] at hm
      · simp at hm
      · intro ℓ hℓ
        rw [hα, List.mem_append, List.mem_cons] at hℓ
        rcases hℓ with hℓ | rfl | hℓ
        · rw [h4 ℓ hℓ]; exact Ne.symm hyq
        · exact Ne.symm hyp
        · rw [hsp ℓ hℓ]; exact Ne.symm hyp
  have hx : respOf α (p, 0) = some r := by simp [respOf, hresp]
  have hpre : ∀ j < n, Precedes α (q, j) (p, 0) := by
    intro j hj
    refine ⟨pre I q f n, _, hα, ?_, ?_⟩
    · simp only [Completed, h6]; exact hj
    · simp [Invoked, opsOf_eq_nil_of_proc_ne hpre_p]
  obtain ⟨j, hj1, hj2, o, ho, hr'⟩ := hL.resp_eq (Impl.Valid.wellFormed (I := I) ⟨_, hrun⟩) q hro hx n hpre
  rw [hops_q, List.length_map] at hj2
  have hjn : j = n := by simp [vals] at hj2; omega
  subst hjn
  have hlen : (vals f j).length = j := by simp [vals]
  rw [hops_q, List.take_of_length_le (by simp [hlen]), runOps_vals] at hr'
  simp only [opOf, hops_p, List.getElem?_cons_zero, Option.some.injEq] at ho
  subst ho
  exact hr'

end Podc.DAPUniversalConstruction
