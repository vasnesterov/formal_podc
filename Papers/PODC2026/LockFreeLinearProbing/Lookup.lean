import Papers.PODC2026.LockFreeLinearProbing.Step
import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# Lookups are wait-free (Section 5.3)

A `lookup` performs at most one forward and one backward scan, with at most two extra accesses
(`validate_copy`) per cell: it returns after at most `6m + 5` shared-memory accesses, whatever the
other processes do.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] (h : K → Fin m)
variable {P : Type} [DecidableEq P]


/-- The potential of a `lookup`: forward-scan states above backward-scan states, decreasing with
the progress of the scans. -/
def lpot (l : Loc K m) : ℕ :=
  match l.pc with
  | .fsLL => 3 * m + 3 + 3 * (m - dist h l.op.key l.i) + 2
  | .bsLL => 3 * dist h l.op.key l.i + 3
  | .vcSC => if l.fwd then 3 * m + 3 + 3 * (m - dist h l.op.key l.i) + 1
      else 3 * dist h l.op.key l.i + 2
  | .vcRD => if l.fwd then 3 * m + 3 + 3 * (m - dist h l.op.key l.i)
      else 3 * dist h l.op.key l.i + 1
  | _ => 0

/-- The program counters a `lookup` can be at. -/
def PC.isLook : PC → Bool
  | .fsLL | .bsLL | .vcSC | .vcRD | .ret => true
  | _ => false

/-- A local state of a `lookup` together with a bound on the scan position of the scans. -/
def LookOK (l : Loc K m) : Prop := (∃ v, l.op = .lookup v) ∧ l.pc.isLook

lemma dist_pred (v : K) (i : Fin m) (hi : i ≠ h v) : dist h v (i - 1) + 1 = dist h v i := by
  have := dist_succ h v (i - 1) (by simpa using hi)
  simp only [sub_add_cancel] at this; omega

@[simp] lemma DOp.key_lookup (v : K) : (DOp.lookup v).key = v := rfl
@[simp] lemma DOp.key_insert (v : K) : (DOp.insert v).key = v := rfl
@[simp] lemma DOp.key_delete (v : K) : (DOp.delete v).key = v := rfl

section
variable {v : K}

/-- Facts about the local state reached by a `lookup`. -/
def LK (l l' : Loc K m) (b : ℕ) : Prop := l'.pc.isLook ∧ l'.op = l.op ∧ lpot h l' ≤ b

lemma lk_retL (l : Loc K m) (r : Res) (b : ℕ) : LK h l (retL l r) b := by
  simp [LK, retL, PC.isLook, lpot]

lemma lk_fsReturn {l : Loc K m} (hv : l.op = .lookup v) (r : SR m) :
    LK h l (fsReturn l r) (3 * m) := by
  have := dist_lt h v
  rcases r with _ | _ | k | _ <;> simp [fsReturn, hv, LK, retL, PC.isLook, lpot]
  have := dist_lt h v k; omega

lemma lk_fsEnd {l : Loc K m} (hv : l.op = .lookup v) : LK h l (fsEnd h l) (3 * m) := by
  unfold fsEnd; split_ifs <;> exact lk_fsReturn h hv _

lemma lk_fsNext {l : Loc K m} (hv : l.op = .lookup v) :
    LK h l (fsNext h l) (3 * m + 3 * (m - dist h v l.i) + 2) := by
  unfold fsNext; split_ifs with h1
  · obtain ⟨a, b, c⟩ := lk_fsEnd h (l := { l with i := l.i + 1 }) hv
    exact ⟨a, b, by omega⟩
  · have e := dist_succ h l.op.key l.i h1
    have := dist_lt h l.op.key (l.i + 1)
    refine ⟨by simp [PC.isLook], rfl, ?_⟩
    simp only [lpot]; rw [hv, DOp.key_lookup] at e this; simp only [hv, DOp.key_lookup]; omega

lemma lk_bsReturn {l : Loc K m} (hv : l.op = .lookup v) (r : SR m) :
    LK h l (bsReturn h l r) 0 := by
  rcases r with _ | _ | k | _ <;> simp [bsReturn, hv, LK, retL, PC.isLook, lpot]

lemma lk_bsCheck {l : Loc K m} (hv : l.op = .lookup v) :
    LK h l (bsCheck h l) (3 * dist h v l.i) := by
  unfold bsCheck; split_ifs with h1
  · obtain ⟨a, b, c⟩ := lk_bsReturn h hv (l := l) .bot; exact ⟨a, b, by omega⟩
  · rw [hv] at h1
    have e := dist_pred h v l.i h1
    refine ⟨by simp [PC.isLook], rfl, ?_⟩
    simp only [lpot, hv, DOp.key_lookup]; omega

lemma lk_vcRet {l : Loc K m} (hv : l.op = .lookup v) (b : Bool) :
    LK h l (vcRet h l b) (if l.fwd then 3 * m + 3 * (m - dist h v l.i) + 2
      else 3 * dist h v l.i) := by
  unfold vcRet
  have := dist_lt h v l.i
  split_ifs with h1 h2 h2
  · obtain ⟨a, b, c⟩ := lk_fsReturn h hv (l := l) .tt; exact ⟨a, b, by omega⟩
  · exact lk_fsNext h hv
  · obtain ⟨a, b, c⟩ := lk_bsReturn h hv (l := l) .tt; exact ⟨a, b, by omega⟩
  · exact lk_bsCheck h hv

lemma lk_vcStart {l : Loc K m} (hv : l.op = .lookup v) :
    LK h l (vcStart h l) (if l.fwd then 3 * m + 3 + 3 * (m - dist h v l.i) + 1
      else 3 * dist h v l.i + 2) := by
  unfold vcStart
  split_ifs with h1 h2 h2
  · obtain ⟨a, b, c⟩ := lk_vcRet h hv (l := l) true; rw [if_pos h2] at c; exact ⟨a, b, by omega⟩
  · obtain ⟨a, b, c⟩ := lk_vcRet h hv (l := l) true; rw [if_neg h2] at c; exact ⟨a, b, by omega⟩
  · refine ⟨by simp [PC.isLook], rfl, ?_⟩; simp [lpot, h2, hv]
  · refine ⟨by simp [PC.isLook], rfl, ?_⟩; simp [lpot, h2, hv]

lemma lk_fsBody {l : Loc K m} (hv : l.op = .lookup v) :
    LK h l (fsBody h l) (3 * m + 3 + 3 * (m - dist h v l.i) + 1) := by
  unfold fsBody
  have := dist_lt h v l.i
  split_ifs with h1 h2 h3
  · obtain ⟨a, b, c⟩ := lk_fsEnd h hv (l := l); exact ⟨a, b, by omega⟩
  · obtain ⟨a, b, c⟩ := lk_vcStart h (l := { l with fwd := true }) hv
    simp only [ite_true] at c; exact ⟨a, b, c⟩
  · simp [hv, DOp.isInsLook] at h3
  · obtain ⟨a, b, c⟩ := lk_fsNext h hv (l := l); exact ⟨a, b, by omega⟩

lemma lk_bsBody {l : Loc K m} (hv : l.op = .lookup v) :
    LK h l (bsBody h l) (3 * dist h v l.i + 2) := by
  unfold bsBody
  split_ifs with h2 h3
  · obtain ⟨a, b, c⟩ := lk_vcStart h (l := { l with fwd := false }) hv
    simp only [Bool.false_eq_true, ite_false] at c; exact ⟨a, b, c⟩
  · simp [hv, DOp.isInsLook] at h3
  · obtain ⟨a, b, c⟩ := lk_bsCheck h hv (l := l); exact ⟨a, b, by omega⟩

lemma access_inj {p : P} {l : Loc K m} {x x' : Fin m} {o o' : LLOp (Cell K) P}
    {k k' : Cell K × Bool → Loc K m}
    (h1 : act h p l = .access x o k) (h2 : act h p l = .access x' o' k') : x = x' ∧ o = o' ∧ k = k' := by
  rw [h1] at h2; injection h2 with a b c; subst a; exact ⟨rfl, b, c⟩

/-- Every shared-memory access of a `lookup` decreases its potential. -/
lemma lookup_act {p : P} {l : Loc K m} (hv : l.op = .lookup v) (hl : l.pc.isLook) {x : Fin m}
    {o : LLOp (Cell K) P} {k : Cell K × Bool → Loc K m} (hact : act h p l = .access x o k)
    (r : Cell K × Bool) : (k r).pc.isLook ∧ (k r).op = l.op ∧ lpot h (k r) < lpot h l := by
  have := dist_lt h v l.i
  have hne : l.pc ≠ .ret := by intro h0; simp [act, h0] at hact
  have hne' : l.pc ≠ .idle := by intro h0; simp [act, h0] at hact
  have hcases : l.pc = .fsLL ∨ l.pc = .bsLL ∨ l.pc = .vcSC ∨ l.pc = .vcRD := by
    revert hl hne hne'; cases l.pc <;> simp [PC.isLook]
  rcases hcases with hpc | hpc | hpc | hpc
  · have h' : act h p l = .access l.i (.ll p) (fun r => fsBody h { l with val := r.1 }) := by
      simp only [act, hpc]
    obtain ⟨-, -, rfl⟩ := access_inj h hact h'
    obtain ⟨a, b, c⟩ := lk_fsBody h (l := { l with val := r.1 }) hv
    have e : lpot h l = 3 * m + 3 + 3 * (m - dist h v l.i) + 2 := by
      simp only [lpot, hpc, hv, DOp.key_lookup]
    simp only at a b c ⊢
    exact ⟨a, b, by rw [e]; omega⟩
  · have h' : act h p l = .access l.i (.ll p) (fun r => bsBody h { l with val := r.1 }) := by
      simp only [act, hpc]
    obtain ⟨-, -, rfl⟩ := access_inj h hact h'
    obtain ⟨a, b, c⟩ := lk_bsBody h (l := { l with val := r.1 }) hv
    have e : lpot h l = 3 * dist h v l.i + 3 := by simp only [lpot, hpc, hv, DOp.key_lookup]
    simp only at a b c ⊢
    exact ⟨a, b, by rw [e]; omega⟩
  · have h' : act h p l = .access l.i (.sc p (.key l.op.key .reval)) (fun r =>
        if r.2 then vcRet h l true else { l with pc := .vcRD }) := by
      simp only [act, hpc]
    obtain ⟨-, -, rfl⟩ := access_inj h hact h'
    have e : lpot h l = if l.fwd then 3 * m + 3 + 3 * (m - dist h v l.i) + 1
        else 3 * dist h v l.i + 2 := by simp only [lpot, hpc, hv, DOp.key_lookup]
    simp only
    split_ifs with h1
    · obtain ⟨a, b, c⟩ := lk_vcRet h (l := l) hv true
      refine ⟨a, b, ?_⟩; rw [e]; split_ifs at c ⊢ <;> omega
    · refine ⟨by simp [PC.isLook], rfl, ?_⟩
      rw [e]; simp only [lpot, hv, DOp.key_lookup]; split_ifs <;> omega
  · have h' : act h p l = .access l.i (.vl p) (fun r =>
        vcRet h { l with val := r.1 } (r.1.key? = some l.op.key)) := by
      simp only [act, hpc]
    obtain ⟨-, -, rfl⟩ := access_inj h hact h'
    obtain ⟨a, b, c⟩ := lk_vcRet h (l := { l with val := r.1 }) hv (decide (r.1.key? = some l.op.key))
    have e : lpot h l = if l.fwd then 3 * m + 3 + 3 * (m - dist h v l.i)
        else 3 * dist h v l.i + 1 := by simp only [lpot, hpc, hv, DOp.key_lookup]
    simp only at a b c ⊢
    refine ⟨a, b, ?_⟩; rw [e]; split_ifs at c ⊢ <;> omega

end

/-- The bookkeeping invariant of `lookup`s. -/
def LkInv (C : Cfg K m P) : Prop :=
  ∀ p v, C.pend p = some (.lookup v) → (C.loc p).op = .lookup v ∧ (C.loc p).pc.isLook ∧
    lpot h (C.loc p) ≤ 6 * m + 5

lemma lkInv_step {C C' : Cfg K m P} (hI : LkInv h C) {ℓ : Label P (dict K)}
    (hs : (impl h).step C ℓ = some C') : LkInv h C' := by
  intro q v hq
  by_cases hql : ℓ.proc = q
  · cases ℓ with
    | inv p o =>
      simp only [Label.proc] at hql; subst hql
      obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv hs
      rw [hpend, update_self] at hq; injection hq with hq; subst hq
      rw [hloc, update_self]
      refine ⟨rfl, rfl, ?_⟩
      simp only [impl, start, lpot, DOp.key_lookup, dist_self]; omega
    | tau p =>
      simp only [Label.proc] at hql; subst hql
      obtain ⟨-, hpend, x, o, k, hact, -, hloc⟩ := Impl.step_tau hs
      rw [hpend] at hq
      obtain ⟨h1, h2, h3⟩ := hI p v hq
      rw [hloc, update_self]
      obtain ⟨a, b, c⟩ := lookup_act h h1 h2 hact _
      exact ⟨b.trans h1, a, by omega⟩
    | ret p r =>
      simp only [Label.proc] at hql; subst hql
      obtain ⟨-, hpend, -⟩ := Impl.step_ret hs
      simp [hpend] at hq
  · obtain ⟨h1, h2⟩ := Impl.step_other hs hql
    rw [h2] at hq; rw [h1]; exact hI q v hq

lemma lkInv_of_run {α : List (Label P (dict K))} {C : Cfg K m P} (hα : (impl h).run α = some C) :
    LkInv h C := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at hα; subst hα
    intro p v hp; simp [Impl.initCfg] at hp
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at hα
    cases hrun : (impl h).run α with
    | none => simp [hrun] at hα
    | some C₀ => rw [hrun] at hα; exact lkInv_step h (ih hrun) hα

/-- Along a fragment without a response of `p`, `p`'s pending operation does not change. -/
lemma pend_of_runFrom {C D : Cfg K m P} {β : List (Label P (dict K))}
    (hβ : (impl h).runFrom C β = some D) {p : P} {o : DOp K} (hp : C.pend p = some o)
    (hr : ∀ r, Label.ret p r ∉ β) : D.pend p = some o := by
  induction β generalizing C with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at hβ; subst hβ; exact hp
  | cons ℓ β ih =>
    simp only [Impl.runFrom_cons] at hβ
    cases hs : (impl h).step C ℓ with
    | none => simp [hs] at hβ
    | some C₁ =>
      rw [hs] at hβ
      refine ih hβ ?_ (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))
      by_cases hq : ℓ.proc = p
      · cases ℓ with
        | inv q o' =>
          simp only [Label.proc] at hq; subst hq
          exact absurd (Impl.step_inv hs).1 (by simp [hp])
        | ret q r =>
          simp only [Label.proc] at hq; subst hq
          exact absurd List.mem_cons_self (hr r)
        | tau q => rw [(Impl.step_tau hs).2.1]; exact hp
      · rw [(Impl.step_other hs hq).2]; exact hp

/-- **Lookups are wait-free** (Section 5.3): from any reachable configuration in which `p` has a
pending `lookup`, along any continuation in which `p` does not return, `p` takes at most
`6m + 5` steps (shared-memory accesses). -/
theorem lookup_waitFree {α : List (Label P (dict K))} {C : Cfg K m P}
    (hα : (impl h).run α = some C) {p : P} {v : K} (hp : C.pend p = some (.lookup v))
    {γ : List (Label P (dict K))} {C' : Cfg K m P} (hγ : (impl h).runFrom C γ = some C')
    (hr : ∀ r, .ret p r ∉ γ) : γ.countP (Label.isTauOf p) ≤ 6 * m + 5 := by
  have hI := lkInv_of_run h hα
  have key := (impl h).countP_isTauOf_add_le_of_cfgPotential p
    (fun D => if (D.loc p).op = .lookup v ∧ (D.loc p).pc.isLook then lpot h (D.loc p) else 0)
    γ C C' hγ (by simp [hp]) hr ?_
  · have := (hI p v hp).2.2; simp only [(hI p v hp).1, (hI p v hp).2.1, and_self, ite_true] at key
    omega
  intro β ℓ D D' hpre hβ hs hD hD'
  -- `D` is reachable, and `p`'s pending operation is still the lookup
  have hrD : (impl h).run (α ++ β) = some D := by rw [(impl h).run_append_of_eq hα]; exact hβ
  have hnr : ∀ r, Label.ret p r ∉ β := fun r hr' =>
    hr r ((List.prefix_append β [ℓ]).trans hpre |>.subset hr')
  have hDp : D.pend p = some (.lookup v) := pend_of_runFrom h hβ hp hnr
  obtain ⟨h1, h2, -⟩ := lkInv_of_run h hrD p v hDp
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq
      exact absurd (Impl.step_inv hs).1 (by simp [hDp])
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      exact absurd (by simp [(Impl.step_ret hs).2.1]) hD'
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, x, o, k, hact, -, hloc⟩ := Impl.step_tau hs
      obtain ⟨a, b, c⟩ := lookup_act h h1 h2 hact (((Mem K m P x).δ (D.mem x) o).2)
      have hloc' : D'.loc q = k (((Mem K m P x).δ (D.mem x) o).2) := by
        rw [hloc, update_self]
      simp only [hloc', b.trans h1, a, and_self, ite_true, h1, h2]
      exact ⟨c.le, fun _ => c⟩
  · rw [(Impl.step_other hs hq).1]
    exact ⟨le_rfl, fun h5 => absurd (by rw [h5]; rfl) hq⟩

end Podc.LockFreeLinearProbing
