import Papers.PODC2026.LockFreeLinearProbing.LockFree
import Cslib.Foundations.Data.Finset.SumUpdate

/-!
# Lock-freedom: the potential decreases at every step that is not a response
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] [Fintype P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

/-- The budget term of process `q`. -/
abbrev bud (C : Cfg K m P) (q : P) : ℕ := budL (C.loc q) (C.val (C.loc q).j)

lemma sum_locC_le (C : Cfg K m P) : ∑ q, locC h C q ≤ Fintype.card P * maxLoc m := by
  calc ∑ q, locC h C q ≤ ∑ _q : P, maxLoc m := Finset.sum_le_sum fun q _ => locL_le h _ _
    _ = Fintype.card P * maxLoc m := by simp

/-- A step that decreases the budget decreases the potential. -/
lemma pot_lt_of_budget_lt (hb : budget C' < budget C) : pot h C' < pot h C := by
  unfold pot
  have h1 := sum_locC_le (h := h) C'
  have h2 : (maxLoc m * Fintype.card P + 1) * budget C' + (maxLoc m * Fintype.card P + 1) ≤
      (maxLoc m * Fintype.card P + 1) * budget C := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb
  have : Fintype.card P * maxLoc m = maxLoc m * Fintype.card P := Nat.mul_comm _ _
  omega

/-- A step that does not increase the budget and decreases the local potentials decreases the
potential. -/
lemma pot_lt_of_local (hb : budget C' ≤ budget C) (hl : ∑ q, locC h C' q < ∑ q, locC h C q) :
    pot h C' < pot h C := by
  unfold pot
  have := Nat.mul_le_mul_left (maxLoc m * Fintype.card P + 1) hb
  omega

/-- Two budget terms change. -/
lemma budget_lt_two {o : P} (hpo : p ≠ o) (hoth : ∀ q, q ≠ p → q ≠ o → bud C' q = bud C q)
    (hlt : bud C' p + bud C' o < bud C p + bud C o) : budget C' < budget C := by
  change ∑ q, bud C' q < ∑ q, bud C q
  have hp : p ∈ (Finset.univ : Finset P) := Finset.mem_univ _
  have ho : o ∈ (Finset.univ : Finset P).erase p := Finset.mem_erase.2 ⟨Ne.symm hpo, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hp, ← Finset.add_sum_erase _ _ ho,
    ← Finset.add_sum_erase _ (fun q => bud C q) hp, ← Finset.add_sum_erase _ (fun q => bud C q) ho]
  have : ∑ q ∈ ((Finset.univ : Finset P).erase p).erase o, bud C' q =
      ∑ q ∈ ((Finset.univ : Finset P).erase p).erase o, bud C q := by
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_erase] at hq
    exact hoth q hq.2.1 hq.1
  omega

/-- One budget term changes. -/
lemma budget_lt_one (hoth : ∀ q, q ≠ p → bud C' q = bud C q) (hlt : bud C' p < bud C p) :
    budget C' < budget C :=
  Fintype.sum_lt_sum_of_eq_off p hoth hlt

/-- A step that changes no cell value: the other processes keep their budget and local
potential. -/
lemma others_same {l' : Loc K m} {x : Fin m} {c' : Cell K × List P} (hv : c'.1 = C.val x)
    (hlk : ∀ q, q ≠ p → (q ∈ c'.2 ↔ q ∈ C.lks x)) (q : P) (hq : q ≠ p) :
    bud (upd C p l' x c') q = bud C q ∧ locC h (upd C p l' x c') q = locC h C q := by
  have hval : ∀ y, (upd C p l' x c').val y = C.val y := by
    intro y; rw [mem_val_upd]; split_ifs with h1
    · rw [h1]; exact hv
    · rfl
  have hl : ∀ y, q ∈ (upd C p l' x c').lks y ↔ q ∈ C.lks y := by
    intro y; by_cases h1 : y = x
    · subst h1; simp only [upd_lks_self]; exact hlk q hq
    · rw [upd_lks_ne _ _ _ _ h1]
  refine ⟨?_, ?_⟩
  · simp only [bud, upd_loc_ne _ _ _ _ hq, hval]
  · simp only [locC, upd_loc_ne _ _ _ _ hq]
    congr 1; simp only [decide_eq_decide]; exact hl _

/-- A step of `p` that changes no cell value and decreases `p`'s local potential, without
increasing its budget. -/
lemma pot_unchanged {l' : Loc K m} {x : Fin m} {c' : Cell K × List P} (hv : c'.1 = C.val x)
    (hlk : ∀ q, q ≠ p → (q ∈ c'.2 ↔ q ∈ C.lks x))
    (hbud : budL l' (C.val l'.j) ≤ budL (C.loc p) (C.val (C.loc p).j))
    (hloc : locL h l' (decide (p ∈ (upd C p l' x c').lks (target l'))) < locC h C p) :
    pot h (upd C p l' x c') < pot h C := by
  have hval : ∀ y, (upd C p l' x c').val y = C.val y := by
    intro y; rw [mem_val_upd]; split_ifs with h1
    · rw [h1]; exact hv
    · rfl
  apply pot_lt_of_local
  · unfold budget
    exact Fintype.sum_le_sum_of_eq_off p (fun q hq => (others_same (h := h) hv hlk q hq).1)
      (by simp only [upd_loc_self, hval]; exact hbud)
  · exact Fintype.sum_lt_sum_of_eq_off p (fun q hq => (others_same (h := h) hv hlk q hq).2)
      (by simp only [locC, upd_loc_self]; exact hloc)

/-- Program counters whose local potential depends on the validity of the link. -/
def PC.dep : PC → Bool
  | .tdSCD | .dcSC78 | .dcSC80 => true
  | _ => false

lemma locL_vld {l : Loc K m} (hl : l.pc.dep = false) (b : Bool) : locL h l b = locL h l true := by
  unfold locL; revert hl; cases l.pc <;> simp [PC.dep]

/-- An `LL` of cell `x` by `p`. -/
lemma pot_LL (hs : (impl h).step C (.tau p) = some C') {x : Fin m}
    {k : Cell K × Bool → Loc K m} (hact : act h p (C.loc p) = .access x (.ll p) k)
    (hdep : (k (C.val x, true)).pc.dep = true → target (k (C.val x, true)) = x)
    (hbud : budL (k (C.val x, true)) (C.val (k (C.val x, true)).j) ≤ bud C p)
    (hloc : locL h (k (C.val x, true)) true < locC h C p) : pot h C' < pot h C := by
  obtain ⟨-, rfl⟩ := step_tau_access hs hact
  show pot h (upd C p (k (C.val x, true)) x (C.val x, if p ∈ C.lks x then C.lks x else p :: C.lks x))
    < pot h C
  refine pot_unchanged (l' := k (C.val x, true)) (x := x)
    (c' := (C.val x, if p ∈ C.lks x then C.lks x else p :: C.lks x)) rfl
    (fun q hq => mem_addLink_iff hq) hbud ?_
  cases hd : (k (C.val x, true)).pc.dep
  · rw [locL_vld hd]; exact hloc
  · rw [hdep hd]; simp only [upd_lks_self]
    have : p ∈ (if p ∈ C.lks x then C.lks x else p :: C.lks x) := mem_addLink_self _
    simp only [Cfg.lks] at this hloc ⊢
    simp only [this, decide_true]; exact hloc

/-- A plain read (`VL`) of cell `x` by `p`. -/
lemma pot_VL (hs : (impl h).step C (.tau p) = some C') {x : Fin m}
    {k : Cell K × Bool → Loc K m} (hact : act h p (C.loc p) = .access x (.vl p) k)
    (hdep : (k (C.val x, decide (p ∈ C.lks x))).pc.dep = false)
    (hbud : budL (k (C.val x, decide (p ∈ C.lks x)))
      (C.val (k (C.val x, decide (p ∈ C.lks x))).j) ≤ bud C p)
    (hloc : locL h (k (C.val x, decide (p ∈ C.lks x))) true < locC h C p) :
    pot h C' < pot h C := by
  obtain ⟨-, rfl⟩ := step_tau_access hs hact
  show pot h (upd C p (k (C.val x, decide (p ∈ C.lks x))) x (C.val x, C.lks x)) < pot h C
  refine pot_unchanged (l' := k (C.val x, decide (p ∈ C.lks x))) (x := x) (c' := (C.val x, C.lks x))
    rfl (fun _ _ => Iff.rfl) hbud ?_
  rw [locL_vld hdep]; exact hloc

/-- A failed `SC` on cell `x` by `p`. -/
lemma pot_SCfail (hs : (impl h).step C (.tau p) = some C') {x : Fin m} {w : Cell K}
    {k : Cell K × Bool → Loc K m} (hact : act h p (C.loc p) = .access x (.sc p w) k)
    (hsc : p ∉ C.lks x) (hpre : (C.loc p).pc.dep = true → target (C.loc p) = x)
    (hdep : (k (C.val x, false)).pc.dep = false)
    (hbud : budL (k (C.val x, false)) (C.val (k (C.val x, false)).j) ≤ bud C p)
    (hloc : locL h (k (C.val x, false)) true < locL h (C.loc p) false) :
    pot h C' < pot h C := by
  obtain ⟨-, rfl⟩ := step_tau_access hs hact
  have hsc' : p ∉ (C.mem x).2 := hsc
  show pot h (upd C p (k (if p ∈ (C.mem x).2 then ((w, []), (C.mem x).1, true)
    else (C.mem x, (C.mem x).1, false)).2) x (if p ∈ (C.mem x).2 then ((w, []), (C.mem x).1, true)
    else (C.mem x, (C.mem x).1, false)).1) < pot h C
  simp only [hsc', ite_false]
  refine pot_unchanged (l' := k (C.val x, false)) (x := x) (c' := (C.val x, C.lks x))
    rfl (fun _ _ => Iff.rfl) hbud ?_
  rw [locL_vld hdep]
  have : locC h C p = locL h (C.loc p) false := by
    unfold locC
    cases hd : (C.loc p).pc.dep
    · rw [locL_vld hd, locL_vld hd false]
    · rw [hpre hd]; simp [Cfg.lks, hsc']
  rw [this]; exact hloc

/-- `pot_SCfail` with the failure state given explicitly. -/
lemma pot_SCfail' (hs : (impl h).step C (.tau p) = some C') {x : Fin m} {w : Cell K}
    {k : Cell K × Bool → Loc K m} (hact : act h p (C.loc p) = .access x (.sc p w) k)
    (hsc : p ∉ C.lks x) (hpre : (C.loc p).pc.dep = true → target (C.loc p) = x)
    (l' : Loc K m) (hk : k (C.val x, false) = l') (hdep : l'.pc.dep = false)
    (hbud : budL l' (C.val l'.j) ≤ bud C p)
    (hloc : locL h l' true < locL h (C.loc p) false) : pot h C' < pot h C := by
  subst hk; exact pot_SCfail hs hact hsc hpre hdep hbud hloc

/-- `pot_LL` with the new state given explicitly. -/
lemma pot_LL' (hs : (impl h).step C (.tau p) = some C') {x : Fin m}
    {k : Cell K × Bool → Loc K m} (hact : act h p (C.loc p) = .access x (.ll p) k)
    (l' : Loc K m) (hk : k (C.val x, true) = l')
    (hdep : l'.pc.dep = true → target l' = x) (hbud : budL l' (C.val l'.j) ≤ bud C p)
    (hloc : locL h l' true < locC h C p) : pot h C' < pot h C := by
  subst hk; exact pot_LL hs hact hdep hbud hloc

/-- `pot_VL` with the new state given explicitly. -/
lemma pot_VL' (hs : (impl h).step C (.tau p) = some C') {x : Fin m}
    {k : Cell K × Bool → Loc K m} (hact : act h p (C.loc p) = .access x (.vl p) k)
    (l' : Loc K m) (hk : k (C.val x, decide (p ∈ C.lks x)) = l')
    (hdep : l'.pc.dep = false) (hbud : budL l' (C.val l'.j) ≤ bud C p)
    (hloc : locL h l' true < locC h C p) : pot h C' < pot h C := by
  subst hk; exact pot_VL hs hact hdep hbud hloc

/-- The budget term of `q ≠ p` after `p` writes `c'` into `x`. -/
lemma bud_upd_ne {l' : Loc K m} {x : Fin m} {c' : Cell K × List P} {q : P} (hq : q ≠ p) :
    bud (upd C p l' x c') q = budL (C.loc q) (if (C.loc q).j = x then c'.1 else C.val (C.loc q).j) := by
  simp only [bud, upd_loc_ne _ _ _ _ hq, mem_val_upd]

lemma budL_nonval {l : Loc K m} (hl : l.pc.isVal = false) (c c' : Cell K) :
    budL l c = budL l c' := by
  unfold budL; revert hl; cases l.pc <;> simp [PC.isVal]

/-- A successful `SC` of `p` into `x` changes the budget terms of `p` and of the owner of `x`
only. -/
lemma bud_upd_other {l' : Loc K m} {x : Fin m} {c' : Cell K × List P}
    {q : P} (hq : q ≠ p) (hown : ¬ ((C.loc q).pc.isVal ∧ (C.loc q).j = x)) :
    bud (upd C p l' x c') q = bud C q := by
  rw [bud_upd_ne hq]
  by_cases h1 : (C.loc q).j = x
  · rw [if_pos h1]
    have : (C.loc q).pc.isVal = false := by
      cases h2 : (C.loc q).pc.isVal
      · rfl
      · exact absurd ⟨h2, h1⟩ hown
    exact budL_nonval this _ _
  · rw [if_neg h1]

lemma dep_of_scanOut {l l' : Loc K m} (hs : ScanOut h l l') :
    l'.pc.dep = true → target l' = l.i := by
  obtain ⟨-, hnv, -, -, hrec⟩ := hs
  intro hd
  have : l'.pc = .tdSCD := by revert hnv hd; cases l'.pc <;> simp [PC.dep, PC.isVal]
  rcases hrec with hr | hr <;> simp only [recorded, this] at hr
  · cases hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr; simp [target, this, hr.1]

lemma dep_of_scanOut0 {l l' : Loc K m} (hs : ScanOut0 h l l') : l'.pc.dep = false := by
  obtain ⟨-, hnv, -, -, hrec⟩ := hs
  revert hnv hrec; unfold recorded; cases l'.pc <;> simp [PC.dep, PC.isVal]

lemma fsReturn_tt (l : Loc K m) : (fsReturn l .tt).pc = .ret := by
  rcases hop : l.op <;> simp [fsReturn, hop, retL]

lemma bsReturn_tt (l : Loc K m) : (bsReturn h l .tt).pc = .ret := by
  rcases hop : l.op <;> simp [bsReturn, hop, retL]

lemma vcRet_true_ret (l : Loc K m) : (vcRet h l true).pc = .ret := by
  unfold vcRet; simp only [ite_true]; split_ifs
  · exact fsReturn_tt l
  · exact bsReturn_tt l

lemma tdRet_tt_ret (l : Loc K m) : (tdRet h l .tt).pc = .ret := by
  unfold tdRet; simp only; split_ifs
  · exact fsReturn_tt l
  · exact bsReturn_tt l

/-- A successful `SC` that decreases the budget. -/
lemma pot_SCsucc (hs : (impl h).step C (.tau p) = some C') {x : Fin m} {w : Cell K}
    {k : Cell K × Bool → Loc K m} (hact : act h p (C.loc p) = .access x (.sc p w) k)
    (hsc : p ∈ C.lks x) (hb : budget (upd C p (k (C.val x, true)) x (w, [])) < budget C) :
    pot h C' < pot h C := by
  obtain ⟨-, rfl⟩ := step_tau_access hs hact
  have hsc' : p ∈ (C.mem x).2 := hsc
  show pot h (upd C p (k (if p ∈ (C.mem x).2 then ((w, []), (C.mem x).1, true)
    else (C.mem x, (C.mem x).1, false)).2) x (if p ∈ (C.mem x).2 then ((w, []), (C.mem x).1, true)
    else (C.mem x, (C.mem x).1, false)).1) < pot h C
  simp only [hsc', ite_true]
  exact pot_lt_of_budget_lt hb

lemma bud_upd_self {l' : Loc K m} {x : Fin m} {c' : Cell K × List P} :
    bud (upd C p l' x c') p = budL l' (if l'.j = x then c'.1 else C.val l'.j) := by
  simp only [bud, upd_loc_self, mem_val_upd]

/-- No owner other than `p` owns `x`. -/
lemma budget_lt_noOwner {l' : Loc K m} {x : Fin m} {c' : Cell K × List P}
    (hno : ∀ q, q ≠ p → ¬ ((C.loc q).pc.isVal ∧ (C.loc q).j = x))
    (hlt : budL l' (if l'.j = x then c'.1 else C.val l'.j) < bud C p) :
    budget (upd C p l' x c') < budget C :=
  budget_lt_one (fun q hq => bud_upd_other hq (hno q hq)) (by rw [bud_upd_self]; exact hlt)

/-- The owner `o` of `x` changes too. -/
lemma budget_lt_owner (hI : Inv h N ts C) {l' : Loc K m} {x : Fin m} {c' : Cell K × List P}
    {o : P} (hpo : p ≠ o) (ho : (C.loc o).pc.isVal) (hox : (C.loc o).j = x)
    (hlt : budL l' (if l'.j = x then c'.1 else C.val l'.j) + budL (C.loc o) c'.1 <
      bud C p + bud C o) :
    budget (upd C p l' x c') < budget C := by
  refine budget_lt_two hpo (fun q hq hqo => bud_upd_other hq ?_) ?_
  · rintro ⟨h1, h2⟩; exact hqo (hI.own_inj q o h1 ho (h2.trans hox.symm))
  · rw [bud_upd_self, bud_upd_ne (Ne.symm hpo), if_pos hox]; exact hlt

end Podc.LockFreeLinearProbing
