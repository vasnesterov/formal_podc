import Papers.PODC2026.LockFreeLinearProbing.Prop2

/-!
# Lock-freedom (Section 5.3, Lemmas 15–19)

A potential argument. Every successful `SC` consumes a unit of a global *budget*: each pending
operation holds a few units (3 before it owns a cell, 1 as an owner), plus credits on the cells
of owners (1 for a tentative copy, 2 for a copy marked `⟨v, revalidate⟩`); an idle process
holds 4. Between successful `SC`s every step of a process
decreases its *local potential* (scan positions, free-cell search position, duplicate-scan
position, and for the retry loops of `try_delete` and `del_copy` whether the last `LL` is still
valid). The potential `A · budget + Σ local` decreases at every step that is not a response.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] (h : K → Fin m)
variable {P : Type} [DecidableEq P]

/-! ## The potential -/

/-- Credit of an owner's cell: one for a tentative copy, two for a copy to be revalidated. -/
def credit : Cell K → ℕ
  | .key _ .tent => 1
  | .key _ .reval => 2
  | _ => 0

/-- The budget held by a process in local state `l` whose own cell holds `c`. -/
def budL (l : Loc K m) (c : Cell K) : ℕ :=
  match l.pc with
  | .idle => 4
  | .ret => 0
  | .fsLL | .bsLL | .vcSC | .vcRD | .tdSCF | .tdSCD | .tdLL | .iLL | .iSC => 3
  | _ => 1 + credit c

/-- The cell whose link matters for the retry loops (`try_delete`, `del_copy`). -/
def target (l : Loc K m) : Fin m :=
  match l.pc with
  | .dcSC78 | .dcSC80 => l.j
  | _ => l.i

/-- Forward-scan base potential at cell `i`. -/
def potF (v : K) (i : Fin m) : ℕ := 12 * m + 4 + 8 * (m - dist h v i)
/-- Backward-scan base potential at cell `i`. -/
def potB (v : K) (i : Fin m) : ℕ := 4 * m + 4 + 8 * dist h v i
/-- Free-cell search base potential at cell `j`. -/
def potS (v : K) (j : Fin m) : ℕ := 4 * (m - dist h v j)
/-- Duplicate-scan base potential at cell `i`. -/
def potD (v : K) (i : Fin m) : ℕ := 11 + 16 * (m - dist h v i)

/-- The local potential; `vld` says whether the process's link on `target l` is valid. -/
def locL (l : Loc K m) (vld : Bool) : ℕ :=
  let v := l.op.key
  let base := if l.fwd then potF h v l.i else potB h v l.i
  match l.pc with
  | .fsLL => potF h v l.i + 7
  | .bsLL => potB h v l.i + 7
  | .vcSC => base + 6
  | .vcRD => base + 5
  | .tdSCF => base + 4
  | .tdSCD => if vld then base + 3 else base + 6
  | .tdLL => base + 5
  | .iLL => potS h v l.j + 2
  | .iSC => potS h v l.j + 1
  | .dsLL => potD h v l.i + 15
  | .docRD => potD h v l.i + 14
  | .docSC => potD h v l.i + 13
  | .docRD2 => potD h v l.i + 12
  | .l57LL => 8
  | .l58SC => 7
  | .l66LL => 10
  | .l67SC => 9
  | .l69SC => 9
  | .dcLL76 => 3
  | .dcSC78 => if vld then 2 else 5
  | .dcLL79 => 2
  | .dcSC80 => if vld then 1 else 5
  | .ret | .idle => 0

/-- The budget of a configuration. -/
def budget [Fintype P] (C : Cfg K m P) : ℕ := ∑ q, budL (C.loc q) (C.val (C.loc q).j)

/-- The local potential of process `q` in `C`. -/
def locC (C : Cfg K m P) (q : P) : ℕ :=
  locL h (C.loc q) (decide (q ∈ C.lks (target (C.loc q))))

/-- The bound on local potentials. -/
def maxLoc (m : ℕ) : ℕ := 20 * m + 30

/-- The potential. -/
def pot [Fintype P] (C : Cfg K m P) : ℕ :=
  (maxLoc m * Fintype.card P + 1) * budget C + ∑ q, locC h C q

lemma dist_lt' (v : K) (i : Fin m) : dist h v i + 1 ≤ m := dist_lt h v i

lemma locL_le (l : Loc K m) (b : Bool) : locL h l b ≤ maxLoc m := by
  have h1 := dist_lt' h l.op.key l.i
  have h2 := dist_lt' h l.op.key l.j
  unfold locL maxLoc potF potB potS potD
  rcases l.pc <;> simp only <;> (try split_ifs) <;> omega

/-! ## Local potentials of the local computations -/

section Bounds

variable {h}
variable (l : Loc K m)

local notation "vk" => l.op.key

lemma potF_ge (v : K) (i : Fin m) : 12 * m + 12 ≤ potF h v i := by
  have := dist_lt' h v i; unfold potF; omega

lemma potB_ge (v : K) (i : Fin m) : 4 * m + 4 ≤ potB h v i := by unfold potB; omega

lemma potS_ge (v : K) (j : Fin m) : 4 ≤ potS h v j := by
  have := dist_lt' h v j; unfold potS; omega

lemma potD_ge (v : K) (i : Fin m) : 27 ≤ potD h v i := by
  have := dist_lt' h v i; unfold potD; omega

lemma potB_le (v : K) (i : Fin m) : potB h v i + 7 ≤ 12 * m + 3 := by
  have := dist_lt' h v i; unfold potB; omega

lemma loc_retL (r : Res) (b : Bool) : locL h (retL l r) b = 0 := by simp [locL, retL]

lemma loc_fsReturn (r : SR m) : locL h (fsReturn l r) true ≤ 12 * m + 3 := by
  unfold fsReturn
  split <;> first
    | (rw [loc_retL]; omega)
    | (simp only [locL]; exact potB_le _ _)

lemma loc_fsEnd : locL h (fsEnd h l) true ≤ 12 * m + 3 := by
  unfold fsEnd; split_ifs <;> exact loc_fsReturn _ _

lemma loc_fsNext : locL h (fsNext h l) true + 1 ≤ potF h vk l.i := by
  unfold fsNext; split_ifs with h1
  · have := loc_fsEnd (h := h) { l with i := l.i + 1 }; have := potF_ge (h := h) vk l.i; omega
  · have e := dist_succ h vk l.i h1
    have := dist_lt' h vk (l.i + 1)
    simp only [locL, potF]; rw [e]; omega

lemma loc_bsReturn (r : SR m) : locL h (bsReturn h l r) true ≤ 4 * m + 2 := by
  unfold bsReturn
  split <;> first
    | (rw [loc_retL]; omega)
    | (simp [locL, potS])

lemma loc_bsCheck : locL h (bsCheck h l) true + 1 ≤ potB h vk l.i := by
  unfold bsCheck; split_ifs with h1
  · have := loc_bsReturn (h := h) l .bot; have := potB_ge (h := h) vk l.i; omega
  · have e := dist_pred h vk l.i h1
    simp only [locL, potB]; omega

/-- The scan base potential of `l`. -/
def baseL (l : Loc K m) : ℕ := if l.fwd then potF h l.op.key l.i else potB h l.op.key l.i

lemma loc_vcRet (b : Bool) : locL h (vcRet h l b) true + 1 ≤ baseL (h := h) l := by
  unfold vcRet baseL
  have := potF_ge (h := h) vk l.i; have := potB_ge (h := h) vk l.i
  split_ifs with h1 h2 h2
  · have := loc_fsReturn (h := h) l .tt; omega
  · exact loc_fsNext l
  · have := loc_bsReturn (h := h) l .tt; omega
  · exact loc_bsCheck l

lemma loc_vcStart : locL h (vcStart h l) true ≤ baseL (h := h) l + 6 := by
  unfold vcStart; split_ifs
  · have := loc_vcRet (h := h) l true; omega
  · simp [locL, baseL]

lemma loc_tdRet (r : SR m) : locL h (tdRet h l r) true + 1 ≤ baseL (h := h) l := by
  unfold tdRet baseL
  have := potF_ge (h := h) vk l.i; have := potB_ge (h := h) vk l.i
  split
  · split_ifs
    · exact loc_fsNext l
    · exact loc_bsCheck l
  · split_ifs
    · have := loc_fsReturn (h := h) l r; omega
    · have := loc_bsReturn (h := h) l r; omega

lemma loc_tdBody : locL h (tdBody h l) true ≤ baseL (h := h) l + 4 := by
  unfold tdBody; split_ifs
  · simp [locL, baseL]
  · simp [locL, baseL]
  · have := loc_tdRet (h := h) l .bot; omega

lemma loc_fsBody : locL h (fsBody h l) true ≤ potF h vk l.i + 6 := by
  unfold fsBody
  have := potF_ge (h := h) vk l.i
  split_ifs
  · have := loc_fsEnd (h := h) l; omega
  · have := loc_vcStart (h := h) { l with fwd := true }; simpa [baseL] using this
  · have := loc_tdBody (h := h) { l with fwd := true }; simp [baseL] at this; omega
  · have := loc_fsNext (h := h) l; omega

lemma loc_bsBody : locL h (bsBody h l) true ≤ potB h vk l.i + 6 := by
  unfold bsBody
  split_ifs
  · have := loc_vcStart (h := h) { l with fwd := false }; simpa [baseL] using this
  · have := loc_tdBody (h := h) { l with fwd := false }; simp [baseL] at this; omega
  · have := loc_bsCheck (h := h) l; omega

lemma loc_iNext : locL h (iNext h l) true + 1 ≤ potS h vk l.j := by
  unfold iNext; split_ifs with h1
  · rw [loc_retL]; have := potS_ge (h := h) vk l.j; omega
  · have e := dist_succ h vk l.j h1
    have := dist_lt' h vk (l.j + 1)
    simp only [locL, potS]; rw [e]; omega

lemma loc_iBody : locL h (iBody h l) true ≤ potS h vk l.j + 1 := by
  unfold iBody; split_ifs
  · simp [locL]
  · have := loc_iNext (h := h) l; omega

lemma loc_dsNext : locL h (dsNext h l) true + 1 ≤ potD h vk l.i := by
  unfold dsNext; split_ifs with h1
  · have := potD_ge (h := h) vk l.i; simp only [locL]; omega
  · have e := dist_succ h vk l.i h1
    have := dist_lt' h vk (l.i + 1)
    simp only [locL, potD]; rw [e]; omega

lemma loc_dsBody : locL h (dsBody h l) true ≤ potD h vk l.i + 14 := by
  unfold dsBody
  have := potD_ge (h := h) vk l.i
  split_ifs
  · simp only [locL]; omega
  · simp only [locL]; omega
  · simp [locL]
  · have := loc_dsNext (h := h) l; omega
  · have := loc_dsNext (h := h) l; omega

lemma loc_docRet (b : Bool) : locL h (docRet h l b) true + 1 ≤ potD h vk l.i := by
  unfold docRet
  have := potD_ge (h := h) vk l.i
  split_ifs
  · exact loc_dsNext l
  · simp only [locL]; omega

/-! ### The local computations of scanning operations never lead to `idle` -/

lemma ni_retL (r : Res) : (retL l r).pc ≠ .idle := by simp [retL]
lemma ni_fsReturn (r : SR m) : (fsReturn l r).pc ≠ .idle := by
  unfold fsReturn; split <;> simp [retL]
lemma ni_fsEnd : (fsEnd h l).pc ≠ .idle := by unfold fsEnd; split_ifs <;> exact ni_fsReturn _ _
lemma ni_fsNext : (fsNext h l).pc ≠ .idle := by
  unfold fsNext; split_ifs
  · exact ni_fsEnd _
  · simp
lemma ni_bsReturn (r : SR m) : (bsReturn h l r).pc ≠ .idle := by
  unfold bsReturn; split <;> simp [retL]
lemma ni_bsCheck : (bsCheck h l).pc ≠ .idle := by
  unfold bsCheck; split_ifs
  · exact ni_bsReturn _ _
  · simp
lemma ni_vcRet (b : Bool) : (vcRet h l b).pc ≠ .idle := by
  unfold vcRet; split_ifs
  · exact ni_fsReturn _ _
  · exact ni_fsNext _
  · exact ni_bsReturn _ _
  · exact ni_bsCheck _
lemma ni_vcStart : (vcStart h l).pc ≠ .idle := by
  unfold vcStart; split_ifs
  · exact ni_vcRet _ _
  · simp
lemma ni_tdRet (r : SR m) : (tdRet h l r).pc ≠ .idle := by
  unfold tdRet; split
  · split_ifs
    · exact ni_fsNext _
    · exact ni_bsCheck _
  · split_ifs
    · exact ni_fsReturn _ _
    · exact ni_bsReturn _ _
lemma ni_tdBody : (tdBody h l).pc ≠ .idle := by
  unfold tdBody; split_ifs
  · simp
  · simp
  · exact ni_tdRet _ _
lemma ni_fsBody : (fsBody h l).pc ≠ .idle := by
  unfold fsBody; split_ifs
  · exact ni_fsEnd _
  · exact ni_vcStart _
  · exact ni_tdBody _
  · exact ni_fsNext _
lemma ni_bsBody : (bsBody h l).pc ≠ .idle := by
  unfold bsBody; split_ifs
  · exact ni_vcStart _
  · exact ni_tdBody _
  · exact ni_bsCheck _
lemma ni_iNext : (iNext h l).pc ≠ .idle := by
  unfold iNext; split_ifs
  · simp [retL]
  · simp
lemma ni_iBody : (iBody h l).pc ≠ .idle := by
  unfold iBody; split_ifs
  · simp
  · exact ni_iNext _

end Bounds

/-- The budget of a non-owner state that is neither idle nor about to return depends only on
the operation. -/
lemma budL_scan {l l' : Loc K m} (_hop : l'.op = l.op) (hv : l'.pc.isVal = false)
    (hi : l'.pc ≠ .idle) (hl : l.pc.isVal = false) (hli : l.pc ≠ .idle) (hlr : l.pc ≠ .ret)
    (c c' : Cell K) : budL l' c ≤ budL l c' := by
  unfold budL
  revert hv hi hl hli hlr
  cases l'.pc <;> cases l.pc <;> simp [PC.isVal]

end Podc.LockFreeLinearProbing
