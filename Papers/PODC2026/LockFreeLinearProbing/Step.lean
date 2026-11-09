import Papers.PODC2026.LockFreeLinearProbing.Defs

/-!
# Step lemmas for the hash table

Classification of program counters, the *local* invariant of a process (facts about its local
variables that hold by construction of the code), and the explicit form of the configuration
after a step of the implementation `impl h`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] (h : K → Fin m)
variable {P : Type} [DecidableEq P]

/-- Configurations of the hash table. -/
abbrev Cfg (K : Type) (m : ℕ) (P : Type) [DecidableEq K] [DecidableEq P] :=
  Config (dict K) (Mem K m P) P (Loc K m)

/-- The program counters of an `insert` that owns a cell (it wrote its tentative copy into
`table[j]` and has neither finalized nor withdrawn it): lines 48–73 and `del_copy`. -/
def PC.isVal : PC → Bool
  | .dsLL | .docRD | .docSC | .docRD2 | .l57LL | .l58SC | .l66LL | .l67SC | .l69SC | .dcLL76
  | .dcSC78 | .dcLL79 | .dcSC80 => true
  | _ => false

/-- The program counters of an `insert` looking for a free cell (lines 41–47). -/
def PC.isIns : PC → Bool
  | .iLL | .iSC => true
  | _ => false

/-- The cells that an owner has *covered* in its current duplicate scan: those strictly before
the scan position, or all cells once the scan is complete. -/
def covers (l : Loc K m) (c : Fin m) : Prop :=
  match l.pc with
  | .dsLL | .docRD | .docSC | .docRD2 => dist h l.op.key c < dist h l.op.key l.i
  | .l66LL | .l67SC | .l69SC => True
  | _ => False

/-- The cell and value that a process poised on an `SC` read with its last `LL`. -/
def recorded (l : Loc K m) : Option (Fin m × Cell K) :=
  match l.pc with
  | .vcSC | .tdSCF | .tdSCD | .docRD | .docSC => some (l.i, l.val)
  | .iSC | .dcSC78 | .dcSC80 => some (l.j, l.val)
  | .l58SC | .l67SC | .l69SC => some (l.j, l.cur)
  | _ => none

/-- Facts about the local variables that hold by the code. -/
def LocInv (l : Loc K m) : Prop :=
  match l.pc with
  | .vcSC => l.val = .key l.op.key .tent
  | .tdSCF => l.val = .key l.op.key .fin
  | .tdSCD => l.val.key? = some l.op.key ∧ l.val ≠ .key l.op.key .fin
  | .iSC => l.val = .empty ∨ l.val = .tomb
  | .docRD | .docSC => l.val = .key l.op.key .tent ∧ l.i ≠ l.j
  | .docRD2 => l.i ≠ l.j
  | .l67SC => l.cur = .key l.op.key .tent
  | .l58SC | .l69SC => l.cur = .key l.op.key .reval
  | .dcSC78 => l.val = .key l.op.key .reval
  | _ => True

end Podc.LockFreeLinearProbing

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] (h : K → Fin m)
variable {P : Type} [DecidableEq P]

/-- The value stored in cell `y`. -/
def Cfg.val (C : Cfg K m P) (y : Fin m) : Cell K := (C.mem y).1

/-- The processes holding a valid link on cell `y`. -/
def Cfg.lks (C : Cfg K m P) (y : Fin m) : List P := (C.mem y).2

/-- The invariant behind Lemma 4, with ghost round timestamps `ts` (the step at which an owner
last wrote its tentative copy) bounded by the number `N` of steps so far. -/
structure Inv (N : ℕ) (ts : P → ℕ) (C : Cfg K m P) : Prop where
  idle : ∀ p, C.pend p = none → (C.loc p).pc = .idle
  loc : ∀ p, LocInv (C.loc p)
  link : ∀ p x w, recorded (C.loc p) = some (x, w) → p ∈ C.lks x → C.val x = w
  own : ∀ p, (C.loc p).pc.isVal →
    C.val (C.loc p).j = .key (C.loc p).op.key .tent ∨
    C.val (C.loc p).j = .key (C.loc p).op.key .reval ∨
    C.val (C.loc p).j = .deleted ∨ C.val (C.loc p).j = .collided
  own_inj : ∀ p q, (C.loc p).pc.isVal → (C.loc q).pc.isVal → (C.loc p).j = (C.loc q).j → p = q
  own2 : ∀ c v t, C.val c = .key v t → t ≠ .fin →
    ∃ p, (C.loc p).pc.isVal ∧ (C.loc p).j = c ∧ (C.loc p).op.key = v
  p3 : ∀ c v t, C.val c = .key v t → ∀ c', dist h v c' ≤ dist h v c → C.val c' ≠ .empty
  p3' : ∀ p, ((C.loc p).pc.isIns ∨ (C.loc p).pc.isVal) → ∀ c',
    dist h (C.loc p).op.key c' < dist h (C.loc p).op.key (C.loc p).j → C.val c' ≠ .empty
  ts_lt : ∀ p, ts p < N
  a1 : ∀ I J, I ≠ J → (C.loc I).pc.isVal → (C.loc J).pc.isVal →
    (C.loc J).op.key = (C.loc I).op.key →
    C.val (C.loc J).j = .key (C.loc I).op.key .tent → covers h (C.loc I) (C.loc J).j →
    ts I < ts J
  doc : ∀ I J, ((((C.loc I).pc = .docRD ∨ (C.loc I).pc = .docSC) ∧ I ∉ C.lks (C.loc I).i) ∨
      (C.loc I).pc = .docRD2) → (C.loc J).pc.isVal → (C.loc J).j = (C.loc I).i →
    (C.loc J).op.key = (C.loc I).op.key →
    C.val (C.loc I).i = .key (C.loc I).op.key .tent → ts I < ts J
  a4 : ∀ J c, (C.loc J).pc.isVal → C.val (C.loc J).j = .key (C.loc J).op.key .tent →
    covers h (C.loc J) c → C.val c ≠ .key (C.loc J).op.key .fin
  l4 : ∀ v c c', C.val c = .key v .fin → C.val c' = .key v .fin → c = c'
  isc : ∀ p, (C.loc p).pc = .iSC → C.val (C.loc p).j = .empty → p ∈ C.lks (C.loc p).j

end Podc.LockFreeLinearProbing

namespace Podc.LockFreeLinearProbing

variable {K : Type} {m : ℕ} [NeZero m] (h : K → Fin m)

omit [NeZero m] in
lemma dist_lt (v : K) (i : Fin m) : dist h v i < m := (i - h v).isLt

@[simp] lemma dist_self (v : K) : dist h v (h v) = 0 := by simp [dist]

lemma dist_eq_zero_iff (v : K) (i : Fin m) : dist h v i = 0 ↔ i = h v := by
  simp [dist, Fin.val_eq_zero_iff, sub_eq_zero]

lemma dist_inj (v : K) {i j : Fin m} (hij : dist h v i = dist h v j) : i = j := by
  simp only [dist] at hij
  have := Fin.ext hij
  simpa using this

lemma dist_succ (v : K) (i : Fin m) (hi : i + 1 ≠ h v) : dist h v (i + 1) = dist h v i + 1 := by
  have e : i + 1 - h v = (i - h v) + 1 := by abel
  have hne : (i - h v) + 1 ≠ 0 := by
    intro h0; apply hi; rw [← e] at h0; exact sub_eq_zero.mp h0
  simp only [dist, e]
  rcases Nat.lt_or_ge 1 m with hm | hm
  · rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hm]
    have := (i - h v).isLt
    rcases Nat.lt_or_ge ((i - h v : Fin m).val + 1) m with h2 | h2
    · exact Nat.mod_eq_of_lt h2
    · exfalso; apply hne; ext; rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hm]
      have : (i - h v : Fin m).val + 1 = m := by omega
      rw [this, Nat.mod_self]; rfl
  · exfalso; apply hi
    have : m = 1 := by have := NeZero.pos m; omega
    subst this; exact Subsingleton.elim _ _

lemma dist_of_succ_eq (v : K) (i : Fin m) (hi : i + 1 = h v) : dist h v i = m - 1 := by
  have e : i - h v = -1 := by rw [← hi]; abel
  simp only [dist, e]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
  simp [Fin.coe_neg_one]

end Podc.LockFreeLinearProbing

namespace Podc.LockFreeLinearProbing

variable {K : Type} [DecidableEq K] {m : ℕ} [NeZero m] (h : K → Fin m)

/-- What the local computation of a scanning operation (forward/backward scan,
`validate_copy`, `try_delete`) can lead to: a non-owner state, at most the start of the free-cell
search, and a recorded `LL` value that is the one just read. -/
def ScanOut (l l' : Loc K m) : Prop :=
  l'.op = l.op ∧ l'.pc.isVal = false ∧ (l'.pc.isIns = true → l'.pc = .iLL ∧ l'.j = h l.op.key) ∧
    LocInv l' ∧ (recorded l' = none ∨ recorded l' = some (l.i, l.val))

/-- Like `ScanOut`, without a recorded value. -/
def ScanOut0 (l l' : Loc K m) : Prop :=
  l'.op = l.op ∧ l'.pc.isVal = false ∧ (l'.pc.isIns = true → l'.pc = .iLL ∧ l'.j = h l.op.key) ∧
    LocInv l' ∧ recorded l' = none

lemma ScanOut0.scanOut {l l' : Loc K m} (hs : ScanOut0 h l l') : ScanOut h l l' :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, Or.inl hs.2.2.2.2⟩

lemma ScanOut0.congr {l₁ l l' : Loc K m} (hs : ScanOut0 h l l') (hop : l.op = l₁.op) :
    ScanOut0 h l₁ l' := by
  obtain ⟨a, b, c, d, e⟩ := hs; exact ⟨a.trans hop, b, by rw [← hop]; exact c, d, e⟩

lemma scanOut0_retL (l : Loc K m) (r : Res) : ScanOut0 h l (retL l r) := by
  simp [ScanOut0, retL, PC.isVal, PC.isIns, LocInv, recorded]

lemma scanOut0_fsReturn (l : Loc K m) (r : SR m) : ScanOut0 h l (fsReturn l r) := by
  unfold fsReturn
  split <;> first
    | exact scanOut0_retL h _ _
    | simp [ScanOut0, PC.isVal, PC.isIns, LocInv, recorded]

lemma scanOut0_fsEnd (l : Loc K m) : ScanOut0 h l (fsEnd h l) := by
  unfold fsEnd; split_ifs <;> exact scanOut0_fsReturn h _ _

lemma scanOut0_fsNext (l : Loc K m) : ScanOut0 h l (fsNext h l) := by
  unfold fsNext; split_ifs
  · exact (scanOut0_fsEnd h _).congr h rfl
  · simp [ScanOut0, PC.isVal, PC.isIns, LocInv, recorded]

lemma scanOut0_bsReturn (l : Loc K m) (r : SR m) : ScanOut0 h l (bsReturn h l r) := by
  unfold bsReturn
  split <;> first
    | exact scanOut0_retL h _ _
    | simp_all [ScanOut0, PC.isVal, PC.isIns, LocInv, recorded, DOp.key]

lemma scanOut0_bsCheck (l : Loc K m) : ScanOut0 h l (bsCheck h l) := by
  unfold bsCheck; split_ifs
  · exact scanOut0_bsReturn h _ _
  · simp [ScanOut0, PC.isVal, PC.isIns, LocInv, recorded]

lemma scanOut0_vcRet (l : Loc K m) (b : Bool) : ScanOut0 h l (vcRet h l b) := by
  unfold vcRet; split_ifs
  · exact scanOut0_fsReturn h _ _
  · exact scanOut0_fsNext h _
  · exact scanOut0_bsReturn h _ _
  · exact scanOut0_bsCheck h _

lemma scanOut0_tdRet (l : Loc K m) (r : SR m) : ScanOut0 h l (tdRet h l r) := by
  unfold tdRet
  split
  · split_ifs
    · exact scanOut0_fsNext h _
    · exact scanOut0_bsCheck h _
  · split_ifs
    · exact scanOut0_fsReturn h _ _
    · exact scanOut0_bsReturn h _ _

lemma scanOut_vcStart (l : Loc K m) (hk : l.val.key? = some l.op.key) :
    ScanOut h l (vcStart h l) := by
  unfold vcStart; split_ifs with h1
  · exact (scanOut0_vcRet h _ _).scanOut h
  · refine ⟨rfl, rfl, by simp [PC.isIns], ?_, Or.inr rfl⟩
    simp only [LocInv]
    push Not at h1
    rcases hv : l.val with _ | _ | _ | _ | ⟨w, t⟩ <;> simp_all [Cell.key?]
    cases t <;> simp_all

lemma scanOut_tdBody (l : Loc K m) : ScanOut h l (tdBody h l) := by
  unfold tdBody; split_ifs with h1 h2
  · exact ⟨rfl, rfl, by simp [PC.isIns], by simpa [LocInv] using h2, Or.inr rfl⟩
  · exact ⟨rfl, rfl, by simp [PC.isIns], by simp only [LocInv]; exact ⟨h1, h2⟩, Or.inr rfl⟩
  · exact (scanOut0_tdRet h _ _).scanOut h

lemma scanOut_fsBody (l : Loc K m) : ScanOut h l (fsBody h l) := by
  unfold fsBody; split_ifs with h1 h2 h3
  · exact (scanOut0_fsEnd h _).scanOut h
  · exact scanOut_vcStart h { l with fwd := true } h2
  · exact scanOut_tdBody h { l with fwd := true }
  · exact (scanOut0_fsNext h _).scanOut h

lemma scanOut_bsBody (l : Loc K m) : ScanOut h l (bsBody h l) := by
  unfold bsBody; split_ifs with h2 h3
  · exact scanOut_vcStart h { l with fwd := false } h2
  · exact scanOut_tdBody h { l with fwd := false }
  · exact (scanOut0_bsCheck h _).scanOut h

end Podc.LockFreeLinearProbing
