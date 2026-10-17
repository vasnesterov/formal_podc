import Papers.PODC2024.HistoryIndependent.Universal
import Podc.Computability.Distributed.SharedMemory.Model
import Podc.Computability.Distributed.SharedMemory.StrongLin
import Cslib.Computability.Distributed.SharedMemory.Linearization
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Model
import Mathlib

/-!
# Algorithm 5: the invariant

We prove a single inductive invariant (`Universal.Inv`) of all executions of Algorithm 5 (with
atomic R-LLSC base objects). It replaces the paper's Invariants 21–22 and Lemmas 23, 24, 26, 39:
instead of reasoning about "modes" `A_i`/`B_i` of the whole execution, it describes the
configuration reached, together with the linearization `hlin α` built so far.

The linearization function `hlin` appends

* a state-changing operation of `p_j` at the successful `SC(head, ⟨q', ⟨r, j⟩⟩)` (line 14) that
  applies it (the paper's transition from mode `A_{i-1}` to `B_i`), and
* a read-only operation at its `Load(head)` (line 1).

(The paper places a read-only operation after the state-changing operation of the segment it
reads from, ordering read-only operations of the same segment by invocation; linearizing it at
its `Load` is the same up to the order of read-only operations within a segment, which is
irrelevant.)
-/

namespace Cslib.SharedMemory

open List


namespace Universal

variable {A : ObjSpec} {n : ℕ}

/-! ## Views of the memory -/

/-- Memory configurations of Algorithm 5. -/
abbrev Mem (A : ObjSpec) (n : ℕ) := (i : Obj n) → (B A n i).State

/-- The value of `head`. -/
def hv (m : Mem A n) : HeadVal A n := (m .head).1
/-- The context of `head`. -/
def hc (m : Mem A n) : Finset (Fin n) := (m .head).2
/-- The value of `announce[j]`. -/
def av (m : Mem A n) (j : Fin n) : AnnVal A := (m (.ann j)).1
/-- The context of `announce[j]`. -/
def ac (m : Mem A n) (j : Fin n) : Finset (Fin n) := (m (.ann j)).2

section Update

variable (m : Mem A n)

@[simp] lemma hv_update_head (s : (B A n .head).State) :
    hv (Function.update m .head s) = s.1 := by simp [hv]
@[simp] lemma hc_update_head (s : (B A n .head).State) :
    hc (Function.update m .head s) = s.2 := by simp [hc]
@[simp] lemma av_update_head (s : (B A n .head).State) (j : Fin n) :
    av (Function.update m .head s) j = av m j := by simp [av]
@[simp] lemma ac_update_head (s : (B A n .head).State) (j : Fin n) :
    ac (Function.update m .head s) j = ac m j := by simp [ac]
@[simp] lemma hv_update_ann (j : Fin n) (s : (B A n (.ann j)).State) :
    hv (Function.update m (.ann j) s) = hv m := by simp [hv]
@[simp] lemma hc_update_ann (j : Fin n) (s : (B A n (.ann j)).State) :
    hc (Function.update m (.ann j) s) = hc m := by simp [hc]

lemma av_update_ann (j k : Fin n) (s : (B A n (.ann j)).State) :
    av (Function.update m (.ann j) s) k = if k = j then s.1 else av m k := by
  by_cases h : k = j
  · subst h; simp [av]
  · simp [av, h]

lemma ac_update_ann (j k : Fin n) (s : (B A n (.ann j)).State) :
    ac (Function.update m (.ann j) s) k = if k = j then s.2 else ac m k := by
  by_cases h : k = j
  · subst h; simp [ac]
  · simp [ac, h]

@[simp] lemma av_update_ann_self (j : Fin n) (s : (B A n (.ann j)).State) :
    av (Function.update m (.ann j) s) j = s.1 := by simp [av_update_ann]
@[simp] lemma ac_update_ann_self (j : Fin n) (s : (B A n (.ann j)).State) :
    ac (Function.update m (.ann j) s) j = s.2 := by simp [ac_update_ann]

@[simp] lemma av_update_ann_same (j k : Fin n) (s : Finset (Fin n)) :
    av (Function.update m (.ann j) (av m j, s)) k = av m k := by
  rw [av_update_ann]; split_ifs with h <;> simp [h]

lemma av_update_ann_ne {j k : Fin n} (h : k ≠ j) (s : (B A n (.ann j)).State) :
    av (Function.update m (.ann j) s) k = av m k := by simp [av_update_ann, h]
lemma ac_update_ann_ne {j k : Fin n} (h : k ≠ j) (s : (B A n (.ann j)).State) :
    ac (Function.update m (.ann j) s) k = ac m k := by simp [ac_update_ann, h]

end Update

section Delta

variable (p : Fin n)

@[simp] lemma δh_ll (s : (B A n .head).State) :
    (B A n .head).δ s (.ll p) = ((s.1, insert p s.2), .inl s.1) := rfl
@[simp] lemma δh_vl (s : (B A n .head).State) :
    (B A n .head).δ s (.vl p) = (s, .inr (decide (p ∈ s.2))) := rfl
@[simp] lemma δh_sc (s : (B A n .head).State) (v : HeadVal A n) :
    (B A n .head).δ s (.sc p v) = if p ∈ s.2 then ((v, ∅), .inr true) else (s, .inr false) := rfl
@[simp] lemma δh_rl (s : (B A n .head).State) :
    (B A n .head).δ s (.rl p) = ((s.1, s.2.erase p), .inr true) := rfl
@[simp] lemma δh_load (s : (B A n .head).State) :
    (B A n .head).δ s .load = (s, .inl s.1) := rfl
@[simp] lemma δa_ll (j : Fin n) (s : (B A n (.ann j)).State) :
    (B A n (.ann j)).δ s (.ll p) = ((s.1, insert p s.2), .inl s.1) := rfl
@[simp] lemma δa_sc (j : Fin n) (s : (B A n (.ann j)).State) (v : AnnVal A) :
    (B A n (.ann j)).δ s (.sc p v) = if p ∈ s.2 then ((v, ∅), .inr true) else (s, .inr false) :=
  rfl
@[simp] lemma δa_rl (j : Fin n) (s : (B A n (.ann j)).State) :
    (B A n (.ann j)).δ s (.rl p) = ((s.1, s.2.erase p), .inr true) := rfl
@[simp] lemma δa_load (j : Fin n) (s : (B A n (.ann j)).State) :
    (B A n (.ann j)).δ s .load = (s, .inl s.1) := rfl
@[simp] lemma δa_store (j : Fin n) (s : (B A n (.ann j)).State) (v : AnnVal A) :
    (B A n (.ann j)).δ s (.store v) = ((v, ∅), .inr true) := rfl

end Delta

section Fold

variable (m : Mem A n) (j : Fin n)

@[simp] lemma head_fst : (m .head).1 = hv m := rfl
@[simp] lemma head_snd : (m .head).2 = hc m := rfl
@[simp] lemma ann_fst : (m (.ann j)).1 = av m j := rfl
@[simp] lemma ann_snd : (m (.ann j)).2 = ac m j := rfl

@[simp] lemma update_head_self : Function.update m .head (hv m, hc m) = m :=
  Function.update_eq_self _ _
@[simp] lemma update_ann_self : Function.update m (.ann j) (av m j, ac m j) = m :=
  Function.update_eq_self _ _

end Fold

/-! ## Classes of program counters -/

/-- The main loop (lines 5–23). -/
def PC.inLoop : PC A n → Bool
  | .loop | .llHead | .help | .own | .scApply _ _ | .llAnn | .vl | .scAnn | .scHead | .rlAnn => true
  | _ => false

/-- Program counters at which a process may belong to `head.context`. -/
def PC.mayHC : PC A n → Bool
  | .resp | .llHead2 _ | .clear _ | .rlHead _ | .rl18 _ => true
  | pc => pc.inLoop

/-- Lines 19–22 (after `LL(announce[j])`). -/
def PC.inVL : PC A n → Bool
  | .vl | .scAnn | .scHead | .rlAnn => true
  | _ => false

/-- Lines 19–21. -/
def PC.inK3 : PC A n → Bool
  | .vl | .scAnn | .scHead => true
  | _ => false

/-! ## The invariant -/

/-- The response the linearization `L` gives to `x` (`none` if `x ∉ L`). -/
abbrev specResp (L : List (OpId (Fin n) × A.Op)) (x : OpId (Fin n)) : Option A.Resp :=
  A.respIn A.init L x

/-- The status of process `q` (with current instance `x` and pending operation `pd`), according
to its program counter: what `announce[q]` holds and whether (and with which response) its
current operation is linearized. -/
def PInv (L : List (OpId (Fin n) × A.Op)) (x : OpId (Fin n)) (pd : Option A.Op) (m : Mem A n)
    (q : Fin n) : PC A n → Prop
  | .idle => pd = none ∧ av m q = none
  | .ro o => pd = some o ∧ A.ReadOnly o ∧ av m q = none ∧ specResp L x = none
  | .roRet r => (∃ o, pd = some o ∧ A.ReadOnly o) ∧ av m q = none ∧ specResp L x = some r
  | .ann o => pd = some o ∧ ¬ A.ReadOnly o ∧ av m q = none ∧ specResp L x = none
  | .resp | .rl18 _ => (∃ o, pd = some o ∧ ¬ A.ReadOnly o) ∧
      ∃ r, av m q = some (.inr r) ∧ specResp L x = some r
  | .llHead2 r | .clear r | .rlHead r | .storeBot r => (∃ o, pd = some o ∧ ¬ A.ReadOnly o) ∧
      av m q = some (.inr r) ∧ specResp L x = some r
  | .retSC r => (∃ o, pd = some o ∧ ¬ A.ReadOnly o) ∧ av m q = none ∧ specResp L x = some r
  | _ => ∃ o, pd = some o ∧ ¬ A.ReadOnly o ∧
      ((av m q = some (.inl o) ∧ (specResp L x ≠ none → ∃ rsp, (hv m).2 = some (rsp, q))) ∨
        ∃ r, av m q = some (.inr r) ∧ specResp L x = some r)

/-- Consistency of local variables with the program counter. -/
def LocInv (q : Fin n) (l : Loc A n) : Prop :=
  match l.pc with
  | .help | .own => l.hd.2 = none
  | .scApply j _ => l.hd.2 = none ∧ (j = l.prio ∨ j = q)
  | .llAnn => l.hd.2.isSome
  | .vl | .scHead => ∃ rsp, l.hd.2 = some (rsp, l.aj)
  | .scAnn => (∃ rsp, l.hd.2 = some (rsp, l.aj)) ∧ isOp l.a
  | .clear _ => ∃ rsp, l.hd.2 = some (rsp, q)
  | _ => True

/-- The part of the invariant concerning process `q` (local state `l`, pending operation `pd`,
current instance `x`). -/
structure ProcOK (L : List (OpId (Fin n) × A.Op)) (x : OpId (Fin n)) (pd : Option A.Op)
    (m : Mem A n) (q : Fin n) (l : Loc A n) : Prop where
  pinv : PInv L x pd m q l.pc
  ch : q ∈ hc m → l.hd = hv m ∧ l.pc.mayHC
  ca1 : ∀ j, q ∈ ac m j → l.aj = j → av m j = l.a
  ca2 : ∀ j, q ∈ ac m j → (l.aj = j ∧ l.pc.inVL) ∨ av m j ≠ none
  k3 : q ∈ hc m → l.pc.inK3 → q ∉ ac m l.aj → ∀ o, av m l.aj ≠ some (.inl o)
  k4 : l.pc = .scHead → isOp l.a → q ∉ ac m l.aj
  k5 : l.pc = .scAnn → q ∈ ac m l.aj → q ∈ hc m
  k6 : ∀ j o, l.pc = .scApply j o → q ∈ hc m → av m j = some (.inl o)
  loc : LocInv q l
  h2 : ∀ rsp, (hv m).2 = some (rsp, q) → specResp L x = some rsp ∧
    (l.pc.inLoop ∨ l.pc = .resp ∨ (∃ r, l.pc = .llHead2 r) ∨ (∃ r, l.pc = .clear r ∧ q ∈ hc m) ∨
      ∃ j, l.pc = .rl18 j)

/-- The configuration part of the invariant, for a linearization `L` and current instances
`cur`. -/
structure InvC (L : List (OpId (Fin n) × A.Op)) (cur : Fin n → OpId (Fin n))
    (pend : Fin n → Option A.Op) (m : Mem A n) (loc : Fin n → Loc A n) : Prop where
  h1 : linState L = (hv m).1
  proc : ∀ q, ProcOK L (cur q) (pend q) m q (loc q)

/-! ## Basic preservation lemmas -/

/-- `m'` looks the same as `m` from the point of view of process `q`: same values, same
membership of `q` in the contexts. -/
structure Sim (q : Fin n) (m m' : Mem A n) : Prop where
  hv : hv m' = hv m
  av : ∀ j, av m' j = av m j
  hc : q ∈ hc m' ↔ q ∈ hc m
  ac : ∀ j, q ∈ ac m' j ↔ q ∈ ac m j

lemma PInv.sim {L : List (OpId (Fin n) × A.Op)} {x : OpId (Fin n)} {pd : Option A.Op}
    {m m' : Mem A n} {q : Fin n} {pc : PC A n} (s : Sim q m m') (h : PInv L x pd m q pc) :
    PInv L x pd m' q pc := by
  cases pc <;> simpa [PInv, s.hv, s.av] using h

lemma ProcOK.sim {L : List (OpId (Fin n) × A.Op)} {x : OpId (Fin n)} {pd : Option A.Op}
    {m m' : Mem A n} {q : Fin n} {l : Loc A n} (h : ProcOK L x pd m q l) (s : Sim q m m') :
    ProcOK L x pd m' q l where
  pinv := h.pinv.sim s
  ch := by simpa [s.hv, s.hc] using h.ch
  ca1 := by simpa [s.av, s.ac] using h.ca1
  ca2 := by simpa [s.av, s.ac] using h.ca2
  k3 := by simpa [s.av, s.ac, s.hc] using h.k3
  k4 := by simpa [s.ac] using h.k4
  k5 := by simpa [s.ac, s.hc] using h.k5
  k6 := by simpa [s.av, s.hc] using h.k6
  loc := h.loc
  h2 := by simpa [s.hv, s.hc] using h.h2

lemma PInv.append {L M : List (OpId (Fin n) × A.Op)} {x : OpId (Fin n)} {pd : Option A.Op}
    {m : Mem A n} {q : Fin n} {pc : PC A n} (hx : x ∉ M.map Prod.fst) (h : PInv L x pd m q pc) :
    PInv (L ++ M) x pd m q pc := by
  have e : specResp (L ++ M) x = specResp L x := ObjSpec.respIn_append_of_not_mem_right hx
  cases pc <;> simpa [PInv, e] using h

lemma ProcOK.append {L M : List (OpId (Fin n) × A.Op)} {x : OpId (Fin n)} {pd : Option A.Op}
    {m : Mem A n} {q : Fin n} {l : Loc A n} (hx : x ∉ M.map Prod.fst) (h : ProcOK L x pd m q l) :
    ProcOK (L ++ M) x pd m q l :=
  have e : specResp (L ++ M) x = specResp L x := ObjSpec.respIn_append_of_not_mem_right hx
  { h with pinv := h.pinv.append hx, h2 := by simpa [e] using h.h2 }

/-! ## Helper lemmas on `PInv` and `ProcOK` -/

section Helpers

variable {L L' : List (OpId (Fin n) × A.Op)} {x : OpId (Fin n)} {pd : Option A.Op}
  {m m' : Mem A n} {q : Fin n} {l : Loc A n} {pc : PC A n}

/-- `PInv` in the main loop. -/
def LoopP (L : List (OpId (Fin n) × A.Op)) (x : OpId (Fin n)) (pd : Option A.Op) (m : Mem A n)
    (q : Fin n) : Prop :=
  ∃ o, pd = some o ∧ ¬ A.ReadOnly o ∧
    ((av m q = some (.inl o) ∧ (specResp L x ≠ none → ∃ rsp, (hv m).2 = some (rsp, q))) ∨
      ∃ r, av m q = some (.inr r) ∧ specResp L x = some r)

lemma PInv_loop (h : pc.inLoop = true) : PInv L x pd m q pc ↔ LoopP L x pd m q := by
  cases pc <;> simp_all [PInv, PC.inLoop, LoopP]

lemma PInv.inl {o : A.Op} (h : PInv L x pd m q pc) (ho : av m q = some (.inl o)) :
    pc.inLoop = true ∧ pd = some o ∧ ¬ A.ReadOnly o ∧
      (specResp L x ≠ none → ∃ rsp, (hv m).2 = some (rsp, q)) := by
  by_cases hl : pc.inLoop
  · rw [PInv_loop hl] at h
    obtain ⟨o', h1, h2, h3 | ⟨r, h3, -⟩⟩ := h
    · rw [ho] at h3; cases h3.1; exact ⟨hl, h1, h2, h3.2⟩
    · rw [ho] at h3; cases h3
  · cases pc <;> simp_all [PInv, PC.inLoop]

lemma PInv.congr (h : PInv L x pd m q pc) (ha : av m' q = av m q) (hh : hv m' = hv m) :
    PInv L x pd m' q pc := by
  cases pc <;> simpa [PInv, ha, hh] using h

lemma PInv.hv_change (h : PInv L x pd m q pc) (ha : av m' q = av m q)
    (hh : ∀ o, av m q = some (.inl o) → specResp L x ≠ none → ∃ rsp, (hv m').2 = some (rsp, q)) :
    PInv L x pd m' q pc := by
  by_cases hl : pc.inLoop
  · rw [PInv_loop hl] at h ⊢
    obtain ⟨o, h1, h2, h3⟩ := h
    refine ⟨o, h1, h2, ?_⟩
    rw [ha]
    rcases h3 with h3 | h3
    · exact Or.inl ⟨h3.1, hh o h3.1⟩
    · exact Or.inr h3
  · cases pc <;> simp_all [PInv, PC.inLoop]

lemma LocInv.k3 (h : LocInv q l) (hk : l.pc.inK3 = true) : ∃ rsp, l.hd.2 = some (rsp, l.aj) := by
  unfold LocInv at h
  split at h <;> simp_all [PC.inK3]

/-- Effect of a write `(v, ∅)` to `announce[j]` (by a process other than `q`). -/
lemma ProcOK.writeAnn (h : ProcOK L x pd m q l) (v : AnnVal A) (j : Fin n)
    (hpinv : PInv L x pd (Function.update m (.ann j) (v, ∅)) q l.pc)
    (hk3 : q ∈ hc m → l.pc.inK3 = true → l.aj = j → ∀ o, v ≠ some (.inl o))
    (hk6 : ∀ o, l.pc = .scApply j o → q ∈ hc m → v = some (.inl o)) :
    ProcOK L x pd (Function.update m (.ann j) (v, ∅)) q l where
  pinv := hpinv
  ch := by simpa using h.ch
  ca1 := by
    intro k hk hk'
    rw [ac_update_ann] at hk
    split_ifs at hk with e
    · simp at hk
    · rw [av_update_ann_ne _ e]; exact h.ca1 k hk hk'
  ca2 := by
    intro k hk
    rw [ac_update_ann] at hk
    split_ifs at hk with e
    · simp at hk
    · rw [av_update_ann_ne _ e]; exact h.ca2 k hk
  k3 := by
    intro hq hk hn o
    simp only [hc_update_ann] at hq
    by_cases e : l.aj = j
    · rw [e, av_update_ann_self]; exact hk3 hq hk e o
    · rw [av_update_ann_ne _ e]; rw [ac_update_ann_ne _ e] at hn; exact h.k3 hq hk hn o
  k4 := by
    intro h1 h2'
    by_cases e : l.aj = j
    · rw [e, ac_update_ann_self]; simp
    · rw [ac_update_ann_ne _ e]; exact h.k4 h1 h2'
  k5 := by
    intro h1 h2'
    by_cases e : l.aj = j
    · rw [e, ac_update_ann_self] at h2'; simp at h2'
    · rw [ac_update_ann_ne _ e] at h2'; simpa using h.k5 h1 h2'
  k6 := by
    intro k o h1 h2'
    simp only [hc_update_ann] at h2'
    by_cases e : k = j
    · subst e; rw [av_update_ann_self]; exact hk6 o h1 h2'
    · rw [av_update_ann_ne _ e]; exact h.k6 k o h1 h2'
  loc := h.loc
  h2 := by simpa using h.h2

/-- Effect of a write `(v, ∅)` to `head` (by a process other than `q`); the linearization may
change at the same time. -/
lemma ProcOK.writeHead (h : ProcOK L x pd m q l) (v : HeadVal A n)
    (hpinv : PInv L' x pd (Function.update m .head (v, ∅)) q l.pc)
    (hk5 : l.pc = .scAnn → q ∉ ac m l.aj)
    (hh2 : ∀ rsp, v.2 = some (rsp, q) → specResp L' x = some rsp ∧
      (l.pc.inLoop ∨ l.pc = .resp ∨ ∃ r, l.pc = .llHead2 r)) :
    ProcOK L' x pd (Function.update m .head (v, ∅)) q l where
  pinv := hpinv
  ch := by simp
  ca1 := by simpa using h.ca1
  ca2 := by simpa using h.ca2
  k3 := by simp
  k4 := by simpa using h.k4
  k5 := by intro h1 h2'; simp only [ac_update_head] at h2'; exact absurd h2' (hk5 h1)
  k6 := by simp
  loc := h.loc
  h2 := by
    intro rsp hr
    simp only [hv_update_head] at hr
    obtain ⟨a, b⟩ := hh2 rsp hr
    refine ⟨a, ?_⟩
    rcases b with b | b | b
    · exact Or.inl b
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (Or.inl b))

lemma PInv.loop_to {pc' : PC A n} (h : PInv L x pd m q pc) (h1 : pc.inLoop = true)
    (h2 : pc'.inLoop = true) : PInv L x pd m q pc' :=
  (PInv_loop h2).2 ((PInv_loop h1).1 h)

/-- A step inside the main loop that changes only the program counter. -/
lemma ProcOK.loopMove {l' : Loc A n} (h : ProcOK L x pd m q l) (h1 : l.pc.inLoop = true)
    (h1' : l'.pc.inLoop = true) (hhd : l'.hd = l.hd) (ha : l'.a = l.a) (haj : l'.aj = l.aj)
    (hvl : l.pc.inVL = false) (hk : l'.pc.inK3 = false) (h4 : l'.pc ≠ .scHead)
    (h5 : l'.pc ≠ .scAnn) (h6 : ∀ j o, l'.pc = .scApply j o → q ∈ hc m → av m j = some (.inl o))
    (hloc : LocInv q l') : ProcOK L x pd m q l' where
  pinv := h.pinv.loop_to h1 h1'
  ch := fun hh => ⟨by rw [hhd]; exact (h.ch hh).1, by simp [PC.mayHC]; split <;> simp_all⟩
  ca1 := by rw [ha, haj]; exact h.ca1
  ca2 := by
    intro j hj
    rcases h.ca2 j hj with e | e
    · simp [hvl] at e
    · exact Or.inr e
  k3 := by simp [hk]
  k4 := fun e => absurd e h4
  k5 := fun e => absurd e h5
  k6 := h6
  loc := hloc
  h2 := fun rsp hr => ⟨(h.h2 rsp hr).1, Or.inl h1'⟩

end Helpers

/-! ## Preservation by steps -/

variable [DecidablePred A.ReadOnly]

/-- The operation linearized by a step of process `p` from configuration `C` (with current
instances `cur`): a read-only operation at its `Load(head)`, and the applied operation at a
successful `SC(head, ⟨q', ⟨r, j⟩⟩)` in line 14. -/
def contribT (cur : Fin n → OpId (Fin n)) (C : Config A (B A n) (Fin n) (Loc A n)) (p : Fin n) :
    List (OpId (Fin n) × A.Op) :=
  match (C.loc p).pc with
  | .ro o => [(cur p, o)]
  | .scApply j o => if p ∈ hc C.mem then [(cur j, o)] else []
  | _ => []


/-- Preservation of the configuration invariant by a step `tau p`. -/
theorem InvC.tau {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    (hcur : ∀ q, (cur q).1 = q)
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.tau p) = some C') :
    InvC (L ++ contribT cur C p) cur C'.pend C'.mem C'.loc := by
  have cur_ne : ∀ {q r : Fin n}, q ≠ r → cur q ≠ cur r :=
    fun hq e => hq (by have := congrArg Prod.fst e; rwa [hcur, hcur] at this)
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  rw [hpend]
  have hP := hI.proc p
  cases hpc : (C.loc p).pc with
  | idle =>
    have := hP.pinv; rw [hpc] at this; exact absurd this.1 hp
  | roRet r => simp only [alg5, act, hpc] at hact; cases hact
  | retSC r => simp only [alg5, act, hpc] at hact; cases hact
  | ro o =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    simp only [PInv] at pinv
    obtain ⟨hpo, hro, hav, hsr⟩ := pinv
    have hnot : cur p ∉ L.map Prod.fst := ObjSpec.respIn_eq_none_iff.1 hsr
    simp only [contribT, hpc]
    refine ⟨by rw [linState_concat, hro, hI.h1], fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      refine ⟨?_, ?_, ca1, ?_, ?_, by simp, by simp, by simp, by simp [LocInv], ?_⟩
      · refine ⟨⟨o, hpo, hro⟩, hav, ?_⟩
        rw [specResp, ObjSpec.respIn_concat_self hnot, ← hI.h1]
        rfl
      · intro hh; simpa [PC.mayHC, PC.inLoop] using (ch hh).2
      · simpa [PC.inVL] using ca2
      · simp [PC.inK3]
      · intro rsp hr; simpa [PC.inLoop] using (h2 rsp hr).2
    · rw [Function.update_of_ne hq]
      exact (hI.proc q).append (by simpa using cur_ne hq)
  | ann o =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    simp only [PInv] at pinv
    obtain ⟨hpo, hro, hav, hsr⟩ := pinv
    have hpc_hc : p ∉ hc C.mem := fun hh => by simpa [PC.mayHC, PC.inLoop] using (ch hh).2
    have hhv : ∀ rsp, (hv C.mem).2 ≠ some (rsp, p) := fun rsp e => by
      simpa [PC.inLoop] using (h2 rsp e).2
    simp only [contribT, hpc, append_nil]
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      refine ⟨?_, ?_, ?_, ?_, ?_, by simp, by simp, by simp, by simp [LocInv], ?_⟩
      · rw [PInv_loop rfl]
        exact ⟨o, hpo, hro, Or.inl ⟨by simp, fun h => absurd hsr h⟩⟩
      · intro hh; simp at hh; exact absurd hh hpc_hc
      · intro j hj hj'
        rw [ac_update_ann] at hj
        split_ifs at hj with e
        · simp at hj
        · rw [av_update_ann_ne _ e]; exact ca1 j hj hj'
      · intro j hj
        rw [ac_update_ann] at hj
        split_ifs at hj with e
        · simp at hj
        · rw [av_update_ann_ne _ e]
          rcases ca2 j hj with h' | h'
          · simp [PC.inVL] at h'
          · exact Or.inr h'
      · intro hh; simp at hh; exact absurd hh hpc_hc
      · intro rsp hr; simp at hr; exact absurd hr (hhv rsp)
    · rw [Function.update_of_ne hq]
      have hQ := hI.proc q
      refine hQ.writeAnn _ _ (hQ.pinv.congr (by simp [av_update_ann, hq]) (by simp)) ?_ ?_
      · intro hh hk e o'
        obtain ⟨rsp, hr⟩ := hQ.loc.k3 hk
        rw [(hQ.ch hh).1, e] at hr
        exact absurd hr (hhv rsp)
      · intro o' hpc' hh
        have := hQ.k6 p o' hpc' hh
        rw [hav] at this; cases this
  | loop =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    refine ⟨hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      split
      · rename_i r hav
        replace hav := Sum.inl.inj hav
        obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
        simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
        rw [PInv_loop rfl] at pinv
        obtain ⟨o, hpo, hro, h3 | h3⟩ := pinv
        · rw [hav] at h3; cases h3.1
        refine ⟨⟨⟨o, hpo, hro⟩, h3⟩, fun hh => ⟨(ch hh).1, rfl⟩, ca1, ?_, by simp [PC.inK3],
          by simp, by simp, by simp, by simp [LocInv], fun rsp hr => ⟨(h2 rsp hr).1, by simp⟩⟩
        intro j hj; rcases ca2 j hj with e | e
        · simp [PC.inVL] at e
        · exact Or.inr e
      · exact hP.loopMove (by simp [hpc, PC.inLoop]) rfl rfl rfl rfl (by simp [hpc, PC.inVL])
          rfl (by simp) (by simp) (by simp) (by simp [LocInv])
    · rw [Function.update_of_ne hq]; exact hI.proc q
  | llHead =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc
    rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
      simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
      constructor
      · split <;> simpa [PInv] using pinv
      · intro _; split <;> simp [PC.mayHC, PC.inLoop]
      · simpa using ca1
      · intro j hj
        rcases ca2 j hj with h | h
        · simp [PC.inVL] at h
        · exact Or.inr h
      · intro _; split <;> simp [PC.inK3]
      · split <;> simp
      · split <;> simp
      · split <;> simp
      · split <;> simp_all [LocInv, Option.isSome_iff_ne_none]
      · intro rsp hr
        refine ⟨(h2 rsp hr).1, ?_⟩
        split <;> simp [PC.inLoop]
    · rw [Function.update_of_ne hq]
      exact (hI.proc q).sim ⟨by simp, by simp, by simp [hq], by simp⟩
  | help =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    refine ⟨hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      have hl : LocInv q (C.loc q) := hP.loc
      simp only [LocInv, hpc] at hl
      split
      · rename_i o hav
        replace hav := Sum.inl.inj hav
        refine hP.loopMove (by simp [hpc, PC.inLoop]) rfl rfl rfl rfl (by simp [hpc, PC.inVL]) rfl
          (by simp) (by simp) ?_ (by simp [LocInv, hl])
        intro j o' e _
        simp only [PC.scApply.injEq] at e
        obtain ⟨rfl, rfl⟩ := e; exact hav
      · exact hP.loopMove (by simp [hpc, PC.inLoop]) rfl rfl rfl rfl (by simp [hpc, PC.inVL])
          rfl (by simp) (by simp) (by simp) (by simp [LocInv, hl])
    · rw [Function.update_of_ne hq]; exact hI.proc q
  | own =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    refine ⟨hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      have hl : LocInv q (C.loc q) := hP.loc
      simp only [LocInv, hpc] at hl
      split
      · rename_i o hav
        replace hav := Sum.inl.inj hav
        refine hP.loopMove (by simp [hpc, PC.inLoop]) rfl rfl rfl rfl (by simp [hpc, PC.inVL]) rfl
          (by simp) (by simp) ?_ (by simp [LocInv, hl])
        intro j o' e _
        simp only [PC.scApply.injEq] at e
        obtain ⟨rfl, rfl⟩ := e; exact hav
      · exact hP.loopMove (by simp [hpc, PC.inLoop]) rfl rfl rfl rfl (by simp [hpc, PC.inVL])
          rfl (by simp) (by simp) (by simp) (by simp [LocInv])
    · rw [Function.update_of_ne hq]; exact hI.proc q
  | scApply j o =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl : LocInv p (C.loc p) := hP.loc
    simp only [LocInv, hpc] at hl
    by_cases hin : p ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (hP.ch hin).1
      rw [hhd] at hmem
      rw [hmem, hloc]
      simp only [contribT, hpc, hin, ↓reduceIte]
      have hav : av C.mem j = some (.inl o) := hP.k6 j o hpc hin
      have hvnone : (hv C.mem).2 = none := by rw [← hhd]; exact hl.1
      have hJ := hI.proc j
      obtain ⟨hjl, hjo, hjro, hjsr⟩ := hJ.pinv.inl hav
      have hjn : specResp L (cur j) = none := by
        by_contra hc'
        obtain ⟨rsp, e⟩ := hjsr hc'
        rw [hvnone] at e; cases e
      have hjnot : cur j ∉ L.map Prod.fst := ObjSpec.respIn_eq_none_iff.1 hjn
      have hspec : specResp (L ++ [(cur j, o)]) (cur j) = some (A.δ (hv C.mem).1 o).2 := by
        rw [specResp, ObjSpec.respIn_concat_self hjnot, ← hI.h1]; rfl
      have key : ∀ q (lq : Loc A n), ProcOK L (cur q) (C.pend q) C.mem q lq →
          (q = j → lq.pc.inLoop = true) →
          ProcOK (L ++ [(cur j, o)]) (cur q) (C.pend q) (Function.update C.mem .head
            (((A.δ (hv C.mem).1 o).1, some ((A.δ (hv C.mem).1 o).2, j)), ∅)) q lq := by
        intro q lq hQ hql
        refine hQ.writeHead _ ?_ ?_ ?_
        · by_cases hqj : q = j
          · subst hqj
            have hlq := hql rfl
            have := hQ.pinv
            rw [PInv_loop hlq] at this ⊢
            obtain ⟨o', h1, h2, h3 | ⟨r, h3, _⟩⟩ := this
            · exact ⟨o', h1, h2, Or.inl ⟨by simpa using h3.1, fun _ => ⟨(A.δ (hv C.mem).1 o).2, by simp⟩⟩⟩
            · rw [hav] at h3; cases h3
          · have hx : cur q ∉ [(cur j, o)].map Prod.fst := by simpa using cur_ne hqj
            refine (hQ.pinv.append hx).hv_change (by simp) ?_
            intro o' ho' hne
            exfalso
            rw [specResp, ObjSpec.respIn_append_of_not_mem_right hx] at hne
            obtain ⟨-, -, -, h4⟩ := hQ.pinv.inl ho'
            obtain ⟨rsp, e⟩ := h4 hne
            rw [hvnone] at e; cases e
        · intro hsc hin'
          have h5 := hQ.k5 hsc hin'
          have hlq := hQ.loc
          simp only [LocInv, hsc] at hlq
          obtain ⟨⟨rsp, e⟩, -⟩ := hlq
          rw [(hQ.ch h5).1, hvnone] at e; cases e
        · intro rsp hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨hspec, Or.inl (hql rfl)⟩
      refine ⟨by simp [linState_concat, hI.h1], fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        refine key q _ (hP.loopMove (by simp [hpc, PC.inLoop]) rfl rfl rfl rfl
          (by simp [hpc, PC.inVL]) rfl (by simp) (by simp) (by simp) (by simp [LocInv]))
          (fun _ => rfl)
      · rw [Function.update_of_ne hq]
        exact key q _ (hI.proc q) (fun e => e ▸ hjl)
    · simp [hin] at hmem hloc
      rw [hmem, hloc]
      simp only [contribT, hpc, hin, ↓reduceIte, append_nil]
      refine ⟨hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        exact hP.loopMove (by simp [hpc, PC.inLoop]) rfl rfl rfl rfl
          (by simp [hpc, PC.inVL]) rfl (by simp) (by simp) (by simp) (by simp [LocInv])
      · rw [Function.update_of_ne hq]; exact hI.proc q
  | llAnn =>
    have hl : LocInv p (C.loc p) := hP.loc
    simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, j⟩, hj⟩ := Option.isSome_iff_exists.1 hl
    simp only [alg5, act, hpc, hj] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
      simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
      refine ⟨?_, ?_, ?_, ?_, ?_, by simp, by simp, by simp, ?_, ?_⟩
      · exact (pinv.loop_to rfl rfl).congr (by simp) (by simp)
      · intro hh; simp at hh; exact ⟨(ch hh).1, rfl⟩
      · intro k hk hk'; simp only at hk'; subst hk'; simp
      · intro k hk
        by_cases e : k = j
        · subst e; exact Or.inl ⟨rfl, rfl⟩
        · rw [ac_update_ann_ne _ e] at hk; rw [av_update_ann_ne _ e]
          rcases ca2 k hk with h' | h'
          · simp [PC.inVL] at h'
          · exact Or.inr h'
      · intro _ _ hn; simp at hn
      · simp only [LocInv]; exact ⟨rsp, hj⟩
      · intro rsp' hr; exact ⟨(h2 rsp' (by simpa using hr)).1, by simp [PC.inLoop]⟩
    · rw [Function.update_of_ne hq]
      refine (hI.proc q).sim ⟨by simp, by simp, by simp, fun k => ?_⟩
      rw [ac_update_ann]; split_ifs with e <;> simp [e, hq]
  | vl =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl : LocInv p (C.loc p) := hP.loc
    simp only [LocInv, hpc] at hl
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    by_cases hin : p ∈ hc C.mem
    · simp [hin] at hmem hloc; rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      refine ⟨hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        by_cases hop : isOp (C.loc q).a = true
        · simp only [hop, ↓reduceIte]
          refine ⟨pinv.loop_to rfl rfl, fun hh => ⟨(ch hh).1, rfl⟩, ca1, ?_,
            fun hh _ => k3 hh rfl, by simp, fun _ _ => hin, by simp, ⟨hl, hop⟩,
            fun rsp hr => ⟨(h2 rsp hr).1, by simp [PC.inLoop]⟩⟩
          simpa [PC.inVL] using ca2
        · simp only [hop, Bool.false_eq_true, ↓reduceIte]
          refine ⟨pinv.loop_to rfl rfl, fun hh => ⟨(ch hh).1, rfl⟩, ca1, ?_,
            fun hh _ => k3 hh rfl, fun _ h => absurd h hop, by simp, by simp, hl,
            fun rsp hr => ⟨(h2 rsp hr).1, by simp [PC.inLoop]⟩⟩
          simpa [PC.inVL] using ca2
      · rw [Function.update_of_ne hq]; exact hI.proc q
    · simp [hin] at hmem hloc; rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      refine ⟨hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        by_cases hnone : (C.loc q).a = none
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hnone)]
          refine ⟨pinv.loop_to rfl rfl, fun hh => absurd hh hin, ca1, ?_,
            fun hh => absurd hh hin, by simp, by simp, by simp, by simp [LocInv],
            fun rsp hr => ⟨(h2 rsp hr).1, by simp [PC.inLoop]⟩⟩
          simpa [PC.inVL] using ca2
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hnone)]
          refine ⟨pinv.loop_to rfl rfl, fun hh => absurd hh hin, ca1, ?_,
            fun hh => absurd hh hin, by simp, by simp, by simp, by simp [LocInv],
            fun rsp hr => ⟨(h2 rsp hr).1, by simp [PC.inLoop]⟩⟩
          intro j hj
          rcases ca2 j hj with ⟨e, -⟩ | e
          · right; rw [ca1 j hj e]; exact hnone
          · exact Or.inr e
      · rw [Function.update_of_ne hq]; exact hI.proc q
  | scAnn =>
    have hl : LocInv p (C.loc p) := hP.loc
    simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, hrsp⟩, hop⟩ := hl
    simp only [alg5, act, hpc, hrsp] at hact; cases hact
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    generalize hjd : (C.loc p).aj = j at *
    by_cases hin : p ∈ ac C.mem j
    · simp [hin] at hmem hloc
      rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      have hphc : p ∈ hc C.mem := k5 trivial hin
      have hhd := (ch hphc).1
      have hvj : (hv C.mem).2 = some (rsp, j) := by rw [← hhd, hrsp]
      have havj : av C.mem j = (C.loc p).a := ca1 j hin rfl
      obtain ⟨oj, hoj⟩ : ∃ oj, av C.mem j = some (.inl oj) := by
        rw [havj]; revert hop
        rcases (C.loc p).a with _ | v
        · simp [isOp]
        · cases v <;> simp [isOp]
      have hJ := hI.proc j
      have hjsr := (hJ.h2 rsp hvj).1
      have newPInv : ∀ q (pcq : PC A n), PInv L (cur q) (C.pend q) C.mem q pcq →
          PInv L (cur q) (C.pend q) (Function.update C.mem (.ann j) (some (.inr rsp), ∅)) q pcq := by
        intro q pcq hq'
        by_cases hqj : q = j
        · subst hqj
          obtain ⟨hl', ho1, ho2, -⟩ := hq'.inl hoj
          rw [PInv_loop hl'] at hq' ⊢
          exact ⟨oj, ho1, ho2, Or.inr ⟨rsp, by simp, hjsr⟩⟩
        · exact hq'.congr (by simp [av_update_ann, hqj]) (by simp)
      refine ⟨by simpa using hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        refine ⟨newPInv _ _ (pinv.loop_to rfl rfl), ?_, ?_, ?_, ?_, ?_, by simp, by simp,
          ⟨rsp, hrsp⟩, ?_⟩
        · intro hh; simp at hh; exact ⟨(ch hh).1, rfl⟩
        · intro k hk hk'
          rw [ac_update_ann] at hk
          split_ifs at hk with e
          · simp at hk
          · rw [av_update_ann_ne _ e]; exact ca1 k hk hk'
        · intro k hk
          rw [ac_update_ann] at hk
          split_ifs at hk with e
          · simp at hk
          · rw [av_update_ann_ne _ e]; simpa [PC.inVL] using ca2 k hk
        · intro _ _ _ o'; simp
        · intro _ _; simp
        · intro rsp' hr; simp at hr; exact ⟨(h2 rsp' hr).1, by simp [PC.inLoop]⟩
      · rw [Function.update_of_ne hq]
        have hQ := hI.proc q
        refine hQ.writeAnn _ _ (newPInv _ _ hQ.pinv) (fun _ _ _ o' => by simp) ?_
        intro o' hpcq hh
        exfalso
        have hlq := hQ.loc; simp only [LocInv, hpcq] at hlq
        rw [(hQ.ch hh).1, hvj] at hlq; cases hlq.1
    · simp [hin] at hmem hloc; rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      refine ⟨hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        refine ⟨pinv.loop_to rfl rfl, fun hh => ⟨(ch hh).1, rfl⟩, ca1,
          by simpa [PC.inVL] using ca2, fun hh _ hn => k3 hh rfl hn, fun _ _ => hin, by simp,
          by simp, ⟨rsp, hrsp⟩, fun rsp' hr => ⟨(h2 rsp' hr).1, by simp [PC.inLoop]⟩⟩
      · rw [Function.update_of_ne hq]; exact hI.proc q
  | scHead =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl : LocInv p (C.loc p) := hP.loc
    simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    have hpl : ProcOK L (cur p) (C.pend p) C.mem p
        { C.loc p with pc := if (C.loc p).a = none then .rlAnn else .loop } := by
      refine ⟨pinv.loop_to rfl (by split <;> rfl), fun hh => ⟨(ch hh).1, by split <;> rfl⟩, ca1,
        ?_, by split <;> simp [PC.inK3], by split <;> simp, by split <;> simp,
        by split <;> simp, by split <;> simp [LocInv],
        fun rsp hr => ⟨(h2 rsp hr).1, Or.inl (by split <;> rfl)⟩⟩
      intro j hj
      by_cases hnone : (C.loc p).a = none
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hnone)]; simpa [PC.inVL] using ca2 j hj
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hnone)]
        rcases ca2 j hj with ⟨e, -⟩ | e
        · right; rw [ca1 j hj e]; exact hnone
        · exact Or.inr e
    by_cases hin : p ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (ch hin).1
      rw [hhd] at hmem
      rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      have hvj : (hv C.mem).2 = some (rsp, (C.loc p).aj) := by rw [← hhd, hrsp]
      have hnotinl : ∀ o, av C.mem (C.loc p).aj ≠ some (.inl o) := by
        by_cases hac : p ∈ ac C.mem (C.loc p).aj
        · rw [ca1 _ hac rfl]; intro o e
          exact k4 trivial (by rw [e]; rfl) hac
        · exact k3 hin rfl hac
      have key : ∀ q (lq : Loc A n), ProcOK L (cur q) (C.pend q) C.mem q lq →
          ProcOK L (cur q) (C.pend q) (Function.update C.mem .head (((hv C.mem).1, none), ∅))
            q lq := by
        intro q lq hQ
        refine hQ.writeHead _ ?_ ?_ (by simp)
        · refine hQ.pinv.hv_change (by simp) fun o ho hne => ?_
          exfalso
          obtain ⟨rsp', e⟩ := (hQ.pinv.inl ho).2.2.2 hne
          rw [hvj] at e
          simp only [Option.some.injEq, Prod.mk.injEq] at e
          rw [← e.2] at ho; exact hnotinl o ho
        · intro hsc hac
          have h5 := hQ.k5 hsc hac
          have hlq := hQ.loc; simp only [LocInv, hsc] at hlq
          obtain ⟨⟨rsp', e⟩, hop⟩ := hlq
          rw [(hQ.ch h5).1, hvj] at e
          simp only [Option.some.injEq, Prod.mk.injEq] at e
          have := hQ.ca1 _ hac rfl
          rw [← e.2] at this
          revert hop this
          rcases lq.a with _ | v
          · simp [isOp]
          · cases v with
            | inl o => intro _ e'; exact hnotinl o e'
            | inr _ => simp [isOp]
      refine ⟨by simpa using hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]; exact key q _ hpl
      · rw [Function.update_of_ne hq]; exact key q _ (hI.proc q)
    · simp [hin] at hmem hloc
      rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      refine ⟨hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]; exact hpl
      · rw [Function.update_of_ne hq]; exact hI.proc q
  | rlAnn =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      refine ⟨(pinv.loop_to rfl rfl).congr (by simp) (by simp), ?_, ?_, ?_, by simp [PC.inK3],
        by simp, by simp, by simp, by simp [LocInv],
        fun rsp hr => ⟨(h2 rsp (by simpa using hr)).1, by simp [PC.inLoop]⟩⟩
      · intro hh; simp at hh; exact ⟨(ch hh).1, rfl⟩
      · intro k hk hk'
        by_cases e : k = (C.loc q).aj
        · subst e; simp at hk
        · rw [ac_update_ann_ne _ e] at hk; simpa using ca1 k hk hk'
      · intro k hk
        by_cases e : k = (C.loc q).aj
        · subst e; simp at hk
        · rw [ac_update_ann_ne _ e] at hk
          rcases ca2 k hk with ⟨e', -⟩ | e'
          · exact absurd e'.symm e
          · right; simpa using e'
    · rw [Function.update_of_ne hq]
      refine (hI.proc q).sim ⟨by simp, by simp, by simp, fun k => ?_⟩
      rw [ac_update_ann]; split_ifs with e <;> simp [e, hq]
  | resp =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    obtain ⟨hsc, r, hav, hsr⟩ := pinv
    refine ⟨hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self, hav]
      refine ⟨⟨hsc, hav, hsr⟩, fun hh => ⟨(ch hh).1, rfl⟩, ca1, by simpa [PC.inVL] using ca2,
        by simp [PC.inK3], by simp, by simp, by simp, by simp [LocInv],
        fun rsp hr => ⟨(h2 rsp hr).1, Or.inr (Or.inr (Or.inl ⟨r, rfl⟩))⟩⟩
    · rw [Function.update_of_ne hq]; exact hI.proc q
  | llHead2 r =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      by_cases hcl : ownerIs q (hv C.mem).2 = true
      · simp only [hcl, ↓reduceIte]
        refine ⟨by simpa [PInv] using pinv, fun _ => ⟨rfl, rfl⟩, ca1,
          by simpa [PC.inVL] using ca2, by simp [PC.inK3], by simp, by simp, by simp, ?_, ?_⟩
        · simp only [LocInv]
          revert hcl
          rcases (hv C.mem).2 with _ | ⟨rsp, q'⟩
          · simp [ownerIs]
          · simp only [ownerIs, decide_eq_true_eq]; rintro rfl; exact ⟨rsp, rfl⟩
        · intro rsp hr
          exact ⟨(h2 rsp (by simpa using hr)).1, Or.inr (Or.inr (Or.inr (Or.inl ⟨r, rfl, by simp⟩)))⟩
      · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by simpa [PInv] using pinv, fun _ => ⟨rfl, rfl⟩, ca1,
          by simpa [PC.inVL] using ca2, by simp [PC.inK3], by simp, by simp, by simp,
          by simp [LocInv], ?_⟩
        intro rsp hr
        simp only [hv_update_head] at hr
        exact absurd (by rw [hr]; simp [ownerIs]) hcl
    · rw [Function.update_of_ne hq]
      exact (hI.proc q).sim ⟨by simp, by simp, by simp [hq], by simp⟩
  | clear r =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl : LocInv p (C.loc p) := hP.loc
    simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    obtain ⟨hsc, hav, hsr⟩ := pinv
    by_cases hin : p ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (ch hin).1
      rw [hhd] at hmem
      rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      have hvp : (hv C.mem).2 = some (rsp, p) := by rw [← hhd, hrsp]
      refine ⟨by simpa using hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        exact ⟨⟨hsc, by simpa using hav, hsr⟩, by simp, by simpa using ca1,
          by simpa [PC.inVL] using ca2, by simp, by simp, by simp, by simp, by simp [LocInv],
          by simp⟩
      · rw [Function.update_of_ne hq]
        have hQ := hI.proc q
        refine hQ.writeHead _ ?_ ?_ (by simp)
        · refine hQ.pinv.hv_change (by simp) fun o ho hne => ?_
          exfalso
          obtain ⟨rsp', e⟩ := (hQ.pinv.inl ho).2.2.2 hne
          rw [hvp] at e
          simp only [Option.some.injEq, Prod.mk.injEq] at e
          exact hq e.2.symm
        · intro hsc' hac
          have h5 := hQ.k5 hsc' hac
          have hlq := hQ.loc; simp only [LocInv, hsc'] at hlq
          obtain ⟨⟨rsp', e⟩, hop⟩ := hlq
          rw [(hQ.ch h5).1, hvp] at e
          simp only [Option.some.injEq, Prod.mk.injEq] at e
          have := hQ.ca1 _ hac rfl
          rw [← e.2, hav] at this
          rw [← this] at hop; simp [isOp] at hop
    · simp [hin] at hmem hloc
      rw [hmem, hloc]
      simp only [contribT, hpc, append_nil]
      refine ⟨hI.h1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        refine ⟨⟨hsc, hav, hsr⟩, fun hh => absurd hh hin, ca1, by simpa [PC.inVL] using ca2,
          by simp [PC.inK3], by simp, by simp, by simp, by simp [LocInv], ?_⟩
        intro rsp' hr
        have := (h2 rsp' hr).2
        simp [PC.inLoop, hin] at this
      · rw [Function.update_of_ne hq]; exact hI.proc q
  | rlHead r =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      refine ⟨by simpa [PInv] using pinv, by simp, ca1, by simpa [PC.inVL] using ca2,
        by simp, by simp, by simp, by simp, by simp [LocInv], ?_⟩
      intro rsp' hr
      have := (h2 rsp' (by simpa using hr)).2
      simp [PC.inLoop] at this
    · rw [Function.update_of_ne hq]
      exact (hI.proc q).sim ⟨by simp, by simp, by simp [hq], by simp⟩
  | rl18 j =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      refine ⟨by simpa [PInv] using pinv, ?_, ?_, ?_, by simp [PC.inK3], by simp, by simp,
        by simp, by simp [LocInv], ?_⟩
      · intro hh; simp at hh; exact ⟨(ch hh).1, rfl⟩
      · intro k hk hk'
        by_cases e : k = j
        · subst e; simp at hk
        · rw [ac_update_ann_ne _ e] at hk; simpa using ca1 k hk hk'
      · intro k hk
        by_cases e : k = j
        · subst e; simp at hk
        · rw [ac_update_ann_ne _ e] at hk
          rcases ca2 k hk with ⟨-, e'⟩ | e'
          · simp [PC.inVL] at e'
          · right; simpa using e'
      · intro rsp hr; exact ⟨(h2 rsp (by simpa using hr)).1, Or.inr (Or.inl rfl)⟩
    · rw [Function.update_of_ne hq]
      refine (hI.proc q).sim ⟨by simp, by simp, by simp, fun k => ?_⟩
      rw [ac_update_ann]; split_ifs with e <;> simp [e, hq]
  | storeBot r =>
    simp only [alg5, act, hpc] at hact; cases hact
    simp at hmem hloc; rw [hmem, hloc]
    simp only [contribT, hpc, append_nil]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hP
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    obtain ⟨hsc, hav, hsr⟩ := pinv
    have hpc_hc : p ∉ hc C.mem := fun hh => by simpa [PC.mayHC, PC.inLoop] using (ch hh).2
    refine ⟨by simpa using hI.h1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      refine ⟨⟨hsc, by simp, hsr⟩, ?_, ?_, ?_, ?_, by simp, by simp, by simp, by simp [LocInv], ?_⟩
      · intro hh; simp at hh; exact absurd hh hpc_hc
      · intro j hj hj'
        rw [ac_update_ann] at hj
        split_ifs at hj with e
        · simp at hj
        · rw [av_update_ann_ne _ e]; exact ca1 j hj hj'
      · intro j hj
        rw [ac_update_ann] at hj
        split_ifs at hj with e
        · simp at hj
        · rw [av_update_ann_ne _ e]
          rcases ca2 j hj with h' | h'
          · simp [PC.inVL] at h'
          · exact Or.inr h'
      · intro hh; simp at hh; exact absurd hh hpc_hc
      · intro rsp' hr
        have := (h2 rsp' (by simpa using hr)).2
        simp [PC.inLoop] at this
    · rw [Function.update_of_ne hq]
      have hQ := hI.proc q
      refine hQ.writeAnn _ _ (hQ.pinv.congr (by simp [av_update_ann, hq]) (by simp))
        (fun _ _ _ o' => by simp) ?_
      intro o' hpc' hh
      have := hQ.k6 p o' hpc' hh
      rw [hav] at this; cases this

/-- Preservation of the configuration invariant by an invocation. -/
theorem InvC.inv {L : List (OpId (Fin n) × A.Op)} {cur cur' : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {o : A.Op}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.inv p o) = some C')
    (hcur' : ∀ q, q ≠ p → cur' q = cur q) (hnew : specResp L (cur' p) = none) :
    InvC L cur' C'.pend C'.mem C'.loc := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  rw [hpend, hloc, hmem]
  refine ⟨hI.h1, fun q => ?_⟩
  by_cases hq : q = p
  · subst hq
    simp only [Function.update_self]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hI.proc q
    have hpc : (C.loc q).pc = .idle := by
      revert pinv; cases (C.loc q).pc <;> simp_all [PInv]
    simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
    have hnhc : q ∉ hc C.mem := fun hh => by simpa [PC.mayHC, PC.inLoop] using (ch hh).2
    have hca2 : ∀ j, q ∈ ac C.mem j → av C.mem j ≠ none := fun j hj => by
      simpa [PC.inVL] using ca2 j hj
    by_cases hro : A.ReadOnly o
    · simp only [alg5, hro, ↓reduceIte]
      refine ⟨⟨rfl, hro, pinv.2, hnew⟩, fun hh => absurd hh hnhc, ca1, fun j hj => Or.inr (hca2 j hj),
        fun hh => absurd hh hnhc, by simp, by simp, by simp, by simp [LocInv], ?_⟩
      intro rsp hr; have := (h2 rsp hr).2; simp [PC.inLoop] at this
    · simp only [alg5, hro, ↓reduceIte]
      refine ⟨⟨rfl, hro, pinv.2, hnew⟩, fun hh => absurd hh hnhc, ca1, fun j hj => Or.inr (hca2 j hj),
        fun hh => absurd hh hnhc, by simp, by simp, by simp, by simp [LocInv], ?_⟩
      intro rsp hr; have := (h2 rsp hr).2; simp [PC.inLoop] at this
  · simp only [Function.update_of_ne hq, hcur' q hq]
    exact hI.proc q

/-- Preservation of the configuration invariant by a response. -/
theorem InvC.ret {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {r : A.Resp}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.ret p r) = some C') :
    InvC L cur C'.pend C'.mem C'.loc ∧ specResp L (cur p) = some r := by
  obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  rw [hpend, hloc, hmem]
  obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hI.proc p
  have key : ∀ (pc : PC A n), (C.loc p).pc = pc → InvC L cur (Function.update C.pend p none) C.mem
      (Function.update C.loc p l) ∧ specResp L (cur p) = some r := by
    intro pc hpc
    cases pc with
    | roRet r' =>
      simp only [alg5, act, hpc, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      simp only [hpc, PInv] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
      refine ⟨⟨hI.h1, fun q => ?_⟩, pinv.2.2⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        refine ⟨⟨rfl, pinv.2.1⟩, fun hh => by simpa [PC.mayHC, PC.inLoop] using (ch hh).2, ca1,
          fun j hj => by simpa [PC.inVL] using ca2 j hj, by simp [PC.inK3], by simp, by simp,
          by simp, by simp [LocInv], ?_⟩
        intro rsp hr; have := (h2 rsp hr).2; simp [PC.inLoop] at this
      · simp only [Function.update_of_ne hq]; exact hI.proc q
    | retSC r' =>
      simp only [alg5, act, hpc, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      simp only [hpc, PInv] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
      refine ⟨⟨hI.h1, fun q => ?_⟩, pinv.2.2⟩
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]
        refine ⟨⟨rfl, pinv.2.1⟩, fun hh => by simpa [PC.mayHC, PC.inLoop] using (ch hh).2, ca1,
          fun j hj => by simpa [PC.inVL] using ca2 j hj, by simp [PC.inK3], by simp, by simp,
          by simp, by simp [LocInv], ?_⟩
        intro rsp hr; have := (h2 rsp hr).2; simp [PC.inLoop] at this
      · simp only [Function.update_of_ne hq]; exact hI.proc q
    | _ =>
      simp only [alg5, act, hpc] at hact
      first | cases hact | (split at hact <;> cases hact)
  exact key _ rfl

omit [DecidablePred A.ReadOnly] in
/-- What a step contributes to the linearization. -/
lemma contribT_spec {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n}
    (hI : InvC L cur C.pend C.mem C.loc) :
    contribT cur C p = [] ∨ ∃ j o, contribT cur C p = [(cur j, o)] ∧ C.pend j = some o ∧
      specResp L (cur j) = none := by
  have hP := hI.proc p
  unfold contribT
  split
  · rename_i o hpc
    have := hP.pinv; rw [hpc] at this
    exact Or.inr ⟨p, o, rfl, this.1, this.2.2.2⟩
  · rename_i j o hpc
    split_ifs with hin
    · right
      have hav := hP.k6 j o hpc hin
      obtain ⟨-, h1, -, h3⟩ := (hI.proc j).pinv.inl hav
      refine ⟨j, o, rfl, h1, ?_⟩
      by_contra hne
      obtain ⟨rsp, e⟩ := h3 hne
      have hl := hP.loc; simp only [LocInv, hpc] at hl
      rw [← (hP.ch hin).1, hl.1] at e; cases e
    · exact Or.inl rfl
  · exact Or.inl rfl

/-! ## The linearization function and the invariant of executions -/

/-- The current operation instance of process `j` after `α`. -/
def curOf (α : List (Label (Fin n) A)) (j : Fin n) : OpId (Fin n) := (j, (opsOf α j).length - 1)

/-- The contribution of the label `ℓ`, executed after `α`, to the linearization. -/
noncomputable def contrib (α : List (Label (Fin n) A)) (ℓ : Label (Fin n) A) :
    List (OpId (Fin n) × A.Op) :=
  match (alg5 A n).run α, ℓ with
  | some C, .tau p => contribT (curOf α) C p
  | _, _ => []

variable (A n) in
/-- The linearization function `h_uc` of Algorithm 5 (Section 6.2): state-changing operations are
linearized at the successful `SC(head, ⟨q', ⟨r, j⟩⟩)` of line 14 that applies them, read-only
operations at their `Load(head)`. -/
noncomputable def hlin (α : List (Label (Fin n) A)) : List (OpId (Fin n) × A.Op) :=
  linOfPts contrib α

@[simp] lemma hlin_nil : hlin A n [] = [] := rfl

lemma hlin_snoc (α : List (Label (Fin n) A)) (ℓ : Label (Fin n) A) :
    hlin A n (α ++ [ℓ]) = hlin A n α ++ contrib α ℓ :=
  linOfPts_concat _ α ℓ

/-- The invariant of an execution `α`, with linearization `L`, reaching configuration `C`. -/
structure InvL (α : List (Label (Fin n) A)) (L : List (OpId (Fin n) × A.Op))
    (C : Config A (B A n) (Fin n) (Loc A n)) : Prop where
  invC : InvC L (curOf α) C.pend C.mem C.loc
  nodup : (L.map Prod.fst).Nodup
  op_eq : ∀ y ∈ L, opOf α y.1 = some y.2
  complete : ∀ x, Completed α x → x ∈ L.map Prod.fst
  resp : ∀ x r, respOf α x = some r → specResp L x = some r

/-- The invariant of Algorithm 5 for an execution `α` reaching configuration `C`. -/
abbrev Inv (α : List (Label (Fin n) A)) (C : Config A (B A n) (Fin n) (Loc A n)) : Prop :=
  InvL α (hlin A n α) C

lemma InvL.invoked {α : List (Label (Fin n) A)} {L : List (OpId (Fin n) × A.Op)}
    {C : Config A (B A n) (Fin n) (Loc A n)}
    (hI : InvL α L C) {x : OpId (Fin n)} (hx : x ∈ L.map Prod.fst) : Invoked α x := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  have := hI.op_eq y hy
  simp only [opOf] at this
  exact (List.getElem?_eq_some_iff.1 this).1

lemma Inv.invoked {α : List (Label (Fin n) A)} {C : Config A (B A n) (Fin n) (Loc A n)}
    (hI : Inv α C) {x : OpId (Fin n)} (hx : x ∈ (hlin A n α).map Prod.fst) : Invoked α x :=
  InvL.invoked hI hx

lemma opOf_curOf {α : List (Label (Fin n) A)} {C : Config A (B A n) (Fin n) (Loc A n)}
    (h : (alg5 A n).run α = some C) {j : Fin n} {o : A.Op} (hj : C.pend j = some o) :
    opOf α (curOf α j) = some o := by
  have := (alg5 A n).run_pend h hj
  simp only [opOf, curOf]
  rw [List.getLast?_eq_getElem?] at this
  exact this

theorem inv_init : Inv ([] : List (Label (Fin n) A)) (alg5 A n).initCfg where
  invC := by
    refine ⟨rfl, fun q => ?_⟩
    refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩ <;>
      simp [Impl.initCfg, alg5, hc, ac, hv, PC.inK3]
  nodup := by simp
  op_eq := by simp
  complete := fun x hx => by simp [Completed] at hx
  resp := fun x r hx => by simp [respOf] at hx

/-- Preservation of `InvL` by a step `tau p` of Algorithm 5 (from any configuration satisfying
the invariant; `hpo` relates pending operations to the history). -/
theorem InvL.tauStep {α : List (Label (Fin n) A)} {L : List (OpId (Fin n) × A.Op)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} (hI : InvL α L C)
    (hpo : ∀ j o, C.pend j = some o → opOf α (curOf α j) = some o)
    (h : (alg5 A n).step C (.tau p) = some C') :
    InvL (α ++ [.tau p]) (L ++ contribT (curOf α) C p) C' := by
  have hcur : ∀ q, (curOf α q).1 = q := fun q => rfl
  have hops : ∀ q, opsOf (α ++ [.tau p]) q = opsOf α q :=
    fun _ => opsOf_concat_of_ne (by simp)
  have hresps : ∀ q, respsOf (α ++ [.tau p]) q = respsOf α q :=
    fun _ => respsOf_concat_of_ne (by simp)
  have hcurE : curOf (α ++ [.tau p]) = curOf α := by funext q; simp [curOf, hops]
  have hC := hI.invC.tau hcur h
  rcases contribT_spec (p := p) hI.invC with he | ⟨j, o, he, hpj, hsj⟩
  · rw [he] at hC ⊢
    simp only [append_nil] at hC ⊢
    refine ⟨by rw [hcurE]; exact hC, hI.nodup, fun y hy => ?_, fun x hx => ?_, fun x r hx => ?_⟩
    · rw [opOf_append_of_invoked (hI.invoked (List.mem_map_of_mem hy))]; exact hI.op_eq y hy
    · exact hI.complete x (by simpa [Completed, hresps] using hx)
    · exact hI.resp x r (by simpa [respOf, hresps] using hx)
  · rw [he] at hC ⊢
    have hjn : curOf α j ∉ L.map Prod.fst := ObjSpec.respIn_eq_none_iff.1 hsj
    refine ⟨by rw [hcurE]; exact hC, ?_, fun y hy => ?_, fun x hx => ?_, fun x r hx => ?_⟩
    · simp only [map_append, map_cons, map_nil]
      refine List.nodup_append.2 ⟨hI.nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb; subst hb
      rintro rfl; exact hjn ha
    · rcases List.mem_append.1 hy with hy | hy
      · rw [opOf_append_of_invoked (hI.invoked (List.mem_map_of_mem hy))]; exact hI.op_eq y hy
      · simp only [List.mem_singleton] at hy; subst hy
        have := hpo j o hpj
        rw [opOf_append_of_invoked (by simp only [Invoked]; simp [opOf] at this; exact
          (List.getElem?_eq_some_iff.1 this).1)]
        exact this
    · have := hI.complete x (by simpa [Completed, hresps] using hx)
      simp only [map_append, mem_append]; exact Or.inl this
    · have hx' : respOf α x = some r := by simpa [respOf, hresps] using hx
      have hmem := hI.complete x (by
        simp only [Completed]; simp only [respOf] at hx'
        exact (List.getElem?_eq_some_iff.1 hx').1)
      rw [specResp, ObjSpec.respIn_append_of_mem hmem]; exact hI.resp x r hx'

/-- Preservation of `InvL` by an invocation. -/
theorem InvL.invStep {α : List (Label (Fin n) A)} {L : List (OpId (Fin n) × A.Op)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {o : A.Op} (hI : InvL α L C)
    (h : (alg5 A n).step C (.inv p o) = some C') : InvL (α ++ [.inv p o]) L C' := by
  have hresps : ∀ q, respsOf (α ++ [.inv p o]) q = respsOf α q :=
    fun _ => respsOf_concat_of_ne (by simp)
  have hops : ∀ q, opsOf (α ++ [.inv p o]) q = opsOf α q ++ (if p = q then [o] else []) := by
    intro q; by_cases hq : p = q <;> simp [opsOf_append, opsOf_cons, hq]
  have hpn : C.pend p = none := (Impl.step_inv h).1
  refine ⟨hI.invC.inv h (fun q hq => ?_) ?_, hI.nodup, fun y hy => ?_, fun x hx => ?_,
    fun x r hx => ?_⟩
  · simp [curOf, hops, Ne.symm hq]
  · rw [specResp, ObjSpec.respIn_eq_none_iff]
    intro hm
    have := hI.invoked hm
    simp [Invoked, curOf, hops] at this
  · rw [opOf_append_of_invoked (hI.invoked (List.mem_map_of_mem hy))]; exact hI.op_eq y hy
  · exact hI.complete x (by simpa [Completed, hresps] using hx)
  · exact hI.resp x r (by simpa [respOf, hresps] using hx)

/-- Preservation of `InvL` by a response. -/
theorem InvL.retStep {α : List (Label (Fin n) A)} {L : List (OpId (Fin n) × A.Op)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {r : A.Resp} (hI : InvL α L C)
    (hcnt : C.pend p ≠ none → (opsOf α p).length = (respsOf α p).length + 1)
    (h : (alg5 A n).step C (.ret p r) = some C') : InvL (α ++ [.ret p r]) L C' := by
  have hops : ∀ q, opsOf (α ++ [.ret p r]) q = opsOf α q :=
    fun _ => opsOf_concat_of_ne (by simp)
  have hcurE : curOf (α ++ [.ret p r]) = curOf α := by funext q; simp [curOf, hops]
  have hresps : ∀ q, respsOf (α ++ [.ret p r]) q =
      respsOf α q ++ (if p = q then [r] else []) := by
    intro q; by_cases hq : p = q <;> simp [respsOf_append, respsOf_cons, hq]
  obtain ⟨hC, hsr⟩ := hI.invC.ret h
  have hpend : C.pend p ≠ none := (Impl.step_ret h).1
  have hcnt : (opsOf α p).length = (respsOf α p).length + 1 := by
    exact hcnt hpend
  have hcurp : curOf α p = (p, (respsOf α p).length) := by simp [curOf, hcnt]
  refine ⟨by rw [hcurE]; exact hC, hI.nodup, fun y hy => ?_, fun x hx => ?_, fun x r' hx => ?_⟩
  · rw [opOf_append_of_invoked (hI.invoked (List.mem_map_of_mem hy))]; exact hI.op_eq y hy
  · obtain ⟨q, i⟩ := x
    simp only [Completed, hresps] at hx
    by_cases hq : p = q
    · subst hq
      simp only [↓reduceIte, length_append, length_singleton] at hx
      rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
      · exact hI.complete _ hx
      · subst hx; rw [← hcurp]
        by_contra hn
        have := (ObjSpec.respIn_eq_none_iff (q := A.init)).2 hn
        simp only [specResp] at hsr
        rw [this] at hsr; cases hsr
    · simp only [hq, ↓reduceIte, append_nil] at hx; exact hI.complete _ hx
  · obtain ⟨q, i⟩ := x
    simp only [respOf, hresps] at hx
    by_cases hq : p = q
    · subst hq
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at hx
      rcases lt_or_ge i (respsOf α p).length with hi | hi
      · rw [List.getElem?_append_left hi] at hx; exact hI.resp _ _ hx
      · rw [List.getElem?_append_right hi] at hx
        have : i - (respsOf α p).length = 0 := by
          by_contra hne
          rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx
        have hi' : i = (respsOf α p).length := by omega
        simp [this] at hx; subst hx; subst hi'
        rw [← hcurp]; exact hsr
    · simp only [hq, ↓reduceIte, append_nil] at hx; exact hI.resp _ _ hx


theorem inv_step {α : List (Label (Fin n) A)} {C C' : Config A (B A n) (Fin n) (Loc A n)}
    {ℓ : Label (Fin n) A} (hrun : (alg5 A n).run α = some C) (hI : Inv α C)
    (h : (alg5 A n).step C ℓ = some C') : Inv (α ++ [ℓ]) C' := by
  show InvL _ _ _
  rw [hlin_snoc]
  cases ℓ with
  | tau p =>
    have hcon : contrib α (.tau p) = contribT (curOf α) C p := by simp [contrib, hrun]
    rw [hcon]
    exact hI.tauStep (fun j o hj => opOf_curOf hrun hj) h
  | inv p o =>
    have hcon : contrib α (.inv p o) = [] := by simp [contrib]
    rw [hcon, append_nil]
    exact hI.invStep h
  | ret p r =>
    have hcon : contrib α (.ret p r) = [] := by simp [contrib]
    rw [hcon, append_nil]
    exact hI.retStep (Impl.run_pend_counts hrun) h

/-- **The invariant** holds in every reachable configuration. -/
theorem inv_run {α : List (Label (Fin n) A)} {C : Config A (B A n) (Fin n) (Loc A n)}
    (h : (alg5 A n).run α = some C) : Inv α C :=
  Impl.run_induction inv_init (fun _ _ _ _ hα hI hs => inv_step hα hI hs) h
