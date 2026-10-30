import Papers.PODC2025.AuditingWithoutLeaks.LinAux
import Papers.PODC2025.AuditingWithoutLeaks.WaitFree
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.StrongLin

/-!
# Linearizability of Algorithm 1 (Theorem 8, first part)

We linearize by a forward simulation (hence Algorithm 1 is even *strongly* linearizable):

* a silent read is linearized at its read of `SN` (line 2), where it reads `x = prev_sn = SN`
  and returns `prev_val`, the value of sequence number `SN`;
* the abstract value of the register is the value of sequence number `SN` (not `R.seq`):
  all writes with sequence number `x + 1` (the silent ones first, the visible one, whose input
  is `R.val`, last) are linearized at the step `σ_{x+1}` that moves `SN` from `x` to `x + 1`;
* a direct read (fetch&xor) or an audit (read of `R`) is linearized at its access to `R` if it
  happens in an `E` phase (`R.seq = SN`); in a `D` phase (`R.seq = SN + 1`) it is linearized at
  `σ_{x+1}`, right after the writes, in the order of the accesses to `R` (ghost list `Dl`).

This differs from the paper's linearization `L(α)` (rules R1–R3), which linearizes the visible
write at `ρ_{x+1}` and pushes silent operations back before it; both orders coincide up to the
placement of `D`-phase operations relative to the visible write.
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

section Defs

variable (rnd) in
/-- The pairs `(i, value of t)` of the fetches at sequence numbers `t ≤ n`. -/
def Pairs (C : Cfg m W Au V v₀) (n : ℕ) : Set (Fin m × V) :=
  {x | ∃ t ≤ n, Fetched rnd C x.1 t ∧ x.2 = hv v₀ C t}

variable (v₀) in
/-- Response assigned by a sequential history. -/
abbrev respL (L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)) (x : OpId (Proc m W Au)) :
    Option (auditReg m V v₀).Resp :=
  (auditReg m V v₀).respIn (auditReg m V v₀).init L x

/-- Status of a reader w.r.t. the linearization `L` and the ghost list `Dl`. -/
def RSt (α : List (Label (Proc m W Au) (auditReg m V v₀))) (C : Cfg m W Au V v₀)
    (L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)) (Dl : List (Proc m W Au)) (j : Fin m) :
    Prop :=
  match C.loc (.rd j) with
  | .rSN _ | .rFX _ _ => curOp α (.rd j) ∉ L.map Prod.fst
  | .rCAS _ sn val => (respL v₀ L (curOp α (.rd j)) = some (.val val) ∧ sn ≤ snOf C) ∨
      (curOp α (.rd j) ∉ L.map Prod.fst ∧ Proc.rd j ∈ Dl ∧ sn = (rOf C).seq ∧
        (rOf C).seq = snOf C + 1)
  | .rRet _ val => respL v₀ L (curOp α (.rd j)) = some (.val val)
  | _ => True

/-- The sequence number held by a writer (if any). -/
def wsn : Loc m V → Option ℕ
  | .wR _ sn | .wV _ sn _ | .wB _ sn _ _ | .wCAS _ sn _ | .wHelp sn => some sn
  | _ => none

/-- Status of a writer. -/
def WSt (α : List (Label (Proc m W Au) (auditReg m V v₀))) (C : Cfg m W Au V v₀)
    (L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)) (w : W) : Prop :=
  match C.loc (.wr w) with
  | .wSN _ => curOp α (.wr w) ∉ L.map Prod.fst
  | .wRet => curOp α (.wr w) ∈ L.map Prod.fst
  | l => ∀ sn, wsn l = some sn → (curOp α (.wr w) ∈ L.map Prod.fst ↔ sn ≤ snOf C)

/-- The triple read by an auditor (if any). -/
def ar : Loc m V → Option (RVal m V)
  | .aV _ r _ | .aB _ r _ _ _ | .aCAS _ r => some r
  | _ => none

/-- Status of an auditor. -/
def ASt (α : List (Label (Proc m W Au) (auditReg m V v₀))) (C : Cfg m W Au V v₀)
    (L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)) (Dl : List (Proc m W Au)) (a : Au) :
    Prop :=
  match C.loc (.au a) with
  | .aR _ _ => curOp α (.au a) ∉ L.map Prod.fst
  | .aRet A _ => respL v₀ L (curOp α (.au a)) = some (.set A)
  | l => ∀ r, ar l = some r →
      (respL v₀ L (curOp α (.au a)) = some (.set (Target rnd C r)) ∧ r.seq ≤ snOf C) ∨
      (curOp α (.au a) ∉ L.map Prod.fst ∧ Proc.au a ∈ Dl ∧ r.seq = (rOf C).seq ∧
        (rOf C).seq = snOf C + 1)

variable (rnd) in
/-- The simulation relation. -/
structure LInv (α : List (Label (Proc m W Au) (auditReg m V v₀))) (C : Cfg m W Au V v₀)
    (L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)) (Dl : List (Proc m W Au)) : Prop where
  inv : Inv rnd C
  dinv : DInv2 C
  binv : BInv rnd C
  lin : IsLinearization α L
  abs : linState L = (hv v₀ C (snOf C), Pairs rnd C (snOf C))
  rd : ∀ j, RSt α C L Dl j
  wr : ∀ w, WSt α C L w
  au : ∀ a, ASt (rnd := rnd) α C L Dl a
  dl_nodup : Dl.Nodup
  dl_E : (rOf C).seq = snOf C → Dl = []
  dl_rd : ∀ j, Proc.rd j ∈ Dl → ∃ prev sn val, C.loc (.rd j) = .rCAS prev sn val
  dl_au : ∀ a, Proc.au a ∈ Dl → ∃ r, ar (C.loc (.au a)) = some r ∧ r.seq = (rOf C).seq
  dl_wr : ∀ w, Proc.wr w ∉ Dl
  dl_readers : ∀ i, Proc.rd i ∈ Dl ↔
    ((rOf C).seq = snOf C + 1 ∧ (rOf C).bits i ≠ rnd (rOf C).seq i)
  dl_order : ∀ a r, ar (C.loc (.au a)) = some r → Proc.au a ∈ Dl →
    ∀ i, (readersOf rnd r i ↔ [Proc.rd i, Proc.au a].Sublist Dl)

end Defs

section Basic

variable {α α' : List (Label (Proc m W Au) (auditReg m V v₀))} {C C' : Cfg m W Au V v₀}
  {L M : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)} {Dl Dl' : List (Proc m W Au)}

lemma respL_append_of_eq {x : OpId (Proc m W Au)} {r : (auditReg m V v₀).Resp}
    (h : respL v₀ L x = some r) : respL v₀ (L ++ M) x = some r :=
  ObjSpec.respIn_append_of_eq_some h _

lemma mem_of_respL {x : OpId (Proc m W Au)} {r : (auditReg m V v₀).Resp}
    (h : respL v₀ L x = some r) : x ∈ L.map Prod.fst :=
  ObjSpec.mem_of_respIn_eq_some h

lemma not_mem_append {x : OpId (Proc m W Au)} (h1 : x ∉ L.map Prod.fst)
    (h2 : x ∉ M.map Prod.fst) : x ∉ (L ++ M).map Prod.fst := by
  simp only [List.map_append, List.mem_append, not_or]; exact ⟨h1, h2⟩

/-- Responses of writes are acknowledgements. -/
lemma respL_of_write {x : OpId (Proc m W Au)} (hx : x ∈ L.map Prod.fst)
    (hw : ∀ y ∈ L, y.1 = x → ∃ v, y.2 = AOp.write v) : respL v₀ L x = some .ack := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
    ((ObjSpec.respIn_isSome_iff (A := auditReg m V v₀) (q := (auditReg m V v₀).init)).2 hx)
  obtain ⟨L₁, L₂, o, hs, hr'⟩ := ObjSpec.exists_split_of_respIn_eq_some hr
  obtain ⟨v, hv⟩ := hw (x, o) (by rw [hs]; simp) rfl
  simp only at hv; subst hv
  show (auditReg m V v₀).respIn _ L x = _
  rw [hr, ← hr']

lemma ar_aok {a : Au} (hI : Inv rnd C) {r : RVal m V} (h : ar (C.loc (.au a)) = some r) :
    AOK rnd C r := by
  have hA := hI.au a
  unfold AInv at hA
  revert hA h
  cases C.loc (.au a) <;> simp only [ar, reduceCtorEq, IsEmpty.forall_iff, Option.some.injEq]
  all_goals rintro rfl; intro hA; exact hA.2.1

lemma RSt.transfer {j : Fin m} (h : RSt α C L Dl j) (hloc : C'.loc (.rd j) = C.loc (.rd j))
    (hcur : curOp α' (.rd j) = curOp α (.rd j)) (hM : curOp α (.rd j) ∉ M.map Prod.fst)
    (hDl : Proc.rd j ∈ Dl → Proc.rd j ∈ Dl') (hsn : snOf C ≤ snOf C')
    (hD : Proc.rd j ∈ Dl → (rOf C').seq = (rOf C).seq ∧ snOf C' = snOf C) :
    RSt α' C' (L ++ M) Dl' j := by
  unfold RSt at h ⊢
  rw [hloc, hcur]
  split at h
  · exact not_mem_append h hM
  · exact not_mem_append h hM
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨respL_append_of_eq h1, h2.trans hsn⟩
    · obtain ⟨e1, e2⟩ := hD h2
      exact Or.inr ⟨not_mem_append h1 hM, hDl h2, by rw [e1]; exact h3, by rw [e1, e2]; exact h4⟩
  · exact respL_append_of_eq h
  · trivial

lemma WSt.transfer {w : W} (h : WSt α C L w) (hloc : C'.loc (.wr w) = C.loc (.wr w))
    (hcur : curOp α' (.wr w) = curOp α (.wr w)) (hM : curOp α (.wr w) ∉ M.map Prod.fst)
    (hsn : snOf C' = snOf C) : WSt α' C' (L ++ M) w := by
  unfold WSt at h ⊢
  rw [hloc, hcur, hsn]
  have hiff : curOp α (.wr w) ∈ (L ++ M).map Prod.fst ↔ curOp α (.wr w) ∈ L.map Prod.fst := by
    simp only [List.map_append, List.mem_append]; tauto
  split at h
  · exact not_mem_append h hM
  · rw [hiff]; exact h
  · intro sn hsn'; rw [hiff]; exact h sn hsn'

lemma ASt.transfer {a : Au} (hI : Inv rnd C) (E : Evo rnd C C') (h : ASt (rnd := rnd) α C L Dl a)
    (hloc : C'.loc (.au a) = C.loc (.au a))
    (hcur : curOp α' (.au a) = curOp α (.au a)) (hM : curOp α (.au a) ∉ M.map Prod.fst)
    (hDl : Proc.au a ∈ Dl → Proc.au a ∈ Dl')
    (hD : Proc.au a ∈ Dl → (rOf C').seq = (rOf C).seq ∧ snOf C' = snOf C) :
    ASt (rnd := rnd) α' C' (L ++ M) Dl' a := by
  unfold ASt at h ⊢
  rw [hloc, hcur]
  have hcases : ∀ r, ar (C.loc (.au a)) = some r →
      (respL v₀ L (curOp α (.au a)) = some (.set (Target rnd C r)) ∧ r.seq ≤ snOf C) ∨
      (curOp α (.au a) ∉ L.map Prod.fst ∧ Proc.au a ∈ Dl ∧ r.seq = (rOf C).seq ∧
        (rOf C).seq = snOf C + 1) →
      (respL v₀ (L ++ M) (curOp α (.au a)) = some (.set (Target rnd C' r)) ∧ r.seq ≤ snOf C') ∨
      (curOp α (.au a) ∉ (L ++ M).map Prod.fst ∧ Proc.au a ∈ Dl' ∧ r.seq = (rOf C').seq ∧
        (rOf C').seq = snOf C' + 1) := by
    intro r hr hh
    have hok := (ar_aok hI hr).1
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨by rw [E.target hok]; exact respL_append_of_eq h1, h2.trans E.sn⟩
    · obtain ⟨e1, e2⟩ := hD h2
      exact Or.inr ⟨not_mem_append h1 hM, hDl h2, by rw [e1]; exact h3, by rw [e1, e2]; exact h4⟩
  cases hl : C.loc (.au a) <;> simp only [hl] at h ⊢
  all_goals first
    | exact not_mem_append h hM
    | exact respL_append_of_eq h
    | (intro r hr; exact hcases r (by rw [hl]; exact hr) (h r hr))

end Basic

section Quiet

variable {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C C' : Cfg m W Au V v₀}
  {L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)} {Dl : List (Proc m W Au)}

variable (rnd) in
/-- Status of a process. -/
def PSt (α : List (Label (Proc m W Au) (auditReg m V v₀))) (C : Cfg m W Au V v₀)
    (L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)) (Dl : List (Proc m W Au)) :
    Proc m W Au → Prop
  | .rd j => RSt α C L Dl j
  | .wr w => WSt α C L w
  | .au a => ASt (rnd := rnd) α C L Dl a

lemma pairs_eq (E : Evo rnd C C') (hseq : (rOf C').seq = (rOf C).seq)
    (hbits : (rOf C').bits = (rOf C).bits) {n : ℕ} (hn : n ≤ (rOf C).seq) :
    Pairs rnd C' n = Pairs rnd C n := by
  ext ⟨i, v⟩
  simp only [Pairs, Set.mem_ofPred_eq]
  have hf : ∀ t ≤ n, (Fetched rnd C' i t ↔ Fetched rnd C i t) := by
    intro t ht
    rcases Nat.lt_or_eq_of_le (ht.trans hn) with h | h
    · exact E.fet_iff _ _ h
    · subst h; simp only [Fetched, hseq, hbits, lt_irrefl, false_and, false_or]
  constructor
  · rintro ⟨t, ht, h1, h2⟩; exact ⟨t, ht, (hf t ht).1 h1, by rw [h2, E.hv _ (ht.trans hn)]⟩
  · rintro ⟨t, ht, h1, h2⟩; exact ⟨t, ht, (hf t ht).2 h1, by rw [h2, E.hv _ (ht.trans hn)]⟩

/-- A step that appends `M` (operations of the stepping process only) to `L`, does not change
`Dl` and the sequence numbers, and changes the tracking bits only in an `E` phase. -/
lemma LInv.quiet (hL : LInv rnd α C L Dl) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some C') {M : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)}
    (hseq : (rOf C').seq = (rOf C).seq) (hsn : snOf C' = snOf C)
    (hbits : (rOf C).seq = snOf C + 1 → (rOf C').bits = (rOf C).bits)
    (hlin : IsLinearization (α ++ [ℓ]) (L ++ M))
    (habs : linState (L ++ M) = (hv v₀ C' (snOf C'), Pairs rnd C' (snOf C')))
    (hcur : ∀ q, q ≠ ℓ.proc → curOp (α ++ [ℓ]) q = curOp α q)
    (hM : ∀ q, q ≠ ℓ.proc → curOp α q ∉ M.map Prod.fst)
    (hloc : ∀ q, q ≠ ℓ.proc → C'.loc q = C.loc q)
    (hown : PSt rnd (α ++ [ℓ]) C' (L ++ M) Dl ℓ.proc)
    (hrdDl : ∀ j, Proc.rd j = ℓ.proc → Proc.rd j ∈ Dl →
      ∃ prev sn val, C'.loc (.rd j) = .rCAS prev sn val)
    (hauDl : ∀ a, Proc.au a = ℓ.proc → Proc.au a ∈ Dl →
      ar (C'.loc (.au a)) = ar (C.loc (.au a))) :
    LInv rnd (α ++ [ℓ]) C' (L ++ M) Dl := by
  obtain ⟨hI', E⟩ := Inv.step hL.inv hs
  refine ⟨hI', DInv2.step hL.inv hL.dinv hs, BInv.step hL.inv hL.binv hs, hlin, habs, fun j => ?_,
    fun w => ?_, fun a => ?_, hL.dl_nodup, fun h => hL.dl_E (by rw [← hseq, h, hsn]),
    fun j hj => ?_, fun a ha => ?_, hL.dl_wr, fun i => ?_, fun a r hr ha i => ?_⟩
  · by_cases h : Proc.rd j = ℓ.proc
    · have := hown; rw [← h] at this; exact this
    · exact RSt.transfer (hL.rd j) (hloc _ h) (hcur _ h) (hM _ h) id (by omega)
        (fun _ => ⟨hseq, hsn⟩)
  · by_cases h : Proc.wr w = ℓ.proc
    · have := hown; rw [← h] at this; exact this
    · exact WSt.transfer (hL.wr w) (hloc _ h) (hcur _ h) (hM _ h) hsn
  · by_cases h : Proc.au a = ℓ.proc
    · have := hown; rw [← h] at this; exact this
    · exact ASt.transfer hL.inv E (hL.au a) (hloc _ h) (hcur _ h) (hM _ h) id
        (fun _ => ⟨hseq, hsn⟩)
  · by_cases h : Proc.rd j = ℓ.proc
    · exact hrdDl j h hj
    · rw [hloc _ h]; exact hL.dl_rd j hj
  · by_cases h : Proc.au a = ℓ.proc
    · rw [hauDl a h ha, hseq]; exact hL.dl_au a ha
    · rw [hloc _ h, hseq]; exact hL.dl_au a ha
  · rw [hL.dl_readers i, hseq, hsn]
    by_cases hD : (rOf C).seq = snOf C + 1
    · rw [hbits hD]
    · simp [hD]
  · have hr' : ar (C.loc (.au a)) = some r := by
      by_cases h : Proc.au a = ℓ.proc
      · rw [← hauDl a h ha]; exact hr
      · rw [← hloc _ h]; exact hr
    exact hL.dl_order a r hr' ha i

end Quiet

section Batch

/-- The operation of a reader or auditor in the `D` list. -/
def opOfP : Proc m W Au → AOp m V
  | .rd i => .read i
  | _ => .audit

lemma runOps_dl (D : List (Proc m W Au)) (hD : ∀ q ∈ D, ∀ w, q ≠ Proc.wr w) (v : V)
    (S : Set (Fin m × V)) :
    (auditReg m V v₀).runOps (v, S) (D.map opOfP) = (v, S ∪ {x | ∃ i, Proc.rd i ∈ D ∧ x = (i, v)}) := by
  induction D generalizing S with
  | nil =>
    rw [List.map_nil, ObjSpec.runOps_nil]
    exact Prod.ext rfl (by ext x; simp)
  | cons q D ih =>
    rw [List.map_cons, ObjSpec.runOps_cons]
    have ih' := ih (fun q hq => hD q (by simp [hq]))
    cases q with
    | rd i =>
      have h1 : ((auditReg m V v₀).δ (v, S) (opOfP (Proc.rd i : Proc m W Au))).1 =
          (v, insert (i, v) S) := rfl
      rw [h1, ih']
      refine Prod.ext rfl ?_
      ext ⟨i', v'⟩
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, List.mem_cons, Prod.mk.injEq,
        Proc.rd.injEq]
      aesop
    | wr w => exact absurd rfl (hD _ (by simp) w)
    | au a =>
      have h1 : ((auditReg m V v₀).δ (v, S) (opOfP (Proc.au a : Proc m W Au))).1 = (v, S) := rfl
      rw [h1, ih']
      first | rfl | (refine Prod.ext rfl ?_; ext x; simp)

lemma runOps_writes (l : List (AOp m V)) (hl : ∀ o ∈ l, ∃ v, o = AOp.write v)
    (q : (auditReg m V v₀).State) : ((auditReg m V v₀).runOps q l).2 = q.2 := by
  induction l generalizing q with
  | nil => rfl
  | cons o l ih =>
    obtain ⟨v, rfl⟩ := hl o (by simp)
    rw [ObjSpec.runOps_cons, ih (fun o ho => hl o (by simp [ho]))]

/-- Writers occurring in an execution. -/
def writersIn (α : List (Label (Proc m W Au) (auditReg m V v₀))) : List W :=
  (α.filterMap fun ℓ => match ℓ with
    | .inv (.wr w) _ => some w
    | _ => none).dedup

lemma mem_writersIn {α : List (Label (Proc m W Au) (auditReg m V v₀))} {w : W}
    (h : Invoked α (curOp α (.wr w))) : w ∈ writersIn α := by
  unfold writersIn
  rw [List.mem_dedup, List.mem_filterMap]
  have : opsOf α (.wr w) ≠ [] := by
    intro h'; simp [Invoked, h', curOp] at h
  obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ this
  simp only [opsOf, List.mem_filterMap] at ho
  obtain ⟨ℓ, hℓ, h2⟩ := ho
  refine ⟨ℓ, hℓ, ?_⟩
  cases ℓ with
  | inv q o' =>
    simp only [Label.invOf] at h2
    split_ifs at h2 with hq
    subst hq; rfl
  | ret q r => simp at h2
  | tau q => simp at h2

end Batch

section SigmaFacts

variable {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
  {L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)} {Dl : List (Proc m W Au)}

lemma LInv.dl_rd_info (hL : LInv rnd α C L Dl) {j : Fin m} (hj : Proc.rd j ∈ Dl) :
    ∃ prev, C.loc (.rd j) = .rCAS prev (rOf C).seq (rOf C).val ∧
      curOp α (.rd j) ∉ L.map Prod.fst ∧ C.pend (.rd j) = some (.read j) := by
  obtain ⟨prev, sn, val, hl⟩ := hL.dl_rd j hj
  obtain ⟨hD, hb⟩ := (hL.dl_readers j).1 hj
  obtain ⟨hb1, hr⟩ := hL.inv.rd j
  rw [hl] at hb1 hr
  have hsn : sn = (rOf C).seq := by
    have := hb1.1 hb; simpa [lastFx] using this
  subst hsn
  obtain ⟨hp1, -, -, -, -, hv, -⟩ := hr
  have hst := hL.rd j
  unfold RSt at hst; rw [hl] at hst
  refine ⟨prev, by rw [hl, hv]; simp [AuditingWithoutLeaks.hv], ?_, hp1⟩
  rcases hst with ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · exact h

lemma LInv.dl_au_info (hL : LInv rnd α C L Dl) {a : Au} (ha : Proc.au a ∈ Dl) :
    ∃ r, ar (C.loc (.au a)) = some r ∧ r.seq = (rOf C).seq ∧
      curOp α (.au a) ∉ L.map Prod.fst ∧ C.pend (.au a) = some .audit := by
  obtain ⟨r, hr, hrs⟩ := hL.dl_au a ha
  have hD : (rOf C).seq = snOf C + 1 := by
    by_contra hc
    have : (rOf C).seq = snOf C := by have := hL.inv.sn_le; have := hL.inv.seq_le; omega
    rw [hL.dl_E this] at ha; cases ha
  have hst := hL.au a
  have hA := hL.inv.au a
  unfold ASt at hst; unfold AInv at hA
  refine ⟨r, hr, hrs, ?_, ?_⟩
  · revert hst hr; cases C.loc (.au a) <;> simp only [ar, reduceCtorEq, IsEmpty.forall_iff,
      Option.some.injEq] <;> rintro rfl h <;> rcases h _ rfl with ⟨-, h⟩ | ⟨h, -⟩ <;>
      first | omega | exact h
  · revert hA hr; cases C.loc (.au a) <;> simp only [ar, reduceCtorEq, IsEmpty.forall_iff,
      Option.some.injEq] <;> rintro rfl h <;> exact h.1

lemma LInv.wr_info (hL : LInv rnd α C L Dl) {w : W} (hw : wsn (C.loc (.wr w)) = some (snOf C + 1)) :
    curOp α (.wr w) ∉ L.map Prod.fst ∧ ∃ u, C.pend (.wr w) = some (.write u) := by
  have hst := hL.wr w
  have hW := hL.inv.wr w
  unfold WSt at hst; unfold WInv at hW
  revert hst hW hw
  cases C.loc (.wr w) <;> simp only [wsn, reduceCtorEq, IsEmpty.forall_iff, Option.some.injEq]
  all_goals intro hsn hst hW
  all_goals first
    | exact ⟨fun h => by have := (hst _ rfl).1 h; omega, _, hW.1⟩
    | exact ⟨fun h => by have := (hst _ rfl).1 h; omega, hW.1⟩

end SigmaFacts

section Sigma

variable {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C C' : Cfg m W Au V v₀}
  {L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)} {Dl : List (Proc m W Au)}

lemma completed_append_tau {x : OpId (Proc m W Au)} {p : Proc m W Au} :
    Completed (α ++ [.tau p]) x ↔ Completed α x := by
  simp [Completed, respsOf_append]

lemma wsn_le (hI : Inv rnd C) {w : W} {sn : ℕ} (h : wsn (C.loc (.wr w)) = some sn) :
    sn ≤ snOf C + 1 := by
  have hW := hI.wr w
  have := hI.seq_le
  unfold WInv at hW
  revert hW h
  cases C.loc (.wr w) <;> simp only [wsn, reduceCtorEq, IsEmpty.forall_iff, Option.some.injEq]
  all_goals rintro rfl hW
  · exact hW.2.2
  · exact hW.2.2.2.2.2
  · exact hW.2.1.2.2.2.2
  · exact hW.2.1.2.2.2.2
  · omega

/-- The response of an audit in the `D` list equals the set it will return. -/
lemma target_eq_dl (hL : LInv rnd α C L Dl) (hD : (rOf C).seq = snOf C + 1) {a : Au}
    {r : RVal m V} (hr : ar (C.loc (.au a)) = some r) (hrs : r.seq = (rOf C).seq)
    {D1 D2 : List (Proc m W Au)} (hsplit : Dl = D1 ++ Proc.au a :: D2) :
    Target rnd C r = Pairs rnd C (snOf C) ∪ {x | ∃ i, Proc.rd i ∈ D1 ∧ x = (i, (rOf C).val)} := by
  have hok := ar_aok hL.inv hr
  have ha : Proc.au a ∈ Dl := by rw [hsplit]; simp
  have hnd := hL.dl_nodup
  ext ⟨i, u⟩
  simp only [Target, Pairs, Set.mem_union, Set.mem_ofPred_eq, Prod.mk.injEq]
  have hrd : readersOf rnd r i ↔ Proc.rd i ∈ D1 := by
    rw [hL.dl_order a r hr ha i]
    constructor
    · intro h; rw [hsplit] at h hnd; exact mem_left_of_sublist_pair hnd h
    · intro h; rw [hsplit]; exact sublist_pair_iff.2 ⟨D1, Proc.au a :: D2, rfl, h, by simp⟩
  have hval : r.val = (rOf C).val := by rw [hok.2.1, hrs]; simp [AuditingWithoutLeaks.hv]
  constructor
  · rintro (⟨t, ht, hf, rfl⟩ | ⟨h1, rfl⟩)
    · exact Or.inl ⟨t, by omega, hf, rfl⟩
    · exact Or.inr ⟨i, hrd.1 h1, rfl, hval⟩
  · rintro (⟨t, ht, hf, rfl⟩ | ⟨i', h1, rfl, rfl⟩)
    · exact Or.inl ⟨t, by omega, hf, rfl⟩
    · exact Or.inr ⟨hrd.2 h1, hval.symm⟩

lemma LInv.sigma (hL : LInv rnd α C L Dl) (hrun : (alg1 rnd v₀).run α = some C)
    {p : Proc m W Au} (hs : (alg1 rnd v₀).step C (.tau p) = some C')
    (hD : (rOf C).seq = snOf C + 1) (hR : C'.mem .R = C.mem .R)
    (hV : ∀ t, C'.mem (.V t) = C.mem (.V t)) (hB : ∀ t i, C'.mem (.B t i) = C.mem (.B t i))
    (hsn : snOf C' = (rOf C).seq) (hpend : C'.pend = C.pend)
    (hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hp : (∃ j prev val, p = .rd j ∧ C.loc p = .rCAS prev (rOf C).seq val ∧
              C'.loc p = .rRet (some ((rOf C).seq, val)) val) ∨
          (∃ w, p = .wr w ∧ C.loc p = .wHelp (rOf C).seq ∧ C'.loc p = .wRet) ∨
          (∃ a A r, p = .au a ∧ C.loc p = .aCAS A r ∧ r.seq = (rOf C).seq ∧
              C'.loc p = .aRet A r.seq)) :
    ∃ M, LInv rnd (α ++ [.tau p]) C' (L ++ M) [] := by
  obtain ⟨hI', E⟩ := Inv.step hL.inv hs
  obtain ⟨wst, hwl, hwp⟩ := hL.dinv hD
  have hrR : rOf C' = rOf C := hR
  have hinj : Function.Injective (curOp α) := fun a b h => congrArg Prod.fst h
  let ws := (writersIn α).filter (fun w => decide (w ≠ wst ∧ wsn (C.loc (.wr w)) = some (rOf C).seq))
  let wop : W → AOp m V := fun w => (C.pend (.wr w)).getD (.write v₀)
  let Ws := ws.map (fun w => (curOp α (.wr w), wop w))
  let vis : OpId (Proc m W Au) × AOp m V := (curOp α (.wr wst), .write (rOf C).val)
  let Dops := Dl.map (fun q => (curOp α q, (opOfP q : AOp m V)))
  let M := Ws ++ vis :: Dops
  -- writers holding the new sequence number
  have hws : ∀ w ∈ ws, w ≠ wst ∧ wsn (C.loc (.wr w)) = some (rOf C).seq := by
    intro w hw; simpa [ws] using (List.mem_filter.1 hw).2
  have hwsall : ∀ w, w ≠ wst → wsn (C.loc (.wr w)) = some (rOf C).seq → w ∈ ws := by
    intro w hw hs'
    obtain ⟨u, hu⟩ := (hL.wr_info (by rw [hs', hD])).2
    have hinv := (Impl.run_pend_curOp hrun hu).1
    exact List.mem_filter.2 ⟨mem_writersIn hinv, by simp [hw, hs']⟩
  have hprocs : (ws.map Proc.wr ++ Proc.wr wst :: Dl).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.nodup_dedup _).filter _ |>.map (fun _ _ h => by cases h; rfl), ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun h => hL.dl_wr wst h, hL.dl_nodup⟩
    · intro x hx y hy hxy
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      rcases List.mem_cons.1 hy with h | h
      · rw [h] at hxy; exact (hws w hw).1 (Proc.wr.inj hxy)
      · rw [← hxy] at h; exact hL.dl_wr w h
  have hkeys : M.map Prod.fst = (ws.map Proc.wr ++ Proc.wr wst :: Dl).map (curOp α) := by
    simp [M, Ws, vis, Dops, Function.comp_def]
  have hpendM : ∀ y ∈ M, ∃ q, y.1 = curOp α q ∧ C.pend q = some y.2 := by
    intro y hy
    simp only [M, Ws, vis, Dops, List.mem_append, List.mem_map, List.mem_cons] at hy
    rcases hy with ⟨w, hw, rfl⟩ | rfl | ⟨q, hq, rfl⟩
    · obtain ⟨u, hu⟩ := (hL.wr_info (by rw [(hws w hw).2, hD])).2
      exact ⟨.wr w, rfl, by simp [wop, hu]⟩
    · exact ⟨.wr wst, rfl, hwp⟩
    · cases q with
      | rd i => exact ⟨.rd i, rfl, (hL.dl_rd_info hq).choose_spec.2.2⟩
      | wr w => exact absurd hq (hL.dl_wr w)
      | au a => exact ⟨.au a, rfl, (hL.dl_au_info hq).choose_spec.2.2.2⟩
  have hdisj : ∀ y ∈ M, y.1 ∉ L.map Prod.fst := by
    intro y hy
    simp only [M, Ws, vis, Dops, List.mem_append, List.mem_map, List.mem_cons] at hy
    rcases hy with ⟨w, hw, rfl⟩ | rfl | ⟨q, hq, rfl⟩
    · exact (hL.wr_info (by rw [(hws w hw).2, hD])).1
    · exact (hL.wr_info (by rw [hwl]; simp [wsn, hD])).1
    · cases q with
      | rd i => exact (hL.dl_rd_info hq).choose_spec.2.1
      | wr w => exact absurd hq (hL.dl_wr w)
      | au a => exact (hL.dl_au_info hq).choose_spec.2.2.1
  have hlin : IsLinearization (α ++ [.tau p]) (L ++ M) := by
    refine (hL.lin.append_tau p).push_list M (fun y hy => ?_) ?_ hdisj
    · obtain ⟨q, hq1, hq2⟩ := hpendM y hy
      obtain ⟨-, h2, h3⟩ := Impl.run_pend_curOp hrun hq2
      rw [hq1]
      exact ⟨by rw [opOf_append_tau]; exact h3, by rw [completed_append_tau]; exact h2⟩
    · rw [hkeys]; exact hprocs.map hinj
  have hnd : ((L ++ M).map Prod.fst).Nodup := hlin.nodup
  -- the abstract state after `Ws ++ [vis]`
  have hpre : (auditReg m V v₀).runOps (auditReg m V v₀).init ((L ++ Ws ++ [vis]).map Prod.snd) =
      ((rOf C).val, Pairs rnd C (snOf C)) := by
    rw [List.map_append, List.map_append, ObjSpec.runOps_append, ObjSpec.runOps_append]
    have h0 : (auditReg m V v₀).runOps (auditReg m V v₀).init (L.map Prod.snd) =
        (hv v₀ C (snOf C), Pairs rnd C (snOf C)) := hL.abs
    rw [h0]
    have h1 := runOps_writes (v₀ := v₀) (Ws.map Prod.snd) (fun o ho => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ho
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
      obtain ⟨u, hu⟩ := (hL.wr_info (by rw [(hws w hw).2, hD])).2
      exact ⟨u, by simp [wop, hu]⟩) (hv v₀ C (snOf C), Pairs rnd C (snOf C))
    simp only [List.map_cons, List.map_nil, ObjSpec.runOps_cons, ObjSpec.runOps_nil]
    exact Prod.ext rfl h1
  have hnoW : ∀ q ∈ Dl, ∀ w, q ≠ Proc.wr w := fun q hq w h => hL.dl_wr w (h ▸ hq)
  have hresp : ∀ D1 q D2, Dl = D1 ++ q :: D2 →
      respL v₀ (L ++ M) (curOp α q) = some ((auditReg m V v₀).δ
        ((rOf C).val, Pairs rnd C (snOf C) ∪ {x | ∃ i, Proc.rd i ∈ D1 ∧ x = (i, (rOf C).val)})
        (opOfP q)).2 := by
    intro D1 q D2 hsp
    have hsplit : L ++ M = (L ++ Ws ++ vis :: D1.map (fun q => (curOp α q, (opOfP q : AOp m V))))
        ++ (curOp α q, opOfP q) :: D2.map (fun q => (curOp α q, (opOfP q : AOp m V))) := by
      simp [M, Dops, hsp]
    rw [respL, ObjSpec.respIn_of_split hnd hsplit]
    congr 2
    rw [show L ++ Ws ++ vis :: D1.map (fun q => (curOp α q, (opOfP q : AOp m V))) =
      (L ++ Ws ++ [vis]) ++ D1.map (fun q => (curOp α q, (opOfP q : AOp m V))) by simp,
      List.map_append, ObjSpec.runOps_append, hpre, List.map_map]
    have hm : D1.map (Prod.snd ∘ fun q => (curOp α q, (opOfP q : AOp m V))) = D1.map opOfP := by
      simp [Function.comp_def]
    rw [hm, runOps_dl (v₀ := v₀) D1 (fun q' hq' => hnoW q' (by rw [hsp]; simp [hq']))]
  have hmemM : ∀ q, curOp α q ∈ M.map Prod.fst ↔ q ∈ ws.map Proc.wr ++ Proc.wr wst :: Dl := by
    intro q; rw [hkeys]
    exact ⟨fun h => by obtain ⟨q', hq', he⟩ := List.mem_map.1 h; rwa [hinj he] at hq',
      fun h => List.mem_map_of_mem h⟩
  have hcur : ∀ q, curOp (α ++ [.tau p]) q = curOp α q := fun q => curOp_append_tau _ _ _
  have hfet : ∀ i t, Fetched rnd C' i t ↔ Fetched rnd C i t := by
    intro i t; simp only [Fetched, hrR, hB]
  have hhv : ∀ t, hv v₀ C' t = hv v₀ C t := by
    intro t; simp only [AuditingWithoutLeaks.hv, hrR, hV]
  have habs : linState (L ++ M) = (hv v₀ C' (snOf C'), Pairs rnd C' (snOf C')) := by
    have hLM : L ++ M = (L ++ Ws ++ [vis]) ++ Dops := by simp [M]
    simp only [linState]
    rw [hLM, List.map_append, ObjSpec.runOps_append, hpre]
    have hm : Dops.map Prod.snd = Dl.map opOfP := by simp [Dops, Function.comp_def]
    rw [hm, runOps_dl (v₀ := v₀) Dl hnoW]
    refine Prod.ext ?_ ?_
    · simp [AuditingWithoutLeaks.hv, hsn, hrR]
    · ext ⟨i, u⟩
      simp only [Pairs, Set.mem_union, Set.mem_ofPred_eq, Prod.mk.injEq, hsn, hfet, hhv]
      constructor
      · rintro (⟨t, ht, hf, rfl⟩ | ⟨i', h1, rfl, rfl⟩)
        · exact ⟨t, by omega, hf, rfl⟩
        · obtain ⟨-, hb⟩ := (hL.dl_readers i).1 h1
          exact ⟨(rOf C).seq, le_rfl, Or.inr ⟨rfl, hb⟩, by simp [AuditingWithoutLeaks.hv]⟩
      · rintro ⟨t, ht, hf, rfl⟩
        rcases Nat.lt_or_eq_of_le ht with ht | rfl
        · exact Or.inl ⟨t, by omega, hf, rfl⟩
        · rcases hf with ⟨h, -⟩ | ⟨-, hb⟩
          · omega
          · exact Or.inr ⟨i, (hL.dl_readers i).2 ⟨hD, hb⟩, rfl, by simp [AuditingWithoutLeaks.hv]⟩
  refine ⟨M, hI', DInv2.step hL.inv hL.dinv hs, BInv.step hL.inv hL.binv hs, hlin, habs,
    fun j => ?_, fun w => ?_, fun a => ?_, List.nodup_nil, fun _ => rfl, by simp, by simp,
    by simp, fun i => by simp [hrR, hsn], by simp⟩
  · -- readers
    by_cases hjp : Proc.rd j = p
    · rcases hp with ⟨j', prev, val, hpj, hl, hl'⟩ | ⟨w, hpw, -⟩ | ⟨a, -, -, hpa, -⟩
      · rw [← hjp] at hl hl'
        have hj : Proc.rd j ∈ Dl := by
          have hst := hL.rd j
          unfold RSt at hst; rw [hl] at hst
          rcases hst with ⟨-, h⟩ | ⟨-, h, -⟩
          · omega
          · exact h
        obtain ⟨prev', hl2, -, -⟩ := hL.dl_rd_info hj
        rw [hl] at hl2
        obtain ⟨-, -, rfl⟩ := Loc.rCAS.inj hl2
        obtain ⟨s1, t1, hsplit⟩ := List.append_of_mem hj
        unfold RSt; rw [hcur, hl', hresp s1 _ t1 hsplit]; rfl
      · rw [hpw] at hjp; cases hjp
      · rw [hpa] at hjp; cases hjp
    · by_cases hj : Proc.rd j ∈ Dl
      · obtain ⟨prev, hl, -, -⟩ := hL.dl_rd_info hj
        obtain ⟨s1, t1, hsplit⟩ := List.append_of_mem hj
        unfold RSt; rw [hcur, hlocq _ hjp, hl]
        exact Or.inl ⟨by rw [hresp s1 _ t1 hsplit]; rfl, by rw [hsn]⟩
      · exact RSt.transfer (hL.rd j) (hlocq _ hjp) (hcur _)
          (fun h => by rw [hmemM] at h; simp [hj] at h) (fun h => absurd h hj) E.sn
          (fun h => absurd h hj)
  · -- writers
    have hinM : ∀ w, wsn (C.loc (.wr w)) = some (rOf C).seq → curOp α (.wr w) ∈ M.map Prod.fst := by
      intro w hw'
      rw [hmemM]
      by_cases hww : w = wst
      · subst hww; simp
      · simp [hwsall w hww hw']
    by_cases hwp' : Proc.wr w = p
    · rcases hp with ⟨j', -, -, hpj, -⟩ | ⟨w', hpw, hl, hl'⟩ | ⟨a, -, -, hpa, -⟩
      · rw [hpj] at hwp'; cases hwp'
      · rw [← hwp'] at hl hl'
        unfold WSt; rw [hcur, hl']
        have := hinM w (by rw [hl]; rfl)
        simp only [List.map_append, List.mem_append]; exact Or.inr this
      · rw [hpa] at hwp'; cases hwp'
    · have hst := hL.wr w
      have hle : ∀ sn, wsn (C.loc (.wr w)) = some sn → sn ≤ snOf C + 1 :=
        fun sn h => wsn_le hL.inv h
      unfold WSt at hst ⊢
      rw [hcur, hlocq _ hwp']
      cases hl : C.loc (.wr w) <;> simp only [hl] at hst ⊢
      case wSN v =>
        refine not_mem_append hst (fun h => ?_)
        rw [hmemM] at h
        simp only [List.mem_append, List.mem_map, List.mem_cons, Proc.wr.injEq] at h
        rcases h with ⟨w', hw', he⟩ | he | h
        · subst he; have := (hws w' hw').2; rw [hl] at this; simp [wsn] at this
        · subst he; rw [hwl] at hl; cases hl
        · exact hL.dl_wr w h
      case wRet =>
        simp only [List.map_append, List.mem_append]; exact Or.inl hst
      all_goals
        intro sn hsn'
        have h1 := hle sn (by rw [hl]; exact hsn')
        rw [hsn]
        by_cases hx : sn = (rOf C).seq
        · subst hx
          simp only [le_refl, iff_true, List.map_append, List.mem_append]
          exact Or.inr (hinM w (by rw [hl]; exact hsn'))
        · have h2 : sn ≤ snOf C := by omega
          simp only [List.map_append, List.mem_append]
          exact ⟨fun _ => by omega, fun _ => Or.inl ((hst sn hsn').2 h2)⟩
  · -- auditors
    by_cases hap : Proc.au a = p
    · rcases hp with ⟨j', -, -, hpj, -⟩ | ⟨w', hpw, -⟩ | ⟨a', A, r, hpa, hl, hrs, hl'⟩
      · rw [hpj] at hap; cases hap
      · rw [hpw] at hap; cases hap
      · rw [← hap] at hl hl'
        have ha : Proc.au a ∈ Dl := by
          have hst := hL.au a
          unfold ASt at hst; rw [hl] at hst
          rcases hst r rfl with ⟨-, h⟩ | ⟨-, h, -⟩
          · omega
          · exact h
        have hA := hL.inv.au a
        unfold AInv at hA; rw [hl] at hA
        obtain ⟨s1, t1, hsplit⟩ := List.append_of_mem ha
        unfold ASt; rw [hcur, hl', hresp s1 _ t1 hsplit, hA.2.2,
          target_eq_dl hL hD (by rw [hl]; rfl) hrs hsplit]
        rfl
    · by_cases ha : Proc.au a ∈ Dl
      · obtain ⟨r, hr, hrs, -, -⟩ := hL.dl_au_info ha
        obtain ⟨s1, t1, hsplit⟩ := List.append_of_mem ha
        have htg := target_eq_dl hL hD hr hrs hsplit
        have hok := (ar_aok hL.inv hr).1
        unfold ASt
        rw [hcur, hlocq _ hap]
        have key : ∀ r', ar (C.loc (.au a)) = some r' →
            (respL v₀ (L ++ M) (curOp α (.au a)) = some (.set (Target rnd C' r')) ∧
              r'.seq ≤ snOf C') ∨ (curOp α (.au a) ∉ (L ++ M).map Prod.fst ∧ Proc.au a ∈ ([] : List (Proc m W Au)) ∧
              r'.seq = (rOf C').seq ∧ (rOf C').seq = snOf C' + 1) := by
          intro r' hr'
          rw [hr] at hr'; cases hr'
          left
          refine ⟨?_, by rw [hsn, hrs]⟩
          rw [hresp s1 _ t1 hsplit, E.target hok, htg]; rfl
        revert key hr
        cases C.loc (.au a) <;> simp only [ar, reduceCtorEq, IsEmpty.forall_iff, imp_self,
          imp_true_iff] <;> intro _ key <;> first | exact key | exact fun r h => key r h
      · exact ASt.transfer hL.inv E (hL.au a) (hlocq _ hap) (hcur _)
          (fun h => by rw [hmemM] at h; simp [ha] at h) (fun h => absurd h ha)
          (fun h => absurd h ha)

end Sigma

section Pushes

variable {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C C' : Cfg m W Au V v₀}
  {L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)} {Dl : List (Proc m W Au)}

lemma sublist_pair_append_ne {X : Type} {x y z : X} {l : List X} (hyz : y ≠ z) :
    [x, y].Sublist (l ++ [z]) ↔ [x, y].Sublist l := by
  constructor
  · intro h
    obtain ⟨l1, l2, he, h1, h2⟩ := List.sublist_append_iff.1 h
    rcases List.sublist_singleton.1 h2 with rfl | rfl
    · rw [he, List.append_nil]; exact h1
    · have : l1 ++ [z] = [x, y] := he.symm
      have hz := congrArg List.getLast? this
      simp at hz; exact absurd hz.symm hyz
  · intro h; exact h.trans (List.sublist_append_left _ _)

lemma sublist_pair_append_self {X : Type} {x y : X} {l : List X} (hxy : x ≠ y) :
    [x, y].Sublist (l ++ [y]) ↔ x ∈ l := by
  constructor
  · intro h
    have : x ∈ l ++ [y] := h.subset (by simp)
    simpa [hxy] using this
  · intro h; exact sublist_pair_iff.2 ⟨l, [y], rfl, h, by simp⟩

/-- A successful `R.compare&swap` (`ρ`): nothing is linearized. -/
lemma LInv.rho (hL : LInv rnd α C L Dl) {w : W} (hs : (alg1 rnd v₀).step C (.tau (.wr w)) = some C')
    {v : V} {sn : ℕ} {r : RVal m V} (hl : C.loc (.wr w) = .wCAS v sn r) (heq : rOf C = r)
    (hR : (C'.mem .R : RVal m V) = ⟨sn, v, rnd sn⟩) (hsn : snOf C' = snOf C)
    (hV : ∀ t, C'.mem (.V t) = C.mem (.V t)) (hB : ∀ t i, C'.mem (.B t i) = C.mem (.B t i))
    (hpend : C'.pend = C.pend) (hlocq : ∀ q, q ≠ Proc.wr w → C'.loc q = C.loc q)
    (hl' : C'.loc (.wr w) = .wHelp sn) :
    LInv rnd (α ++ [.tau (.wr w)]) C' L [] := by
  obtain ⟨hI', E⟩ := Inv.step hL.inv hs
  have hW := hL.inv.wr w
  unfold WInv at hW; rw [hl] at hW
  obtain ⟨-, hw1, -, -⟩ := hW
  have hE : (rOf C).seq = snOf C := by
    have := hw1.1; have := hw1.2.2.2.2; have := hL.inv.sn_le; subst heq; omega
  have hDl : Dl = [] := hL.dl_E hE
  subst hDl
  have hsn1 : sn = (rOf C).seq + 1 := by subst heq; exact hw1.1.symm
  have hrR : rOf C' = ⟨sn, v, rnd sn⟩ := hR
  have hcur : ∀ q, curOp (α ++ [.tau (.wr w)]) q = curOp α q := fun q => curOp_append_tau _ _ _
  have hL0 : L = L ++ [] := (List.append_nil L).symm
  refine ⟨hI', DInv2.step hL.inv hL.dinv hs, BInv.step hL.inv hL.binv hs,
    hL.lin.append_tau _, ?_, fun j => ?_, fun w' => ?_, fun a => ?_, List.nodup_nil,
    fun _ => rfl, by simp, by simp, by simp, fun i => ?_, by simp⟩
  · rw [hL.abs, hsn, E.hv _ hL.inv.sn_le]
    congr 1
    ext ⟨i, u⟩
    simp only [Pairs, Set.mem_ofPred_eq]
    have hf : ∀ t ≤ snOf C, (Fetched rnd C' i t ↔ Fetched rnd C i t) := by
      intro t ht
      rcases Nat.lt_or_eq_of_le (ht.trans hL.inv.sn_le) with h | h
      · exact E.fet_iff _ _ h
      · subst h
        refine ⟨fun h' => ?_, E.fet _ _⟩
        rcases h' with ⟨-, hb⟩ | ⟨h1, -⟩
        · rw [hB] at hb
          exact Or.inr (hL.binv _ _ le_rfl hb)
        · rw [hrR] at h1; simp at h1; omega
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      exact ⟨t, ht, (hf t ht).2 h1, by rw [h2, E.hv _ (ht.trans hL.inv.sn_le)]⟩
    · rintro ⟨t, ht, h1, h2⟩
      exact ⟨t, ht, (hf t ht).1 h1, by rw [h2, E.hv _ (ht.trans hL.inv.sn_le)]⟩
  · rw [hL0]
    exact RSt.transfer (hL.rd j) (hlocq _ (by simp)) (hcur _) (by simp) (fun h => by simp at h)
      E.sn (fun h => by simp at h)
  · by_cases hw : w' = w
    · subst hw
      have hst := hL.wr w'
      unfold WSt at hst ⊢
      rw [hl] at hst; rw [hl', hcur, hsn]
      intro sn' hs'
      simp only [wsn, Option.some.injEq] at hs'
      rw [← hs']; exact hst sn rfl
    · rw [hL0]
      exact WSt.transfer (hL.wr w') (hlocq _ (by simpa using hw)) (hcur _) (by simp) hsn
  · rw [hL0]
    exact ASt.transfer hL.inv E (hL.au a) (hlocq _ (by simp)) (hcur _) (by simp)
      (fun h => by simp at h) (fun h => by simp at h)
  · simp [hrR, hsn, hsn1, hE]

/-- A fetch&xor in a `D` phase: the reader is appended to `Dl`. -/
lemma LInv.dpush_rd (hL : LInv rnd α C L Dl) {j : Fin m}
    (hs : (alg1 rnd v₀).step C (.tau (.rd j)) = some C') (hD : (rOf C).seq = snOf C + 1)
    {prev : Option (ℕ × V)} {y : ℕ} (hl : C.loc (.rd j) = .rFX prev y)
    (hR : (C'.mem .R : RVal m V) = { rOf C with bits := flip (rOf C).bits j })
    (hsn : snOf C' = snOf C)
    (hV : ∀ t, C'.mem (.V t) = C.mem (.V t)) (hB : ∀ t i, C'.mem (.B t i) = C.mem (.B t i))
    (hlocq : ∀ q, q ≠ Proc.rd j → C'.loc q = C.loc q)
    (hl' : C'.loc (.rd j) = .rCAS prev (rOf C).seq (rOf C).val) :
    LInv rnd (α ++ [.tau (.rd j)]) C' L (Dl ++ [.rd j]) := by
  obtain ⟨hI', E⟩ := Inv.step hL.inv hs
  have hrR : rOf C' = { rOf C with bits := flip (rOf C).bits j } := hR
  have hseq : (rOf C').seq = (rOf C).seq := by rw [hrR]
  have hcur : ∀ q, curOp (α ++ [.tau (.rd j)]) q = curOp α q := fun q => curOp_append_tau _ _ _
  have hjD : Proc.rd j ∉ Dl := by
    intro h; obtain ⟨_, _, _, h'⟩ := hL.dl_rd j h; rw [hl] at h'; cases h'
  have hbj : (rOf C).bits j = rnd (rOf C).seq j := by
    by_contra hc; exact hjD ((hL.dl_readers j).2 ⟨hD, hc⟩)
  have hL0 : L = L ++ [] := (List.append_nil L).symm
  refine ⟨hI', DInv2.step hL.inv hL.dinv hs, BInv.step hL.inv hL.binv hs,
    hL.lin.append_tau _, ?_, fun j' => ?_, fun w => ?_, fun a => ?_, ?_, ?_, fun j' hj' => ?_,
    fun a ha => ?_, fun w => by simpa using hL.dl_wr w, fun i => ?_, fun a r hr ha i => ?_⟩
  · rw [hL.abs, hsn, E.hv _ hL.inv.sn_le]
    congr 1
    ext ⟨i, u⟩
    simp only [Pairs, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      exact ⟨t, ht, (E.fet_iff i t (by omega)).2 h1, by rw [h2, E.hv _ (by omega)]⟩
    · rintro ⟨t, ht, h1, h2⟩
      exact ⟨t, ht, (E.fet_iff i t (by omega)).1 h1, by rw [h2, E.hv _ (by omega)]⟩
  · by_cases h : j' = j
    · subst h
      have hst := hL.rd j'
      unfold RSt at hst ⊢
      rw [hl] at hst; rw [hl', hcur]
      exact Or.inr ⟨by rw [hL0]; exact not_mem_append hst (by simp), by simp, hseq.symm,
        by rw [hseq, hsn]; exact hD⟩
    · rw [hL0]
      exact RSt.transfer (hL.rd j') (hlocq _ (by simpa using h)) (hcur _) (by simp)
        (fun h' => List.mem_append_left _ h') E.sn (fun _ => ⟨hseq, hsn⟩)
  · rw [hL0]
    exact WSt.transfer (hL.wr w) (hlocq _ (by simp)) (hcur _) (by simp) hsn
  · rw [hL0]
    exact ASt.transfer hL.inv E (hL.au a) (hlocq _ (by simp)) (hcur _) (by simp)
      (fun h' => List.mem_append_left _ h') (fun _ => ⟨hseq, hsn⟩)
  · exact List.nodup_append.2 ⟨hL.dl_nodup, List.nodup_singleton _,
      fun a ha b hb hab => by simp at hb; subst hb; subst hab; exact hjD ha⟩
  · intro h; rw [hseq, hsn] at h; omega
  · rcases List.mem_append.1 hj' with h | h
    · have hne : j' ≠ j := fun he => hjD (he ▸ h)
      rw [hlocq _ (by simpa using hne)]; exact hL.dl_rd j' h
    · simp at h; subst h; exact ⟨_, _, _, hl'⟩
  · have ha' : Proc.au a ∈ Dl := by simpa using ha
    rw [hlocq _ (by simp), hseq]; exact hL.dl_au a ha'
  · simp only [List.mem_append, List.mem_singleton, Proc.rd.injEq, hseq, hsn, hrR]
    rw [hL.dl_readers i]
    by_cases h : i = j
    · subst h; simp [flip, hbj, hD]
    · simp [flip, Function.update_of_ne h, h]
  · have ha' : Proc.au a ∈ Dl := by simpa using ha
    have hr' : ar (C.loc (.au a)) = some r := by rw [← hlocq _ (by simp)]; exact hr
    rw [hL.dl_order a r hr' ha' i, sublist_pair_append_ne (by simp)]

/-- A read of `R` by an audit in a `D` phase: the auditor is appended to `Dl`. -/
lemma LInv.dpush_au (hL : LInv rnd α C L Dl) {a : Au}
    (hs : (alg1 rnd v₀).step C (.tau (.au a)) = some C') (hD : (rOf C).seq = snOf C + 1)
    {A : Set (Fin m × V)} {lsa : ℕ} (hl : C.loc (.au a) = .aR A lsa)
    (hm : C'.mem = C.mem) (hlocq : ∀ q, q ≠ Proc.au a → C'.loc q = C.loc q)
    (hl' : ar (C'.loc (.au a)) = some (rOf C)) :
    LInv rnd (α ++ [.tau (.au a)]) C' L (Dl ++ [.au a]) := by
  obtain ⟨hI', E⟩ := Inv.step hL.inv hs
  have hrR : rOf C' = rOf C := by simp [rOf, hm]
  have hsn : snOf C' = snOf C := by simp [snOf, hm]
  have hcur : ∀ q, curOp (α ++ [.tau (.au a)]) q = curOp α q := fun q => curOp_append_tau _ _ _
  have haD : Proc.au a ∉ Dl := by
    intro h; obtain ⟨_, h', -⟩ := hL.dl_au a h; rw [hl] at h'; simp [ar] at h'
  have hL0 : L = L ++ [] := (List.append_nil L).symm
  have hpairs : Pairs rnd C' (snOf C) = Pairs rnd C (snOf C) :=
    pairs_eq E (by rw [hrR]) (by rw [hrR]) hL.inv.sn_le
  refine ⟨hI', DInv2.step hL.inv hL.dinv hs, BInv.step hL.inv hL.binv hs,
    hL.lin.append_tau _, ?_, fun j => ?_, fun w => ?_, fun a' => ?_, ?_, ?_,
    fun j hj => ?_, fun a' ha' => ?_, fun w => by simpa using hL.dl_wr w, fun i => ?_,
    fun a' r hr ha' i => ?_⟩
  · rw [hL.abs, hsn, hpairs, E.hv _ hL.inv.sn_le]
  · rw [hL0]
    exact RSt.transfer (hL.rd j) (hlocq _ (by simp)) (hcur _) (by simp)
      (fun h' => List.mem_append_left _ h') E.sn (fun _ => ⟨by rw [hrR], hsn⟩)
  · rw [hL0]
    exact WSt.transfer (hL.wr w) (hlocq _ (by simp)) (hcur _) (by simp) hsn
  · by_cases h : a' = a
    · subst h
      have hst := hL.au a'
      unfold ASt at hst ⊢
      rw [hl] at hst; rw [hcur]
      have key : ∀ r, ar (C'.loc (.au a')) = some r →
          (respL v₀ L (curOp α (.au a')) = some (.set (Target rnd C' r)) ∧ r.seq ≤ snOf C') ∨
          (curOp α (.au a') ∉ L.map Prod.fst ∧ Proc.au a' ∈ Dl ++ [.au a'] ∧
            r.seq = (rOf C').seq ∧ (rOf C').seq = snOf C' + 1) := by
        intro r hr; rw [hl'] at hr; cases hr
        exact Or.inr ⟨hst, by simp, by rw [hrR], by rw [hrR, hsn]; exact hD⟩
      revert key hl'
      cases C'.loc (.au a') <;> simp only [ar, reduceCtorEq, IsEmpty.forall_iff, imp_self,
        imp_true_iff, List.append_nil] <;> intro _ key <;> first | exact key | exact fun r h => key r h
    · rw [hL0]
      exact ASt.transfer hL.inv E (hL.au a') (hlocq _ (by simpa using h)) (hcur _) (by simp)
        (fun h' => List.mem_append_left _ h') (fun _ => ⟨by rw [hrR], hsn⟩)
  · exact List.nodup_append.2 ⟨hL.dl_nodup, List.nodup_singleton _,
      fun x hx b hb hab => by simp at hb; subst hb; subst hab; exact haD hx⟩
  · intro h; rw [hrR, hsn] at h; omega
  · have hj' : Proc.rd j ∈ Dl := by simpa using hj
    rw [hlocq _ (by simp)]; exact hL.dl_rd j hj'
  · rcases List.mem_append.1 ha' with h | h
    · have hne : a' ≠ a := fun he => haD (he ▸ h)
      rw [hlocq _ (by simpa using hne), hrR]; exact hL.dl_au a' h
    · simp at h; subst h; exact ⟨_, hl', by rw [hrR]⟩
  · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false, hrR, hsn]
    exact hL.dl_readers i
  · by_cases h : a' = a
    · subst h
      rw [hl'] at hr; cases hr
      rw [sublist_pair_append_self (by simp), hL.dl_readers i]
      simp [readersOf, hD]
    · have ha'' : Proc.au a' ∈ Dl := by simpa [h] using ha'
      have hr' : ar (C.loc (.au a')) = some r := by rw [← hlocq _ (by simpa using h)]; exact hr
      rw [hL.dl_order a' r hr' ha'' i, sublist_pair_append_ne (by simpa using h)]

end Pushes

section Steps

variable {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C C' : Cfg m W Au V v₀}
  {L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)} {Dl : List (Proc m W Au)}

/-- `LInv.quiet` without new linearization points. -/
lemma LInv.quiet0 (hL : LInv rnd α C L Dl) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some C')
    (hseq : (rOf C').seq = (rOf C).seq) (hsn : snOf C' = snOf C)
    (hbits : (rOf C').bits = (rOf C).bits) (hlin : IsLinearization (α ++ [ℓ]) L)
    (hcur : ∀ q, q ≠ ℓ.proc → curOp (α ++ [ℓ]) q = curOp α q)
    (hloc : ∀ q, q ≠ ℓ.proc → C'.loc q = C.loc q)
    (hown : PSt rnd (α ++ [ℓ]) C' L Dl ℓ.proc)
    (hrdDl : ∀ j, Proc.rd j = ℓ.proc → Proc.rd j ∈ Dl →
      ∃ prev sn val, C'.loc (.rd j) = .rCAS prev sn val)
    (hauDl : ∀ a, Proc.au a = ℓ.proc → Proc.au a ∈ Dl →
      ar (C'.loc (.au a)) = ar (C.loc (.au a))) :
    LInv rnd (α ++ [ℓ]) C' L Dl := by
  have E := (Inv.step hL.inv hs).2
  have h := hL.quiet hs (M := []) hseq hsn (fun _ => hbits) (by simpa using hlin)
    (by rw [List.append_nil, hL.abs, hsn, pairs_eq E hseq hbits hL.inv.sn_le,
      E.hv _ hL.inv.sn_le]) hcur (fun q _ => by simp) hloc (by simpa using hown) hrdDl hauDl
  simpa using h

lemma linState_concat (L : List (OpId (Proc m W Au) × (auditReg m V v₀).Op))
    (x : OpId (Proc m W Au)) (o : (auditReg m V v₀).Op) :
    linState (L ++ [(x, o)]) = ((auditReg m V v₀).δ (linState L) o).1 := by
  unfold linState; rw [List.map_append, ObjSpec.runOps_append]; rfl

lemma curOp_ne {α : List (Label (Proc m W Au) (auditReg m V v₀))} {p q : Proc m W Au}
    (h : q ≠ p) : curOp α q ≠ curOp α p := fun h' => h (congrArg Prod.fst h')

lemma LInv.step_rd (hL : LInv rnd α C L Dl) (hrun : (alg1 rnd v₀).run α = some C) {j : Fin m}
    (hs : (alg1 rnd v₀).step C (.tau (.rd j)) = some C') :
    ∃ M Dl', LInv rnd (α ++ [.tau (.rd j)]) C' (L ++ M) Dl' := by
  obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hlocq : ∀ q, q ≠ Proc.rd j → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hcur : ∀ q, q ≠ (Label.tau (Proc.rd j) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      curOp (α ++ [.tau (.rd j)]) q = curOp α q := fun q _ => curOp_append_tau _ _ _
  have hlocq' : ∀ q, q ≠ (Label.tau (Proc.rd j) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      C'.loc q = C.loc q := hlocq
  have hnoDl : ∀ prev, C.loc (.rd j) ≠ .rCAS prev 0 v₀ ∨ True := fun _ => Or.inr trivial
  obtain ⟨hb, hr⟩ := hL.inv.rd j
  have hst := hL.rd j
  unfold RSt at hst
  have hlin0 : IsLinearization (α ++ [.tau (.rd j)]) L := hL.lin.append_tau _
  have hnotDl : (∀ prev sn val, C.loc (.rd j) ≠ .rCAS prev sn val) → Proc.rd j ∉ Dl := by
    intro h hd; obtain ⟨a, b, c, h'⟩ := hL.dl_rd j hd; exact h a b c h'
  cases hl : C.loc (.rd j) <;> rw [hl] at hr hb hst <;>
    simp only [alg1, readerAct, hl, reduceCtorEq] at hact
  case rSN prev =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    have hjD : Proc.rd j ∉ Dl := hnotDl (by rw [hl]; simp)
    obtain ⟨hp1, hp2⟩ := hr
    by_cases hsil : prev.map Prod.fst = some (snOf C)
    · obtain ⟨⟨x, pv⟩, rfl, hx⟩ := Option.map_eq_some_iff.1 hsil
      simp only at hx
      have hnew : C'.loc (.rd j) = .rRet (some (x, pv)) pv := by
        have hx' : x = C.mem .SN := hx
        simp [hloc, hx']
      obtain ⟨-, hpv, hfx⟩ := hp2 x pv rfl
      have hop := Impl.run_pend_curOp hrun hp1
      have hlin : IsLinearization (α ++ [.tau (.rd j)])
          (L ++ [(curOp α (.rd j), (AOp.read j : AOp m V))]) :=
        hlin0.push (by rw [opOf_append_tau]; exact hop.2.2) hst
          (by rw [completed_append_tau]; exact hop.2.1)
      have hmemP : (j, hv v₀ C (snOf C)) ∈ Pairs rnd C (snOf C) :=
        ⟨x, by omega, hfx, by rw [hx]⟩
      have hδ : (auditReg m V v₀).δ (linState L) (.read j) = (linState L, .val pv) := by
        rw [hL.abs]
        show ((hv v₀ C (snOf C), insert (j, hv v₀ C (snOf C)) (Pairs rnd C (snOf C))),
          AResp.val (hv v₀ C (snOf C))) = _
        rw [Set.insert_eq_of_mem hmemP, hpv, hx]
      refine ⟨[(curOp α (.rd j), (AOp.read j : AOp m V))], Dl,
        hL.quiet hs (by rw [hR]) hS (fun _ => by rw [hR]) hlin ?_ hcur
          (fun q hq => by simp only [List.map_cons, List.map_nil, List.mem_singleton]; exact curOp_ne hq) hlocq' ?_ (fun j' hj' h => by simp only [Label.proc, Proc.rd.injEq] at hj'; subst hj'; exact absurd h hjD)
          (fun _ h => by cases h)⟩
      · have hhv : hv v₀ C' = hv v₀ C := by funext t; unfold AuditingWithoutLeaks.hv rOf; rw [hm]
        have hP : Pairs rnd C' = Pairs rnd C := by funext n; simp [Pairs, Fetched, rOf, hm, hhv]
        rw [linState_concat, hδ, hL.abs, hhv, hP, hS]
      · show RSt _ _ _ _ j
        unfold RSt
        rw [hnew, curOp_append_tau, respL, ObjSpec.respIn_concat_self hst]
        rw [show (auditReg m V v₀).runOps (auditReg m V v₀).init (L.map Prod.snd) = linState L
          from rfl, hδ]
    · have hnew : C'.loc (.rd j) = .rFX prev (snOf C) := by
        have : ¬ prev.map Prod.fst = some (C.mem .SN) := hsil
        simp [hloc, this, snOf]
      refine ⟨[], Dl, ?_⟩
      rw [List.append_nil]
      refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) hlin0 hcur hlocq' ?_
          (fun j' hj' h => by simp only [Label.proc, Proc.rd.injEq] at hj'; subst hj'; exact absurd h hjD) (fun _ h => by cases h)
      show RSt _ _ _ _ j
      unfold RSt; rw [hnew, curOp_append_tau]; exact hst
  case rFX prev y =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hr
    have hjD : Proc.rd j ∉ Dl := hnotDl (by rw [hl]; simp)
    have hbj : (rOf C).bits j = rnd (rOf C).seq j := by
      by_contra hc
      obtain ⟨⟨x, v⟩, hx, hxe⟩ := Option.map_eq_some_iff.1 (hb.1 hc)
      have := hp3 x v hx
      have := hL.inv.sn_le
      simp at hxe; omega
    have hRm : (C'.mem .R : RVal m V) = { rOf C with bits := flip (rOf C).bits j } := by
      simp [hmem, rOf]
    have hrR : rOf C' = { rOf C with bits := flip (rOf C).bits j } := hRm
    have hseq : (rOf C').seq = (rOf C).seq := by rw [hrR]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hV : ∀ t, C'.mem (.V t) = C.mem (.V t) := fun t => by simp [hmem]
    have hB : ∀ t i, C'.mem (.B t i) = C.mem (.B t i) := fun t i => by simp [hmem]
    have hnew : C'.loc (.rd j) = .rCAS prev (rOf C).seq (rOf C).val := by simp [hloc, rOf]
    by_cases hE : (rOf C).seq = snOf C
    · have E := (Inv.step hL.inv hs).2
      have hop := Impl.run_pend_curOp hrun hp1
      have hlin : IsLinearization (α ++ [.tau (.rd j)])
          (L ++ [(curOp α (.rd j), (AOp.read j : AOp m V))]) :=
        hlin0.push (by rw [opOf_append_tau]; exact hop.2.2) hst
          (by rw [completed_append_tau]; exact hop.2.1)
      have hδ : (auditReg m V v₀).δ (linState L) (.read j) =
          ((hv v₀ C (snOf C), insert (j, hv v₀ C (snOf C)) (Pairs rnd C (snOf C))),
            .val (hv v₀ C (snOf C))) := by rw [hL.abs]
      have hvs : hv v₀ C (snOf C) = (rOf C).val := by simp [AuditingWithoutLeaks.hv, hE]
      refine ⟨[(curOp α (.rd j), (AOp.read j : AOp m V))], Dl,
        hL.quiet hs hseq hS (fun h => by omega) hlin ?_ hcur
          (fun q hq => by simp only [List.map_cons, List.map_nil, List.mem_singleton]; exact curOp_ne hq) hlocq' ?_ (fun j' hj' h => by simp only [Label.proc, Proc.rd.injEq] at hj'; subst hj'; exact absurd h hjD)
          (fun _ h => by cases h)⟩
      · rw [linState_concat, hδ, hS, E.hv _ hL.inv.sn_le]
        congr 1
        ext ⟨i', u⟩
        simp only [Pairs, Set.mem_insert_iff, Set.mem_ofPred_eq, Prod.mk.injEq]
        have hf : ∀ t ≤ snOf C, (Fetched rnd C' i' t ↔ (Fetched rnd C i' t ∨ (i' = j ∧ t = snOf C))) := by
          intro t ht
          rcases Nat.lt_or_eq_of_le ht with h | h
          · rw [E.fet_iff _ _ (by omega)]; simp [h.ne]
          · subst h
            simp only [Fetched, hrR, ← hE, lt_irrefl, false_and, false_or, true_and, and_true]
            by_cases hij : i' = j
            · subst hij; simp [flip, hbj]
            · simp [flip, Function.update_of_ne hij, hij]
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨t, ht, h1, rfl⟩)
          · exact ⟨snOf C, le_rfl, (hf _ le_rfl).2 (Or.inr ⟨rfl, rfl⟩), (E.hv _ hL.inv.sn_le).symm⟩
          · exact ⟨t, ht, (hf t ht).2 (Or.inl h1), (E.hv _ (ht.trans hL.inv.sn_le)).symm⟩
        · rintro ⟨t, ht, h1, rfl⟩
          rw [E.hv _ (ht.trans hL.inv.sn_le)]
          rcases (hf t ht).1 h1 with h | ⟨rfl, rfl⟩
          · exact Or.inr ⟨t, ht, h, rfl⟩
          · exact Or.inl rfl
      · show RSt _ _ _ _ j
        unfold RSt
        rw [hnew, curOp_append_tau, respL, ObjSpec.respIn_concat_self hst]
        rw [show (auditReg m V v₀).runOps (auditReg m V v₀).init (L.map Prod.snd) = linState L
          from rfl, hδ, hvs, hS]
        left; exact ⟨rfl, by omega⟩
    · have hD : (rOf C).seq = snOf C + 1 := by
        have := hL.inv.sn_le; have := hL.inv.seq_le; omega
      exact ⟨[], Dl ++ [.rd j], by
        simpa using hL.dpush_rd hs hD hl hRm hS hV hB hlocq hnew⟩
  case rCAS prev sn val =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hnew : C'.loc (.rd j) = .rRet (some (sn, val)) val := by simp [hloc]
    have hR : (C'.mem .R : RVal m V) = C.mem .R := by simp [hmem]
    have hV : ∀ t, C'.mem (.V t) = C.mem (.V t) := fun t => by simp [hmem]
    have hB : ∀ t i, C'.mem (.B t i) = C.mem (.B t i) := fun t i => by simp [hmem]
    have hSv : snOf C' = if snOf C = sn - 1 then sn else snOf C := by
      simp [snOf, hmem, casObject]; split_ifs <;> simp_all
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · have hS : snOf C' = snOf C := by rw [hSv]; split_ifs <;> omega
      have hrR : rOf C' = rOf C := hR
      refine ⟨[], Dl, ?_⟩
      rw [List.append_nil]
      refine hL.quiet0 hs (by rw [hrR]) hS (by rw [hrR]) hlin0 hcur hlocq' ?_
          (fun j' hj' hd => ?_) (fun _ h => by cases h)
      · show RSt _ _ _ _ j
        unfold RSt; rw [hnew, curOp_append_tau]; exact h1
      · exfalso
        have hj'' : j' = j := by simpa only [Label.proc, Proc.rd.injEq] using hj'
        subst hj''
        obtain ⟨prev', hl2, -, -⟩ := hL.dl_rd_info hd
        rw [hl] at hl2; obtain ⟨-, rfl, -⟩ := Loc.rCAS.inj hl2
        have := hL.inv.seq_le; have := hL.inv.sn_le
        have hD := ((hL.dl_readers j').1 hd).1
        omega
    · have hS : snOf C' = (rOf C).seq := by rw [hSv, if_pos (by omega)]; exact h3
      obtain rfl := h3
      exact ⟨_, [], (hL.sigma hrun hs h4 hR hV hB hS hpend hlocq
        (Or.inl ⟨j, prev, val, rfl, hl, hnew⟩)).choose_spec⟩

lemma LInv.step_wr (hL : LInv rnd α C L Dl) (hrun : (alg1 rnd v₀).run α = some C) {w : W}
    (hs : (alg1 rnd v₀).step C (.tau (.wr w)) = some C') :
    ∃ M Dl', LInv rnd (α ++ [.tau (.wr w)]) C' (L ++ M) Dl' := by
  obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hlocq : ∀ q, q ≠ Proc.wr w → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hcur : ∀ q, q ≠ (Label.tau (Proc.wr w) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      curOp (α ++ [.tau (.wr w)]) q = curOp α q := fun q _ => curOp_append_tau _ _ _
  have hlocq' : ∀ q, q ≠ (Label.tau (Proc.wr w) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      C'.loc q = C.loc q := hlocq
  have hlin0 : IsLinearization (α ++ [.tau (.wr w)]) L := hL.lin.append_tau _
  have hW := hL.inv.wr w
  unfold WInv at hW
  have hst := hL.wr w
  unfold WSt at hst
  have hrd0 : ∀ j, Proc.rd j = (Label.tau (Proc.wr w) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      Proc.rd j ∈ Dl → ∃ prev sn val, C'.loc (.rd j) = .rCAS prev sn val :=
    fun j h => by cases h
  have hau0 : ∀ a, Proc.au a = (Label.tau (Proc.wr w) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      Proc.au a ∈ Dl → ar (C'.loc (.au a)) = ar (C.loc (.au a)) := fun a h => by cases h
  -- generic finish for steps that keep `R`, `SN` and the writer's sequence number
  have fin : ∀ sn l', (curOp α (.wr w) ∈ L.map Prod.fst ↔ sn ≤ snOf C) →
      C'.loc (.wr w) = l' → wsn l' = some sn →
      (∀ l'', l' ≠ .wSN l'') → l' ≠ .wRet →
      rOf C' = rOf C → snOf C' = snOf C →
      ∃ M Dl', LInv rnd (α ++ [.tau (.wr w)]) C' (L ++ M) Dl' := by
    intro sn l' hold hl' hsn' hn1 hn2 hR hS
    refine ⟨[], Dl, ?_⟩
    rw [List.append_nil]
    refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) hlin0 hcur hlocq' ?_ hrd0 hau0
    show WSt _ _ _ w
    unfold WSt
    rw [hl', curOp_append_tau, hS]
    cases l' <;> simp only [wsn, reduceCtorEq] at hsn' ⊢
    all_goals first
      | exact absurd rfl (hn1 _)
      | exact absurd rfl hn2
      | (intro sn' h; simp only [Option.some.injEq] at h hsn'; rw [← h, hsn']; exact hold)
  cases hl : C.loc (.wr w) <;> rw [hl] at hW hst <;>
    simp only [alg1, writerAct, hl, reduceCtorEq] at hact
  case wSN v =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    have hnew : C'.loc (.wr w) = .wR v (snOf C + 1) := by simp [hloc, snOf]
    refine ⟨[], Dl, ?_⟩
    rw [List.append_nil]
    refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) hlin0 hcur hlocq' ?_ hrd0 hau0
    show WSt _ _ _ w
    unfold WSt
    rw [hnew, curOp_append_tau, hS]
    intro sn' hs'
    simp only [wsn, Option.some.injEq] at hs'
    subst hs'
    exact ⟨fun h => absurd h hst, fun h => by omega⟩
  case wR v sn =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    by_cases hb : sn ≤ (rOf C).seq
    · have hnew : C'.loc (.wr w) = .wHelp sn := by
        have : sn ≤ (C.mem .R : RVal m V).seq := hb
        simp [hloc, this]
      exact fin sn _ (hst sn rfl) hnew rfl (by simp) (by simp) hR hS
    · have hnew : C'.loc (.wr w) = .wV v sn (rOf C) := by
        have : ¬ sn ≤ (C.mem .R : RVal m V).seq := hb
        simp [hloc, this, rOf]
      exact fin sn _ (hst sn rfl) hnew rfl (by simp) (by simp) hR hS
  case wV v sn r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hnew : C'.loc (.wr w) = wBnext v sn r (todoOf rnd r) := by simp [hloc]
    cases htd : todoOf rnd r with
    | nil =>
      rw [htd] at hnew
      exact fin sn _ (hst sn rfl) hnew rfl (by simp [wBnext])
        (by simp [wBnext]) hR hS
    | cons j rest =>
      rw [htd] at hnew
      exact fin sn _ (hst sn rfl) hnew rfl (by simp [wBnext])
        (by simp [wBnext]) hR hS
  case wB v sn r todo =>
    cases todo with
    | nil => simp at hact
    | cons j rest =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      obtain rfl := eq_of_heq ho
      obtain rfl := eq_of_heq hk
      have hR : rOf C' = rOf C := by simp [rOf, hmem]
      have hS : snOf C' = snOf C := by simp [snOf, hmem]
      have hnew : C'.loc (.wr w) = wBnext v sn r rest := by simp [hloc]
      cases rest with
      | nil =>
        exact fin sn _ (hst sn rfl) hnew rfl (by simp [wBnext])
          (by simp [wBnext]) hR hS
      | cons j2 rest2 =>
        exact fin sn _ (hst sn rfl) hnew rfl (by simp [wBnext])
          (by simp [wBnext]) hR hS
  case wCAS v sn r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    by_cases heq : (C.mem .R : RVal m V) = r
    · have hRm : (C'.mem .R : RVal m V) = ⟨sn, v, rnd sn⟩ := by simp [hmem, heq]
      have hS : snOf C' = snOf C := by simp [snOf, hmem]
      have hnew : C'.loc (.wr w) = .wHelp sn := by simp [hloc, heq]
      exact ⟨[], [], by
        simpa using hL.rho hs hl heq hRm hS (fun t => by simp [hmem]) (fun t i => by simp [hmem])
          hpend hlocq hnew⟩
    · have hm : C'.mem = C.mem := by simp [hmem, heq]
      have hR : rOf C' = rOf C := by simp [rOf, hm]
      have hS : snOf C' = snOf C := by simp [snOf, hm]
      have hnew : C'.loc (.wr w) = .wR v sn := by simp [hloc, heq]
      exact fin sn _ (hst sn rfl) hnew rfl (by simp) (by simp) hR hS
  case wHelp sn =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨-, hW2, hW3⟩ := hW
    have hnew : C'.loc (.wr w) = .wRet := by simp [hloc]
    have hR : (C'.mem .R : RVal m V) = C.mem .R := by simp [hmem]
    have hrR : rOf C' = rOf C := hR
    have hSv : snOf C' = if snOf C = sn - 1 then sn else snOf C := by
      simp [snOf, hmem, casObject]; split_ifs <;> simp_all
    have hle := hL.inv.seq_le
    have hle2 := hL.inv.sn_le
    by_cases hc : snOf C = sn - 1
    · have hsq : sn = (rOf C).seq := by omega
      have hD : (rOf C).seq = snOf C + 1 := by omega
      have hS : snOf C' = (rOf C).seq := by rw [hSv, if_pos hc, hsq]
      subst hsq
      exact ⟨_, [], (hL.sigma hrun hs hD hR (fun t => by simp [hmem]) (fun t i => by simp [hmem])
        hS hpend hlocq (Or.inr (Or.inl ⟨w, rfl, hl, hnew⟩))).choose_spec⟩
    · have hS : snOf C' = snOf C := by rw [hSv, if_neg hc]
      refine ⟨[], Dl, ?_⟩
      rw [List.append_nil]
      refine hL.quiet0 hs (by rw [hrR]) hS (by rw [hrR]) hlin0 hcur hlocq' ?_ hrd0 hau0
      show WSt _ _ _ w
      unfold WSt
      rw [hnew, curOp_append_tau]
      exact (hst sn rfl).2 (by omega)

lemma ar_aNext {A : Set (Fin m × V)} {r : RVal m V} {s : ℕ} : ar (aNext rnd A r s) = some r := by
  unfold aNext; split_ifs <;> rfl

lemma ar_aVnext {A : Set (Fin m × V)} {r : RVal m V} {s : ℕ} {val : Option V} :
    ar (aVnext rnd A r s val) = some r := by
  unfold aVnext; split_ifs
  · rfl
  · exact ar_aNext

lemma ar_aBnext {A : Set (Fin m × V)} {r : RVal m V} {s : ℕ} {val : Option V} {j : Fin m} :
    ar (aBnext rnd A r s val j) = some r := by
  unfold aBnext; split_ifs
  · rfl
  · exact ar_aNext

lemma ASt_of_ar {a : Au} (har : ∃ r, ar (C.loc (.au a)) = some r)
    (H : ∀ r, ar (C.loc (.au a)) = some r →
      (respL v₀ L (curOp α (.au a)) = some (.set (Target rnd C r)) ∧ r.seq ≤ snOf C) ∨
      (curOp α (.au a) ∉ L.map Prod.fst ∧ Proc.au a ∈ Dl ∧ r.seq = (rOf C).seq ∧
        (rOf C).seq = snOf C + 1)) :
    ASt (rnd := rnd) α C L Dl a := by
  unfold ASt
  revert har H
  cases C.loc (.au a) <;> simp only [ar, reduceCtorEq, exists_false, IsEmpty.forall_iff,
    false_imp_iff] <;> intro _ H <;> exact H

lemma LInv.step_au (hL : LInv rnd α C L Dl) (hrun : (alg1 rnd v₀).run α = some C) {a : Au}
    (hs : (alg1 rnd v₀).step C (.tau (.au a)) = some C') :
    ∃ M Dl', LInv rnd (α ++ [.tau (.au a)]) C' (L ++ M) Dl' := by
  obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hlocq : ∀ q, q ≠ Proc.au a → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hcur : ∀ q, q ≠ (Label.tau (Proc.au a) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      curOp (α ++ [.tau (.au a)]) q = curOp α q := fun q _ => curOp_append_tau _ _ _
  have hlocq' : ∀ q, q ≠ (Label.tau (Proc.au a) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      C'.loc q = C.loc q := hlocq
  have hlin0 : IsLinearization (α ++ [.tau (.au a)]) L := hL.lin.append_tau _
  have hA := hL.inv.au a
  unfold AInv at hA
  have hst := hL.au a
  unfold ASt at hst
  have hrd0 : ∀ j, Proc.rd j = (Label.tau (Proc.au a) : Label (Proc m W Au) (auditReg m V v₀)).proc →
      Proc.rd j ∈ Dl → ∃ prev sn val, C'.loc (.rd j) = .rCAS prev sn val :=
    fun j h => by cases h
  cases hl : C.loc (.au a) <;> rw [hl] at hA hst <;>
    simp only [alg1, auditorAct, hl, reduceCtorEq] at hact
  case aR A lsa =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    have hnew : C'.loc (.au a) = aNext rnd A (rOf C) lsa := by simp [hloc, rOf]
    have hnar : ar (C'.loc (.au a)) = some (rOf C) := by rw [hnew]; exact ar_aNext
    by_cases hE : (rOf C).seq = snOf C
    · obtain ⟨hp1, -, -⟩ := hA
      have hop := Impl.run_pend_curOp hrun hp1
      have hlin : IsLinearization (α ++ [.tau (.au a)])
          (L ++ [(curOp α (.au a), (AOp.audit : AOp m V))]) :=
        hlin0.push (by rw [opOf_append_tau]; exact hop.2.2) hst
          (by rw [completed_append_tau]; exact hop.2.1)
      have hhv : hv v₀ C' = hv v₀ C := by funext t; unfold AuditingWithoutLeaks.hv rOf; rw [hm]
      have hP : Pairs rnd C' = Pairs rnd C := by funext n; simp [Pairs, Fetched, rOf, hm, hhv]
      have hT : Target rnd C' (rOf C) = Pairs rnd C (snOf C) := by
        have hTT : Target rnd C' (rOf C) = Target rnd C (rOf C) := by
          simp [Target, Fetched, rOf, hm, hhv]
        rw [hTT]
        ext ⟨i', u⟩
        simp only [Target, Pairs, Set.mem_ofPred_eq, readersOf]
        constructor
        · rintro (⟨t, ht, hf, rfl⟩ | ⟨h1, rfl⟩)
          · exact ⟨t, by omega, hf, rfl⟩
          · exact ⟨(rOf C).seq, by omega, Or.inr ⟨rfl, h1⟩, by simp [AuditingWithoutLeaks.hv]⟩
        · rintro ⟨t, ht, hf, rfl⟩
          rcases Nat.lt_or_eq_of_le (show t ≤ (rOf C).seq by omega) with h | h
          · exact Or.inl ⟨t, h, hf, rfl⟩
          · subst h
            rcases hf with ⟨h, -⟩ | ⟨-, hb⟩
            · omega
            · exact Or.inr ⟨hb, by simp [AuditingWithoutLeaks.hv]⟩
      have hδ : (auditReg m V v₀).δ (linState L) .audit =
          (linState L, .set (Pairs rnd C (snOf C))) := by rw [hL.abs]
      have haD : Proc.au a ∉ Dl := by rw [hL.dl_E hE]; simp
      refine ⟨[(curOp α (.au a), (AOp.audit : AOp m V))], Dl,
        hL.quiet hs (by rw [hR]) hS (fun _ => by rw [hR]) hlin ?_ hcur
          (fun q hq => by simp only [List.map_cons, List.map_nil, List.mem_singleton]; exact curOp_ne hq) hlocq' ?_ hrd0
          (fun a' ha' h => by simp only [Label.proc, Proc.au.injEq] at ha'; subst ha'; exact absurd h haD)⟩
      · rw [linState_concat, hδ, hL.abs, hhv, hP, hS]
      · show ASt _ _ _ _ a
        refine ASt_of_ar ⟨_, hnar⟩ fun r hr => ?_
        rw [hnar] at hr; cases hr
        rw [curOp_append_tau, respL, ObjSpec.respIn_concat_self hst]
        rw [show (auditReg m V v₀).runOps (auditReg m V v₀).init (L.map Prod.snd) = linState L
          from rfl, hδ, hT, hS]
        exact Or.inl ⟨rfl, by omega⟩
    · have hD : (rOf C).seq = snOf C + 1 := by
        have := hL.inv.sn_le; have := hL.inv.seq_le; omega
      exact ⟨[], Dl ++ [.au a], by simpa using hL.dpush_au hs hD hl hm hlocq hnar⟩
  case aCAS A r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hnew : C'.loc (.au a) = .aRet A r.seq := by simp [hloc]
    have hR : (C'.mem .R : RVal m V) = C.mem .R := by simp [hmem]
    have hrR : rOf C' = rOf C := hR
    have hSv : snOf C' = if snOf C = r.seq - 1 then r.seq else snOf C := by
      simp [snOf, hmem, casObject]; split_ifs <;> simp_all
    rcases hst r rfl with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · have hS : snOf C' = snOf C := by rw [hSv]; split_ifs <;> omega
      have haD : Proc.au a ∉ Dl := by
        intro h
        obtain ⟨r', hr', hrs⟩ := hL.dl_au a h
        rw [hl] at hr'; simp only [ar, Option.some.injEq] at hr'; subst hr'
        have hD : (rOf C).seq = snOf C + 1 := by
          by_contra hc
          have := hL.inv.sn_le; have := hL.inv.seq_le
          rw [hL.dl_E (by omega)] at h; cases h
        omega
      refine ⟨[], Dl, ?_⟩
      rw [List.append_nil]
      refine hL.quiet0 hs (by rw [hrR]) hS (by rw [hrR]) hlin0 hcur hlocq' ?_ hrd0
        (fun a' ha' h => by simp only [Label.proc, Proc.au.injEq] at ha'; subst ha'; exact absurd h haD)
      show ASt _ _ _ _ a
      unfold ASt
      rw [hnew, curOp_append_tau, hA.2.2]; exact h1
    · have hS : snOf C' = (rOf C).seq := by rw [hSv, if_pos (by omega)]; exact h3
      exact ⟨_, [], (hL.sigma hrun hs h4 hR (fun t => by simp [hmem]) (fun t i => by simp [hmem])
        hS hpend hlocq (Or.inr (Or.inr ⟨a, A, r, rfl, hl, h3, hnew⟩))).choose_spec⟩
  all_goals
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    have hhv : hv v₀ C' = hv v₀ C := by funext t; unfold AuditingWithoutLeaks.hv rOf; rw [hm]
    have hTT : ∀ r, Target rnd C' r = Target rnd C r := by
      intro r; simp [Target, Fetched, rOf, hm, hhv]
  case aV A r s =>
    have hnew : ar (C'.loc (.au a)) = some r := by simp [hloc, ar_aVnext]
    refine ⟨[], Dl, ?_⟩
    rw [List.append_nil]
    refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) hlin0 hcur hlocq' ?_ hrd0
      (fun a' ha' h => by simp only [Label.proc, Proc.au.injEq] at ha'; subst ha'; rw [hnew, hl]; rfl)
    show ASt _ _ _ _ a
    refine ASt_of_ar ⟨_, hnew⟩ fun r' hr' => ?_
    rw [hnew] at hr'; cases hr'
    rw [curOp_append_tau, hTT, hS, hR]; exact hst r rfl
  case aB A r s val j =>
    have hnew : ar (C'.loc (.au a)) = some r := by simp [hloc, ar_aBnext]
    refine ⟨[], Dl, ?_⟩
    rw [List.append_nil]
    refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) hlin0 hcur hlocq' ?_ hrd0
      (fun a' ha' h => by simp only [Label.proc, Proc.au.injEq] at ha'; subst ha'; rw [hnew, hl]; rfl)
    show ASt _ _ _ _ a
    refine ASt_of_ar ⟨_, hnew⟩ fun r' hr' => ?_
    rw [hnew] at hr'; cases hr'
    rw [curOp_append_tau, hTT, hS, hR]; exact hst r rfl

lemma LInv.step_inv (hL : LInv rnd α C L Dl) (hrun : (alg1 rnd v₀).run α = some C)
    {p : Proc m W Au} {o : (auditReg m V v₀).Op}
    (hs : (alg1 rnd v₀).step C (.inv p o) = some C') :
    LInv rnd (α ++ [.inv p o]) C' L Dl := by
  obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hR : rOf C' = rOf C := by simp [rOf, hmem]
  have hS : snOf C' = snOf C := by simp [snOf, hmem]
  have hni : curOp α p ∉ L.map Prod.fst := fun h =>
    (alg1 rnd v₀).not_invoked_curOp_of_idle hrun h0 (hL.lin.invoked_of_mem h)
  have hcur : ∀ q, curOp (α ++ [.inv p o]) q = curOp α q := fun q => curOp_append_inv _ _ _ _
  have hlocq : ∀ q, q ≠ (Label.inv p o).proc → C'.loc q = C.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne (show q ≠ p from hq)]
  refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) (hL.lin.append_inv p o) (fun q _ => hcur q)
    hlocq ?_ ?_ ?_
  · cases p with
    | rd j =>
      obtain ⟨prev, hl, -⟩ := (hL.inv.rd j).idle h0
      show RSt _ _ _ _ j
      unfold RSt
      rw [hcur, hloc, Function.update_self, hl]
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      exact hni
    | wr w =>
      have hl := (hL.inv.wr w).idle h0
      show WSt _ _ _ w
      unfold WSt
      rw [hcur, hloc, Function.update_self, hl]
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      exact hni
    | au a =>
      obtain ⟨A, lsa, hl, -⟩ := (hL.inv.au a).idle h0
      show ASt _ _ _ _ a
      unfold ASt
      rw [hcur, hloc, Function.update_self, hl]
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      exact hni
  · intro j hj hd
    simp only [Label.proc] at hj; subst hj
    obtain ⟨prev, hl, -⟩ := (hL.inv.rd j).idle h0
    obtain ⟨_, _, _, hl'⟩ := hL.dl_rd j hd
    rw [hl] at hl'; cases hl'
  · intro a ha hd
    simp only [Label.proc] at ha; subst ha
    obtain ⟨A, lsa, hl, -⟩ := (hL.inv.au a).idle h0
    obtain ⟨r, hr, -⟩ := hL.dl_au a hd
    rw [hl] at hr; simp [ar] at hr

lemma LInv.step_ret (hL : LInv rnd α C L Dl) (hrun : (alg1 rnd v₀).run α = some C)
    {p : Proc m W Au} {r : (auditReg m V v₀).Resp}
    (hs : (alg1 rnd v₀).step C (.ret p r) = some C') :
    LInv rnd (α ++ [.ret p r]) C' L Dl := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  have hR : rOf C' = rOf C := by simp [rOf, hmem]
  have hS : snOf C' = snOf C := by simp [snOf, hmem]
  have hcur : ∀ q, q ≠ (Label.ret p r : Label (Proc m W Au) (auditReg m V v₀)).proc →
      curOp (α ++ [.ret p r]) q = curOp α q := fun q hq => curOp_append_ret_of_ne _ _ (Ne.symm hq)
  have hlocq : ∀ q, q ≠ (Label.ret p r : Label (Proc m W Au) (auditReg m V v₀)).proc →
      C'.loc q = C.loc q := fun q hq => by rw [hloc, Function.update_of_ne (show q ≠ p from hq)]
  have hlinOf : respL v₀ L (curOp α p) = some r → IsLinearization (α ++ [.ret p r]) L :=
    fun h => hL.lin.append_ret_of_respIn (by simpa [curOp] using h)
  cases p with
  | rd j =>
    obtain ⟨-, hr⟩ := hL.inv.rd j
    have hst := hL.rd j
    unfold RSt at hst
    cases hl : C.loc (.rd j) <;> rw [hl] at hst hr <;>
      simp only [alg1, readerAct, hl, reduceCtorEq, Action.ret.injEq] at hact
    case rRet prev val =>
      obtain ⟨rfl, rfl⟩ := hact
      refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) (hlinOf hst) hcur hlocq ?_ ?_ ?_
      · show RSt _ _ _ _ j; unfold RSt; rw [hloc, Function.update_self]; trivial
      · intro j' hj' hd
        simp only [Label.proc, Proc.rd.injEq] at hj'; subst hj'
        obtain ⟨_, _, _, h'⟩ := hL.dl_rd _ hd; rw [hl] at h'; cases h'
      · intro a ha; cases ha
    case rIdle prev => exact absurd hr.1 h0
    all_goals simp at hr
  | wr w =>
    have hW := hL.inv.wr w
    unfold WInv at hW
    have hst := hL.wr w
    unfold WSt at hst
    cases hl : C.loc (.wr w) <;> rw [hl] at hst hW <;>
      simp only [alg1, writerAct, hl, reduceCtorEq, Action.ret.injEq] at hact
    case wRet =>
      obtain ⟨rfl, rfl⟩ := hact
      obtain ⟨v, hv⟩ := hW
      have hresp : respL v₀ L (curOp α (.wr w)) = some .ack :=
        respL_of_write hst fun y hy hyx => ⟨v, by
          have h1 := hL.lin.op_eq y hy
          rw [hyx, (Impl.run_pend_curOp hrun hv).2.2] at h1
          exact (Option.some.inj h1).symm⟩
      refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) (hlinOf hresp) hcur hlocq ?_
        (fun j h => by cases h) (fun a h => by cases h)
      show WSt _ _ _ w; unfold WSt; rw [hloc, Function.update_self]
      intro sn h; simp [wsn] at h
    case wIdle => exact absurd hW h0
    case wB v sn r' todo =>
      cases todo with
      | nil => exact absurd rfl hW.2.2.2.1
      | cons j rest => simp at hact
    all_goals simp at hW
  | au a =>
    have hA := hL.inv.au a
    unfold AInv at hA
    have hst := hL.au a
    unfold ASt at hst
    cases hl : C.loc (.au a) <;> rw [hl] at hst hA <;>
      simp only [alg1, auditorAct, hl, reduceCtorEq, Action.ret.injEq] at hact
    case aRet A lsa =>
      obtain ⟨rfl, rfl⟩ := hact
      refine hL.quiet0 hs (by rw [hR]) hS (by rw [hR]) (hlinOf hst) hcur hlocq ?_
        (fun j h => by cases h) ?_
      · show ASt _ _ _ _ a; unfold ASt; rw [hloc, Function.update_self]
        intro r' h; simp [ar] at h
      · intro a' ha' hd
        simp only [Label.proc, Proc.au.injEq] at ha'; subst ha'
        obtain ⟨r', hr', -⟩ := hL.dl_au _ hd; rw [hl] at hr'; simp [ar] at hr'
    case aIdle A lsa => exact absurd hA.1 h0
    all_goals simp at hA

theorem LInv.step (hL : LInv rnd α C L Dl) (hrun : (alg1 rnd v₀).run α = some C)
    {ℓ : Label (Proc m W Au) (auditReg m V v₀)} (hs : (alg1 rnd v₀).step C ℓ = some C') :
    ∃ M Dl', LInv rnd (α ++ [ℓ]) C' (L ++ M) Dl' := by
  cases ℓ with
  | inv p o => exact ⟨[], Dl, by simpa using hL.step_inv hrun hs⟩
  | ret p r => exact ⟨[], Dl, by simpa using hL.step_ret hrun hs⟩
  | tau p =>
    cases p with
    | rd j => exact hL.step_rd hrun hs
    | wr w => exact hL.step_wr hrun hs
    | au a => exact hL.step_au hrun hs

end Steps

end Podc.AuditingWithoutLeaks

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

lemma LInv.init : LInv rnd ([] : List (Label (Proc m W Au) (auditReg m V v₀)))
    (alg1 rnd v₀).initCfg [] [] := by
  refine ⟨Inv.init, DInv2.init, BInv.init, isLinearization_nil, ?_, fun j => ?_, fun w => ?_,
    fun a => ?_, List.nodup_nil, fun _ => rfl, by simp, by simp, by simp, fun i => ?_, by simp⟩
  · have h0 : linState ([] : List (OpId (Proc m W Au) × (auditReg m V v₀).Op)) =
        ((v₀, ∅) : V × Set (Fin m × V)) := rfl
    rw [h0]
    refine Prod.ext ?_ ?_
    · simp [AuditingWithoutLeaks.hv, rOf, snOf, Impl.initCfg, alg1]
    · ext x
      simp [Pairs, Fetched, rOf, snOf, Impl.initCfg, alg1]
  · simp [RSt, Impl.initCfg, alg1, locInit]
  · simp [WSt, Impl.initCfg, alg1, locInit, wsn]
  · simp [ASt, Impl.initCfg, alg1, locInit, ar]
  · simp [rOf, snOf, Impl.initCfg, alg1]

/-- The forward simulation of Algorithm 1 by the atomic auditable register. -/
theorem alg1_linSim :
    (alg1 (W := W) (Au := Au) rnd v₀).LinSim (fun α C L => ∃ Dl, LInv rnd α C L Dl) where
  init := ⟨[], LInv.init⟩
  step := by
    rintro α C L ℓ C' hrun ⟨Dl, hL⟩ hs
    obtain ⟨M, Dl', h⟩ := hL.step hrun hs
    exact ⟨M, Dl', h⟩
  lin := by
    rintro α C L - ⟨Dl, hL⟩
    exact hL.lin

/-- **Theorem 8 (linearizability).** Algorithm 1 is a linearizable implementation of an
auditable multi-writer, multi-reader register; in fact it is strongly linearizable. -/
theorem alg1_stronglyLinearizable : (alg1 (W := W) (Au := Au) rnd v₀).StronglyLinearizable :=
  Impl.stronglyLinearizable_of_linSim _ _ alg1_linSim

/-- **Theorem 8 (linearizability).** -/
theorem alg1_linearizable : (alg1 (W := W) (Au := Au) rnd v₀).Linearizable :=
  alg1_stronglyLinearizable.linearizable

end Podc.AuditingWithoutLeaks
