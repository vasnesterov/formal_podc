import Podc.Computability.Distributed.SharedMemory.WriteStrongLin
import Cslib.Computability.Distributed.SharedMemory.SWMRRegister

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/MWMRRegister.lean

/-!
# A linearizability criterion for multi-writer registers

The multi-writer analogue of `SWMRReadsFrom` (`SWMRRegister.lean`). For a history `α` of
`register V v₀`, linearizability follows from

* a *write order* `ws : List (OpId P)`: distinct invoked writes, containing every completed write
  (pending writes may be included), and
* a *reads-from* map `rf : OpId P → ℕ` on the completed reads: `rf x = 0` means that read `x`
  returns the initial value `v₀`, `rf x = m + 1` that it returns the value of the write `ws[m]`,

subject to the real-time conditions (`MWMRReadsFrom`):

* `ww`: if `ws[i]` precedes `ws[j]` then `i < j`;
* `wr`: if `ws[i]` precedes a completed read `x` then `i < rf x` (no overwritten value is read);
* `rw`: if a completed read `x` precedes `ws[i]` then `rf x ≤ i` (no value from the future);
* `rr`: if a completed read `x` precedes a completed read `y` then `rf x ≤ rf y` (no new–old
  inversion).

**Main statement** (`MWMRReadsFrom.isLinearization`): `mwmrLin α ws rf` — the writes in the order
`ws`, every completed read right after the write it reads from (reads from the same write in
invocation order) — is a linearization of `α`. Its writes are exactly `ws`
(`opsFor_mwmrLin`), which is what write strong-linearizability proofs need.
-/

namespace Cslib.SharedMemory

open List

variable {P : Type} [DecidableEq P] {V : Type} {v₀ : V}

/-- The value written by the `m`-th write of `ws` (1-based); `v₀` for `m = 0`. -/
def wsVal (α : List (Label P (register V v₀))) (ws : List (OpId P)) : ℕ → V
  | 0 => v₀
  | m + 1 => match ws[m]?.bind (opOf α) with
    | some (.write v) => v
    | _ => v₀

/-- The operation of an invoked instance (`read` if not invoked). -/
def opOrRead (α : List (Label P (register V v₀))) (x : OpId P) : RWOp V :=
  (opOf α x).getD .read

open Classical in
/-- The completed reads that read from write `m` (`m = 0`: the initial value), in invocation
order. -/
noncomputable def mwmrReads (α : List (Label P (register V v₀))) (rf : OpId P → ℕ) (m : ℕ) :
    List (OpId P × RWOp V) :=
  ((invIds α).filter (fun x => decide (opOf α x = some .read ∧ Completed α x ∧ rf x = m))).map
    (fun x => (x, RWOp.read))

/-- The first `j` writes of `ws`, each followed by the reads that read from it (preceded by the
reads from the initial value). -/
noncomputable def mwmrLinAux (α : List (Label P (register V v₀))) (ws : List (OpId P))
    (rf : OpId P → ℕ) : ℕ → List (OpId P × RWOp V)
  | 0 => mwmrReads α rf 0
  | j + 1 => mwmrLinAux α ws rf j ++
      ((ws[j]?.map (fun x => (x, opOrRead α x))).toList ++ mwmrReads α rf (j + 1))

/-- The reads-from linearization of `α`. -/
noncomputable def mwmrLin (α : List (Label P (register V v₀))) (ws : List (OpId P))
    (rf : OpId P → ℕ) : List (OpId P × RWOp V) :=
  mwmrLinAux α ws rf ws.length

/-- Hypotheses of the MWMR reads-from criterion (see the module docstring). -/
structure MWMRReadsFrom (α : List (Label P (register V v₀))) (ws : List (OpId P))
    (rf : OpId P → ℕ) : Prop where
  wellFormed : WellFormed α
  nodup : ws.Nodup
  ws_write : ∀ x ∈ ws, ∃ v, opOf α x = some (.write v)
  complete : ∀ x v, opOf α x = some (.write v) → Completed α x → x ∈ ws
  write_resp : ∀ x v r, opOf α x = some (.write v) → respOf α x = some r → r = v
  read_le : ∀ x, opOf α x = some .read → Completed α x → rf x ≤ ws.length
  read_val : ∀ x, opOf α x = some .read → Completed α x → respOf α x = some (wsVal α ws (rf x))
  ww : ∀ i j (hi : i < ws.length) (hj : j < ws.length), Precedes α ws[i] ws[j] → i < j
  wr : ∀ i (hi : i < ws.length) x, opOf α x = some .read → Completed α x →
    Precedes α ws[i] x → i < rf x
  rw : ∀ x i (hi : i < ws.length), opOf α x = some .read → Completed α x →
    Precedes α x ws[i] → rf x ≤ i
  rr : ∀ x y, opOf α x = some .read → Completed α x → opOf α y = some .read → Completed α y →
    Precedes α x y → rf x ≤ rf y

/-! ## Proof of the criterion -/

section Proof

variable {A : ObjSpec}

/-- Sort key: the write `ws[j]` gets `2 j + 1`, every other instance `x` gets `2 rf(x)`. -/
def mwmrKey (ws : List (OpId P)) (rf : OpId P → ℕ) (x : OpId P) : ℕ :=
  if x ∈ ws then 2 * ws.idxOf x + 1 else 2 * rf x

/-- The strict order used to show that the linearization respects real time: smaller key, or the
same key and earlier invocation. -/
def mwmrBefore (α : List (Label P A)) (ws : List (OpId P)) (rf : OpId P → ℕ)
    (x y : OpId P) : Prop :=
  mwmrKey ws rf x < mwmrKey ws rf y ∨
    (mwmrKey ws rf x = mwmrKey ws rf y ∧ x ≠ y ∧ [x, y].Sublist (invIds α))

lemma mwmrKey_getElem {ws : List (OpId P)} (hnd : ws.Nodup) (rf : OpId P → ℕ) {i : ℕ}
    (hi : i < ws.length) : mwmrKey ws rf ws[i] = 2 * i + 1 := by
  simp [mwmrKey, List.getElem_mem, hnd.idxOf_getElem]

lemma mwmrKey_of_not_mem {ws : List (OpId P)} (rf : OpId P → ℕ) {x : OpId P} (hx : x ∉ ws) :
    mwmrKey ws rf x = 2 * rf x := by
  simp [mwmrKey, hx]

lemma mem_mwmrReads {α : List (Label P (register V v₀))} {rf : OpId P → ℕ} {m : ℕ}
    {y : OpId P × RWOp V} :
    y ∈ mwmrReads α rf m ↔
      ∃ x, opOf α x = some .read ∧ Completed α x ∧ rf x = m ∧ y = (x, .read) := by
  simp only [mwmrReads, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_invIds]
  constructor
  · rintro ⟨x, ⟨-, h1, h2, h3⟩, rfl⟩; exact ⟨x, h1, h2, h3, rfl⟩
  · rintro ⟨x, h1, h2, h3, rfl⟩; exact ⟨x, ⟨Invoked.of_opOf_eq_some h1, h1, h2, h3⟩, rfl⟩

lemma mem_wsEntry {α : List (Label P (register V v₀))} {ws : List (OpId P)} {j : ℕ}
    {y : OpId P × RWOp V} :
    y ∈ (ws[j]?.map (fun x => (x, opOrRead α x))).toList ↔
      ∃ hj : j < ws.length, y = (ws[j], opOrRead α ws[j]) := by
  rcases Nat.lt_or_ge j ws.length with hj | hj
  · simp [hj]
  · simp [not_lt.2 hj]

lemma mem_mwmrLinAux {α : List (Label P (register V v₀))} {ws : List (OpId P)}
    {rf : OpId P → ℕ} (j : ℕ) {y : OpId P × RWOp V} :
    y ∈ mwmrLinAux α ws rf j ↔
      (∃ i, ∃ hi : i < ws.length, i < j ∧ y = (ws[i], opOrRead α ws[i])) ∨
        (∃ x, opOf α x = some .read ∧ Completed α x ∧ rf x ≤ j ∧ y = (x, .read)) := by
  induction j with
  | zero =>
    simp only [mwmrLinAux, mem_mwmrReads, Nat.not_lt_zero, false_and, exists_false,
      false_or, Nat.le_zero]
  | succ j ih =>
    simp only [mwmrLinAux, List.mem_append, ih, mem_wsEntry, mem_mwmrReads]
    constructor
    · rintro ((⟨i, hi, hij, rfl⟩ | ⟨x, h0, h1, h2, rfl⟩) | ⟨hj, rfl⟩ | ⟨x, h0, h1, h2, rfl⟩)
      · exact Or.inl ⟨i, hi, by omega, rfl⟩
      · exact Or.inr ⟨x, h0, h1, by omega, rfl⟩
      · exact Or.inl ⟨j, hj, by omega, rfl⟩
      · exact Or.inr ⟨x, h0, h1, by omega, rfl⟩
    · rintro (⟨i, hi, hij, rfl⟩ | ⟨x, h0, h1, h2, rfl⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
        · exact Or.inl (Or.inl ⟨i, hi, hij, rfl⟩)
        · exact Or.inr (Or.inl ⟨hi, rfl⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h2) with h' | h'
        · exact Or.inl (Or.inr ⟨x, h0, h1, by omega, rfl⟩)
        · exact Or.inr (Or.inr ⟨x, h0, h1, h', rfl⟩)

variable {α : List (Label P (register V v₀))} {ws : List (OpId P)} {rf : OpId P → ℕ}

lemma pairwise_mwmrReads (hr : ∀ x, opOf α x = some .read → x ∉ ws) (m : ℕ) :
    (mwmrReads α rf m).Pairwise (fun y z => mwmrBefore α ws rf y.1 z.1) := by
  unfold mwmrReads
  rw [List.pairwise_map]
  refine (((pairwise_sublist_self (invIds α)).sublist List.filter_sublist).and
    ((nodup_invIds α).filter _)).imp_of_mem ?_
  intro a b ha hb hab
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  right
  refine ⟨?_, hab.2, hab.1⟩
  rw [mwmrKey_of_not_mem rf (hr a ha.2.1), mwmrKey_of_not_mem rf (hr b hb.2.1), ha.2.2.2,
    hb.2.2.2]

lemma mwmrKey_le_of_mem (hnd : ws.Nodup) (hr : ∀ x, opOf α x = some .read → x ∉ ws) {j : ℕ}
    {y : OpId P × RWOp V} (hy : y ∈ mwmrLinAux α ws rf j) : mwmrKey ws rf y.1 ≤ 2 * j := by
  rcases (mem_mwmrLinAux j).1 hy with ⟨i, hi, hij, rfl⟩ | ⟨x, hx, -, hk, rfl⟩
  · rw [mwmrKey_getElem hnd rf hi]; omega
  · rw [mwmrKey_of_not_mem rf (hr x hx)]; omega

lemma pairwise_mwmrLinAux (hnd : ws.Nodup) (hr : ∀ x, opOf α x = some .read → x ∉ ws)
    (j : ℕ) : (mwmrLinAux α ws rf j).Pairwise (fun y z => mwmrBefore α ws rf y.1 z.1) := by
  induction j with
  | zero => exact pairwise_mwmrReads hr 0
  | succ j ih =>
    have hW : ∀ y ∈ (ws[j]?.map (fun x => (x, opOrRead α x))).toList,
        mwmrKey ws rf y.1 = 2 * j + 1 := by
      intro y hy
      obtain ⟨hj, rfl⟩ := mem_wsEntry.1 hy
      exact mwmrKey_getElem hnd rf hj
    have hR : ∀ y ∈ mwmrReads α rf (j + 1), mwmrKey ws rf y.1 = 2 * (j + 1) := by
      intro y hy
      obtain ⟨x, hx, -, hk, rfl⟩ := mem_mwmrReads.1 hy
      rw [mwmrKey_of_not_mem rf (hr x hx), hk]
    simp only [mwmrLinAux]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨ih, ⟨?_, pairwise_mwmrReads hr _, ?_⟩, ?_⟩
    · cases ws[j]? <;> simp
    · intro y hy z hz; left; rw [hW y hy, hR z hz]; omega
    · intro y hy z hz
      left
      have := mwmrKey_le_of_mem hnd hr hy
      rcases List.mem_append.1 hz with hz | hz
      · rw [hW z hz]; omega
      · rw [hR z hz]; omega

lemma wsVal_succ (hws : ∀ x ∈ ws, ∃ v, opOf α x = some (.write v)) {j : ℕ}
    (hj : j < ws.length) :
    ((register V v₀).δ (wsVal α ws j) (opOrRead α ws[j])).1 = wsVal α ws (j + 1) := by
  obtain ⟨v, hv⟩ := hws _ (List.getElem_mem hj)
  simp [opOrRead, hv, wsVal, List.getElem?_eq_getElem hj]

/-- State reached by the first `j` writes of the reads-from linearization. -/
lemma runOps_mwmrLinAux (hws : ∀ x ∈ ws, ∃ v, opOf α x = some (.write v)) {j : ℕ}
    (hj : j ≤ ws.length) :
    (register V v₀).runOps v₀ ((mwmrLinAux α ws rf j).map Prod.snd) = wsVal α ws j := by
  have hreads : ∀ m q,
      (register V v₀).runOps q ((mwmrReads α rf m).map Prod.snd) = q :=
    fun m q => ObjSpec.runOps_of_readOnly _ _ _ (by
      intro o ho
      simp only [mwmrReads, List.map_map, List.mem_map] at ho
      obtain ⟨_, _, rfl⟩ := ho
      intro q; rfl)
  induction j with
  | zero => simp [mwmrLinAux, hreads, wsVal]
  | succ j ih =>
    have hj' : j < ws.length := by omega
    rw [mwmrLinAux, List.map_append, ObjSpec.runOps_append, ih (by omega), List.map_append,
      ObjSpec.runOps_append, hreads, List.getElem?_eq_getElem hj', ← wsVal_succ hws hj']
    rfl

lemma seqOK_mwmrReads {m : ℕ} {q : V}
    (h : ∀ x, opOf α x = some .read → Completed α x → rf x = m → respOf α x = some q) :
    SeqOK α q (mwmrReads α rf m) := by
  unfold mwmrReads
  generalize hl : List.filter _ (invIds α) = l
  have hl' : ∀ x ∈ l, opOf α x = some .read ∧ Completed α x ∧ rf x = m := by
    intro x hx; rw [← hl] at hx; simpa using (List.mem_filter.1 hx).2
  clear hl
  induction l with
  | nil => trivial
  | cons x l ih =>
    refine ⟨?_, ih (fun x' hx' => hl' x' (by simp [hx']))⟩
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hl' x (by simp)
    rw [h x h1 h2 h3] at hr; cases hr; rfl

end Proof

/-- **Reads-from criterion for MWMR registers.** -/
theorem MWMRReadsFrom.isLinearization {α : List (Label P (register V v₀))} {ws : List (OpId P)}
    {rf : OpId P → ℕ} (h : MWMRReadsFrom α ws rf) : IsLinearization α (mwmrLin α ws rf) := by
  have hα := h.wellFormed
  have hnd := h.nodup
  have hr : ∀ x, opOf α x = some .read → x ∉ ws := by
    intro x hx hxw
    obtain ⟨v, hv⟩ := h.ws_write x hxw
    rw [hx] at hv; cases hv
  have hL : mwmrLin α ws rf = mwmrLinAux α ws rf ws.length := rfl
  rw [hL]
  have hmem := fun y => mem_mwmrLinAux (α := α) (ws := ws) (rf := rf) ws.length (y := y)
  have hpw := pairwise_mwmrLinAux (rf := rf) hnd hr ws.length
  have hop : ∀ x, Invoked α x → opOf α x = some .read ∨ ∃ v, opOf α x = some (.write v) := by
    intro x hx
    obtain ⟨o, ho⟩ : ∃ o, opOf α x = some o := ⟨_, List.getElem?_eq_getElem hx⟩
    cases o with
    | read => exact Or.inl ho
    | write v => exact Or.inr ⟨v, ho⟩
  have hcomplete : ∀ a, Completed α a → a ∈ (mwmrLinAux α ws rf ws.length).map Prod.fst := by
    intro a ha
    rcases hop a (hα.invoked_of_completed ha) with hrd | ⟨v, hv⟩
    · exact List.mem_map.2 ⟨(a, .read),
        (hmem _).2 (Or.inr ⟨a, hrd, ha, h.read_le a hrd ha, rfl⟩), rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (h.complete a v hv ha)
      exact List.mem_map.2 ⟨_, (hmem _).2 (Or.inl ⟨i, hi, hi, rfl⟩), rfl⟩
  refine ⟨?_, ?_, hcomplete, ?_, ?_⟩
  · -- nodup
    refine (List.pairwise_map.2 hpw).imp ?_
    intro x y hxy heq; subst heq
    rcases hxy with hxy | ⟨-, hne, -⟩
    · exact lt_irrefl _ hxy
    · exact hne rfl
  · -- operations
    intro y hy
    rcases (hmem y).1 hy with ⟨i, hi, -, rfl⟩ | ⟨x, hx, -, -, rfl⟩
    · obtain ⟨v, hv⟩ := h.ws_write _ (List.getElem_mem hi)
      simp [opOrRead, hv]
    · exact hx
  · -- real time
    intro a b hab hb
    have ha := hcomplete a hab.completed
    have hac := hab.completed
    have hbefore : mwmrBefore α ws rf a b := by
      obtain ⟨yb, hyb, rfl⟩ := List.mem_map.1 hb
      rcases (hmem yb).1 hyb with ⟨j, hj, -, rfl⟩ | ⟨x, hx, hxc, -, rfl⟩
      · -- `b` is the write `ws[j]`
        left
        simp only
        rw [mwmrKey_getElem hnd rf hj]
        rcases hop a (hα.invoked_of_completed hac) with hrd | ⟨v, hv⟩
        · rw [mwmrKey_of_not_mem rf (hr a hrd)]
          have := h.rw a j hj hrd hac hab; omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (h.complete a v hv hac)
          rw [mwmrKey_getElem hnd rf hi]
          have := h.ww i j hi hj hab; omega
      · -- `b` is the read `x`
        simp only
        have hkx := mwmrKey_of_not_mem rf (hr x hx)
        rcases hop a (hα.invoked_of_completed hac) with hrd | ⟨v, hv⟩
        · have hm := h.rr a x hrd hac hx hxc hab
          have hka := mwmrKey_of_not_mem rf (hr a hrd)
          have hsub := hab.sublist_invIds (Invoked.of_opOf_eq_some hx) hα
          rcases Nat.lt_or_ge (rf a) (rf x) with hlt | hge
          · left; rw [hka, hkx]; omega
          · right
            refine ⟨by rw [hka, hkx]; omega, ?_, hsub⟩
            rintro rfl
            exact (List.nodup_cons.1 ((nodup_invIds α).sublist hsub)).1 (by simp)
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (h.complete a v hv hac)
          left
          rw [mwmrKey_getElem hnd rf hi, hkx]
          have := h.wr i hi x hx hxc hab; omega
    refine sublist_pair_of_pairwise (List.pairwise_map.2 hpw) ha hb hbefore ?_
    intro h'
    rcases hbefore with h1 | ⟨h1, -, h2⟩ <;> rcases h' with h3 | ⟨h3, -, h4⟩
    · omega
    · omega
    · omega
    · exact not_sublist_pair_both (nodup_invIds α) h2 h4
  · -- legality
    have hreads : ∀ m, SeqOK α (wsVal α ws m) (mwmrReads α rf m) := by
      intro m
      apply seqOK_mwmrReads
      intro x hx hc hxm
      rw [h.read_val x hx hc, hxm]
    suffices ∀ j ≤ ws.length, SeqOK α v₀ (mwmrLinAux α ws rf j) from this _ le_rfl
    intro j hj
    induction j with
    | zero => exact hreads 0
    | succ j ih =>
      have hj' : j < ws.length := by omega
      rw [mwmrLinAux, seqOK_append, runOps_mwmrLinAux h.ws_write (by omega),
        List.getElem?_eq_getElem hj']
      refine ⟨ih (by omega), fun r hr' => ?_, ?_⟩
      · obtain ⟨v, hv⟩ := h.ws_write _ (List.getElem_mem hj')
        simp [opOrRead, hv, h.write_resp _ v r hv hr']
      · rw [wsVal_succ h.ws_write hj']
        exact hreads _

/-- The writes of the reads-from linearization are those of `ws`, in this order. -/
theorem opsFor_mwmrLin (α : List (Label P (register V v₀))) (ws : List (OpId P))
    (rf : OpId P → ℕ) :
    opsFor RWOp.isWrite (mwmrLin α ws rf) =
      (ws.filter (fun x => (opOrRead α x).isWrite)).map (fun x => (x, opOrRead α x)) := by
  have hR : ∀ m, opsFor RWOp.isWrite (mwmrReads α rf m) = [] := by
    intro m; simp [opsFor, mwmrReads, List.filter_map]
  suffices ∀ j, opsFor RWOp.isWrite (mwmrLinAux α ws rf j) =
      ((ws.take j).filter (fun x => (opOrRead α x).isWrite)).map (fun x => (x, opOrRead α x)) by
    rw [mwmrLin, this, List.take_length]
  intro j
  induction j with
  | zero => simp [mwmrLinAux, hR]
  | succ j ih =>
    rw [mwmrLinAux, opsFor_append, opsFor_append, ih, hR, List.take_add_one, List.filter_append,
      List.map_append, List.append_nil]
    congr 1
    cases ws[j]? <;> simp [opsFor, List.filter_cons]
    split <;> simp_all

end Cslib.SharedMemory
