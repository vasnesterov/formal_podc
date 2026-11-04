import Papers.PODC2014.WritableObjects.Defs
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# A sequentially writable `k`-word register (Figure 4.2, Section 4.1.1)

Aghazadeh, Golab, Woelfel, *Making Objects Writable*, PODC 2014; numbering of Chapter 4 of
Aghazadeh's PhD thesis.

The `k`-word register (`kWordReg k W w₀`) stores a `k`-tuple of words, initially all `w₀`;
`Read()` returns the tuple, `Write(x₀, …, x_{k-1})` replaces it. Implementation of Figure 4.2
(`kWordImpl`) from single-word registers `R[0..k-1]` (initially `w₀`):

* `SWrite(x₀, …, x_{k-1})`: `for i = 0 to k-1 do R[i].Write(x_i)`
* `Read()`: `for i = 0 to k-1 do x_i := R[i].Read()`; `return (x₀, …, x_{k-1})`

The thesis states without proof ("It is obvious") that every history in which no `SWrite`
overlaps another operation is linearizable, i.e. the object is sequentially writable
(`SeqWritable`, `Defs.lean`). This is `kWord_seqWritable`. Each operation performs exactly `k`
base-object accesses (`kwBound_invoke`, `kwBound_access`).

Proof: operations are linearized at their response. While a write is pending every other
process is idle, so a read only ever sees the memory of the last completed write.
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

/-- Operations of a `k`-word register. -/
inductive KWOp (k : ℕ) (W : Type) where
  | read
  | write (x : Fin k → W)

/-- The `k`-word register over words `W`, initially `(w₀, …, w₀)`. `Read()` returns
`some` of the tuple, `Write` returns the acknowledgement `none`. -/
abbrev kWordReg (k : ℕ) (W : Type) (w₀ : W) : ObjSpec where
  State := Fin k → W
  Op := KWOp k W
  Resp := Option (Fin k → W)
  init := fun _ => w₀
  δ S
    | .read => (S, some S)
    | .write x => (x, none)

/-- The `k`-word register is a writable type. -/
def kWordWritable (k : ℕ) (W : Type) (w₀ : W) : Writable (kWordReg k W w₀) where
  wr x := .write x
  wresp _ := none
  δ_wr _ _ := rfl

/-- Local states: `wr x j` has written `R[0..j-1]`; `rd j acc` has read `R[0..j-1]` into
`acc`. -/
inductive KWLoc (k : ℕ) (W : Type) where
  | idle
  | wr (x : Fin k → W) (j : ℕ)
  | rd (j : ℕ) (acc : Fin k → W)

/-- The implementation of Figure 4.2 from `k` single-word registers, for processes `P`. -/
def kWordImpl (k : ℕ) (W : Type) (w₀ : W) (P : Type) :
    Impl (kWordReg k W w₀) (fun _ : Fin k => register W w₀) P (KWLoc k W) where
  memInit _ := w₀
  locInit _ := .idle
  invoke _ _ o := match o with
    | .read => .rd 0 (fun _ => w₀)
    | .write x => .wr x 0
  act _ l := match l with
    | .idle => .ret none .idle
    | .wr x j =>
      if h : j < k then .access ⟨j, h⟩ (RWOp.write (x ⟨j, h⟩)) (fun _ => .wr x (j + 1))
      else .ret none .idle
    | .rd j acc =>
      if h : j < k then
        .access ⟨j, h⟩ RWOp.read (fun w => .rd (j + 1) (Function.update acc ⟨j, h⟩ w))
      else .ret (some acc) .idle

/-! ## Step complexity -/

/-- Number of base-object accesses a process still performs before returning. -/
def kwBound {k : ℕ} {W : Type} : KWLoc k W → ℕ
  | .idle => 0
  | .wr _ j => k - j
  | .rd j _ => k - j

/-- Right after an invocation, `k` accesses remain. -/
theorem kwBound_invoke (k : ℕ) (W : Type) (w₀ : W) (P : Type) (p : P) (l : KWLoc k W)
    (o : KWOp k W) : kwBound ((kWordImpl k W w₀ P).invoke p l o) = k := by
  cases o <;> simp [kWordImpl, kwBound]

/-- Every access decreases the bound by one, and a process with bound `0` returns next. -/
theorem kwBound_access (k : ℕ) (W : Type) (w₀ : W) (P : Type) (p : P) (l : KWLoc k W) :
    (∀ i o c, (kWordImpl k W w₀ P).act p l = .access i o c → ∀ r, kwBound (c r) + 1 = kwBound l) ∧
    (kwBound l = 0 → ∃ r l', (kWordImpl k W w₀ P).act p l = .ret r l') := by
  constructor
  · intro i o c h r
    cases l with
    | idle => simp [kWordImpl] at h
    | wr x j =>
      simp only [kWordImpl] at h
      split_ifs at h with hj
      obtain ⟨rfl, -, h⟩ := Action.access.inj h
      cases eq_of_heq h; simp [kwBound]; omega
    | rd j acc =>
      simp only [kWordImpl] at h
      split_ifs at h with hj
      obtain ⟨rfl, -, h⟩ := Action.access.inj h
      cases eq_of_heq h; simp [kwBound]; omega
  · intro h
    cases l with
    | idle => simp [kWordImpl]
    | wr x j =>
      simp only [kwBound] at h
      simp [kWordImpl, show ¬ j < k by omega]
    | rd j acc =>
      simp only [kwBound] at h
      simp [kWordImpl, show ¬ j < k by omega]

namespace KWord

variable {k : ℕ} {W : Type} {w₀ : W} {P : Type} [DecidableEq P]

/-- Configurations of the implementation. -/
abbrev KCfg (k : ℕ) (W : Type) (w₀ : W) (P : Type) :=
  Config (kWordReg k W w₀) (fun _ : Fin k => register W w₀) P (KWLoc k W)

/-- Per-process part of the invariant (memory `m`). -/
def LocOK (β : List (Label P (kWordReg k W w₀))) (L : List (OpId P × (kWordReg k W w₀).Op))
    (m : Fin k → W) (p : P) : KWLoc k W → Option (KWOp k W) → Prop
  | .idle, pd => pd = none
  | .wr x j, pd => pd = some (.write x) ∧ curOp β p ∉ L.map Prod.fst ∧ j ≤ k ∧
      ∀ i : Fin k, i.val < j → m i = x i
  | .rd j acc, pd => pd = some .read ∧ curOp β p ∉ L.map Prod.fst ∧ j ≤ k ∧
      ∀ i : Fin k, i.val < j → acc i = m i

/-- The invariant: `L` linearizes `β`, all pending operations are not yet linearized, and if no
write is pending, the registers hold the abstract state. -/
structure Inv (β : List (Label P (kWordReg k W w₀))) (C : KCfg k W w₀ P)
    (L : List (OpId P × (kWordReg k W w₀).Op)) : Prop where
  lin : IsLinearization β L
  loc : ∀ p, LocOK β L C.mem p (C.loc p) (C.pend p)
  good : (∀ p x, C.pend p ≠ some (.write x)) → C.mem = linState L

lemma LocOK.eq_idle {β : List (Label P (kWordReg k W w₀))}
    {L : List (OpId P × (kWordReg k W w₀).Op)} {m : Fin k → W} {p : P} {l : KWLoc k W}
    (h : LocOK β L m p l none) : l = .idle := by
  cases l <;> simp_all [LocOK]

lemma LocOK.frame {β β' : List (Label P (kWordReg k W w₀))}
    {L M : List (OpId P × (kWordReg k W w₀).Op)} {m m' : Fin k → W} {p : P} {l : KWLoc k W}
    {pd : Option (KWOp k W)} (h : LocOK β L m p l pd) (hcur : curOp β' p = curOp β p)
    (hM : curOp β p ∉ M.map Prod.fst) (hm : l ≠ .idle → m' = m) :
    LocOK β' (L ++ M) m' p l pd := by
  have hnm : curOp β p ∉ L.map Prod.fst → curOp β p ∉ (L ++ M).map Prod.fst := by
    intro hL; simp only [List.map_append, List.mem_append, not_or]; exact ⟨hL, hM⟩
  cases l with
  | idle => exact h
  | wr x j => rw [hm (by simp)]; exact ⟨h.1, hcur ▸ hnm h.2.1, h.2.2⟩
  | rd j acc => rw [hm (by simp)]; exact ⟨h.1, hcur ▸ hnm h.2.1, h.2.2⟩

/-- While a write is pending, every other process is idle. -/
lemma excl {β : List (Label P (kWordReg k W w₀))} {C : KCfg k W w₀ P}
    (hrun : (kWordImpl k W w₀ P).run β = some C) (hWI : WritesIsolated (kWordWritable k W w₀) β)
    {p q : P} {x : Fin k → W} (hp : C.pend p = some (.write x)) (hq : q ≠ p) :
    C.pend q = none := by
  by_contra hne
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨-, hpc, hpo⟩ := (kWordImpl k W w₀ P).run_pend_curOp hrun hp
  obtain ⟨hqi, hqc, -⟩ := (kWordImpl k W w₀ P).run_pend_curOp hrun ho
  have hxy : curOp β p ≠ curOp β q := fun h => hq (congrArg Prod.fst h).symm
  rcases hWI _ _ hxy ⟨x, hpo⟩ hqi with h | h
  · exact hpc h.completed
  · exact hqc h.completed

lemma WritesIsolated.of_append {β γ : List (Label P (kWordReg k W w₀))}
    (h : WritesIsolated (kWordWritable k W w₀) (β ++ γ)) :
    WritesIsolated (kWordWritable k W w₀) β := by
  rintro x y hxy ⟨v, hx⟩ hy
  rcases h x y hxy ⟨v, opOf_append_of_eq_some hx γ⟩ hy.mono with h' | h'
  · exact Or.inl (h'.of_append_of_invoked hy)
  · exact Or.inr (h'.of_append_of_invoked (Invoked.of_opOf_eq_some hx))

section Step

variable {β : List (Label P (kWordReg k W w₀))} {C₀ C : KCfg k W w₀ P}
  {L : List (OpId P × (kWordReg k W w₀).Op)}

lemma inv_step_inv (hrun : (kWordImpl k W w₀ P).run β = some C₀) (hI : Inv β C₀ L)
    {p : P} {o : KWOp k W} (hs : (kWordImpl k W w₀ P).step C₀ (.inv p o) = some C) :
    Inv (β ++ [.inv p o]) C L := by
  obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hl0 : C₀.loc p = .idle := by
    have h := hI.loc p; rw [h0] at h; exact h.eq_idle
  have hnot : curOp β p ∉ L.map Prod.fst := fun hm =>
    (kWordImpl k W w₀ P).not_invoked_curOp_of_idle hrun h0 (hI.lin.mem_invoked hm)
  refine ⟨hI.lin.append_inv p o, fun q => ?_, fun hno => ?_⟩
  · by_cases hq : q = p
    · subst hq
      rw [hloc, hpend, Function.update_self, Function.update_self, hl0]
      cases o <;> exact ⟨rfl, by rwa [curOp_append_inv], Nat.zero_le _, fun i hi => by simp at hi⟩
    · have h := (hI.loc q).frame (β' := β ++ [.inv p o]) (M := []) (m' := C.mem)
        (curOp_append_inv _ _ _ _) (by simp) (fun _ => hmem)
      rw [List.append_nil] at h
      rwa [hloc, hpend, Function.update_of_ne hq, Function.update_of_ne hq]
  · rw [hmem]
    refine hI.good (fun q x hqx => ?_)
    by_cases hq : q = p
    · subst hq; rw [h0] at hqx; cases hqx
    · exact hno q x (by rw [hpend, Function.update_of_ne hq]; exact hqx)

lemma inv_step_tau (hrun : (kWordImpl k W w₀ P).run β = some C₀) (hI : Inv β C₀ L)
    (hWI : WritesIsolated (kWordWritable k W w₀) β) {p : P}
    (hs : (kWordImpl k W w₀ P).step C₀ (.tau p) = some C) :
    Inv (β ++ [.tau p]) C L := by
  obtain ⟨h0, hpend, i', o', κ, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hcl := hI.loc p
  have hcur : ∀ q, curOp (β ++ [.tau p]) q = curOp β q := fun q => curOp_append_tau _ _ _
  refine ⟨hI.lin.append_tau p, fun q => ?_, fun hno => ?_⟩
  · by_cases hq : q = p
    · subst hq
      rw [hpend]
      cases hl : C₀.loc q with
      | idle => simp [kWordImpl, hl] at hact
      | wr x j =>
        rw [hl] at hcl hact
        obtain ⟨hpd, hnot, -, hm⟩ := hcl
        simp only [kWordImpl] at hact
        split_ifs at hact with hj
        cases hact
        rw [hloc, Function.update_self, hpd, hmem]
        refine ⟨rfl, by rwa [hcur], hj, fun i hi => ?_⟩
        by_cases hij : i = ⟨j, hj⟩
        · subst hij; exact Function.update_self _ _ _
        · rw [Function.update_of_ne hij]
          exact hm i (by
            have : i.val ≠ j := fun h => hij (Fin.ext h)
            omega)
      | rd j acc =>
        rw [hl] at hcl hact
        obtain ⟨hpd, hnot, -, hm⟩ := hcl
        simp only [kWordImpl] at hact
        split_ifs at hact with hj
        cases hact
        have hmem' : C.mem = C₀.mem := by rw [hmem]; exact Function.update_eq_self _ _
        rw [hloc, Function.update_self, hpd, hmem']
        refine ⟨rfl, by rwa [hcur], hj, fun i hi => ?_⟩
        by_cases hij : i = ⟨j, hj⟩
        · subst hij; exact Function.update_self _ _ _
        · rw [Function.update_of_ne hij]
          exact hm i (by
            have : i.val ≠ j := fun h => hij (Fin.ext h)
            omega)
    · -- `q` is idle if `p` writes; otherwise the memory is unchanged
      rw [hloc, hpend, Function.update_of_ne hq]
      by_cases hw : ∃ x, C₀.pend p = some (.write x)
      · obtain ⟨x, hx⟩ := hw
        have hqi := excl hrun hWI hx hq
        have h := hI.loc q
        rw [hqi] at h ⊢
        rw [h.eq_idle]; rfl
      · push Not at hw
        have hmem' : C.mem = C₀.mem := by
          cases hl : C₀.loc p with
          | idle => simp [kWordImpl, hl] at hact
          | wr x j =>
            rw [hl] at hcl; exact absurd hcl.1 (hw x)
          | rd j acc =>
            simp only [kWordImpl, hl] at hact
            split_ifs at hact with hj
            cases hact
            rw [hmem]; exact Function.update_eq_self _ _
        have h := (hI.loc q).frame (β' := β ++ [.tau p]) (M := []) (m' := C.mem) (hcur q)
          (by simp) (fun _ => hmem')
        rwa [List.append_nil] at h
  · -- some write would be pending in `C` if `p` were writing
    have hmem' : C.mem = C₀.mem := by
      cases hl : C₀.loc p with
      | idle => simp [kWordImpl, hl] at hact
      | wr x j =>
        rw [hl] at hcl; exact absurd (by rw [hpend]; exact hcl.1) (hno p x)
      | rd j acc =>
        simp only [kWordImpl, hl] at hact
        split_ifs at hact with hj
        cases hact
        rw [hmem]; exact Function.update_eq_self _ _
    rw [hmem']
    exact hI.good (fun q x hqx => hno q x (by rw [hpend]; exact hqx))

lemma inv_step_ret (hrun : (kWordImpl k W w₀ P).run β = some C₀) (hI : Inv β C₀ L)
    (hWI : WritesIsolated (kWordWritable k W w₀) β) {p : P} {r : Option (Fin k → W)}
    (hs : (kWordImpl k W w₀ P).step C₀ (.ret p r) = some C) :
    ∃ L', Inv (β ++ [.ret p r]) C L' := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  have hcl := hI.loc p
  have hcurq : ∀ q, q ≠ p → curOp (β ++ [.ret p r]) q = curOp β q :=
    fun q hq => curOp_append_ret_of_ne _ _ (Ne.symm hq)
  have hnotM : ∀ q, q ≠ p → ∀ o : KWOp k W, curOp β q ∉ [(curOp β p, o)].map Prod.fst :=
    fun q hq o h => hq (by simpa using congrArg Prod.fst (List.mem_singleton.1 h))
  cases hl : C₀.loc p with
  | idle => rw [hl] at hcl; exact absurd hcl h0
  | wr x j =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot, hjk, hm⟩ := hcl
    simp only [kWordImpl] at hact
    split_ifs at hact with hj
    obtain ⟨rfl, rfl⟩ := Action.ret.inj hact
    have hmx : C₀.mem = x := funext fun i => hm i (by have := i.isLt; omega)
    have hop := ((kWordImpl k W w₀ P).run_pend_curOp hrun hpd).2.2
    have hlin := hI.lin.push hop hnot (not_completed_curOp _ _)
    refine ⟨L ++ [(curOp β p, .write x)],
      hlin.append_ret_of_respIn (by rw [ObjSpec.respIn_concat_self hnot]),
      fun q => ?_, fun _ => ?_⟩
    · by_cases hq : q = p
      · subst hq; rw [hpend, hloc, Function.update_self, Function.update_self]; rfl
      · have hqi := excl hrun hWI hpd hq
        rw [hpend, hloc, Function.update_of_ne hq, Function.update_of_ne hq, hqi]
        have h := hI.loc q
        rw [hqi] at h
        rw [h.eq_idle]; rfl
    · rw [hmem, hmx, linState_concat]
  | rd j acc =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot, hjk, hm⟩ := hcl
    simp only [kWordImpl] at hact
    split_ifs at hact with hj
    obtain ⟨rfl, rfl⟩ := Action.ret.inj hact
    have hG := hI.good (fun q x hqx => by
      by_cases hq : q = p
      · subst hq; rw [hpd] at hqx; cases hqx
      · exact h0 (excl hrun hWI hqx (Ne.symm hq)))
    have hacc : acc = C₀.mem := funext fun i => hm i (by have := i.isLt; omega)
    have hop := ((kWordImpl k W w₀ P).run_pend_curOp hrun hpd).2.2
    have hlin := hI.lin.push hop hnot (not_completed_curOp _ _)
    refine ⟨L ++ [(curOp β p, .read)],
      hlin.append_ret_of_respIn (by rw [ObjSpec.respIn_concat_self hnot, hacc, hG]; rfl),
      fun q => ?_, fun _ => ?_⟩
    · by_cases hq : q = p
      · subst hq; rw [hpend, hloc, Function.update_self, Function.update_self]; rfl
      · have h := (hI.loc q).frame (β' := β ++ [.ret p (some acc)]) (m' := C.mem)
          (hcurq q hq) (hnotM q hq .read) (fun _ => hmem)
        rwa [hpend, hloc, Function.update_of_ne hq, Function.update_of_ne hq]
    · rw [hmem, hG, linState_concat]

end Step

theorem inv_of_run {β : List (Label P (kWordReg k W w₀))} {C : KCfg k W w₀ P}
    (h : (kWordImpl k W w₀ P).run β = some C) (hWI : WritesIsolated (kWordWritable k W w₀) β) :
    ∃ L, Inv β C L := by
  revert hWI
  refine (kWordImpl k W w₀ P).run_induction
    (Q := fun β C => WritesIsolated (kWordWritable k W w₀) β → ∃ L, Inv β C L)
    (fun _ => ⟨[], isLinearization_nil, fun _ => rfl, fun _ => rfl⟩) ?_ h
  intro β C₀ ℓ C hrun ih hs hWI
  obtain ⟨L, hI⟩ := ih (WritesIsolated.of_append hWI)
  cases ℓ with
  | inv p o => exact ⟨L, inv_step_inv hrun hI hs⟩
  | tau p => exact ⟨L, inv_step_tau hrun hI (WritesIsolated.of_append hWI) hs⟩
  | ret p r => exact inv_step_ret hrun hI (WritesIsolated.of_append hWI) hs

end KWord

/-- **Section 4.1.1 / Figure 4.2 of [AGW14] (thesis numbering).** The `k`-word register built
from `k` single-word registers (write `R[0..k-1]` in order, read `R[0..k-1]` in order) is
sequentially writable: every execution in which no `SWrite` overlaps another operation is
linearizable. -/
theorem kWord_seqWritable (k : ℕ) (W : Type) (w₀ : W) (P : Type) [DecidableEq P]
    (α : List (Label P (kWordReg k W w₀))) (hα : (kWordImpl k W w₀ P).Valid α) :
    SeqWritable (kWordWritable k W w₀) α := by
  intro hWI
  obtain ⟨C, hC⟩ := hα
  obtain ⟨L, hI⟩ := KWord.inv_of_run hC hWI
  exact ⟨L, hI.lin⟩

end Podc.WritableObjects
