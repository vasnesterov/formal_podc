import Papers.PODC2011.TimestampSpace.SimpleAlg
import Cslib.Computability.Distributed.SharedMemory.History
import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Lemma 5.1: correctness of the simple one-shot timestamp algorithm

Invariant-based proof of Lemma 5.1 of Helmi, Higham, Pacheco, Woelfel (PODC 2011): in every
one-shot execution of Algorithms 1 and 2 (`SimpleTS.alg`),

* every register only takes values in `{0, 1, 2}` and never decreases (`mem_le_two`,
  `mem_mono`);
* if a `getTS` returning `t₁` precedes a `getTS` returning `t₂` then `t₁ < t₂`, hence the
  history satisfies `TSCorrect` (`correct`).

Proof idea (the paper's): register `R[j]` is only written by its two owners, each at most once
(one-shot), with `r + 1` where `r` was read before; `r ≤ 1` and `r = 1` only if the partner has
already written, so writes never decrease `R[j]`. A `getTS` that started after another one
finished reads every register at least at the value the earlier one used, and its own register
strictly above. The invariant `Inv` makes this precise with an upper bound `UB` (the partial sum
is at most the sum of the current values of the registers read so far) and, for pending `getTS`
operations, a lower bound `LB` on the eventually returned value (partial sum + current values of
the registers still to be read + 1 for the pending increment).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.SimpleTS

open Cslib.SharedMemory

/-! ### Sums of register values -/

section Sums

variable {n : ℕ}

/-- Register values as a function on `ℕ` (`0` beyond the last register). -/
def ext (M : Fin ((n + 1) / 2) → ℕ) (j : ℕ) : ℕ := if h : j < (n + 1) / 2 then M ⟨j, h⟩ else 0

/-- Sum of `R[0..i-1]`. -/
def pre (M : Fin ((n + 1) / 2) → ℕ) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, ext M j

/-- Sum of `R[i..]`. -/
def suf (M : Fin ((n + 1) / 2) → ℕ) (i : ℕ) : ℕ := ∑ j ∈ Finset.Ico i ((n + 1) / 2), ext M j

/-- Sum of all registers. -/
def tot (M : Fin ((n + 1) / 2) → ℕ) : ℕ := suf M 0

variable {M M' : Fin ((n + 1) / 2) → ℕ}

lemma pre_succ (i : ℕ) : pre M (i + 1) = pre M i + ext M i := Finset.sum_range_succ _ _

lemma suf_of_lt {i : ℕ} (h : i < (n + 1) / 2) : suf M i = ext M i + suf M (i + 1) :=
  Finset.sum_eq_sum_Ico_succ_bot h _

lemma suf_of_ge {i : ℕ} (h : (n + 1) / 2 ≤ i) : suf M i = 0 := by
  simp [suf, Finset.Ico_eq_empty_of_le h]

lemma ext_of_ge {i : ℕ} (h : (n + 1) / 2 ≤ i) : ext M i = 0 := by
  simp [ext, show ¬ i < (n + 1) / 2 by omega]

lemma pre_add_suf (i : ℕ) : pre M i + suf M i = tot M := by
  induction i with
  | zero => simp [pre, tot]
  | succ i ih =>
    rw [pre_succ]
    rcases lt_or_ge i ((n + 1) / 2) with h | h
    · rw [suf_of_lt h] at ih; omega
    · rw [suf_of_ge h] at ih; rw [ext_of_ge h, suf_of_ge (by omega)]; omega

lemma pre_of_ge {i : ℕ} (h : (n + 1) / 2 ≤ i) : pre M i = tot M := by
  have := pre_add_suf (M := M) i; rw [suf_of_ge h] at this; omega

lemma ext_own (M : Fin ((n + 1) / 2) → ℕ) (p : Fin n) : ext M (own p).val = M (own p) := by
  simp [ext, (own p).isLt]

lemma ext_mono (h : ∀ j, M j ≤ M' j) (i : ℕ) : ext M i ≤ ext M' i := by
  unfold ext; split_ifs <;> simp [h]

lemma pre_mono (h : ∀ j, M j ≤ M' j) (i : ℕ) : pre M i ≤ pre M' i :=
  Finset.sum_le_sum fun j _ => ext_mono h j

lemma suf_mono (h : ∀ j, M j ≤ M' j) (i : ℕ) : suf M i ≤ suf M' i :=
  Finset.sum_le_sum fun j _ => ext_mono h j

lemma tot_mono (h : ∀ j, M j ≤ M' j) : tot M ≤ tot M' := suf_mono h 0

end Sums

/-! ### The invariant -/

variable {n : ℕ} {reread : Bool}

/-- Configurations of the algorithm. -/
abbrev Cfg (n : ℕ) := Config (tsObj ℕ) (Regs n) (Fin n) Loc

/-- Executions of the algorithm. -/
abbrev Exec (n : ℕ) := List (Label (Fin n) (tsObj ℕ))

/-- Number of processes that have written register `j`. -/
def cnt (w : Fin n → Bool) (j : Fin ((n + 1) / 2)) : ℕ :=
  (Finset.univ.filter (fun q : Fin n => own q = j ∧ w q = true)).card

lemma cnt_le_one {w : Fin n → Bool} {p : Fin n} (hp : w p = false) : cnt w (own p) ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, own, Fin.ext_iff] at ha hb
  have hap : a ≠ p := fun h => by subst h; simp [hp] at ha
  have hbp : b ≠ p := fun h => by subst h; simp [hp] at hb
  simp only [ne_eq, Fin.ext_iff] at hap hbp
  ext; omega

lemma cnt_le_two (w : Fin n → Bool) (j : Fin ((n + 1) / 2)) : cnt w j ≤ 2 := by
  have hj := j.isLt
  let x : Fin n := ⟨2 * j.val, by omega⟩
  have hx : own x = j := by ext; simp [own, x]
  have h1 : cnt w j ≤ cnt (Function.update w x false) j + 1 := by
    unfold cnt
    calc _ ≤ (insert x (Finset.univ.filter (fun q : Fin n =>
            own q = j ∧ Function.update w x false q = true))).card := by
          apply Finset.card_le_card
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hq ⊢
          by_cases hqx : q = x
          · exact Or.inl hqx
          · right; simp [Function.update_of_ne hqx, hq]
      _ ≤ _ := Finset.card_insert_le _ _
  have h2 := cnt_le_one (w := Function.update w x false) (p := x) (by simp)
  rw [hx] at h2; omega

lemma cnt_mono {w w' : Fin n → Bool} (h : ∀ q, w q = true → w' q = true) (j) :
    cnt w j ≤ cnt w' j := by
  apply Finset.card_le_card
  intro q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun ⟨a, b⟩ => ⟨a, h q b⟩

/-- Consistency of the pending operation with the program counter. -/
def PendOK : Option (TSOp ℕ) → PC → Prop
  | none, .idle => True
  | some .getTS, .rd _ _ => True
  | some .getTS, .wr _ _ => True
  | some .getTS, .rr _ => True
  | some (.compare a b), .cmp c => c = decide (a < b)
  | _, _ => False

/-- The ghost flag is consistent with the program counter (one-shot). -/
def WroteOK (p : Fin n) (l : Loc) : Prop :=
  match l.pc with
  | .rd i _ => (i ≤ (own p).val ↔ l.wrote = false)
  | .wr _ _ => l.wrote = false
  | .rr _ => l.wrote = true
  | _ => True

/-- Upper bound: the partial sum is at most the current sum of the registers read so far. -/
def UB (p : Fin n) (l : Loc) (M : Fin ((n + 1) / 2) → ℕ) : Prop :=
  match l.pc with
  | .rd i s => s ≤ pre M i
  | .wr _ s => s ≤ pre M (own p).val
  | .rr s => s ≤ pre M (own p).val
  | _ => True

/-- Lower bound on the value a pending `getTS` will return. -/
def LB (p : Fin n) (l : Loc) (M : Fin ((n + 1) / 2) → ℕ) : ℕ :=
  match l.pc with
  | .rd i s => s + suf M i + if i ≤ (own p).val then 1 else 0
  | .wr r s => s + (r + 1) + suf M ((own p).val + 1)
  | .rr s => s + suf M (own p).val
  | _ => 0

/-- Responses of completed operations. -/
def RespOK : TSOp ℕ → ℕ ⊕ Bool → Prop
  | .getTS, r => ∃ t, r = .inl t
  | .compare a b, r => r = .inr (decide (a < b))

lemma UB_mono {M M' : Fin ((n + 1) / 2) → ℕ} (h : ∀ j, M j ≤ M' j) {p : Fin n} {l : Loc}
    (hu : UB p l M) : UB p l M' := by
  obtain ⟨pc, w⟩ := l
  cases pc with
  | rd i s => exact (show s ≤ pre M i from hu).trans (pre_mono h _)
  | wr r s => exact (show s ≤ pre M (own p).val from hu).trans (pre_mono h _)
  | rr s => exact (show s ≤ pre M (own p).val from hu).trans (pre_mono h _)
  | idle => trivial
  | cmp b => trivial

lemma LB_mono {M M' : Fin ((n + 1) / 2) → ℕ} (h : ∀ j, M j ≤ M' j) (p : Fin n) (l : Loc) :
    LB p l M ≤ LB p l M' := by
  obtain ⟨pc, w⟩ := l
  cases pc with
  | rd i s => simp only [LB]; have := suf_mono h i; omega
  | wr r s => simp only [LB]; have := suf_mono h ((own p).val + 1); omega
  | rr s => simp only [LB]; have := suf_mono h (own p).val; omega
  | idle => exact le_rfl
  | cmp b => exact le_rfl

/-- The invariant of one-shot executions. -/
structure Inv (α : Exec n) (C : Cfg n) : Prop where
  pend : ∀ p, PendOK (C.pend p) (C.loc p).pc
  wok : ∀ p, WroteOK p (C.loc p)
  wr_le : ∀ p r s, (C.loc p).pc = .wr r s → r ≤ cnt (fun q => (C.loc q).wrote) (own p)
  cnt1 : ∀ p, (C.loc p).wrote = true ∨ C.pend p = some .getTS → 1 ≤ getTSCount α p
  reg : ∀ j, C.mem j ≤ cnt (fun q => (C.loc q).wrote) j
  ub : ∀ p, UB p (C.loc p) C.mem
  done_le : ∀ g t, opOf α g = some .getTS → respOf α g = some (.inl t) → t ≤ tot C.mem
  lb : ∀ q g t, C.pend q = some .getTS → opOf α g = some .getTS →
    respOf α g = some (.inl t) → Precedes α g (q, (respsOf α q).length) →
    t < LB q (C.loc q) C.mem
  order : ∀ g₁ g₂ t₁ t₂, opOf α g₁ = some .getTS → respOf α g₁ = some (.inl t₁) →
    opOf α g₂ = some .getTS → respOf α g₂ = some (.inl t₂) → Precedes α g₁ g₂ → t₁ < t₂
  resp : ∀ g o r, opOf α g = some o → respOf α g = some r → RespOK o r

/-! ### Steps of the algorithm -/

section Steps

variable {C C' : Cfg n} {p : Fin n}

lemma step_inv_eq {o : TSOp ℕ} (h : (alg n reread).step C (.inv p o) = some C') :
    C.pend p = none ∧ C' = ⟨Function.update C.loc p (invoke (C.loc p) o),
      Function.update C.pend p (some o), C.mem⟩ := by
  obtain ⟨h0, -, h1, h2, h3⟩ := Impl.step_inv h
  refine ⟨h0, ?_⟩
  obtain ⟨l', p', m'⟩ := C'
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

lemma step_ret_eq {r : ℕ ⊕ Bool} (h : (alg n reread).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ ∃ l, act reread p (C.loc p) = .ret r l ∧
      C' = ⟨Function.update C.loc p l, Function.update C.pend p none, C.mem⟩ := by
  obtain ⟨h0, h1, h2, l, hl, h3⟩ := Impl.step_ret h
  refine ⟨h0, l, hl, ?_⟩
  obtain ⟨l', p', m'⟩ := C'
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

lemma step_tau_eq (h : (alg n reread).step C (.tau p) = some C') :
    C.pend p ≠ none ∧
    ((∃ i s, (C.loc p).pc = .rd i s ∧ ∃ hi : i < (n + 1) / 2, i ≠ (own p).val ∧
        C' = ⟨Function.update C.loc p { C.loc p with pc := .rd (i + 1) (s + C.mem ⟨i, hi⟩) },
          C.pend, C.mem⟩) ∨
      (∃ s, (C.loc p).pc = .rd (own p).val s ∧
        C' = ⟨Function.update C.loc p { C.loc p with pc := .wr (C.mem (own p)) s },
          C.pend, C.mem⟩) ∨
      (∃ r s, (C.loc p).pc = .wr r s ∧
        C' = ⟨Function.update C.loc p
            ⟨if reread then .rr s else .rd ((own p).val + 1) (s + (r + 1)), true⟩,
          C.pend, Function.update C.mem (own p) (r + 1)⟩) ∨
      (∃ s, (C.loc p).pc = .rr s ∧
        C' = ⟨Function.update C.loc p
            { C.loc p with pc := .rd ((own p).val + 1) (s + C.mem (own p)) },
          C.pend, C.mem⟩)) := by
  have h0 := (Impl.step_tau h).1
  refine ⟨h0, ?_⟩
  simp only [Impl.step, h0, ite_false, alg, act] at h
  rcases hl : C.loc p with ⟨pc, w⟩
  rw [hl] at h
  cases pc with
  | idle => simp at h
  | cmp b => simp at h
  | rd i s =>
    simp only at h
    split_ifs at h with hi ho
    · simp only [Option.some.injEq] at h
      subst h ho
      right; left; exact ⟨s, rfl, by simp⟩
    · simp only [Option.some.injEq] at h
      subst h
      left; exact ⟨i, s, rfl, hi, ho, by simp⟩
  | wr r s =>
    simp only [Option.some.injEq] at h
    subst h
    right; right; left; exact ⟨r, s, rfl, by simp⟩
  | rr s =>
    simp only [Option.some.injEq] at h
    subst h
    right; right; right; exact ⟨s, rfl, by simp⟩

end Steps

/-! ### Preservation of the invariant -/

lemma pendOK_none {pc : PC} (h : PendOK none pc) : pc = .idle := by
  cases pc <;> simp_all [PendOK]

lemma pendOK_getTS_of_access {o : Option (TSOp ℕ)} {pc : PC} (h : PendOK o pc)
    (hpc : pc ≠ .idle ∧ ∀ b, pc ≠ .cmp b) : o = some .getTS := by
  rcases o with _ | _ | ⟨a, b⟩
  · exact absurd (pendOK_none h) hpc.1
  · rfl
  · cases pc <;> simp_all [PendOK]

lemma inv_init : Inv ([] : Exec n) (alg n reread).initCfg where
  pend _ := trivial
  wok _ := trivial
  wr_le _ _ _ h := by simp [Impl.initCfg, alg] at h
  cnt1 _ h := by simp [Impl.initCfg, alg] at h
  reg _ := Nat.zero_le _
  ub _ := trivial
  done_le _ _ h := by simp [opOf] at h
  lb _ _ _ h := by simp [Impl.initCfg] at h
  order _ _ _ _ h := by simp [opOf] at h
  resp _ _ _ h := by simp [opOf] at h

lemma getTSCount_snoc_tau (α : Exec n) (p q : Fin n) :
    getTSCount (α ++ [.tau p]) q = getTSCount α q := by
  simp [getTSCount]

/-- Frame lemma for internal steps: only the stepping process' local state and the memory
change; the memory and the set of writers only grow. -/
lemma inv_tau_frame {α : Exec n} {C : Cfg n} {p : Fin n} {l' : Loc}
    {M' : Fin ((n + 1) / 2) → ℕ} (hI : Inv α C)
    (hM : ∀ j, C.mem j ≤ M' j)
    (hW : ∀ q, (C.loc q).wrote = true → (Function.update C.loc p l' q).wrote = true)
    (hpend : PendOK (C.pend p) l'.pc) (hwok : WroteOK p l')
    (hwr : ∀ r s, l'.pc = .wr r s →
      r ≤ cnt (fun q => (Function.update C.loc p l' q).wrote) (own p))
    (hcnt1 : l'.wrote = true ∨ C.pend p = some .getTS → 1 ≤ getTSCount α p)
    (hreg : ∀ j, M' j ≤ cnt (fun q => (Function.update C.loc p l' q).wrote) j)
    (hub : UB p l' M')
    (hlb : C.pend p = some .getTS → LB p (C.loc p) C.mem ≤ LB p l' M') :
    Inv (α ++ [.tau p]) ⟨Function.update C.loc p l', C.pend, M'⟩ := by
  have hne : ∀ q r, (Label.tau p : Label (Fin n) (tsObj ℕ)) ≠ .ret q r := by simp
  have hni : ∀ q o, (Label.tau p : Label (Fin n) (tsObj ℕ)) ≠ .inv q o := by simp
  have hcntm := cnt_mono hW
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simpa using hpend
    · simpa [Function.update_of_ne hq] using hI.pend q
  · intro q
    by_cases hq : q = p
    · subst hq; simpa using hwok
    · simpa [Function.update_of_ne hq] using hI.wok q
  · intro q r s h
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self] at h; exact hwr r s h
    · simp only [Function.update_of_ne hq] at h
      exact (hI.wr_le q r s h).trans (hcntm _)
  · intro q h
    rw [getTSCount_snoc_tau]
    by_cases hq : q = p
    · subst hq; simpa using hcnt1 (by simpa using h)
    · exact hI.cnt1 q (by simpa [Function.update_of_ne hq] using h)
  · exact hreg
  · intro q
    by_cases hq : q = p
    · subst hq; simpa using hub
    · simpa [Function.update_of_ne hq] using UB_mono hM (hI.ub q)
  · intro g t h1 h2
    rw [opOf_concat_of_ne (x := g) (hni g.1), respOf_concat_of_ne (x := g) (hne g.1)] at *
    exact (hI.done_le g t h1 h2).trans (tot_mono hM)
  · intro q g t hq h1 h2 h3
    rw [opOf_concat_of_ne (x := g) (hni g.1), respOf_concat_of_ne (x := g) (hne g.1)] at *
    rw [respsOf_concat_of_ne (hne q)] at h3
    have h3 := Precedes.of_concat_of_not_ret hne h3
    have key := hI.lb q g t hq h1 h2 h3
    by_cases hqp : q = p
    · subst hqp; simpa using key.trans_le (hlb hq)
    · simpa [Function.update_of_ne hqp] using key.trans_le (LB_mono hM q _)
  · intro g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5
    rw [opOf_concat_of_ne (x := g₁) (hni g₁.1), respOf_concat_of_ne (x := g₁) (hne g₁.1),
      opOf_concat_of_ne (x := g₂) (hni g₂.1), respOf_concat_of_ne (x := g₂) (hne g₂.1)] at *
    exact hI.order g₁ g₂ t₁ t₂ h1 h2 h3 h4 (Precedes.of_concat_of_not_ret hne h5)
  · intro g o r h1 h2
    rw [opOf_concat_of_ne (x := g) (hni g.1), respOf_concat_of_ne (x := g) (hne g.1)] at *
    exact hI.resp g o r h1 h2

lemma hW_of_wrote {C : Cfg n} {p : Fin n} {l' : Loc}
    (h : (C.loc p).wrote = true → l'.wrote = true) :
    ∀ q, (C.loc q).wrote = true → (Function.update C.loc p l' q).wrote = true := by
  intro q hq
  by_cases hqp : q = p
  · subst hqp; simpa using h hq
  · simpa [Function.update_of_ne hqp] using hq

lemma wrote_update_same {C : Cfg n} {p : Fin n} {l' : Loc} (h : l'.wrote = (C.loc p).wrote) :
    (fun q => (Function.update C.loc p l' q).wrote) = fun q => (C.loc q).wrote := by
  funext q
  by_cases hqp : q = p
  · subst hqp; simpa using h
  · simp [Function.update_of_ne hqp]

lemma reg_update_same {C : Cfg n} {p : Fin n} {l' : Loc} (hI : ∀ j, C.mem j ≤ cnt (fun q => (C.loc q).wrote) j)
    (h : l'.wrote = (C.loc p).wrote) :
    ∀ j, C.mem j ≤ cnt (fun q => (Function.update C.loc p l' q).wrote) j := by
  rw [wrote_update_same h]; exact hI

lemma ext_fin (M : Fin ((n + 1) / 2) → ℕ) {i : ℕ} (hi : i < (n + 1) / 2) :
    ext M i = M ⟨i, hi⟩ := by simp [ext, hi]

lemma cnt_update_true {w : Fin n → Bool} {p : Fin n} (hp : w p = false) :
    cnt w (own p) + 1 ≤ cnt (Function.update w p true) (own p) := by
  unfold cnt
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter _) (a := p) (by simp [hp])]
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  rcases hq with rfl | ⟨h1, h2⟩
  · simp
  · by_cases hqp : q = p
    · subst hqp; simp
    · simp [Function.update_of_ne hqp, h1, h2]

/-- Internal steps preserve the invariant. -/
lemma inv_tau {α : Exec n} {C C' : Cfg n} {p : Fin n} (hI : Inv α C)
    (hs : (alg n reread).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' := by
  have hown := (own p).isLt
  obtain ⟨h0, h | h | h | h⟩ := step_tau_eq hs
  · obtain ⟨i, s, hpc, hi, hio, rfl⟩ := h
    have hg : C.pend p = some .getTS := pendOK_getTS_of_access (hI.pend p) (by simp [hpc])
    have hwok := hI.wok p; simp only [WroteOK, hpc] at hwok
    have hub := hI.ub p; simp only [UB, hpc] at hub
    refine inv_tau_frame hI (fun _ => le_rfl) (hW_of_wrote id) (by rw [hg]; trivial)
      ?_ (by intro r s h; simp at h) (fun _ => hI.cnt1 p (Or.inr hg))
      (reg_update_same hI.reg (by rfl)) ?_ (fun _ => ?_)
    · simp only [WroteOK]; rw [← hwok]; exact ⟨fun h => by omega, fun h => by omega⟩
    · simp only [UB]; rw [pre_succ, ext_fin _ hi]; omega
    · simp only [LB, hpc]; rw [suf_of_lt hi, ext_fin _ hi]
      split_ifs <;> omega
  · obtain ⟨s, hpc, rfl⟩ := h
    have hg : C.pend p = some .getTS := pendOK_getTS_of_access (hI.pend p) (by simp [hpc])
    have hwok := hI.wok p; simp only [WroteOK, hpc, le_refl, true_iff] at hwok
    have hub := hI.ub p; simp only [UB, hpc] at hub
    refine inv_tau_frame hI (fun _ => le_rfl) (hW_of_wrote id) (by rw [hg]; trivial)
      hwok ?_ (fun _ => hI.cnt1 p (Or.inr hg))
      (reg_update_same hI.reg (by rfl)) hub (fun _ => ?_)
    · intro r s' h
      simp only [PC.wr.injEq] at h
      rw [← h.1]; exact reg_update_same hI.reg (by rfl) _
    · simp only [LB, hpc, le_refl, ite_true]; rw [suf_of_lt hown, ext_own]; omega
  · obtain ⟨r, s, hpc, rfl⟩ := h
    have hg : C.pend p = some .getTS := pendOK_getTS_of_access (hI.pend p) (by simp [hpc])
    have hwok : (C.loc p).wrote = false := by have := hI.wok p; simpa [WroteOK, hpc] using this
    have hub := hI.ub p; simp only [UB, hpc] at hub
    have hwr := hI.wr_le p r s hpc
    have hcw : (fun q => (Function.update C.loc p
        (⟨if reread then .rr s else .rd ((own p).val + 1) (s + (r + 1)), true⟩ : Loc) q).wrote) =
        Function.update (fun q => (C.loc q).wrote) p true := by
      funext q; by_cases hqp : q = p
      · subst hqp; simp
      · simp [Function.update_of_ne hqp]
    have hc1 := cnt_le_one (w := fun q => (C.loc q).wrote) hwok
    have hc2 := cnt_update_true (w := fun q => (C.loc q).wrote) hwok
    have hmem : ∀ j, C.mem j ≤ Function.update C.mem (own p) (r + 1) j := by
      intro j; by_cases hj : j = own p
      · subst hj; simp only [Function.update_self]
        exact le_trans (hI.reg (own p)) (le_trans hc1 (Nat.le_add_left 1 r))
      · simp [Function.update_of_ne hj]
    refine inv_tau_frame hI hmem (hW_of_wrote (fun _ => rfl)) ?_ ?_ ?_
      (fun _ => hI.cnt1 p (Or.inr hg)) ?_ ?_ (fun _ => ?_)
    · rw [hg]; cases reread <;> trivial
    · cases reread <;> simp [WroteOK]
    · intro r' s' h; cases reread <;> simp at h
    · rw [hcw]; intro j; by_cases hj : j = own p
      · subst hj; simp only [Function.update_self]; omega
      · have hmono : ∀ q, (C.loc q).wrote = true →
            Function.update (fun q => (C.loc q).wrote) p true q = true := by
          intro q hq; by_cases hqp : q = p
          · subst hqp; simp
          · simpa [Function.update_of_ne hqp] using hq
        simp only [Function.update_of_ne hj]
        exact (hI.reg j).trans (cnt_mono hmono j)
    · have hp := pre_mono hmem (own p).val
      cases reread
      · simp only [UB, Bool.false_eq_true, ite_false]
        rw [pre_succ, ext_own]; simp only [Function.update_self]; omega
      · simp only [UB, ite_true]; omega
    · have hsuf := suf_mono hmem ((own p).val + 1)
      cases reread
      · simp only [LB, hpc, Bool.false_eq_true, ite_false]; split_ifs <;> omega
      · simp only [LB, hpc, ite_true]
        rw [suf_of_lt hown, ext_own]; simp only [Function.update_self]; omega
  · obtain ⟨s, hpc, rfl⟩ := h
    have hg : C.pend p = some .getTS := pendOK_getTS_of_access (hI.pend p) (by simp [hpc])
    have hwok : (C.loc p).wrote = true := by have := hI.wok p; simpa [WroteOK, hpc] using this
    have hub := hI.ub p; simp only [UB, hpc] at hub
    refine inv_tau_frame hI (fun _ => le_rfl) (hW_of_wrote id) (by rw [hg]; trivial)
      ?_ (by intro r s h; simp at h) (fun _ => hI.cnt1 p (Or.inr hg))
      (reg_update_same hI.reg (by rfl)) ?_ (fun _ => ?_)
    · simp [WroteOK, hwok]
    · simp only [UB]; rw [pre_succ, ext_own]; omega
    · simp only [LB, hpc]; rw [suf_of_lt hown, ext_own]; split_ifs <;> omega

/-- Invocations preserve the invariant (here one-shotness is used). -/
lemma inv_inv {α : Exec n} {C C' : Cfg n} {p : Fin n} {o : TSOp ℕ} (hI : Inv α C)
    (hrun : (alg n reread).run α = some C) (hadm : Adm true (α ++ [.inv p o]))
    (hs : (alg n reread).step C (.inv p o) = some C') : Inv (α ++ [.inv p o]) C' := by
  obtain ⟨h0, rfl⟩ := step_inv_eq hs
  have hidle : (C.loc p).pc = .idle := pendOK_none (h0 ▸ hI.pend p)
  have hne : ∀ q r, (Label.inv p o : Label (Fin n) (tsObj ℕ)) ≠ .ret q r := by simp
  have hresp : ∀ g, respOf (α ++ [.inv p o]) g = respOf α g :=
    fun g => respOf_concat_of_ne (x := g) (hne g.1)
  have hlw : (invoke (C.loc p) o).wrote = (C.loc p).wrote := by cases o <;> rfl
  have hop : ∀ g r, respOf α g = some r → opOf (α ++ [.inv p o]) g = opOf α g := by
    intro g r h
    apply opOf_append_of_invoked
    have h1 := Completed.of_respOf_eq_some h
    have h2 := Impl.run_resps_le_ops hrun g.1
    simp only [Invoked, Completed] at *; omega
  have hcount : ∀ q, getTSCount α q ≤ getTSCount (α ++ [.inv p o]) q := by intro q; simp
  have hfresh : o = .getTS → (C.loc p).wrote = false := by
    rintro rfl
    by_contra hw
    simp only [Bool.not_eq_false] at hw
    have h1 := hI.cnt1 p (Or.inl hw)
    have h2 := hadm rfl p
    have h3 : getTSCount [(Label.inv p TSOp.getTS : Label (Fin n) (tsObj ℕ))] p = 1 := by
      simp [getTSCount, TSOp.isGetTS]
    rw [getTSCount_append, h3] at h2
    omega
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; cases o <;> simp [PendOK, invoke]
    · simpa [Function.update_of_ne hq] using hI.pend q
  · intro q
    by_cases hq : q = p
    · subst hq
      cases o with
      | getTS => simp [WroteOK, invoke, hfresh rfl]
      | compare a b => simp [WroteOK, invoke]
    · simpa [Function.update_of_ne hq] using hI.wok q
  · intro q r s h
    by_cases hq : q = p
    · subst hq; cases o <;> simp [invoke] at h
    · simp only [Function.update_of_ne hq] at h
      simp only [wrote_update_same hlw]
      exact hI.wr_le q r s h
  · intro q h
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, Option.some.injEq] at h
      rcases h with h | rfl
      · rw [hlw] at h; exact (hI.cnt1 q (Or.inl h)).trans (hcount q)
      · simp [getTSCount, TSOp.isGetTS]
    · simp only [Function.update_of_ne hq] at h
      exact (hI.cnt1 q h).trans (hcount q)
  · simp only [wrote_update_same hlw]; exact hI.reg
  · intro q
    by_cases hq : q = p
    · subst hq; cases o <;> simp [UB, invoke]
    · simpa [Function.update_of_ne hq] using hI.ub q
  · intro g t h1 h2
    rw [hresp] at h2; rw [hop g _ h2] at h1
    exact hI.done_le g t h1 h2
  · intro q g t hq h1 h2 h3
    rw [hresp] at h2; rw [hop g _ h2] at h1
    rw [respsOf_concat_of_ne (hne q)] at h3
    have h3 := Precedes.of_concat_of_not_ret hne h3
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, Option.some.injEq] at hq
      subst hq
      have := hI.done_le g t h1 h2
      simp only [Function.update_self, LB, invoke, Nat.zero_le, ite_true, zero_add]
      unfold tot at this; omega
    · simp only [Function.update_of_ne hqp] at hq ⊢
      exact hI.lb q g t hq h1 h2 h3
  · intro g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5
    rw [hresp] at h2 h4; rw [hop _ _ h2] at h1; rw [hop _ _ h4] at h3
    exact hI.order g₁ g₂ t₁ t₂ h1 h2 h3 h4 (Precedes.of_concat_of_not_ret hne h5)
  · intro g o' r h1 h2
    rw [hresp] at h2; rw [hop _ _ h2] at h1
    exact hI.resp g o' r h1 h2

lemma act_ret_cases {p : Fin n} {l l' : Loc} {r : ℕ ⊕ Bool}
    (h : act reread p l = .ret r l') :
    l.pc = .idle ∨ (∃ b, l.pc = .cmp b ∧ r = .inr b ∧ l' = { l with pc := .idle }) ∨
      (∃ i s, l.pc = .rd i s ∧ (n + 1) / 2 ≤ i ∧ r = .inl s ∧ l' = { l with pc := .idle }) := by
  obtain ⟨pc, w⟩ := l
  cases pc with
  | idle => exact Or.inl rfl
  | cmp b =>
    simp only [act, Action.ret.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Or.inl ⟨b, rfl, rfl, rfl⟩)
  | rd i s =>
    simp only [act] at h
    split_ifs at h with h1 h2
    simp only [Action.ret.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Or.inr ⟨i, s, rfl, by omega, rfl, rfl⟩)
  | wr r s => simp [act] at h
  | rr s => simp [act] at h

/-- Responses preserve the invariant. -/
lemma inv_ret {α : Exec n} {C C' : Cfg n} {p : Fin n} {r : ℕ ⊕ Bool} (hI : Inv α C)
    (hrun : (alg n reread).run α = some C)
    (hs : (alg n reread).step C (.ret p r) = some C') : Inv (α ++ [.ret p r]) C' := by
  obtain ⟨h0, l, hact, rfl⟩ := step_ret_eq hs
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
  have hop0 := (Impl.run_pend_curOp hrun ho).2.2
  have hni : ∀ q o, (Label.ret p r : Label (Fin n) (tsObj ℕ)) ≠ .inv q o := by simp
  have hopeq : ∀ g, opOf (α ++ [.ret p r]) g = opOf α g :=
    fun g => opOf_concat_of_ne (x := g) (hni g.1)
  have hcase : (∃ b, (C.loc p).pc = .cmp b ∧ r = .inr b ∧ l = { C.loc p with pc := .idle }) ∨
      (∃ i s, (C.loc p).pc = .rd i s ∧ (n + 1) / 2 ≤ i ∧ r = .inl s ∧
        l = { C.loc p with pc := .idle }) := by
    rcases act_ret_cases hact with h | h | h
    · have := hI.pend p; rw [ho, h] at this; cases o <;> simp [PendOK] at this
    · exact Or.inl h
    · exact Or.inr h
  have hlw : l.wrote = (C.loc p).wrote := by
    rcases hcase with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> rfl
  have hlpc : l.pc = .idle := by
    rcases hcase with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> rfl
  have hnew : ∀ g r', respOf (α ++ [.ret p r]) g = some r' →
      respOf α g = some r' ∨ (g = (p, (respsOf α p).length) ∧ r' = r) := by
    intro g r' h
    rcases respOf_concat_cases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · simp only [Label.ret.injEq] at h1
      obtain ⟨h1, rfl⟩ := h1
      right; refine ⟨Prod.ext h1.symm ?_, rfl⟩
      rw [h2, ← h1]
  have hval : o = .getTS → ∃ i s, (C.loc p).pc = .rd i s ∧ (n + 1) / 2 ≤ i ∧ r = .inl s := by
    rintro rfl
    rcases hcase with ⟨b, hb, -⟩ | ⟨i, s, h1, h2, h3, -⟩
    · have := hI.pend p; rw [ho, hb] at this; simp [PendOK] at this
    · exact ⟨i, s, h1, h2, h3⟩
  have hcount : ∀ q, getTSCount (α ++ [.ret p r]) q = getTSCount α q := by
    intro q; simp [getTSCount]
  have hcompl : ∀ g r', respOf (α ++ [.ret p r]) g = some r' → Completed α g →
      respOf α g = some r' := by
    intro g r' h hc; rwa [respOf_append_of_completed hc] at h
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simp [hlpc, PendOK]
    · simpa [Function.update_of_ne hq] using hI.pend q
  · intro q
    by_cases hq : q = p
    · subst hq; simp [WroteOK, hlpc]
    · simpa [Function.update_of_ne hq] using hI.wok q
  · intro q r' s h
    by_cases hq : q = p
    · subst hq; simp [hlpc] at h
    · simp only [Function.update_of_ne hq] at h
      simp only [wrote_update_same hlw]
      exact hI.wr_le q r' s h
  · intro q h
    rw [hcount]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, reduceCtorEq, or_false] at h
      exact hI.cnt1 q (Or.inl (hlw ▸ h))
    · simp only [Function.update_of_ne hq] at h
      exact hI.cnt1 q h
  · simp only [wrote_update_same hlw]; exact hI.reg
  · intro q
    by_cases hq : q = p
    · subst hq; simp [UB, hlpc]
    · simpa [Function.update_of_ne hq] using hI.ub q
  · intro g t h1 h2
    rw [hopeq] at h1
    rcases hnew g _ h2 with h2 | ⟨rfl, hr⟩
    · exact hI.done_le g t h1 h2
    · rw [hop0] at h1
      obtain ⟨i, s, hpc, hi, hrs⟩ := hval (Option.some.inj h1)
      rw [hrs] at hr; cases hr
      have := hI.ub p; simp only [UB, hpc] at this
      rw [pre_of_ge hi] at this; exact this
  · intro q g t hq h1 h2 h3
    have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq ⊢
    rw [hopeq] at h1
    rw [respsOf_concat_of_ne (q := q) (by simp [Ne.symm hqp])] at h3
    rcases precedes_concat h3 with h3 | ⟨-, h4⟩
    · exact hI.lb q g t hq h1 (hcompl g _ h2 h3.completed) h3
    · exact absurd (Invoked.of_opOf_eq_some ((Impl.run_pend_curOp hrun hq).2.2)).mono h4
  · intro g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5
    rw [hopeq] at h1 h3
    rcases precedes_concat h5 with h5 | ⟨-, h6⟩
    · have h2' := hcompl g₁ _ h2 h5.completed
      rcases hnew g₂ _ h4 with h4 | ⟨rfl, hr⟩
      · exact hI.order g₁ g₂ t₁ t₂ h1 h2' h3 h4 h5
      · rw [hop0] at h3
        have hog := Option.some.inj h3
        obtain ⟨i, s, hpc, hi, hrs⟩ := hval hog
        rw [hrs] at hr; cases hr
        have := hI.lb p g₁ t₁ (by rw [ho, hog]) h1 h2' h5
        simp only [LB, hpc, suf_of_ge hi] at this
        have hown := (own p).isLt
        split_ifs at this <;> omega
    · exact absurd (Invoked.of_opOf_eq_some h3).mono h6
  · intro g o' r' h1 h2
    rw [hopeq] at h1
    rcases hnew g _ h2 with h2 | ⟨rfl, rfl⟩
    · exact hI.resp g o' r' h1 h2
    · rw [hop0] at h1
      cases Option.some.inj h1
      rcases hcase with ⟨b, hb, rfl, -⟩ | ⟨i, s, hpc, -, rfl, -⟩
      · have := hI.pend p; rw [ho, hb] at this
        cases o with
        | getTS => simp [PendOK] at this
        | compare a b' => simp only [PendOK] at this; subst this; rfl
      · have := hI.pend p; rw [ho, hpc] at this
        cases o with
        | getTS => exact ⟨s, rfl⟩
        | compare a b' => simp [PendOK] at this

/-- **The invariant** holds in every one-shot execution. -/
theorem inv_run {α : Exec n} {C : Cfg n} (h : (alg n reread).run α = some C)
    (hadm : Adm true α) : Inv α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [Impl.run_nil, Option.some.injEq] at h; subst h; exact inv_init
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases h1 : (alg n reread).runFrom (alg n reread).initCfg α with
    | none => simp [h1] at h
    | some C₁ =>
      simp only [h1, Option.bind_some, Impl.runFrom_singleton] at h
      have hI := ih h1 hadm.of_append
      cases ℓ with
      | inv p o => exact inv_inv hI h1 hadm h
      | tau p => exact inv_tau hI h
      | ret p r => exact inv_ret hI h1 h

/-! ### Main results -/

/-- Every step of a one-shot execution leaves each register at least as large. -/
lemma step_mem_mono {α : Exec n} {C C' : Cfg n} {ℓ : Label (Fin n) (tsObj ℕ)} (hI : Inv α C)
    (hs : (alg n reread).step C ℓ = some C') (j : Fin ((n + 1) / 2)) : C.mem j ≤ C'.mem j := by
  cases ℓ with
  | inv p o => obtain ⟨-, rfl⟩ := step_inv_eq hs; exact le_rfl
  | ret p r => obtain ⟨-, l, -, rfl⟩ := step_ret_eq hs; exact le_rfl
  | tau p =>
    obtain ⟨-, h | h | h | h⟩ := step_tau_eq hs
    · obtain ⟨i, s, -, hi, -, rfl⟩ := h; exact le_rfl
    · obtain ⟨s, -, rfl⟩ := h; exact le_rfl
    · obtain ⟨r, s, hpc, rfl⟩ := h
      have hwok : (C.loc p).wrote = false := by
        have := hI.wok p; simpa [WroteOK, hpc] using this
      have hc1 := cnt_le_one (w := fun q => (C.loc q).wrote) hwok
      by_cases hj : j = own p
      · subst hj; simp only [Function.update_self]
        exact le_trans (hI.reg (own p)) (le_trans hc1 (Nat.le_add_left 1 r))
      · simp [Function.update_of_ne hj]
    · obtain ⟨s, -, rfl⟩ := h; exact le_rfl

/-- **Lemma 5.1 (register values).** In every one-shot execution every register holds a value
in `{0, 1, 2}`. -/
theorem mem_le_two {α : Exec n} {C : Cfg n} (h : (alg n reread).run α = some C)
    (hadm : Adm true α) (j : Fin ((n + 1) / 2)) : C.mem j ≤ 2 :=
  le_trans ((inv_run h hadm).reg j) (cnt_le_two _ j)

/-- **Lemma 5.1 (proof, first claim).** In one-shot executions registers never decrease. -/
theorem mem_mono {α β : Exec n} {C C' : Cfg n} (h : (alg n reread).run α = some C)
    (h' : (alg n reread).run (α ++ β) = some C') (hadm : Adm true (α ++ β))
    (j : Fin ((n + 1) / 2)) : C.mem j ≤ C'.mem j := by
  induction β using List.reverseRecOn generalizing C' with
  | nil => simp only [List.append_nil, h, Option.some.injEq] at h'; subst h'; exact le_rfl
  | append_singleton β ℓ ih =>
    rw [← List.append_assoc, Impl.run, Impl.runFrom_append] at h'
    cases h1 : (alg n reread).runFrom (alg n reread).initCfg (α ++ β) with
    | none => simp [h1] at h'
    | some C₁ =>
      simp only [h1, Option.bind_some, Impl.runFrom_singleton] at h'
      rw [← List.append_assoc] at hadm
      exact (ih h1 hadm.of_append).trans (step_mem_mono (inv_run h1 hadm.of_append) h' j)

/-- **Lemma 5.1 (proof, second claim).** In a one-shot execution, if a `getTS` returning `t₁`
precedes a `getTS` returning `t₂`, then `t₁ < t₂`. -/
theorem getTS_lt {α : Exec n} {C : Cfg n} (h : (alg n reread).run α = some C)
    (hadm : Adm true α) {g₁ g₂ : OpId (Fin n)} {t₁ t₂ : ℕ}
    (h1 : opOf α g₁ = some .getTS) (h2 : respOf α g₁ = some (.inl t₁))
    (h3 : opOf α g₂ = some .getTS) (h4 : respOf α g₂ = some (.inl t₂))
    (h5 : Precedes α g₁ g₂) : t₁ < t₂ :=
  (inv_run h hadm).order g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5

/-- **Lemma 5.1 (correctness).** Every one-shot execution of Algorithms 1 and 2 satisfies the
timestamp specification. -/
theorem correct (reread : Bool) :
    ∀ α, (alg n reread).Valid α → Adm true α → TSCorrect α := by
  rintro α ⟨C, h⟩ hadm
  have hI := inv_run h hadm
  constructor
  · intro g r h1 h2; exact hI.resp g _ r h1 h2
  · intro g₁ g₂ c t₁ t₂ o r h1 h2 h3 h4 h5 _ h7 h8
    have hlt := hI.order g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5
    have hr := hI.resp c o r h7 h8
    refine ⟨?_, ?_⟩
    · rintro rfl; simp only [RespOK] at hr; simp [hr, hlt]
    · rintro rfl; simp only [RespOK] at hr; simp only [hr, Sum.inr.injEq, decide_eq_false_iff_not,
        not_lt]; omega

/-- Algorithms 1 and 2 form a one-shot timestamp implementation (`IsTS … true`). -/
theorem isTS (reread : Bool) : IsTS (alg n reread) true where
  allowed _ _ := trivial
  correct := correct reread
  progress _ C p hα _ hp := Impl.WaitFree.obstructionFree _ (waitFree reread) C p ⟨_, hα⟩ hp

/-- **Lemma 5.1.** Algorithms 1 and 2 (`alg n reread`, either reading of `sum := sum + R[i]`)
constitute a wait-free implementation of one-shot timestamps for `n` processes from
`⌈n/2⌉ = (n+1)/2` registers, each of which only ever holds values in `{0, 1, 2}` in one-shot
executions. -/
theorem lemma_5_1 (reread : Bool) :
    IsTS (alg n reread) true ∧ (alg n reread).WaitFree ∧
      ∀ α C, (alg n reread).run α = some C → Adm true α → ∀ j, C.mem j ≤ 2 :=
  ⟨isTS reread, waitFree reread, fun _ _ h hadm j => mem_le_two h hadm j⟩

end Cslib.SharedMemory.Timestamp.SimpleTS
