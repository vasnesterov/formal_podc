import Papers.PODC2021.RegisterLinTermination.Alg4
import Podc.Computability.Distributed.SharedMemory.MWMRRegister
import Mathlib.Order.Prod.Lex.Basic

/-!
# Theorem 12: Algorithm 4 is linearizable

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Section 5 and
Appendix D.

We prove `alg4_linearizable`: for every value type `V`, initial value `v₀` and number `n ≥ 1` of
processes, Algorithm 4 (`alg4 V v₀ n`) is a linearizable implementation of an MWMR register.

## Proof

We apply the reads-from criterion for MWMR registers (`MWMRReadsFrom.isLinearization`) to

* `ws` = the writes that have already written their cell `Val[k]`, sorted by timestamp
  (`sortWs`), and
* `rf x` = `0` if the read `x` returned a cell with sequence number `0` (the initial value), and
  otherwise `1 +` the position in `ws` of the write whose timestamp `x` returned (`rfOf`).

The real-time conditions of the criterion are the paper's Corollary 58 and Lemmas 59–61; they are
derived from an invariant `Inv` of all executions, proved by induction over the execution
(`exists_inv`). The invariant carries a ghost list `W` of the writes that have written to `Val[-]`
and a ghost map `tok` giving the timestamp of each such write and the timestamp returned by each
read. Its main clauses:

* `Val[k]` holds a timestamp with process id `k`, and the timestamp of every write of `p_k` in `W`
  is at most that of `Val[k]` (timestamps in `Val[k]` only grow: `own_wr`); distinct writes have
  distinct timestamps (`W_inj`, the paper's Observation 51);
* every cell (in memory, or kept by a reader) holds either the initial value with sequence number
  `0`, or the value of the write in `W` with this timestamp (`Good`, Observations 52, 53);
* `prec`: if `a` precedes `b` in real time then the timestamp of `a` is *covered* by `b`: if `b`
  is a completed or written write then `tok a < tok b`, if `b` is a completed read then
  `tok a ≤ tok b`, and while `b` is still scanning `Val[-]`, `tok a` is below what `b` has seen or
  below a register `b` has still to read (`CoveredBy`). This is the paper's Lemma 50 and the core of
  Lemmas 59–61 ("timestamps in `Val[-]` are non-decreasing").
-/

namespace Podc.RegisterLinTermination.Alg4

open Cslib.SharedMemory List

set_option linter.unusedSectionVars false

variable {V : Type} {v₀ : V} {n : ℕ} [NeZero n]

/-! ## Timestamps -/

lemma tsLt_iff (a b : TS n) : tsLt a b = true ↔ toLex a < toLex b := by
  simp [tsLt, Prod.Lex.toLex_lt_toLex]

lemma fst_le_of_le {a b : TS n} (h : toLex a ≤ toLex b) : a.1 ≤ b.1 := by
  rcases Prod.Lex.toLex_le_toLex.1 h with h | h
  · exact h.le
  · exact h.1.le

lemma lt_of_fst_lt {a b : TS n} (h : a.1 < b.1) : toLex a < toLex b :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

lemma zero_le_ts (t : TS n) : toLex ((0, 0) : TS n) ≤ toLex t := by
  rw [Prod.Lex.toLex_le_toLex]
  rcases Nat.eq_zero_or_pos t.1 with h | h
  · right; exact ⟨h.symm, Fin.zero_le _⟩
  · left; exact h

/-- The cell kept by a reader that has kept `best` so far and reads `c`. -/
def pick (best c : Cell V n) : Cell V n := if tsLt best.2 c.2 then c else best

lemma pick_ge_left (best c : Cell V n) : toLex best.2 ≤ toLex (pick best c).2 := by
  unfold pick; split_ifs with h
  · exact ((tsLt_iff _ _).1 h).le
  · exact le_rfl

lemma pick_ge_right (best c : Cell V n) : toLex c.2 ≤ toLex (pick best c).2 := by
  unfold pick; split_ifs with h
  · exact le_rfl
  · exact not_lt.1 (fun h' => h ((tsLt_iff _ _).2 h'))

lemma pick_cases (best c : Cell V n) : pick best c = best ∨ pick best c = c := by
  unfold pick; split_ifs <;> simp

lemma next_eq_some {i j : Fin n} (h : next i = some j) : j.val = i.val + 1 := by
  unfold next at h; split_ifs at h with h1; cases h; rfl

lemma next_eq_none {i : Fin n} (h : next i = none) : i.val + 1 = n := by
  unfold next at h; split_ifs at h with h1; have := i.isLt; omega

/-! ## The invariant -/

/-- Histories of Algorithm 4. -/
abbrev Hist (V : Type) (v₀ : V) (n : ℕ) := List (Label (Fin n) (register V v₀))

/-- Configurations of Algorithm 4. -/
abbrev Cfg (V : Type) (v₀ : V) (n : ℕ) [NeZero n] :=
  Config (register V v₀) (base V v₀ n) (Fin n) (Loc V n)

/-- The high-level operation a local state belongs to. -/
def locOp : Loc V n → Option (RWOp V)
  | .idle => none
  | .wRead v _ _ => some (.write v)
  | .wWrite v _ => some (.write v)
  | .wRet v => some (.write v)
  | .rRead _ _ => some .read
  | .rRet _ => some .read

/-- A cell is *good*: it holds the initial value with sequence number `0`, or the value written
by the write of `W` with the cell's timestamp. -/
def Good (α : Hist V v₀ n) (W : List (OpId (Fin n))) (tok : OpId (Fin n) → TS n)
    (c : Cell V n) : Prop :=
  (c.2.1 = 0 ∧ c.1 = v₀) ∨ ∃ w ∈ W, tok w = c.2 ∧ opOf α w = some (.write c.1)

/-- The timestamp `t` is covered by a pending operation in local state `l` (with ghost timestamp
`tb`, memory `mem`): the operation will end up with a timestamp `> t` (writes) or `≥ t` (reads). -/
def CoveredBy (mem : Fin n → Cell V n) (tb t : TS n) : Loc V n → Prop
  | .idle => True
  | .wRead _ i m => t.1 ≤ m ∨ ∃ j, i ≤ j ∧ toLex t ≤ toLex (mem j).2
  | .wWrite _ m => t.1 ≤ m
  | .wRet _ => toLex t < toLex tb
  | .rRead i best => toLex t ≤ toLex best.2 ∨ ∃ j, i ≤ j ∧ toLex t ≤ toLex (mem j).2
  | .rRet _ => toLex t ≤ toLex tb

/-- The timestamp of `a` is covered by `b`. -/
def Covers (α : Hist V v₀ n) (C : Cfg V v₀ n) (tok : OpId (Fin n) → TS n)
    (a b : OpId (Fin n)) : Prop :=
  (Completed α b → (opOf α b = some .read → toLex (tok a) ≤ toLex (tok b)) ∧
      (∀ v, opOf α b = some (.write v) → toLex (tok a) < toLex (tok b))) ∧
    (¬ Completed α b → CoveredBy C.mem (tok b) (tok a) (C.loc b.1))

/-- The invariant of Algorithm 4, with ghost list `W` (writes that have written to `Val[-]`) and
ghost timestamps `tok`. -/
structure Inv (α : Hist V v₀ n) (C : Cfg V v₀ n) (W : List (OpId (Fin n)))
    (tok : OpId (Fin n) → TS n) : Prop where
  pend_eq : ∀ p, C.pend p = locOp (C.loc p)
  mem_pid : ∀ k, (C.mem k).2.2 = k
  own_rd : ∀ k v i m, C.loc k = .wRead v i m → k < i → (C.mem k).2.1 ≤ m
  own_wr : ∀ k v m, C.loc k = .wWrite v m → (C.mem k).2.1 ≤ m
  W_nodup : W.Nodup
  W_op : ∀ w ∈ W, ∃ v, opOf α w = some (.write v)
  W_tok : ∀ w ∈ W, (tok w).2 = w.1 ∧ toLex (tok w) ≤ toLex (C.mem w.1).2 ∧ 0 < (tok w).1
  W_pend : ∀ w ∈ W, ¬ Completed α w → ∃ v, C.loc w.1 = .wRet v
  W_complete : ∀ x v, opOf α x = some (.write v) → Completed α x → x ∈ W
  W_ret : ∀ p v, C.loc p = .wRet v → curOp α p ∈ W
  W_inj : ∀ w ∈ W, ∀ w' ∈ W, tok w = tok w' → w = w'
  mem_good : ∀ j, Good α W tok (C.mem j)
  rd_good : ∀ p i best, C.loc p = .rRead i best →
    Good α W tok best ∧ ∃ j, toLex best.2 ≤ toLex (C.mem j).2
  ret_good : ∀ p v, C.loc p = .rRet v →
    Good α W tok (v, tok (curOp α p)) ∧ ∃ j, toLex (tok (curOp α p)) ≤ toLex (C.mem j).2
  done_good : ∀ x v, opOf α x = some .read → respOf α x = some v → Good α W tok (v, tok x)
  done_mem : ∀ x, Completed α x → ∃ j, toLex (tok x) ≤ toLex (C.mem j).2
  write_resp : ∀ x v r, opOf α x = some (.write v) → respOf α x = some r → r = v
  prec : ∀ a b, Precedes α a b → Invoked α b → Covers α C tok a b

/-! ## Basic facts -/

section Basic

variable {α α' : Hist V v₀ n} {C : Cfg V v₀ n} {W W' : List (OpId (Fin n))}
  {tok tok' : OpId (Fin n) → TS n}

lemma Good.mono {c : Cell V n} (hop : ∀ x o, opOf α x = some o → opOf α' x = some o)
    (hW : ∀ w ∈ W, w ∈ W' ∧ tok' w = tok w) (h : Good α W tok c) : Good α' W' tok' c := by
  rcases h with h | ⟨w, hw, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, (hW w hw).1, by rw [(hW w hw).2, h1], hop _ _ h2⟩

lemma CoveredBy.mono {mem mem' : Fin n → Cell V n} {tb t : TS n} {l : Loc V n}
    (hm : ∀ j, toLex (mem j).2 ≤ toLex (mem' j).2) (h : CoveredBy mem tb t l) :
    CoveredBy mem' tb t l := by
  cases l with
  | idle => trivial
  | wRead v i m =>
    rcases h with h | ⟨j, hj, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, h.trans (hm j)⟩
  | wWrite v m => exact h
  | wRet v => exact h
  | rRead i best =>
    rcases h with h | ⟨j, hj, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, h.trans (hm j)⟩
  | rRet v => exact h

lemma locOp_eq_none {l : Loc V n} : locOp l = none ↔ l = .idle := by
  cases l <;> simp [locOp]

/-- An invoked, not completed instance is the pending operation of its process. -/
lemma pend_of_not_completed (hrun : (alg4 V v₀ n).run α = some C) {x : OpId (Fin n)}
    (hi : Invoked α x) (hc : ¬ Completed α x) : C.pend x.1 ≠ none ∧ x = curOp α x.1 := by
  simp only [Invoked, Completed, not_lt] at hi hc
  rcases (alg4 V v₀ n).run_counts hrun x.1 with ⟨-, h2⟩ | ⟨h1, h2⟩
  · omega
  · refine ⟨h1, ?_⟩
    obtain ⟨p, k⟩ := x
    simp only [curOp, Prod.mk.injEq, true_and]
    simp only at hi hc h2
    omega

/-- The operation of the current instance of a process is given by its local state. -/
lemma opOf_curOp (hrun : (alg4 V v₀ n).run α = some C) (h : Inv α C W tok) {p : Fin n}
    {o : RWOp V} (ho : locOp (C.loc p) = some o) : opOf α (curOp α p) = some o :=
  ((alg4 V v₀ n).run_pend_curOp hrun ((h.pend_eq p).trans ho)).2.2

lemma Inv.cur_not_mem (h : Inv α C W tok) (p : Fin n) (hp : ∀ v, C.loc p ≠ .wRet v) :
    curOp α p ∉ W := by
  intro hc
  obtain ⟨v, hv⟩ := h.W_pend _ hc (not_completed_curOp α p)
  exact hp v hv

end Basic

/-! ## Initial configuration -/

lemma inv_init : Inv ([] : Hist V v₀ n) (alg4 V v₀ n).initCfg [] (fun _ => (0, 0)) where
  pend_eq _ := rfl
  mem_pid _ := rfl
  own_rd _ _ _ _ h := by cases h
  own_wr _ _ _ h := by cases h
  W_nodup := nodup_nil
  W_op _ h := by cases h
  W_tok _ h := by cases h
  W_pend _ h := by cases h
  W_complete _ _ _ h := by simp [Completed] at h
  W_ret _ _ h := by cases h
  W_inj _ h := by cases h
  mem_good _ := Or.inl ⟨rfl, rfl⟩
  rd_good _ _ _ h := by cases h
  ret_good _ _ h := by cases h
  done_good _ _ _ h := by simp [respOf] at h
  done_mem _ h := by simp [Completed] at h
  write_resp _ _ _ _ h := by simp [respOf] at h
  prec _ _ h _ := absurd h.completed (by simp [Completed])

/-! ## Steps -/

section Steps

variable {α : Hist V v₀ n} {C C' : Cfg V v₀ n} {W : List (OpId (Fin n))}
  {tok : OpId (Fin n) → TS n}

/-- A local step of `p` (a read of `Val[i]` by a writer or a reader): the memory and `W` do not
change, the local state of `p` becomes `l'` and the ghost timestamp of `p`'s operation `t'`. -/
lemma inv_local (hrun : (alg4 V v₀ n).run α = some C) (h : Inv α C W tok) {p : Fin n}
    {l' : Loc V n} {t' : TS n} (hnret : ∀ v, C.loc p ≠ .wRet v)
    (hpend : C'.pend = C.pend) (hmem : C'.mem = C.mem)
    (hloc : C'.loc = Function.update C.loc p l') (hop : locOp l' = locOp (C.loc p))
    (hnret' : ∀ v, l' ≠ .wRet v)
    (hown_rd : ∀ v i m, l' = .wRead v i m → p < i → (C.mem p).2.1 ≤ m)
    (hown_wr : ∀ v m, l' = .wWrite v m → (C.mem p).2.1 ≤ m)
    (hrd : ∀ i best, l' = .rRead i best →
      Good α W tok best ∧ ∃ j, toLex best.2 ≤ toLex (C.mem j).2)
    (hret : ∀ v, l' = .rRet v → Good α W tok (v, t') ∧ ∃ j, toLex t' ≤ toLex (C.mem j).2)
    (hcov : ∀ t, CoveredBy C.mem (tok (curOp α p)) t (C.loc p) → CoveredBy C.mem t' t l') :
    Inv (α ++ [.tau p]) C' W (Function.update tok (curOp α p) t') := by
  have hcur : curOp α p ∉ W := h.cur_not_mem p hnret
  have htokW : ∀ w ∈ W, Function.update tok (curOp α p) t' w = tok w :=
    fun w hw => Function.update_of_ne (fun e => hcur (by rw [← e]; exact hw)) _ _
  have htokC : ∀ x, Completed α x → Function.update tok (curOp α p) t' x = tok x :=
    fun x hx => Function.update_of_ne (fun e => not_completed_curOp α p (by rw [← e]; exact hx)) _ _
  have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne hq]
  have hlocp : C'.loc p = l' := by rw [hloc, Function.update_self]
  have hcomp : ∀ x, Completed (α ++ [.tau p]) x ↔ Completed α x :=
    completed_append_of_not_ret (by simp)
  have hinvk : ∀ x, Invoked (α ++ [.tau p]) x ↔ Invoked α x := by intro x; simp [Invoked]
  have hresp : ∀ x, respOf (α ++ [.tau p]) x = respOf α x := respOf_append_of_not_ret (by simp)
  have hgood : ∀ c, Good α W tok c →
      Good (α ++ [.tau p]) W (Function.update tok (curOp α p) t') c :=
    fun c => Good.mono (fun x o hx => by simpa using hx) (fun w hw => ⟨hw, htokW w hw⟩)
  constructor
  · intro q; rcases eq_or_ne q p with rfl | hq
    · rw [hpend, hlocp, hop, h.pend_eq]
    · rw [hpend, hlocq q hq, h.pend_eq]
  · intro k; rw [hmem]; exact h.mem_pid k
  · intro k v i m hl hk; rw [hmem]
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl; exact hown_rd v i m hl hk
    · rw [hlocq k hq] at hl; exact h.own_rd k v i m hl hk
  · intro k v m hl; rw [hmem]
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl; exact hown_wr v m hl
    · rw [hlocq k hq] at hl; exact h.own_wr k v m hl
  · exact h.W_nodup
  · intro w hw; simpa using h.W_op w hw
  · intro w hw; rw [htokW w hw, hmem]; exact h.W_tok w hw
  · intro w hw hc
    rw [hcomp] at hc
    obtain ⟨v, hv⟩ := h.W_pend w hw hc
    have : w.1 ≠ p := fun e => hnret v (e ▸ hv)
    exact ⟨v, by rw [hlocq _ this]; exact hv⟩
  · intro x v hx hc; rw [hcomp] at hc; exact h.W_complete x v (by simpa using hx) hc
  · intro q v hl
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; exact absurd hl (hnret' v)
    · rw [hlocq q hq] at hl; simpa using h.W_ret q v hl
  · intro w hw w' hw' he
    rw [htokW w hw, htokW w' hw'] at he; exact h.W_inj w hw w' hw' he
  · intro j; rw [hmem]; exact hgood _ (h.mem_good j)
  · intro q i best hl
    rw [hmem]
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; obtain ⟨h1, h2⟩ := hrd i best hl; exact ⟨hgood _ h1, h2⟩
    · rw [hlocq q hq] at hl; obtain ⟨h1, h2⟩ := h.rd_good q i best hl; exact ⟨hgood _ h1, h2⟩
  · intro q v hl
    rw [curOp_append_tau, hmem]
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; rw [Function.update_self]
      obtain ⟨h1, h2⟩ := hret v hl; exact ⟨hgood _ h1, h2⟩
    · rw [hlocq q hq] at hl
      have hne : curOp α q ≠ curOp α p := fun e => hq (congrArg Prod.fst e)
      rw [Function.update_of_ne hne]
      obtain ⟨h1, h2⟩ := h.ret_good q v hl; exact ⟨hgood _ h1, h2⟩
  · intro x v hx hv
    rw [hresp] at hv; simp only [opOf_append_tau] at hx
    rw [htokC x (Completed.of_respOf_eq_some hv)]
    exact hgood _ (h.done_good x v hx hv)
  · intro x hx; rw [hcomp] at hx; rw [htokC x hx, hmem]; exact h.done_mem x hx
  · intro x v r hx hr
    rw [hresp] at hr; simp only [opOf_append_tau] at hx; exact h.write_resp x v r hx hr
  · intro a b hab hb
    have hab' := Precedes.of_concat_of_not_ret (by simp) hab
    rw [hinvk] at hb
    have hc := h.prec a b hab' hb
    have ha := htokC a hab'.completed
    refine ⟨fun hbc => ?_, fun hbc => ?_⟩
    · rw [hcomp] at hbc
      rw [ha, htokC b hbc]; simp only [opOf_append_tau]; exact hc.1 hbc
    · rw [hcomp] at hbc
      obtain ⟨-, hbcur⟩ := pend_of_not_completed hrun hb hbc
      have hc2 := hc.2 hbc
      rw [ha, hmem]
      rcases eq_or_ne b.1 p with hbp | hbp
      · have hb0 : b = curOp α p := hbcur.trans (by rw [hbp])
        subst hb0
        rw [Function.update_self, hlocp]
        exact hcov _ hc2
      · rw [hlocq _ hbp, Function.update_of_ne (fun e => hbp (by rw [e]))]
        exact hc2

/-- The write step of `p_k`: it writes `(v, ⟨m + 1, k⟩)` into `Val[k]`. -/
lemma inv_write (hrun : (alg4 V v₀ n).run α = some C) (h : Inv α C W tok) {p : Fin n} {v : V}
    {m : ℕ} (hl : C.loc p = .wWrite v m)
    (hpend : C'.pend = C.pend) (hmem : C'.mem = Function.update C.mem p (v, m + 1, p))
    (hloc : C'.loc = Function.update C.loc p (.wRet v)) :
    Inv (α ++ [.tau p]) C' (curOp α p :: W) (Function.update tok (curOp α p) (m + 1, p)) := by
  have hcur : curOp α p ∉ W := h.cur_not_mem p (by rw [hl]; simp)
  have hopc : opOf α (curOp α p) = some (.write v) := opOf_curOp hrun h (by rw [hl]; rfl)
  have hown := h.own_wr p v m hl
  have hmemp : C'.mem p = (v, m + 1, p) := by rw [hmem, Function.update_self]
  have hmemq : ∀ j, j ≠ p → C'.mem j = C.mem j := fun j hj => by rw [hmem, Function.update_of_ne hj]
  have hmono : ∀ j, toLex (C.mem j).2 ≤ toLex (C'.mem j).2 := by
    intro j
    rcases eq_or_ne j p with rfl | hj
    · rw [hmemp]; exact (lt_of_fst_lt (by simp; omega)).le
    · rw [hmemq j hj]
  set tok' := Function.update tok (curOp α p) (m + 1, p) with htok'
  have htokW : ∀ w ∈ W, tok' w = tok w :=
    fun w hw => Function.update_of_ne (fun e => hcur (by rw [← e]; exact hw)) _ _
  have htokC : ∀ x, Completed α x → tok' x = tok x :=
    fun x hx => Function.update_of_ne (fun e => not_completed_curOp α p (by rw [← e]; exact hx)) _ _
  have htokc : tok' (curOp α p) = (m + 1, p) := Function.update_self _ _ _
  have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne hq]
  have hlocp : C'.loc p = .wRet v := by rw [hloc, Function.update_self]
  have hcomp : ∀ x, Completed (α ++ [.tau p]) x ↔ Completed α x :=
    completed_append_of_not_ret (by simp)
  have hinvk : ∀ x, Invoked (α ++ [.tau p]) x ↔ Invoked α x := by intro x; simp [Invoked]
  have hresp : ∀ x, respOf (α ++ [.tau p]) x = respOf α x := respOf_append_of_not_ret (by simp)
  have hgood : ∀ c, Good α W tok c → Good (α ++ [.tau p]) (curOp α p :: W) tok' c :=
    fun c => Good.mono (fun x o hx => by simpa using hx)
      (fun w hw => ⟨mem_cons_of_mem _ hw, htokW w hw⟩)
  -- the new timestamp is larger than every timestamp of `W` of process `p`
  have hnew : ∀ w ∈ W, tok w ≠ (m + 1, p) := by
    intro w hw he
    obtain ⟨h1, h2, -⟩ := h.W_tok w hw
    rw [he] at h1 h2
    simp only at h1
    rw [← h1] at h2
    have := fst_le_of_le h2
    simp only at this
    omega
  constructor
  · intro q; rcases eq_or_ne q p with rfl | hq
    · rw [hpend, hlocp, h.pend_eq, hl]; rfl
    · rw [hpend, hlocq q hq, h.pend_eq]
  · intro k
    rcases eq_or_ne k p with rfl | hk
    · rw [hmemp]
    · rw [hmemq k hk]; exact h.mem_pid k
  · intro k v' i m' hl' hk
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl'; cases hl'
    · rw [hlocq k hq] at hl'; rw [hmemq k hq]; exact h.own_rd k v' i m' hl' hk
  · intro k v' m' hl'
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl'; cases hl'
    · rw [hlocq k hq] at hl'; rw [hmemq k hq]; exact h.own_wr k v' m' hl'
  · exact nodup_cons.2 ⟨hcur, h.W_nodup⟩
  · intro w hw
    rcases mem_cons.1 hw with rfl | hw
    · exact ⟨v, by simpa using hopc⟩
    · simpa using h.W_op w hw
  · intro w hw
    rcases mem_cons.1 hw with rfl | hw
    · rw [htokc]; exact ⟨rfl, by rw [hmemp], by omega⟩
    · rw [htokW w hw]
      obtain ⟨h1, h2, h3⟩ := h.W_tok w hw
      exact ⟨h1, h2.trans (hmono _), h3⟩
  · intro w hw hc
    rw [hcomp] at hc
    rcases mem_cons.1 hw with rfl | hw
    · exact ⟨v, hlocp⟩
    · obtain ⟨v', hv'⟩ := h.W_pend w hw hc
      have : w.1 ≠ p := fun e => by rw [e, hl] at hv'; cases hv'
      exact ⟨v', by rw [hlocq _ this]; exact hv'⟩
  · intro x v' hx hc; rw [hcomp] at hc
    exact mem_cons_of_mem _ (h.W_complete x v' (by simpa using hx) hc)
  · intro q v' hl'
    rw [curOp_append_tau]
    rcases eq_or_ne q p with rfl | hq
    · exact mem_cons_self
    · rw [hlocq q hq] at hl'; exact mem_cons_of_mem _ (h.W_ret q v' hl')
  · intro w hw w' hw' he
    rcases mem_cons.1 hw with rfl | hw <;> rcases mem_cons.1 hw' with rfl | hw'
    · rfl
    · rw [htokc, htokW w' hw'] at he; exact absurd he.symm (hnew w' hw')
    · rw [htokc, htokW w hw] at he; exact absurd he (hnew w hw)
    · rw [htokW w hw, htokW w' hw'] at he; exact h.W_inj w hw w' hw' he
  · intro j
    rcases eq_or_ne j p with rfl | hj
    · rw [hmemp]; exact Or.inr ⟨curOp α j, mem_cons_self, htokc, by simpa using hopc⟩
    · rw [hmemq j hj]; exact hgood _ (h.mem_good j)
  · intro q i best hl'
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl'; cases hl'
    · rw [hlocq q hq] at hl'
      obtain ⟨h1, j, h2⟩ := h.rd_good q i best hl'
      exact ⟨hgood _ h1, j, h2.trans (hmono j)⟩
  · intro q v' hl'
    rw [curOp_append_tau]
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl'; cases hl'
    · rw [hlocq q hq] at hl'
      have hne : curOp α q ≠ curOp α p := fun e => hq (congrArg Prod.fst e)
      rw [htok', Function.update_of_ne hne]
      obtain ⟨h1, j, h2⟩ := h.ret_good q v' hl'
      exact ⟨hgood _ h1, j, h2.trans (hmono j)⟩
  · intro x v' hx hv
    rw [hresp] at hv; simp only [opOf_append_tau] at hx
    rw [htokC x (Completed.of_respOf_eq_some hv)]
    exact hgood _ (h.done_good x v' hx hv)
  · intro x hx; rw [hcomp] at hx; rw [htokC x hx]
    obtain ⟨j, hj⟩ := h.done_mem x hx
    exact ⟨j, hj.trans (hmono j)⟩
  · intro x v' r hx hr
    rw [hresp] at hr; simp only [opOf_append_tau] at hx; exact h.write_resp x v' r hx hr
  · intro a b hab hb
    have hab' := Precedes.of_concat_of_not_ret (by simp) hab
    rw [hinvk] at hb
    have hc := h.prec a b hab' hb
    have ha := htokC a hab'.completed
    refine ⟨fun hbc => ?_, fun hbc => ?_⟩
    · rw [hcomp] at hbc
      rw [ha, htokC b hbc]; simp only [opOf_append_tau]; exact hc.1 hbc
    · rw [hcomp] at hbc
      obtain ⟨-, hbcur⟩ := pend_of_not_completed hrun hb hbc
      have hc2 := hc.2 hbc
      rw [ha]
      rcases eq_or_ne b.1 p with hbp | hbp
      · have hb0 : b = curOp α p := hbcur.trans (by rw [hbp])
        subst hb0
        rw [htokc, hlocp]
        rw [hl] at hc2
        exact lt_of_fst_lt (show (tok a).1 < m + 1 from Nat.lt_succ_of_le hc2)
      · rw [hlocq _ hbp, htok', Function.update_of_ne (fun e => hbp (by rw [e]))]
        exact hc2.mono hmono

lemma inv_step_inv (hrun : (alg4 V v₀ n).run α = some C) (h : Inv α C W tok) {p : Fin n}
    {o : RWOp V} (hs : (alg4 V v₀ n).step C (.inv p o) = some C') :
    Inv (α ++ [.inv p o]) C' W tok := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hwf : WellFormed α := Impl.Valid.wellFormed _ ⟨C, hrun⟩
  have hlp : C.loc p = .idle := locOp_eq_none.1 ((h.pend_eq p).symm.trans hp)
  have hcnt : (opsOf α p).length = (respsOf α p).length := (alg4 V v₀ n).run_idle_counts hrun hp
  have hlocp : C'.loc p = invoke v₀ o := by rw [hloc, Function.update_self]; rfl
  have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne hq]
  have hpendp : C'.pend p = some o := by rw [hpend, Function.update_self]
  have hpendq : ∀ q, q ≠ p → C'.pend q = C.pend q := fun q hq => by
    rw [hpend, Function.update_of_ne hq]
  have hop : ∀ x o', opOf α x = some o' → opOf (α ++ [.inv p o]) x = some o' :=
    fun x o' hx => opOf_append_of_eq_some hx _
  have hresp : ∀ x, respOf (α ++ [.inv p o]) x = respOf α x := respOf_append_of_not_ret (by simp)
  have hcomp : ∀ x, Completed (α ++ [.inv p o]) x ↔ Completed α x :=
    completed_append_of_not_ret (by simp)
  have hgood : ∀ c, Good α W tok c → Good (α ++ [.inv p o]) W tok c :=
    fun c => Good.mono hop (fun w hw => ⟨hw, rfl⟩)
  have hopC : ∀ x o', Completed α x → opOf (α ++ [.inv p o]) x = some o' → opOf α x = some o' := by
    intro x o' hc hx
    rwa [opOf_append_of_invoked (hwf.invoked_of_completed hc)] at hx
  have hinvk : ∀ x, Invoked (α ++ [.inv p o]) x → Invoked α x ∨ x = (p, (opsOf α p).length) := by
    intro x hx
    by_cases hi : Invoked α x
    · exact Or.inl hi
    · right
      obtain ⟨q, k⟩ := x
      simp only [Invoked, opsOf_concat, length_append, not_lt] at hx hi
      by_cases hq : p = q
      · subst hq; simp at hx; simp only [Prod.mk.injEq, true_and]; omega
      · simp [hq] at hx; omega
  have hx0nc : ¬ Completed α (p, (opsOf α p).length) := by simp [Completed, hcnt]
  constructor
  · intro q; rcases eq_or_ne q p with rfl | hq
    · rw [hpendp, hlocp]; cases o <;> rfl
    · rw [hpendq q hq, hlocq q hq]; exact h.pend_eq q
  · intro k; rw [hmem]; exact h.mem_pid k
  · intro k v i m hl hk
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl
      cases o with
      | read => cases hl
      | write v' => simp only [invoke, Loc.wRead.injEq] at hl; obtain ⟨-, rfl, -⟩ := hl
                    exact absurd hk (not_lt.2 (Fin.zero_le _))
    · rw [hlocq k hq] at hl; rw [hmem]; exact h.own_rd k v i m hl hk
  · intro k v m hl
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl; cases o <;> cases hl
    · rw [hlocq k hq] at hl; rw [hmem]; exact h.own_wr k v m hl
  · exact h.W_nodup
  · intro w hw; obtain ⟨v, hv⟩ := h.W_op w hw; exact ⟨v, hop _ _ hv⟩
  · intro w hw; rw [hmem]; exact h.W_tok w hw
  · intro w hw hc
    rw [hcomp] at hc
    obtain ⟨v, hv⟩ := h.W_pend w hw hc
    have : w.1 ≠ p := fun e => by rw [e, hlp] at hv; cases hv
    exact ⟨v, by rw [hlocq _ this]; exact hv⟩
  · intro x v hx hc; rw [hcomp] at hc; exact h.W_complete x v (hopC x _ hc hx) hc
  · intro q v hl
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; cases o <;> cases hl
    · rw [hlocq q hq] at hl; rw [curOp_append_inv]; exact h.W_ret q v hl
  · exact h.W_inj
  · intro j; rw [hmem]; exact hgood _ (h.mem_good j)
  · intro q i best hl
    rw [hmem]
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl
      cases o with
      | read =>
        simp only [invoke, Loc.rRead.injEq] at hl; obtain ⟨-, rfl⟩ := hl
        exact ⟨Or.inl ⟨rfl, rfl⟩, 0, zero_le_ts _⟩
      | write v' => cases hl
    · rw [hlocq q hq] at hl; obtain ⟨h1, h2⟩ := h.rd_good q i best hl; exact ⟨hgood _ h1, h2⟩
  · intro q v hl
    rw [hmem, curOp_append_inv]
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; cases o <;> cases hl
    · rw [hlocq q hq] at hl; obtain ⟨h1, h2⟩ := h.ret_good q v hl; exact ⟨hgood _ h1, h2⟩
  · intro x v hx hv
    rw [hresp] at hv
    exact hgood _ (h.done_good x v (hopC x _ (Completed.of_respOf_eq_some hv) hx) hv)
  · intro x hx; rw [hcomp] at hx; rw [hmem]; exact h.done_mem x hx
  · intro x v r hx hr
    rw [hresp] at hr
    exact h.write_resp x v r (hopC x _ (Completed.of_respOf_eq_some hr) hx) hr
  · intro a b hab hb
    rcases hinvk b hb with hb | rfl
    · have hab' : Precedes α a b := hab.of_append_of_invoked hb
      have hc := h.prec a b hab' hb
      refine ⟨fun hbc => ?_, fun hbc => ?_⟩
      · rw [hcomp] at hbc
        rw [opOf_append_of_invoked hb]; exact hc.1 hbc
      · rw [hcomp] at hbc
        obtain ⟨hpb, -⟩ := pend_of_not_completed hrun hb hbc
        have hbp : b.1 ≠ p := fun e => hpb (by rw [e]; exact hp)
        rw [hmem, hlocq _ hbp]; exact hc.2 hbc
    · have ha : Completed α a := precedes_append_inv_iff.1 hab
      refine ⟨fun hbc => absurd ((hcomp _).1 hbc) hx0nc, fun _ => ?_⟩
      obtain ⟨j, hj⟩ := h.done_mem a ha
      show CoveredBy C'.mem _ (tok a) (C'.loc p)
      rw [hlocp, hmem]
      cases o with
      | read => exact Or.inr ⟨j, Fin.zero_le _, hj⟩
      | write v => exact Or.inr ⟨j, Fin.zero_le _, hj⟩

lemma inv_step_ret (hrun : (alg4 V v₀ n).run α = some C) (h : Inv α C W tok) {p : Fin n}
    {r : V} (hs : (alg4 V v₀ n).step C (.ret p r) = some C') :
    Inv (α ++ [.ret p r]) C' W tok := by
  obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  have hcase : (C.loc p = .wRet r ∨ C.loc p = .rRet r) ∧ l = .idle := by
    cases hl : C.loc p with
    | idle => exact absurd (by rw [h.pend_eq, hl]; rfl) hp
    | wRet v =>
      rw [hl] at hact; simp only [alg4, act, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact; exact ⟨Or.inl rfl, rfl⟩
    | rRet v =>
      rw [hl] at hact; simp only [alg4, act, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact; exact ⟨Or.inr rfl, rfl⟩
    | wRead v i m => rw [hl] at hact; cases hact
    | wWrite v m => rw [hl] at hact; cases hact
    | rRead i best => rw [hl] at hact; cases hact
  obtain ⟨hlp, rfl⟩ := hcase
  have hopw : C.loc p = .wRet r → opOf α (curOp α p) = some (.write r) :=
    fun e => opOf_curOp hrun h (by rw [e]; rfl)
  have hopr : C.loc p = .rRet r → opOf α (curOp α p) = some .read :=
    fun e => opOf_curOp hrun h (by rw [e]; rfl)
  have hlocp : C'.loc p = .idle := by rw [hloc, Function.update_self]
  have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne hq]
  have hcomp : ∀ x, Completed (α ++ [.ret p r]) x ↔ Completed α x ∨ x = curOp α p :=
    completed_append_ret
  have hinvk : ∀ x, Invoked (α ++ [.ret p r]) x ↔ Invoked α x := by intro x; simp [Invoked]
  have hcurq : ∀ q, q ≠ p → curOp (α ++ [.ret p r]) q = curOp α q :=
    fun q hq => curOp_append_ret_of_ne _ _ (Ne.symm hq)
  have hgood : ∀ c, Good α W tok c → Good (α ++ [.ret p r]) W tok c :=
    fun c => Good.mono (fun x o hx => by simpa using hx) (fun w hw => ⟨hw, rfl⟩)
  constructor
  · intro q; rcases eq_or_ne q p with rfl | hq
    · rw [hpend, Function.update_self, hlocp]; rfl
    · rw [hpend, Function.update_of_ne hq, hlocq q hq]; exact h.pend_eq q
  · intro k; rw [hmem]; exact h.mem_pid k
  · intro k v i m hl hk
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl; cases hl
    · rw [hlocq k hq] at hl; rw [hmem]; exact h.own_rd k v i m hl hk
  · intro k v m hl
    rcases eq_or_ne k p with rfl | hq
    · rw [hlocp] at hl; cases hl
    · rw [hlocq k hq] at hl; rw [hmem]; exact h.own_wr k v m hl
  · exact h.W_nodup
  · intro w hw; simpa using h.W_op w hw
  · intro w hw; rw [hmem]; exact h.W_tok w hw
  · intro w hw hc
    rw [hcomp, not_or] at hc
    obtain ⟨v, hv⟩ := h.W_pend w hw hc.1
    obtain ⟨v', hv'⟩ := h.W_op w hw
    have : w.1 ≠ p := fun e => hc.2 (by
      rw [(pend_of_not_completed hrun (Invoked.of_opOf_eq_some hv') hc.1).2, e])
    exact ⟨v, by rw [hlocq _ this]; exact hv⟩
  · intro x v hx hc
    simp only [opOf_append_ret] at hx
    rcases (hcomp x).1 hc with hc | rfl
    · exact h.W_complete x v hx hc
    · rcases hlp with e | e
      · exact h.W_ret p r e
      · rw [hopr e] at hx; cases hx
  · intro q v hl
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; cases hl
    · rw [hlocq q hq] at hl; rw [hcurq q hq]; exact h.W_ret q v hl
  · exact h.W_inj
  · intro j; rw [hmem]; exact hgood _ (h.mem_good j)
  · intro q i best hl
    rw [hmem]
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; cases hl
    · rw [hlocq q hq] at hl; obtain ⟨h1, h2⟩ := h.rd_good q i best hl; exact ⟨hgood _ h1, h2⟩
  · intro q v hl
    rw [hmem]
    rcases eq_or_ne q p with rfl | hq
    · rw [hlocp] at hl; cases hl
    · rw [hlocq q hq] at hl; rw [hcurq q hq]
      obtain ⟨h1, h2⟩ := h.ret_good q v hl; exact ⟨hgood _ h1, h2⟩
  · intro x v hx hv
    simp only [opOf_append_ret] at hx
    rw [respOf_append_ret] at hv
    split_ifs at hv with hx0
    · cases hv
      subst hx0
      rcases hlp with e | e
      · rw [hopw e] at hx; cases hx
      · exact hgood _ (h.ret_good p r e).1
    · exact hgood _ (h.done_good x v hx hv)
  · intro x hx
    rw [hmem]
    rcases (hcomp x).1 hx with hx | rfl
    · exact h.done_mem x hx
    · rcases hlp with e | e
      · exact ⟨p, (h.W_tok _ (h.W_ret p r e)).2.1⟩
      · exact (h.ret_good p r e).2
  · intro x v r' hx hr
    simp only [opOf_append_ret] at hx
    rw [respOf_append_ret] at hr
    split_ifs at hr with hx0
    · cases hr
      subst hx0
      rcases hlp with e | e
      · rw [hopw e] at hx; cases hx; rfl
      · rw [hopr e] at hx; cases hx
    · exact h.write_resp x v r' hx hr
  · intro a b hab hb
    rw [hinvk] at hb
    have hab' : Precedes α a b := by
      rcases precedes_concat hab with h1 | ⟨-, h2⟩
      · exact h1
      · exact absurd ((hinvk b).2 hb) h2
    have hc := h.prec a b hab' hb
    refine ⟨fun hbc => ?_, fun hbc => ?_⟩
    · simp only [opOf_append_ret]
      rcases (hcomp b).1 hbc with hbc | rfl
      · exact hc.1 hbc
      · have hc2 : CoveredBy C.mem (tok (curOp α p)) (tok a) (C.loc p) :=
          hc.2 (not_completed_curOp α p)
        rcases hlp with e | e
        · rw [e] at hc2
          refine ⟨fun hr => ?_, fun v _ => hc2⟩
          rw [hopw e] at hr; cases hr
        · rw [e] at hc2
          refine ⟨fun _ => hc2, fun v hv => ?_⟩
          rw [hopr e] at hv; cases hv
    · rw [hcomp, not_or] at hbc
      obtain ⟨-, hbcur⟩ := pend_of_not_completed hrun hb hbc.1
      have hbp : b.1 ≠ p := fun e => hbc.2 (by rw [hbcur, e])
      rw [hmem, hlocq _ hbp]; exact hc.2 hbc.1

lemma inv_step_tau (hrun : (alg4 V v₀ n).run α = some C) (h : Inv α C W tok) {p : Fin n}
    (hs : (alg4 V v₀ n).step C (.tau p) = some C') :
    ∃ W' tok', Inv (α ++ [.tau p]) C' W' tok' := by
  have hp : C.pend p ≠ none := (Impl.step_tau hs).1
  have hle_i : ∀ i j : Fin n, next i = none → i ≤ j → j = i := by
    intro i j hn hij
    have := next_eq_none hn
    have := j.isLt
    rw [Fin.le_def] at hij
    exact Fin.ext (by omega)
  have hle_s : ∀ i j k : Fin n, next i = some j → i ≤ k → k = i ∨ j ≤ k := by
    intro i j k hn hik
    have := next_eq_some hn
    rw [Fin.le_def] at hik
    rcases Nat.lt_or_ge i.val k.val with h1 | h1
    · right; rw [Fin.le_def]; omega
    · left; exact Fin.ext (by omega)
  cases hl : C.loc p with
  | idle => exfalso; rw [h.pend_eq, hl] at hp; exact hp rfl
  | wRet v =>
    exfalso; obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
    rw [hl] at hact; cases hact
  | rRet v =>
    exfalso; obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
    rw [hl] at hact; cases hact
  | wWrite v m =>
    have hact : (alg4 V v₀ n).act p (C.loc p) =
        .access p (.write (v, m + 1, p)) (fun _ => .wRet v) := by rw [hl]; rfl
    rw [Impl.step_tau_eq_some hp hact] at hs
    obtain rfl := Option.some.inj hs
    exact ⟨_, _, inv_write hrun h hl rfl rfl rfl⟩
  | wRead v i m =>
    have hact : (alg4 V v₀ n).act p (C.loc p) = .access i .read (fun c =>
        match next i with
        | some j => .wRead v j (max m c.2.1)
        | none => .wWrite v (max m c.2.1)) := by rw [hl]; rfl
    rw [Impl.step_tau_eq_some hp hact] at hs
    obtain rfl := Option.some.inj hs
    have hown := h.own_rd p v i m hl
    refine ⟨W, tok, ?_⟩
    rw [← Function.update_eq_self (curOp α p) tok]
    cases hn : next i with
    | none =>
      refine inv_local (l' := .wWrite v (max m (C.mem i).2.1)) hrun h (by rw [hl]; simp) rfl
        (by simp) (by simp) (by rw [hl]; rfl) (by simp) (by simp) ?_ (by simp) (by simp) ?_
      · rintro v' m' he
        simp only [Loc.wWrite.injEq] at he
        obtain ⟨-, rfl⟩ := he
        have hpi : p ≤ i := by
          have := next_eq_none hn; have := p.isLt; rw [Fin.le_def]; omega
        rcases lt_or_eq_of_le hpi with hpi | rfl
        · exact (hown hpi).trans (le_max_left _ _)
        · exact le_max_right _ _
      · intro t ht
        rw [hl] at ht
        rcases ht with ht | ⟨j, hj, ht⟩
        · exact ht.trans (le_max_left _ _)
        · rw [hle_i i j hn hj] at ht
          exact (fst_le_of_le ht).trans (le_max_right _ _)
    | some j =>
      have hj := next_eq_some hn
      refine inv_local (l' := .wRead v j (max m (C.mem i).2.1)) hrun h (by rw [hl]; simp) rfl
        (by simp) (by simp) (by rw [hl]; rfl) (by simp) ?_ (by simp) (by simp) (by simp) ?_
      · rintro v' j' m' he hpj
        simp only [Loc.wRead.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [Fin.lt_def, hj] at hpj
        rcases Nat.lt_or_ge p.val i.val with hpi | hpi
        · exact (hown (Fin.lt_def.2 hpi)).trans (le_max_left _ _)
        · have : p = i := Fin.ext (by omega)
          subst this; exact le_max_right _ _
      · intro t ht
        rw [hl] at ht
        rcases ht with ht | ⟨k, hk, ht⟩
        · exact Or.inl (ht.trans (le_max_left _ _))
        · rcases hle_s i j k hn hk with rfl | hk'
          · exact Or.inl ((fst_le_of_le ht).trans (le_max_right _ _))
          · exact Or.inr ⟨k, hk', ht⟩
  | rRead i best =>
    have hact : (alg4 V v₀ n).act p (C.loc p) = .access i .read (fun c =>
        match next i with
        | some j => .rRead j (pick best c)
        | none => .rRet (pick best c).1) := by rw [hl]; rfl
    rw [Impl.step_tau_eq_some hp hact] at hs
    obtain rfl := Option.some.inj hs
    obtain ⟨hgb, jb, hjb⟩ := h.rd_good p i best hl
    -- the new kept cell is good and below the memory
    have hpk : Good α W tok (pick best (C.mem i)) ∧
        ∃ j, toLex (pick best (C.mem i)).2 ≤ toLex (C.mem j).2 := by
      rcases pick_cases best (C.mem i) with he | he <;> rw [he]
      · exact ⟨hgb, jb, hjb⟩
      · exact ⟨h.mem_good i, i, le_rfl⟩
    have hcov : ∀ t, CoveredBy C.mem (tok (curOp α p)) t (C.loc p) →
        toLex t ≤ toLex (pick best (C.mem i)).2 ∨ ∃ k, i < k ∧ toLex t ≤ toLex (C.mem k).2 := by
      intro t ht
      rw [hl] at ht
      rcases ht with ht | ⟨k, hk, ht⟩
      · exact Or.inl (ht.trans (pick_ge_left _ _))
      · rcases lt_or_eq_of_le hk with hk | rfl
        · exact Or.inr ⟨k, hk, ht⟩
        · exact Or.inl (ht.trans (pick_ge_right _ _))
    cases hn : next i with
    | none =>
      refine ⟨W, _, inv_local (l' := .rRet (pick best (C.mem i)).1)
        (t' := (pick best (C.mem i)).2) hrun h (by rw [hl]; simp) rfl
        (by simp) (by simp) (by rw [hl]; rfl) (by simp) (by simp) (by simp) (by simp) ?_ ?_⟩
      · rintro v' he
        simp only [Loc.rRet.injEq] at he
        subst he
        exact hpk
      · intro t ht
        rcases hcov t ht with ht | ⟨k, hk, ht⟩
        · exact ht
        · exfalso
          have := next_eq_none hn
          have := k.isLt
          rw [Fin.lt_def] at hk
          omega
    | some j =>
      have hj := next_eq_some hn
      refine ⟨W, tok, ?_⟩
      rw [← Function.update_eq_self (curOp α p) tok]
      refine inv_local (l' := .rRead j (pick best (C.mem i))) hrun h (by rw [hl]; simp) rfl
        (by simp) (by simp) (by rw [hl]; rfl) (by simp) (by simp) (by simp) ?_ (by simp) ?_
      · rintro j' b he
        simp only [Loc.rRead.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hpk
      · intro t ht
        rcases hcov t ht with ht | ⟨k, hk, ht⟩
        · exact Or.inl ht
        · refine Or.inr ⟨k, ?_, ht⟩
          rw [Fin.lt_def] at hk; rw [Fin.le_def]; omega

end Steps

lemma exists_inv {α : Hist V v₀ n} {C : Cfg V v₀ n} (hrun : (alg4 V v₀ n).run α = some C) :
    ∃ W tok, Inv α C W tok := by
  refine (alg4 V v₀ n).run_induction (Q := fun α C => ∃ W tok, Inv α C W tok)
    ⟨_, _, inv_init⟩ ?_ hrun
  rintro α C ℓ C' hα ⟨W, tok, h⟩ hs
  cases ℓ with
  | inv p o => exact ⟨W, tok, inv_step_inv hα h hs⟩
  | ret p r => exact ⟨W, tok, inv_step_ret hα h hs⟩
  | tau p => exact inv_step_tau hα h hs

/-! ## The linearization -/

/-- The written writes sorted by timestamp. -/
noncomputable def sortWs (W : List (OpId (Fin n))) (tok : OpId (Fin n) → TS n) :
    List (OpId (Fin n)) :=
  W.mergeSort (fun a b => decide (toLex (tok a) ≤ toLex (tok b)))

/-- The reads-from map: `0` for reads returning sequence number `0`, otherwise `1 +` the position
of the write with the returned timestamp. -/
def rfOf (ws : List (OpId (Fin n))) (tok : OpId (Fin n) → TS n) (x : OpId (Fin n)) : ℕ :=
  if (tok x).1 = 0 then 0 else ws.findIdx (fun w => decide (tok w = tok x)) + 1

section Sorted

variable {ws : List (OpId (Fin n))} {tok : OpId (Fin n) → TS n}
  (hs : ws.Pairwise (fun a b => toLex (tok a) ≤ toLex (tok b))) (hnd : ws.Nodup)
  (hinj : ∀ a ∈ ws, ∀ b ∈ ws, tok a = tok b → a = b)
include hs hnd hinj

lemma idx_eq_of_tok_eq {i j : ℕ} (hi : i < ws.length) (hj : j < ws.length)
    (h : tok ws[i] = tok ws[j]) : i = j :=
  (hnd.getElem_inj_iff).1 (hinj _ (getElem_mem hi) _ (getElem_mem hj) h)

lemma idx_lt_of_tok_lt {i j : ℕ} (hi : i < ws.length) (hj : j < ws.length)
    (h : toLex (tok ws[i]) < toLex (tok ws[j])) : i < j := by
  by_contra hc
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact absurd (pairwise_iff_getElem.1 hs j i hj hi hlt) (not_le.2 h)
  · have : i = j := by omega
    subst this; exact lt_irrefl _ h

lemma findIdx_tok {i : ℕ} (hi : i < ws.length) :
    ws.findIdx (fun w => decide (tok w = tok ws[i])) = i := by
  rw [findIdx_eq hi]
  refine ⟨by simp, fun j hji => ?_⟩
  have := idx_eq_of_tok_eq hs hnd hinj (show j < ws.length by omega) hi
  simp only [decide_eq_false_iff_not]
  intro h; have := this h; omega

end Sorted

/-- The invariant gives the hypotheses of the MWMR reads-from criterion. -/
theorem Inv.readsFrom {α : Hist V v₀ n} {C : Cfg V v₀ n} {W : List (OpId (Fin n))}
    {tok : OpId (Fin n) → TS n} (hrun : (alg4 V v₀ n).run α = some C) (h : Inv α C W tok) :
    MWMRReadsFrom α (sortWs W tok) (rfOf (sortWs W tok) tok) := by
  set ws := sortWs W tok with hws_def
  have hperm : ws.Perm W := mergeSort_perm _ _
  have hmem : ∀ x, x ∈ ws ↔ x ∈ W := fun x => hperm.mem_iff
  have hnd : ws.Nodup := hperm.nodup_iff.2 h.W_nodup
  have hs : ws.Pairwise (fun a b => toLex (tok a) ≤ toLex (tok b)) := by
    have := pairwise_mergeSort (le := fun a b => decide (toLex (tok a) ≤ toLex (tok b)))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
      (fun a b => by simpa using le_total _ _) W
    simp only [decide_eq_true_eq] at this
    exact this
  have hinj : ∀ a ∈ ws, ∀ b ∈ ws, tok a = tok b → a = b :=
    fun a ha b hb => h.W_inj a ((hmem a).1 ha) b ((hmem b).1 hb)
  have hpos : ∀ i (hi : i < ws.length), 0 < (tok ws[i]).1 :=
    fun i hi => (h.W_tok _ ((hmem _).1 (getElem_mem hi))).2.2
  have hwf : WellFormed α := Impl.Valid.wellFormed _ ⟨C, hrun⟩
  -- the lookup of a completed read
  have hlook : ∀ x, opOf α x = some .read → Completed α x → (tok x).1 ≠ 0 →
      ∃ k, ∃ hk : k < ws.length, tok ws[k] = tok x ∧ rfOf ws tok x = k + 1 ∧
        respOf α x = some (wsVal α ws (k + 1)) := by
    intro x hx hc h0
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
    rcases h.done_good x v hx hv with ⟨h1, -⟩ | ⟨w, hw, h1, h2⟩
    · exact absurd h1 h0
    · obtain ⟨k, hk, rfl⟩ := getElem_of_mem ((hmem w).2 hw)
      have h1' : tok ws[k] = tok x := h1
      refine ⟨k, hk, h1', ?_, ?_⟩
      · rw [rfOf, ite_eq_right_of_eq_false _ _ (eq_false h0), ← h1', findIdx_tok hs hnd hinj hk]
      · rw [hv]; simp [wsVal, getElem?_eq_getElem hk, h2]
  have hinvW : ∀ i (hi : i < ws.length), Invoked α ws[i] := fun i hi => by
    obtain ⟨v, hv⟩ := h.W_op _ ((hmem _).1 (getElem_mem hi)); exact Invoked.of_opOf_eq_some hv
  -- Lemma 50 / Corollary 58 and Lemma 59: what precedes a written write has a smaller timestamp
  have hW_after : ∀ a i (hi : i < ws.length), Precedes α a ws[i] →
      toLex (tok a) < toLex (tok ws[i]) := by
    intro a i hi hab
    have hc := h.prec a _ hab (hinvW i hi)
    obtain ⟨v, hv⟩ := h.W_op _ ((hmem _).1 (getElem_mem hi))
    by_cases hcomp : Completed α ws[i]
    · exact (hc.1 hcomp).2 v hv
    · obtain ⟨v', hv'⟩ := h.W_pend _ ((hmem _).1 (getElem_mem hi)) hcomp
      have := hc.2 hcomp
      rw [hv'] at this; exact this
  -- Lemmas 60, 61: what precedes a completed read has a timestamp at most the returned one
  have hR_after : ∀ a x, opOf α x = some .read → Completed α x → Precedes α a x →
      toLex (tok a) ≤ toLex (tok x) := by
    intro a x hx hxc hab
    exact ((h.prec a x hab (Invoked.of_opOf_eq_some hx)).1 hxc).1 hx
  refine ⟨hwf, hnd, fun x hx => h.W_op x ((hmem x).1 hx),
    fun x v hv hc => (hmem x).2 (h.W_complete x v hv hc), h.write_resp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- read_le
    intro x hx hc
    by_cases h0 : (tok x).1 = 0
    · simp [rfOf, h0]
    · obtain ⟨k, hk, -, hrf, -⟩ := hlook x hx hc h0
      omega
  · -- read_val
    intro x hx hc
    by_cases h0 : (tok x).1 = 0
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
      rcases h.done_good x v hx hv with ⟨-, h1⟩ | ⟨w, hw, h1, -⟩
      · rw [hv, rfOf, ite_eq_left_of_eq_true _ _ (eq_true h0)]; exact congrArg some h1
      · exfalso
        have h2 := (h.W_tok w hw).2.2
        have h3 : (tok w).1 = (tok x).1 := congrArg Prod.fst h1
        omega
    · obtain ⟨k, hk, -, hrf, hval⟩ := hlook x hx hc h0
      rw [hrf]; exact hval
  · -- ww
    intro i j hi hj hij
    exact idx_lt_of_tok_lt hs hnd hinj hi hj (hW_after _ j hj hij)
  · -- wr
    intro i hi x hx hxc hix
    have hle := hR_after _ x hx hxc hix
    have h0 : (tok x).1 ≠ 0 := by have := fst_le_of_le hle; have := hpos i hi; omega
    obtain ⟨k, hk, htk, hrf, -⟩ := hlook x hx hxc h0
    rw [hrf]; rw [← htk] at hle
    rcases hle.lt_or_eq with hlt | heq
    · have := idx_lt_of_tok_lt hs hnd hinj hi hk hlt; omega
    · have := idx_eq_of_tok_eq hs hnd hinj hi hk (toLex.injective heq); omega
  · -- rw
    intro x i hi hx hxc hxi
    have hlt := hW_after x i hi hxi
    by_cases h0 : (tok x).1 = 0
    · simp [rfOf, h0]
    · obtain ⟨k, hk, htk, hrf, -⟩ := hlook x hx hxc h0
      rw [hrf]; rw [← htk] at hlt
      have := idx_lt_of_tok_lt hs hnd hinj hk hi hlt; omega
  · -- rr
    intro x y hx hxc hy hyc hxy
    have hle := hR_after x y hy hyc hxy
    by_cases h0 : (tok x).1 = 0
    · simp [rfOf, h0]
    · have h0' : (tok y).1 ≠ 0 := by have := fst_le_of_le hle; omega
      obtain ⟨k, hk, htk, hrf, -⟩ := hlook x hx hxc h0
      obtain ⟨k', hk', htk', hrf', -⟩ := hlook y hy hyc h0'
      rw [hrf, hrf']; rw [← htk, ← htk'] at hle
      rcases hle.lt_or_eq with hlt | heq
      · have := idx_lt_of_tok_lt hs hnd hinj hk hk' hlt; omega
      · have := idx_eq_of_tok_eq hs hnd hinj hk hk' (toLex.injective heq); omega

/-- **Theorem 12** (Hadzilacos–Hu–Toueg, PODC 2021). Algorithm 4 is a linearizable implementation
of an MWMR register from SWMR registers, for every value type `V`, initial value `v₀` and number
`n ≥ 1` of processes. -/
theorem alg4_linearizable (V : Type) (v₀ : V) (n : ℕ) [NeZero n] :
    (alg4 V v₀ n).Linearizable := by
  refine Impl.linearizable_of_run (fun α C hrun => ?_)
  obtain ⟨W, tok, h⟩ := exists_inv hrun
  exact ⟨_, (h.readsFrom hrun).isLinearization⟩

end Podc.RegisterLinTermination.Alg4
