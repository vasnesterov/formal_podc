import Papers.PODC2021.RegisterLinTermination.Alg2
import Podc.Computability.Distributed.SharedMemory.MWMRRegister
import Mathlib.Data.List.GetD

/-!
# Theorem 10, part 1: the on-line write order and the state invariant

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Algorithm 3
and Appendix C.

We compute, along an execution `α` of Algorithm 2, a *ghost state* `ghost α`:

* `ws` — the write sequence `WS` of Algorithm 3, built on-line: when a process `p_k` writes
  `Val[k]` with timestamp `ts` and its write `w` is not yet in `ws`, we append the batch `B`:
  the pending writes not yet in `ws` whose partial timestamp (padded with `∞`) is
  lexicographically smaller than `ts` (in process order), followed by `w`;
* `wts x` — the timestamp written by the write `x` (once it has written `Val[-]`);
* `rcell x` — the cell `(v, ts)` returned by the read `x` (fixed at its last base step).

The state invariant `Inv` relates the configuration, the history and the ghost state.
-/

namespace Podc.RegisterLinTermination.Alg2

open Cslib.SharedMemory List

set_option linter.unusedSectionVars false

namespace WSL

variable {V : Type} {v₀ : V} {n : ℕ} [NeZero n]

/-- Labels of executions of Algorithm 2. -/
abbrev Lbl (V : Type) (v₀ : V) (n : ℕ) := Label (Fin n) (register V v₀)

/-- Configurations of Algorithm 2. -/
abbrev Cfg (V : Type) (v₀ : V) (n : ℕ) :=
  Config (register V v₀) (base V v₀ n) (Fin n) (Loc V n)

/-! ## Lexicographic order on timestamps -/

section Lex

/-- Componentwise order on vector timestamps (entries read with `getD _ 0`). -/
def CwLe (a b : List ℕ) : Prop := ∀ l, a.getD l 0 ≤ b.getD l 0

lemma CwLe.refl (a : List ℕ) : CwLe a a := fun _ => le_rfl

lemma CwLe.trans {a b c : List ℕ} (h₁ : CwLe a b) (h₂ : CwLe b c) : CwLe a c :=
  fun l => (h₁ l).trans (h₂ l)

/-- If the first `m` entries of `a` are lexicographically below those of `b` (same lengths),
then `a < b`. -/
lemma lt_of_take_lt {a b : List ℕ} {m : ℕ} (hab : a.length = b.length) (hm : m ≤ a.length)
    (h : a.take m < b.take m) : a < b := by
  rw [List.lt_iff_exists] at h ⊢
  rcases h with ⟨-, h⟩ | ⟨i, h₁, h₂, h₃, h₄⟩
  · simp at h; omega
  · right
    simp only [length_take] at h₁ h₂
    refine ⟨i, by omega, by omega, fun j hj => ?_, ?_⟩
    · have := h₃ j hj; simpa using this
    · simpa using h₄

lemma lt_of_append_lt_append {T a b : List ℕ} (h : T ++ a < T ++ b) : a < b := by
  induction T with
  | nil => simpa using h
  | cons x T ih =>
    rw [cons_append, cons_append, List.cons_lt_cons_iff] at h
    rcases h with h | ⟨-, h⟩
    · exact absurd h (Nat.lt_irrefl _)
    · exact ih h

/-- Equal-length lists that are componentwise ordered are lexicographically ordered. -/
lemma not_lt_of_cwLe {a b : List ℕ} (hab : a.length = b.length) (h : CwLe a b) : ¬ b < a := by
  induction a generalizing b with
  | nil => exact List.not_lt_nil _
  | cons x a ih =>
    rcases b with _ | ⟨y, b⟩
    · simp at hab
    · have hxy : x ≤ y := by simpa using h 0
      have hab' : CwLe a b := fun l => by simpa using h (l + 1)
      rw [List.cons_lt_cons_iff]
      rintro (h' | ⟨-, h'⟩)
      · omega
      · exact ih (by simpa using hab) hab' h'

/-- Lemma 37-style comparison: if `ts`'s first `m` entries are not above those of `t`
lexicographically, and the remaining entries are componentwise below, then `¬ t < ts`. -/
lemma not_lt_of_take_not_lt {t ts : List ℕ} {m : ℕ} (hl : t.length = ts.length)
    (hm : m ≤ t.length) (h : ¬ t.take m < ts.take m)
    (hr : ∀ l, m ≤ l → ts.getD l 0 ≤ t.getD l 0) : ¬ t < ts := by
  rcases Std.lt_trichotomy (ts.take m) (t.take m) with h' | h' | h'
  · exact List.lt_asymm (lt_of_take_lt hl.symm (by omega) h')
  · rw [← List.take_append_drop m t, ← List.take_append_drop m ts, h']
    intro hc
    refine not_lt_of_cwLe (by simp [hl]) (fun l => ?_) (lt_of_append_lt_append hc)
    simp only [getD_eq_getElem?_getD, getElem?_drop]
    simpa [getD_eq_getElem?_getD] using hr (m + l) (by omega)
  · exact absurd h' h

end Lex

/-! ## The ghost state -/

/-- The partial timestamp of a write in progress: the prefix of `new_ts` computed so far (the
rest is `∞`), or the complete timestamp. -/
def part : Loc V n → Option (List ℕ)
  | .wRead _ _ pre => some pre
  | .wWrite _ ts => some ts
  | _ => none

/-- The partial timestamp of the write in progress in local state `l` is lexicographically below
the (complete) timestamp `ts`; padding with `∞` this is `pre < ts.take pre.length`. -/
def below (ts : List ℕ) (l : Loc V n) : Bool :=
  match part l with
  | some pre => decide (pre < ts.take pre.length)
  | none => false

/-- The batch `B` appended to `WS` (Algorithm 3, lines 6–10) when label `ℓ` is taken in
configuration `C` after history `α`, with `ws` the write sequence so far. -/
def batch (α : List (Lbl V v₀ n)) (C : Cfg V v₀ n) (ws : List (OpId (Fin n))) :
    Lbl V v₀ n → List (OpId (Fin n))
  | .tau k =>
    match C.loc k with
    | .wWrite _ ts =>
      if curOp α k ∈ ws then [] else
        ((finRange n).filter (fun p => decide (p ≠ k) && below ts (C.loc p) &&
          decide (curOp α p ∉ ws))).map (curOp α) ++ [curOp α k]
    | _ => []
  | _ => []

/-- Ghost state: write sequence, timestamps of writes, cells returned by reads. -/
structure GS (V : Type) (n : ℕ) where
  /-- the write sequence `WS` -/
  ws : List (OpId (Fin n))
  /-- the timestamp written by a write (once it has written `Val[-]`) -/
  wts : OpId (Fin n) → Option (List ℕ)
  /-- the cell returned by a read (once fixed) -/
  rcell : OpId (Fin n) → Option (Cell V)

/-- The cell kept by a read after reading cell `c` with best cell `best`. -/
def newBest (best c : Cell V) : Cell V := if best.2 < c.2 then c else best

/-- Update of the timestamps of writes. -/
def wtsStep (α : List (Lbl V v₀ n)) (C : Cfg V v₀ n) (w : OpId (Fin n) → Option (List ℕ)) :
    Lbl V v₀ n → OpId (Fin n) → Option (List ℕ)
  | .tau k =>
    match C.loc k with
    | .wWrite _ ts => Function.update w (curOp α k) (some ts)
    | _ => w
  | _ => w

/-- Update of the cells returned by reads. -/
def rcellStep (α : List (Lbl V v₀ n)) (C : Cfg V v₀ n) (r : OpId (Fin n) → Option (Cell V)) :
    Lbl V v₀ n → OpId (Fin n) → Option (Cell V)
  | .tau p =>
    match C.loc p with
    | .rRead i best =>
      if Alg4.next i = none then Function.update r (curOp α p) (some (newBest best (C.mem i)))
      else r
    | _ => r
  | _ => r

/-- One step of the ghost state. -/
def gstep (α : List (Lbl V v₀ n)) (C : Cfg V v₀ n) (g : GS V n) (ℓ : Lbl V v₀ n) : GS V n where
  ws := g.ws ++ batch α C g.ws ℓ
  wts := wtsStep α C g.wts ℓ
  rcell := rcellStep α C g.rcell ℓ

/-- The initial ghost state. -/
def ghost₀ : GS V n := ⟨[], fun _ => none, fun _ => none⟩

/-- Ghost state along a reversed history. -/
noncomputable def ghostR : List (Lbl V v₀ n) → GS V n
  | [] => ghost₀
  | ℓ :: r =>
    match (alg2 V v₀ n).run r.reverse with
    | some C => gstep r.reverse C (ghostR r) ℓ
    | none => ghostR r

/-- The ghost state after the history `α`. -/
noncomputable def ghost (α : List (Lbl V v₀ n)) : GS V n := ghostR α.reverse

@[simp] lemma ghost_nil : ghost ([] : List (Lbl V v₀ n)) = ghost₀ := rfl

lemma ghost_concat {α : List (Lbl V v₀ n)} {C : Cfg V v₀ n} (h : (alg2 V v₀ n).run α = some C)
    (ℓ : Lbl V v₀ n) : ghost (α ++ [ℓ]) = gstep α C (ghost α) ℓ := by
  simp [ghost, ghostR, h]

lemma ghost_ws_prefix (α β : List (Lbl V v₀ n)) : (ghost α).ws <+: (ghost (α ++ β)).ws := by
  induction β using List.reverseRecOn with
  | nil => simp
  | append_singleton β ℓ ih =>
    refine ih.trans ?_
    rw [← List.append_assoc]
    cases h : (alg2 V v₀ n).run (α ++ β) with
    | none => simp [ghost, ghostR, h]
    | some C => rw [ghost_concat h]; exact List.prefix_append _ _

/-- The reads-from map: `0` for a read returning the initial cell, otherwise `1 +` the position in
`WS` of the write whose timestamp the read returned. -/
def rfOf (g : GS V n) (x : OpId (Fin n)) : ℕ :=
  match g.rcell x with
  | some c =>
    match g.ws.find? (fun y => decide (g.wts y = some c.2)) with
    | some w => g.ws.idxOf w + 1
    | none => 0
  | none => 0

/-! ## Steps of Algorithm 2 -/

section Steps

variable {C : Cfg V v₀ n} {p : Fin n}

/-- `diag C l = Val[l].ts[l]`, the number of writes of `p_l` that have written `Val[l]`. -/
def diag (C : Cfg V v₀ n) (l : Fin n) : ℕ := (C.mem l).2.getD l 0

/-- The entry read by a write of `p` from `Val[i]`. -/
def rv (C : Cfg V v₀ n) (p i : Fin n) : ℕ := (C.mem i).2.getD i 0 + if i = p then 1 else 0

/-- Local state after a write of `p` reads `Val[i]`. -/
def wReadNext (v : V) (i : Fin n) (pre : List ℕ) (x : ℕ) : Loc V n :=
  match Alg4.next i with
  | some j => .wRead v j (pre ++ [x])
  | none => .wWrite v (pre ++ [x])

/-- Local state after a read reads `Val[i]`. -/
def rReadNext (i : Fin n) (best : Cell V) : Loc V n :=
  match Alg4.next i with
  | some j => .rRead j best
  | none => .rRet best.1

lemma step_wRead (hp : C.pend p ≠ none) {v : V} {i : Fin n} {pre : List ℕ}
    (hl : C.loc p = .wRead v i pre) :
    (alg2 V v₀ n).step C (.tau p) =
      some { C with loc := Function.update C.loc p (wReadNext v i pre (rv C p i)) } := by
  rw [Impl.step_tau_eq_some hp (by simp only [alg2, hl, act]; rfl)]
  simp only [Function.update_eq_self]
  rfl

lemma step_wWrite (hp : C.pend p ≠ none) {v : V} {ts : List ℕ} (hl : C.loc p = .wWrite v ts) :
    (alg2 V v₀ n).step C (.tau p) =
      some { C with mem := Function.update C.mem p (v, ts),
                    loc := Function.update C.loc p (.wRet v) } := by
  rw [Impl.step_tau_eq_some hp (by simp only [alg2, hl, act]; rfl)]

lemma step_rRead (hp : C.pend p ≠ none) {i : Fin n} {best : Cell V}
    (hl : C.loc p = .rRead i best) :
    (alg2 V v₀ n).step C (.tau p) =
      some { C with loc := Function.update C.loc p (rReadNext i (newBest best (C.mem i))) } := by
  rw [Impl.step_tau_eq_some hp (by simp only [alg2, hl, act]; rfl)]
  simp only [Function.update_eq_self]
  rfl

end Steps

/-! ## Batches -/

section Batch

variable {α : List (Lbl V v₀ n)} {C : Cfg V v₀ n} {ws : List (OpId (Fin n))}

lemma next_some {i j : Fin n} (h : Alg4.next i = some j) : j.val = i.val + 1 := by
  unfold Alg4.next at h; split_ifs at h; cases h; rfl

lemma next_none {i : Fin n} (h : Alg4.next i = none) : i.val + 1 = n := by
  unfold Alg4.next at h; split_ifs at h with h1; omega

lemma below_iff {ts : List ℕ} {l : Loc V n} :
    below ts l = true ↔ ∃ pre, part l = some pre ∧ pre < ts.take pre.length := by
  unfold below; cases part l <;> simp

lemma curOp_injective (α : List (Lbl V v₀ n)) : Function.Injective (curOp α) :=
  fun _ _ h => congrArg Prod.fst h

lemma batch_wWrite {k : Fin n} {v : V} {ts : List ℕ} (h : C.loc k = .wWrite v ts) :
    batch α C ws (.tau k) = if curOp α k ∈ ws then [] else
      ((finRange n).filter (fun p => decide (p ≠ k) && below ts (C.loc p) &&
        decide (curOp α p ∉ ws))).map (curOp α) ++ [curOp α k] := by
  simp [batch, h]

lemma batch_of_not_wWrite {k : Fin n} (h : ∀ v ts, C.loc k ≠ .wWrite v ts) :
    batch α C ws (.tau k) = [] := by
  unfold batch
  cases hk : C.loc k <;> simp_all

/-- Members of a batch. -/
lemma mem_batch {ℓ : Lbl V v₀ n} {x : OpId (Fin n)} (hx : x ∈ batch α C ws ℓ) :
    ∃ k v ts, ℓ = .tau k ∧ C.loc k = .wWrite v ts ∧ curOp α k ∉ ws ∧
      (x = curOp α k ∨ ∃ p, p ≠ k ∧ below ts (C.loc p) = true ∧ curOp α p ∉ ws ∧
        x = curOp α p) := by
  cases ℓ with
  | inv q o => simp [batch] at hx
  | ret q r => simp [batch] at hx
  | tau k =>
    cases hk : C.loc k with
    | wWrite v ts =>
      rw [batch_wWrite hk] at hx
      split_ifs at hx with h1
      · simp at hx
      · refine ⟨k, v, ts, rfl, hk, h1, ?_⟩
        simp only [mem_append, mem_map, mem_filter, mem_finRange, true_and, Bool.and_eq_true,
          decide_eq_true_eq, mem_singleton] at hx
        rcases hx with ⟨p, ⟨⟨h2, h3⟩, h4⟩, rfl⟩ | rfl
        · exact Or.inr ⟨p, h2, h3, h4, rfl⟩
        · exact Or.inl rfl
    | _ => simp [batch, hk] at hx

lemma batch_nodup (ℓ : Lbl V v₀ n) : (batch α C ws ℓ).Nodup := by
  cases ℓ with
  | inv q o => simp [batch]
  | ret q r => simp [batch]
  | tau k =>
    cases hk : C.loc k with
    | wWrite v ts =>
      rw [batch_wWrite hk]
      split_ifs
      · simp
      · rw [nodup_append]
        refine ⟨((nodup_finRange n).filter _).map (curOp_injective α), by simp, ?_⟩
        simp only [mem_map, mem_filter, mem_finRange, true_and, Bool.and_eq_true,
          decide_eq_true_eq, mem_singleton]
        rintro _ ⟨p, ⟨⟨h2, -⟩, -⟩, rfl⟩ _ rfl h
        exact h2 (curOp_injective α h)
    | _ => simp [batch, hk]

lemma batch_disjoint {ℓ : Lbl V v₀ n} {x : OpId (Fin n)} (hx : x ∈ batch α C ws ℓ) : x ∉ ws := by
  obtain ⟨k, v, ts, -, -, h1, h2 | ⟨p, -, -, h3, rfl⟩⟩ := mem_batch hx
  · subst h2; exact h1
  · exact h3

end Batch

/-! ## The state invariant -/

section Inv

/-- Local states match pending operations. -/
def LocOK : Loc V n → Option (RWOp V) → Prop
  | .idle, o => o = none
  | .wRead v i pre, o => o = some (.write v) ∧ pre.length = i.val
  | .wWrite v ts, o => o = some (.write v) ∧ ts.length = n
  | .wRet v, o => o = some (.write v)
  | .rRead _ best, o => o = some .read ∧ best.2.length = n
  | .rRet _, o => o = some .read

/-- Bounds on the partial timestamp `pre` of a write of `p`: its entries are at least those of
`Val[p]` (strictly at `p`) and at most `diag` (plus one at `p`). -/
def PreOK (C : Cfg V v₀ n) (p : Fin n) (pre : List ℕ) : Prop :=
  pre.length ≤ n ∧ ∀ l : Fin n, l.val < pre.length →
    (C.mem p).2.getD l 0 + (if l = p then 1 else 0) ≤ pre.getD l 0 ∧
    pre.getD l 0 ≤ diag C l + (if l = p then 1 else 0)

/-- A cell is the initial one or was written by a write with this value and timestamp. -/
def CellOK (α : List (Lbl V v₀ n)) (g : GS V n) (c : Cell V) : Prop :=
  c = (v₀, replicate n 0) ∨ ∃ w, opOf α w = some (.write c.1) ∧ g.wts w = some c.2

/-- The state invariant. -/
structure Inv (α : List (Lbl V v₀ n)) (C : Cfg V v₀ n) (g : GS V n) : Prop where
  loc : ∀ p, LocOK (C.loc p) (C.pend p)
  partOK : ∀ p pre, part (C.loc p) = some pre → PreOK C p pre ∧ g.wts (curOp α p) = none
  memLen : ∀ k, (C.mem k).2.length = n
  memLe : ∀ k (l : Fin n), (C.mem k).2.getD l 0 ≤ diag C l
  memCell : ∀ k, CellOK α g (C.mem k)
  wsInv : ∀ x ∈ g.ws, Invoked α x ∧ ∃ v, opOf α x = some (.write v)
  wsNodup : g.ws.Nodup
  wtsInv : ∀ x t, g.wts x = some t →
    x ∈ g.ws ∧ t.length = n ∧ CwLe t (C.mem x.1).2 ∧ 1 ≤ t.getD x.1 0
  wtsInj : ∀ x y t, g.wts x = some t → g.wts y = some t → x = y
  wRet : ∀ p v, C.loc p = .wRet v → g.wts (curOp α p) ≠ none
  complW : ∀ x v, opOf α x = some (.write v) → Completed α x → g.wts x ≠ none
  rRead : ∀ p i best, C.loc p = .rRead i best → CellOK α g best ∧ g.rcell (curOp α p) = none
  rRet : ∀ p v, C.loc p = .rRet v → ∃ c, g.rcell (curOp α p) = some c ∧ c.1 = v
  rcellInv : ∀ x c, g.rcell x = some c → Invoked α x ∧ CellOK α g c ∧ c.2.length = n
  complR : ∀ x, opOf α x = some .read → Completed α x →
    ∃ c, g.rcell x = some c ∧ respOf α x = some c.1
  writeResp : ∀ x v r, opOf α x = some (.write v) → respOf α x = some r → r = v

variable {α : List (Lbl V v₀ n)} {C C' : Cfg V v₀ n} {g : GS V n}

lemma CellOK.mono {c : Cell V} (h : CellOK α g c) (β : List (Lbl V v₀ n)) {g' : GS V n}
    (hg : ∀ x t, g.wts x = some t → g'.wts x = some t) : CellOK (α ++ β) g' c := by
  rcases h with h | ⟨w, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, opOf_append_of_eq_some h1 β, hg _ _ h2⟩

lemma inv_init : Inv ([] : List (Lbl V v₀ n)) (alg2 V v₀ n).initCfg ghost₀ := by
  refine ⟨fun p => rfl, fun p pre h => by simp [Impl.initCfg, alg2, part] at h,
    fun k => by simp [Impl.initCfg, alg2], fun k l => by simp [Impl.initCfg, alg2, diag],
    fun k => Or.inl rfl, by simp [ghost₀], by simp [ghost₀], by simp [ghost₀],
    by simp [ghost₀], fun p v h => by simp [Impl.initCfg, alg2] at h,
    fun x v h => by simp [opOf] at h, fun p i b h => by simp [Impl.initCfg, alg2] at h,
    fun p v h => by simp [Impl.initCfg, alg2] at h, by simp [ghost₀],
    fun x h => by simp [opOf] at h, fun x v r h => by simp [opOf] at h⟩

lemma Inv.invoked_of_wts (hI : Inv α C g) {x : OpId (Fin n)} {t : List ℕ}
    (h : g.wts x = some t) : Invoked α x :=
  (hI.wsInv x (hI.wtsInv x t h).1).1

lemma Inv.locOK_pend (hI : Inv α C g) {p : Fin n} {pre : List ℕ}
    (h : part (C.loc p) = some pre) : ∃ v, C.pend p = some (.write v) := by
  have := hI.loc p
  revert this h
  cases C.loc p <;> simp [part, LocOK] <;> intros <;> simp_all

lemma gstep_inv (q : Fin n) (o : RWOp V) : gstep α C g (.inv q o) = g := by
  simp [gstep, batch, wtsStep, rcellStep]

lemma gstep_ret (q : Fin n) (r : V) : gstep α C g (.ret q r) = g := by
  simp [gstep, batch, wtsStep, rcellStep]

lemma Inv.step_inv (hrun : (alg2 V v₀ n).run α = some C) (hI : Inv α C g) {q : Fin n}
    {o : RWOp V} (hs : (alg2 V v₀ n).step C (.inv q o) = some C') :
    Inv (α ++ [.inv q o]) C' g := by
  obtain ⟨hpn, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hidle : C.loc q = .idle := by
    have := hI.loc q
    revert this; cases C.loc q <;> simp [LocOK, hpn]
  have hnew : ¬ Invoked α (curOp α q) := Impl.not_invoked_curOp_of_idle hrun hpn
  have hwq : g.wts (curOp α q) = none := by
    cases h : g.wts (curOp α q) with
    | none => rfl
    | some t => exact absurd (hI.invoked_of_wts h) hnew
  have hrq : g.rcell (curOp α q) = none := by
    cases h : g.rcell (curOp α q) with
    | none => rfl
    | some c => exact absurd (hI.rcellInv _ _ h).1 hnew
  have hcell : ∀ c, CellOK α g c → CellOK (α ++ [.inv q o]) g c := fun c h => h.mono _ (by simp)
  have hcompl : ∀ x, Completed (α ++ [.inv q o]) x ↔ Completed α x :=
    completed_append_of_not_ret (by simp)
  have hresp : ∀ x, respOf (α ++ [.inv q o]) x = respOf α x := respOf_append_of_not_ret (by simp)
  have hopc : ∀ x, Completed α x → opOf (α ++ [.inv q o]) x = opOf α x := fun x h =>
    opOf_append_of_invoked ((Impl.Valid.wellFormed _ ⟨C, hrun⟩).invoked_of_completed h)
  have hlocq : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by simp [hloc, hp]
  have hpendq : ∀ p, p ≠ q → C'.pend p = C.pend p := fun p hp => by simp [hpend, hp]
  have hdiag : diag C' = diag C := by unfold diag; rw [hmem]
  refine ⟨fun p => ?_, fun p pre hp => ?_, fun k => hmem ▸ hI.memLen k,
    fun k l => hmem ▸ hdiag ▸ hI.memLe k l, fun k => hmem ▸ hcell _ (hI.memCell k),
    fun x hx => ?_, hI.wsNodup, fun x t h => hmem ▸ hI.wtsInv x t h, hI.wtsInj,
    fun p v hp => ?_, fun x v h hc => ?_, fun p i best hp => ?_, fun p v hp => ?_,
    fun x c h => ?_, fun x h hc => ?_, fun x v r h hr => ?_⟩
  · by_cases hpq : p = q
    · subst hpq
      simp only [hloc, hpend, Function.update_self, alg2]
      cases o <;> simp [invoke, LocOK]
    · rw [hlocq p hpq, hpendq p hpq]; exact hI.loc p
  · rw [curOp_append_inv]
    by_cases hpq : p = q
    · subst hpq
      simp only [hloc, Function.update_self, alg2] at hp
      cases o <;> simp [invoke, part] at hp
      subst hp
      exact ⟨⟨by simp, by simp⟩, hwq⟩
    · rw [hlocq p hpq] at hp
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI.partOK p pre hp
      exact ⟨⟨h1, by simpa [hmem, hdiag] using h2⟩, h3⟩
  · obtain ⟨h1, v, h2⟩ := hI.wsInv x hx
    exact ⟨h1.mono, v, opOf_append_of_eq_some h2 _⟩
  · rw [curOp_append_inv]
    by_cases hpq : p = q
    · subst hpq; simp only [hloc, Function.update_self, alg2] at hp; cases o <;> simp [invoke] at hp
    · rw [hlocq p hpq] at hp; exact hI.wRet p v hp
  · rw [hcompl] at hc
    rw [hopc x hc] at h
    exact hI.complW x v h hc
  · rw [curOp_append_inv]
    by_cases hpq : p = q
    · subst hpq
      simp only [hloc, Function.update_self, alg2] at hp
      cases o <;> simp [invoke] at hp
      obtain ⟨-, rfl⟩ := hp
      exact ⟨Or.inl rfl, hrq⟩
    · rw [hlocq p hpq] at hp
      obtain ⟨h1, h2⟩ := hI.rRead p i best hp
      exact ⟨hcell _ h1, h2⟩
  · rw [curOp_append_inv]
    by_cases hpq : p = q
    · subst hpq; simp only [hloc, Function.update_self, alg2] at hp; cases o <;> simp [invoke] at hp
    · rw [hlocq p hpq] at hp; exact hI.rRet p v hp
  · obtain ⟨h1, h2, h3⟩ := hI.rcellInv x c h
    exact ⟨h1.mono, hcell _ h2, h3⟩
  · rw [hcompl] at hc
    rw [hopc x hc] at h
    obtain ⟨c, h1, h2⟩ := hI.complR x h hc
    exact ⟨c, h1, by rw [hresp]; exact h2⟩
  · rw [hresp] at hr
    rw [hopc x (Completed.of_respOf_eq_some hr)] at h
    exact hI.writeResp x v r h hr

lemma Inv.step_ret (hrun : (alg2 V v₀ n).run α = some C) (hI : Inv α C g) {q : Fin n}
    {r : V} (hs : (alg2 V v₀ n).step C (.ret q r) = some C') :
    Inv (α ++ [.ret q r]) C' g := by
  obtain ⟨hpn, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpn
  obtain ⟨-, hnc, hop⟩ := Impl.run_pend_curOp hrun ho
  -- the returning process is in state `wRet r` or `rRet r`
  have hcases : (C.loc q = .wRet r ∧ o = .write r) ∨ (C.loc q = .rRet r ∧ o = .read) := by
    have h1 := hI.loc q
    rw [ho] at h1
    revert h1 hact
    cases C.loc q <;> simp [alg2, act, LocOK] <;> intros <;> simp_all
  have hl : l = .idle := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [alg2, h1, act] at hact <;> exact hact.symm
  subst hl
  have hcell : ∀ c, CellOK α g c → CellOK (α ++ [.ret q r]) g c := fun c h => h.mono _ (by simp)
  have hlocq : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by simp [hloc, hp]
  have hpendq : ∀ p, p ≠ q → C'.pend p = C.pend p := fun p hp => by simp [hpend, hp]
  have hcurq : ∀ p, p ≠ q → curOp (α ++ [.ret q r]) p = curOp α p := fun p hp =>
    curOp_append_ret_of_ne α r (Ne.symm hp)
  have hdiag : diag C' = diag C := by unfold diag; rw [hmem]
  refine ⟨fun p => ?_, fun p pre hp => ?_, fun k => hmem ▸ hI.memLen k,
    fun k l => hmem ▸ hdiag ▸ hI.memLe k l, fun k => hmem ▸ hcell _ (hI.memCell k),
    fun x hx => ?_, hI.wsNodup, fun x t h => hmem ▸ hI.wtsInv x t h, hI.wtsInj,
    fun p v hp => ?_, fun x v h hc => ?_, fun p i best hp => ?_, fun p v hp => ?_,
    fun x c h => ?_, fun x h hc => ?_, fun x v r' h hr => ?_⟩
  · by_cases hpq : p = q
    · subst hpq; simp [hloc, hpend, LocOK]
    · rw [hlocq p hpq, hpendq p hpq]; exact hI.loc p
  · by_cases hpq : p = q
    · subst hpq; simp [hloc, part] at hp
    · rw [hlocq p hpq] at hp
      rw [hcurq p hpq]
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI.partOK p pre hp
      exact ⟨⟨h1, by simpa [hmem, hdiag] using h2⟩, h3⟩
  · obtain ⟨h1, v, h2⟩ := hI.wsInv x hx
    exact ⟨h1.mono, v, opOf_append_of_eq_some h2 _⟩
  · by_cases hpq : p = q
    · subst hpq; simp [hloc] at hp
    · rw [hlocq p hpq] at hp; rw [hcurq p hpq]; exact hI.wRet p v hp
  · rw [opOf_append_ret] at h
    rcases (completed_append_ret x).1 hc with hc | rfl
    · exact hI.complW x v h hc
    · rcases hcases with ⟨h1, -⟩ | ⟨-, rfl⟩
      · exact hI.wRet q r h1
      · rw [hop] at h; cases h
  · by_cases hpq : p = q
    · subst hpq; simp [hloc] at hp
    · rw [hlocq p hpq] at hp
      rw [hcurq p hpq]
      obtain ⟨h1, h2⟩ := hI.rRead p i best hp
      exact ⟨hcell _ h1, h2⟩
  · by_cases hpq : p = q
    · subst hpq; simp [hloc] at hp
    · rw [hlocq p hpq] at hp; rw [hcurq p hpq]; exact hI.rRet p v hp
  · obtain ⟨h1, h2, h3⟩ := hI.rcellInv x c h
    exact ⟨h1.mono, hcell _ h2, h3⟩
  · rw [opOf_append_ret] at h
    rcases (completed_append_ret x).1 hc with hc | rfl
    · obtain ⟨c, h1, h2⟩ := hI.complR x h hc
      exact ⟨c, h1, respOf_append_of_eq_some h2 _⟩
    · rcases hcases with ⟨-, rfl⟩ | ⟨h1, -⟩
      · rw [hop] at h; cases h
      · obtain ⟨c, h2, h3⟩ := hI.rRet q r h1
        exact ⟨c, h2, by rw [respOf_append_ret, ite_eq_left_iff.mpr (fun h => absurd rfl h), h3]⟩
  · rw [opOf_append_ret] at h
    rw [respOf_append_ret] at hr
    split_ifs at hr with hx
    · subst hx
      cases hr
      rcases hcases with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [hop] at h; cases h; rfl
      · rw [hop] at h; cases h
    · exact hI.writeResp x v r' h hr

lemma Inv.step_wRead (_hrun : (alg2 V v₀ n).run α = some C) (hI : Inv α C g) {q : Fin n}
    {v : V} {i : Fin n} {pre : List ℕ} (hq : C.loc q = .wRead v i pre)
    (hs : (alg2 V v₀ n).step C (.tau q) = some C') :
    Inv (α ++ [.tau q]) C' (gstep α C g (.tau q)) := by
  have hpq : C.pend q = some (.write v) ∧ pre.length = i.val := by
    have := hI.loc q; rw [hq] at this; exact this
  rw [WSL.step_wRead (by simp [hpq.1]) hq, Option.some.injEq] at hs
  subst hs
  have hb : batch α C g.ws (.tau q) = [] := batch_of_not_wWrite (C := C) (by simp [hq])
  have hg : gstep α C g (.tau q) = g := by
    simp [gstep, hb, wtsStep, rcellStep, hq]
  rw [hg]
  have hcell : ∀ c, CellOK α g c → CellOK (α ++ [.tau q]) g c := fun c h => h.mono _ (by simp)
  have hcompl : ∀ x, Completed (α ++ [.tau q]) x ↔ Completed α x :=
    completed_append_of_not_ret (by simp)
  have hresp : ∀ x, respOf (α ++ [.tau q]) x = respOf α x := respOf_append_of_not_ret (by simp)
  have hlocq : ∀ p, p ≠ q → Function.update C.loc q (wReadNext v i pre (rv C q i)) p = C.loc p :=
    fun p hp => by simp [hp]
  obtain ⟨⟨hpre1, hpre2⟩, hwq⟩ := hI.partOK q pre (by simp [hq, part])
  refine ⟨fun p => ?_, fun p pre' hp => ?_, hI.memLen, hI.memLe, fun k => hcell _ (hI.memCell k),
    fun x hx => ?_, hI.wsNodup, hI.wtsInv, hI.wtsInj,
    fun p v hp => ?_, fun x v h hc => ?_, fun p i best hp => ?_, fun p v hp => ?_,
    fun x c h => ?_, fun x h hc => ?_, fun x v r h hr => ?_⟩
  · by_cases hpq' : p = q
    · subst hpq'
      simp only [Function.update_self, wReadNext]
      split
      · rename_i j hj; simp [LocOK, hpq.1, next_some hj, hpq.2]
      · rename_i hj; simp [LocOK, hpq.1, hpq.2, next_none hj]
    · simp only [hlocq p hpq']; exact hI.loc p
  · simp only [curOp_append_tau]
    by_cases hpq' : p = q
    · subst hpq'
      have hp' : pre' = pre ++ [rv C p i] := by
        simp only [Function.update_self, wReadNext] at hp
        split at hp <;> simpa [part] using hp.symm
      subst hp'
      refine ⟨⟨by simp; have := i.isLt; omega, fun l hl => ?_⟩, hwq⟩
      simp only [length_append, length_singleton] at hl
      rcases Nat.lt_or_ge l.val pre.length with hl' | hl'
      · rw [getD_append _ _ _ _ hl']; exact hpre2 l hl'
      · have hli : l = i := Fin.ext (by omega)
        subst hli
        rw [getD_append_right _ _ _ _ hl', show (l : ℕ) - pre.length = 0 by omega]
        simp only [getD_cons_zero, rv]
        exact ⟨by simpa [diag] using hI.memLe p l, by simp [diag]⟩
    · simp only [hlocq p hpq'] at hp; exact hI.partOK p pre' hp
  · obtain ⟨h1, v, h2⟩ := hI.wsInv x hx
    exact ⟨h1.mono, v, opOf_append_of_eq_some h2 _⟩
  · by_cases hpq' : p = q
    · subst hpq'; simp only [Function.update_self, wReadNext] at hp; split at hp <;> cases hp
    · simp only [hlocq p hpq'] at hp; simpa using hI.wRet p v hp
  · rw [hcompl] at hc; rw [opOf_append_tau] at h; exact hI.complW x v h hc
  · by_cases hpq' : p = q
    · subst hpq'; simp only [Function.update_self, wReadNext] at hp; split at hp <;> cases hp
    · simp only [hlocq p hpq'] at hp
      obtain ⟨h1, h2⟩ := hI.rRead p i best hp
      exact ⟨hcell _ h1, by simpa using h2⟩
  · by_cases hpq' : p = q
    · subst hpq'; simp only [Function.update_self, wReadNext] at hp; split at hp <;> cases hp
    · simp only [hlocq p hpq'] at hp; simpa using hI.rRet p v hp
  · obtain ⟨h1, h2, h3⟩ := hI.rcellInv x c h
    exact ⟨h1.mono, hcell _ h2, h3⟩
  · rw [hcompl] at hc; rw [opOf_append_tau] at h
    obtain ⟨c, h1, h2⟩ := hI.complR x h hc
    exact ⟨c, h1, by rw [hresp]; exact h2⟩
  · rw [hresp] at hr; rw [opOf_append_tau] at h; exact hI.writeResp x v r h hr

lemma Inv.step_wWrite (hrun : (alg2 V v₀ n).run α = some C) (hI : Inv α C g) {q : Fin n}
    {v : V} {ts : List ℕ} (hq : C.loc q = .wWrite v ts)
    (hs : (alg2 V v₀ n).step C (.tau q) = some C') :
    Inv (α ++ [.tau q]) C' (gstep α C g (.tau q)) := by
  have hpq : C.pend q = some (.write v) ∧ ts.length = n := by
    have := hI.loc q; rw [hq] at this; exact this
  rw [WSL.step_wWrite (by simp [hpq.1]) hq, Option.some.injEq] at hs
  subst hs
  obtain ⟨⟨-, hts⟩, hwq⟩ := hI.partOK q ts (by simp [hq, part])
  obtain ⟨-, -, hcur⟩ := Impl.run_pend_curOp hrun hpq.1
  have htsq : ts.getD q 0 = diag C q + 1 := by
    have := hts q (by rw [hpq.2]; exact q.isLt)
    simp only [ite_true] at this
    unfold diag at this ⊢; omega
  have hcw : CwLe (C.mem q).2 ts := by
    intro l
    rcases Nat.lt_or_ge l n with hl | hl
    · have := (hts ⟨l, hl⟩ (by rw [hpq.2]; exact hl)).1
      simp only at this; omega
    · rw [getD_eq_default _ _ (by rw [hI.memLen q]; exact hl)]; exact Nat.zero_le _
  set C' : Cfg V v₀ n :=
    { C with mem := Function.update C.mem q (v, ts), loc := Function.update C.loc q (.wRet v) }
    with hC'
  have hdiag' : ∀ l, diag C' l = if l = q then ts.getD q 0 else diag C l := by
    intro l; by_cases hl : l = q
    · subst hl; simp [diag, hC']
    · simp [diag, hC', hl]
  have hdmono : ∀ l, diag C l ≤ diag C' l := by
    intro l; rw [hdiag']; split_ifs with hl
    · subst hl; omega
    · exact le_rfl
  have hmemq : ∀ k, k ≠ q → C'.mem k = C.mem k := fun k hk => by simp [hC', hk]
  have hlocq : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by simp [hC', hp]
  have hg : gstep α C g (.tau q) =
      ⟨g.ws ++ batch α C g.ws (.tau q), Function.update g.wts (curOp α q) (some ts), g.rcell⟩ := by
    simp [gstep, wtsStep, rcellStep, hq]
  rw [hg]
  set g' : GS V n :=
    ⟨g.ws ++ batch α C g.ws (.tau q), Function.update g.wts (curOp α q) (some ts), g.rcell⟩
    with hg'
  have hwts' : ∀ x t, g.wts x = some t → g'.wts x = some t := by
    intro x t h
    have : x ≠ curOp α q := by rintro rfl; rw [hwq] at h; cases h
    simp [hg', this, h]
  have hcell : ∀ c, CellOK α g c → CellOK (α ++ [.tau q]) g' c := fun c h => h.mono _ hwts'
  have hcompl : ∀ x, Completed (α ++ [.tau q]) x ↔ Completed α x :=
    completed_append_of_not_ret (by simp)
  have hresp : ∀ x, respOf (α ++ [.tau q]) x = respOf α x := respOf_append_of_not_ret (by simp)
  have hcurin : curOp α q ∈ g'.ws := by
    simp only [hg', batch_wWrite hq]
    split_ifs with h
    · exact mem_append_left _ h
    · simp
  have hold : ∀ y t, g.wts y = some t → t.getD q 0 ≤ diag C q := fun y t h =>
    ((hI.wtsInv y t h).2.2.1 q).trans (hI.memLe y.1 q)
  have hcurne : ∀ p, p ≠ q → curOp α p ≠ curOp α q := fun p hp h =>
    hp (curOp_injective α h)
  refine ⟨fun p => ?_, fun p pre hp => ?_, fun k => ?_, fun k l => ?_, fun k => ?_,
    fun x hx => ?_, ?_, fun x t h => ?_, fun x y t hx hy => ?_,
    fun p v hp => ?_, fun x v h hc => ?_, fun p i best hp => ?_, fun p v hp => ?_,
    fun x c h => ?_, fun x h hc => ?_, fun x v r h hr => ?_⟩
  · by_cases hpq' : p = q
    · subst hpq'; simp [hC', LocOK, hpq.1]
    · rw [hlocq p hpq']; exact hI.loc p
  · simp only [curOp_append_tau]
    by_cases hpq' : p = q
    · subst hpq'; simp [hC', part] at hp
    · rw [hlocq p hpq'] at hp
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI.partOK p pre hp
      refine ⟨⟨h1, fun l hl => ?_⟩, by simp [hg', hcurne p hpq', h3]⟩
      rw [hmemq p hpq']
      exact ⟨(h2 l hl).1, (h2 l hl).2.trans (by have := hdmono l; omega)⟩
  · by_cases hk : k = q
    · subst hk; simp [hC', hpq.2]
    · rw [hmemq k hk]; exact hI.memLen k
  · rw [hdiag']
    by_cases hk : k = q
    · subst hk
      simp only [hC', Function.update_self]
      split_ifs with hl
      · subst hl; exact le_rfl
      · have := (hts l (by rw [hpq.2]; exact l.isLt)).2
        simpa [hl] using this
    · rw [hmemq k hk]
      split_ifs with hl
      · subst hl; have := hI.memLe k l; omega
      · exact hI.memLe k l
  · by_cases hk : k = q
    · subst hk
      simp only [hC', Function.update_self]
      exact Or.inr ⟨curOp α k, opOf_append_of_eq_some hcur _, by simp [hg']⟩
    · rw [hmemq k hk]; exact hcell _ (hI.memCell k)
  · rcases mem_append.1 hx with hx | hx
    · obtain ⟨h1, v, h2⟩ := hI.wsInv x hx
      exact ⟨h1.mono, v, opOf_append_of_eq_some h2 _⟩
    · obtain ⟨k, v', ts', hk, -, -, h1 | ⟨p, -, hb, -, rfl⟩⟩ := mem_batch hx
      · cases hk; subst h1
        exact ⟨(Invoked.of_opOf_eq_some hcur).mono, v, opOf_append_of_eq_some hcur _⟩
      · obtain ⟨pre, hp, -⟩ := below_iff.1 hb
        obtain ⟨w, hw⟩ := hI.locOK_pend hp
        obtain ⟨h1, -, h2⟩ := Impl.run_pend_curOp hrun hw
        exact ⟨h1.mono, w, opOf_append_of_eq_some h2 _⟩
  · rw [nodup_append]
    exact ⟨hI.wsNodup, batch_nodup _, fun a ha b hb h => batch_disjoint hb (h ▸ ha)⟩
  · simp only [hg'] at h
    by_cases hx : x = curOp α q
    · subst hx
      simp only [Function.update_self, Option.some.injEq] at h
      subst h
      refine ⟨hcurin, hpq.2, by simp [hC']; exact CwLe.refl _, by rw [htsq]; omega⟩
    · rw [Function.update_of_ne hx] at h
      obtain ⟨h1, h2, h3, h4⟩ := hI.wtsInv x t h
      refine ⟨mem_append_left _ h1, h2, ?_, h4⟩
      by_cases hk : x.1 = q
      · rw [hk] at h3 ⊢; simp only [hC', Function.update_self]; exact h3.trans hcw
      · rw [hmemq _ hk]; exact h3
  · simp only [hg'] at hx hy
    by_cases hxq : x = curOp α q <;> by_cases hyq : y = curOp α q
    · rw [hxq, hyq]
    · subst hxq
      rw [Function.update_self, Option.some.injEq] at hx; subst hx
      rw [Function.update_of_ne hyq] at hy
      have := hold y _ hy; omega
    · subst hyq
      rw [Function.update_self, Option.some.injEq] at hy; subst hy
      rw [Function.update_of_ne hxq] at hx
      have := hold x _ hx; omega
    · rw [Function.update_of_ne hxq] at hx; rw [Function.update_of_ne hyq] at hy
      exact hI.wtsInj x y t hx hy
  · simp only [curOp_append_tau]
    by_cases hpq' : p = q
    · subst hpq'; simp [hg']
    · rw [hlocq p hpq'] at hp
      intro h; apply hI.wRet p v hp
      cases h' : g.wts (curOp α p) with
      | none => rfl
      | some t => rw [hwts' _ _ h'] at h; cases h
  · rw [hcompl] at hc; rw [opOf_append_tau] at h
    intro h'
    cases h'' : g.wts x with
    | none => exact hI.complW x v h hc h''
    | some t => rw [hwts' _ _ h''] at h'; cases h'
  · by_cases hpq' : p = q
    · subst hpq'; simp [hC'] at hp
    · rw [hlocq p hpq'] at hp
      obtain ⟨h1, h2⟩ := hI.rRead p i best hp
      exact ⟨hcell _ h1, by simpa [hg'] using h2⟩
  · by_cases hpq' : p = q
    · subst hpq'; simp [hC'] at hp
    · rw [hlocq p hpq'] at hp; simpa [hg'] using hI.rRet p v hp
  · obtain ⟨h1, h2, h3⟩ := hI.rcellInv x c h
    exact ⟨h1.mono, hcell _ h2, h3⟩
  · rw [hcompl] at hc; rw [opOf_append_tau] at h
    obtain ⟨c, h1, h2⟩ := hI.complR x h hc
    exact ⟨c, h1, by rw [hresp]; exact h2⟩
  · rw [hresp] at hr; rw [opOf_append_tau] at h; exact hI.writeResp x v r h hr

lemma Inv.step_rRead (hrun : (alg2 V v₀ n).run α = some C) (hI : Inv α C g) {q : Fin n}
    {i : Fin n} {best : Cell V} (hq : C.loc q = .rRead i best)
    (hs : (alg2 V v₀ n).step C (.tau q) = some C') :
    Inv (α ++ [.tau q]) C' (gstep α C g (.tau q)) := by
  have hpq : C.pend q = some .read ∧ best.2.length = n := by
    have := hI.loc q; rw [hq] at this; exact this
  rw [WSL.step_rRead (by simp [hpq.1]) hq, Option.some.injEq] at hs
  subst hs
  obtain ⟨hinvq, -, hcur⟩ := Impl.run_pend_curOp hrun hpq.1
  obtain ⟨hbest, hrq⟩ := hI.rRead q i best hq
  set nb := newBest best (C.mem i) with hnb
  have hnbOK : CellOK α g nb ∧ nb.2.length = n := by
    simp only [hnb, newBest]; split_ifs
    · exact ⟨hI.memCell i, hI.memLen i⟩
    · exact ⟨hbest, hpq.2⟩
  have hb : batch α C g.ws (.tau q) = [] := batch_of_not_wWrite (C := C) (by simp [hq])
  set r' := rcellStep α C g.rcell (.tau q) with hr'
  have hg : gstep α C g (.tau q) = ⟨g.ws, g.wts, r'⟩ := by simp [gstep, hb, wtsStep, hq, hr']
  rw [hg]
  have hr'eq : r' = if Alg4.next i = none then Function.update g.rcell (curOp α q) (some nb)
      else g.rcell := by simp [hr', rcellStep, hq, hnb]
  have hr'old : ∀ x, x ≠ curOp α q → r' x = g.rcell x := by
    intro x hx; rw [hr'eq]; split_ifs <;> simp [hx]
  have hr'mono : ∀ x c, g.rcell x = some c → r' x = some c := by
    intro x c h
    have : x ≠ curOp α q := by rintro rfl; rw [hrq] at h; cases h
    rw [hr'old x this, h]
  have hcell : ∀ c, CellOK α g c → CellOK (α ++ [.tau q]) ⟨g.ws, g.wts, r'⟩ c :=
    fun c h => h.mono _ (by simp)
  have hcompl : ∀ x, Completed (α ++ [.tau q]) x ↔ Completed α x :=
    completed_append_of_not_ret (by simp)
  have hresp : ∀ x, respOf (α ++ [.tau q]) x = respOf α x := respOf_append_of_not_ret (by simp)
  have hlocq : ∀ p, p ≠ q → Function.update C.loc q (rReadNext i nb) p = C.loc p :=
    fun p hp => by simp [hp]
  have hcurne : ∀ p, p ≠ q → curOp α p ≠ curOp α q := fun p hp h =>
    hp (curOp_injective α h)
  refine ⟨fun p => ?_, fun p pre hp => ?_, hI.memLen, hI.memLe, fun k => hcell _ (hI.memCell k),
    fun x hx => ?_, hI.wsNodup, hI.wtsInv, hI.wtsInj,
    fun p v hp => ?_, fun x v h hc => ?_, fun p i' best' hp => ?_, fun p v hp => ?_,
    fun x c h => ?_, fun x h hc => ?_, fun x v r h hr => ?_⟩
  · by_cases hpq' : p = q
    · subst hpq'
      simp only [Function.update_self, rReadNext]
      split
      · simp [LocOK, hpq.1, hnbOK.2]
      · simp [LocOK, hpq.1]
    · simp only [hlocq p hpq']; exact hI.loc p
  · by_cases hpq' : p = q
    · subst hpq'; simp only [Function.update_self, rReadNext] at hp; split at hp <;> cases hp
    · simp only [hlocq p hpq'] at hp; simp only [curOp_append_tau]; exact hI.partOK p pre hp
  · obtain ⟨h1, v, h2⟩ := hI.wsInv x hx
    exact ⟨h1.mono, v, opOf_append_of_eq_some h2 _⟩
  · by_cases hpq' : p = q
    · subst hpq'; simp only [Function.update_self, rReadNext] at hp; split at hp <;> cases hp
    · simp only [hlocq p hpq'] at hp; simpa using hI.wRet p v hp
  · rw [hcompl] at hc; rw [opOf_append_tau] at h; exact hI.complW x v h hc
  · simp only [curOp_append_tau]
    by_cases hpq' : p = q
    · subst hpq'
      simp only [Function.update_self, rReadNext] at hp
      split at hp
      · rename_i j hj
        cases hp
        refine ⟨hcell _ hnbOK.1, ?_⟩
        show r' _ = _; rw [hr'eq]; simpa [hj] using hrq
      · cases hp
    · simp only [hlocq p hpq'] at hp
      obtain ⟨h1, h2⟩ := hI.rRead p i' best' hp
      exact ⟨hcell _ h1, by show r' _ = _; rw [hr'old _ (hcurne p hpq')]; exact h2⟩
  · simp only [curOp_append_tau]
    by_cases hpq' : p = q
    · subst hpq'
      simp only [Function.update_self, rReadNext] at hp
      split at hp
      · cases hp
      · rename_i hj
        cases hp
        refine ⟨nb, ?_, rfl⟩
        show r' _ = _; rw [hr'eq]; simp [hj]
    · simp only [hlocq p hpq'] at hp
      obtain ⟨c, h1, h2⟩ := hI.rRet p v hp
      exact ⟨c, by show r' _ = _; rw [hr'old _ (hcurne p hpq')]; exact h1, h2⟩
  · change r' x = some c at h
    by_cases hx : x = curOp α q
    · subst hx
      rw [hr'eq] at h
      split_ifs at h
      · simp only [Function.update_self, Option.some.injEq] at h
        subst h
        exact ⟨hinvq.mono, hcell _ hnbOK.1, hnbOK.2⟩
      · rw [hrq] at h; cases h
    · rw [hr'old x hx] at h
      obtain ⟨h1, h2, h3⟩ := hI.rcellInv x c h
      exact ⟨h1.mono, hcell _ h2, h3⟩
  · rw [hcompl] at hc; rw [opOf_append_tau] at h
    obtain ⟨c, h1, h2⟩ := hI.complR x h hc
    exact ⟨c, hr'mono _ _ h1, by rw [hresp]; exact h2⟩
  · rw [hresp] at hr; rw [opOf_append_tau] at h; exact hI.writeResp x v r h hr

/-- The invariant is preserved by every step. -/
lemma Inv.step (hrun : (alg2 V v₀ n).run α = some C) (hI : Inv α C g) {ℓ : Lbl V v₀ n}
    (hs : (alg2 V v₀ n).step C ℓ = some C') : Inv (α ++ [ℓ]) C' (gstep α C g ℓ) := by
  cases ℓ with
  | inv q o => rw [gstep_inv]; exact hI.step_inv hrun hs
  | ret q r => rw [gstep_ret]; exact hI.step_ret hrun hs
  | tau q =>
    cases hq : C.loc q with
    | wRead v i pre => exact hI.step_wRead hrun hq hs
    | wWrite v ts => exact hI.step_wWrite hrun hq hs
    | rRead i best => exact hI.step_rRead hrun hq hs
    | idle =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      simp [alg2, hq, act] at hact
    | wRet v =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      simp [alg2, hq, act] at hact
    | rRet v =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      simp [alg2, hq, act] at hact

/-- **The state invariant** holds along every execution. -/
theorem inv_run (h : (alg2 V v₀ n).run α = some C) : Inv α C (ghost α) := by
  refine Impl.run_induction (Q := fun α C => Inv α C (ghost α)) inv_init ?_ h
  intro α C ℓ C' hrun hI hs
  rw [ghost_concat hrun]
  exact hI.step hrun hs

lemma Inv.cwLe_wWrite (hI : Inv α C g) {q : Fin n} {v : V} {ts : List ℕ}
    (hq : C.loc q = .wWrite v ts) : CwLe (C.mem q).2 ts := by
  have hlen : ts.length = n := by have := hI.loc q; rw [hq] at this; exact this.2
  obtain ⟨⟨-, hts⟩, -⟩ := hI.partOK q ts (by simp [hq, part])
  intro l
  rcases Nat.lt_or_ge l n with hl | hl
  · have := (hts ⟨l, hl⟩ (by rw [hlen]; exact hl)).1
    simp only at this; omega
  · rw [getD_eq_default _ _ (by rw [hI.memLen q]; exact hl)]; exact Nat.zero_le _

end Inv

end WSL

end Podc.RegisterLinTermination.Alg2
