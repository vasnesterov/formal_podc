import Cslib.Computability.Distributed.SharedMemory.SWSRRegister
import Mathlib
import Podc.SharedMemory.Progress
import Podc.Order.NatDescent

/-!
# Algorithm 2: a lock-free state-quiescent HI SWSR `K`-valued register (Theorem 9)

Algorithm 2 of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent Concurrent
Objects* (PODC 2024), with `TryRead` (Algorithm 3), implements a single-writer single-reader
register with values `Fin K` (the paper's `{1, …, K}`, here 0-based) and initial value `v₀`
from `K` binary registers `A[0], …, A[K-1]` (initially `A[v₀] = 1`, all others `0`).

* `Write(v)`: `A[v] ← 1`, then `A[v-1], …, A[0] ← 0`, then `A[v+1], …, A[K-1] ← 0`, return.
* `Read()`: repeat `TryRead()` until it succeeds. `TryRead()` scans up for the first `j` with
  `A[j] = 1` (failing if there is none), sets `val ← j`, then scans down `j-1, …, 0` and sets
  `val ← j'` whenever it reads `A[j'] = 1`; returns `val`.

The two processes are `Proc.w` (writer) and `Proc.r` (reader). In our model a failed `TryRead`
directly restarts the up-scan at index `0` (the step that reads `A[K-1] = 0` moves to the
up-scan state at `0`).

## Proof

Linearizability uses the reads-from criterion `SWSRReadsFrom` of
`Cslib.Computability.Distributed.SharedMemory.SWSRRegister`. The reads-from assignment is computed by a *ghost run*
(`ghost`) alongside the execution: for every cell `i`, `src i` is the number of the `Write`
(1-based, `0` = initial value) that performed the last low-level write to `A[i]`; when the reader
reads `A[j] = 1` and sets `val ← j` it records `cur ← src j`; when the `Read` returns, `cur` is
its reads-from value. The invariant `Inv` (preserved by every step, `inv_run`) contains:

* `A[i] = 1 ↔ value of write src(i) = i` (`Inv.mem`), and the shape of `src` during a write;
* the paper's case analysis (read-before-read, cases `v₁ = v₂`, `v₁ > v₂`, `v₁ < v₂`) is turned
  into forward invariants about the last completed read (`last`, `lastv`): `src[lastv] ≥ last`
  and every `A[j] = 1` with `j ≤ lastv` has `src j ≥ last`; once the up-scan passes `lastv`,
  all `src ≥ last`.

HI: in a state-quiescent configuration the writer is idle (or `K = 1`), so `A` is the indicator
of the current value (`mem_of_stateQuiescent`). Lock-freedom: once responses stop, the writer
takes at most `2K + 2` more steps (measure `wμ`), and then the reader, running against a fixed
memory that contains a `1` (`exists_one`), returns within `4K + 1` steps (measure `rμ`).

## Main results

* `alg2` — the implementation; `rf` / `ghost` — the reads-from assignment.
* `linearizable`, `lockFree`, `stateQuiescentHI`, `theorem9` (Theorem 9).
* `sampleExec` + an `example`: `Write(1)` followed by a `Read()` returning `1` is a valid
  execution (non-vacuity).
-/

namespace Cslib.SharedMemory

namespace Alg2

/-- The two processes: the writer and the reader. -/
inductive Proc where
  | w
  | r
  deriving DecidableEq

variable {K : ℕ}

/-- `j mod K` as an element of `Fin K` (the argument `x` only witnesses `K > 0`). -/
def fin (x : Fin K) (j : ℕ) : Fin K := ⟨j % K, Nat.mod_lt _ (Nat.zero_lt_of_lt x.isLt)⟩

lemma fin_val (x : Fin K) {j : ℕ} (h : j < K) : (fin x j).val = j := Nat.mod_eq_of_lt h

/-- Local states. -/
inductive Loc (K : ℕ) where
  /-- No pending operation. -/
  | idle
  /-- Writer executing `Write(v)`, about to perform its `t`-th low-level write. -/
  | wr (v : Fin K) (t : ℕ)
  /-- Reader in the up-scan, about to read `A[j]`. -/
  | up (j : Fin K)
  /-- Reader in the down-scan with current value `val`, about to read `A[d-1]` (returns `val`
  if `d = 0`). -/
  | down (val : Fin K) (d : ℕ)

/-- The `t`-th cell written by `Write(v)`: `v, v-1, …, 0, v+1, …, K-1`. -/
def order (v t : ℕ) : ℕ := if t ≤ v then v - t else t

/-- The position of cell `i` in the writing order of `Write(v)`. -/
def pos (v i : ℕ) : ℕ := if i ≤ v then v - i else i

/-- The high-level object: a register with values `Fin K`. -/
abbrev Reg (v₀ : Fin K) : ObjSpec := register (Fin K) v₀

/-- The base objects: binary registers `A[i]`. -/
abbrev Base (K : ℕ) : Fin K → ObjSpec := fun _ => binaryRegister

/-- The code. -/
def act (v₀ : Fin K) : Loc K → Action (Reg v₀) (Base K) (Loc K)
  | .idle => .ret v₀ .idle
  | .wr v t =>
    if t < K then
      .access (fin v (order v t)) (.write (decide (v = fin v (order v t)))) (fun _ => .wr v (t + 1))
    else .ret v .idle
  | .up j => .access j .read (fun b => if b = true then .down j j.val else .up (fin j (j.val + 1)))
  | .down val 0 => .ret val .idle
  | .down val (d + 1) =>
    .access (fin val d) .read (fun b => if b = true then .down (fin val d) d else .down val d)

/-- Invocation: `Write(v)` starts at the first low-level write, `Read()` at the up-scan. -/
def start (v₀ : Fin K) : RWOp (Fin K) → Loc K
  | .write v => .wr v 0
  | .read => .up (fin v₀ 0)

/-- **Algorithm 2.** -/
def alg2 (v₀ : Fin K) : Impl (Reg v₀) (Base K) Proc (Loc K) where
  memInit i := decide (v₀ = i)
  locInit _ := .idle
  invoke _ _ o := start v₀ o
  act _ l := act v₀ l
  allowed := RWOp.SWSR Proc.w Proc.r

/-- Configurations of Algorithm 2. -/
abbrev Cfg (v₀ : Fin K) := Config (Reg v₀) (Base K) Proc (Loc K)

/-- Labels of executions of Algorithm 2. -/
abbrev Lbl (v₀ : Fin K) := Label Proc (Reg v₀)

/-! ## Ghost state: the reads-from relation -/

/-- Ghost state. -/
structure Ghost (K : ℕ) where
  /-- `src i`: number (1-based) of the write that last wrote `A[i]` (`0`: initial value). -/
  src : Fin K → ℕ
  /-- Number of invoked writes. -/
  nw : ℕ
  /-- `src` of the cell whose `1` set the reader's current `val`. -/
  cur : ℕ
  /-- Reads-from value of the last completed read (`0` if none). -/
  last : ℕ
  /-- Return value of the last completed read (`v₀` if none). -/
  lastv : Fin K
  /-- Reads-from values of the completed reads. -/
  rfs : List ℕ

/-- Initial ghost state. -/
def Ghost.init (v₀ : Fin K) : Ghost K := ⟨fun _ => 0, 0, 0, 0, v₀, []⟩

/-- Ghost update for a step from configuration `C`. -/
def gstep {v₀ : Fin K} (C : Cfg v₀) (g : Ghost K) : Lbl v₀ → Ghost K
  | .inv _ (.write _) => { g with nw := g.nw + 1 }
  | .inv _ .read => g
  | .tau p =>
    match C.loc p with
    | .wr v t => { g with src := Function.update g.src (fin v (order v t)) g.nw }
    | .up j => if C.mem j = true then { g with cur := g.src j } else g
    | .down val (d + 1) =>
      if C.mem (fin val d) = true then { g with cur := g.src (fin val d) } else g
    | _ => g
  | .ret p _ =>
    match C.loc p with
    | .down val _ => { g with rfs := g.rfs ++ [g.cur], last := g.cur, lastv := val }
    | _ => g

/-- The ghost run from configuration `C` and ghost state `g`. -/
noncomputable def ghostFrom (v₀ : Fin K) : Cfg v₀ → Ghost K → List (Lbl v₀) → Ghost K
  | _, g, [] => g
  | C, g, ℓ :: α =>
    match (alg2 v₀).step C ℓ with
    | some C' => ghostFrom v₀ C' (gstep C g ℓ) α
    | none => g

/-- The ghost state at the end of an execution. -/
noncomputable def ghost (v₀ : Fin K) (α : List (Lbl v₀)) : Ghost K :=
  ghostFrom v₀ (alg2 v₀).initCfg (Ghost.init v₀) α

/-- The reads-from assignment: read `k` reads from write `rf α k` (1-based, `0` = initial). -/
noncomputable def rf (v₀ : Fin K) (α : List (Lbl v₀)) (k : ℕ) : ℕ := (ghost v₀ α).rfs.getD k 0

lemma ghostFrom_append {v₀ : Fin K} {C C₁ : Cfg v₀} {α : List (Lbl v₀)}
    (h : (alg2 v₀).runFrom C α = some C₁) (g : Ghost K) (β : List (Lbl v₀)) :
    ghostFrom v₀ C g (α ++ β) = ghostFrom v₀ C₁ (ghostFrom v₀ C g α) β := by
  induction α generalizing C g with
  | nil => simp at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg2 v₀).step C ℓ with
    | none => simp [hs] at h
    | some C' =>
      simp only [hs, Option.bind_some] at h
      simp only [List.cons_append, ghostFrom, hs]
      exact ih h _

lemma ghost_snoc {v₀ : Fin K} {C C' : Cfg v₀} {α : List (Lbl v₀)} {ℓ : Lbl v₀}
    (h : (alg2 v₀).run α = some C) (hs : (alg2 v₀).step C ℓ = some C') :
    ghost v₀ (α ++ [ℓ]) = gstep C (ghost v₀ α) ℓ := by
  rw [ghost, ghostFrom_append h]
  simp [ghostFrom, hs, ghost]

/-! ## The invariant -/

/-- The phase invariant of a pending read. -/
def Phase {v₀ : Fin K} (α : List (Lbl v₀)) (C : Cfg v₀) (g : Ghost K) : Prop :=
  (∃ j, C.loc .r = .up j ∧ (g.lastv < j → ∀ i, g.last ≤ g.src i)) ∨
  (∃ val d, C.loc .r = .down val d ∧ d ≤ val.val ∧
    writeVal v₀ (opsOf α .w) g.cur = val ∧ g.cur ≤ g.src val ∧
    (∀ j : Fin K, d ≤ j.val → j < val → C.mem j = true → g.cur ≤ g.src j) ∧
    g.last ≤ g.cur ∧ (g.lastv < val → ∀ i, g.last ≤ g.src i) ∧
    ¬ Precedes α (.w, g.cur) (.r, (respsOf α .r).length))

/-- The invariant of Algorithm 2 (with its ghost state). -/
structure Inv {v₀ : Fin K} (α : List (Lbl v₀)) (C : Cfg v₀) (g : Ghost K) : Prop where
  nw : g.nw = (opsOf α .w).length
  w_idle : C.pend .w = none → C.loc .w = .idle ∧ ∀ i, g.src i = (opsOf α .w).length
  w_pend : ∀ o, C.pend .w = some o → ∃ v t, o = .write v ∧ C.loc .w = .wr v t ∧ t ≤ K ∧
    ∀ i, g.src i = if pos v i < t then (opsOf α .w).length else (opsOf α .w).length - 1
  w_resp : ∀ j v x, opOf α (.w, j) = some (.write v) → respOf α (.w, j) = some x → x = v
  mem : ∀ i, C.mem i = decide (writeVal v₀ (opsOf α .w) (g.src i) = i)
  rfs_len : g.rfs.length = (respsOf α .r).length
  rf_val : ∀ k (hk : k < g.rfs.length),
    respOf α (.r, k) = some (writeVal v₀ (opsOf α .w) g.rfs[k])
  rf_le : ∀ x ∈ g.rfs, x ≤ (opsOf α .w).length
  rf_fut : ∀ k (hk : k < g.rfs.length), 0 < g.rfs[k] → ¬ Precedes α (.r, k) (.w, g.rfs[k] - 1)
  rf_over : ∀ k (hk : k < g.rfs.length), ¬ Precedes α (.w, g.rfs[k]) (.r, k)
  rf_sorted : g.rfs.Pairwise (· ≤ ·)
  rf_last : ∀ x ∈ g.rfs, x ≤ g.last
  last_val : writeVal v₀ (opsOf α .w) g.last = g.lastv
  last_src : g.last ≤ g.src g.lastv
  last_low : ∀ j : Fin K, j ≤ g.lastv → C.mem j = true → g.last ≤ g.src j
  r_idle : C.pend .r = none → C.loc .r = .idle
  r_pend : ∀ o, C.pend .r = some o →
    (∀ i, ¬ Precedes α (.w, g.src i) (.r, (respsOf α .r).length)) ∧ Phase α C g

lemma inv_init (v₀ : Fin K) : Inv ([] : List (Lbl v₀)) (alg2 v₀).initCfg (Ghost.init v₀) where
  nw := rfl
  w_idle _ := ⟨rfl, fun _ => rfl⟩
  w_pend o h := by simp [Impl.initCfg] at h
  w_resp j v x _ h := by simp [respOf] at h
  mem i := rfl
  rfs_len := rfl
  rf_val k hk := by simp [Ghost.init] at hk
  rf_le x hx := by simp [Ghost.init] at hx
  rf_fut k hk := by simp [Ghost.init] at hk
  rf_over k hk := by simp [Ghost.init] at hk
  rf_sorted := List.Pairwise.nil
  rf_last x hx := by simp [Ghost.init] at hx
  last_val := rfl
  last_src := Nat.zero_le _
  last_low _ _ _ := Nat.zero_le _
  r_idle _ := rfl
  r_pend o h := by simp [Impl.initCfg] at h

/-! ### Helper lemmas for the invariant -/

section Helpers

variable {v₀ : Fin K} {α : List (Lbl v₀)} {C : Cfg v₀} {g : Ghost K}

lemma wv_snoc {ℓ : Lbl v₀} {m : ℕ} (h : m ≤ (opsOf α .w).length) :
    writeVal v₀ (opsOf (α ++ [ℓ]) .w) m = writeVal v₀ (opsOf α .w) m := by
  rw [opsOf_append]; exact writeVal_append_of_le h

lemma counts (hrun : (alg2 v₀).run α = some C) (p : Proc) :
    (C.pend p = none ∧ (opsOf α p).length = (respsOf α p).length) ∨
    (C.pend p ≠ none ∧ (opsOf α p).length = (respsOf α p).length + 1) :=
  (alg2 v₀).run_counts hrun p

lemma Inv.src_le (hI : Inv α C g) (i : Fin K) : g.src i ≤ (opsOf α .w).length := by
  cases h : C.pend .w with
  | none => rw [(hI.w_idle h).2 i]
  | some o =>
    obtain ⟨v, t, -, -, -, hs⟩ := hI.w_pend o h
    rw [hs i]; split_ifs <;> omega

lemma Inv.src_ge (hI : Inv α C g) (hrun : (alg2 v₀).run α = some C) (i : Fin K) :
    (respsOf α .w).length ≤ g.src i := by
  rcases counts hrun .w with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [(hI.w_idle h1).2 i]; omega
  · obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h1
    obtain ⟨v, t, -, -, -, hs⟩ := hI.w_pend o ho
    rw [hs i]; split_ifs <;> omega

lemma Inv.spread (hI : Inv α C g) (hrun : (alg2 v₀).run α = some C) (i j : Fin K) :
    g.src j ≤ g.src i + 1 := by
  rcases counts hrun .w with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [(hI.w_idle h1).2 i, (hI.w_idle h1).2 j]; omega
  · obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h1
    obtain ⟨v, t, -, -, -, hs⟩ := hI.w_pend o ho
    rw [hs i, hs j]; split_ifs <;> omega

/-- The completed-read facts transport along any step. -/
lemma Inv.rf_transport (hI : Inv α C g) (hwf : WellFormed α) (ℓ : Lbl v₀) :
    (∀ k (hk : k < g.rfs.length),
      respOf (α ++ [ℓ]) (.r, k) = some (writeVal v₀ (opsOf (α ++ [ℓ]) .w) g.rfs[k])) ∧
    (∀ x ∈ g.rfs, x ≤ (opsOf (α ++ [ℓ]) .w).length) ∧
    (∀ k (hk : k < g.rfs.length), 0 < g.rfs[k] →
      ¬ Precedes (α ++ [ℓ]) (.r, k) (.w, g.rfs[k] - 1)) ∧
    (∀ k (hk : k < g.rfs.length), ¬ Precedes (α ++ [ℓ]) (.w, g.rfs[k]) (.r, k)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    have hc : Completed α (.r, k) := by
      simp only [Completed]; rw [← hI.rfs_len]; exact hk
    rw [respOf_append_of_completed hc, hI.rf_val k hk,
      wv_snoc (hI.rf_le _ (List.getElem_mem hk))]
  · intro x hx
    have := hI.rf_le x hx
    simp only [opsOf_append, List.length_append]; omega
  · intro k hk hpos hp
    apply hI.rf_fut k hk hpos
    apply hp.of_append_of_invoked
    have := hI.rf_le _ (List.getElem_mem hk)
    simp only [Invoked]; omega
  · intro k hk hp
    apply hI.rf_over k hk
    apply hp.of_append_of_invoked
    have := hwf.resps_le_ops .r
    have := hI.rfs_len
    simp only [Invoked]; omega

lemma Inv.last_val_snoc (hI : Inv α C g) (ℓ : Lbl v₀) :
    writeVal v₀ (opsOf (α ++ [ℓ]) .w) g.last = g.lastv := by
  rw [wv_snoc ((hI.last_src).trans (hI.src_le _)), hI.last_val]

/-- `(r, nR)` is invoked while a read is pending. -/
lemma invoked_pending_read (hrun : (alg2 v₀).run α = some C) {o} (h : C.pend .r = some o) :
    Invoked α (.r, (respsOf α .r).length) := by
  rcases counts hrun .r with ⟨h1, -⟩ | ⟨-, h2⟩
  · simp [h1] at h
  · simp only [Invoked]; omega

end Helpers

section Cases

variable {v₀ : Fin K} {α : List (Lbl v₀)} {C C' : Cfg v₀} {g : Ghost K}

lemma inv_step_inv_w (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g) {v : Fin K}
    (hs : (alg2 v₀).step C (.inv .w (.write v)) = some C') :
    Inv (α ++ [.inv .w (.write v)]) C' (gstep C g (.inv .w (.write v))) := by
  obtain ⟨hpw, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hwf := Impl.Valid.wellFormed (alg2 v₀) ⟨C, hrun⟩
  have hops_w : opsOf (α ++ [.inv .w (.write v)]) .w = opsOf α .w ++ [.write v] := by simp
  have hresps : ∀ p, respsOf (α ++ [.inv .w (.write v)]) p = respsOf α p := by simp
  obtain ⟨hlw, hsrc⟩ := hI.w_idle hpw
  obtain ⟨t1, t2, t3, t4⟩ := hI.rf_transport hwf (.inv .w (.write v))
  have hpr : C'.pend .r = C.pend .r := by rw [hpend]; simp
  have hlr : C'.loc .r = C.loc .r := by rw [hloc]; simp
  have hpw' : C'.pend .w = some (.write v) := by rw [hpend]; simp
  have hlw' : C'.loc .w = .wr v 0 := by rw [hloc]; simp [alg2, start]
  simp only [gstep]
  refine
    { nw := by simp [hI.nw]
      w_idle := by simp [hpw']
      w_pend := ?_
      w_resp := ?_
      mem := ?_
      rfs_len := by simp [hresps, hI.rfs_len]
      rf_val := t1
      rf_le := t2
      rf_fut := t3
      rf_over := t4
      rf_sorted := hI.rf_sorted
      rf_last := hI.rf_last
      last_val := hI.last_val_snoc _
      last_src := hI.last_src
      last_low := by rw [hmem]; exact hI.last_low
      r_idle := by rw [hpr, hlr]; exact hI.r_idle
      r_pend := ?_ }
  · intro o ho
    rw [hpw'] at ho; cases ho
    refine ⟨v, 0, rfl, hlw', Nat.zero_le _, fun i => ?_⟩
    simp [hsrc i]
  · intro j v' x hop hx
    simp only [respOf, hresps] at hx
    have hj : j < (respsOf α .w).length := (List.getElem?_eq_some_iff.1 hx).1
    have hinv : Invoked α (.w, j) := lt_of_lt_of_le hj (hwf.resps_le_ops _)
    rw [opOf_append_of_invoked hinv] at hop
    exact hI.w_resp j v' x hop hx
  · intro i
    rw [hmem, hI.mem i, wv_snoc (hI.src_le i)]
  · intro o ho
    rw [hpr] at ho
    obtain ⟨hnp, hph⟩ := hI.r_pend o ho
    have hinv := invoked_pending_read hrun ho
    simp only [Phase, hresps]
    refine ⟨fun i hp => hnp i (hp.of_append_of_invoked hinv), ?_⟩
    rcases hph with ⟨j, hj, h2⟩ | ⟨val, d, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · exact Or.inl ⟨j, hlr ▸ hj, h2⟩
    · refine Or.inr ⟨val, d, hlr ▸ h1, h2, ?_, h4, hmem ▸ h5, h6, h7,
        fun hp => h8 (hp.of_append_of_invoked hinv)⟩
      rw [wv_snoc (h4.trans (hI.src_le _)), h3]

lemma inv_step_inv_r (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g)
    (hs : (alg2 v₀).step C (.inv .r .read) = some C') :
    Inv (α ++ [.inv .r .read]) C' (gstep C g (.inv .r .read)) := by
  obtain ⟨hpr, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hwf := Impl.Valid.wellFormed (alg2 v₀) ⟨C, hrun⟩
  have hops_w : opsOf (α ++ [.inv .r .read]) .w = opsOf α .w := by simp
  have hresps : ∀ p, respsOf (α ++ [.inv .r .read]) p = respsOf α p := by simp
  have hopw : ∀ j, opOf (α ++ [.inv .r .read]) (.w, j) = opOf α (.w, j) := by
    intro j; simp only [opOf, hops_w]
  obtain ⟨t1, t2, t3, t4⟩ := hI.rf_transport hwf (.inv .r .read)
  have hpw : C'.pend .w = C.pend .w := by rw [hpend]; simp
  have hlw : C'.loc .w = C.loc .w := by rw [hloc]; simp
  have hpr' : C'.pend .r = some .read := by rw [hpend]; simp
  have hlr' : C'.loc .r = .up (fin v₀ 0) := by rw [hloc]; simp [alg2, start]
  simp only [gstep]
  refine
    { nw := by rw [hops_w]; exact hI.nw
      w_idle := by rw [hpw, hlw, hops_w]; exact hI.w_idle
      w_pend := by rw [hpw, hlw, hops_w]; exact hI.w_pend
      w_resp := by
        intro j v x h1 h2
        rw [hopw] at h1
        simp only [respOf, hresps] at h2
        exact hI.w_resp j v x h1 h2
      mem := by rw [hmem, hops_w]; exact hI.mem
      rfs_len := by simp [hresps, hI.rfs_len]
      rf_val := t1
      rf_le := t2
      rf_fut := t3
      rf_over := t4
      rf_sorted := hI.rf_sorted
      rf_last := hI.rf_last
      last_val := hI.last_val_snoc _
      last_src := hI.last_src
      last_low := by rw [hmem]; exact hI.last_low
      r_idle := by simp [hpr']
      r_pend := ?_ }
  intro o ho
  simp only [Phase, hresps]
  refine ⟨fun i hp => ?_, Or.inl ⟨fin v₀ 0, hlr', fun h => ?_⟩⟩
  · have hc := hp.completed_of_append_singleton (by
      rcases counts hrun .r with ⟨-, h2⟩ | ⟨h1, -⟩
      · simp only [Invoked, opsOf_append]; simp; omega
      · exact absurd hpr h1)
    have := hI.src_ge hrun i
    simp only [Completed] at hc; omega
  · exfalso
    have : (fin v₀ 0).val = 0 := fin_val v₀ (Nat.zero_lt_of_lt v₀.isLt)
    rw [Fin.lt_def, this] at h; omega

lemma pos_lt {v i : ℕ} (hv : v < K) (hi : i < K) : pos v i < K := by
  unfold pos; split_ifs <;> omega

lemma inv_step_ret_w (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g) {x : Fin K}
    (hs : (alg2 v₀).step C (.ret .w x) = some C') :
    Inv (α ++ [.ret .w x]) C' (gstep C g (.ret .w x)) := by
  obtain ⟨hpw, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpw
  obtain ⟨v, t, rfl, hlw, ht, hsrc⟩ := hI.w_pend o ho
  rw [hlw] at hact
  simp only [alg2, act] at hact
  split_ifs at hact with htK
  cases hact
  have htK' : t = K := by omega
  subst htK'
  have hwf := Impl.Valid.wellFormed (alg2 v₀) ⟨C, hrun⟩
  have hops : ∀ p, opsOf (α ++ [.ret .w x]) p = opsOf α p := by simp
  have hresps_r : respsOf (α ++ [.ret .w x]) .r = respsOf α .r := by simp
  have hresps_w : respsOf (α ++ [.ret .w x]) .w = respsOf α .w ++ [x] := by simp
  have hopw : ∀ j, opOf (α ++ [.ret .w x]) (.w, j) = opOf α (.w, j) := by
    intro j; simp only [opOf, hops]
  obtain ⟨t1, t2, t3, t4⟩ := hI.rf_transport hwf (.ret .w x)
  have hpr : C'.pend .r = C.pend .r := by rw [hpend]; simp
  have hlr : C'.loc .r = C.loc .r := by rw [hloc]; simp
  have hpw' : C'.pend .w = none := by rw [hpend]; simp
  have hlw' : C'.loc .w = .idle := by rw [hloc]; simp
  have hcnt : (opsOf α .w).length = (respsOf α .w).length + 1 := by
    rcases counts hrun .w with ⟨h1, -⟩ | ⟨-, h2⟩
    · simp [h1] at ho
    · exact h2
  have hlast := (alg2 v₀).run_pend hrun ho
  simp only [gstep, hlw]
  refine
    { nw := by rw [hops]; exact hI.nw
      w_idle := fun _ => ⟨hlw', fun i => ?_⟩
      w_pend := by simp [hpw']
      w_resp := ?_
      mem := by rw [hmem, hops]; exact hI.mem
      rfs_len := by simp [hresps_r, hI.rfs_len]
      rf_val := t1
      rf_le := t2
      rf_fut := t3
      rf_over := t4
      rf_sorted := hI.rf_sorted
      rf_last := hI.rf_last
      last_val := hI.last_val_snoc _
      last_src := hI.last_src
      last_low := by rw [hmem]; exact hI.last_low
      r_idle := by rw [hpr, hlr]; exact hI.r_idle
      r_pend := ?_ }
  · rw [hsrc i, hops, ite_eq_left (pos_lt x.isLt i.isLt)]
  · intro j v' y hop hy
    rw [hopw] at hop
    simp only [respOf, hresps_w] at hy
    rcases Nat.lt_or_ge j (respsOf α .w).length with hj | hj
    · rw [List.getElem?_append_left hj] at hy
      exact hI.w_resp j v' y hop hy
    · have hj' : j = (respsOf α .w).length := by
        have := (List.getElem?_eq_some_iff.1 hy).1; simp at this; omega
      subst hj'
      rw [List.getElem?_append_right (le_refl _)] at hy
      simp at hy
      rw [List.getLast?_eq_getElem?] at hlast
      simp only [opOf, hcnt, Nat.add_sub_cancel] at hlast hop
      rw [hlast] at hop
      cases hop; exact hy.symm
  · intro o' ho'
    rw [hpr] at ho'
    obtain ⟨hnp, hph⟩ := hI.r_pend o' ho'
    have hinv := invoked_pending_read hrun ho'
    simp only [Phase, hresps_r]
    refine ⟨fun i hp => hnp i (hp.of_append_of_invoked hinv), ?_⟩
    rcases hph with ⟨j, hj, h2⟩ | ⟨val, d, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · exact Or.inl ⟨j, hlr ▸ hj, h2⟩
    · refine Or.inr ⟨val, d, hlr ▸ h1, h2, ?_, h4, hmem ▸ h5, h6, h7,
        fun hp => h8 (hp.of_append_of_invoked hinv)⟩
      rw [hops, h3]

lemma forall_getElem_snoc {l : List ℕ} {c : ℕ} {Q : ℕ → ℕ → Prop}
    (h1 : ∀ k (hk : k < l.length), Q k l[k]) (h2 : Q l.length c) :
    ∀ k (hk : k < (l ++ [c]).length), Q k (l ++ [c])[k] := by
  intro k hk
  rcases Nat.lt_or_ge k l.length with h | h
  · rw [List.getElem_append_left h]; exact h1 k h
  · have : k = l.length := by simp at hk; omega
    subst this; simpa using h2

lemma inv_step_ret_r (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g) {x : Fin K}
    (hs : (alg2 v₀).step C (.ret .r x) = some C') :
    Inv (α ++ [.ret .r x]) C' (gstep C g (.ret .r x)) := by
  obtain ⟨hpr, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpr
  obtain ⟨hnp, hph⟩ := hI.r_pend o ho
  have hinv := invoked_pending_read hrun ho
  rcases hph with ⟨j, hj, -⟩ | ⟨val, d, hlr, h2, h3, h4, h5, h6, h7, h8⟩
  · rw [hj] at hact; simp [alg2, act] at hact
  rw [hlr] at hact
  rcases d with _ | d
  swap
  · simp [alg2, act] at hact
  simp only [alg2, act, Action.ret.injEq] at hact
  obtain ⟨rfl, rfl⟩ := hact
  have hwf := Impl.Valid.wellFormed (alg2 v₀) ⟨C, hrun⟩
  have hops : ∀ p, opsOf (α ++ [.ret .r val]) p = opsOf α p := by simp
  have hresps_w : respsOf (α ++ [.ret .r val]) .w = respsOf α .w := by simp
  have hresps_r : respsOf (α ++ [.ret .r val]) .r = respsOf α .r ++ [val] := by simp
  obtain ⟨t1, t2, t3, t4⟩ := hI.rf_transport hwf (.ret .r val)
  have hpw : C'.pend .w = C.pend .w := by rw [hpend]; simp
  have hlw : C'.loc .w = C.loc .w := by rw [hloc]; simp
  have hpr' : C'.pend .r = none := by rw [hpend]; simp
  have hlr' : C'.loc .r = .idle := by rw [hloc]; simp
  have hcur := h4.trans (hI.src_le val)
  simp only [gstep, hlr]
  refine
    { nw := by rw [hops]; exact hI.nw
      w_idle := by rw [hpw, hlw, hops]; exact hI.w_idle
      w_pend := by rw [hpw, hlw, hops]; exact hI.w_pend
      w_resp := by
        intro j v y h1 h2
        simp only [opOf, hops] at h1
        simp only [respOf, hresps_w] at h2
        exact hI.w_resp j v y h1 h2
      mem := by rw [hmem, hops]; exact hI.mem
      rfs_len := by simp [hresps_r, hI.rfs_len]
      rf_val := forall_getElem_snoc (Q := fun k y => respOf (α ++ [.ret .r val]) (.r, k) =
        some (writeVal v₀ (opsOf (α ++ [.ret .r val]) .w) y)) t1 ?_
      rf_le := ?_
      rf_fut := forall_getElem_snoc
        (Q := fun k y => 0 < y → ¬ Precedes (α ++ [.ret .r val]) (.r, k) (.w, y - 1)) t3 ?_
      rf_over := forall_getElem_snoc
        (Q := fun k y => ¬ Precedes (α ++ [.ret .r val]) (.w, y) (.r, k)) t4 ?_
      rf_sorted := ?_
      rf_last := ?_
      last_val := by rw [hops]; exact h3
      last_src := h4
      last_low := ?_
      r_idle := fun _ => hlr'
      r_pend := by simp [hpr'] }
  · simp [respOf, hresps_r, hI.rfs_len, hops, h3]
  · intro y hy
    rw [hops]
    rcases List.mem_append.1 hy with hy | hy
    · exact hI.rf_le y hy
    · simp at hy; subst hy; exact hcur
  · intro hpos hp
    have hp' := hp.of_append_of_invoked (by simp only [Invoked]; omega)
    have := hp'.completed
    simp [Completed, hI.rfs_len] at this
  · intro hp
    rw [hI.rfs_len] at hp
    exact h8 (hp.of_append_of_invoked hinv)
  · rw [List.pairwise_append]
    refine ⟨hI.rf_sorted, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    exact (hI.rf_last a ha).trans h6
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact (hI.rf_last y hy).trans h6
    · simp at hy; subst hy; exact le_refl _
  · intro j hj hmj
    rw [hmem] at hmj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact h5 j (Nat.zero_le _) hj hmj
    · exact h4

lemma order_lt {v t : ℕ} (hv : v < K) (ht : t < K) : order v t < K := by
  unfold order; split_ifs <;> omega

lemma pos_order {v t : ℕ} : pos v (order v t) = t := by
  unfold pos order; split_ifs <;> omega

lemma pos_inj {v i j : ℕ} (h : pos v i = pos v j) : i = j := by
  unfold pos at h; split_ifs at h <;> omega

lemma inv_step_tau_w (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g)
    (hs : (alg2 v₀).step C (.tau .w) = some C') :
    Inv (α ++ [.tau .w]) C' (gstep C g (.tau .w)) := by
  obtain ⟨hpw, hpend, i₀, o₀, k₀, hact, hmem, hloc⟩ := Impl.step_tau hs
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpw
  obtain ⟨v, t, rfl, hlw, ht, hsrc⟩ := hI.w_pend o ho
  rw [hlw] at hact
  simp only [alg2, act] at hact
  split_ifs at hact with htK
  cases hact
  set c := fin v (order v t) with hc
  have hcv : c.val = order v t := fin_val v (order_lt v.isLt htK)
  have hposc : pos v c = t := by rw [hcv, pos_order]
  have hwf := Impl.Valid.wellFormed (alg2 v₀) ⟨C, hrun⟩
  have hops : ∀ p, opsOf (α ++ [.tau .w]) p = opsOf α p := by simp
  have hresps : ∀ p, respsOf (α ++ [.tau .w]) p = respsOf α p := by simp
  obtain ⟨t1, t2, t3, t4⟩ := hI.rf_transport hwf (.tau .w)
  have hpr : C'.pend .r = C.pend .r := by rw [hpend]
  have hlr : C'.loc .r = C.loc .r := by rw [hloc]; simp
  have hlw' : C'.loc .w = .wr v (t + 1) := by rw [hloc]; simp
  have hcnt : (opsOf α .w).length = (respsOf α .w).length + 1 := by
    rcases counts hrun .w with ⟨h1, -⟩ | ⟨-, h2⟩
    · simp [h1] at ho
    · exact h2
  have hlast := (alg2 v₀).run_pend hrun ho
  have hwv : writeVal v₀ (opsOf α .w) (opsOf α .w).length = v := by
    rw [List.getLast?_eq_getElem?] at hlast
    rw [hcnt] at hlast ⊢
    exact writeVal_succ (by simpa using hlast)
  set n := (opsOf α .w).length with hn
  have hmem' : ∀ i, C'.mem i = if i = c then decide (v = c) else C.mem i := by
    intro i; rw [hmem, Function.update_apply]
  simp only [gstep, hlw]
  set src' := Function.update g.src c g.nw with hsrc'
  have hsrc'i : ∀ i, src' i = if i = c then n else g.src i := by
    intro i; rw [hsrc', Function.update_apply, hI.nw]
  have hmono : ∀ i, g.src i ≤ src' i := by
    intro i; rw [hsrc'i]; split_ifs with h
    · subst h; exact hI.src_le _
    · exact le_refl _
  have hcn : ∀ y, y ≤ g.src c → y ≤ n := fun y hy => hy.trans (hI.src_le c)
  refine
    { nw := by rw [hops]; exact hI.nw
      w_idle := by rw [hpend]; intro h; exact absurd h hpw
      w_pend := ?_
      w_resp := by
        intro j v' y h1 h2
        simp only [opOf, hops] at h1
        simp only [respOf, hresps] at h2
        exact hI.w_resp j v' y h1 h2
      mem := ?_
      rfs_len := by simp [hresps, hI.rfs_len]
      rf_val := t1
      rf_le := t2
      rf_fut := t3
      rf_over := t4
      rf_sorted := hI.rf_sorted
      rf_last := hI.rf_last
      last_val := hI.last_val_snoc _
      last_src := hI.last_src.trans (hmono _)
      last_low := ?_
      r_idle := by rw [hpr, hlr]; exact hI.r_idle
      r_pend := ?_ }
  · intro o' ho'
    rw [hpend, ho] at ho'; cases ho'
    refine ⟨v, t + 1, rfl, hlw', htK, fun i => ?_⟩
    dsimp only
    rw [hops, hsrc'i]
    split_ifs with h1 h2 h2
    · rfl
    · subst h1; omega
    · rw [hsrc i, ite_eq_left (by have := pos_inj (v := v.val) (i := i.val) (j := c.val); omega)]
    · rw [hsrc i, ite_eq_right (by omega)]
  · intro i
    dsimp only
    rw [hmem', hops]
    simp only [hsrc'i]
    by_cases h : i = c
    · simp [h, hwv]
    · simp only [h, ite_false]; exact hI.mem i
  · intro j hj hmj
    dsimp only at hj ⊢
    rw [hmem'] at hmj
    rw [hsrc'i]
    split_ifs at hmj ⊢ with h
    · exact hI.last_src.trans (hI.src_le _)
    · exact hI.last_low j hj hmj
  · intro o' ho'
    rw [hpr] at ho'
    obtain ⟨hnp, hph⟩ := hI.r_pend o' ho'
    have hinv := invoked_pending_read hrun ho'
    simp only [Phase, hresps, hops]
    refine ⟨fun i hp => ?_, ?_⟩
    · rw [hsrc'i] at hp
      split_ifs at hp with h
      · have := hp.completed
        simp only [Completed, hresps] at this; omega
      · exact hnp i (hp.of_append_of_invoked hinv)
    rcases hph with ⟨j, hj, h2⟩ | ⟨val, d, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · exact Or.inl ⟨j, hlr ▸ hj, fun h i => (h2 h i).trans (hmono i)⟩
    · refine Or.inr ⟨val, d, hlr ▸ h1, h2, h3, h4.trans (hmono _), ?_, h6,
        fun h i => (h7 h i).trans (hmono i), fun hp => h8 (hp.of_append_of_invoked hinv)⟩
      intro j hdj hjv hmj
      rw [hmem'] at hmj
      rw [hsrc'i]
      split_ifs at hmj ⊢ with h
      · exact h4.trans (hI.src_le _)
      · exact h5 j hdj hjv hmj

lemma inv_tau_r_aux (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g) {o : RWOp (Fin K)}
    (ho : C.pend .r = some o) (hpend : C'.pend = C.pend) (hmem : C'.mem = C.mem)
    (hlw : C'.loc .w = C.loc .w) (c : ℕ) (hph : Phase α C' { g with cur := c }) :
    Inv (α ++ [.tau .r]) C' { g with cur := c } := by
  have hwf := Impl.Valid.wellFormed (alg2 v₀) ⟨C, hrun⟩
  have hops : ∀ p, opsOf (α ++ [.tau .r]) p = opsOf α p := by simp
  have hresps : ∀ p, respsOf (α ++ [.tau .r]) p = respsOf α p := by simp
  obtain ⟨t1, t2, t3, t4⟩ := hI.rf_transport hwf (.tau .r)
  have hinv := invoked_pending_read hrun ho
  obtain ⟨hnp, -⟩ := hI.r_pend o ho
  refine
    { nw := by rw [hops]; exact hI.nw
      w_idle := by rw [hpend, hlw, hops]; exact hI.w_idle
      w_pend := by rw [hpend, hlw, hops]; exact hI.w_pend
      w_resp := by
        intro j v y h1 h2
        simp only [opOf, hops] at h1
        simp only [respOf, hresps] at h2
        exact hI.w_resp j v y h1 h2
      mem := by rw [hmem, hops]; exact hI.mem
      rfs_len := by simp [hresps, hI.rfs_len]
      rf_val := t1
      rf_le := t2
      rf_fut := t3
      rf_over := t4
      rf_sorted := hI.rf_sorted
      rf_last := hI.rf_last
      last_val := hI.last_val_snoc _
      last_src := hI.last_src
      last_low := by rw [hmem]; exact hI.last_low
      r_idle := by rw [hpend, ho]; simp
      r_pend := ?_ }
  intro o' _
  simp only [Phase, hresps, hops]
  refine ⟨fun i hp => hnp i (hp.of_append_of_invoked hinv), ?_⟩
  rcases hph with ⟨j, hj, h2⟩ | ⟨val, d, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact Or.inl ⟨j, hj, h2⟩
  · exact Or.inr ⟨val, d, h1, h2, h3, h4, h5, h6, h7,
      fun hp => h8 (hp.of_append_of_invoked hinv)⟩

lemma inv_step_tau_r (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g)
    (hs : (alg2 v₀).step C (.tau .r) = some C') :
    Inv (α ++ [.tau .r]) C' (gstep C g (.tau .r)) := by
  obtain ⟨hpr, hpend, j, o₀, k₀, hact, hmem, hloc⟩ := Impl.step_tau hs
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpr
  obtain ⟨hnp, hph⟩ := hI.r_pend o ho
  have hlw : C'.loc .w = C.loc .w := by rw [hloc]; simp
  have hgeq : g = { g with cur := g.cur } := rfl
  rcases hph with ⟨j', hj, hG2⟩ | ⟨val, d, hlr, h2, h3, h4, h5, h6, h7, h8⟩
  · -- up-scan: read `A[j]`
    rw [hj] at hact
    simp only [alg2, act] at hact
    cases hact
    have hmem' : C'.mem = C.mem := by rw [hmem]; simp
    have hlr' : C'.loc .r = if C.mem j = true then .down j j.val else .up (fin j (j.val + 1)) := by
      rw [hloc]; simp
    simp only [gstep, hj]
    by_cases hb : C.mem j = true
    · simp only [hb, ite_true] at hlr' ⊢
      apply inv_tau_r_aux hrun hI ho hpend hmem' hlw
      refine Or.inr ⟨j, j.val, hlr', le_refl _, ?_, le_refl _, ?_, ?_, ?_, hnp j⟩
      · have := hI.mem j; rw [hb] at this; exact (of_decide_eq_true this.symm)
      · intro jj h1 h2; rw [Fin.lt_def] at h2; omega
      · by_cases hjl : j ≤ g.lastv
        · exact hI.last_low j hjl hb
        · exact hG2 (lt_of_not_ge hjl) j
      · exact hG2
    · simp only [hb, ite_false, Bool.false_eq_true] at hlr' ⊢
      rw [hgeq]
      apply inv_tau_r_aux hrun hI ho hpend hmem' hlw
      refine Or.inl ⟨_, hlr', fun h i => ?_⟩
      dsimp only at h ⊢
      rcases lt_trichotomy g.lastv j with hl | hl | hl
      · exact hG2 hl i
      · subst hl
        have hne : g.last ≠ g.src g.lastv := by
          intro heq
          have := hI.mem g.lastv
          rw [← heq, hI.last_val] at this
          simp at this; exact hb this
        have := hI.spread hrun i g.lastv
        have := hI.last_src
        omega
      · exfalso
        have h1 : (fin j (j.val + 1)).val ≤ j.val + 1 := Nat.mod_le _ _
        rw [Fin.lt_def] at h hl
        omega
  · -- down-scan
    rw [hlr] at hact
    rcases d with _ | d
    · simp [alg2, act] at hact
    simp only [alg2, act] at hact
    cases hact
    have hmem' : C'.mem = C.mem := by rw [hmem]; simp
    simp only [gstep, hlr]
    set c := fin val d with hc
    have hcv : c.val = d := fin_val val (by omega)
    have hlr' : C'.loc .r = if C.mem c = true then .down c d else .down val d := by
      rw [hloc]; simp
    by_cases hb : C.mem c = true
    · simp only [hb, ite_true] at hlr' ⊢
      apply inv_tau_r_aux hrun hI ho hpend hmem' hlw
      refine Or.inr ⟨c, d, hlr', hcv.ge, ?_, le_refl _, ?_, ?_, ?_, hnp c⟩
      · have := hI.mem c; rw [hb] at this; exact (of_decide_eq_true this.symm)
      · intro jj h1 h2; rw [Fin.lt_def] at h2; omega
      · by_cases hvl : val ≤ g.lastv
        · exact hI.last_low c (le_trans (le_of_lt (by rw [Fin.lt_def]; omega)) hvl) hb
        · exact h7 (lt_of_not_ge hvl) c
      · intro h; exact h7 (lt_trans h (by rw [Fin.lt_def]; omega))
    · simp only [hb, ite_false, Bool.false_eq_true] at hlr' ⊢
      rw [hgeq]
      apply inv_tau_r_aux hrun hI ho hpend hmem' hlw
      refine Or.inr ⟨val, d, hlr', by omega, h3, h4, ?_, h6, h7, h8⟩
      intro jj h1 h2 hm
      rw [hmem'] at hm
      rcases Nat.lt_or_ge d jj.val with h | h
      · exact h5 jj h h2 hm
      · have : jj = c := Fin.ext (by omega)
        subst this; exact absurd hm hb

end Cases

lemma inv_step {v₀ : Fin K} {α : List (Lbl v₀)} {C C' : Cfg v₀} {g : Ghost K} {ℓ : Lbl v₀}
    (hrun : (alg2 v₀).run α = some C) (hI : Inv α C g) (hs : (alg2 v₀).step C ℓ = some C') :
    Inv (α ++ [ℓ]) C' (gstep C g ℓ) := by
  cases ℓ with
  | inv p o =>
    have hal : RWOp.SWSR Proc.w Proc.r p o := (Impl.step_inv hs).2.1
    rcases hal with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩
    · exact inv_step_inv_w hrun hI hs
    · exact inv_step_inv_r hrun hI hs
  | tau p =>
    cases p
    · exact inv_step_tau_w hrun hI hs
    · exact inv_step_tau_r hrun hI hs
  | ret p x =>
    cases p
    · exact inv_step_ret_w hrun hI hs
    · exact inv_step_ret_r hrun hI hs

theorem inv_run {v₀ : Fin K} {α : List (Lbl v₀)} {C : Cfg v₀} (h : (alg2 v₀).run α = some C) :
    Inv α C (ghost v₀ α) :=
  Impl.run_induction (Q := fun α C => Inv α C (ghost v₀ α)) (inv_init v₀)
    (fun _ _ _ _ h1 hI h2 => by rw [ghost_snoc h1 h2]; exact inv_step h1 hI h2) h

end Alg2

end Cslib.SharedMemory

namespace Cslib.SharedMemory

namespace Alg2

variable {K : ℕ}

/-! ## Linearizability -/

/-- The reads-from assignment of the ghost run satisfies the reads-from criterion. -/
theorem readsFrom {v₀ : Fin K} {α : List (Lbl v₀)} (hα : (alg2 v₀).Valid α) :
    SWSRReadsFrom α Proc.w Proc.r (rf v₀ α) := by
  obtain ⟨C, hC⟩ := hα
  have hI := inv_run hC
  have hwf := Impl.Valid.wellFormed _ ⟨C, hC⟩
  have hget : ∀ k (hk : k < (respsOf α .r).length),
      rf v₀ α k = (ghost v₀ α).rfs[k]'(hI.rfs_len ▸ hk) := by
    intro k hk
    simp [rf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hI.rfs_len ▸ hk)]
  refine ⟨by decide, hwf, ?_, hI.w_resp, ?_, ?_, ?_, ?_⟩
  · intro p o ho; exact Impl.allowed_of_mem_opsOf _ ⟨C, hC⟩ ho
  · intro k hk; rw [hget k hk]; exact hI.rf_val _ _
  · intro k hk; rw [hget k hk]; exact hI.rf_fut _ _
  · intro k hk; rw [hget k hk]; exact hI.rf_over _ _
  · intro k k' hkk hk' _
    rw [hget k (by omega), hget k' hk']
    exact List.pairwise_iff_getElem.1 hI.rf_sorted _ _ _ _ hkk

/-- The reads-from linearization function. -/
noncomputable def linFun (v₀ : Fin K) (α : List (Lbl v₀)) : List (OpId Proc × RWOp (Fin K)) :=
  swsrLin α Proc.w Proc.r (rf v₀ α)

theorem isLinFun (v₀ : Fin K) : (alg2 v₀).IsLinFun (linFun v₀) :=
  Impl.isLinFun_swsrLin _ _ _ _ (fun _ h => readsFrom h)

/-- Algorithm 2 is linearizable. -/
theorem linearizable (v₀ : Fin K) : (alg2 v₀).Linearizable := ⟨_, isLinFun v₀⟩

/-! ## State-quiescent history independence -/

/-- In a state-quiescent configuration, the memory is the canonical representation of the
abstract state: `A[i] = 1` iff `i` is the current value. -/
theorem mem_of_stateQuiescent {v₀ : Fin K} {α : List (Lbl v₀)} {C : Cfg v₀}
    (h : (alg2 v₀).run α = some C) (hq : C.StateQuiescent) (i : Fin K) :
    C.mem i = decide (linState (A := Reg v₀) (linFun v₀ α) = i) := by
  have hI := inv_run h
  rw [linFun, linState_swsrLin, hI.mem i]
  cases hw : C.pend .w with
  | none => rw [(hI.w_idle hw).2 i]
  | some o =>
    obtain ⟨v, t, rfl, -⟩ := hI.w_pend _ hw
    have hro := hq _ _ hw
    have hall : ∀ q : Fin K, q = v := fun q => by
      have := hro q; simp at this; exact this.symm
    simp [hall (writeVal _ _ _), hall i]

/-- Algorithm 2 is state-quiescent history independent. -/
theorem stateQuiescentHI (v₀ : Fin K) : (alg2 v₀).StateQuiescentHI := by
  refine ⟨linFun v₀, isLinFun v₀, fun α α' C C' h h' hq hq' hs => ?_⟩
  funext i
  rw [mem_of_stateQuiescent h hq, mem_of_stateQuiescent h' hq', hs]

/-! ## Lock-freedom -/

/-- The value of the last invoked write, while it is pending. -/
lemma wv_pending {v₀ : Fin K} {α : List (Lbl v₀)} {C : Cfg v₀} {v : Fin K}
    (h : (alg2 v₀).run α = some C) (hw : C.pend .w = some (.write v)) :
    writeVal v₀ (opsOf α .w) (opsOf α .w).length = v := by
  have hcnt : (opsOf α .w).length = (respsOf α .w).length + 1 := by
    rcases counts h .w with ⟨h1, -⟩ | ⟨-, h2⟩
    · simp [h1] at hw
    · exact h2
  have hlast := (alg2 v₀).run_pend h hw
  rw [List.getLast?_eq_getElem?] at hlast
  rw [hcnt] at hlast ⊢
  exact writeVal_succ (by simpa using hlast)

/-- Some cell of `A` always holds `1`. -/
lemma exists_one {v₀ : Fin K} {α : List (Lbl v₀)} {C : Cfg v₀} (h : (alg2 v₀).run α = some C) :
    ∃ i, C.mem i = true := by
  have hI := inv_run h
  cases hw : C.pend .w with
  | none =>
    refine ⟨writeVal v₀ (opsOf α .w) (opsOf α .w).length, ?_⟩
    rw [hI.mem, (hI.w_idle hw).2]; simp
  | some o =>
    obtain ⟨v, t, rfl, -, -, hsrc⟩ := hI.w_pend _ hw
    rcases Nat.eq_zero_or_pos t with ht | ht
    · refine ⟨writeVal v₀ (opsOf α .w) ((opsOf α .w).length - 1), ?_⟩
      rw [hI.mem, hsrc, ite_eq_right (by omega)]; simp
    · refine ⟨v, ?_⟩
      rw [hI.mem, hsrc, ite_eq_left (by simp [pos]; omega), wv_pending h hw]; simp

/-- Progress measure of the writer. -/
def wμ : Loc K → ℕ
  | .idle => K + 2
  | .wr _ t => K - t
  | _ => 0

/-- Progress measure of the reader when the memory `M` is fixed (and has a `1`). -/
noncomputable def rμ (M : Fin K → Bool) : Loc K → ℕ
  | .idle => 4 * K + 1
  | .up j => by
    classical
    exact if ∃ i : Fin K, j ≤ i ∧ M i = true then 3 * K - j.val else 4 * K - j.val
  | .down _ d => d + 1
  | .wr _ _ => 0

lemma writer_step {v₀ : Fin K} {α : List (Lbl v₀)} {C C' : Cfg v₀} {ℓ : Lbl v₀}
    (hrun : (alg2 v₀).run α = some C) (hs : (alg2 v₀).step C ℓ = some C')
    (hret : ∀ x, ℓ ≠ .ret .w x) :
    wμ (C'.loc .w) ≤ wμ (C.loc .w) ∧ (ℓ.proc = .w → wμ (C'.loc .w) < wμ (C.loc .w)) := by
  have hI := inv_run hrun
  by_cases hp : ℓ.proc = .w
  · suffices wμ (C'.loc .w) < wμ (C.loc .w) from ⟨this.le, fun _ => this⟩
    cases ℓ with
    | inv p o =>
      simp only [Label.proc] at hp; subst hp
      obtain ⟨hpw, hal, -, hloc, -⟩ := Impl.step_inv hs
      rcases hal with ⟨-, v, rfl⟩ | ⟨h, -⟩
      · rw [hloc, (hI.w_idle hpw).1]; simp [alg2, start, wμ]
      · cases h
    | tau p =>
      simp only [Label.proc] at hp; subst hp
      obtain ⟨hpw, -, i₀, o₀, k₀, hact, -, hloc⟩ := Impl.step_tau hs
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpw
      obtain ⟨v, t, rfl, hlw, ht, -⟩ := hI.w_pend o ho
      rw [hlw] at hact
      simp only [alg2, act] at hact
      split_ifs at hact with htK
      cases hact
      rw [hloc, hlw]; simp [wμ]; omega
    | ret p x =>
      simp only [Label.proc] at hp; subst hp
      exact absurd rfl (hret x)
  · exact ⟨by rw [(Impl.step_other hs hp).1], fun h => absurd h hp⟩

lemma reader_step {v₀ : Fin K} {α : List (Lbl v₀)} {C C' : Cfg v₀} {ℓ : Lbl v₀}
    (hrun : (alg2 v₀).run α = some C) (hs : (alg2 v₀).step C ℓ = some C')
    (hp : ℓ.proc = .r) (hret : ∀ x, ℓ ≠ .ret .r x) :
    C'.mem = C.mem ∧ rμ C.mem (C'.loc .r) < rμ C.mem (C.loc .r) := by
  classical
  have hI := inv_run hrun
  cases ℓ with
  | inv p o =>
    simp only [Label.proc] at hp; subst hp
    obtain ⟨hpr, hal, -, hloc, hmem⟩ := Impl.step_inv hs
    refine ⟨hmem, ?_⟩
    rcases hal with ⟨h, -⟩ | ⟨-, rfl⟩
    · cases h
    · rw [hloc, hI.r_idle hpr]
      simp only [Function.update_self, alg2, start, rμ]
      split_ifs <;> omega
  | tau p =>
    simp only [Label.proc] at hp; subst hp
    obtain ⟨hpr, -, i₀, o₀, k₀, hact, hmem, hloc⟩ := Impl.step_tau hs
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpr
    obtain ⟨-, hph⟩ := hI.r_pend o ho
    rcases hph with ⟨j, hj, -⟩ | ⟨val, d, hlr, h2, -⟩
    · rw [hj] at hact
      simp only [alg2, act] at hact
      cases hact
      refine ⟨by rw [hmem]; simp, ?_⟩
      rw [hloc, hj]
      simp only [Function.update_self]
      have hjK := i₀.isLt
      by_cases hb : C.mem i₀ = true
      · simp only [hb, ↓reduceIte, rμ]
        rw [ite_eq_left ⟨i₀, le_refl _, hb⟩]; omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, rμ]
        obtain ⟨i₁, hi₁⟩ := exists_one hrun
        rcases Nat.lt_or_ge (i₀.val + 1) K with hlt | hge
        · have hv : (fin i₀ (i₀.val + 1)).val = i₀.val + 1 := fin_val i₀ hlt
          have hiff : (∃ i : Fin K, fin i₀ (i₀.val + 1) ≤ i ∧ C.mem i = true) ↔
              (∃ i : Fin K, i₀ ≤ i ∧ C.mem i = true) := by
            constructor
            · rintro ⟨i, h1, h2⟩
              exact ⟨i, by rw [Fin.le_def] at h1 ⊢; omega, h2⟩
            · rintro ⟨i, h1, h2⟩
              refine ⟨i, ?_, h2⟩
              rw [Fin.le_def] at h1 ⊢
              rcases Nat.lt_or_ge i₀.val i.val with h | h
              · omega
              · have : i = i₀ := Fin.ext (by omega)
                subst this; exact absurd h2 hb
          rw [hv]
          by_cases hex : ∃ i : Fin K, i₀ ≤ i ∧ C.mem i = true
          · rw [ite_eq_left (hiff.2 hex), ite_eq_left hex]; omega
          · rw [ite_eq_right (fun h => hex (hiff.1 h)), ite_eq_right hex]; omega
        · have hv : (fin i₀ (i₀.val + 1)).val = 0 := by
            simp only [fin]; rw [show i₀.val + 1 = K by omega, Nat.mod_self]
          have hnex : ¬ ∃ i : Fin K, i₀ ≤ i ∧ C.mem i = true := by
            rintro ⟨i, h1, h2⟩
            rw [Fin.le_def] at h1
            have : i = i₀ := Fin.ext (by omega)
            subst this; exact hb h2
          rw [ite_eq_right hnex, ite_eq_left ⟨i₁, by rw [Fin.le_def, hv]; omega, hi₁⟩, hv]
          omega
    · rw [hlr] at hact
      rcases d with _ | d
      · simp [alg2, act] at hact
      simp only [alg2, act] at hact
      cases hact
      refine ⟨by rw [hmem]; simp, ?_⟩
      rw [hloc, hlr]
      simp only [Function.update_self]
      split_ifs <;> simp [rμ]
  | ret p x =>
    simp only [Label.proc] at hp; subst hp
    exact absurd rfl (hret x)

/-- Algorithm 2 is lock-free. -/
theorem lockFree (v₀ : Fin K) : (alg2 v₀).LockFree := by
  intro e _ N
  by_contra hcon
  push Not at hcon
  have hreach := e.run_lbls
  -- the writer takes finitely many steps after `N`
  obtain ⟨N₁, -, hN₁⟩ := Nat.eventually_not_of_succ_le (f := fun m => wμ ((e.cfg m).loc .w))
    (N := N) (p := fun m => (e.lbl m).proc = .w)
    (fun m hm => (writer_step (hreach m) (e.step_eq m) (hcon m hm .w)).1)
    (fun m hm => (writer_step (hreach m) (e.step_eq m) (hcon m hm .w)).2)
  -- afterwards, only the reader moves; the memory is fixed
  have hr : ∀ m ≥ max N N₁, (e.lbl m).proc = .r := by
    intro m hm
    have := hN₁ m (by omega)
    cases h : (e.lbl m).proc
    · exact absurd h this
    · rfl
  set M := (e.cfg (max N N₁)).mem with hM
  have hmem : ∀ k, (e.cfg (max N N₁ + k)).mem = M := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← ih, ← Nat.add_assoc]
      exact (reader_step (hreach _) (e.step_eq _) (hr _ (by omega)) (hcon _ (by omega) .r)).1
  -- the reader's measure decreases at every step: contradiction
  obtain ⟨N₂, -, hN₂⟩ := Nat.eventually_not_of_succ_le
    (f := fun m => rμ M ((e.cfg (max N N₁ + m)).loc .r)) (N := 0) (p := fun _ => True)
    (fun m _ => by
      have := (reader_step (hreach _) (e.step_eq _) (hr (max N N₁ + m) (by omega))
        (hcon _ (by omega) .r)).2
      rw [hmem m] at this; rw [← Nat.add_assoc]; exact this.le)
    (fun m _ _ => by
      have := (reader_step (hreach _) (e.step_eq _) (hr (max N N₁ + m) (by omega))
        (hcon _ (by omega) .r)).2
      rw [hmem m] at this; rw [← Nat.add_assoc]; exact this)
  exact hN₂ N₂ le_rfl trivial

/-! ## Theorem 9 -/

/-- **Theorem 9** of [Attiya, Bender, Farach-Colton, Oshman, Schiller, PODC 2024]:
Algorithm 2 (with Algorithm 3) is a linearizable, lock-free, state-quiescent history-independent
single-writer single-reader `K`-valued register (`alg2 v₀ : Impl (register (Fin K) v₀) …` with
`allowed = RWOp.SWSR Proc.w Proc.r`) implemented from binary registers. -/
theorem theorem9 (v₀ : Fin K) :
    (alg2 v₀).Linearizable ∧ (alg2 v₀).LockFree ∧ (alg2 v₀).StateQuiescentHI :=
  ⟨linearizable v₀, lockFree v₀, stateQuiescentHI v₀⟩

/-! ## Non-vacuity: a concrete execution -/

/-- With `K = 2`, `v₀ = 0`: `Write(1)` followed by a `Read()` that returns `1`. -/
def sampleExec : List (Lbl (0 : Fin 2)) :=
  [.inv .w (.write 1), .tau .w, .tau .w, .ret .w 1,
   .inv .r .read, .tau .r, .tau .r, .tau .r, .ret .r 1]

example : (alg2 (0 : Fin 2)).Valid sampleExec ∧ respOf sampleExec (.r, 0) = some 1 := by
  refine ⟨?_, rfl⟩
  simp [Impl.Valid, sampleExec, Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, alg2, act, start, fin,
    order, RWOp.SWSR, Function.update]

end Alg2

end Cslib.SharedMemory
