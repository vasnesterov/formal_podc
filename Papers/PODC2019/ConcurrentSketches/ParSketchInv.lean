import Papers.PODC2019.ConcurrentSketches.ParSketch

/-!
# `ParSketch`: ghost histories and the invariant

The proof of Lemma 1 (full version, Section 6.2) uses two maps from executions to sequential
histories:

* `l(σ)` (*linearization*): an update at its invocation, a query at its snapshot;
* `f(σ)` (*visibility*): a query at its snapshot, an update filtered out by `shouldAdd` at that
  moment, any other update at the merge of the local sketch it was ingested into.

We compute both, together with the per-thread lists of *unpropagated* updates (the paper's
`up_suff_i(σ)`), by a ghost run `ghost` along the execution (`Ghost.lin`, `Ghost.vis`,
`Ghost.buf`). The invariant `Inv` collects the paper's Invariants 1–3, Lemma 2 (the global
sketch summarises `f(σ)`), Lemma 5 (`|up_suff_i| ≤ b`) and the facts making `l(σ)` a
linearization.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable {S : Composable} {N : ℕ} {Q : Type} [NeZero N] [DecidableEq Q]

section Defs

variable (S N Q)

/-- Configurations of `ParSketch`. -/
abbrev PCfg := Config (seqObj S.toSketch) (pobjs S N) (Proc N Q) (PLoc S N)

/-- Labels of executions of the sketch object. -/
abbrev Lbl := Label (Proc N Q) (seqObj S.toSketch)

/-- The ghost state: the linearization `l`, the visibility order `f`, and for each update
thread its accepted updates not yet merged into the global sketch. -/
structure Ghost where
  /-- `l(σ)`. -/
  lin : List (Entry (Proc N Q) S.toSketch)
  /-- `f(σ)`. -/
  vis : List (Entry (Proc N Q) S.toSketch)
  /-- `up_suff_i(σ)`. -/
  buf : Fin N → List (Entry (Proc N Q) S.toSketch)

end Defs

/-- The ghost step for the label `ℓ` taken after `α` from configuration `C`. -/
noncomputable def gstep (α : List (Lbl S N Q)) (C : PCfg S N Q) (g : Ghost S N Q) :
    Lbl S N Q → Ghost S N Q
  | .inv (.upd j) (.update a) =>
    match C.loc (.upd j) with
    | .uIdle _ h =>
      if S.shouldAdd h a then
        { g with lin := g.lin ++ [(curOp α (.upd j), .update a, .ack)],
                 buf := Function.update g.buf j (g.buf j ++ [(curOp α (.upd j), .update a, .ack)]) }
      else
        { g with lin := g.lin ++ [(curOp α (.upd j), .update a, .ack)],
                 vis := g.vis ++ [(curOp α (.upd j), .update a, .ack)] }
    | _ => g
  | .tau (.qry q) =>
    match C.loc (.qry q) with
    | .qSnap a =>
      let e : Entry (Proc N Q) S.toSketch :=
        (curOp α (.qry q), .query a, .val (S.snapQuery (S.snapshot (C.mem .glob)) a))
      { g with lin := g.lin ++ [e], vis := g.vis ++ [e] }
    | _ => g
  | .tau .prop =>
    match C.loc .prop with
    | .pMerge j _ => { g with vis := g.vis ++ g.buf j, buf := Function.update g.buf j [] }
    | _ => g
  | _ => g

variable (S N Q) in
/-- The initial ghost state. -/
def Ghost.init : Ghost S N Q := ⟨[], [], fun _ => []⟩

/-- The ghost run on a reversed execution. -/
noncomputable def ghostRev (b : ℕ) (hint₀ : S.Hint) : List (Lbl S N Q) → Ghost S N Q
  | [] => Ghost.init S N Q
  | ℓ :: β =>
    match (parSketch S N Q b hint₀).run β.reverse with
    | some C => gstep β.reverse C (ghostRev b hint₀ β) ℓ
    | none => ghostRev b hint₀ β

/-- The ghost state after the execution `α`. -/
noncomputable def ghost (b : ℕ) (hint₀ : S.Hint) (α : List (Lbl S N Q)) : Ghost S N Q :=
  ghostRev b hint₀ α.reverse

@[simp] lemma ghost_nil (b : ℕ) (hint₀ : S.Hint) :
    ghost (Q := Q) (N := N) b hint₀ [] = Ghost.init S N Q := rfl

lemma ghost_concat (b : ℕ) (hint₀ : S.Hint) (α : List (Lbl S N Q)) (ℓ : Lbl S N Q)
    {C : PCfg S N Q} (hC : (parSketch S N Q b hint₀).run α = some C) :
    ghost b hint₀ (α ++ [ℓ]) = gstep α C (ghost b hint₀ α) ℓ := by
  simp [ghost, ghostRev, hC]

/-! ## The phase of the propagator with respect to a thread -/

/-- What the propagator is doing with thread `j`'s local sketch. -/
inductive Phase (S : Composable) where
  | free
  | read
  | merge (s : S.State)
  | reset
  | hint
  | signal (h : S.Hint)

/-- The phase of the propagator (in local state `l`) with respect to thread `j`. -/
def phaseOf (j : Fin N) : PLoc S N → Phase S
  | .pRead j' => if j' = j then .read else .free
  | .pMerge j' s => if j' = j then .merge s else .free
  | .pReset j' => if j' = j then .reset else .free
  | .pHint j' => if j' = j then .hint else .free
  | .pSignal j' h => if j' = j then .signal h else .free
  | _ => .free

/-! ## The per-thread invariant -/

/-- The invariant of update thread `j` (paper: Invariants 1–2, Lemma 5), in terms of its local
state `l`, pending operation `pd`, local sketch `ls`, register `prop_j` (`pr`), the
propagator's phase `ph` w.r.t. `j`, its unpropagated updates `B`, the stream `F` of `f(σ)`, its
current operation instance `x`, and the linearization `lin`. -/
def TI (b : ℕ) (l : PLoc S N) (pd : Option (SkOp S.toSketch)) (ls : S.State)
    (pr : Option S.Hint) (ph : Phase S) (B : List (Entry (Proc N Q) S.toSketch))
    (F : List S.Elem) (x : OpId (Proc N Q)) (lin : List (Entry (Proc N Q) S.toSketch)) : Prop :=
  match l with
  | .uIdle c h => pd = none ∧ c < b ∧ B.length = c ∧ ls = S.run (upds B) ∧ pr ≠ none ∧
      S.Safe h F ∧ ph = .free
  | .uApply a c h => pd = some (.update a) ∧ c < b ∧
      (∃ B', B = B' ++ [(x, .update a, .ack)] ∧ B'.length = c ∧ ls = S.run (upds B')) ∧
      pr ≠ none ∧ S.Safe h F ∧ ph = .free
  | .uRet c h => (∃ a, pd = some (.update a)) ∧ c < b ∧ B.length = c ∧ ls = S.run (upds B) ∧
      pr ≠ none ∧ S.Safe h F ∧ ph = .free ∧ x ∈ lin.map Prod.fst
  | .uSignal h => (∃ a, pd = some (.update a)) ∧ B.length = b ∧ ls = S.run (upds B) ∧
      pr ≠ none ∧ S.Safe h F ∧ ph = .free ∧ x ∈ lin.map Prod.fst
  | .uWait h => (∃ a, pd = some (.update a)) ∧ S.Safe h F ∧ x ∈ lin.map Prod.fst ∧
      match pr with
      | some h' => S.Safe h' F ∧ B = [] ∧ ls = S.init ∧ ph = .free
      | none =>
        match ph with
        | .free => B.length = b ∧ ls = S.run (upds B)
        | .read => B.length = b ∧ ls = S.run (upds B)
        | .merge s => B.length = b ∧ s = S.run (upds B)
        | .reset => B = []
        | .hint => B = [] ∧ ls = S.init
        | .signal h' => B = [] ∧ ls = S.init ∧ S.Safe h' F
  | _ => False

/-- The invariant of query thread `q`. -/
def QI (l : PLoc S N) (pd : Option (SkOp S.toSketch)) (x : OpId (Proc N Q))
    (lin : List (Entry (Proc N Q) S.toSketch)) : Prop :=
  match l with
  | .qIdle => pd = none
  | .qSnap a => pd = some (.query a) ∧ x ∉ lin.map Prod.fst
  | .qRet v => ∃ a, pd = some (.query a) ∧ (x, .query a, .val v) ∈ lin
  | _ => False

/-- Local states of the propagator. -/
def IsPLoc : PLoc S N → Prop
  | .pIdle | .pCheck _ | .pRead _ | .pMerge _ _ | .pReset _ | .pHint _ | .pSignal _ _ => True
  | _ => False

/-- The invariant of `ParSketch` after the execution `α` with final configuration `C` and ghost
state `g`. -/
structure Inv (b : ℕ) (α : List (Lbl S N Q)) (C : PCfg S N Q) (g : Ghost S N Q) : Prop where
  /-- Invariant 3 / Lemma 2: the global sketch summarises the stream of `f(σ)`. -/
  glob : C.mem .glob = S.run (upds g.vis)
  /-- Lemma 3: `f(σ) ∈ SeqSketch`. -/
  vis_legal : SeqSketch S.toSketch g.vis
  lin_nodup : (g.lin.map Prod.fst).Nodup
  vis_nodup : g.vis.Nodup
  lin_op : ∀ y ∈ g.lin, opOf α y.1 = some y.2.1
  lin_resp : ∀ y ∈ g.lin, ∀ r, respOf α y.1 = some r → y.2.2 = r
  lin_comp : ∀ x, Completed α x → x ∈ g.lin.map Prod.fst
  vis_lin : ∀ y ∈ g.vis, y ∈ g.lin
  lin_cover : ∀ y ∈ g.lin, y ∈ g.vis ∨ ∃ j, y ∈ g.buf j
  buf_lin : ∀ j, ∀ y ∈ g.buf j, y ∈ g.lin
  buf_vis : ∀ j, ∀ y ∈ g.buf j, y ∉ g.vis
  buf_shape : ∀ j, ∀ y ∈ g.buf j, y.1.1 = .upd j ∧ ∃ a, y.2 = (.update a, .ack)
  buf_nodup : ∀ j, (g.buf j).Nodup
  /-- Invariants 1–2 and Lemma 5 for every update thread. -/
  thr : ∀ j, TI b (C.loc (.upd j)) (C.pend (.upd j)) (C.mem (.loc j)) (C.mem (.prop j))
    (phaseOf j (C.loc .prop)) (g.buf j) (upds g.vis) (curOp α (.upd j)) g.lin
  qry : ∀ q, QI (C.loc (.qry q)) (C.pend (.qry q)) (curOp α (.qry q)) g.lin
  /-- Shape of the linearization: updates of update threads and queries of query threads. -/
  lin_shape : ∀ y ∈ g.lin, (∃ j, y.1.1 = .upd j ∧ ∃ a, y.2 = (.update a, .ack)) ∨
    (∃ q, y.1.1 = .qry q ∧ ∃ a v, y.2 = (.query a, .val v))
  /-- Once started, the propagator never returns to its initial state. -/
  prop_live : C.pend .prop ≠ none → C.loc .prop ≠ .pIdle
  /-- The propagator is in one of its own local states. -/
  prop_kind : IsPLoc (C.loc .prop)

/-! ## Basic facts -/

lemma mem_map_fst_mono {lin lin' : List (Entry (Proc N Q) S.toSketch)}
    (hlin : ∀ y ∈ lin, y ∈ lin') {x : OpId (Proc N Q)} (hx : x ∈ lin.map Prod.fst) :
    x ∈ lin'.map Prod.fst := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact List.mem_map_of_mem (hlin y hy)

lemma TI.congr {b : ℕ} {l l' : PLoc S N} {pd pd' : Option (SkOp S.toSketch)} {ls ls' : S.State}
    {pr pr' : Option S.Hint} {ph ph' : Phase S} {B B' : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x x' : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : TI b l pd ls pr ph B F x lin) (e1 : l' = l) (e2 : pd' = pd) (e3 : ls' = ls)
    (e4 : pr' = pr) (e5 : ph' = ph) (e6 : B' = B) (e7 : x' = x) :
    TI b l' pd' ls' pr' ph' B' F x' lin := by
  subst_vars; exact h

/-- The thread invariant only depends monotonically on `f(σ)` and `l(σ)`. -/
lemma TI.mono {b : ℕ} {l : PLoc S N} {pd : Option (SkOp S.toSketch)} {ls : S.State}
    {pr : Option S.Hint} {ph : Phase S} {B : List (Entry (Proc N Q) S.toSketch)}
    {F F' : List S.Elem} {x : OpId (Proc N Q)} {lin lin' : List (Entry (Proc N Q) S.toSketch)}
    (h : TI b l pd ls pr ph B F x lin) (hF : F <+: F') (hlin : ∀ y ∈ lin, y ∈ lin') :
    TI b l pd ls pr ph B F' x lin' := by
  have hm := fun hx => mem_map_fst_mono (x := x) hlin hx
  cases l with
  | uIdle c h' =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h; exact ⟨h1, h2, h3, h4, h5, h6.mono hF, h7⟩
  | uApply a c h' =>
    obtain ⟨h1, h2, h3, h5, h6, h7⟩ := h; exact ⟨h1, h2, h3, h5, h6.mono hF, h7⟩
  | uRet c h' =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6.mono hF, h7, hm h8⟩
  | uSignal h' =>
    obtain ⟨h1, h2, h3, h5, h6, h7, h8⟩ := h
    exact ⟨h1, h2, h3, h5, h6.mono hF, h7, hm h8⟩
  | uWait h' =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2.mono hF, hm h3, ?_⟩
    cases pr with
    | some h'' => obtain ⟨k1, k2⟩ := h4; exact ⟨k1.mono hF, k2⟩
    | none =>
      cases ph with
      | signal h'' => obtain ⟨k1, k2, k3⟩ := h4; exact ⟨k1, k2, k3.mono hF⟩
      | _ => exact h4
  | _ => exact h

lemma QI.mono {l : PLoc S N} {pd : Option (SkOp S.toSketch)} {x : OpId (Proc N Q)}
    {lin lin' : List (Entry (Proc N Q) S.toSketch)} (h : QI l pd x lin)
    (hlin : ∀ y ∈ lin, y ∈ lin') (hnew : ∀ y ∈ lin', y ∈ lin ∨ y.1 ≠ x) :
    QI l pd x lin' := by
  cases l with
  | qSnap a =>
    refine ⟨h.1, fun hm => h.2 ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    rcases hnew y hy with h' | h'
    · exact List.mem_map_of_mem h'
    · exact absurd rfl h'
  | qRet v => obtain ⟨a, h1, h2⟩ := h; exact ⟨a, h1, hlin _ h2⟩
  | _ => exact h

/-- If the propagator is busy with thread `j`, the thread waits and `prop_j = 0`. -/
lemma TI.wait_of_busy {b : ℕ} {l : PLoc S N} {pd : Option (SkOp S.toSketch)} {ls : S.State}
    {pr : Option S.Hint} {ph : Phase S} {B : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : TI b l pd ls pr ph B F x lin) (hph : ph ≠ .free) :
    ∃ hh, l = .uWait hh ∧ pr = none := by
  cases l with
  | uIdle c h' => exact absurd h.2.2.2.2.2.2 hph
  | uApply a c h' => exact absurd h.2.2.2.2.2 hph
  | uRet c h' => exact absurd h.2.2.2.2.2.2.1 hph
  | uSignal h' => exact absurd h.2.2.2.2.2.1 hph
  | uWait h' =>
    refine ⟨h', rfl, ?_⟩
    obtain ⟨-, -, -, h4⟩ := h
    cases pr with
    | none => rfl
    | some _ => exact absurd h4.2.2.2 hph
  | _ => exact h.elim

/-- If `prop_j = 0`, thread `j` waits. -/
lemma TI.wait_of_none {b : ℕ} {l : PLoc S N} {pd : Option (SkOp S.toSketch)} {ls : S.State}
    {ph : Phase S} {B : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : TI b l pd ls none ph B F x lin) : ∃ hh, l = .uWait hh := by
  cases l with
  | uIdle c h' => exact absurd rfl h.2.2.2.2.1
  | uApply a c h' => exact absurd rfl h.2.2.2.1
  | uRet c h' => exact absurd rfl h.2.2.2.2.1
  | uSignal h' => exact absurd rfl h.2.2.2.1
  | uWait h' => exact ⟨h', rfl⟩
  | _ => exact h.elim

lemma phaseOf_ne {j j' : Fin N} (h : j' ≠ j) :
    phaseOf (S := S) j (.pRead j') = .free ∧ (∀ s, phaseOf (S := S) j (.pMerge j' s) = .free) ∧
    phaseOf (S := S) j (.pReset j') = .free ∧ phaseOf (S := S) j (.pHint j') = .free ∧
    (∀ hh, phaseOf (S := S) j (.pSignal j' hh) = .free) := by
  simp [phaseOf, h]

section Transitions

variable {b : ℕ} {l : PLoc S N} {pd : Option (SkOp S.toSketch)} {ls : S.State}
  {B : List (Entry (Proc N Q) S.toSketch)} {F : List S.Elem} {x : OpId (Proc N Q)}
  {lin : List (Entry (Proc N Q) S.toSketch)}

/-! Phase transitions of the propagator for a waiting thread. -/

lemma TI.toRead (h : TI b l pd ls none .free B F x lin) : TI b l pd ls none .read B F x lin := by
  obtain ⟨hh, rfl⟩ := h.wait_of_none; exact h

lemma TI.toMerge (h : TI b l pd ls none .read B F x lin) :
    TI b l pd ls none (.merge ls) B F x lin := by
  obtain ⟨hh, rfl⟩ := h.wait_of_none
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; exact ⟨h1, h2, h3, h4, h5⟩

lemma TI.toReset {s : S.State} (h : TI b l pd ls none (.merge s) B F x lin) {F' : List S.Elem}
    (hF : F <+: F') : TI b l pd ls none .reset [] F' x lin := by
  obtain ⟨hh, rfl⟩ := h.wait_of_none
  obtain ⟨h1, h2, h3, -⟩ := h; exact ⟨h1, h2.mono hF, h3, rfl⟩

lemma TI.toHint (h : TI b l pd ls none .reset B F x lin) :
    TI b l pd S.init none .hint B F x lin := by
  obtain ⟨hh, rfl⟩ := h.wait_of_none
  obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, h4, rfl⟩

lemma TI.toSignal {hh : S.Hint} (h : TI b l pd ls none .hint B F x lin) (hs : S.Safe hh F) :
    TI b l pd ls none (.signal hh) B F x lin := by
  obtain ⟨hh', rfl⟩ := h.wait_of_none
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; exact ⟨h1, h2, h3, h4, h5, hs⟩

lemma TI.toSome {hh : S.Hint} (h : TI b l pd ls none (.signal hh) B F x lin) :
    TI b l pd ls (some hh) .free B F x lin := by
  obtain ⟨hh', rfl⟩ := h.wait_of_none
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1, h2, h3, h6, h4, h5, rfl⟩

end Transitions

/-- Lemma 5 of the full paper: at most `b` unpropagated updates per thread. -/
lemma TI.length_le {b : ℕ} {l : PLoc S N} {pd : Option (SkOp S.toSketch)} {ls : S.State}
    {pr : Option S.Hint} {ph : Phase S} {B : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : TI b l pd ls pr ph B F x lin) : B.length ≤ b := by
  cases l with
  | uIdle c h' => obtain ⟨-, h2, h3, -⟩ := h; omega
  | uApply a c h' =>
    obtain ⟨-, h2, ⟨B', rfl, h3, -⟩, -⟩ := h; simp; omega
  | uRet c h' => obtain ⟨-, h2, h3, -⟩ := h; omega
  | uSignal h' => obtain ⟨-, h2, -⟩ := h; omega
  | uWait h' =>
    obtain ⟨-, -, -, h4⟩ := h
    cases pr with
    | some h'' => obtain ⟨-, rfl, -⟩ := h4; simp
    | none =>
      cases ph with
      | free => omega
      | read => omega
      | merge s => omega
      | reset => simp [h4]
      | hint => simp [h4.1]
      | signal h'' => simp [h4.1]
  | _ => exact h.elim

end Podc.ConcurrentSketches
