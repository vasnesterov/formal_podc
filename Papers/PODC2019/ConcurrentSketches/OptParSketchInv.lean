import Papers.PODC2019.ConcurrentSketches.OptParSketch
import Papers.PODC2019.ConcurrentSketches.ParSketchMain

/-!
# `OptParSketch`: ghost histories and the invariant

We prove Theorem 1 directly, by the ghost/invariant method used for `ParSketch` (Lemma 1),
instead of the paper's simulation of `OptParSketch` by `ParSketch` with `2N` threads.

The ghost state consists of the linearization `l(σ)` (updates at their invocation, queries at
their snapshot), the visibility order `f(σ)` (queries at their snapshot, filtered updates at
their invocation, accepted updates at the merge of the local sketch they were ingested into),
and for each update thread `t_j`
* `bAct j`: the accepted updates ingested (or being ingested) into the *active* local sketch
  `localS_j[cur_j]`;
* `bIn j`: the full batch of the *inactive* local sketch `localS_j[1 - cur_j]` handed over to the
  propagator and not yet merged into the global sketch.

Ghost steps: an accepted invocation appends to `lin` and `bAct j`; a filtered one to `lin` and
`vis`; a snapshot to `lin` and `vis`; the flip of `cur_j` moves `bAct j` to `bIn j`; the
propagator's merge of `localS_j[k]` moves `bIn j` to `vis`. Per thread
`|bIn j| + |bAct j| ≤ 2b`, which gives the relaxation bound `2Nb`.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable {S : Composable} {N : ℕ} {Q : Type} [NeZero N] [DecidableEq Q]

section Defs

variable (S N Q)

/-- Configurations of `OptParSketch`. -/
abbrev OCfg := Config (seqObj S.toSketch) (oobjs S N) (Proc N Q) (OLoc S N)

/-- The ghost state of `OptParSketch`. -/
structure OGhost where
  /-- `l(σ)`. -/
  lin : List (Entry (Proc N Q) S.toSketch)
  /-- `f(σ)`. -/
  vis : List (Entry (Proc N Q) S.toSketch)
  /-- The batch in the inactive local sketch of thread `j`, not yet merged. -/
  bIn : Fin N → List (Entry (Proc N Q) S.toSketch)
  /-- The accepted updates in the active local sketch of thread `j`. -/
  bAct : Fin N → List (Entry (Proc N Q) S.toSketch)

end Defs

/-- All unpropagated accepted updates of thread `j`. -/
def OGhost.buf (g : OGhost S N Q) (j : Fin N) : List (Entry (Proc N Q) S.toSketch) :=
  g.bIn j ++ g.bAct j

/-- The ghost step for the label `ℓ` taken after `α` from configuration `C`. -/
noncomputable def ogstep (α : List (Lbl S N Q)) (C : OCfg S N Q) (g : OGhost S N Q) :
    Lbl S N Q → OGhost S N Q
  | .inv (.upd j) (.update a) =>
    match C.loc (.upd j) with
    | .oIdle _ _ h =>
      if S.shouldAdd h a then
        { g with lin := g.lin ++ [(curOp α (.upd j), .update a, .ack)],
                 bAct := Function.update g.bAct j
                   (g.bAct j ++ [(curOp α (.upd j), .update a, .ack)]) }
      else
        { g with lin := g.lin ++ [(curOp α (.upd j), .update a, .ack)],
                 vis := g.vis ++ [(curOp α (.upd j), .update a, .ack)] }
    | _ => g
  | .tau (.upd j) =>
    match C.loc (.upd j) with
    | .oFlip _ _ => { g with bIn := Function.update g.bIn j (g.bAct j),
                             bAct := Function.update g.bAct j [] }
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
    | .pMerge j _ _ => { g with vis := g.vis ++ g.bIn j, bIn := Function.update g.bIn j [] }
    | _ => g
  | _ => g

variable (S N Q) in
/-- The initial ghost state. -/
def OGhost.init : OGhost S N Q := ⟨[], [], fun _ => [], fun _ => []⟩

/-- The ghost run on a reversed execution. -/
noncomputable def oghostRev (b : ℕ) (hint₀ : S.Hint) : List (Lbl S N Q) → OGhost S N Q
  | [] => OGhost.init S N Q
  | ℓ :: β =>
    match (optParSketch S N Q b hint₀).run β.reverse with
    | some C => ogstep β.reverse C (oghostRev b hint₀ β) ℓ
    | none => oghostRev b hint₀ β

/-- The ghost state after the execution `α`. -/
noncomputable def oghost (b : ℕ) (hint₀ : S.Hint) (α : List (Lbl S N Q)) : OGhost S N Q :=
  oghostRev b hint₀ α.reverse

@[simp] lemma oghost_nil (b : ℕ) (hint₀ : S.Hint) :
    oghost (Q := Q) (N := N) b hint₀ [] = OGhost.init S N Q := rfl

lemma oghost_concat (b : ℕ) (hint₀ : S.Hint) (α : List (Lbl S N Q)) (ℓ : Lbl S N Q)
    {C : OCfg S N Q} (hC : (optParSketch S N Q b hint₀).run α = some C) :
    oghost b hint₀ (α ++ [ℓ]) = ogstep α C (oghost b hint₀ α) ℓ := by
  simp [oghost, oghostRev, hC]

/-! ## The phase of the propagator with respect to a thread -/

/-- What the propagator is doing with thread `j`. -/
inductive OPhase (S : Composable) where
  | free
  | cur
  | read (k : Bool)
  | merge (k : Bool) (s : S.State)
  | reset (k : Bool)
  | hint
  | signal (h : S.Hint)

/-- The phase of the propagator (in local state `l`) with respect to thread `j`. -/
def ophaseOf (j : Fin N) : OLoc S N → OPhase S
  | .pCur j' => if j' = j then .cur else .free
  | .pRead j' k => if j' = j then .read k else .free
  | .pMerge j' k s => if j' = j then .merge k s else .free
  | .pReset j' k => if j' = j then .reset k else .free
  | .pHint j' => if j' = j then .hint else .free
  | .pSignal j' h => if j' = j then .signal h else .free
  | _ => .free

/-! ## The per-thread invariant -/

/-- The invariant of the *inactive* half of thread `j` (current index `cur`): `pr` is `prop_j`,
`ph` the propagator's phase w.r.t. `j`, `li` the inactive local sketch `localS_j[!cur]`, `bIn`
its unmerged batch, `F` the stream of `f(σ)`. -/
def OInact (b : ℕ) (cur : Bool) (pr : Option S.Hint) (ph : OPhase S) (li : S.State)
    (bIn : List (Entry (Proc N Q) S.toSketch)) (F : List S.Elem) : Prop :=
  match pr with
  | some h' => S.Safe h' F ∧ bIn = [] ∧ li = S.init ∧ ph = .free
  | none =>
    match ph with
    | .free => bIn.length = b ∧ li = S.run (upds bIn)
    | .cur => bIn.length = b ∧ li = S.run (upds bIn)
    | .read k => k = !cur ∧ bIn.length = b ∧ li = S.run (upds bIn)
    | .merge k s => k = !cur ∧ bIn.length = b ∧ s = S.run (upds bIn)
    | .reset k => k = !cur ∧ bIn = []
    | .hint => bIn = [] ∧ li = S.init
    | .signal h' => bIn = [] ∧ li = S.init ∧ S.Safe h' F

/-- The invariant of update thread `j`, in terms of its local state `l`, pending operation `pd`,
local sketches `ls`, register `cur_j` (`cr`), register `prop_j` (`pr`), the propagator's phase
`ph` w.r.t. `j`, the ghost batches `bIn`, `bAct`, the stream `F` of `f(σ)`, its current
operation instance `x`, and the linearization `lin`. -/
def OTI (b : ℕ) (l : OLoc S N) (pd : Option (SkOp S.toSketch)) (ls : Bool → S.State) (cr : Bool)
    (pr : Option S.Hint) (ph : OPhase S) (bIn bAct : List (Entry (Proc N Q) S.toSketch))
    (F : List S.Elem) (x : OpId (Proc N Q)) (lin : List (Entry (Proc N Q) S.toSketch)) : Prop :=
  match l with
  | .oIdle cur c h => (pd = none ∧ c < b ∧ bAct.length = c ∧ ls cur = S.run (upds bAct) ∧
      cr = cur ∧ S.Safe h F) ∧ OInact b cur pr ph (ls (!cur)) bIn F
  | .oApply a cur c h => (pd = some (.update a) ∧ c < b ∧
      (∃ B', bAct = B' ++ [(x, .update a, .ack)] ∧ B'.length = c ∧ ls cur = S.run (upds B')) ∧
      cr = cur ∧ S.Safe h F) ∧ OInact b cur pr ph (ls (!cur)) bIn F
  | .oRet cur c h => ((∃ a, pd = some (.update a)) ∧ c < b ∧ bAct.length = c ∧
      ls cur = S.run (upds bAct) ∧ cr = cur ∧ S.Safe h F ∧ x ∈ lin.map Prod.fst) ∧
      OInact b cur pr ph (ls (!cur)) bIn F
  | .oWait cur h => ((∃ a, pd = some (.update a)) ∧ bAct.length = b ∧
      ls cur = S.run (upds bAct) ∧ cr = cur ∧ S.Safe h F ∧ x ∈ lin.map Prod.fst) ∧
      OInact b cur pr ph (ls (!cur)) bIn F
  | .oFlip cur h => (∃ a, pd = some (.update a)) ∧ bAct.length = b ∧
      ls cur = S.run (upds bAct) ∧ cr = cur ∧ pr = some h ∧ S.Safe h F ∧ bIn = [] ∧
      ls (!cur) = S.init ∧ ph = .free ∧ x ∈ lin.map Prod.fst
  | .oSignal cur h => (∃ a, pd = some (.update a)) ∧ bAct = [] ∧ ls cur = S.init ∧
      bIn.length = b ∧ ls (!cur) = S.run (upds bIn) ∧ cr = cur ∧ pr ≠ none ∧ ph = .free ∧
      S.Safe h F ∧ x ∈ lin.map Prod.fst
  | _ => False

/-- The invariant of query thread `q`. -/
def OQI (l : OLoc S N) (pd : Option (SkOp S.toSketch)) (x : OpId (Proc N Q))
    (lin : List (Entry (Proc N Q) S.toSketch)) : Prop :=
  match l with
  | .qIdle => pd = none
  | .qSnap a => pd = some (.query a) ∧ x ∉ lin.map Prod.fst
  | .qRet v => ∃ a, pd = some (.query a) ∧ (x, .query a, .val v) ∈ lin
  | _ => False

/-- Local states of the propagator. -/
def IsOPLoc : OLoc S N → Prop
  | .pIdle | .pCheck _ | .pCur _ | .pRead _ _ | .pMerge _ _ _ | .pReset _ _ | .pHint _
  | .pSignal _ _ => True
  | _ => False

/-- The invariant of `OptParSketch` after the execution `α` with final configuration `C` and
ghost state `g`. -/
structure OInv (b : ℕ) (α : List (Lbl S N Q)) (C : OCfg S N Q) (g : OGhost S N Q) : Prop where
  /-- The global sketch summarises the stream of `f(σ)`. -/
  glob : C.mem .glob = S.run (upds g.vis)
  /-- `f(σ) ∈ SeqSketch`. -/
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
  /-- The invariant of every update thread. -/
  thr : ∀ j, OTI b (C.loc (.upd j)) (C.pend (.upd j)) (fun k => C.mem (.loc j k))
    (C.mem (.cur j)) (C.mem (.prop j)) (ophaseOf j (C.loc .prop)) (g.bIn j) (g.bAct j)
    (upds g.vis) (curOp α (.upd j)) g.lin
  qry : ∀ q, OQI (C.loc (.qry q)) (C.pend (.qry q)) (curOp α (.qry q)) g.lin
  /-- Shape of the linearization: updates of update threads and queries of query threads. -/
  lin_shape : ∀ y ∈ g.lin, (∃ j, y.1.1 = .upd j ∧ ∃ a, y.2 = (.update a, .ack)) ∨
    (∃ q, y.1.1 = .qry q ∧ ∃ a v, y.2 = (.query a, .val v))
  /-- Once started, the propagator never returns to its initial state. -/
  prop_live : C.pend .prop ≠ none → C.loc .prop ≠ .pIdle
  /-- The propagator is in one of its own local states. -/
  prop_kind : IsOPLoc (C.loc .prop)

/-! ## Basic facts -/

lemma OTI.congr {b : ℕ} {l l' : OLoc S N} {pd pd' : Option (SkOp S.toSketch)}
    {ls ls' : Bool → S.State} {cr cr' : Bool} {pr pr' : Option S.Hint} {ph ph' : OPhase S}
    {bIn bIn' bAct bAct' : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x x' : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : OTI b l pd ls cr pr ph bIn bAct F x lin) (e1 : l' = l) (e2 : pd' = pd) (e3 : ls' = ls)
    (e4 : cr' = cr) (e5 : pr' = pr) (e6 : ph' = ph) (e7 : bIn' = bIn) (e8 : bAct' = bAct)
    (e9 : x' = x) :
    OTI b l' pd' ls' cr' pr' ph' bIn' bAct' F x' lin := by
  subst_vars; exact h

lemma OInact.mono {b : ℕ} {cur : Bool} {pr : Option S.Hint} {ph : OPhase S} {li : S.State}
    {bIn : List (Entry (Proc N Q) S.toSketch)} {F F' : List S.Elem}
    (h : OInact b cur pr ph li bIn F) (hF : F <+: F') : OInact b cur pr ph li bIn F' := by
  cases pr with
  | some h' => obtain ⟨k1, k2⟩ := h; exact ⟨k1.mono hF, k2⟩
  | none =>
    cases ph with
    | signal h'' => obtain ⟨k1, k2, k3⟩ := h; exact ⟨k1, k2, k3.mono hF⟩
    | _ => exact h

/-- The thread invariant only depends monotonically on `f(σ)` and `l(σ)`. -/
lemma OTI.mono {b : ℕ} {l : OLoc S N} {pd : Option (SkOp S.toSketch)} {ls : Bool → S.State}
    {cr : Bool} {pr : Option S.Hint} {ph : OPhase S}
    {bIn bAct : List (Entry (Proc N Q) S.toSketch)}
    {F F' : List S.Elem} {x : OpId (Proc N Q)} {lin lin' : List (Entry (Proc N Q) S.toSketch)}
    (h : OTI b l pd ls cr pr ph bIn bAct F x lin) (hF : F <+: F') (hlin : ∀ y ∈ lin, y ∈ lin') :
    OTI b l pd ls cr pr ph bIn bAct F' x lin' := by
  have hm := fun hx => mem_map_fst_mono (x := x) hlin hx
  cases l with
  | oIdle cur c h' =>
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h
    exact ⟨⟨h1, h2, h3, h4, h5, h6.mono hF⟩, h7.mono hF⟩
  | oApply a cur c h' =>
    obtain ⟨⟨h1, h2, h3, h5, h6⟩, h7⟩ := h
    exact ⟨⟨h1, h2, h3, h5, h6.mono hF⟩, h7.mono hF⟩
  | oRet cur c h' =>
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h8⟩, h7⟩ := h
    exact ⟨⟨h1, h2, h3, h4, h5, h6.mono hF, hm h8⟩, h7.mono hF⟩
  | oWait cur h' =>
    obtain ⟨⟨h1, h2, h3, h4, h6, h8⟩, h7⟩ := h
    exact ⟨⟨h1, h2, h3, h4, h6.mono hF, hm h8⟩, h7.mono hF⟩
  | oFlip cur h' =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6.mono hF, h7, h8, h9, hm h10⟩
  | oSignal cur h' =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9.mono hF, hm h10⟩
  | _ => exact h.elim

lemma OQI.mono {l : OLoc S N} {pd : Option (SkOp S.toSketch)} {x : OpId (Proc N Q)}
    {lin lin' : List (Entry (Proc N Q) S.toSketch)} (h : OQI l pd x lin)
    (hlin : ∀ y ∈ lin, y ∈ lin') (hnew : ∀ y ∈ lin', y ∈ lin ∨ y.1 ≠ x) :
    OQI l pd x lin' := by
  cases l with
  | qSnap a =>
    refine ⟨h.1, fun hm => h.2 ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    rcases hnew y hy with h' | h'
    · exact List.mem_map_of_mem h'
    · exact absurd rfl h'
  | qRet v => obtain ⟨a, h1, h2⟩ := h; exact ⟨a, h1, hlin _ h2⟩
  | _ => exact h

lemma OInact.free_of_some {b : ℕ} {cur : Bool} {h' : S.Hint} {ph : OPhase S} {li : S.State}
    {bIn : List (Entry (Proc N Q) S.toSketch)} {F : List S.Elem}
    (h : OInact b cur (some h') ph li bIn F) : ph = .free := h.2.2.2

/-- If the propagator is busy with thread `j`, then `prop_j = 0`. -/
lemma OTI.none_of_busy {b : ℕ} {l : OLoc S N} {pd : Option (SkOp S.toSketch)}
    {ls : Bool → S.State} {cr : Bool} {pr : Option S.Hint} {ph : OPhase S}
    {bIn bAct : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : OTI b l pd ls cr pr ph bIn bAct F x lin) (hph : ph ≠ .free) : pr = none := by
  cases pr with
  | none => rfl
  | some h' =>
    exfalso; apply hph
    cases l with
    | oIdle cur c hh => exact h.2.free_of_some
    | oApply a cur c hh => exact h.2.free_of_some
    | oRet cur c hh => exact h.2.free_of_some
    | oWait cur hh => exact h.2.free_of_some
    | oFlip cur hh => exact h.2.2.2.2.2.2.2.2.1
    | oSignal cur hh => exact h.2.2.2.2.2.2.2.1
    | _ => exact h.elim

/-- **Transport of the thread invariant along propagator steps.** If `prop_j = 0`, thread `j`
fills its active buffer `cur = cr`, and the invariant is preserved by any change of the inactive
half (`prop_j`, inactive local sketch, phase, batch) that preserves `OInact`. -/
lemma OTI.transport {b : ℕ} {l : OLoc S N} {pd : Option (SkOp S.toSketch)}
    {ls : Bool → S.State} {cr : Bool} {ph : OPhase S}
    {bIn bAct : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : OTI b l pd ls cr none ph bIn bAct F x lin) :
    OInact b cr none ph (ls (!cr)) bIn F ∧
      ∀ (ls' : Bool → S.State) (pr' : Option S.Hint) (ph' : OPhase S)
        (bIn' : List (Entry (Proc N Q) S.toSketch))
        (F' : List S.Elem) (lin' : List (Entry (Proc N Q) S.toSketch)),
        ls' cr = ls cr → F <+: F' → (∀ y ∈ lin, y ∈ lin') →
        OInact b cr pr' ph' (ls' (!cr)) bIn' F' → OTI b l pd ls' cr pr' ph' bIn' bAct F' x lin' := by
  cases l with
  | oIdle cur c hh =>
    obtain ⟨⟨h1, h2, h3, h4, rfl, h6⟩, h7⟩ := h
    exact ⟨h7, fun ls' pr' ph' bIn' F' lin' e hF hlin hI =>
      ⟨⟨h1, h2, h3, e ▸ h4, rfl, h6.mono hF⟩, hI⟩⟩
  | oApply a cur c hh =>
    obtain ⟨⟨h1, h2, ⟨B', hB, hB', h4⟩, rfl, h6⟩, h7⟩ := h
    exact ⟨h7, fun ls' pr' ph' bIn' F' lin' e hF hlin hI =>
      ⟨⟨h1, h2, ⟨B', hB, hB', e ▸ h4⟩, rfl, h6.mono hF⟩, hI⟩⟩
  | oRet cur c hh =>
    obtain ⟨⟨h1, h2, h3, h4, rfl, h6, h8⟩, h7⟩ := h
    exact ⟨h7, fun ls' pr' ph' bIn' F' lin' e hF hlin hI =>
      ⟨⟨h1, h2, h3, e ▸ h4, rfl, h6.mono hF, mem_map_fst_mono hlin h8⟩, hI⟩⟩
  | oWait cur hh =>
    obtain ⟨⟨h1, h2, h4, rfl, h6, h8⟩, h7⟩ := h
    exact ⟨h7, fun ls' pr' ph' bIn' F' lin' e hF hlin hI =>
      ⟨⟨h1, h2, e ▸ h4, rfl, h6.mono hF, mem_map_fst_mono hlin h8⟩, hI⟩⟩
  | oFlip cur hh => cases h.2.2.2.2.1
  | oSignal cur hh => exact absurd rfl h.2.2.2.2.2.2.1
  | _ => exact h.elim

/-- Bounds on the unpropagated batches. -/
lemma OInact.length_le {b : ℕ} {cur : Bool} {pr : Option S.Hint} {ph : OPhase S} {li : S.State}
    {bIn : List (Entry (Proc N Q) S.toSketch)} {F : List S.Elem}
    (h : OInact b cur pr ph li bIn F) : bIn.length ≤ b := by
  cases pr with
  | some h' => simp [h.2.1]
  | none =>
    cases ph with
    | free => exact h.1.le
    | cur => exact h.1.le
    | read k => exact h.2.1.le
    | merge k s => exact h.2.1.le
    | reset k => simp [h.2]
    | hint => simp [h.1]
    | signal h'' => simp [h.1]

/-- Lemma 5 for `OptParSketch`: at most `2b` unpropagated updates per thread. -/
lemma OTI.length_le {b : ℕ} {l : OLoc S N} {pd : Option (SkOp S.toSketch)}
    {ls : Bool → S.State} {cr : Bool} {pr : Option S.Hint} {ph : OPhase S}
    {bIn bAct : List (Entry (Proc N Q) S.toSketch)}
    {F : List S.Elem} {x : OpId (Proc N Q)} {lin : List (Entry (Proc N Q) S.toSketch)}
    (h : OTI b l pd ls cr pr ph bIn bAct F x lin) : bIn.length + bAct.length ≤ 2 * b := by
  cases l with
  | oIdle cur c hh => have := h.2.length_le; have := h.1.2.1; have := h.1.2.2.1; omega
  | oApply a cur c hh =>
    obtain ⟨⟨-, h2, ⟨B', rfl, h3, -⟩, -⟩, h7⟩ := h
    have := h7.length_le; simp; omega
  | oRet cur c hh => have := h.2.length_le; have := h.1.2.1; have := h.1.2.2.1; omega
  | oWait cur hh => have := h.2.length_le; have := h.1.2.1; omega
  | oFlip cur hh => obtain ⟨-, h2, -, -, -, -, h7, -⟩ := h; simp [h7]; omega
  | oSignal cur hh => obtain ⟨-, h2, -, h4, -⟩ := h; simp [h2]; omega
  | _ => exact h.elim

end Podc.ConcurrentSketches
