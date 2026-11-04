import Papers.PODC2018.CausalRecordReplay.Basic

/-!
# The shared-memory model of Sections 2–4

R. L. Jones, M. S. Khan, N. H. Vaidya. *Optimal Record and Replay under Causal Consistency.*
PODC 2018 (brief announcement); full version arXiv:1805.08804v2.

* `Program P Op X`: processes `P`, operations `Op`, shared variables `X`; every operation has a
  process, a kind (read/write) and a variable; the program order `po` is a strict total order on
  the operations of each process and relates no operations of different processes (Section 2).
* An `Execution` is a writes-to map (Definition 2.1); `none` is the initial value.
* A view of process `i` (Section 3) is a strict total order on `Obs i = (∗,i,∗,∗) ∪ (w,∗,∗,∗)` in
  which each read of `i` returns the last value written to its variable (`IsViewOf`).
* Strong causal order `SCO` (Definition 3.3) and strong causal consistency (Definition 3.4).
* Records, replays and good records for both RnR models (Section 4).

The replay is any execution explained by views `V'` that respect the record. The values read in
the replay are not constrained: every family of strict total orders explains some execution
(`exists_explains`), so "there is a replay certified by `V'`" just means that `V'` is a family of
strict total orders satisfying the consistency condition and respecting the record.
-/

namespace Podc.CausalRecordReplay

open Relation

/-- A shared-memory program (Section 2): processes `P`, operations `Op`, variables `X`. -/
structure Program (P Op X : Type*) where
  /-- The process performing the operation. -/
  proc : Op → P
  /-- The operation is a write (otherwise it is a read). -/
  IsWrite : Op → Prop
  /-- The shared variable accessed. -/
  var : Op → X
  /-- Program order. -/
  po : Op → Op → Prop
  po_irrefl : ∀ a, ¬ po a a
  po_trans : ∀ {a b c}, po a b → po b c → po a c
  po_proc : ∀ {a b}, po a b → proc a = proc b
  po_total : ∀ {a b}, proc a = proc b → a ≠ b → po a b ∨ po b a

variable {P Op X : Type*} (π : Program P Op X)

namespace Program

/-- The operations observed by process `i`: `(∗,i,∗,∗) ∪ (w,∗,∗,∗)`. -/
def Obs (i : P) (o : Op) : Prop := π.proc o = i ∨ π.IsWrite o

/-- Program order restricted to `Obs i`, i.e. `PO | (∗,i,∗,∗) ∪ (w,∗,∗,∗)`. -/
def poOn (i : P) (a b : Op) : Prop := π.po a b ∧ π.Obs i a ∧ π.Obs i b

/-- An execution: the writes-to relation (Definition 2.1), as the write read by each read
(`none` = the initial value). -/
structure Execution (Op : Type*) where
  rf : Op → Option Op

/-- `w` is the last write to the variable of the read `rd` before `rd` in the order `r`. -/
def LastWriteBefore (r : Op → Op → Prop) (rd w : Op) : Prop :=
  π.IsWrite w ∧ π.var w = π.var rd ∧ r w rd ∧
    ∀ w', π.IsWrite w' → π.var w' = π.var rd → r w' rd → w' = w ∨ r w' w

/-- `r` is a view of the execution `ex` on the set `S` (Section 3): a strict total order on `S` in
which each read of `S` returns the last value written to its variable. -/
def IsViewOf (ex : Execution Op) (S : Op → Prop) (r : Op → Op → Prop) : Prop :=
  IsStrictTotalOn S r ∧
    ∀ rd, S rd → ¬ π.IsWrite rd →
      match ex.rf rd with
      | some w => π.LastWriteBefore r rd w
      | none => ∀ w, π.IsWrite w → π.var w = π.var rd → ¬ r w rd

/-- The per-process views `V` explain the execution `ex`: each `V i` is a view on `Obs i`. -/
def Explains (ex : Execution Op) (V : P → Op → Op → Prop) : Prop :=
  ∀ i, π.IsViewOf ex (π.Obs i) (V i)

/-- Definition 3.3 (strong causal order): `(w₁, w₂) ∈ SCO(V)` iff both are writes and
`w₁ <_{V_j} w₂` where `j` is the process of `w₂`. -/
def SCO (V : P → Op → Op → Prop) (a b : Op) : Prop :=
  π.IsWrite a ∧ π.IsWrite b ∧ V (π.proc b) a b

/-- Definition 3.4 (strong causal consistency), condition on the views: each `V i` is a strict
total order on `Obs i` respecting `SCO(V) ∪ PO|Obs i` (union with transitive closure). -/
def StronglyCausal (V : P → Op → Op → Prop) : Prop :=
  ∀ i, IsStrictTotalOn (π.Obs i) (V i) ∧
    ∀ a b, TransGen (fun x y => π.SCO V x y ∨ π.poOn i x y) a b → V i a b

/-- Definition 3.4: the views `V` explain the execution `ex` under strong causal consistency. -/
def SCCExplains (ex : Execution Op) (V : P → Op → Op → Prop) : Prop :=
  π.Explains ex V ∧ π.StronglyCausal V

/-! ### Records and replays (Section 4) -/

/-- RnR Model 1: `R` is a record of `V` if `R i ⊆ V i` for all `i`. -/
def IsRecord1 (V R : P → Op → Op → Prop) : Prop := ∀ i a b, R i a b → V i a b

/-- RnR Model 1: the record `R` of `V` is good if every set of views `V'` certifying a strongly
causally consistent replay valid for `R` (views of some execution, strongly causal, respecting
`R`) equals `V`. -/
def Good1 (V R : P → Op → Op → Prop) : Prop :=
  ∀ (ex : Execution Op) (V' : P → Op → Op → Prop), π.SCCExplains ex V' →
    (∀ i a b, R i a b → V' i a b) → V' = V

/-- The data-race order `DRO(V_i)`: pairs of `V_i` on the same variable. -/
def DRO (r : Op → Op → Prop) (a b : Op) : Prop := r a b ∧ π.var a = π.var b

/-- RnR Model 2: `R` is a record of `V` if `R i ⊆ DRO(V i)` for all `i`. -/
def IsRecord2 (V R : P → Op → Op → Prop) : Prop := ∀ i a b, R i a b → π.DRO (V i) a b

/-- RnR Model 2: the record `R` of `V` is good if every set of views certifying a strongly causally
consistent replay valid for `R` has the same data-race orders as `V`. -/
def Good2 (V R : P → Op → Op → Prop) : Prop :=
  ∀ (ex : Execution Op) (V' : P → Op → Op → Prop), π.SCCExplains ex V' →
    (∀ i a b, R i a b → V' i a b) → ∀ i, π.DRO (V' i) = π.DRO (V i)

/-! ### Basic facts -/

theorem po_obs {i : P} {a b : Op} (h : π.po a b) (ha : π.Obs i a) (hb : π.Obs i b) :
    π.poOn i a b := ⟨h, ha, hb⟩

theorem write_obs {o : Op} (h : π.IsWrite o) (i : P) : π.Obs i o := Or.inr h

theorem own_obs (o : Op) : π.Obs (π.proc o) o := Or.inl rfl

variable {π}

theorem StronglyCausal.total {V : P → Op → Op → Prop} (hV : π.StronglyCausal V) (i : P) :
    IsStrictTotalOn (π.Obs i) (V i) := (hV i).1

theorem StronglyCausal.sco {V : P → Op → Op → Prop} (hV : π.StronglyCausal V) (i : P)
    {a b : Op} (h : π.SCO V a b) : V i a b :=
  (hV i).2 a b (TransGen.single (Or.inl h))

theorem StronglyCausal.po {V : P → Op → Op → Prop} (hV : π.StronglyCausal V) (i : P)
    {a b : Op} (h : π.po a b) (ha : π.Obs i a) (hb : π.Obs i b) : V i a b :=
  (hV i).2 a b (TransGen.single (Or.inr ⟨h, ha, hb⟩))

/-- Strong causal consistency only needs `SCO(V) ⊆ V i` and `PO|Obs i ⊆ V i`, since each `V i` is
transitive. -/
theorem stronglyCausal_iff {V : P → Op → Op → Prop} :
    π.StronglyCausal V ↔ ∀ i, IsStrictTotalOn (π.Obs i) (V i) ∧
      (∀ a b, π.SCO V a b → V i a b) ∧ (∀ a b, π.poOn i a b → V i a b) := by
  refine ⟨fun h i => ⟨h.total i, fun a b hab => h.sco i hab,
    fun a b hab => h.po i hab.1 hab.2.1 hab.2.2⟩, fun h i => ⟨(h i).1, fun a b hab => ?_⟩⟩
  induction hab with
  | single hab => exact hab.elim ((h i).2.1 _ _) ((h i).2.2 _ _)
  | tail _ hbc ih => exact (h i).1.trans ih (hbc.elim ((h i).2.1 _ _) ((h i).2.2 _ _))

/-- Two operations of the same process ordered by a strongly causal view are ordered by `PO`. -/
theorem StronglyCausal.po_of_view {V : P → Op → Op → Prop} (hV : π.StronglyCausal V) {i : P}
    {a b : Op} (hab : V i a b) (hp : π.proc a = π.proc b) : π.po a b := by
  have ha := ((hV.total i).supp hab).1
  have hb := ((hV.total i).supp hab).2
  rcases π.po_total hp ((hV.total i).ne hab) with h | h
  · exact h
  · exact absurd (hV.po i h hb ha) ((hV.total i).asymm hab)

/-- `SCO(V)` is transitive for strongly causal views. -/
theorem StronglyCausal.sco_trans {V : P → Op → Op → Prop} (hV : π.StronglyCausal V) {a b c : Op}
    (hab : π.SCO V a b) (hbc : π.SCO V b c) : π.SCO V a c :=
  ⟨hab.1, hbc.2.1, (hV.total _).trans (hV.sco _ hab) hbc.2.2⟩

/-- `SCO(V)` is a strict partial order for strongly causal views (when there is a process). -/
theorem StronglyCausal.sco_strictPO {V : P → Op → Op → Prop} (hV : π.StronglyCausal V) :
    IsStrictPO (π.SCO V) :=
  ⟨fun a h => (hV.total (π.proc a)).irrefl a h.2.2, fun h1 h2 => hV.sco_trans h1 h2⟩

/-- Every family of strict total orders on the sets `Obs i` explains some execution: the replay's
read values are determined by the views. -/
theorem exists_explains [Finite Op] (V : P → Op → Op → Prop)
    (hV : ∀ i, IsStrictTotalOn (π.Obs i) (V i)) : ∃ ex : Program.Execution Op, π.Explains ex V := by
  classical
  -- for each read, the last write to its variable before it in its process's view
  have hlast : ∀ rd, (∃ w, π.IsWrite w ∧ π.var w = π.var rd ∧ V (π.proc rd) w rd) →
      ∃ w, π.LastWriteBefore (V (π.proc rd)) rd w := by
    intro rd hex
    have hpo := (hV (π.proc rd)).toStrictPO
    -- a maximal element of the finite set of candidate writes
    let S : Set Op := {w | π.IsWrite w ∧ π.var w = π.var rd ∧ V (π.proc rd) w rd}
    have hwf := hpo.swap.wellFounded
    obtain ⟨w, hwS, hmax⟩ := hwf.has_min S hex
    refine ⟨w, hwS.1, hwS.2.1, hwS.2.2, fun w' h1 h2 h3 => ?_⟩
    by_cases hww : w' = w
    · exact Or.inl hww
    · right
      rcases (hV _).total ((hV _).supp h3).1 ((hV _).supp hwS.2.2).1 hww with h | h
      · exact h
      · exact absurd h (hmax w' ⟨h1, h2, h3⟩)
  refine ⟨⟨fun rd => if h : ∃ w, π.LastWriteBefore (V (π.proc rd)) rd w then some h.choose
    else none⟩, fun i => ⟨hV i, fun rd hrd hnw => ?_⟩⟩
  have hi : π.proc rd = i := hrd.resolve_right hnw
  subst hi
  simp only
  split
  · rename_i w hw
    split at hw
    · rename_i h
      cases hw
      exact h.choose_spec
    · cases hw
  · rename_i hw
    split at hw
    · cases hw
    · rename_i h
      intro w h1 h2 h3
      exact h (hlast rd ⟨w, h1, h2, h3⟩)

end Program

end Podc.CausalRecordReplay
