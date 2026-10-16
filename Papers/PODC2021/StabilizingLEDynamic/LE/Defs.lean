import Papers.PODC2021.StabilizingLEDynamic.Model
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max

/-!
# Algorithm `LE` (Algorithm 1)

The pseudo-stabilizing leader election algorithm for `J^B_{1,*}(Δ)`.

## Data

* `FMap ι α`: finite maps `ι ⇀ α` (the paper's `MapType`, whose tuples are
  `⟨id, susp, ttl⟩`), as functions `ι → Option α` with finite support; here `α = ℕ × Fin (Δ+1)`
  (suspicion value, timer in `{0, …, Δ}`).
* `Rcd`: records `⟨id, LSPs, ttl⟩`.
* `St`: the local state `(lid, Lstable, Gstable, msgs)`; every component may be arbitrary
  initially (finite maps, finite set of records, timers in `{0, …, Δ}`).

## One round of process `me` (lines 2–27)

The received records (`mailbox`) are those records `r ∈ msgs(q)` with `r.ttl > 0` and
`r.id ∈ r.LSPs` (line 2) of every in-neighbour `q ≠ me`. The loop of lines 11–18 processes them in
an arbitrary but fixed order (`Finset.toList`); all lemmas hold for every order.
-/

namespace StabilizingLEDynamic.LE

open Cslib.HeardOf

/-! ### Finite maps -/

/-- A finite map from `ι` to `α`. -/
@[ext]
structure FMap (ι α : Type*) where
  /-- The underlying partial function. -/
  f : ι → Option α
  /-- Finite support. -/
  fin : {i | f i ≠ none}.Finite

namespace FMap

variable {ι α : Type*}

/-- Build a map from a partial function supported in a finite set. -/
def ofSub (f : ι → Option α) (S : Set ι) (hS : S.Finite) (h : ∀ i, f i ≠ none → i ∈ S) :
    FMap ι α :=
  ⟨f, hS.subset fun i hi => h i hi⟩

/-- `M[k] := v` (insertion, refresh, or removal with `v = none`). -/
def set [DecidableEq ι] (M : FMap ι α) (k : ι) (v : Option α) : FMap ι α :=
  ofSub (Function.update M.f k v) (insert k {i | M.f i ≠ none}) (M.fin.insert k) fun i hi => by
    by_cases hik : i = k
    · exact Or.inl hik
    · right; simpa [Function.update_of_ne hik] using hi

/-- Transform every entry (possibly deleting it). -/
def modify (M : FMap ι α) (g : ι → α → Option α) : FMap ι α :=
  ofSub (fun i => (M.f i).bind (g i)) {i | M.f i ≠ none} M.fin fun i hi => by
    intro h; simp [h] at hi

@[simp] theorem set_f [DecidableEq ι] (M : FMap ι α) (k : ι) (v : Option α) (i : ι) :
    (M.set k v).f i = if i = k then v else M.f i := by
  simp only [set, ofSub]
  by_cases h : i = k
  · subst h; simp
  · simp [Function.update_of_ne h, h]

@[simp] theorem modify_f (M : FMap ι α) (g : ι → α → Option α) (i : ι) :
    (M.modify g).f i = (M.f i).bind (g i) := rfl

/-- The (finite) domain. -/
noncomputable def dom (M : FMap ι α) : Finset ι := M.fin.toFinset

@[simp] theorem mem_dom {M : FMap ι α} {i : ι} : i ∈ M.dom ↔ M.f i ≠ none := by
  simp [dom]

end FMap

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ}

/-- An entry of a `MapType` map: (suspicion value, timer). -/
abbrev Entry (Δ : ℕ) := ℕ × Fin (Δ + 1)

/-- The paper's `MapType`. -/
abbrev MapT (ι : Type*) (Δ : ℕ) := FMap ι (Entry Δ)

/-- A record `⟨id, LSPs, ttl⟩`. -/
@[ext]
structure Rcd (ι : Type*) (Δ : ℕ) where
  /-- The identifier of the initiator. -/
  id : ι
  /-- The `Lstable` map of the initiator when it initiated the record. -/
  lsps : MapT ι Δ
  /-- Remaining relay time. -/
  ttl : Fin (Δ + 1)

/-- The local state of a process. -/
structure St (ι : Type*) (Δ : ℕ) where
  /-- The output: identifier of the leader. -/
  lid : ι
  /-- Locally stable processes. -/
  L : MapT ι Δ
  /-- Globally stable processes. -/
  G : MapT ι Δ
  /-- Records to be sent in the next round. -/
  msgs : Finset (Rcd ι Δ)

open Classical

/-- `M[k].susp` (`0` if absent; only used when present). -/
def suspOf (M : MapT ι Δ) (k : ι) : ℕ := match M.f k with
  | some e => e.1
  | none => 0

/-- Decrement a timer (`0` stays `0`). -/
def dec (t : Fin (Δ + 1)) : Fin (Δ + 1) := ⟨t.val - 1, by omega⟩

/-- The records actually sent by a process in state `s` (line 2). -/
noncomputable def sent (s : St ι Δ) : Finset (Rcd ι Δ) :=
  s.msgs.filter fun r => 0 < r.ttl.val ∧ r.lsps.f r.id ≠ none

/-- The set of records received by `me` (from in-neighbours other than itself). -/
def mailboxSet (me : ι) (m : ι → Option (St ι Δ)) : Set (Rcd ι Δ) :=
  {r | ∃ q, q ≠ me ∧ ∃ s, m q = some s ∧ r ∈ sent s}

/-- The mailbox as a finite set (it is always finite in executions; `∅` is a junk value). -/
noncomputable def mailbox (me : ι) (m : ι → Option (St ι Δ)) : Finset (Rcd ι Δ) :=
  if h : (mailboxSet me m).Finite then h.toFinset else ∅

/-- Increment the suspicion value of `me` (line 18). -/
def incr (me : ι) (M : MapT ι Δ) : MapT ι Δ :=
  M.modify fun k e => if k = me then some (e.1 + 1, e.2) else some e

/-- Lines 13 and 18 restricted to `msgs`: line 13. -/
noncomputable def bodyM (me : ι) (M : Finset (Rcd ι Δ)) (r : Rcd ι Δ) : Finset (Rcd ι Δ) :=
  if r.id ≠ me ∧ ¬ ∃ r' ∈ M, r'.id = r.id ∧ r'.ttl = r.ttl then insert r M else M

/-- Lines 14–15 and 18 restricted to `Lstable`. -/
noncomputable def bodyL (me : ι) (L : MapT ι Δ) (r : Rcd ι Δ) : MapT ι Δ :=
  if r.id = me then L else
  let L := if L.f r.id = none ∨ ∃ e, L.f r.id = some e ∧ e.2 < r.ttl
    then L.set r.id (some (suspOf r.lsps r.id, r.ttl)) else L
  if r.lsps.f me = none then incr me L else L

/-- Lines 16–17 and 18 restricted to `Gstable`. -/
noncomputable def bodyG (me : ι) (G : MapT ι Δ) (r : Rcd ι Δ) : MapT ι Δ :=
  if r.id = me then G else
  let G : MapT ι Δ := FMap.ofSub
    (fun k => if k ≠ me ∧ r.lsps.f k ≠ none then some (suspOf r.lsps k, Fin.last Δ) else G.f k)
    ({k | G.f k ≠ none} ∪ {k | r.lsps.f k ≠ none}) (G.fin.union r.lsps.fin) (fun k hk => by
      by_cases h : k ≠ me ∧ r.lsps.f k ≠ none
      · exact Or.inr h.2
      · left; simpa [h] using hk)
  if r.lsps.f me = none then incr me G else G

/-- Lines 12–18 for one received record `r`, acting on `(msgs, Lstable, Gstable)`. Each line
only reads and writes one of the three variables (line 18 touches only the entries of `me`, which
lines 15 and 17 never touch), so the body acts componentwise. -/
noncomputable def body (me : ι) (x : Finset (Rcd ι Δ) × MapT ι Δ × MapT ι Δ) (r : Rcd ι Δ) :
    Finset (Rcd ι Δ) × MapT ι Δ × MapT ι Δ :=
  (bodyM me x.1 r, bodyL me x.2.1 r, bodyG me x.2.2 r)

/-- The leader chosen from a `Gstable` map (line 27): the smallest identifier among those with
minimum suspicion value (`me` if the map is empty, which never happens after line 5). -/
noncomputable def leaderOf (me : ι) (G : MapT ι Δ) : ι :=
  if h : G.dom.Nonempty then
    let m := (G.dom.image (suspOf G)).min' (h.image _)
    if h2 : (G.dom.filter fun k => suspOf G k = m).Nonempty then
      (G.dom.filter fun k => suspOf G k = m).min' h2
    else me
  else me

/-- Line 4. -/
noncomputable def initL (me : ι) (L : MapT ι Δ) : MapT ι Δ :=
  if ∃ σ, L.f me = some (σ, Fin.last Δ) then L else L.set me (some (0, Fin.last Δ))

/-- Lines 5–6 (`L` is the map after line 4). -/
noncomputable def initG (me : ι) (L G : MapT ι Δ) : MapT ι Δ :=
  if ∃ σ, G.f me = some (σ, Fin.last Δ) ∧ σ = suspOf L me then G else G.set me (L.f me)

/-- Lines 7–10: decrement the nonzero timers of the other identifiers. -/
def decAll (me : ι) (M : MapT ι Δ) : MapT ι Δ :=
  M.modify fun k e => if k ≠ me ∧ e.2.val ≠ 0 then some (e.1, dec e.2) else some e

/-- Lines 19–22: remove the entries with timer `0`. -/
def purge (M : MapT ι Δ) : MapT ι Δ :=
  M.modify fun _ e => if e.2.val = 0 then none else some e

/-- Lines 23–26 (`L` is the final `Lstable`). -/
noncomputable def finalMsgs (me : ι) (L : MapT ι Δ) (M : Finset (Rcd ι Δ)) :
    Finset (Rcd ι Δ) :=
  insert ⟨me, L, Fin.last Δ⟩ ((M.filter fun r => r.ttl.val ≠ 0 ∧ r.lsps.f r.id ≠ none).image
    fun r => { r with ttl := dec r.ttl })

/-- The loop of lines 11–18 over the received records, in the order of the list `mb`. -/
noncomputable def loop (me : ι) (mb : List (Rcd ι Δ)) (s : St ι Δ) :
    Finset (Rcd ι Δ) × MapT ι Δ × MapT ι Δ :=
  mb.foldl (body me)
    (s.msgs, decAll me (initL me s.L), decAll me (initG me (initL me s.L) s.G))

/-- One round of Algorithm `LE` at process `me`, from its state `s`, processing the received
records in the order of the list `mb`. -/
noncomputable def roundLE (me : ι) (s : St ι Δ) (mb : List (Rcd ι Δ)) : St ι Δ :=
  let y := loop me mb s
  ⟨leaderOf me (purge y.2.2), purge y.2.1, purge y.2.2, finalMsgs me (purge y.2.1) y.1⟩

/-- The arbitrary state used if a process does not receive its own state (never happens). -/
def junk (me : ι) : St ι Δ := ⟨me, ⟨fun _ => none, by simp⟩, ⟨fun _ => none, by simp⟩, ∅⟩

/-- Algorithm `LE` as a full-information algorithm (`lid` is the output). -/
noncomputable def algLE (Δ : ℕ) : Algorithm ι (St ι Δ) where
  step me m := roundLE me ((m me).getD (junk me)) (mailbox me m).toList
  lid _ s := s.lid

end StabilizingLEDynamic.LE
