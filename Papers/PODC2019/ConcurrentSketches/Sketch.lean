import Papers.PODC2019.ConcurrentSketches.Relaxation
import Podc.Computability.Distributed.SharedMemory.HistorySpecLin

/-!
# Fast Concurrent Data Sketches (PODC 2019): sequential and composable sketches

Sections 3–5.1 of the paper.

* `Sketch`: a *derandomised* sequential sketch (Section 4: the coin flips are fixed by an
  oracle, so the sketch is a deterministic object): a state, `init`, `update`, `query`.
  `Sketch.run A` is the state after ingesting the stream `A` from `init`; a state *summarises*
  `A` iff it is `run A` (the paper: "a state summarizes two different streams iff that state is
  reached after ingesting each of them to an empty sketch").
* `Composable` (Section 5.1): a sketch with `merge`, `snapshot` and the pre-filtering API
  `calcHint`/`shouldAdd`, with the paper's semantic requirements as fields:
  - `merge_run`: if `S` summarises `A` and `S'` summarises `A'`, then `merge S S'` summarises
    `A ‖ A'`;
  - `snapQuery_snapshot`: a snapshot answers every query like the sketch it was taken from;
  - `shouldAdd_spec`: if `S` summarises `A` and `shouldAdd(S.calcHint(), a)` is false, then for
    all streams `B₁, B₂`, `A ‖ B₁ ‖ a ‖ B₂` and `A ‖ B₁ ‖ B₂` are summarised by the same state.
  The paper's requirement `calcHint() ≠ 0` is built into the algorithms' encoding of `prop`
  (`Option Hint`, `none` = 0).
* `seqObj S`: the sketch as a CSLib `ObjSpec` (operations `update a`, `query arg`, and the
  never-returning `propagate` operation that starts the background propagator thread of the
  concurrent algorithms; it is a no-op in the sequential specification).
* `SeqSketch S`: the sequential histories of the derandomised sketch (legal histories of
  `seqObj S`, stated directly); `SeqSketchR r S` (Definition 2): histories that have an
  `r`-relaxation in
  `SeqSketch S`.
* `Safe h F`: the hint `h` is safe for the stream `F` (it was computed from a prefix of `F`), so
  filtering out `a` with `shouldAdd h a = false` does not change `run F`.
-/

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

/-- A derandomised sequential sketch (Section 3; the randomness is fixed by an oracle). -/
structure Sketch where
  /-- Sketch states. -/
  State : Type
  /-- Stream elements. -/
  Elem : Type
  /-- Query arguments. -/
  Arg : Type
  /-- Query results. -/
  Val : Type
  /-- The empty sketch (`S.init()`). -/
  init : State
  /-- `S.update(a)`. -/
  update : State → Elem → State
  /-- `S.query(arg)`. -/
  query : State → Arg → Val

namespace Sketch

variable (S : Sketch)

/-- The state after ingesting the stream `A` into the empty sketch: the unique state that
*summarises* `A`. -/
def run (A : List S.Elem) : S.State := A.foldl S.update S.init

@[simp] lemma run_nil : S.run [] = S.init := rfl

lemma run_concat (A : List S.Elem) (a : S.Elem) : S.run (A ++ [a]) = S.update (S.run A) a := by
  simp [run]

end Sketch

/-- A *composable* sketch (Section 5.1) with its semantic requirements. -/
structure Composable extends Sketch where
  /-- `S.merge(S')`. -/
  merge : State → State → State
  /-- Results of `snapshot`. -/
  Snap : Type
  /-- `S.snapshot()`. -/
  snapshot : State → Snap
  /-- Querying a snapshot. -/
  snapQuery : Snap → Arg → Val
  /-- Hints. -/
  Hint : Type
  /-- `S.calcHint()`. -/
  calcHint : State → Hint
  /-- `shouldAdd(h, a)` (a static function). -/
  shouldAdd : Hint → Elem → Bool
  /-- Merging a sketch summarising `A` with one summarising `B` summarises `A ‖ B`. -/
  merge_run : ∀ A B : List Elem,
    merge (A.foldl update init) (B.foldl update init) = (A ++ B).foldl update init
  /-- A snapshot answers every query like the sketch it was taken from. -/
  snapQuery_snapshot : ∀ s q, snapQuery (snapshot s) q = query s q
  /-- Pre-filtering is safe: if `S` summarises `A` and `shouldAdd(S.calcHint(), a)` is false,
  then `A ‖ B₁ ‖ a ‖ B₂` and `A ‖ B₁ ‖ B₂` are summarised by the same state. -/
  shouldAdd_spec : ∀ (A : List Elem) (a : Elem),
    shouldAdd (calcHint (A.foldl update init)) a = false →
      ∀ B₁ B₂ : List Elem,
        (A ++ B₁ ++ a :: B₂).foldl update init = (A ++ B₁ ++ B₂).foldl update init

namespace Composable

variable (S : Composable)

lemma merge_run' (A B : List S.Elem) :
    S.merge (S.run A) (S.run B) = S.run (A ++ B) := S.merge_run A B

/-- The hint `h` is *safe* for the stream `F`: there is a prefix `A` of `F` such that filtering
by `h` is as harmless as filtering by the hint of a sketch summarising `A`. -/
def Safe (h : S.Hint) (F : List S.Elem) : Prop :=
  ∃ A, A <+: F ∧ ∀ a, S.shouldAdd h a = false →
    ∀ B₁ B₂ : List S.Elem, S.run (A ++ B₁ ++ a :: B₂) = S.run (A ++ B₁ ++ B₂)

variable {S}

lemma Safe.append {h : S.Hint} {F : List S.Elem} (hs : S.Safe h F) (G : List S.Elem) :
    S.Safe h (F ++ G) := by
  obtain ⟨A, hA, h⟩ := hs
  exact ⟨A, hA.trans (List.prefix_append F G), h⟩

lemma Safe.mono {h : S.Hint} {F G : List S.Elem} (hs : S.Safe h F) (hFG : F <+: G) :
    S.Safe h G := by
  obtain ⟨T, rfl⟩ := hFG; exact hs.append T

/-- The hint computed from a sketch summarising `F` is safe for `F`. -/
lemma safe_calcHint (F : List S.Elem) : S.Safe (S.calcHint (S.run F)) F :=
  ⟨F, List.prefix_refl F, fun a ha B₁ B₂ => S.shouldAdd_spec F a ha B₁ B₂⟩

/-- Filtering out an element rejected by a safe hint does not change the summary. -/
lemma Safe.run_concat {h : S.Hint} {F : List S.Elem} (hs : S.Safe h F) {a : S.Elem}
    (ha : S.shouldAdd h a = false) : S.run (F ++ [a]) = S.run F := by
  obtain ⟨A, ⟨B, rfl⟩, h⟩ := hs
  simpa using h a ha B []

end Composable

/-! ## The sketch as a sequential object -/

/-- Operations of the sketch object. `propagate` is the (never-returning) operation that starts
the background propagator thread of the concurrent algorithms; it is a no-op sequentially. -/
inductive SkOp (S : Sketch) where
  | update (a : S.Elem)
  | query (q : S.Arg)
  | propagate

/-- Responses of the sketch object. -/
inductive SkResp (S : Sketch) where
  | ack
  | val (v : S.Val)

/-- The derandomised sequential sketch as a deterministic sequential object. -/
abbrev seqObj (S : Sketch) : ObjSpec where
  State := S.State
  Op := SkOp S
  Resp := SkResp S
  init := S.init
  δ s o := match o with
    | .update a => (S.update s a, .ack)
    | .query q => (s, .val (S.query s q))
    | .propagate => (s, .ack)

/-- The response of the sequential sketch in state `s` to operation `o`. -/
def seqResp (S : Sketch) (s : S.State) : SkOp S → SkResp S
  | .update _ => .ack
  | .query q => .val (S.query s q)
  | .propagate => .ack

/-- Entries of sequential histories: an operation instance with its operation and response. -/
abbrev Entry (P : Type) (S : Sketch) := OpId P × SkOp S × SkResp S

variable {P : Type} {S : Sketch}

/-- The stream of an entry list: the arguments of its updates, in order. -/
def upds : List (Entry P S) → List S.Elem :=
  List.filterMap fun e => match e.2.1 with
    | .update a => some a
    | _ => none

@[simp] lemma upds_nil : upds ([] : List (Entry P S)) = [] := rfl

@[simp] lemma upds_append (H H' : List (Entry P S)) : upds (H ++ H') = upds H ++ upds H' := by
  simp [upds]

@[simp] lemma upds_update (x : OpId P) (a : S.Elem) (r : SkResp S) :
    upds [((x, .update a, r) : Entry P S)] = [a] := rfl

@[simp] lemma upds_query (x : OpId P) (q : S.Arg) (r : SkResp S) :
    upds [((x, .query q, r) : Entry P S)] = [] := rfl

/-- `SeqSketch` (Section 4): the sequential histories of the derandomised sketch, i.e. those in
which every operation gets the response of the sequential sketch that has ingested the updates
preceding it (the legal histories of `seqObj S`). -/
def SeqSketch (S : Sketch) (H : List (Entry P S)) : Prop :=
  ∀ H₁ e H₂, H = H₁ ++ e :: H₂ → e.2.2 = seqResp S (S.run (upds H₁)) e.2.1

/-- `SeqSketch_r` (Definition 2): the histories that have an `r`-relaxation in `SeqSketch`. -/
def SeqSketchR (r : ℕ) (S : Sketch) (H' : List (Entry P S)) : Prop :=
  ∃ H, SeqSketch S H ∧ IsRelaxation r H H'

lemma seqSketch_nil : SeqSketch S ([] : List (Entry P S)) := by
  intro H₁ e H₂ h; simp at h

/-- Appending one entry to a history of `SeqSketch`. -/
lemma seqSketch_concat {H : List (Entry P S)} (hH : SeqSketch S H) (e : Entry P S)
    (he : e.2.2 = seqResp S (S.run (upds H)) e.2.1) : SeqSketch S (H ++ [e]) := by
  intro H₁ e' H₂ h
  rcases H₂.eq_nil_or_concat with rfl | ⟨H₂', z, rfl⟩
  · rw [← List.concat_eq_append, ← List.concat_eq_append] at h
    obtain ⟨rfl, rfl⟩ := List.concat_inj.1 h
    exact he
  · have h' : H ++ [e] = (H₁ ++ e' :: H₂') ++ [z] := by rw [h]; simp
    obtain ⟨rfl, -⟩ := List.append_inj' h' rfl
    exact hH _ _ _ rfl

lemma seqSketch_append {H : List (Entry P S)} (hH : SeqSketch S H) (G : List (Entry P S))
    (hG : ∀ e ∈ G, e.2.2 = .ack ∧ ∀ q, e.2.1 ≠ .query q) : SeqSketch S (H ++ G) := by
  induction G using List.reverseRecOn with
  | nil => simpa using hH
  | append_singleton G e ih =>
    rw [← List.append_assoc]
    refine seqSketch_concat (ih fun e he => hG e (by simp [he])) e ?_
    obtain ⟨x, o, r⟩ := e
    obtain ⟨h1, h2⟩ := hG (x, o, r) (by simp)
    simp only at h1 h2 ⊢; subst h1
    cases o with
    | update a => rfl
    | query q => exact absurd rfl (h2 q)
    | propagate => rfl

end Podc.ConcurrentSketches
