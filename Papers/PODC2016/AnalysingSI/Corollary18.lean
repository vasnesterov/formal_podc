import Papers.PODC2016.AnalysingSI.Theorem16

/-!
# Corollary 18: the static chopping analysis (Cerone–Gotsman, PODC 2016, §5)

A set of chopped programs `P = {P₁, P₂, …}` is abstracted by the number `kᵢ` of pieces of each
program and the read and write sets `Rⱼⁱ`, `Wⱼⁱ` of its pieces. The static chopping graph
`SCG(P)` has the pieces as vertices, successor/predecessor edges inside a program, and
read-dependency, write-dependency and anti-dependency edges between pieces of different programs whose read and write sets
intersect accordingly. A history is *produced by* `P` if its sessions correspond one-to-one to
programs of `P` and the `j`-th transaction of a session only reads objects of the read set and
writes objects of the write set of the `j`-th piece of its program.
-/

namespace Podc.AnalysingSI

open Relation

variable {Obj V : Type*} [DecidableEq Obj]

/-- The read and write sets of a set of chopped programs indexed by `κ`. -/
structure Programs (κ Obj : Type*) where
  /-- Number of pieces of each program. -/
  k : κ → ℕ
  /-- Read set `Rⱼⁱ` of the `j`-th piece of program `i`. -/
  R : κ → ℕ → Set Obj
  /-- Write set `Wⱼⁱ` of the `j`-th piece of program `i`. -/
  W : κ → ℕ → Set Obj

namespace Programs

variable {κ : Type*} (P : Programs κ Obj)

/-- The pieces `(i, j)`, `j < kᵢ`: vertices of `SCG(P)`. -/
def Piece : Type _ := {p : κ × ℕ // p.2 < P.k p.1}

open Chopped in
/-- The static chopping graph `SCG(P)`. -/
def scg : CLbl → P.Piece → P.Piece → Prop
  | .succ => fun p q => p.1.1 = q.1.1 ∧ p.1.2 < q.1.2
  | .pred => fun p q => p.1.1 = q.1.1 ∧ q.1.2 < p.1.2
  | .wr => fun p q => p.1.1 ≠ q.1.1 ∧ (P.W p.1.1 p.1.2 ∩ P.R q.1.1 q.1.2).Nonempty
  | .ww => fun p q => p.1.1 ≠ q.1.1 ∧ (P.W p.1.1 p.1.2 ∩ P.W q.1.1 q.1.2).Nonempty
  | .rw => fun p q => p.1.1 ≠ q.1.1 ∧ (P.R p.1.1 p.1.2 ∩ P.W q.1.1 q.1.2).Nonempty

/-- A chopped history `C` can be produced by the programs `P`: an injective assignment of
programs to sessions such that the `j`-th transaction of each session corresponds to the `j`-th
piece of its program, and the read and write sets of the piece cover the objects read and written
by the transaction. -/
def Produces {ι : Type*} (C : Chopped ι Obj V) : Prop :=
  ∃ prog : ι → κ, Function.Injective prog ∧ ∀ s j (hj : j < (C.sess s).length),
    j < P.k (prog s) ∧
      (∀ x n, Op.read x n ∈ (C.sess s)[j] → x ∈ P.R (prog s) j) ∧
      (∀ x n, Op.write x n ∈ (C.sess s)[j] → x ∈ P.W (prog s) j)

end Programs

/-- Mapping the vertices of a walk. -/
theorem Walk.mapVert {L α β : Type*} {E : L → α → α → Prop} {E' : L → β → β → Prop} (f : α → β)
    (hE : ∀ l x y, E l x y → E' l (f x) (f y)) {a b : α} {w : List (L × α)}
    (h : Walk E a w b) : Walk E' (f a) (w.map (Prod.map id f)) (f b) := by
  induction h with
  | nil => exact Walk.nil _
  | cons he _ ih => exact Walk.cons (hE _ _ _ he) ih

namespace Txn

theorem mem_of_reads {T : Txn Obj V} {x : Obj} {n : V} (h : T.Reads x n) : Op.read x n ∈ T :=
  List.mem_of_find?_eq_some h

theorem mem_of_writes {T : Txn Obj V} {x : Obj} {n : V} (h : T.Writes x n) :
    Op.write x n ∈ T := by
  have := List.mem_of_getLast? h
  exact (List.mem_filter.1 this).1

end Txn

open Chopped

/-- **Corollary 18** of Cerone–Gotsman: the chopping defined by `P` is correct — every dependency
graph `G ∈ GraphSI` whose history can be produced by `P` is spliceable — if `SCG(P)` contains no
critical cycles. -/
theorem corollary18 {κ : Type*} (P : Programs κ Obj) (hP : ∀ w, ¬ IsCriticalIn P.scg w)
    {ι : Type*} (C : Chopped ι Obj V) (hC : P.Produces C)
    (WR WW : Obj → C.Tid → C.Tid → Prop) (hG : (C.graph WR WW).IsSI) : C.Spliceable := by
  refine theorem16 C WR WW hG fun w hw => ?_
  obtain ⟨prog, hinj, hprog⟩ := hC
  have hdg := hG.1
  let f : C.Tid → P.Piece := fun p => ⟨(prog p.1.1, p.1.2), (hprog _ _ p.2).1⟩
  have hf : Function.Injective f := by
    intro p q h
    have h' := congrArg Subtype.val h
    simp only [f, Prod.mk.injEq] at h'
    have h := h'
    exact Subtype.ext (Prod.ext (hinj h.1) h.2)
  have hne : ∀ p q : C.Tid, p.1.1 ≠ q.1.1 → (f p).1.1 ≠ (f q).1.1 :=
    fun p q h e => h (hinj e)
  have hR : ∀ (p : C.Tid) x n, ((C.graph WR WW).txn p).Reads x n → x ∈ P.R (f p).1.1 (f p).1.2 :=
    fun p x n h => (hprog _ _ p.2).2.1 x n (Txn.mem_of_reads h)
  have hW : ∀ (p : C.Tid) x, (C.graph WR WW).WriteTx x p → x ∈ P.W (f p).1.1 (f p).1.2 :=
    fun p x ⟨n, h⟩ => (hprog _ _ p.2).2.2 x n (Txn.mem_of_writes h)
  have hE : ∀ l x y, dcg (C.graph WR WW) l x y → P.scg l (f x) (f y) := by
    intro l p q hpq
    cases l with
    | succ => exact ⟨congrArg prog hpq.1, hpq.2⟩
    | pred => exact ⟨congrArg prog hpq.1.symm, hpq.2⟩
    | wr =>
      obtain ⟨⟨x, h⟩, hs⟩ := hpq
      obtain ⟨n, -, hw, hr⟩ := hdg.wr_val p q x h
      exact ⟨hne p q hs, x, hW p x ⟨n, hw⟩, hR q x n hr⟩
    | ww =>
      obtain ⟨⟨x, h⟩, hs⟩ := hpq
      obtain ⟨h1, h2⟩ := hdg.ww_writeTx x p q h
      exact ⟨hne p q hs, x, hW p x h1, hW q x h2⟩
    | rw =>
      obtain ⟨⟨x, -, T', hT'p, hT'q⟩, hs⟩ := hpq
      obtain ⟨n, -, -, hr⟩ := hdg.wr_val T' p x hT'p
      exact ⟨hne p q hs, x, hR p x n hr, hW q x (hdg.ww_writeTx x T' q hT'q).2⟩
  obtain ⟨⟨hwne, a, hwalk⟩, hsimple, hcpc, hsep⟩ := hw
  have hlab : labels (w.map (Prod.map id f)) = labels w := by
    simp only [labels, List.map_map]; rfl
  refine hP (w.map (Prod.map id f)) ⟨⟨by simpa using hwne, f a, hwalk.mapVert f hE⟩, ?_, ?_, ?_⟩
  · unfold IsSimple at hsimple ⊢
    rw [List.map_map]
    have : (Prod.snd ∘ Prod.map (id : CLbl → CLbl) f) = f ∘ Prod.snd := rfl
    rw [this, ← List.map_map]
    exact hsimple.map hf
  · rw [hlab]; exact hcpc
  · rw [hlab]; exact hsep

end Podc.AnalysingSI
