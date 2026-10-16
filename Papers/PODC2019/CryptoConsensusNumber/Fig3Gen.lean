import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Generic tools for Figure 3 (CSLib candidates)

* `linResp A L x`: the response the sequential run of `L` gives to (the first occurrence of) `x`;
  lemmas for appending and for inserting a state-neutral operation;
* `isLin_insert`: retroactive linearization point (insert a pending operation that does not
  change the state at the chosen position; copy of `IsLinearization.insert` of
  `Papers/PODC2021/ScannableBinaryObjects/Impl1Lin.lean`, under another name);
* `split_insert'`: how a split `L = S₁ ++ S₂` survives such an insertion (with the insertion
  position made explicit).
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory List

section Generic

variable {P : Type} [DecidableEq P] (A : ObjSpec)

-- CSLib candidate
/-- The response the sequential run of `L` from state `q` gives to the first occurrence of `x`
(`none` if `x` does not occur). -/
def linRespFrom : A.State → List (OpId P × A.Op) → OpId P → Option A.Resp
  | _, [], _ => none
  | q, (y, o) :: L, x => if y = x then some (A.δ q o).2 else linRespFrom (A.δ q o).1 L x

-- CSLib candidate
/-- The response of `x` in the sequential history `L` (from the initial state). -/
def linResp (L : List (OpId P × A.Op)) (x : OpId P) : Option A.Resp :=
  linRespFrom A A.init L x

variable {A}

lemma linRespFrom_append_of_mem (q : A.State) (L M : List (OpId P × A.Op)) (x : OpId P)
    (hx : x ∈ L.map Prod.fst) : linRespFrom A q (L ++ M) x = linRespFrom A q L x := by
  induction L generalizing q with
  | nil => simp at hx
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [cons_append, linRespFrom]
    split_ifs with h
    · rfl
    · simp only [map_cons, mem_cons] at hx
      exact ih _ (hx.resolve_left (fun h' => h h'.symm))

lemma linRespFrom_append_of_not_mem (q : A.State) (L M : List (OpId P × A.Op)) (x : OpId P)
    (hx : x ∉ L.map Prod.fst) :
    linRespFrom A q (L ++ M) x = linRespFrom A (A.runOps q (L.map Prod.snd)) M x := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [map_cons, mem_cons, not_or] at hx
    simp only [cons_append, linRespFrom, Ne.symm hx.1, ite_false, map_cons, ObjSpec.runOps_cons]
    exact ih _ hx.2

lemma linRespFrom_eq_none (q : A.State) (L : List (OpId P × A.Op)) (x : OpId P)
    (hx : x ∉ L.map Prod.fst) : linRespFrom A q L x = none := by
  have := linRespFrom_append_of_not_mem q L [] x hx
  simpa [linRespFrom] using this

lemma mem_of_linRespFrom {q : A.State} {L : List (OpId P × A.Op)} {x : OpId P} {r : A.Resp}
    (h : linRespFrom A q L x = some r) : x ∈ L.map Prod.fst := by
  by_contra hx
  rw [linRespFrom_eq_none q L x hx] at h
  cases h

lemma linRespFrom_split {q : A.State} {L : List (OpId P × A.Op)} {x : OpId P} {r : A.Resp}
    (h : linRespFrom A q L x = some r) :
    ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧ (A.δ (A.runOps q (L₁.map Prod.snd)) o).2 = r := by
  induction L generalizing q with
  | nil => simp [linRespFrom] at h
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [linRespFrom] at h
    split_ifs at h with hy
    · subst hy
      cases h
      exact ⟨[], L, o, rfl, rfl⟩
    · obtain ⟨L₁, L₂, o', h1, h2⟩ := ih h
      exact ⟨(y, o) :: L₁, L₂, o', by simp [h1], by simpa using h2⟩

/-- Inserting an operation that does not change the state at its position does not change
the responses of the other operations. -/
lemma linRespFrom_insert (q : A.State) (S₁ S₂ : List (OpId P × A.Op)) (y : OpId P) (o : A.Op)
    (hneu : (A.δ (A.runOps q (S₁.map Prod.snd)) o).1 = A.runOps q (S₁.map Prod.snd))
    (x : OpId P) (hxy : y ≠ x) :
    linRespFrom A q (S₁ ++ (y, o) :: S₂) x = linRespFrom A q (S₁ ++ S₂) x := by
  by_cases hx : x ∈ S₁.map Prod.fst
  · rw [linRespFrom_append_of_mem _ _ _ _ hx, linRespFrom_append_of_mem _ _ _ _ hx]
  · rw [linRespFrom_append_of_not_mem _ _ _ _ hx, linRespFrom_append_of_not_mem _ _ _ _ hx]
    simp only [linRespFrom, hxy, ite_false, hneu]

lemma linRespFrom_insert_self (q : A.State) (S₁ S₂ : List (OpId P × A.Op)) (y : OpId P)
    (o : A.Op) (hy : y ∉ S₁.map Prod.fst) :
    linRespFrom A q (S₁ ++ (y, o) :: S₂) y =
      some (A.δ (A.runOps q (S₁.map Prod.snd)) o).2 := by
  rw [linRespFrom_append_of_not_mem _ _ _ _ hy]
  simp [linRespFrom]

lemma linResp_append_of_mem (L M : List (OpId P × A.Op)) (x : OpId P)
    (hx : x ∈ L.map Prod.fst) : linResp A (L ++ M) x = linResp A L x :=
  linRespFrom_append_of_mem _ _ _ _ hx

lemma linResp_append_of_isSome {L : List (OpId P × A.Op)} {x : OpId P} {r : A.Resp}
    (h : linResp A L x = some r) (M : List (OpId P × A.Op)) : linResp A (L ++ M) x = some r := by
  rw [linResp_append_of_mem _ _ _ (mem_of_linRespFrom h)]; exact h

lemma linResp_push (L : List (OpId P × A.Op)) (x : OpId P) (o : A.Op)
    (hx : x ∉ L.map Prod.fst) : linResp A (L ++ [(x, o)]) x = some (A.δ (linState L) o).2 := by
  have := linRespFrom_insert_self A.init L [] x o hx
  simpa [linResp, linState] using this

lemma linResp_insert (S₁ S₂ : List (OpId P × A.Op)) (y : OpId P) (o : A.Op)
    (hneu : (A.δ (linState S₁) o).1 = linState S₁) (x : OpId P) (hxy : y ≠ x) :
    linResp A (S₁ ++ (y, o) :: S₂) x = linResp A (S₁ ++ S₂) x :=
  linRespFrom_insert _ _ _ _ _ hneu x hxy

lemma linResp_insert_self (S₁ S₂ : List (OpId P × A.Op)) (y : OpId P) (o : A.Op)
    (hy : y ∉ S₁.map Prod.fst) :
    linResp A (S₁ ++ (y, o) :: S₂) y = some (A.δ (linState S₁) o).2 :=
  linRespFrom_insert_self _ _ _ _ _ hy

lemma mem_of_linResp {L : List (OpId P × A.Op)} {x : OpId P} {r : A.Resp}
    (h : linResp A L x = some r) : x ∈ L.map Prod.fst := mem_of_linRespFrom h

lemma linResp_split {L : List (OpId P × A.Op)} {x : OpId P} {r : A.Resp}
    (h : linResp A L x = some r) :
    ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧ (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).2 = r :=
  linRespFrom_split h

/-! ### `linState` -/

lemma linState_push (L : List (OpId P × A.Op)) (x : OpId P) (o : A.Op) :
    linState (L ++ [(x, o)]) = (A.δ (linState L) o).1 := by
  simp [linState, ObjSpec.runOps_append]

lemma linState_insert (S₁ S₂ : List (OpId P × A.Op)) (y : OpId P) (o : A.Op)
    (hneu : (A.δ (linState S₁) o).1 = linState S₁) :
    linState (S₁ ++ (y, o) :: S₂) = linState (S₁ ++ S₂) (A := A) := by
  simp only [linState, map_append, map_cons, ObjSpec.runOps_append, ObjSpec.runOps_cons]
  rw [show A.runOps A.init (S₁.map Prod.snd) = linState S₁ from rfl, hneu]

/-! ### Retroactive insertion -/

-- CSLib candidate (copy of `IsLinearization.insert`, ScannableBinaryObjects)
/-- Retroactive linearization point: insert a pending operation `x` (which does not change the
state reached after `L₁`) between `L₁` and `L₂`, if nothing in `L₂` precedes `x`. -/
lemma isLin_insert {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)}
    (hL : IsLinearization α (L₁ ++ L₂)) {x : OpId P} {o : A.Op} (hx : opOf α x = some o)
    (hxL : x ∉ (L₁ ++ L₂).map Prod.fst) (hxc : ¬ Completed α x)
    (hro : (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).1 = A.runOps A.init (L₁.map Prod.snd))
    (h2 : ∀ y ∈ L₂, ¬ Precedes α y.1 x) : IsLinearization α (L₁ ++ (x, o) :: L₂) where
  nodup := by
    have := hL.nodup
    simp only [map_append, map_cons] at this hxL ⊢
    rw [nodup_middle, nodup_cons]
    exact ⟨hxL, this⟩
  op_eq y hy := by
    simp only [mem_append, mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hL.op_eq y (mem_append_left _ hy)
    · exact hx
    · exact hL.op_eq y (mem_append_right _ hy)
  complete a ha := by
    have := hL.complete a ha
    simp only [map_append, map_cons, mem_append, mem_cons] at this ⊢
    tauto
  realtime a b hab hb := by
    have hsub : (L₁ ++ L₂).map Prod.fst <+ (L₁ ++ (x, o) :: L₂).map Prod.fst := by
      simp only [map_append, map_cons]
      exact Sublist.append_left (sublist_cons_self _ _) _
    by_cases hbx : b = x
    · subst hbx
      have ha := hL.complete a hab.completed
      have ha1 : a ∈ L₁.map Prod.fst := by
        simp only [map_append, mem_append] at ha
        rcases ha with ha | ha
        · exact ha
        · obtain ⟨y, hy, rfl⟩ := mem_map.1 ha
          exact absurd hab (h2 y hy)
      rw [sublist_pair_iff]
      exact ⟨L₁.map Prod.fst, (L₂.map Prod.fst).cons b, by simp, ha1, by simp⟩
    · have hb' : b ∈ (L₁ ++ L₂).map Prod.fst := by
        simp only [map_append, map_cons, mem_append, mem_cons] at hb ⊢
        rcases hb with hb | hb | hb
        · exact Or.inl hb
        · exact absurd hb hbx
        · exact Or.inr hb
      exact (hL.realtime a b hab hb').trans hsub
  seq := by
    have hs := hL.seq
    rw [seqOK_append] at hs ⊢
    refine ⟨hs.1, ?_, ?_⟩
    · intro r hr
      exact absurd (completed_iff_respOf.2 (by rw [hr]; rfl)) hxc
    · rw [hro]; exact hs.2

-- CSLib candidate
/-- A split `L = S₁ ++ S₂` survives the insertion of `z` at another split `L = W₁ ++ W₂`:
`z` lands either in the right part, or in the left part right after `W₁`. -/
lemma split_insert' {X : Type} {S₁ S₂ W₁ W₂ : List X} (h : S₁ ++ S₂ = W₁ ++ W₂) (z : X) :
    ∃ S₁' S₂', W₁ ++ z :: W₂ = S₁' ++ S₂' ∧ (∀ y ∈ S₂', y ∈ S₂ ∨ y = z) ∧
      (S₁' = S₁ ∨ ∃ B, S₁ = W₁ ++ B ∧ S₁' = W₁ ++ z :: B) := by
  rcases append_eq_append_iff.1 h with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · refine ⟨S₁, a' ++ z :: W₂, by simp, ?_, Or.inl rfl⟩
    intro y hy; simp only [mem_append, mem_cons] at hy ⊢; tauto
  · exact ⟨W₁ ++ z :: c', S₂, by simp, fun y hy => Or.inl hy, Or.inr ⟨c', rfl, rfl⟩⟩

end Generic

end CryptoCons.Fig3
