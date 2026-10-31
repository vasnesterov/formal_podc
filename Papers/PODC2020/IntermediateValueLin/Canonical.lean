import Papers.PODC2020.IntermediateValueLin.Defs

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/ (IVL / skeleton linearizations)

/-!
# Canonical skeleton linearizations

The IVL proofs of Rinberg–Keidar (Lemma 1 for the concurrent CountMin sketch, Lemma 2 for the
batched counter) use two canonical linearizations of a history:

* `H₁`: every query is linearized at its invocation ("before all concurrent operations") and
  every update at its response;
* `H₂`: every update is linearized at its invocation and every query at its response ("after
  all concurrent operations").

Given a predicate `f : A.Op → Bool` ("linearize at the invocation"), `canon f α` lists the
instances of `α` in the order of their linearization points: an instance whose operation `o`
has `f o = true` at its invocation (pending ones included), an instance with `f o = false` at
its response (pending ones omitted). `H₁ = canon (! isUpdate)`, `H₂ = canon isUpdate`.

Main results:
* `canon_append`, `canon_concat`: `canon` is computed left to right.
* `canon_skel`: `canon f α` only depends on the skeleton `α?` (not on the response values).
* `isSkelLin_canon`: for a well-formed history, `canon f α` is a skeleton linearization.
* `tau_canon_of_inv`, `tau_canon_of_ret`: the response `τ_A` assigns to an instance, in terms
  of the prefix of the history before its linearization point.
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- The entries contributed by the label `ℓ` appended to the history `β`. -/
def canonEnt (f : A.Op → Bool) (β : List (Label P A)) : Label P A → List (OpId P × A.Op)
  | .inv p o => if f o then [((p, (opsOf β p).length), o)] else []
  | .ret p _ =>
    match opOf β (p, (respsOf β p).length) with
    | some o => if f o then [] else [((p, (respsOf β p).length), o)]
    | none => []
  | .tau _ => []

/-- Auxiliary: entries of the labels of `α`, appended to the history `pre`. -/
def canonGo (f : A.Op → Bool) : List (Label P A) → List (Label P A) → List (OpId P × A.Op)
  | _, [] => []
  | pre, ℓ :: α => canonEnt f pre ℓ ++ canonGo f (pre ++ [ℓ]) α

/-- The canonical linearization: instances with `f o` at their invocation, the others at their
response. -/
def canon (f : A.Op → Bool) (α : List (Label P A)) : List (OpId P × A.Op) := canonGo f [] α

lemma canonGo_append (f : A.Op → Bool) (pre α β : List (Label P A)) :
    canonGo f pre (α ++ β) = canonGo f pre α ++ canonGo f (pre ++ α) β := by
  induction α generalizing pre with
  | nil => simp [canonGo]
  | cons ℓ α ih => simp [canonGo, ih, List.append_assoc]

lemma canon_append (f : A.Op → Bool) (α β : List (Label P A)) :
    canon f (α ++ β) = canon f α ++ canonGo f α β := by
  simp [canon, canonGo_append]

lemma canon_concat (f : A.Op → Bool) (α : List (Label P A)) (ℓ : Label P A) :
    canon f (α ++ [ℓ]) = canon f α ++ canonEnt f α ℓ := by
  simp [canon_append, canonGo]

@[simp] lemma canon_nil (f : A.Op → Bool) : canon f ([] : List (Label P A)) = [] := rfl

/-! ### Dependence on the skeleton only -/

lemma canonEnt_skel (f : A.Op → Bool) (β : List (Label P A)) (ℓ : Label P A) :
    canonEnt (A := skelSpec A) f (skel β) ℓ.skel = canonEnt f β ℓ := by
  cases ℓ with
  | inv p o => simp [canonEnt, Label.skel]
  | ret p r =>
    simp only [Label.skel, canonEnt, respsOf_skel, List.length_map, opOf_skel]
    cases opOf β (p, (respsOf β p).length) <;> rfl
  | tau p => rfl

lemma canonGo_skel (f : A.Op → Bool) (pre α : List (Label P A)) :
    canonGo (A := skelSpec A) f (skel pre) (skel α) = canonGo f pre α := by
  induction α generalizing pre with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [skel_cons, canonGo, canonEnt_skel]
    rw [← ih, skel_append, skel_singleton]

/-- The canonical linearization depends only on the skeleton history: it is the same for all
histories with the same invocations and responses, whatever the response values. -/
theorem canon_skel (f : A.Op → Bool) (α : List (Label P A)) :
    canon (A := skelSpec A) f (skel α) = canon f α := canonGo_skel f [] α

/-! ### It is a skeleton linearization -/

/-- The invariant behind `isSkelLin_canon`. -/
structure CanonInv (f : A.Op → Bool) (α : List (Label P A)) : Prop where
  lin : IsSkelLin α (canon f α)
  late : ∀ y ∈ canon f α, f y.2 = false → Completed α y.1
  early : ∀ x o, opOf α x = some o → f o = true → x ∈ (canon f α).map Prod.fst

lemma isSkelLin_concat_iff {α : List (Label P A)} {ℓ : Label P A} {L : List (OpId P × A.Op)} :
    IsSkelLin (α ++ [ℓ]) L ↔ IsLinearization (skel α ++ [ℓ.skel]) L := by
  unfold IsSkelLin; rw [skel_append, skel_singleton]

lemma wellFormed_counts_last {α : List (Label P A)} {ℓ : Label P A}
    (h : WellFormed (α ++ [ℓ])) (p : P) :
    (ℓ.invOf p ≠ none → (opsOf α p).length = (respsOf α p).length) ∧
    (ℓ.retOf p ≠ none → (opsOf α p).length = (respsOf α p).length + 1) :=
  h α ℓ [] rfl p

lemma canonInv_concat {f : A.Op → Bool} {α : List (Label P A)} {ℓ : Label P A}
    (hwf : WellFormed (α ++ [ℓ])) (h : CanonInv f α) : CanonInv f (α ++ [ℓ]) := by
  have hmemop : ∀ y ∈ canon f α, opOf α y.1 = some y.2 := fun y hy => by
    simpa using h.lin.op_eq y hy
  suffices H : IsSkelLin (α ++ [ℓ]) (canon f α ++ canonEnt f α ℓ) ∧
      (∀ y ∈ canon f α ++ canonEnt f α ℓ, f y.2 = false → Completed (α ++ [ℓ]) y.1) ∧
      (∀ x o, opOf (α ++ [ℓ]) x = some o → f o = true →
        x ∈ (canon f α ++ canonEnt f α ℓ).map Prod.fst) by
    rw [← canon_concat] at H; exact ⟨H.1, H.2.1, H.2.2⟩
  cases ℓ with
  | tau p =>
    simp only [canonEnt, List.append_nil]
    refine ⟨?_, ?_, ?_⟩
    · exact isSkelLin_concat_iff.2 (h.lin.append_tau p)
    · intro y hy hf
      exact (completed_append_of_not_ret (by simp) _).2 (h.late y hy hf)
    · intro x o hx hf
      exact h.early x o (by simpa using hx) hf
  | inv p o =>
    have hidle : (opsOf α p).length = (respsOf α p).length :=
      (wellFormed_counts_last hwf p).1 (by simp)
    set x : OpId P := (p, (opsOf α p).length) with hx
    have hxnot : x ∉ (canon f α).map Prod.fst := fun hm => by
      have := h.lin.mem_invoked hm
      simp [Invoked, x] at this
    have hlin' : IsSkelLin (α ++ [.inv p o]) (canon f α) := by
      exact isSkelLin_concat_iff.2 (h.lin.append_inv p o)
    have hcompl : ∀ y, Completed (α ++ [.inv p o]) y ↔ Completed α y :=
      completed_append_of_not_ret (by simp)
    by_cases hf : f o = true
    · simp only [canonEnt, hf, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · refine hlin'.push ?_ hxnot ?_
        · simp [opOf_concat_inv]
        · rw [completed_skel, hcompl]
          simp [Completed, hidle]
      · intro y hy hfy
        rcases List.mem_append.1 hy with hy | hy
        · exact (hcompl _).2 (h.late y hy hfy)
        · simp only [List.mem_singleton] at hy; subst hy; simp [hf] at hfy
      · intro y o' hy hfo
        rw [opOf_concat_inv] at hy
        split_ifs at hy with hyx
        · subst hyx; simp
        · simp [h.early y o' hy hfo]
    · simp only [canonEnt, hf, Bool.false_eq_true, ite_false, List.append_nil]
      refine ⟨hlin', ?_, ?_⟩
      · intro y hy hfy; exact (hcompl _).2 (h.late y hy hfy)
      · intro y o' hy hfo
        rw [opOf_concat_inv] at hy
        split_ifs at hy with hyx
        · cases hy; exact absurd hfo hf
        · exact h.early y o' hy hfo
  | ret p r =>
    have hpend : (opsOf α p).length = (respsOf α p).length + 1 :=
      (wellFormed_counts_last hwf p).2 (by simp)
    set x : OpId P := (p, (respsOf α p).length) with hx
    have hinv : Invoked α x := by simp [Invoked, x, hpend]
    obtain ⟨o, ho⟩ : ∃ o, opOf α x = some o := by
      simp only [opOf, x]
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hxc : ¬ Completed α x := by simp [Completed, x]
    have hcompl : ∀ y, Completed (α ++ [.ret p r]) y ↔ Completed α y ∨ y = x :=
      fun y => completed_append_ret y
    have hops : ∀ y, opOf (α ++ [.ret p r]) y = opOf α y := fun y => opOf_append_ret α p r y
    by_cases hf : f o = true
    · simp only [canonEnt, ← hx, ho, hf, ite_true, List.append_nil]
      refine ⟨?_, ?_, ?_⟩
      · have hm : x ∈ (canon f α).map Prod.fst := h.early x o ho hf
        have := h.lin.append_ret_of_respIn (p := p) (r := ())
          (by
            simp only [respsOf_skel, List.length_map]
            obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1
              ((ObjSpec.respIn_isSome_iff (A := skelSpec A) (q := ())).2 hm)
            simpa [x] using hu)
        exact isSkelLin_concat_iff.2 this
      · intro y hy hfy; exact (hcompl _).2 (Or.inl (h.late y hy hfy))
      · intro y o' hy hfo; rw [hops] at hy; exact h.early y o' hy hfo
    · simp only [canonEnt, ← hx, ho, hf, Bool.false_eq_true, ite_false]
      have hxnot : x ∉ (canon f α).map Prod.fst := by
        intro hm
        obtain ⟨⟨y, o'⟩, hy, rfl⟩ := List.mem_map.1 hm
        have := hmemop _ hy
        rw [ho] at this; cases this
        exact hxc (h.late _ hy (by simpa using hf))
      refine ⟨?_, ?_, ?_⟩
      · have hpush : IsSkelLin α (canon f α ++ [(x, o)]) :=
          h.lin.push (by simpa using ho) hxnot (by simpa using hxc)
        have := hpush.append_ret (p := p) (r := ()) (canon (A := A) f α) [] o
          (by simp [x]) rfl
        exact isSkelLin_concat_iff.2 this
      · intro y hy hfy
        rcases List.mem_append.1 hy with hy | hy
        · exact (hcompl _).2 (Or.inl (h.late y hy hfy))
        · simp only [List.mem_singleton] at hy; subst hy
          exact (hcompl _).2 (Or.inr rfl)
      · intro y o' hy hfo
        rw [hops] at hy
        exact List.map_append .. ▸ List.mem_append_left _ (h.early y o' hy hfo)

lemma canonInv_of_wellFormed (f : A.Op → Bool) {α : List (Label P A)} (hwf : WellFormed α) :
    CanonInv f α := by
  induction α using List.reverseRecOn with
  | nil =>
    refine ⟨?_, by simp, ?_⟩
    · exact isLinearization_nil
    · intro x o hx; simp [opOf] at hx
  | append_singleton α ℓ ih => exact canonInv_concat hwf (ih hwf.of_append)

/-- For a well-formed history, the canonical list `canon f α` is a linearization of the skeleton
history `α?`. -/
theorem isSkelLin_canon (f : A.Op → Bool) {α : List (Label P A)} (hwf : WellFormed α) :
    IsSkelLin α (canon f α) :=
  (canonInv_of_wellFormed f hwf).lin

/-! ### Responses assigned by the canonical linearizations -/

/-- An instance linearized at its invocation: if `α = β ++ inv p o :: γ` with `f o`, then
`τ_S(canon f α)` gives the instance `(p, |ops_β(p)|)` the response of `o` in the state reached by
`canon f β`. -/
theorem tau_canon_of_inv (S : QSpec A.Op A.Resp) (f : A.Op → Bool) {β γ : List (Label P A)} {p : P} {o : A.Op}
    (hwf : WellFormed (β ++ .inv p o :: γ)) (hf : f o = true) :
    tau S (canon f (β ++ .inv p o :: γ)) (p, (opsOf β p).length) =
      some (S.δ (S.obj.runOps S.init ((canon f β).map Prod.snd)) o).2 := by
  have hsplit : canon f (β ++ .inv p o :: γ) =
      canon f β ++ ((p, (opsOf β p).length), o) :: canonGo f (β ++ [.inv p o]) γ := by
    rw [show β ++ .inv p o :: γ = (β ++ [.inv p o]) ++ γ by simp, canon_append, canon_concat]
    simp [canonEnt, hf]
  rw [tau, hsplit]
  refine ObjSpec.respIn_of_split ?_ rfl
  rw [← hsplit]
  exact (isSkelLin_canon f hwf).nodup

/-- An instance linearized at its response: if `α = β ++ ret p r :: γ`, the returning instance
`x = (p, |resps_β(p)|)` has operation `o` and `f o = false`, then `τ_S(canon f α)` gives `x` the
response of `o` in the state reached by `canon f β`. -/
theorem tau_canon_of_ret (S : QSpec A.Op A.Resp) (f : A.Op → Bool) {β γ : List (Label P A)} {p : P} {r : A.Resp}
    {o : A.Op} (hwf : WellFormed (β ++ .ret p r :: γ))
    (ho : opOf β (p, (respsOf β p).length) = some o) (hf : f o = false) :
    tau S (canon f (β ++ .ret p r :: γ)) (p, (respsOf β p).length) =
      some (S.δ (S.obj.runOps S.init ((canon f β).map Prod.snd)) o).2 := by
  have hsplit : canon f (β ++ .ret p r :: γ) =
      canon f β ++ ((p, (respsOf β p).length), o) :: canonGo f (β ++ [.ret p r]) γ := by
    rw [show β ++ .ret p r :: γ = (β ++ [.ret p r]) ++ γ by simp, canon_append, canon_concat]
    simp [canonEnt, ho, hf]
  rw [tau, hsplit]
  refine ObjSpec.respIn_of_split ?_ rfl
  rw [← hsplit]
  exact (isSkelLin_canon f hwf).nodup

end Podc.IntermediateValueLin
