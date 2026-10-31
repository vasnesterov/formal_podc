import Papers.PODC2015.HelpFreeWaitFree.Defs

/-!
# Linearization points inside the operation imply help-freedom (Claim 4.8.1 of [CPT15])

[CPT15]: K. Censor-Hillel, E. Petrank, S. Timnat. *Help!* PODC 2015 (full version: Chapter 4 of
S. Timnat's PhD thesis).

Section 4.8 of [CPT15]: "For any type, an obstruction-free implementation in which the
linearization point of every operation can be specified as a step in the execution of the same
operation is help-free." The linearization function `f` is "derived from the linearization
points": operations are ordered by the execution order of their linearization points.

We formalize "the linearization function is derived from linearization points that are steps of
the operation itself" by a function `lin` such that, for every execution `h ++ [γ]`, the step `γ`
either leaves `lin` unchanged or appends exactly one entry, whose instance is the current
operation of the process taking `γ` (`LinPointFun`). The progress assumption of the paper
(obstruction-freedom) is used, as in the paper's proof, to let the owner of an operation run
solo until that operation is linearized; we additionally assume that every process may invoke
some operation (otherwise the owner cannot reach a future operation instance).

* `LinPointFun I lin` — the shape of `lin` described above.
* `claim_4_8_1` — **Claim 4.8.1**: if `γ` makes `a` decided before `b`, then `γ` is the
  linearization point of `a`: it is a step of `a` (`curOp h γ.proc = a`) and it appends `a` to
  the linearization.
* `helpFreeWith_of_linPointFun`, `helpFree_of_linPointFun` — such an implementation is help-free.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

/-! ### Positions in an extended sequential history -/

section Pos

variable [DecidableEq P]

lemma pos_append_of_mem {S : List (OpId P × A.Op)} {a : OpId P} (ha : a ∈ S.map Prod.fst)
    (t : List (OpId P × A.Op)) : pos (S ++ t) a = pos S a := by
  simp only [pos, List.map_append]; exact List.idxOf_append_of_mem ha

lemma length_le_pos_append {S : List (OpId P × A.Op)} {a : OpId P} (ha : a ∉ S.map Prod.fst)
    (t : List (OpId P × A.Op)) : S.length ≤ pos (S ++ t) a := by
  simp only [pos, List.map_append]
  rw [List.idxOf_append_of_notMem ha]; simp

/-- Precedence in a sequential history is preserved when the history is extended. -/
lemma Prec.append {S : List (OpId P × A.Op)} {a b : OpId P} (h : Prec S a b)
    (t : List (OpId P × A.Op)) : Prec (S ++ t) a b := by
  rw [prec_iff_pos_lt] at *
  have ha : a ∈ S.map Prod.fst := pos_lt_length_iff.1 (lt_of_lt_of_le h (pos_le_length S b))
  rw [pos_append_of_mem ha]
  by_cases hb : b ∈ S.map Prod.fst
  · rwa [pos_append_of_mem hb]
  · exact lt_of_lt_of_le (pos_lt_length_iff.2 ha) (length_le_pos_append hb t)

/-- If `a` occurs in `S` and does not come after `b`, this persists in extensions of `S`. -/
lemma pos_le_pos_append {S : List (OpId P × A.Op)} {a b : OpId P} (ha : a ∈ S.map Prod.fst)
    (h : pos S a ≤ pos S b) (t : List (OpId P × A.Op)) : pos (S ++ t) a ≤ pos (S ++ t) b := by
  rw [pos_append_of_mem ha]
  by_cases hb : b ∈ S.map Prod.fst
  · rwa [pos_append_of_mem hb]
  · exact le_trans (pos_lt_length_iff.2 ha).le (length_le_pos_append hb t)

end Pos

/-! ### Linearization functions derived from linearization points -/

variable [DecidableEq P] {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
variable (I : Impl A B P L)

/-- `lin` is *derived from linearization points that are steps of the operations themselves*:
along every execution, a single step `γ` either leaves `lin` unchanged, or appends one entry,
whose instance is the operation `curOp h γ.proc` that `γ` belongs to. -/
def LinPointFun (lin : List (Label P A) → List (OpId P × A.Op)) : Prop :=
  ∀ h γ, I.Valid (h ++ [γ]) →
    lin (h ++ [γ]) = lin h ∨ ∃ o, lin (h ++ [γ]) = lin h ++ [(curOp h γ.proc, o)]

variable {I}

/-- Along an extension `h ++ s`, a `LinPointFun` only appends entries, each the operation of
the process taking some step of `s`. -/
lemma LinPointFun.exists_append {lin : List (Label P A) → List (OpId P × A.Op)}
    (hl : LinPointFun I lin) (h : List (Label P A)) :
    ∀ s, I.Valid (h ++ s) → ∃ t, lin (h ++ s) = lin h ++ t ∧ ∀ y ∈ t, ∃ γ ∈ s, y.1.1 = γ.proc := by
  intro s
  induction s using List.reverseRecOn with
  | nil => intro _; exact ⟨[], by simp, by simp⟩
  | append_singleton s γ ih =>
    intro hv
    have hv' : I.Valid (h ++ s) := I.valid_of_prefix hv ⟨[γ], by simp⟩
    obtain ⟨t, ht, hts⟩ := ih hv'
    rcases hl (h ++ s) γ (by simpa using hv) with he | ⟨o, he⟩
    · refine ⟨t, by rw [← List.append_assoc, he, ht], fun y hy => ?_⟩
      obtain ⟨γ', hγ', e⟩ := hts y hy
      exact ⟨γ', by simp [hγ'], e⟩
    · refine ⟨t ++ [(curOp (h ++ s) γ.proc, o)], by
        rw [← List.append_assoc, he, ht, List.append_assoc], fun y hy => ?_⟩
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨γ', hγ', e⟩ := hts y hy
        exact ⟨γ', by simp [hγ'], e⟩
      · simp only [List.mem_singleton] at hy; subst hy
        exact ⟨γ, by simp, rfl⟩

/-! ### Running the owner of an operation solo until it completes -/

/-- Under obstruction-freedom, if `q` may invoke some operation, then from any execution `α`
the process `q` alone can run until it has completed exactly `n + 1` operations (for any `n`
at least the number of its responses so far): it finishes its pending operation and then
invokes and completes further operations. -/
lemma exists_solo_complete (hof : I.ObstructionFree) {q : P} {o : A.Op} (ho : I.allowed q o)
    {α : List (Label P A)} (hα : I.Valid α) {n : ℕ} (hn : (respsOf α q).length ≤ n) :
    ∃ s, (∀ ℓ ∈ s, ℓ.proc = q) ∧ I.Valid (α ++ s) ∧
      (respsOf (α ++ s) q).length = n + 1 ∧ (opsOf (α ++ s) q).length = n + 1 := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨γ, F, hγp, hγo, hγr, hFq, -⟩ :=
    I.exists_finish (E := fun _ => True) (hof.obstructionFreeOn _) (fun _ _ _ _ => trivial)
      [q] hC trivial
  have hrunγ : I.run (α ++ γ) = some F := by rw [I.run_append_of_eq hC, hγr]
  have hFq' : F.pend q = none := hFq q (by simp)
  have hops_le : (opsOf α q).length ≤ n + 1 := by
    have := I.run_counts hC q; rcases this with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hidle := I.run_idle_counts hrunγ hFq'
  set m := (opsOf (α ++ γ) q).length with hm
  have hm' : m = (opsOf α q).length := by simp [hm, opsOf_append, hγo q]
  set k := n + 1 - m
  obtain ⟨F', h1, -, h3, h4, h5⟩ :=
    I.soloOps_spec hof q (List.replicate k o) (fun o' ho' => by
      rw [List.eq_of_mem_replicate ho']; exact ho) hrunγ hFq'
  refine ⟨γ ++ I.soloOps q F (List.replicate k o), fun ℓ hℓ => ?_, ⟨F', ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.1 hℓ with hℓ | hℓ
    · simpa using hγp ℓ hℓ
    · exact h3 ℓ hℓ
  · rw [← List.append_assoc, I.run_append_of_eq hrunγ, h1]
  · rw [← List.append_assoc, respsOf_append, List.length_append, h5, List.length_replicate,
      ← hidle]
    omega
  · rw [← List.append_assoc, opsOf_append, List.length_append, h4, List.length_replicate]
    omega

/-! ### Claim 4.8.1 -/

/-- For instances of the same process, an earlier one is always decided before a later one. -/
lemma decidedBefore_of_proc_eq {f : List (Label P A) → List (OpId P × A.Op)} (hf : I.IsLinFun f)
    (h : List (Label P A)) {p : P} {i j : ℕ} (hij : i < j) :
    DecidedBefore I f h (p, i) (p, j) := by
  rw [decidedBefore_iff]
  intro s hs
  by_cases hb : (p, j) ∈ (f (h ++ s)).map Prod.fst
  · have hinv := invoked_of_mem_lin (hf _ hs) hb
    exact (pos_lt_of_precedes (hf _ hs) (hs.wellFormed.precedes_of_lt hij hinv) hb).le
  · rw [pos_eq_length_iff.2 hb]; exact pos_le_length _ _

variable {lin : List (Label P A) → List (OpId P × A.Op)}

/-- **Claim 4.8.1 of [CPT15].** Let `I` be an obstruction-free implementation in which every
process may invoke some operation, and let `lin` be a linearization function derived from
linearization points that are steps of the operations themselves (`LinPointFun`). If a single
step `γ` after `h` makes `a` decided before `b` (and `a` was not decided before `b` in `h`), then
`γ` is the linearization point of `a`: `γ` is a step of `a` (`curOp h γ.proc = a`) and it
appends `a` to the linearization. -/
theorem claim_4_8_1 (hlin : I.IsLinFun lin) (hlp : LinPointFun I lin)
    (hof : I.ObstructionFree) (hall : ∀ p, ∃ o, I.allowed p o)
    {h : List (Label P A)} {γ : Label P A} {a b : OpId P} (hv : I.Valid (h ++ [γ]))
    (hd : DecidedBefore I lin (h ++ [γ]) a b) (hnd : ¬ DecidedBefore I lin h a b) :
    curOp h γ.proc = a ∧ ∃ o, lin (h ++ [γ]) = lin h ++ [(a, o)] := by
  have hvh : I.Valid h := hv.of_append
  have hab : a ≠ b := by rintro rfl; exact hnd (decidedBefore_refl h a)
  -- Step 1 (the paper's first observation): `a` is not linearized in `h`.
  have hah : a ∉ (lin h).map Prod.fst := by
    intro ha
    by_cases hp : Prec (lin h) b a
    · obtain ⟨t, ht, -⟩ := hlp.exists_append h [γ] hv
      exact hd [] (by simpa using hv) (by rw [List.append_nil, ht]; exact hp.append t)
    · apply hnd
      rw [decidedBefore_iff]
      intro s hs
      obtain ⟨t, ht, -⟩ := hlp.exists_append h s hs
      rw [ht]
      exact pos_le_pos_append ha (not_prec_iff.1 hp) t
  -- If `γ` appends `a`, we are done; otherwise `a` is not linearized after `γ` either.
  by_cases hγ : ∃ o, lin (h ++ [γ]) = lin h ++ [(curOp h γ.proc, o)] ∧ curOp h γ.proc = a
  · obtain ⟨o, ho, hc⟩ := hγ
    exact ⟨hc, o, hc ▸ ho⟩
  exfalso
  set α := h ++ [γ] with hαdef
  have haα : a ∉ (lin α).map Prod.fst := by
    rcases hlp h γ hv with he | ⟨o, he⟩
    · rwa [he]
    · rw [he]; simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton, not_or]
      exact ⟨hah, fun e => hγ ⟨o, he, e.symm⟩⟩
  -- Step 2 (the paper's second observation): the owner of `b` runs solo until `b` is
  -- linearized, before `a`.
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  -- an earlier operation of the same process is always decided before a later one
  by_cases hsame : a1 = b1 ∧ a2 < b2
  · obtain ⟨rfl, hlt⟩ := hsame
    exact hnd (decidedBefore_of_proc_eq hlin h hlt)
  -- `b` linearized while `a` is not contradicts `hd`
  have key : ∀ s, I.Valid (α ++ s) → (b1, b2) ∈ (lin (α ++ s)).map Prod.fst →
      (a1, a2) ∉ (lin (α ++ s)).map Prod.fst → False := fun s hs hb ha =>
    hd s hs ⟨hb, Or.inl ha⟩
  by_cases hbc : Completed α (b1, b2)
  · exact key [] (by simpa using hv) (by simpa using (hlin α hv).complete _ hbc)
      (by simpa using haα)
  · obtain ⟨o, ho⟩ := hall b1
    have hn : (respsOf α b1).length ≤ b2 := by simpa [Completed] using hbc
    obtain ⟨s, hsp, hs, hsr, hso⟩ := exists_solo_complete hof ho hv hn
    have hbs : Completed (α ++ s) (b1, b2) := by
      show b2 < (respsOf (α ++ s) b1).length; omega
    refine key s hs ((hlin _ hs).complete _ hbs) ?_
    by_cases h1 : a1 = b1
    · subst h1
      have hlt : b2 < a2 := by
        rcases lt_trichotomy a2 b2 with h' | h' | h'
        · exact absurd ⟨rfl, h'⟩ hsame
        · exact absurd (by rw [h']) hab
        · exact h'
      intro hm
      have := invoked_of_mem_lin (hlin _ hs) hm
      simp only [Invoked, hso] at this; omega
    · obtain ⟨t, ht, hts⟩ := hlp.exists_append α s hs
      rw [ht]
      simp only [List.map_append, List.mem_append, not_or]
      refine ⟨haα, fun hm => ?_⟩
      obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
      obtain ⟨γ', hγ', e⟩ := hts y hy
      rw [hsp γ' hγ', hy1] at e
      exact h1 e

/-- **Claim 4.8.1 of [CPT15]**, consequence: a linearization function derived from
linearization points inside the operations witnesses help-freedom (for obstruction-free
implementations in which every process may invoke some operation). -/
theorem helpFreeWith_of_linPointFun (hlin : I.IsLinFun lin) (hlp : LinPointFun I lin)
    (hof : I.ObstructionFree) (hall : ∀ p, ∃ o, I.allowed p o) : HelpFreeWith I lin :=
  fun _ _ _ _ hv hd hnd => (claim_4_8_1 hlin hlp hof hall hv hd hnd).1

/-- **Section 4.8 of [CPT15]**: "an obstruction-free implementation in which the linearization
point of every operation can be specified as a step in the execution of the same operation is
help-free". -/
theorem helpFree_of_linPointFun (hlin : I.IsLinFun lin) (hlp : LinPointFun I lin)
    (hof : I.ObstructionFree) (hall : ∀ p, ∃ o, I.allowed p o) : HelpFree I :=
  ⟨lin, hlin, helpFreeWith_of_linPointFun hlin hlp hof hall⟩

end Podc.HelpFreeWaitFree
