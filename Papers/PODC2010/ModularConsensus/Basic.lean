import Cslib.Computability.Distributed.SharedMemory.Task
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Basic

/-!
# Deciding objects and their composition (Section 3 of Aspnes, PODC 2010)

J. Aspnes, *A modular approach to shared-memory consensus, with applications to the
probabilistic-write model*, PODC 2010 (full version of May 14, 2011).

A *deciding object* is a one-shot object whose inputs are values `v : V` and whose outputs are
pairs `(d, v)` with a *decision bit* `d ∈ {adopt, commit}`. The properties of Section 3 only
mention the inputs and outputs of an execution, so we describe an object by the set of
input/output pairs its executions can produce:

* `inp : P → Option V` — `some v` iff `p` invoked the object with input `v`;
* `out : P → Option (Decision × V)` — `some (d, v)` iff `p` returned `(d, v)`.

Executions may be partial (processes may crash or not yet have returned). This is exactly the
shape of CSLib's task relation `Task.Δ` (`Cslib.SharedMemory.Task`), so the predicates below are
also used as task specifications for concrete implementations (`adoptCommitTask`).

## Main definitions

* `Decision`, `Validity`, `Coherence`, `Convergence`, `Agreement`;
* `DObj P V`: a deciding object (the input/output pairs of its executions);
* `DObj.seq X Y` — the composition `(X; Y)` of Procedure Composition;
* `DObj.IsWeakConsensus`, `DObj.IsAdoptCommit`.

## Main results

* `DObj.validity_seq` — **Lemma 1**: validity is preserved by composition;
* `DObj.coherence_seq` — **Lemma 3**: `X` coherent, `Y` valid and coherent ⇒ `(X; Y)` coherent;
* `DObj.isWeakConsensus_seq` — **Theorem 4** (safety part; termination, Lemma 2, is
  `Cslib.SharedMemory.Impl.seqComp_waitFree`, `SeqCompose.lean`);
* `DObj.validity_seq_converse_false` — the remark after Lemma 1 (the converse fails);
* `DObj.coherence_seq_needs_validity` — the validity hypothesis of Lemma 3 is needed.
-/

namespace Podc.ModularConsensus

/-- The decision bit of a deciding object. -/
inductive Decision where
  | adopt
  | commit
  deriving DecidableEq, Inhabited, Repr

variable {P V : Type}

/-- **Validity.** Every output value equals some process's input. -/
def Validity (inp : P → Option V) (out : P → Option (Decision × V)) : Prop :=
  ∀ p d v, out p = some (d, v) → ∃ q, inp q = some v

/-- **Coherence.** If any process outputs `(commit, v)`, then no process outputs `(d, v')` with
`v' ≠ v`. -/
def Coherence (out : P → Option (Decision × V)) : Prop :=
  ∀ p q v d w, out p = some (.commit, v) → out q = some (d, w) → w = v

/-- **Convergence.** If all inputs are equal to `v`, all outputs are `(commit, v)`. -/
def Convergence (inp : P → Option V) (out : P → Option (Decision × V)) : Prop :=
  ∀ v, (∀ p x, inp p = some x → x = v) → ∀ p d w, out p = some (d, w) → d = .commit ∧ w = v

/-- **Agreement** (of a deciding object): all output values are equal. -/
def Agreement (out : P → Option (Decision × V)) : Prop :=
  ∀ p q d e v w, out p = some (d, v) → out q = some (e, w) → v = w

/-- A deciding object, described by the input/output pairs of its (possibly partial)
executions. -/
def DObj (P V : Type) := (P → Option V) → (P → Option (Decision × V)) → Prop

namespace DObj

/-- The object satisfies validity in all its executions. -/
def Valid (X : DObj P V) : Prop := ∀ inp out, X inp out → Validity inp out

/-- The object satisfies coherence in all its executions. -/
def Coherent (X : DObj P V) : Prop := ∀ inp out, X inp out → Coherence out

/-- The object satisfies convergence in all its executions. -/
def Convergent (X : DObj P V) : Prop := ∀ inp out, X inp out → Convergence inp out

/-- The safety part of a weak consensus object (validity and coherence); termination is a
property of implementations (`Cslib.SharedMemory.Impl.WaitFree`, see `SeqCompose.lean`). -/
def IsWeakConsensus (X : DObj P V) : Prop := X.Valid ∧ X.Coherent

/-- The safety part of an adopt-commit object: validity, coherence and convergence. -/
def IsAdoptCommit (X : DObj P V) : Prop := X.Valid ∧ X.Coherent ∧ X.Convergent

/-- The output of the composition for a process, given its outputs from `X` and `Y`: a commit
from `X` is returned immediately, otherwise the output from `Y` (if any). -/
def seqOut (oX oY : Option (Decision × V)) : Option (Decision × V) :=
  match oX with
  | some (.commit, v) => some (.commit, v)
  | _ => oY

/-- **Procedure Composition.** `(X; Y)`: run `X`; on `(commit, v)` return it, on `(adopt, v)`
invoke `Y` with input `v` and return its output. An execution of `(X; Y)` consists of an
execution of `X` (same inputs) and an execution of `Y` whose participants are processes that
adopted from `X`, with the adopted value as input (a process that adopted from `X` may not have
invoked `Y` yet, or crash in between); -/
def seq (X Y : DObj P V) : DObj P V := fun inp out =>
  ∃ outX inpY outY, X inp outX ∧ Y inpY outY ∧
    (∀ p v, inpY p = some v → outX p = some (.adopt, v)) ∧
    (∀ p, out p = seqOut (outX p) (outY p))

@[inherit_doc] scoped infixl:65 " ⨾ " => DObj.seq

lemma seqOut_eq_some {oX oY : Option (Decision × V)} {d : Decision} {v : V}
    (h : seqOut oX oY = some (d, v)) :
    (oX = some (.commit, v) ∧ d = .commit) ∨ ((∀ w, oX ≠ some (.commit, w)) ∧ oY = some (d, v)) := by
  unfold seqOut at h
  rcases oX with _ | ⟨_ | _, w⟩
  · exact Or.inr ⟨by simp, h⟩
  · exact Or.inr ⟨by simp, h⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩

/-- **Lemma 1.** Validity is preserved by composition. -/
theorem validity_seq {X Y : DObj P V} (hX : X.Valid) (hY : Y.Valid) : (X ⨾ Y).Valid := by
  rintro inp out ⟨outX, inpY, outY, hx, hy, hlink, hout⟩ p d v hp
  rw [hout] at hp
  rcases seqOut_eq_some hp with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hX _ _ hx p _ _ h1
  · obtain ⟨q, hq⟩ := hY _ _ hy p d v h2
    exact hX _ _ hx q _ _ (hlink q v hq)

/-- **Lemma 3.** If `X` satisfies coherence and `Y` satisfies validity and coherence, then
`(X; Y)` satisfies coherence. -/
theorem coherence_seq {X Y : DObj P V} (hX : X.Coherent) (hYv : Y.Valid) (hYc : Y.Coherent) :
    (X ⨾ Y).Coherent := by
  rintro inp out ⟨outX, inpY, outY, hx, hy, hlink, hout⟩
  -- Case 1 of the paper: some process commits in `X`; then every output has its value.
  have case1 : ∀ p u, outX p = some (.commit, u) → ∀ q d w, out q = some (d, w) → w = u := by
    intro p u hp q d w hq
    rw [hout] at hq
    rcases seqOut_eq_some hq with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hX _ _ hx p q u _ w hp h1
    · obtain ⟨q', hq'⟩ := hYv _ _ hy q d w h2
      exact hX _ _ hx p q' u _ w hp (hlink q' w hq')
  intro p q v d w hp hq
  rw [hout] at hp
  rcases seqOut_eq_some hp with ⟨h1, -⟩ | ⟨-, hpY⟩
  · exact case1 p v h1 q d w hq
  · -- `p` committed in `Y`.
    have hq' := hq
    rw [hout] at hq'
    rcases seqOut_eq_some hq' with ⟨h1, -⟩ | ⟨-, hqY⟩
    · -- `q` committed in `X` (Case 1 applied to `q`).
      have hv := case1 q w h1 p .commit v (by rw [hout]; exact hp)
      exact hv.symm
    · -- Case 2: both outputs come from `Y`.
      exact hYc _ _ hy p q v d w hpY hqY

/-- **Theorem 4** (safety part). The property of being a weak consensus object (validity and
coherence) is preserved by composition. Termination (Lemma 2) is a property of the
implementations, see `Cslib.SharedMemory.Impl.seqComp_waitFree` (`SeqCompose.lean`). -/
theorem isWeakConsensus_seq {X Y : DObj P V} (hX : X.IsWeakConsensus) (hY : Y.IsWeakConsensus) :
    (X ⨾ Y).IsWeakConsensus :=
  ⟨validity_seq hX.1 hY.1, coherence_seq hX.2 hY.1 hY.2⟩

/-- Only processes that invoked the object get an output from it. -/
def WellFormed (X : DObj P V) : Prop := ∀ inp out, X inp out → ∀ p, out p ≠ none → inp p ≠ none

lemma seqOut_assoc (a b c : Option (Decision × V)) :
    seqOut (seqOut a b) c = seqOut a (seqOut b c) := by
  rcases a with _ | ⟨_ | _, w⟩ <;> rfl

/-- Composition is associative (on input/output behaviours): `((X; Y); Z) = (X; (Y; Z))`, for
a well-formed middle object `Y`. -/
theorem seq_assoc (X Y Z : DObj P V) (hY : Y.WellFormed) : ((X ⨾ Y) ⨾ Z) = (X ⨾ (Y ⨾ Z)) := by
  funext inp out
  apply propext
  constructor
  · rintro ⟨oXY, iZ, oZ, ⟨oX, iY, oY, hx, hy, hlXY, hoXY⟩, hz, hlZ, ho⟩
    refine ⟨oX, iY, fun p => seqOut (oY p) (oZ p), hx, ⟨oY, iZ, oZ, hy, hz, ?_, fun _ => rfl⟩,
      hlXY, ?_⟩
    · intro p v hp
      have := hlZ p v hp
      rw [hoXY] at this
      rcases seqOut_eq_some this with ⟨-, h⟩ | ⟨-, h⟩
      · cases h
      · exact h
    · intro p
      rw [ho, hoXY, seqOut_assoc]
  · rintro ⟨oX, iY, oYZ, hx, ⟨oY, iZ, oZ, hy, hz, hlYZ, hoYZ⟩, hlX, ho⟩
    refine ⟨fun p => seqOut (oX p) (oY p), iZ, oZ, ⟨oX, iY, oY, hx, hy, hlX, fun _ => rfl⟩, hz,
      ?_, ?_⟩
    · intro p v hp
      have h1 := hlYZ p v hp
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 (hY _ _ hy p (by simp [h1]))
      have h2 := hlX p u hu
      simp [seqOut, h2, h1]
    · intro p
      rw [ho, hoYZ, seqOut_assoc]

/-! ### Remarks after Lemmas 1 and 3 -/

/-- The scrambling object over `Bool`: every process adopts the negation of its input. -/
def scramble : DObj P Bool := fun inp out => ∀ p, out p = (inp p).map fun v => (.adopt, !v)

/-- Remark after Lemma 1: the converse of Lemma 1 fails. `(scramble; scramble)` is valid (it is
the identity with decision `adopt`), but `scramble` is not. -/
theorem validity_seq_converse_false [Nonempty P] :
    (scramble (P := P) ⨾ scramble).Valid ∧ ¬ (scramble (P := P)).Valid := by
  constructor
  · rintro inp out ⟨oX, iY, oY, hx, hy, hl, ho⟩ p d v hp
    rw [ho, hy p] at hp
    rcases hX : oX p with _ | ⟨_ | _, w⟩ <;> rw [hX] at hp
    · rcases hi : iY p with _ | u <;> simp [seqOut, hi] at hp
      have := hl p u hi
      rw [hx p] at this
      rcases hip : inp p with _ | z <;> simp [hip] at this
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨p, by rw [hip, this]; simp⟩
    · rcases hi : iY p with _ | u <;> simp [seqOut, hi] at hp
      have := hl p u hi
      rw [hx p] at this
      rcases hip : inp p with _ | z <;> simp [hip] at this
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨p, by rw [hip, this]; simp⟩
    · rw [hx p] at hX
      rcases hip : inp p with _ | z <;> simp [hip] at hX
  · intro h
    obtain ⟨p⟩ := ‹Nonempty P›
    obtain ⟨q, hq⟩ := h (fun _ => some true) (fun _ => some (.adopt, false)) (fun _ => rfl) p
      .adopt false rfl
    simp at hq

/-- Remark on Lemma 3: the validity hypothesis on `Y` is needed. With two processes, `X`
commits `true` for process `0` and adopts `true` for process `1` (coherent), `Y` always adopts
`false` (coherent, not valid); then `(X; Y)` is not coherent. -/
theorem coherence_seq_needs_validity :
    ∃ X Y : DObj (Fin 2) Bool, X.Coherent ∧ Y.Coherent ∧ ¬ (X ⨾ Y).Coherent := by
  let oX : Fin 2 → Option (Decision × Bool) := fun p => if p = 0 then some (.commit, true)
    else some (.adopt, true)
  refine ⟨fun _ out => out = oX, fun _ out => ∀ p, out p = some (.adopt, false), ?_, ?_, ?_⟩
  · rintro inp out rfl p q v d w hp hq
    fin_cases p <;> fin_cases q <;> simp_all [oX]
  · intro inp out h p q v d w hp _
    rw [h p] at hp; cases hp
  · intro h
    have := h (fun _ => some true) (fun p => if p = 0 then some (.commit, true)
      else some (.adopt, false))
      ⟨oX, fun p => if p = 0 then none else some true, fun _ => some (.adopt, false), rfl,
        fun _ => rfl, ?_, ?_⟩ 0 1 true .adopt false (by simp) (by simp)
    · exact absurd this (by simp)
    · intro p v hp
      fin_cases p <;> simp_all [oX]
    · intro p
      fin_cases p <;> simp [oX, seqOut]

end DObj

/-- The adopt-commit task for processes `P` and values `V` (as a CSLib task): validity,
coherence and convergence of the inputs and outputs of every (partial) one-shot execution. -/
abbrev adoptCommitTask (P V : Type) : Cslib.SharedMemory.Task P where
  In := V
  Out := Decision × V
  Δ inp out := Validity inp out ∧ Coherence out ∧ Convergence inp out

end Podc.ModularConsensus
