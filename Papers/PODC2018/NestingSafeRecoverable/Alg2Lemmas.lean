import Papers.PODC2018.NestingSafeRecoverable.Alg2Defs

/-!
# Algorithm 2 of [ABH18]: the invariant

Ghost state of the correctness proof of Algorithm 2:

* `W : List (Cnt P V)`: the sequence of all contents `C` ever had (initially `[<null,null>]`; a
  successful `cas` appends its new content). Contents are never repeated (`W.Nodup`): this is the
  paper's "the content of `C` is unique".
* `L`: a linearization of the crash-free projection `N(H)` of the history, maintained
  incrementally (`IsLinearization.push`). Successful `CAS` operations are linearized at their
  successful `cas`, `READ`s and `CAS`es that fail at line 3 at their read of `C`. A `CAS` of `q`
  that read the current content `c` with `val = old` and has not yet applied its `cas` is
  linearized (*speculatively*, as failed) right after the successful `cas` that overwrites `c`.
  A speculatively linearized operation whose process crashes before returning is retracted
  (`IsLinearization.erase_ro`: its entry is read-only at its position).

`At L x o r`: the entry of `x` in `L` gets the response `r`; `ROAt L x o r`: moreover, it does
not change the state.

`LocInv`: the invariant of a process at each program location; `Succ pc v`: the process's `CAS`
has applied a successful `cas` (if its content is in `W`); `NoAfter W c q`: no content written
by `q` comes after `c` in `W`; `GSucc W R q new`: the process that overwrote `<q, new>` has
written `new` to `R[q][·]` (the helping mechanism of lines 5-6).
-/

namespace Podc.NestingSafeRecoverable.Alg2

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V]

@[simp] lemma δ_cas (q old : Option V) (new : V) :
    (casRObj V).δ q (.cas old new) = if q = old then (some new, .inl true) else (q, .inl false) :=
  rfl

@[simp] lemma δ_read (q : Option V) : (casRObj V).δ q .read = (q, .inr q) := rfl

/-- Linearizations of the implemented object. -/
abbrev Lin (P V : Type) [DecidableEq V] := List (OpId P × (casRObj V).Op)

/-- The state after a sequential history of the implemented object. -/
abbrev lst (L : Lin P V) : Option V := linState (A := casRObj V) L

/-! ### Entries of a linearization -/

/-- The entry `(x, o)` occurs in `L` and gets the response `r`. -/
def At (L : Lin P V) (x : OpId P) (o : (casRObj V).Op) (r : Bool ⊕ Option V) : Prop :=
  ∃ L₁ L₂, L = L₁ ++ (x, o) :: L₂ ∧ ((casRObj V).δ (lst L₁) o).2 = r

/-- The entry `(x, o)` occurs in `L`, gets the response `r` and does not change the state. -/
def ROAt (L : Lin P V) (x : OpId P) (o : (casRObj V).Op) (r : Bool ⊕ Option V) : Prop :=
  ∃ L₁ L₂, L = L₁ ++ (x, o) :: L₂ ∧ (casRObj V).δ (lst L₁) o = (lst L₁, r)

lemma ROAt.at {L : Lin P V} {x o r} (h : ROAt L x o r) : At L x o r := by
  obtain ⟨L₁, L₂, rfl, h⟩ := h
  exact ⟨L₁, L₂, rfl, by rw [h]⟩

lemma At.append {L : Lin P V} {x o r} (h : At L x o r) (M : Lin P V) : At (L ++ M) x o r := by
  obtain ⟨L₁, L₂, rfl, h⟩ := h
  exact ⟨L₁, L₂ ++ M, by simp, h⟩

lemma ROAt.append {L : Lin P V} {x o r} (h : ROAt L x o r) (M : Lin P V) :
    ROAt (L ++ M) x o r := by
  obtain ⟨L₁, L₂, rfl, h⟩ := h
  exact ⟨L₁, L₂ ++ M, by simp, h⟩

lemma lst_erase (L₁ K : Lin P V) {y : OpId P} {o' : (casRObj V).Op} {r'}
    (hro : (casRObj V).δ (lst L₁) o' = (lst L₁, r')) :
    lst (L₁ ++ (y, o') :: K) = lst (L₁ ++ K) := by
  unfold lst at hro ⊢
  rw [linState_append (L := L₁), linState_append (L := L₁), List.map_cons, ObjSpec.runOps_cons,
    hro]

lemma lst_erase' (L₁ L₂ : Lin P V) {y : OpId P} {o' : (casRObj V).Op} {r'}
    (hro : (casRObj V).δ (lst L₁) o' = (lst L₁, r')) :
    lst (L₁ ++ (y, o') :: L₂) = lst (L₁ ++ L₂) := lst_erase L₁ L₂ hro

lemma lst_push_ro {L : Lin P V} {x : OpId P} {o : (casRObj V).Op} {r}
    (hro : (casRObj V).δ (lst L) o = (lst L, r)) : lst (L ++ [(x, o)]) = lst L := by
  unfold lst at hro ⊢
  rw [linState_concat, hro]

/-- Splitting a list with a removed element. -/
lemma split_erase {X : Type} {L₁ L₂ M₁ M₂ : List X} {a b : X} (hab : a ≠ b)
    (h : L₁ ++ a :: L₂ = M₁ ++ b :: M₂) :
    (∃ K, L₁ = M₁ ++ b :: K ∧ M₂ = K ++ a :: L₂) ∨
      (∃ K, M₁ = L₁ ++ a :: K ∧ L₂ = K ++ b :: M₂) := by
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · -- M₁ = L₁ ++ a'
    rcases a' with _ | ⟨z, a'⟩
    · simp only [List.nil_append, List.cons.injEq] at h2; exact absurd h2.1 hab
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      exact Or.inr ⟨a', h1, h2⟩
  · rcases c' with _ | ⟨z, c'⟩
    · simp only [List.nil_append, List.cons.injEq] at h2; exact absurd h2.1.symm hab
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      exact Or.inl ⟨c', h1, h2⟩

lemma At.erase {L₁ L₂ : Lin P V} {y : OpId P} {o' : (casRObj V).Op} {r'}
    (hro : (casRObj V).δ (lst L₁) o' = (lst L₁, r')) {x o r}
    (h : At (L₁ ++ (y, o') :: L₂) x o r) (hxy : x ≠ y) : At (L₁ ++ L₂) x o r := by
  obtain ⟨M₁, M₂, hs, h⟩ := h
  rcases split_erase (by simp [Ne.symm hxy]) hs with ⟨K, rfl, rfl⟩ | ⟨K, rfl, rfl⟩
  · exact ⟨M₁, K ++ L₂, by simp, h⟩
  · refine ⟨L₁ ++ K, M₂, by simp, ?_⟩
    rw [← lst_erase L₁ K hro]; exact h

lemma ROAt.erase {L₁ L₂ : Lin P V} {y : OpId P} {o' : (casRObj V).Op} {r'}
    (hro : (casRObj V).δ (lst L₁) o' = (lst L₁, r')) {x o r}
    (h : ROAt (L₁ ++ (y, o') :: L₂) x o r) (hxy : x ≠ y) : ROAt (L₁ ++ L₂) x o r := by
  obtain ⟨M₁, M₂, hs, h⟩ := h
  rcases split_erase (by simp [Ne.symm hxy]) hs with ⟨K, rfl, rfl⟩ | ⟨K, rfl, rfl⟩
  · exact ⟨M₁, K ++ L₂, by simp, h⟩
  · refine ⟨L₁ ++ K, M₂, by simp, ?_⟩
    rw [← lst_erase L₁ K hro]; exact h

/-- How the linearization may change around the entry of `x` without affecting `x`. -/
def LMono (L L' : Lin P V) (x : OpId P) : Prop :=
  (x ∉ L.map Prod.fst → x ∉ L'.map Prod.fst) ∧ (∀ o r, At L x o r → At L' x o r) ∧
    (∀ o r, ROAt L x o r → ROAt L' x o r)

lemma LMono.refl (L : Lin P V) (x : OpId P) : LMono L L x := ⟨id, fun _ _ => id, fun _ _ => id⟩

lemma LMono.append {L : Lin P V} {x : OpId P} (M : Lin P V) (hx : x ∉ M.map Prod.fst) :
    LMono L (L ++ M) x :=
  ⟨fun h => by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h, hx⟩,
    fun _ _ h => h.append M, fun _ _ h => h.append M⟩

lemma LMono.erase {L₁ L₂ : Lin P V} {y : OpId P} {o' : (casRObj V).Op} {r'}
    (hro : (casRObj V).δ (lst L₁) o' = (lst L₁, r')) {x : OpId P} (hxy : x ≠ y) :
    LMono (L₁ ++ (y, o') :: L₂) (L₁ ++ L₂) x :=
  ⟨fun h => by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons,
      not_or] at h ⊢; exact ⟨h.1, h.2.2⟩,
    fun _ _ h => h.erase hro hxy, fun _ _ h => h.erase hro hxy⟩

/-! ### The sequence of contents -/

/-- No content written by `q` comes after `c` in `W`. -/
def NoAfter (W : List (Cnt P V)) (c : Cnt P V) (q : P) : Prop :=
  ∀ W₁ W₂, W = W₁ ++ c :: W₂ → ∀ d ∈ W₂, d.1 ≠ some q

/-- The content following `<q, new>` in `W` was not written by `j`. -/
def NotSucc (W : List (Cnt P V)) (q : P) (new : V) (j : P) : Prop :=
  ∀ W₁ c W₂, W = W₁ ++ (some q, some new) :: c :: W₂ → c.1 ≠ some j

/-- The process that overwrote `<q, new>` has written `new` to `R[q][·]`. -/
def GSucc (W : List (Cnt P V)) (R : P → P → Option V) (q : P) (new : V) : Prop :=
  ∀ W₁ c W₂ k, W = W₁ ++ (some q, some new) :: c :: W₂ → c.1 = some k → R q k = some new

lemma split_concat {X : Type} {W W₁ W₂ : List X} {c n : X} (h : W ++ [n] = W₁ ++ c :: W₂) :
    (W₂ = [] ∧ W = W₁ ∧ c = n) ∨ ∃ W₂', W₂ = W₂' ++ [n] ∧ W = W₁ ++ c :: W₂' := by
  rcases List.eq_nil_or_concat W₂ with rfl | ⟨W₂', z, hz⟩
  · have := List.append_inj' (s₁ := W) (s₂ := W₁) (t₁ := [n]) (t₂ := [c]) (by simpa using h)
      (by simp)
    simp only [List.cons.injEq, and_true] at this
    exact Or.inl ⟨rfl, this.1, this.2.symm⟩
  · simp only [List.concat_eq_append] at hz; subst hz
    have := List.append_inj' (s₁ := W) (s₂ := W₁ ++ c :: W₂') (t₁ := [n]) (t₂ := [z])
      (by simpa using h) (by simp)
    simp only [List.cons.injEq, and_true] at this
    obtain ⟨h1, rfl⟩ := this
    exact Or.inr ⟨W₂', rfl, h1⟩

lemma NoAfter.concat {W : List (Cnt P V)} {c n : Cnt P V} {q : P} (h : NoAfter W c q)
    (hc : c ∈ W) (hn : n ∉ W) (hnq : n.1 ≠ some q) : NoAfter (W ++ [n]) c q := by
  intro W₁ W₂ hs d hd
  rcases split_concat hs with ⟨rfl, rfl, rfl⟩ | ⟨W₂', rfl, hs'⟩
  · exact absurd hc hn
  · rcases List.mem_append.1 hd with hd | hd
    · exact h W₁ W₂' hs' d hd
    · simp only [List.mem_singleton] at hd; subst hd; exact hnq

lemma noAfter_last {W : List (Cnt P V)} {c : Cnt P V} (hnd : W.Nodup) (hl : W.getLast? = some c)
    (q : P) : NoAfter W c q := by
  intro W₁ W₂ hs d hd
  exfalso
  have hne : W₂ ≠ [] := List.ne_nil_of_mem hd
  have : W.getLast? = W₂.getLast? := by
    rw [hs, List.getLast?_append, List.getLast?_cons]
    rcases List.eq_nil_or_concat W₂ with rfl | ⟨W₂', z, hz⟩
    · exact absurd rfl hne
    · simp only [List.concat_eq_append] at hz; subst hz; simp
  rw [hl] at this
  have hc : c ∈ W₂ := List.mem_of_getLast? this.symm
  rw [hs] at hnd
  exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 hc

lemma succ_concat {X : Type} {W W₁ W₂ : List X} {a c n : X}
    (h : W ++ [n] = W₁ ++ a :: c :: W₂) :
    (∃ W₂', W = W₁ ++ a :: c :: W₂') ∨ (W = W₁ ++ [a] ∧ c = n ∧ W₂ = []) := by
  rcases split_concat (W₁ := W₁ ++ [a]) (W₂ := W₂) (c := c) (by simpa using h) with
    ⟨rfl, rfl, rfl⟩ | ⟨W₂', rfl, h'⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨W₂', by simpa using h'⟩

lemma getLast?_of_split {X : Type} {W W₁ : List X} {a : X} (h : W = W₁ ++ [a]) :
    W.getLast? = some a := by
  subst h; simp

lemma NotSucc.concat {W : List (Cnt P V)} {q : P} {new : V} {j : P} {n : Cnt P V}
    (h : NotSucc W q new j) (hl : W.getLast? ≠ some (some q, some new)) :
    NotSucc (W ++ [n]) q new j := by
  intro W₁ c W₂ hs
  rcases succ_concat hs with ⟨W₂', hs'⟩ | ⟨hs', -, -⟩
  · exact h W₁ c W₂' hs'
  · exact absurd (getLast?_of_split hs') hl

lemma GSucc.concat {W : List (Cnt P V)} {R : P → P → Option V} {q : P} {new : V} {n : Cnt P V}
    (h : GSucc W R q new)
    (hl : W.getLast? = some (some q, some new) → ∀ k, n.1 = some k → R q k = some new) :
    GSucc (W ++ [n]) R q new := by
  intro W₁ c W₂ k hs hk
  rcases succ_concat hs with ⟨W₂', hs'⟩ | ⟨hs', rfl, -⟩
  · exact h W₁ c W₂' k hs' hk
  · exact hl (getLast?_of_split hs') k hk

lemma exists_succ {W : List (Cnt P V)} {a : Cnt P V} (ha : a ∈ W) (hl : W.getLast? ≠ some a) :
    ∃ W₁ c W₂, W = W₁ ++ a :: c :: W₂ := by
  obtain ⟨W₁, W₂, rfl⟩ := List.append_of_mem ha
  rcases W₂ with _ | ⟨c, W₂⟩
  · simp at hl
  · exact ⟨W₁, c, W₂, rfl⟩

lemma mem_tail_of_split {X : Type} {W W₁ W₂ : List X} {a c : X}
    (h : W = W₁ ++ a :: c :: W₂) : c ∈ W.tail := by
  subst h
  rcases W₁ with _ | ⟨z, W₁⟩ <;> simp

/-- The position argument for the helping registers: a content `e` of `q` read by `j` after
`j`'s last write cannot be read after `<q,new>` was overwritten by `j`, if `<q,new>` is the last
content of `q`. -/
lemma eq_of_noAfter {W W₁ W₂ : List (Cnt P V)} {a c e : Cnt P V} {q j : P}
    (hs : W = W₁ ++ a :: c :: W₂) (hc : c.1 = some j) (he : e ∈ W) (heq : e.1 = some q)
    (hej : NoAfter W e j) (haq : NoAfter W a q) : e = a := by
  rw [hs] at he
  rcases List.mem_append.1 he with he | he
  · obtain ⟨U, U', rfl⟩ := List.append_of_mem he
    exact absurd hc (hej U (U' ++ a :: c :: W₂) (by simp [hs]) c (by simp))
  · rcases List.mem_cons.1 he with he | he
    · exact he
    · exact absurd heq (haq W₁ (c :: W₂) hs e he)

/-! ### The invariant -/

variable [Fintype P]

/-- The `CAS` of the process has applied a successful `cas` (if its content is in `W`). -/
def Succ : Loc → Vars P V → Prop
  | .c8, v => v = .inr true
  | .r13, _ => True
  | .r14, _ => True
  | .rR _, _ => True
  | .rT _, _ => True
  | _, _ => False

/-- The recovery loop has not passed the process that overwrote `<q, new>`. -/
def Loop (W : List (Cnt P V)) (q : P) (new : V) (i : ℕ) : Prop :=
  ∀ j ∈ (procs P).take i, NotSucc W q new j

/-- Recovery of `CAS(old, new)`: linearized (successfully) iff `<q, new>` was written. -/
def Rec (W : List (Cnt P V)) (L : Lin P V) (x : OpId P) (q : P) (old : Option V) (new : V) :
    Prop :=
  ((some q, some new) ∈ W → At L x (.cas old new) (.inl true)) ∧
    ((some q, some new) ∉ W → x ∉ L.map Prod.fst)

/-- Before the `cas` of line 7 with expected content `c`: not linearized while `C = c`,
speculatively linearized as failed once `C ≠ c`. -/
def Spec7 (mc : Cnt P V) (L : Lin P V) (x : OpId P) (o : (casRObj V).Op) (c : Cnt P V) : Prop :=
  (mc = c → x ∉ L.map Prod.fst) ∧ (mc ≠ c → ROAt L x o (.inl false))

/-- The invariant of process `q` with current operation instance `x`, at each location.
`mc` is the content of `C`, `Rc k = R[k][q]` (the column of `q`). -/
def LocInv (W : List (Cnt P V)) (mc : Cnt P V) (Rc : P → Option V) (L : Lin P V) (x : OpId P)
    (q : P) : CasROp V → Loc → Vars P V → Prop
  | .cas _ new, .c2, _ => x ∉ L.map Prod.fst ∧ (some q, some new) ∉ W
  | .cas old new, .c3, v => ∃ c, v = .inl c ∧ c ∈ W ∧ NoAfter W c q ∧
      (some q, some new) ∉ W ∧ (c.2 ≠ old → ROAt L x (.cas old new) (.inl false)) ∧
      (c.2 = old → Spec7 mc L x (.cas old new) c)
  | .cas old new, .c7, v => ∃ c, v = .inl c ∧ c.2 = old ∧ c ∈ W ∧ NoAfter W c q ∧
      (some q, some new) ∉ W ∧ (∀ k, c.1 = some k → Rc k = c.2) ∧
      Spec7 mc L x (.cas old new) c
  | .cas old new, .c8, v =>
      (v = .inr true ∧ (some q, some new) ∈ W ∧ At L x (.cas old new) (.inl true)) ∨
      (v = .inr false ∧ (some q, some new) ∉ W ∧ ROAt L x (.cas old new) (.inl false))
  | .cas old new, .r13, _ => Rec W L x q old new
  | .cas old new, .r14, v => Rec W L x q old new ∧ ∃ c, v = .inl c ∧ c ∈ W ∧
      (c ≠ (some q, some new) → (some q, some new) ∈ W → mc ≠ (some q, some new))
  | .cas old new, .rR i, _ => Rec W L x q old new ∧
      ((some q, some new) ∈ W → mc ≠ (some q, some new) ∧ Loop W q new i)
  | .cas old new, .rT i, v => Rec W L x q old new ∧
      ((some q, some new) ∈ W → mc ≠ (some q, some new) ∧ Loop W q new i) ∧
      ∃ h : i < (procs P).length, ∃ r, v = .inl (none, r) ∧
        (r = some new → (some q, some new) ∈ W) ∧
        (r ≠ some new → (some q, some new) ∈ W → NotSucc W q new (procs P)[i])
  | .read, .rd10, _ => x ∉ L.map Prod.fst
  | .read, .rd11, v => ∃ c, v = .inl c ∧ ROAt L x .read (.inr c.2)
  | _, _, _ => False

/-- The per-process part of the invariant (`R a b` = `R[a][b]`). -/
def PInv (W : List (Cnt P V)) (mc : Cnt P V) (R : P → P → Option V) (L : Lin P V)
    (α : List (Label P (casRObj V))) (q : P) : Option (CasROp V × Loc × Vars P V) → Prop
  | none => True
  | some (o, pc, v) => opOf α (curOp α q) = some o ∧
      LocInv W mc (fun k => R k q) L (curOp α q) q o pc v ∧
      ∀ old new, o = .cas old new → Succ pc v → (some q, some new) ∈ W →
        NoAfter W (some q, some new) q ∧ GSucc W R q new

/-- The content of `C`. -/
abbrev memC (C : (alg2 P V).Cfg) : Cnt P V := C.mem .C

/-- The registers: `memR C a b = R[a][b]`. -/
abbrev memR (C : (alg2 P V).Cfg) (a b : P) : Option V := C.mem (.R a b)

/-- The invariant of Algorithm 2 with ghost contents `W` and linearization `L`. -/
structure Inv (C : (alg2 P V).Cfg) (W : List (Cnt P V)) (L : Lin P V) : Prop where
  lin : IsLinearization (N C.hist) L
  lst_eq : lst L = (memC C).2
  wnd : W.Nodup
  wlast : W.getLast? = some (memC C)
  wtail : ∀ c ∈ W.tail, c.1.isSome
  wops : ∀ q w, (some q, some w) ∈ W → ∃ i old, opOf (N C.hist) (q, i) = some (.cas old w)
  reg : ∀ q j w, memR C q j = some w → (some q, some w) ∈ W
  proc : ∀ q, PInv W (memC C) (memR C) L (N C.hist) q (C.st q)

/-! ### Frame lemmas -/

lemma Rec.mono {W : List (Cnt P V)} {L L' : Lin P V} {x : OpId P} {q old new}
    (h : Rec W L x q old new) (hm : LMono L L' x) : Rec W L' x q old new :=
  ⟨fun hw => hm.2.1 _ _ (h.1 hw), fun hw => hm.1 (h.2 hw)⟩

lemma Spec7.mono {mc : Cnt P V} {L L' : Lin P V} {x : OpId P} {o c}
    (h : Spec7 mc L x o c) (hm : LMono L L' x) : Spec7 mc L' x o c :=
  ⟨fun hc => hm.1 (h.1 hc), fun hc => hm.2.2 _ _ (h.2 hc)⟩

lemma LocInv.mono {W : List (Cnt P V)} {mc Rc} {L L' : Lin P V} {x : OpId P} {q o pc v}
    (h : LocInv W mc Rc L x q o pc v) (hm : LMono L L' x) : LocInv W mc Rc L' x q o pc v := by
  rcases o with ⟨old, new⟩ | _ <;> rcases pc with _ | _ | _ | _ | _ | _ | i | i | _ | _ <;>
    simp only [LocInv] at h ⊢
  · exact ⟨hm.1 h.1, h.2⟩
  · obtain ⟨c, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨c, h1, h2, h3, h4, fun hc => hm.2.2 _ _ (h5 hc), fun hc => (h6 hc).mono hm⟩
  · obtain ⟨c, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨c, h1, h2, h3, h4, h5, h6, h7.mono hm⟩
  · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, hm.2.1 _ _ h3⟩
    · exact Or.inr ⟨h1, h2, hm.2.2 _ _ h3⟩
  · exact h.mono hm
  · exact ⟨h.1.mono hm, h.2⟩
  · exact ⟨h.1.mono hm, h.2⟩
  · exact ⟨h.1.mono hm, h.2⟩
  · exact hm.1 h
  · obtain ⟨c, h1, h2⟩ := h
    exact ⟨c, h1, hm.2.2 _ _ h2⟩

/-- The per-process invariant of `q` survives changes of the linearization that do not affect
`q`'s current instance, and of the history that do not affect `q`. -/
lemma PInv.mono {W : List (Cnt P V)} {mc R} {L L' : Lin P V} {α α' : List (Label P (casRObj V))}
    {q : P} {s} (h : PInv W mc R L α q s) (hops : opsOf α' q = opsOf α q)
    (hres : respsOf α' q = respsOf α q) (hm : LMono L L' (curOp α q)) :
    PInv W mc R L' α' q s := by
  rcases s with _ | ⟨o, pc, v⟩
  · trivial
  · have hc : curOp α' q = curOp α q := by simp [curOp, hres]
    have ho : opOf α' (curOp α q) = opOf α (curOp α q) := by simp [opOf, hops]
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rw [hc, ho]; exact h1, by rw [hc]; exact h2.mono hm, h3⟩

end Podc.NestingSafeRecoverable.Alg2
