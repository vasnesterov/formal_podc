import Cslib.Computability.Distributed.SharedMemory.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Awareness.lean

/-!
# Awareness sets and erasure for read/write/CAS implementations

Information-flow bookkeeping for lower bounds in the style of Jayanti–Tan–Toueg and
Attiya–Hendler ("processes cannot become aware of others too fast"). The base objects are
read/write/CAS registers (`RWC ι V v₀`, every base object is a `casObject V v₀`).

Along an execution we track a *ghost* (`Ghost`):

* `aw p` — the *awareness set* of `p`: the processes whose participation may have influenced
  `p`'s local state (initially `{p}`);
* `hist i` — the stack of *value-setting events* on base object `i` (most recent first): every
  `write`, and every `CAS` that changes the value, pushes an entry recording the writer, the new
  value and the writer's awareness set at that moment. The *familiarity set* `F i` of `i` is the
  awareness set of the top entry (`∅` if there is none).

A read of `i` (or the read part of a CAS) adds `F i` to the reader's awareness set. Trivial events
(reads, failed CAS, CAS whose new value equals the old one) do not touch `hist`. This is a precise
data-flow semantics: the value of `i` is the value of its top entry (`cons_mem`), and a process
learns exactly the awareness set of the last writer of every object it reads.

## Main results

* `arun` — the run augmented with the ghost; `arun_inv` — invariants (consistency of memory with
  `hist`, self-awareness, entries are bounded by the writer's later awareness); `arun_aw_mono`.
* `erase` / `arun_erase` — **erasure lemma** (a sound version of Lemma 2 of Hendler–Khait,
  PODC'14): removing from an execution all labels of a process `q` issued while `q` is aware of a
  member of `S` yields an execution; processes never aware of `S` keep their local states, pending
  operations and awareness sets; every awareness set shrinks; the history of every base object is
  filtered to the entries whose writer was not aware of `S`.
* `Hidden` / `erase_filter_proc_of_hidden` — erasing a set of *hidden* processes (no other
  process is aware of them) removes exactly their labels.
-/

namespace Cslib.SharedMemory.Awareness

open Cslib.SharedMemory

/-- Base objects: read/write/CAS registers over `V`. -/
abbrev RWC (ι V : Type) [DecidableEq V] (v₀ : V) : ι → ObjSpec := fun _ => casObject V v₀

/-- An entry of the history of a base object: writer, new value, writer's awareness set. -/
structure Entry (P V : Type) where
  /-- The process that set the value. -/
  proc : P
  /-- The new value. -/
  val : V
  /-- The awareness set of the writer when it set the value. -/
  aw : Finset P

/-- The ghost state: awareness sets and histories of value-setting events. -/
structure Ghost (P ι V : Type) where
  /-- Awareness sets. -/
  aw : P → Finset P
  /-- Value-setting events per base object, most recent first. -/
  hist : ι → List (Entry P V)

variable {A : ObjSpec} {ι P L V : Type} [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}

/-- The awareness set stored in the top entry of a history (`∅` for an empty history). -/
def topAw : List (Entry P V) → Finset P
  | [] => ∅
  | e :: _ => e.aw

/-- The value stored in the top entry of a history (`d` for an empty history). -/
def topVal (d : V) : List (Entry P V) → V
  | [] => d
  | e :: _ => e.val

@[simp] lemma topAw_nil : topAw ([] : List (Entry P V)) = ∅ := rfl
@[simp] lemma topAw_cons (e : Entry P V) (h : List (Entry P V)) : topAw (e :: h) = e.aw := rfl
@[simp] lemma topVal_nil (d : V) : topVal d ([] : List (Entry P V)) = d := rfl
@[simp] lemma topVal_cons (d : V) (e : Entry P V) (h : List (Entry P V)) :
    topVal d (e :: h) = e.val := rfl

namespace Ghost

/-- The familiarity set of base object `i`. -/
def F (G : Ghost P ι V) (i : ι) : Finset P := topAw (G.hist i)

/-- The initial ghost: every process is aware only of itself, no value-setting events. -/
def init : Ghost P ι V := ⟨fun p => {p}, fun _ => []⟩

end Ghost

variable (I : Impl A (RWC ι V v₀) P L)

/-- The ghost effect of a label taken in configuration `C`. -/
def gstep (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V) : Label P A → Ghost P ι V
  | .tau p =>
    match I.act p (C.loc p) with
    | .access i o _ =>
      match (o : CASOp V) with
      | .read => { G with aw := Function.update G.aw p (G.aw p ∪ G.F i) }
      | .write v => { G with hist := Function.update G.hist i (⟨p, v, G.aw p⟩ :: G.hist i) }
      | .cas a b =>
        { aw := Function.update G.aw p (G.aw p ∪ G.F i)
          hist := if C.mem i = a ∧ b ≠ a then
              Function.update G.hist i (⟨p, b, G.aw p ∪ G.F i⟩ :: G.hist i)
            else G.hist }
    | .ret _ _ => G
  | _ => G

/-- Augmented step: configuration and ghost. -/
noncomputable def astep (X : Config A (RWC ι V v₀) P L × Ghost P ι V) (ℓ : Label P A) :
    Option (Config A (RWC ι V v₀) P L × Ghost P ι V) :=
  (I.step X.1 ℓ).map (fun C' => (C', gstep I X.1 X.2 ℓ))

/-- Augmented run from a configuration/ghost pair. -/
noncomputable def arunFrom :
    Config A (RWC ι V v₀) P L × Ghost P ι V → List (Label P A) →
      Option (Config A (RWC ι V v₀) P L × Ghost P ι V)
  | X, [] => some X
  | X, ℓ :: α => (astep I X ℓ).bind (fun Y => arunFrom Y α)

/-- Augmented run from the initial configuration. -/
noncomputable def arun (α : List (Label P A)) : Option (Config A (RWC ι V v₀) P L × Ghost P ι V) :=
  arunFrom I (I.initCfg, Ghost.init) α

@[simp] lemma arunFrom_nil (X : Config A (RWC ι V v₀) P L × Ghost P ι V) :
    arunFrom I X [] = some X := rfl

@[simp] lemma arunFrom_cons (X : Config A (RWC ι V v₀) P L × Ghost P ι V) (ℓ : Label P A)
    (α : List (Label P A)) :
    arunFrom I X (ℓ :: α) = (astep I X ℓ).bind (fun Y => arunFrom I Y α) := rfl

lemma arunFrom_append (X : Config A (RWC ι V v₀) P L × Ghost P ι V) (α β : List (Label P A)) :
    arunFrom I X (α ++ β) = (arunFrom I X α).bind (fun Y => arunFrom I Y β) := by
  induction α generalizing X with
  | nil => simp
  | cons ℓ α ih =>
    simp only [List.cons_append, arunFrom_cons, ih]
    cases astep I X ℓ <;> simp

lemma arunFrom_singleton (X : Config A (RWC ι V v₀) P L × Ghost P ι V) (ℓ : Label P A) :
    arunFrom I X [ℓ] = astep I X ℓ := by
  simp only [arunFrom_cons, arunFrom_nil]; cases astep I X ℓ <;> rfl

lemma arun_concat (α : List (Label P A)) (ℓ : Label P A) :
    arun I (α ++ [ℓ]) = (arun I α).bind (fun X => astep I X ℓ) := by
  simp only [arun, arunFrom_append]
  cases arunFrom I (I.initCfg, Ghost.init) α <;> simp [arunFrom_singleton]

lemma arun_append_of_eq {α : List (Label P A)} {X : Config A (RWC ι V v₀) P L × Ghost P ι V}
    (h : arun I α = some X) (β : List (Label P A)) :
    arun I (α ++ β) = arunFrom I X β := by
  unfold arun at h ⊢; rw [arunFrom_append, h]; rfl

lemma astep_eq_some {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V} {ℓ : Label P A} :
    astep I X ℓ = some Y ↔ I.step X.1 ℓ = some Y.1 ∧ Y.2 = gstep I X.1 X.2 ℓ := by
  obtain ⟨C, G⟩ := X; obtain ⟨C', G'⟩ := Y
  simp only [astep, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨C'', h, rfl, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨C', h, rfl, rfl⟩

lemma arunFrom_fst {X : Config A (RWC ι V v₀) P L × Ghost P ι V} {α : List (Label P A)}
    {Y : Config A (RWC ι V v₀) P L × Ghost P ι V} (h : arunFrom I X α = some Y) :
    I.runFrom X.1 α = some Y.1 := by
  induction α generalizing X with
  | nil => simp only [arunFrom_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      have := (astep_eq_some I).1 hs
      simp only [Impl.runFrom_cons, this.1, Option.bind_some]
      exact ih h

lemma arun_fst {α : List (Label P A)} {X : Config A (RWC ι V v₀) P L × Ghost P ι V}
    (h : arun I α = some X) : I.run α = some X.1 := arunFrom_fst I h

lemma exists_arunFrom {C C' : Config A (RWC ι V v₀) P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') (G : Ghost P ι V) :
    ∃ G', arunFrom I (C, G) α = some (C', G') := by
  induction α generalizing C G with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; exact ⟨G, rfl⟩
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨G', hG'⟩ := ih h (gstep I C G ℓ)
      refine ⟨G', ?_⟩
      simp only [arunFrom_cons]
      rw [show astep I (C, G) ℓ = some (C₁, gstep I C G ℓ) from
        (astep_eq_some I).2 ⟨hs, rfl⟩]
      exact hG'

lemma exists_arun {α : List (Label P A)} {C : Config A (RWC ι V v₀) P L} (h : I.run α = some C) :
    ∃ G, arun I α = some (C, G) := exists_arunFrom I h Ghost.init

/-- Induction principle for augmented runs. -/
lemma arun_induction {Q : List (Label P A) → Config A (RWC ι V v₀) P L → Ghost P ι V → Prop}
    (h0 : Q [] I.initCfg Ghost.init)
    (hs : ∀ α C G ℓ C', arun I α = some (C, G) → Q α C G → I.step C ℓ = some C' →
      Q (α ++ [ℓ]) C' (gstep I C G ℓ))
    {α : List (Label P A)} {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V}
    (h : arun I α = some (C, G)) : Q α C G := by
  induction α using List.reverseRecOn generalizing C G with
  | nil => simp only [arun, arunFrom_nil, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h; exact h0
  | append_singleton α ℓ ih =>
    rw [arun_concat] at h
    cases hα : arun I α with
    | none => simp [hα] at h
    | some X =>
      simp only [hα, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := (astep_eq_some I).1 h
      simp only at h1 h2; subst h2
      exact hs α X.1 X.2 ℓ C hα (ih hα) h1

/-! ### Effect of a step on the ghost -/

section Effects

variable {I}

@[simp] lemma gstep_inv' (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V) (p : P) (o : A.Op) :
    gstep I C G (.inv p o) = G := rfl

@[simp] lemma gstep_ret' (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V) (p : P) (r : A.Resp) :
    gstep I C G (.ret p r) = G := rfl

lemma gstep_of_not_tau {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {ℓ : Label P A}
    (h : ∀ p, ℓ ≠ .tau p) : gstep I C G ℓ = G := by
  cases ℓ with
  | inv p o => rfl
  | ret p r => rfl
  | tau p => exact absurd rfl (h p)

lemma gstep_tau_read {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {p : P} {i : ι}
    {k : V ⊕ Bool → L} (h : I.act p (C.loc p) = .access i .read k) :
    gstep I C G (.tau p) = { G with aw := Function.update G.aw p (G.aw p ∪ G.F i) } := by
  simp [gstep, h]

lemma gstep_tau_write {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {p : P} {i : ι} {v : V}
    {k : V ⊕ Bool → L} (h : I.act p (C.loc p) = .access i (.write v) k) :
    gstep I C G (.tau p) =
      { G with hist := Function.update G.hist i (⟨p, v, G.aw p⟩ :: G.hist i) } := by
  simp [gstep, h]

lemma gstep_tau_cas {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {p : P} {i : ι} {a b : V}
    {k : V ⊕ Bool → L} (h : I.act p (C.loc p) = .access i (.cas a b) k) :
    gstep I C G (.tau p) =
      { aw := Function.update G.aw p (G.aw p ∪ G.F i)
        hist := if C.mem i = a ∧ b ≠ a then
            Function.update G.hist i (⟨p, b, G.aw p ∪ G.F i⟩ :: G.hist i)
          else G.hist } := by
  simp [gstep, h]

/-- A step only changes the awareness set of the stepping process, and only by growing it. -/
lemma gstep_aw (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V) (ℓ : Label P A) (q : P) :
    G.aw q ⊆ (gstep I C G ℓ).aw q ∧ (ℓ.proc ≠ q → (gstep I C G ℓ).aw q = G.aw q) := by
  cases ℓ with
  | inv p o => simp [gstep]
  | ret p r => simp [gstep]
  | tau p =>
    simp only [gstep, Label.proc]
    split
    · rename_i i o k _
      cases o with
      | read =>
        by_cases hq : p = q
        · subst hq; simp
        · simp [Function.update_of_ne (Ne.symm hq), hq]
      | write v => simp
      | cas a b =>
        by_cases hq : p = q
        · subst hq; simp
        · simp [Function.update_of_ne (Ne.symm hq), hq]
    · simp

end Effects

/-! ### Invariants of augmented runs -/

/-- Invariants of reachable configuration/ghost pairs. -/
structure Inv (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V) : Prop where
  /-- The value of a base object is the value of its top entry. -/
  mem_eq : ∀ i, C.mem i = topVal (I.memInit i) (G.hist i)
  /-- Every process is aware of itself. -/
  self_mem : ∀ p, p ∈ G.aw p
  /-- Entries are bounded by the later awareness set of their writer, and contain the writer. -/
  entry : ∀ i, ∀ e ∈ G.hist i, e.aw ⊆ G.aw e.proc ∧ e.proc ∈ e.aw

variable {I}

lemma Inv.step {C C' : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {ℓ : Label P A}
    (hI : Inv I C G) (hs : I.step C ℓ = some C') : Inv I C' (gstep I C G ℓ) := by
  have haw := gstep_aw (I := I) C G ℓ
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, -, hm⟩ := Impl.step_inv hs
    exact ⟨fun i => by rw [hm]; exact hI.mem_eq i, hI.self_mem, hI.entry⟩
  | ret p r =>
    obtain ⟨-, -, hm, -⟩ := Impl.step_ret hs
    exact ⟨fun i => by rw [hm]; exact hI.mem_eq i, hI.self_mem, hI.entry⟩
  | tau p =>
    obtain ⟨-, -, i, o, k, hact, hm, -⟩ := Impl.step_tau hs
    have hself : ∀ q, q ∈ (gstep I C G (.tau p)).aw q := fun q => (haw q).1 (hI.self_mem q)
    have hent_old : ∀ j, ∀ e ∈ G.hist j, e.aw ⊆ (gstep I C G (.tau p)).aw e.proc ∧
        e.proc ∈ e.aw := fun j e he =>
      ⟨(hI.entry j e he).1.trans (haw e.proc).1, (hI.entry j e he).2⟩
    cases o with
    | read =>
      rw [gstep_tau_read hact]
      rw [gstep_tau_read hact] at hself hent_old
      refine ⟨fun j => ?_, hself, hent_old⟩
      rw [hm]; by_cases hj : j = i
      · subst hj; simp [hI.mem_eq j]
      · simp [Function.update_of_ne hj, hI.mem_eq j]
    | write v =>
      rw [gstep_tau_write hact]
      rw [gstep_tau_write hact] at hself hent_old
      refine ⟨fun j => ?_, hself, fun j e he => ?_⟩
      · rw [hm]; by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, hI.mem_eq j]
      · by_cases hj : j = i
        · subst hj
          simp only [Function.update_self, List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨subset_rfl, hI.self_mem p⟩
          · exact hent_old j e he
        · simp only [Function.update_of_ne hj] at he; exact hent_old j e he
    | cas a b =>
      rw [gstep_tau_cas hact]
      rw [gstep_tau_cas hact] at hself hent_old
      refine ⟨fun j => ?_, hself, fun j e he => ?_⟩
      · rw [hm]
        by_cases hj : j = i
        · subst hj
          by_cases hc : C.mem j = a
          · by_cases hb : b ≠ a
            · simp [hc, hb]
            · push_neg at hb; subst hb; simp [hc]; rw [← hI.mem_eq j, hc]
          · simp [hc]; exact hI.mem_eq j
        · simp only [Function.update_of_ne hj]
          split_ifs <;> simp [Function.update_of_ne hj, hI.mem_eq j]
      · split_ifs at he with hc
        · by_cases hj : j = i
          · subst hj
            simp only [Function.update_self, List.mem_cons] at he
            rcases he with rfl | he
            · exact ⟨by simp, Finset.mem_union_left _ (hI.self_mem p)⟩
            · exact hent_old j e he
          · simp only [Function.update_of_ne hj] at he; exact hent_old j e he
        · exact hent_old j e he

lemma inv_init : Inv I I.initCfg (Ghost.init : Ghost P ι V) :=
  ⟨fun _ => rfl, fun p => by simp [Ghost.init], fun _ e he => by simp [Ghost.init] at he⟩

lemma arun_inv {α : List (Label P A)} {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V}
    (h : arun I α = some (C, G)) : Inv I C G :=
  arun_induction I (Q := fun _ C G => Inv I C G) inv_init
    (fun _ _ _ _ _ _ hI hs => hI.step hs) h

/-- Awareness sets only grow along an execution. -/
lemma arunFrom_aw_mono {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V} {α : List (Label P A)}
    (h : arunFrom I X α = some Y) (q : P) : X.2.aw q ⊆ Y.2.aw q := by
  induction α generalizing X with
  | nil => simp only [arunFrom_nil, Option.some.injEq] at h; subst h; exact subset_rfl
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      have := ((astep_eq_some I).1 hs).2
      exact (this ▸ (gstep_aw X.1 X.2 ℓ q).1).trans (ih h)

/-- Awareness sets of processes that take no step are unchanged. -/
lemma arunFrom_aw_of_not_mem {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V}
    {α : List (Label P A)} (h : arunFrom I X α = some Y) (q : P) (hq : ∀ ℓ ∈ α, ℓ.proc ≠ q) :
    Y.2.aw q = X.2.aw q := by
  induction α generalizing X with
  | nil => simp only [arunFrom_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      have := ((astep_eq_some I).1 hs).2
      rw [ih h (fun ℓ' h' => hq ℓ' (List.mem_cons_of_mem _ h')), this]
      exact (gstep_aw X.1 X.2 ℓ q).2 (hq ℓ List.mem_cons_self)

/-! ### Erasure -/

variable (I)

/-- The labels kept when erasing `S`: a label of `q` is kept iff after it `q` is not aware of
any process of `S`. -/
noncomputable def eraseFrom (S : Finset P) :
    Config A (RWC ι V v₀) P L → Ghost P ι V → List (Label P A) → List (Label P A)
  | _, _, [] => []
  | C, G, ℓ :: α =>
    match I.step C ℓ with
    | none => []
    | some C' =>
      (if Disjoint ((gstep I C G ℓ).aw ℓ.proc) S then [ℓ] else []) ++
        eraseFrom S C' (gstep I C G ℓ) α

/-- `erase S α`: the execution `α` with every label issued by a process while it is aware of a
process of `S` removed (in particular, all labels of `S`). -/
noncomputable def erase (S : Finset P) (α : List (Label P A)) : List (Label P A) :=
  eraseFrom I S I.initCfg Ghost.init α

variable {I}

/-- The relation between a configuration/ghost and its erased counterpart. -/
structure ERel (S : Finset P) (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V)
    (C' : Config A (RWC ι V v₀) P L) (G' : Ghost P ι V) : Prop where
  loc : ∀ q, Disjoint (G.aw q) S → C'.loc q = C.loc q
  pend : ∀ q, Disjoint (G.aw q) S → C'.pend q = C.pend q
  aw_eq : ∀ q, Disjoint (G.aw q) S → G'.aw q = G.aw q
  aw_sub : ∀ q, G'.aw q ⊆ G.aw q
  hist : ∀ i, G'.hist i = (G.hist i).filter (fun e => Disjoint e.aw S)

lemma topAw_filter_of_disjoint {S : Finset P} {h : List (Entry P V)} (hd : Disjoint (topAw h) S)
    (hne : ∀ e ∈ h, True := fun _ _ => trivial) :
    topAw (h.filter (fun e => Disjoint e.aw S)) = topAw h ∧
      ∀ d, topVal d (h.filter (fun e => Disjoint e.aw S)) = topVal d h := by
  cases h with
  | nil => simp
  | cons e h =>
    simp only [topAw_cons] at hd
    simp [List.filter_cons, hd]

lemma ERel.step {S : Finset P} {C C₁ C' : Config A (RWC ι V v₀) P L} {G G' : Ghost P ι V}
    {ℓ : Label P A} (hR : ERel S C G C' G') (hI : Inv I C G) (hI' : Inv I C' G')
    (hs : I.step C ℓ = some C₁) :
    (Disjoint ((gstep I C G ℓ).aw ℓ.proc) S →
      ∃ C₁', I.step C' ℓ = some C₁' ∧ ERel S C₁ (gstep I C G ℓ) C₁' (gstep I C' G' ℓ)) ∧
    (¬ Disjoint ((gstep I C G ℓ).aw ℓ.proc) S → ERel S C₁ (gstep I C G ℓ) C' G') := by
  have haw := gstep_aw (I := I) C G ℓ
  -- labels of other processes do not touch `q`
  have hother : ∀ q, ℓ.proc ≠ q → C₁.loc q = C.loc q ∧ C₁.pend q = C.pend q :=
    fun q hq => Impl.step_other hs hq
  constructor
  · intro hk
    have hk0 : Disjoint (G.aw ℓ.proc) S := Finset.disjoint_of_subset_left (haw _).1 hk
    cases ℓ with
    | inv p o =>
      simp only [Label.proc] at hk0
      obtain ⟨h0, hal, hp, hl, hm⟩ := Impl.step_inv hs
      have hstep : I.step C' (.inv p o) = some { C' with
          pend := Function.update C'.pend p (some o),
          loc := Function.update C'.loc p (I.invoke p (C'.loc p) o) } := by
        simp [Impl.step, hR.pend p hk0, h0, hal]
      refine ⟨_, hstep, ?_⟩
      simp only [gstep_inv', gstep_ret'] at *
      refine ⟨fun q hq => ?_, fun q hq => ?_, hR.aw_eq, hR.aw_sub, hR.hist⟩
      · by_cases hqp : q = p
        · subst hqp; simp [hl, hR.loc q hq]
        · simp [hl, Function.update_of_ne hqp, hR.loc q hq]
      · by_cases hqp : q = p
        · subst hqp; simp [hp]
        · simp [hp, Function.update_of_ne hqp, hR.pend q hq]
    | ret p r =>
      simp only [Label.proc] at hk0
      obtain ⟨h0, hp, hm, l, hact, hl⟩ := Impl.step_ret hs
      have hstep : I.step C' (.ret p r) = some { C' with
          pend := Function.update C'.pend p none, loc := Function.update C'.loc p l } := by
        simp [Impl.step, hR.pend p hk0, h0, hR.loc p hk0, hact]
      refine ⟨_, hstep, ?_⟩
      simp only [gstep_inv', gstep_ret'] at *
      refine ⟨fun q hq => ?_, fun q hq => ?_, hR.aw_eq, hR.aw_sub, hR.hist⟩
      · by_cases hqp : q = p
        · subst hqp; simp [hl]
        · simp [hl, Function.update_of_ne hqp, hR.loc q hq]
      · by_cases hqp : q = p
        · subst hqp; simp [hp]
        · simp [hp, Function.update_of_ne hqp, hR.pend q hq]
    | tau p =>
      simp only [Label.proc] at hk hk0
      obtain ⟨h0, hp, i, o, k, hact, hm, hl⟩ := Impl.step_tau hs
      have hact' : I.act p (C'.loc p) = .access i o k := by rw [hR.loc p hk0]; exact hact
      have hpend' : C'.pend p ≠ none := by rw [hR.pend p hk0]; exact h0
      have hstep : I.step C' (.tau p) = some { C' with
          mem := Function.update C'.mem i ((casObject V v₀).δ (C'.mem i) o).1,
          loc := Function.update C'.loc p (k ((casObject V v₀).δ (C'.mem i) o).2) } := by
        simp [Impl.step, hpend', hact']
      refine ⟨_, hstep, ?_⟩
      -- the familiarity set of `i` is disjoint from `S` unless `o` is a write
      have hF : (∀ a b, o = .cas a b → Disjoint (G.F i) S) ∧ (o = .read → Disjoint (G.F i) S) := by
        constructor
        · intro a b ho; subst ho
          rw [gstep_tau_cas hact] at hk
          simp only [Function.update_self, Finset.disjoint_union_left] at hk
          exact hk.2
        · intro ho; subst ho
          rw [gstep_tau_read hact] at hk
          simp only [Function.update_self, Finset.disjoint_union_left] at hk
          exact hk.2
      have hmemi : (o = .read ∨ ∃ a b, o = .cas a b) → C'.mem i = C.mem i ∧ G'.F i = G.F i := by
        intro ho
        have hd : Disjoint (topAw (G.hist i)) S := by
          rcases ho with ho | ⟨a, b, ho⟩
          · exact hF.2 ho
          · exact hF.1 a b ho
        obtain ⟨h1, h2⟩ := topAw_filter_of_disjoint hd
        refine ⟨?_, ?_⟩
        · rw [hI'.mem_eq, hI.mem_eq, hR.hist, h2]
        · simp only [Ghost.F, hR.hist, h1]
      have hlocq : ∀ q, q ≠ p → Disjoint (G.aw q) S →
          (Function.update C'.loc p (k ((casObject V v₀).δ (C'.mem i) o).2)) q = C₁.loc q := by
        intro q hq hd
        rw [Function.update_of_ne hq, (hother q (Ne.symm hq)).1, hR.loc q hd]
      cases o with
      | read =>
        obtain ⟨hm1, hF1⟩ := hmemi (Or.inl rfl)
        rw [gstep_tau_read hact] at hk ⊢
        rw [gstep_tau_read hact']
        refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q => ?_, fun j => ?_⟩
        · by_cases hqp : q = p
          · subst hqp; simp [hl, hm1]
          · simp only [Function.update_of_ne hqp] at hq; exact hlocq q hqp hq
        · by_cases hqp : q = p
          · subst hqp; simp [hp, hR.pend q hk0]
          · simp only [Function.update_of_ne hqp] at hq
            simp [hp, hR.pend q hq]
        · by_cases hqp : q = p
          · subst hqp; simp [hF1, hR.aw_eq q hk0]
          · simp only [Function.update_of_ne hqp] at hq ⊢; exact hR.aw_eq q hq
        · by_cases hqp : q = p
          · subst hqp; simp [hF1, hR.aw_eq q hk0]
          · simp only [Function.update_of_ne hqp]; exact hR.aw_sub q
        · exact hR.hist j
      | write v =>
        rw [gstep_tau_write hact] at hk ⊢
        rw [gstep_tau_write hact']
        simp only at hk
        refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q => hR.aw_sub q,
          fun j => ?_⟩
        · by_cases hqp : q = p
          · subst hqp; simp [hl]
          · exact hlocq q hqp hq
        · by_cases hqp : q = p
          · subst hqp; simp [hp, hR.pend q hk0]
          · simp [hp, hR.pend q hq]
        · exact hR.aw_eq q hq
        · by_cases hj : j = i
          · subst hj; simp [hR.hist, hR.aw_eq p hk0, List.filter_cons, hk]
          · simp [Function.update_of_ne hj, hR.hist]
      | cas a b =>
        obtain ⟨hm1, hF1⟩ := hmemi (Or.inr ⟨a, b, rfl⟩)
        rw [gstep_tau_cas hact] at hk ⊢
        rw [gstep_tau_cas hact']
        simp only [Function.update_self] at hk
        refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q => ?_, fun j => ?_⟩
        · by_cases hqp : q = p
          · subst hqp; simp [hl, hm1]
          · simp only [Function.update_of_ne hqp] at hq; exact hlocq q hqp hq
        · by_cases hqp : q = p
          · subst hqp; simp [hp, hR.pend q hk0]
          · simp only [Function.update_of_ne hqp] at hq
            simp [hp, hR.pend q hq]
        · by_cases hqp : q = p
          · subst hqp; simp [hF1, hR.aw_eq q hk0]
          · simp only [Function.update_of_ne hqp] at hq ⊢; exact hR.aw_eq q hq
        · by_cases hqp : q = p
          · subst hqp; simp [hF1, hR.aw_eq q hk0]
          · simp only [Function.update_of_ne hqp]; exact hR.aw_sub q
        · simp only [hm1, hF1, hR.aw_eq p hk0]
          split_ifs with hc
          · by_cases hj : j = i
            · subst hj; simp [hR.hist, List.filter_cons, hk]
            · simp [Function.update_of_ne hj, hR.hist]
          · exact hR.hist j
  · intro hk
    cases ℓ with
    | inv p o =>
      simp only [gstep_inv', gstep_ret', Label.proc] at hk ⊢
      refine ⟨fun q hq => ?_, fun q hq => ?_, hR.aw_eq, hR.aw_sub, hR.hist⟩
      · have hqp : p ≠ q := fun h => hk (h ▸ hq)
        rw [(hother q hqp).1, hR.loc q hq]
      · have hqp : p ≠ q := fun h => hk (h ▸ hq)
        rw [(hother q hqp).2, hR.pend q hq]
    | ret p r =>
      simp only [gstep_inv', gstep_ret', Label.proc] at hk ⊢
      refine ⟨fun q hq => ?_, fun q hq => ?_, hR.aw_eq, hR.aw_sub, hR.hist⟩
      · have hqp : p ≠ q := fun h => hk (h ▸ hq)
        rw [(hother q hqp).1, hR.loc q hq]
      · have hqp : p ≠ q := fun h => hk (h ▸ hq)
        rw [(hother q hqp).2, hR.pend q hq]
    | tau p =>
      simp only [Label.proc] at hk
      have hne : ∀ q, Disjoint ((gstep I C G (.tau p)).aw q) S → (Label.tau p : Label P A).proc ≠ q :=
        fun q hq h => hk (by simp only [Label.proc] at h; subst h; exact hq)
      obtain ⟨h0, hp, i, o, k, hact, hm, hl⟩ := Impl.step_tau hs
      refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q => ?_, fun j => ?_⟩
      · rw [(hother q (hne q hq)).1, hR.loc q ((haw q).2 (hne q hq) ▸ hq)]
      · rw [(hother q (hne q hq)).2, hR.pend q ((haw q).2 (hne q hq) ▸ hq)]
      · rw [(haw q).2 (hne q hq)]; exact hR.aw_eq q ((haw q).2 (hne q hq) ▸ hq)
      · exact (hR.aw_sub q).trans (haw q).1
      · cases o with
        | read => rw [gstep_tau_read hact]; exact hR.hist j
        | write v =>
          rw [gstep_tau_write hact] at hk ⊢
          simp only at hk ⊢
          by_cases hj : j = i
          · subst hj; simp [hR.hist, List.filter_cons, hk]
          · simp [Function.update_of_ne hj, hR.hist]
        | cas a b =>
          rw [gstep_tau_cas hact] at hk ⊢
          simp only [Function.update_self] at hk ⊢
          split_ifs with hc
          · by_cases hj : j = i
            · subst hj; simp [hR.hist, List.filter_cons, hk]
            · simp [Function.update_of_ne hj, hR.hist]
          · exact hR.hist j

lemma Inv.arunFrom {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V} {α : List (Label P A)}
    (hI : Inv I X.1 X.2) (h : arunFrom I X α = some Y) : Inv I Y.1 Y.2 := by
  induction α generalizing X with
  | nil => simp only [arunFrom_nil, Option.some.injEq] at h; subst h; exact hI
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := (astep_eq_some I).1 hs
      exact ih (h2 ▸ hI.step h1) h

lemma eraseFrom_spec {S : Finset P} {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V}
    {α : List (Label P A)} (h : arunFrom I X α = some Y) (hI : Inv I X.1 X.2)
    {C' : Config A (RWC ι V v₀) P L} {G' : Ghost P ι V} (hR : ERel S X.1 X.2 C' G')
    (hI' : Inv I C' G') :
    ∃ Y', arunFrom I (C', G') (eraseFrom I S X.1 X.2 α) = some Y' ∧
      ERel S Y.1 Y.2 Y'.1 Y'.2 ∧ Inv I Y'.1 Y'.2 := by
  induction α generalizing X C' G' with
  | nil =>
    simp only [arunFrom_nil, Option.some.injEq] at h; subst h
    exact ⟨(C', G'), rfl, hR, hI'⟩
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := (astep_eq_some I).1 hs
      have hIZ : Inv I Z.1 Z.2 := h2 ▸ hI.step h1
      obtain ⟨hk, hnk⟩ := hR.step hI hI' h1
      simp only [eraseFrom, h1]
      by_cases hd : Disjoint ((gstep I X.1 X.2 ℓ).aw ℓ.proc) S
      · obtain ⟨C₁', hs', hR'⟩ := hk hd
        rw [← h2] at hR'
        obtain ⟨Y', hY', hR'', hI''⟩ := ih h hIZ hR' (hI'.step hs')
        refine ⟨Y', ?_, hR'', hI''⟩
        rw [if_pos hd, ← h2]
        simp only [List.singleton_append, arunFrom_cons]
        rw [show astep I (C', G') ℓ = some (C₁', gstep I C' G' ℓ) from
          (astep_eq_some I).2 ⟨hs', rfl⟩]
        exact hY'
      · have hR' := hnk hd
        rw [← h2] at hR'
        obtain ⟨Y', hY', hR'', hI''⟩ := ih h hIZ hR' hI'
        refine ⟨Y', ?_, hR'', hI''⟩
        rw [if_neg hd, ← h2]
        exact hY'

/-- **Erasure lemma.** Erasing `S` from an execution gives an execution related to it by
`ERel`. -/
theorem arun_erase (S : Finset P) {α : List (Label P A)} {C : Config A (RWC ι V v₀) P L}
    {G : Ghost P ι V} (h : arun I α = some (C, G)) :
    ∃ C' G', arun I (erase I S α) = some (C', G') ∧ ERel S C G C' G' := by
  obtain ⟨⟨C', G'⟩, h1, h2, -⟩ := eraseFrom_spec (S := S) h inv_init
    (C' := I.initCfg) (G' := Ghost.init)
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => subset_rfl, fun _ => rfl⟩ inv_init
  exact ⟨C', G', h1, h2⟩

lemma eraseFrom_sublist (S : Finset P) (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V)
    (α : List (Label P A)) : (eraseFrom I S C G α).Sublist α := by
  induction α generalizing C G with
  | nil => simp [eraseFrom]
  | cons ℓ α ih =>
    simp only [eraseFrom]
    split
    · exact List.nil_sublist _
    · rename_i C' _
      split_ifs
      · exact (ih C' _).cons₂ ℓ
      · exact (ih C' _).cons ℓ

lemma erase_sublist (S : Finset P) (α : List (Label P A)) : (erase I S α).Sublist α :=
  eraseFrom_sublist S _ _ α

/-- Labels kept by the erasure belong to processes outside `S`. -/
lemma eraseFrom_proc_not_mem {S : Finset P} {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V}
    {α : List (Label P A)} (h : arunFrom I X α = some Y) (hI : Inv I X.1 X.2) :
    ∀ ℓ ∈ eraseFrom I S X.1 X.2 α, ℓ.proc ∉ S := by
  induction α generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := (astep_eq_some I).1 hs
      obtain ⟨Z1, Z2⟩ := Z; simp only at h1 h2; subst h2
      have hIZ := hI.step h1
      intro ℓ' hℓ'
      simp only [eraseFrom, h1] at hℓ'
      rcases List.mem_append.1 hℓ' with hm | hm
      · split_ifs at hm with hd
        · simp only [List.mem_singleton] at hm; subst hm
          intro hS
          exact Finset.disjoint_left.1 hd ((hI.step h1).self_mem ℓ'.proc) hS
        · simp at hm
      · exact ih h hIZ ℓ' hm

/-- Labels of a process that is never aware of `S` are all kept. -/
lemma eraseFrom_filter_proc {S : Finset P} {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V}
    {α : List (Label P A)} (h : arunFrom I X α = some Y) (q : P) (hq : Disjoint (Y.2.aw q) S) :
    (eraseFrom I S X.1 X.2 α).filter (fun ℓ => decide (ℓ.proc = q)) =
      α.filter (fun ℓ => decide (ℓ.proc = q)) := by
  induction α generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := (astep_eq_some I).1 hs
      obtain ⟨Z1, Z2⟩ := Z; simp only at h1 h2; subst h2
      simp only [eraseFrom, h1]
      have ih' := ih h
      by_cases hpq : ℓ.proc = q
      · have hd : Disjoint ((gstep I X.1 X.2 ℓ).aw ℓ.proc) S := by
          rw [hpq]
          exact Finset.disjoint_of_subset_left (arunFrom_aw_mono h q) hq
        rw [if_pos hd]
        simp [List.filter_cons, hpq, ih']
      · split_ifs <;> simp [List.filter_cons, hpq, ih']

/-! ### Hidden processes -/

/-- `H` is a set of *hidden* processes: no process other than `x` is aware of `x ∈ H`. -/
def Hidden (G : Ghost P ι V) (H : Finset P) : Prop := ∀ x ∈ H, ∀ q, x ∈ G.aw q → q = x

lemma Hidden.disjoint {G : Ghost P ι V} {H : Finset P} (hH : Hidden G H) {q : P} (hq : q ∉ H) :
    Disjoint (G.aw q) H :=
  Finset.disjoint_right.2 fun x hx hxq => hq (hH x hx q hxq ▸ hx)

lemma Hidden.mono {G : Ghost P ι V} {H H' : Finset P} (hH : Hidden G H) (h : H' ⊆ H) :
    Hidden G H' := fun x hx => hH x (h hx)

/-- For hidden `H`, entries are kept by the erasure iff their writer is outside `H`. -/
lemma Hidden.filter_hist {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {H : Finset P}
    (hI : Inv I C G) (hH : Hidden G H) (i : ι) :
    (G.hist i).filter (fun e => Disjoint e.aw H) = (G.hist i).filter (fun e => e.proc ∉ H) := by
  apply List.filter_congr
  intro e he
  have := hI.entry i e he
  by_cases hp : e.proc ∈ H
  · simp only [hp, not_true_eq_false, decide_false, decide_eq_false_iff_not]
    exact fun hd => Finset.disjoint_left.1 hd this.2 hp
  · simp only [hp, not_false_eq_true, decide_true, decide_eq_true_eq]
    exact Finset.disjoint_of_subset_left this.1 (hH.disjoint hp)

/-- Erasing hidden processes removes exactly their labels. -/
lemma eraseFrom_eq_filter {S : Finset P} {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V}
    {α : List (Label P A)} (h : arunFrom I X α = some Y) (hI : Inv I X.1 X.2)
    (hS : ∀ q, q ∉ S → Disjoint (Y.2.aw q) S) :
    eraseFrom I S X.1 X.2 α = α.filter (fun ℓ => decide (ℓ.proc ∉ S)) := by
  induction α generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ α ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := (astep_eq_some I).1 hs
      obtain ⟨Z1, Z2⟩ := Z; simp only at h1 h2; subst h2
      simp only [eraseFrom, h1]
      have ih' := ih h (hI.step h1)
      rw [ih']
      by_cases hp : ℓ.proc ∈ S
      · have hd : ¬ Disjoint ((gstep I X.1 X.2 ℓ).aw ℓ.proc) S :=
          fun hd => Finset.disjoint_left.1 hd ((hI.step h1).self_mem ℓ.proc) hp
        simp [hd, hp, List.filter_cons]
      · have hd : Disjoint ((gstep I X.1 X.2 ℓ).aw ℓ.proc) S :=
          Finset.disjoint_of_subset_left (arunFrom_aw_mono h ℓ.proc) (hS _ hp)
        simp [hd, hp, List.filter_cons]

/-- **Erasing hidden processes** (a sound version of Claim 1 of Hendler–Khait): removing all
labels of a hidden set `H` yields an execution in which every other process has the same local
state, pending operation and awareness set, and the history of every base object loses exactly
the entries written by `H`. -/
theorem arun_filter_hidden {H : Finset P} {α : List (Label P A)} {C : Config A (RWC ι V v₀) P L}
    {G : Ghost P ι V} (h : arun I α = some (C, G)) (hH : Hidden G H) :
    ∃ C' G', arun I (α.filter (fun ℓ => decide (ℓ.proc ∉ H))) = some (C', G') ∧
      (∀ q, q ∉ H → C'.loc q = C.loc q ∧ C'.pend q = C.pend q ∧ G'.aw q = G.aw q) ∧
      (∀ q, G'.aw q ⊆ G.aw q) ∧
      (∀ i, G'.hist i = (G.hist i).filter (fun e => e.proc ∉ H)) := by
  obtain ⟨C', G', h1, hR⟩ := arun_erase H h
  have heq : erase I H α = α.filter (fun ℓ => decide (ℓ.proc ∉ H)) :=
    eraseFrom_eq_filter (Y := (C, G)) h inv_init (fun q hq => hH.disjoint hq)
  rw [heq] at h1
  refine ⟨C', G', h1, fun q hq => ?_, hR.aw_sub, fun i => ?_⟩
  · have hd := hH.disjoint hq
    exact ⟨hR.loc q hd, hR.pend q hd, hR.aw_eq q hd⟩
  · rw [hR.hist, Hidden.filter_hist (arun_inv h) hH]

end Cslib.SharedMemory.Awareness
