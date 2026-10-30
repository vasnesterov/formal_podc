import Papers.PODC2021.BFTInBlockDAG.Shim

/-!
# The interpretation of a block DAG is an execution over authenticated links

This file proves what *does* hold of the embedding (safety part of Lemma 4.3 and Theorem 5.1).

Fix a reachable state, a correct server `s` and a label `ℓ`. Replaying, in the order in which `s`
inserted them into its block DAG `G_s`, the events of every block built by a correct server (its
requests for `ℓ`, then its delivered messages `B.Ms[in, ℓ]` in the order `<_M`) gives a list of
events `traceOf` with:
* `trace_linkSafe`: it is an execution over authenticated links (`LinkSafe`): every event is at a
  correct server, every delivered message is addressed to its receiver, and a delivered message
  from a correct sender was sent before by that sender (Lemma 4.3 (3), authenticity);
* `trace_exec`: the process states, the sent messages and the interface (requests and indications)
  of this execution are those of the interpretation of `G_s` (so in particular `shim(P)` at a
  correct server `a` indicates exactly what process `a` indicates in this execution, and process
  `a` is requested exactly what is written in `a`'s blocks);
* `lemma_4_3_2_correct`: deliveries of messages with a *correct* sender are not duplicated, if the
  protocol never sends the same message twice (Cachin et al.'s convention that messages are
  unique). For Byzantine senders no duplication fails (`Counterexample.lean`).

Other ingredients: the insertion order of `G` is topological (`reachable_topo`); a correct server's
blocks form a chain (`own_chain`); Lemma 4.3 (3) at the block level (`lemma_4_3_3`).
-/

set_option linter.unusedSectionVars false

namespace Podc.BFTInBlockDAG

open Block

variable {S L R : Type} [DecidableEq S] [DecidableEq L] [DecidableEq R] {Byz : Set S}

/-! ### The insertion order is topological -/

/-- Every strict ancestor of a block of `l` appears before it in `l`. -/
def TopoT (l : List (Block S L R)) : Prop :=
  ∀ p B q, l = p ++ B :: q → ∀ C, Relation.TransGen Edge C B → C ∈ p

theorem eq_nil_or_append_singleton_of_append_singleton {α : Type*} {l p q : List α} {x B : α}
    (h : l ++ [x] = p ++ B :: q) : (q = [] ∧ l = p ∧ x = B) ∨ ∃ q', q = q' ++ [x] ∧ l = p ++ B :: q' := by
  rcases List.eq_nil_or_concat q with rfl | ⟨q', y, rfl⟩
  · left
    simp only [List.append_singleton_inj] at h ⊢
    simpa using h
  · right
    have h' : l ++ [x] = (p ++ B :: q') ++ [y] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h2
    exact ⟨q', by rw [h2]; simp, h1⟩

theorem TopoT.append {l : List (Block S L R)} (h : TopoT l) {B : Block S L R}
    (hB : ∀ C, Relation.TransGen Edge C B → C ∈ l) : TopoT (l ++ [B]) := by
  intro p D q hl C hC
  rcases eq_nil_or_append_singleton_of_append_singleton hl with ⟨-, rfl, rfl⟩ | ⟨q', -, hl'⟩
  · exact hB C hC
  · exact h p D q' hl' C hC

theorem topo_of_dag {l : List (Block S L R)} (hl : IsBlockDAG {x | x ∈ l}) {B : Block S L R}
    (hB : ∀ C ∈ B.preds, C ∈ l) : ∀ C, Relation.TransGen Edge C B → C ∈ l := by
  intro C hC
  obtain ⟨D, hCD, hD⟩ := Relation.TransGen.tail'_iff.1 hC
  exact hl.mem_of_reflTransGen (hB D hD) hCD

/-- The insertion order of the block DAG of a correct server is a topological order. -/
theorem reachable_topo {σ : Sys S L R} (h : Reachable Byz σ) :
    ∀ s ∉ Byz, TopoT (σ.loc s).log := by
  induction h with
  | refl => intro s _ p B q h; simp [Sys.init] at h
  | tail hr hstep ih =>
    rename_i σ σ'
    obtain ⟨e, hen, rfl⟩ := hstep
    have hI := reachable_inv hr
    intro s hs
    cases e with
    | request a ℓ r =>
      simp only [apply, Sys.upd]
      by_cases h : s = a
      · subst h; simpa using ih s hs
      · simpa [Function.update_of_ne h] using ih s hs
    | recv a src p =>
      cases p with
      | blk B =>
        simp only [apply]
        split_ifs
        · exact ih s hs
        · simp only [Sys.upd]
          by_cases h : s = a
          · subst h; simpa using ih s hs
          · simpa [Function.update_of_ne h] using ih s hs
      | fwd B =>
        simp only [apply]
        split_ifs <;> exact ih s hs
    | validate a B =>
      simp only [apply, Sys.upd]
      by_cases h : s = a
      · subst h
        simp only [Function.update_self]
        exact (ih s hs).append (topo_of_dag ((hI.loc s hs).dag) hen.2.2.2)
      · simpa [Function.update_of_ne h] using ih s hs
    | askFwd a B' B => exact ih s hs
    | disseminate a =>
      simp only [apply]
      by_cases h : s = a
      · subst h
        simp only [Function.update_self]
        exact (ih s hs).append (topo_of_dag ((hI.loc s hs).dag) (lemma_A_4 hI hs).2)
      · simpa [Function.update_of_ne h] using ih s hs
    | byz b dst p => exact ih s hs

/-- In a topologically ordered list without duplicates, a block is not before its ancestors. -/
theorem TopoT.not_mem_of_transGen {l : List (Block S L R)} (h : TopoT l) (hnd : l.Nodup)
    {p q : List (Block S L R)} {B X : Block S L R} (hl : l = p ++ B :: q) (hX : X ∈ p)
    (hBX : Relation.TransGen Edge B X) : False := by
  obtain ⟨p₁, p₂, rfl⟩ := List.mem_iff_append.1 hX
  have hB : B ∈ p₁ := h p₁ X (p₂ ++ B :: q) (by rw [hl]; simp) B hBX
  rw [hl] at hnd
  have : B ∈ p₁ ++ X :: p₂ := List.mem_append_left _ hB
  exact (List.nodup_append.1 hnd).2.2 B this B List.mem_cons_self rfl

/-! ### The blocks of a correct server form a chain -/

theorem own_nodup_k {σ : Sys S L R} {a : S} (h : LInv Byz σ a) :
    ∀ X ∈ (σ.loc a).own, ∀ Y ∈ (σ.loc a).own, X.k = Y.k → X = Y := by
  have hnd : ((σ.loc a).own.map Block.k).Nodup := by rw [h.own_k]; exact List.nodup_range
  intro X hX Y hY hk
  exact List.inj_on_of_nodup_map hnd hX hY hk

/-- The parent of a non-genesis block of a correct server is its previous block. -/
theorem own_parent {σ : Sys S L R} (hI : Inv Byz σ) {a : S} (ha : a ∉ Byz) {B : Block S L R}
    (hB : B ∈ (σ.loc a).own) (hk : B.k ≠ 0) :
    ∃ C ∈ (σ.loc a).own, B.parent? = some C ∧ IsParent C B := by
  have h := hI.loc a ha
  have hBlog := h.own_sub B hB
  obtain ⟨C, hC, hpar⟩ := exists_parent?_of_locallyValid (h.dag.1 B hBlog).locallyValid hk
  refine ⟨C, ?_, hC, hpar⟩
  exact hI.mem_own_of_log ha (h.dag.2 B hBlog C hpar.1) (hpar.2.1.trans (h.own_n B hB))

/-- Earlier blocks of a correct server are ancestors of later ones. -/
theorem own_chain {σ : Sys S L R} (hI : Inv Byz σ) {a : S} (ha : a ∉ Byz) :
    ∀ n, ∀ X ∈ (σ.loc a).own, ∀ Y ∈ (σ.loc a).own, Y.k = X.k + n + 1 →
      Relation.TransGen Edge X Y := by
  intro n
  induction n with
  | zero =>
    intro X hX Y hY hk
    obtain ⟨C, hC, -, hpar⟩ := own_parent hI ha hY (by omega)
    have : C = X := own_nodup_k (hI.loc a ha) C hC X hX (by have := hpar.2.2; omega)
    subst this
    exact Relation.TransGen.single hpar.1
  | succ n ih =>
    intro X hX Y hY hk
    obtain ⟨C, hC, -, hpar⟩ := own_parent hI ha hY (by omega)
    exact (ih X hX C hC (by have := hpar.2.2; omega)).tail hpar.1

theorem own_transGen_of_lt {σ : Sys S L R} (hI : Inv Byz σ) {a : S} (ha : a ∉ Byz)
    {X Y : Block S L R} (hX : X ∈ (σ.loc a).own) (hY : Y ∈ (σ.loc a).own) (hk : X.k < Y.k) :
    Relation.TransGen Edge X Y :=
  own_chain hI ha (Y.k - X.k - 1) X hX Y hY (by omega)

/-! ### Replaying the interpretation -/

section Replay

variable {M I σ : Type} [LinearOrder M] (P : Protocol S L R M I σ) (ℓ : L)

/-- The state from which line 4 of Algorithm 2 starts at `B`. -/
def startSt (B : Block S L R) : σ :=
  match B.parent? with
  | some C => (interp P ℓ C).st
  | none => P.init ℓ B.n

/-- The inputs fed to `B.PIs[ℓ]` at `B`: the requests (lines 5–6), then the delivered messages
in the order `<_M` (lines 10–11). -/
def blockInputs (B : Block S L R) : List (Input R M) :=
  ((B.rs.filter fun x => decide (x.1 = ℓ)).map fun x => Input.req x.2) ++
    (interp P ℓ B).inn.map Input.recv

theorem interp_run (B : Block S L R) :
    (interp P ℓ B).st = (P.run (startSt P ℓ B) (blockInputs P ℓ B)).1 ∧
    (interp P ℓ B).out = (P.run (startSt P ℓ B) (blockInputs P ℓ B)).2.1 ∧
    (interp P ℓ B).ind = (P.run (startSt P ℓ B) (blockInputs P ℓ B)).2.2 := by
  rw [blockInputs, inn_interp]
  rw [interp_eq]
  unfold interpCore startSt
  cases hp : B.parent? with
  | none => simp
  | some C =>
    have hC : C ∈ B.preds := (parent?_eq_some hp).1
    simp [lookup_map_self hC]

theorem mem_req_blockInputs {B : Block S L R} {q : R} :
    Input.req q ∈ blockInputs P ℓ B ↔ (ℓ, q) ∈ B.rs := by
  simp only [blockInputs, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨⟨ℓ', q'⟩, ⟨hx, rfl⟩, h⟩ | ⟨m, -, h⟩)
    · cases h; exact hx
    · cases h
  · intro h
    exact Or.inl ⟨(ℓ, q), ⟨h, rfl⟩, rfl⟩

variable (Byz) [DecidablePred (· ∈ Byz)]

/-- The events of a block: none for a Byzantine builder; otherwise its inputs, at its builder. -/
def blockEvs (B : Block S L R) : List (S × Input R M) :=
  if B.n ∈ Byz then [] else (blockInputs P ℓ B).map fun i => (B.n, i)

/-- The events of a list of blocks (e.g. the block DAG of a server, in insertion order). -/
def traceOf (l : List (Block S L R)) : List (S × Input R M) := l.flatMap (blockEvs Byz P ℓ)

variable {Byz}

/-- The interface events produced by server `a` handling `ins` from state `st`. -/
def ifaceRun (a : S) : σ → List (Input R M) → List (S × (R ⊕ I))
  | _, [] => []
  | st, i :: is =>
    ((match i with | .req q => [(a, Sum.inl q)] | .recv _ => []) ++
      (P.step st i).2.2.map fun j => (a, Sum.inr j)) ++ ifaceRun a (P.step st i).1 is

theorem mem_ifaceRun (a : S) (st : σ) (ins : List (Input R M)) (z : S × (R ⊕ I)) :
    z ∈ ifaceRun P a st ins ↔ z.1 = a ∧ ((∃ q, z.2 = Sum.inl q ∧ Input.req q ∈ ins) ∨
        ∃ j, z.2 = Sum.inr j ∧ j ∈ (P.run st ins).2.2) := by
  obtain ⟨z₁, z₂⟩ := z
  induction ins generalizing st with
  | nil => simp [ifaceRun]
  | cons i is ih =>
    simp only [ifaceRun, List.mem_append, ih, Protocol.run, List.mem_map, List.mem_cons]
    cases i with
    | req q =>
      simp only [List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ((⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩) | ⟨rfl, ⟨q', rfl, hq⟩ | ⟨j, rfl, hj⟩⟩)
        · exact ⟨rfl, Or.inl ⟨q, rfl, Or.inl rfl⟩⟩
        · exact ⟨rfl, Or.inr ⟨j, rfl, Or.inl hj⟩⟩
        · exact ⟨rfl, Or.inl ⟨q', rfl, Or.inr hq⟩⟩
        · exact ⟨rfl, Or.inr ⟨j, rfl, Or.inr hj⟩⟩
      · rintro ⟨rfl, ⟨q', rfl, hq | hq⟩ | ⟨j, rfl, hj⟩⟩
        · cases hq; exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr ⟨rfl, Or.inl ⟨q', rfl, hq⟩⟩
        · rcases hj with hj | hj
          · exact Or.inl (Or.inr ⟨j, hj, rfl, rfl⟩)
          · exact Or.inr ⟨rfl, Or.inr ⟨j, rfl, hj⟩⟩
    | recv m =>
      simp only [List.not_mem_nil, false_or, Prod.mk.injEq]
      constructor
      · rintro (⟨j, hj, rfl, rfl⟩ | ⟨rfl, ⟨q', rfl, hq⟩ | ⟨j, rfl, hj⟩⟩)
        · exact ⟨rfl, Or.inr ⟨j, rfl, Or.inl hj⟩⟩
        · exact ⟨rfl, Or.inl ⟨q', rfl, Or.inr hq⟩⟩
        · exact ⟨rfl, Or.inr ⟨j, rfl, Or.inr hj⟩⟩
      · rintro ⟨rfl, ⟨q', rfl, hq | hq⟩ | ⟨j, rfl, hj⟩⟩
        · cases hq
        · exact Or.inr ⟨rfl, Or.inl ⟨q', rfl, hq⟩⟩
        · rcases hj with hj | hj
          · exact Or.inl ⟨j, hj, rfl, rfl⟩
          · exact Or.inr ⟨rfl, Or.inr ⟨j, rfl, hj⟩⟩

/-- Replaying events that all happen at the same server `a`. -/
theorem foldl_execStep_map (a : S) (ins : List (Input R M))
    (x : (S → σ) × List (S × M) × List (S × (R ⊕ I))) :
    (ins.map fun i => (a, i)).foldl (execStep P) x =
      (Function.update x.1 a (P.run (x.1 a) ins).1,
        x.2.1 ++ (P.run (x.1 a) ins).2.1.map (fun m => (a, m)),
        x.2.2 ++ ifaceRun P a (x.1 a) ins) := by
  induction ins generalizing x with
  | nil => simp [ifaceRun]
  | cons i ins ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    have hst : (execStep P x (a, i)).1 a = (P.step (x.1 a) i).1 := by
      simp [execStep]
    rw [hst]
    cases i <;> simp [execStep, Protocol.run, ifaceRun, List.append_assoc]

/-- A block of the block DAG of a correct server, built by a correct server `a`, is one of `a`'s
own blocks. -/
theorem mem_own_of_mem_log {st : Sys S L R} (hI : Inv Byz st) {s a : S} (hs : s ∉ Byz)
    (ha : a ∉ Byz) {X : Block S L R} (hX : X ∈ (st.loc s).log) (hn : X.n = a) :
    X ∈ (st.loc a).own :=
  hI.mem_own ha ((hI.loc s hs).auth X (Or.inl hX)) hn

/-- In the insertion order, the earlier blocks of a correct server `a` have smaller sequence
numbers. -/
theorem k_lt_of_before {st : Sys S L R} (hr : Reachable Byz st) {s a : S} (hs : s ∉ Byz)
    (ha : a ∉ Byz) {p q : List (Block S L R)} {B : Block S L R}
    (hl : (st.loc s).log = p ++ B :: q) (hB : B.n = a) :
    ∀ X ∈ p, X.n = a → X.k < B.k := by
  have hI := reachable_inv hr
  have hnd := (hI.loc s hs).log_nodup
  have htopo := reachable_topo hr s hs
  intro X hX hXn
  have hXlog : X ∈ (st.loc s).log := by rw [hl]; exact List.mem_append_left _ hX
  have hBlog : B ∈ (st.loc s).log := by rw [hl]; simp
  have hXo := mem_own_of_mem_log hI hs ha hXlog hXn
  have hBo := mem_own_of_mem_log hI hs ha hBlog hB
  have hXB : X ≠ B := by
    rintro rfl
    rw [hl] at hnd
    exact (List.nodup_append.1 hnd).2.2 X hX X List.mem_cons_self rfl
  rcases lt_trichotomy X.k B.k with h | h | h
  · exact h
  · exact absurd (own_nodup_k (hI.loc a ha) X hXo B hBo h) hXB
  · exact (htopo.not_mem_of_transGen hnd hl hX (own_transGen_of_lt hI ha hBo hXo h)).elim

variable (Byz)

/-- The invariant of the replay of a prefix `p` of a block DAG. -/
def RepInv (p : List (Block S L R)) (y : (S → σ) × List (S × M) × List (S × (R ⊕ I))) : Prop :=
  (∀ a ∉ Byz, ((∀ X ∈ p, X.n ≠ a) ∧ y.1 a = P.init ℓ a) ∨
     (∃ X ∈ p, X.n = a ∧ (∀ Y ∈ p, Y.n = a → Y.k ≤ X.k) ∧ y.1 a = (interp P ℓ X).st)) ∧
  y.2.1 = p.flatMap (fun B => if B.n ∈ Byz then [] else (interp P ℓ B).out.map fun m => (B.n, m)) ∧
  y.2.2 = p.flatMap (fun B => if B.n ∈ Byz then [] else
    ifaceRun P B.n (startSt P ℓ B) (blockInputs P ℓ B))

variable {Byz}

/-- Before the events of a correct server's block `B`, the replayed state of its builder is the
start state of `B` (its parent's state, or the initial state for a genesis block). -/
theorem start_eq {st : Sys S L R} (hr : Reachable Byz st) {s a : S} (hs : s ∉ Byz)
    (ha : a ∉ Byz) {p q : List (Block S L R)} {B : Block S L R}
    (hl : (st.loc s).log = p ++ B :: q) (hB : B.n = a)
    {y : (S → σ) × List (S × M) × List (S × (R ⊕ I))} (hy : RepInv Byz P ℓ p y) :
    y.1 a = startSt P ℓ B := by
  have hI := reachable_inv hr
  have hlt := k_lt_of_before hr hs ha hl hB
  have hBlog : B ∈ (st.loc s).log := by rw [hl]; simp
  have hBo := mem_own_of_mem_log hI hs ha hBlog hB
  unfold startSt
  by_cases hk : B.k = 0
  · have hnone : B.parent? = none := by
      cases h : B.parent? with
      | none => rfl
      | some C => exact absurd (parent?_eq_some h) (not_isParent_of_k_eq_zero hk)
    rw [hnone, hB]
    rcases hy.1 a ha with ⟨-, h⟩ | ⟨X, hX, hXn, -, -⟩
    · exact h
    · have := hlt X hX hXn; omega
  · obtain ⟨C, hCo, hC, hpar⟩ := own_parent hI ha hBo hk
    rw [hC]
    have hCp : C ∈ p := reachable_topo hr s hs p B q hl C (Relation.TransGen.single hpar.1)
    have hCn : C.n = a := hpar.2.1.trans hB
    rcases hy.1 a ha with ⟨h, -⟩ | ⟨X, hX, hXn, hmax, h⟩
    · exact absurd hCn (h C hCp)
    · have hXlog : X ∈ (st.loc s).log := by rw [hl]; exact List.mem_append_left _ hX
      have hXo := mem_own_of_mem_log hI hs ha hXlog hXn
      have h1 := hmax C hCp hCn
      have h2 := hlt X hX hXn
      have : X = C := own_nodup_k (hI.loc a ha) X hXo C hCo (by have := hpar.2.2; omega)
      rw [h, this]

/-- The replay of every prefix of the block DAG of a correct server satisfies `RepInv`. -/
theorem replay {st : Sys S L R} (hr : Reachable Byz st) {s : S} (hs : s ∉ Byz) :
    ∀ p q, (st.loc s).log = p ++ q → RepInv Byz P ℓ p (exec P ℓ (traceOf Byz P ℓ p)) := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro q _
    refine ⟨fun a _ => Or.inl ⟨by simp, rfl⟩, by simp [traceOf, exec], by simp [traceOf, exec]⟩
  | append_singleton p B ih =>
    intro q hl
    have hl' : (st.loc s).log = p ++ B :: q := by rw [hl]; simp
    have hy := ih (B :: q) hl'
    set y := exec P ℓ (traceOf Byz P ℓ p)
    have htr : exec P ℓ (traceOf Byz P ℓ (p ++ [B])) = (blockEvs Byz P ℓ B).foldl (execStep P) y := by
      simp [traceOf, List.flatMap_append, exec_append, y]
    rw [htr]
    by_cases hb : B.n ∈ Byz
    · have hev : blockEvs Byz P ℓ B = [] := by simp [blockEvs, hb]
      rw [hev, List.foldl_nil]
      refine ⟨fun a ha => ?_, by simp [hy.2.1, hb], by simp [hy.2.2, hb]⟩
      have hBa : B.n ≠ a := fun h => ha (h ▸ hb)
      rcases hy.1 a ha with ⟨h1, h2⟩ | ⟨X, hX, hXn, hmax, h⟩
      · refine Or.inl ⟨fun X hX => ?_, h2⟩
        rcases List.mem_append.1 hX with hX | hX
        · exact h1 X hX
        · rw [List.mem_singleton.1 hX]; exact hBa
      · refine Or.inr ⟨X, List.mem_append_left _ hX, hXn, fun Y hY hYn => ?_, h⟩
        rcases List.mem_append.1 hY with hY | hY
        · exact hmax Y hY hYn
        · rw [List.mem_singleton.1 hY] at hYn; exact absurd hYn hBa
    · have hev : blockEvs Byz P ℓ B = (blockInputs P ℓ B).map fun i => (B.n, i) := by
        simp [blockEvs, hb]
      rw [hev, foldl_execStep_map]
      have hstart := start_eq P ℓ hr hs hb hl' rfl hy
      rw [hstart]
      obtain ⟨hrst, hrout, -⟩ := interp_run P ℓ B
      refine ⟨fun a ha => ?_, ?_, ?_⟩
      · by_cases hBa : B.n = a
        · subst hBa
          refine Or.inr ⟨B, List.mem_append_right _ (List.mem_singleton_self _), rfl,
            fun Y hY hYn => ?_, ?_⟩
          · rcases List.mem_append.1 hY with hY | hY
            · exact (k_lt_of_before hr hs hb hl' rfl Y hY hYn).le
            · rw [List.mem_singleton.1 hY]
          · simp only [Function.update_self, hrst]
        · simp only [Function.update_of_ne (Ne.symm hBa)]
          rcases hy.1 a ha with ⟨h1, h2⟩ | ⟨X, hX, hXn, hmax, h⟩
          · refine Or.inl ⟨fun X hX => ?_, h2⟩
            rcases List.mem_append.1 hX with hX | hX
            · exact h1 X hX
            · rw [List.mem_singleton.1 hX]; exact hBa
          · refine Or.inr ⟨X, List.mem_append_left _ hX, hXn, fun Y hY hYn => ?_, h⟩
            rcases List.mem_append.1 hY with hY | hY
            · exact hmax Y hY hYn
            · rw [List.mem_singleton.1 hY] at hYn; exact absurd hYn hBa
      · simp [hy.2.1, hb, hrout]
      · simp [hy.2.2, hb]

theorem flatMap_eq_append_cons {α β : Type*} (f : α → List β) :
    ∀ (l : List α) (t₁ t₂ : List β) (e : β), l.flatMap f = t₁ ++ e :: t₂ →
      ∃ p B q u₁ u₂, l = p ++ B :: q ∧ f B = u₁ ++ e :: u₂ ∧ t₁ = p.flatMap f ++ u₁ := by
  intro l
  induction l with
  | nil => intro t₁ t₂ e h; simp at h
  | cons B l ih =>
    intro t₁ t₂ e h
    rw [List.flatMap_cons] at h
    rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · -- `t₁` extends past `f B`
      have : l.flatMap f = a' ++ e :: t₂ := h2
      obtain ⟨p, B', q, u₁, u₂, rfl, hf, rfl⟩ := ih a' t₂ e this
      exact ⟨B :: p, B', q, u₁, u₂, rfl, hf, by simp [h1]⟩
    · -- `e` is inside `f B`
      cases c' with
      | nil =>
        simp only [List.append_nil] at h1
        simp only [List.nil_append] at h2
        obtain ⟨p, B', q, u₁, u₂, hl, hf, ht⟩ := ih [] t₂ e (by simpa using h2.symm)
        obtain ⟨hp, hu⟩ := List.append_eq_nil_iff.1 ht.symm
        refine ⟨B :: p, B', q, u₁, u₂, by simp [hl], hf, ?_⟩
        rw [List.flatMap_cons, hp, hu, h1]; simp
      | cons e' c'' =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨[], B, l, t₁, c'', rfl, h1, by simp⟩

theorem exec_sent_prefix (P : Protocol S L R M I σ) :
    ∀ (t : List (S × Input R M)) (x : (S → σ) × List (S × M) × List (S × (R ⊕ I))),
      x.2.1 <+: (t.foldl (execStep P) x).2.1 := by
  intro t
  induction t with
  | nil => intro x; exact List.prefix_refl _
  | cons e t ih =>
    intro x
    exact (List.prefix_append _ _).trans (ih (execStep P x e))

theorem mem_blockEvs {B : Block S L R} {e : S × Input R M} (h : e ∈ blockEvs Byz P ℓ B) :
    B.n ∉ Byz ∧ e.1 = B.n ∧ e.2 ∈ blockInputs P ℓ B := by
  unfold blockEvs at h
  split_ifs at h with hb
  · simp at h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    exact ⟨hb, rfl, hi⟩

theorem recv_mem_blockInputs {B : Block S L R} {m : M}
    (h : Input.recv m ∈ blockInputs P ℓ B) : m ∈ (interp P ℓ B).inn := by
  simp only [blockInputs, List.mem_append, List.mem_map] at h
  rcases h with ⟨_, -, h⟩ | ⟨m', hm', h⟩
  · cases h
  · cases h; exact hm'

/-- **Lemma 4.3 (3)** (authenticity), and the safety part of the link abstraction: the replay of
the interpretation of the block DAG of a correct server is an execution over authenticated links:
events only at correct servers, deliveries addressed to the receiver, and a delivered message
with a correct sender was sent before by that sender. -/
theorem trace_linkSafe {owner : σ → S} (hP : P.Owned owner) {st : Sys S L R}
    (hr : Reachable Byz st) {s : S} (hs : s ∉ Byz) :
    LinkSafe P ℓ Byz (traceOf Byz P ℓ (st.loc s).log) := by
  have hI := reachable_inv hr
  have hdag := (hI.loc s hs).dag
  refine ⟨fun e he => ?_, fun t₁ s₂ m t₂ h => ?_⟩
  · obtain ⟨B, -, hB⟩ := List.mem_flatMap.1 he
    obtain ⟨hb, he1, -⟩ := mem_blockEvs P ℓ hB
    rw [he1]; exact hb
  · obtain ⟨p, B, q, u₁, u₂, hl, hf, ht⟩ :=
      flatMap_eq_append_cons (blockEvs Byz P ℓ) _ t₁ t₂ _ h
    have hmem : (s₂, Input.recv m) ∈ blockEvs Byz P ℓ B := by rw [hf]; simp
    obtain ⟨hb, rfl, hin⟩ := mem_blockEvs P ℓ hmem
    have hinn := recv_mem_blockInputs P ℓ hin
    obtain ⟨-, hrec, C, hC, hmC⟩ := (mem_inn P).1 hinn
    refine ⟨hrec, fun hsend => ?_⟩
    have hBlog : B ∈ (st.loc s).log := by rw [hl]; simp
    have hClog := hdag.2 B hBlog C hC
    have hsC : P.sender m = C.n := sender_of_mem_out P hP (hdag.1 C hClog) hmC
    have hCp : C ∈ p := reachable_topo hr s hs p B q hl C (Relation.TransGen.single hC)
    -- the replay of `p` has sent `m` from `C.n`
    have hrep := (replay P ℓ hr hs p (B :: q) hl).2.1
    have h1 : (C.n, m) ∈ (exec P ℓ (traceOf Byz P ℓ p)).2.1 := by
      rw [hrep, List.mem_flatMap]
      refine ⟨C, hCp, ?_⟩
      rw [ite_eq_right (hsC ▸ hsend)]
      exact List.mem_map_of_mem hmC
    rw [ht, exec_append, hsC]
    exact (exec_sent_prefix P u₁ _).subset h1

/-- The replayed execution reproduces the interpretation: the state of every correct server `a`
is the state at its last block (or its initial state), the sent messages are the out-buffers of
the blocks of correct servers, and its interface events are exactly the requests written in, and
the indications triggered at, the blocks of correct servers. -/
theorem trace_exec {st : Sys S L R} (hr : Reachable Byz st) {s : S} (hs : s ∉ Byz) :
    RepInv Byz P ℓ (st.loc s).log (exec P ℓ (traceOf Byz P ℓ (st.loc s).log)) ∧
    ∀ z, z ∈ (exec P ℓ (traceOf Byz P ℓ (st.loc s).log)).2.2 ↔
      ∃ B ∈ (st.loc s).log, B.n ∉ Byz ∧ z.1 = B.n ∧
        ((∃ r, z.2 = Sum.inl r ∧ (ℓ, r) ∈ B.rs) ∨ ∃ i, z.2 = Sum.inr i ∧ i ∈ (interp P ℓ B).ind) := by
  have h := replay P ℓ hr hs (st.loc s).log [] (by simp)
  refine ⟨h, fun z => ?_⟩
  rw [h.2.2, List.mem_flatMap]
  refine exists_congr fun B => and_congr_right fun _ => ?_
  by_cases hb : B.n ∈ Byz
  · simp [hb]
  · rw [ite_eq_right hb, mem_ifaceRun, ← (interp_run P ℓ B).2.2]
    simp only [mem_req_blockInputs]
    simp [hb]

/-! ### No duplication for correct senders -/

/-- The protocol never sends the same message twice from a process (the convention of Cachin et
al. that messages are unique). -/
def SendUnique (P : Protocol S L R M I σ) : Prop :=
  ∀ ℓ a ins, (P.run (P.init ℓ a) ins).2.1.Nodup

/-- The replay, projected on one server `b`, is a run of `b`'s process on `b`'s inputs. -/
theorem exec_proj (tr : List (S × Input R M)) (b : S) :
    (exec P ℓ tr).1 b = (P.run (P.init ℓ b) ((tr.filter fun e => decide (e.1 = b)).map Prod.snd)).1 ∧
    ((exec P ℓ tr).2.1.filter fun x => decide (x.1 = b)).map Prod.snd =
      (P.run (P.init ℓ b) ((tr.filter fun e => decide (e.1 = b)).map Prod.snd)).2.1 := by
  induction tr using List.reverseRecOn with
  | nil => simp [exec]
  | append_singleton t e ih =>
    rw [exec_concat]
    by_cases he : e.1 = b
    · subst he
      have hf : ((t ++ [e]).filter fun x => decide (x.1 = e.1)).map Prod.snd =
          ((t.filter fun x => decide (x.1 = e.1)).map Prod.snd) ++ [e.2] := by simp
      rw [hf, Protocol.run_append]
      simp only [execStep, Function.update_self, List.filter_append, List.map_append]
      rw [← ih.1, ← ih.2]
      refine ⟨by simp [Protocol.run], ?_⟩
      simp [Protocol.run, List.filter_map, Function.comp_def]
    · have hf : ((t ++ [e]).filter fun x => decide (x.1 = b)).map Prod.snd =
          ((t.filter fun x => decide (x.1 = b)).map Prod.snd) := by simp [he]
      rw [hf]
      simp only [execStep, Function.update_of_ne (Ne.symm he), List.filter_append,
        List.map_append]
      refine ⟨ih.1, ?_⟩
      rw [← ih.2]
      simp [List.filter_map, Function.comp_def, he]

/-- With unique messages, a message is triggered at most at one block of a correct server. -/
theorem out_unique (hU : SendUnique P) {st : Sys S L R} (hr : Reachable Byz st) {s : S}
    (hs : s ∉ Byz) {C C' : Block S L R} (hC : C ∈ (st.loc s).log) (hC' : C' ∈ (st.loc s).log)
    (hn : C.n = C'.n) (hb : C.n ∉ Byz) {m : M} (hm : m ∈ (interp P ℓ C).out)
    (hm' : m ∈ (interp P ℓ C').out) : C = C' := by
  have hI := reachable_inv hr
  have hnd := (hI.loc s hs).log_nodup
  set b := C.n
  have hrep := (trace_exec P ℓ hr hs).1.2.1
  have hproj := (exec_proj P ℓ (traceOf Byz P ℓ (st.loc s).log) b).2
  have hu := hU ℓ b ((((traceOf Byz P ℓ (st.loc s).log)).filter fun e => decide (e.1 = b)).map
    Prod.snd)
  rw [← hproj, hrep] at hu
  have heq : ((((st.loc s).log.flatMap fun B => if B.n ∈ Byz then [] else
      (interp P ℓ B).out.map fun m => (B.n, m)).filter fun x => decide (x.1 = b)).map Prod.snd) =
      (st.loc s).log.flatMap fun B => if B.n = b ∧ B.n ∉ Byz then (interp P ℓ B).out else [] := by
    rw [List.filter_flatMap, List.map_flatMap]
    congr 1
    funext B
    by_cases h1 : B.n ∈ Byz
    · simp [h1]
    · by_cases h2 : B.n = b
      · rw [ite_eq_right h1, ite_eq_left ⟨h2, h1⟩, h2]
        simp [List.filter_map, Function.comp_def]
      · rw [ite_eq_right h1, ite_eq_right (fun h => h2 h.1)]
        simp [List.filter_map, Function.comp_def, h2]
  rw [heq, List.nodup_flatMap] at hu
  by_contra hne
  have hdis := hu.2.forall hC hC' hne
  have e1 : (if C.n = b ∧ C.n ∉ Byz then (interp P ℓ C).out else []) = (interp P ℓ C).out :=
    ite_eq_left ⟨rfl, hb⟩
  have e2 : (if C'.n = b ∧ C'.n ∉ Byz then (interp P ℓ C').out else []) = (interp P ℓ C').out :=
    ite_eq_left ⟨hn.symm, hn ▸ hb⟩
  change List.Disjoint (if C.n = b ∧ C.n ∉ Byz then (interp P ℓ C).out else [])
    (if C'.n = b ∧ C'.n ∉ Byz then (interp P ℓ C').out else []) at hdis
  rw [e1, e2] at hdis
  exact hdis hm hm'

/-- **Lemma 4.3 (2) for correct senders.** If messages are unique, a correct server never
receives a message with a correct sender twice (at two of its blocks). -/
theorem lemma_4_3_2_correct {owner : σ → S} (hP : P.Owned owner) (hU : SendUnique P)
    {st : Sys S L R} (hr : Reachable Byz st) {s : S} (hs : s ∉ Byz) {B B' : Block S L R}
    (hB : B ∈ (st.loc s).log) (hB' : B' ∈ (st.loc s).log) (hn : B.n = B'.n) (ha : B.n ∉ Byz)
    {m : M} (hm : m ∈ (interp P ℓ B).inn) (hm' : m ∈ (interp P ℓ B').inn)
    (hsend : P.sender m ∉ Byz) : B = B' := by
  have hI := reachable_inv hr
  have hdag := (hI.loc s hs).dag
  obtain ⟨-, -, C, hC, hmC⟩ := (mem_inn P).1 hm
  obtain ⟨-, -, C', hC', hmC'⟩ := (mem_inn P).1 hm'
  have hClog := hdag.2 B hB C hC
  have hClog' := hdag.2 B' hB' C' hC'
  have h1 := sender_of_mem_out P hP (hdag.1 C hClog) hmC
  have h2 := sender_of_mem_out P hP (hdag.1 C' hClog') hmC'
  have hCC : C = C' := out_unique P ℓ hU hr hs hClog hClog' (h1.symm.trans h2) (h1 ▸ hsend) hmC hmC'
  subst hCC
  -- `B`, `B'` are blocks of the correct server `a = B.n`, which references `C` at most once
  set a := B.n
  have hBo := mem_own_of_mem_log hI hs ha hB rfl
  have hBo' := mem_own_of_mem_log hI hs ha hB' hn.symm
  have hrefs := (List.nodup_append.1 (hI.loc a ha).refs_nodup).1
  rw [List.nodup_flatMap] at hrefs
  by_contra hne
  exact hrefs.2.forall hBo hBo' hne hC hC'

theorem nodup_inn (B : Block S L R) : (interp P ℓ B).inn.Nodup := by
  rw [inn_interp]
  split_ifs
  · exact (List.perm_insertionSort _ _).nodup_iff.2 (List.nodup_dedup _)
  · exact List.nodup_nil

theorem filter_isRecv_blockEvs (B : Block S L R) :
    (blockEvs Byz P ℓ B).filter (fun e => decide e.2.IsRecv) =
      if B.n ∈ Byz then [] else (interp P ℓ B).inn.map fun m => (B.n, Input.recv m) := by
  unfold blockEvs blockInputs
  split_ifs with hb
  · rfl
  · simp [List.filter_append, List.filter_map, Function.comp_def, Input.IsRecv]

/-- The replayed execution has no duplicate delivery of a message with a correct sender (if
messages are unique). -/
theorem trace_noDupCorrect {owner : σ → S} (hP : P.Owned owner) (hU : SendUnique P)
    {st : Sys S L R} (hr : Reachable Byz st) {s : S} (hs : s ∉ Byz) :
    NoDupCorrect P Byz (traceOf Byz P ℓ (st.loc s).log) := by
  have hI := reachable_inv hr
  have hnd := (hI.loc s hs).log_nodup
  unfold NoDupCorrect recvs traceOf
  rw [List.filter_flatMap, List.filter_flatMap, List.nodup_flatMap]
  refine ⟨fun B _ => ?_, ?_⟩
  · refine List.Nodup.filter _ ?_
    rw [filter_isRecv_blockEvs]
    split_ifs
    · exact List.nodup_nil
    · exact (nodup_inn P ℓ B).map fun m m' h => by simpa using h
  · refine List.Pairwise.imp_of_mem (fun {B B'} hB hB' hne => ?_) hnd
    intro e he he'
    rw [List.mem_filter, filter_isRecv_blockEvs] at he he'
    obtain ⟨he, hq⟩ := he
    obtain ⟨he', -⟩ := he'
    have hb : B.n ∉ Byz := by intro h; simp [h] at he
    have hb' : B'.n ∉ Byz := by intro h; simp [h] at he'
    rw [ite_eq_right hb] at he
    rw [ite_eq_right hb'] at he'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    obtain ⟨m', hm', he2⟩ := List.mem_map.1 he'
    simp only [Prod.mk.injEq, Input.recv.injEq] at he2
    obtain ⟨hn, hmm⟩ := he2
    subst m'
    have hsend : P.sender m ∉ Byz := by
      rw [@decide_eq_true_iff _ (Classical.propDecidable _)] at hq
      obtain ⟨m'', h1, h2⟩ := hq
      cases h1; exact h2
    exact hne (lemma_4_3_2_correct P ℓ hP hU hr hs hB hB' hn.symm hb hm hm' hsend)

end Replay

/-! ### Theorem 5.1, repaired -/

section Main

variable {M I σ : Type} [LinearOrder M] [DecidablePred (· ∈ Byz)]

/-- A property `Φ` of interface traces holds for `P` over authenticated links *that may duplicate
messages of Byzantine senders* (authenticated perfect links without APL2 for Byzantine senders). -/
def HoldsOverAL (P : Protocol S L R M I σ) (ℓ : L) (Byz : Set S)
    (Φ : List (S × (R ⊕ I)) → Prop) : Prop :=
  ∀ tr, LinkSafe P ℓ Byz tr → NoDupCorrect P Byz tr → Φ (exec P ℓ tr).2.2

/-- **Theorem 5.1, repaired (safety part).** Let `P` be a deterministic protocol whose messages
carry their sender and are unique, and let `Φ` be a property of interface traces that holds for
`P` over authenticated links that may duplicate Byzantine messages. Then for every reachable
state and every correct server `s`, the interpretation of `s`'s block DAG is an execution of `P`
whose interface trace satisfies `Φ`, in which
* process `s` indicates exactly what `shim(P)` at `s` indicates,
* every indication of a correct process `a` is also indicated by `shim(P)` at `a`,
* every request to a correct process `a` was made by the user of `shim(P)` at `a`.
Liveness (every request is eventually written into a block and seen by every correct server,
every message between correct servers is eventually delivered) is `lemma_A_17` and
`lemma_4_3_1` in `GossipLive.lean`. -/
theorem theorem_5_1_repaired (P : Protocol S L R M I σ) (ℓ : L) {owner : σ → S}
    (hP : P.Owned owner) (hU : SendUnique P) {Φ : List (S × (R ⊕ I)) → Prop}
    (hΦ : HoldsOverAL P ℓ Byz Φ) {st : Sys S L R} (hr : Reachable Byz st) {s : S}
    (hs : s ∉ Byz) :
    Φ (exec P ℓ (traceOf Byz P ℓ (st.loc s).log)).2.2 ∧
    (∀ i, (s, Sum.inr i) ∈ (exec P ℓ (traceOf Byz P ℓ (st.loc s).log)).2.2 ↔
      ShimIndicates P st s ℓ i) ∧
    (∀ a i, (a, Sum.inr i) ∈ (exec P ℓ (traceOf Byz P ℓ (st.loc s).log)).2.2 →
      ShimIndicates P st a ℓ i) ∧
    (∀ a r, (a, Sum.inl r) ∈ (exec P ℓ (traceOf Byz P ℓ (st.loc s).log)).2.2 →
      (ℓ, r) ∈ (st.loc a).reqs) := by
  have hI := reachable_inv hr
  have hchar := (trace_exec P ℓ hr hs).2
  refine ⟨hΦ _ (trace_linkSafe P ℓ hP hr hs) (trace_noDupCorrect P ℓ hP hU hr hs), fun i => ?_,
    fun a i h => ?_, fun a r h => ?_⟩
  · rw [hchar]
    constructor
    · rintro ⟨B, hB, -, hn, ⟨r, h, -⟩ | ⟨j, hj, hi⟩⟩
      · cases h
      · cases hj; exact ⟨B, hB, hn.symm, hi⟩
    · rintro ⟨B, hB, hn, hi⟩
      exact ⟨B, hB, hn ▸ hs, hn.symm, Or.inr ⟨i, rfl, hi⟩⟩
  · obtain ⟨B, hB, hb, hn, ⟨r, h, -⟩ | ⟨j, hj, hi⟩⟩ := (hchar _).1 h
    · cases h
    · cases hj
      simp only at hn
      subst hn
      have hBo := mem_own_of_mem_log hI hs hb hB rfl
      exact ⟨B, (hI.loc _ hb).own_sub B hBo, rfl, hi⟩
  · obtain ⟨B, hB, hb, hn, ⟨r', h', hr'⟩ | ⟨j, hj, -⟩⟩ := (hchar _).1 h
    · cases h'
      simp only at hn
      subst hn
      have hBo := mem_own_of_mem_log hI hs hb hB rfl
      rw [← (hI.loc _ hb).reqs]
      exact List.mem_append_left _ (List.mem_flatMap.2 ⟨B, hBo, hr'⟩)
    · cases hj

end Main

end Podc.BFTInBlockDAG
