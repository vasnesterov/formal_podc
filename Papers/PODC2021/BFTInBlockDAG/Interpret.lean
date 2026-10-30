import Papers.PODC2021.BFTInBlockDAG.Block

/-!
# Interpreting a deterministic protocol on a block DAG (Section 4, Algorithm 2)

* `Protocol`: a deterministic protocol `P` as a black box. A process instance of `P` for label `ℓ`
  and server `s` starts in `P.init ℓ s` (the paper's `new process P(ℓ, s)`); on an input (a request
  `r` or a received message `m`) it moves to a new state and returns the messages and indications
  triggered by this input (`P.step`). Messages carry a `sender` and a `receiver`.
* `interp P ℓ B : Res`: the canonical value of `B.PIs[ℓ]`, `B.Ms[out, ℓ]`, `B.Ms[in, ℓ]` and the
  indications at `B` after Algorithm 2 interpreted `B` (lines 4–12), defined by structural recursion
  over the DAG below `B`:
  - line 4: start from the parent's state, or from `P.init ℓ B.n` for a block without parent;
  - lines 5–6: feed the requests `(ℓ, r) ∈ B.rs`, in order;
  - lines 7–11: if a strict ancestor of `B` carries a request for `ℓ`, collect into `Ms[in, ℓ]` the
    set of messages `m ∈ Bᵢ.Ms[out, ℓ]` (`Bᵢ ∈ B.preds`) with `m.receiver = B.n`, and feed them in the
    order `<_M`.
  Line 6 of the paper *assigns* `B.Ms[out, ℓⱼ] ≔ …` inside a loop over the requests, so with two
  requests for the same label in `B.rs` the messages of the first one would be lost; we accumulate
  them (see `differencies.md`).
* Algorithm 2 itself (picking eligible blocks in any order, `I[B]`, the per-block variables):
  `Trav G` with steps `TStep`. Lemma A.9 `TReach.val_eq_none`, Lemma A.10 `TReach.exists_step` /
  `TReach.exists_complete`, Lemma A.11 `TStep.val_eq`, and the key invariant `TReach.val_eq_interp`:
  every interpreted block holds exactly `interp P ℓ B`, whatever the order of picks and the block
  DAG `G ∋ B`. Lemma 4.2 is `lemma_4_2`.
* Lemmas A.12–A.14 (`out_origin`, `owner_interp`, `sender_of_mem_out`), Lemma 4.1
  (`lemma_4_1_1`, `lemma_4_1_2`), Lemma A.16 (`lemma_A_16`).
-/

set_option linter.unusedSectionVars false

namespace Podc.BFTInBlockDAG

open Block

/-- Inputs of a process instance: a request or a received message. -/
inductive Input (R M : Type) where
  | req (r : R)
  | recv (m : M)
  deriving DecidableEq

/-- A deterministic protocol, used as a black box. -/
structure Protocol (S L R M I σ : Type) where
  /-- `P(ℓ, s)`: the initial state of the instance with label `ℓ` of server `s`. -/
  init : L → S → σ
  /-- One deterministic step: new state, triggered messages, triggered indications. -/
  step : σ → Input R M → σ × List M × List I
  /-- The sender of a message. -/
  sender : M → S
  /-- The receiver of a message. -/
  receiver : M → S

/-- The values attached to a block after interpreting it for one label. -/
structure Res (M I σ : Type) where
  /-- `B.PIs[ℓ]`. -/
  st : σ
  /-- `B.Ms[out, ℓ]`. -/
  out : List M
  /-- `B.Ms[in, ℓ]` (sorted by `<_M`, without duplicates). -/
  inn : List M
  /-- The indications triggered at `B` (lines 13–14). -/
  ind : List I
  deriving DecidableEq

variable {S L R M I σ : Type}

namespace Protocol

/-- Feed a list of inputs, collecting the triggered messages and indications. -/
def run (P : Protocol S L R M I σ) : σ → List (Input R M) → σ × List M × List I
  | st, [] => (st, [], [])
  | st, i :: is =>
    let a := P.step st i
    let b := run P a.1 is
    (b.1, a.2.1 ++ b.2.1, a.2.2 ++ b.2.2)

variable (P : Protocol S L R M I σ)

@[simp] theorem run_nil (st : σ) : P.run st [] = (st, [], []) := rfl

theorem run_append (st : σ) (l₁ l₂ : List (Input R M)) :
    P.run st (l₁ ++ l₂) =
      ((P.run (P.run st l₁).1 l₂).1, (P.run st l₁).2.1 ++ (P.run (P.run st l₁).1 l₂).2.1,
        (P.run st l₁).2.2 ++ (P.run (P.run st l₁).1 l₂).2.2) := by
  induction l₁ generalizing st with
  | nil => simp
  | cons i is ih => simp [run, ih]

/-- A process "owns" its messages: `owner` is preserved by steps, `owner (init ℓ s) = s`, and every
message triggered in a state has that state's owner as sender. -/
structure Owned (owner : σ → S) : Prop where
  init : ∀ ℓ s, owner (P.init ℓ s) = s
  step : ∀ st i, owner (P.step st i).1 = owner st
  sender : ∀ st i m, m ∈ (P.step st i).2.1 → P.sender m = owner st

theorem Owned.run {P : Protocol S L R M I σ} {owner : σ → S} (h : P.Owned owner) (st : σ) (l : List (Input R M)) :
    owner (P.run st l).1 = owner st ∧ ∀ m ∈ (P.run st l).2.1, P.sender m = owner st := by
  induction l generalizing st with
  | nil => simp
  | cons i is ih =>
    simp only [Protocol.run, List.mem_append]
    obtain ⟨h1, h2⟩ := ih (P.step st i).1
    refine ⟨h1.trans (h.step st i), ?_⟩
    rintro m (hm | hm)
    · exact h.sender st i m hm
    · exact (h2 m hm).trans (h.step st i)

end Protocol

variable [DecidableEq S] [DecidableEq L] [DecidableEq R] [LinearOrder M]

/-- Line 7: some strict ancestor of `B` carries a request for label `ℓ`. -/
def seen (ℓ : L) (B : Block S L R) : Bool := (anc B).any fun C => C.rs.any fun x => decide (x.1 = ℓ)

theorem seen_iff {ℓ : L} {B : Block S L R} :
    seen ℓ B = true ↔ ∃ C, Relation.TransGen Edge C B ∧ ∃ r, (ℓ, r) ∈ C.rs := by
  simp only [seen, List.any_eq_true, decide_eq_true_eq, mem_anc]
  constructor
  · rintro ⟨C, hC, ⟨ℓ', r⟩, hx, rfl⟩
    exact ⟨C, hC, r, hx⟩
  · rintro ⟨C, hC, r, hx⟩
    exact ⟨C, hC, (ℓ, r), hx, rfl⟩

/-- The messages of `B.Ms[in, ℓ]` given the results of the predecessors (line 9), sorted by
`<_M` (line 10). -/
def inbox (P : Protocol S L R M I σ) (B : Block S L R) (pr : List (Block S L R × Res M I σ)) :
    List M :=
  ((pr.flatMap fun x => x.2.out.filter fun m => decide (P.receiver m = B.n)).dedup).insertionSort
    (· ≤ ·)

/-- Lines 4–12 of Algorithm 2 for one label `ℓ`, given whether line 7 selects `ℓ` and the
results `pr` of the predecessors. -/
def interpCore (P : Protocol S L R M I σ) (ℓ : L) (B : Block S L R) (sel : Bool)
    (pr : List (Block S L R × Res M I σ)) : Res M I σ :=
  let st₀ := match B.parent?.bind fun C => pr.lookup C with
    | some r => r.st
    | none => P.init ℓ B.n
  let reqs := (B.rs.filter fun x => decide (x.1 = ℓ)).map fun x => Input.req x.2
  let inn := if sel then inbox P B pr else []
  let a := P.run st₀ (reqs ++ inn.map Input.recv)
  ⟨a.1, a.2.1, inn, a.2.2⟩

/-- The interpretation of a block for label `ℓ` (the values Algorithm 2 computes for `B`). -/
def interp (P : Protocol S L R M I σ) (ℓ : L) : Block S L R → Res M I σ :=
  Block.fold fun B rs => interpCore P ℓ B (seen ℓ B) (B.preds.zip rs)

theorem zip_map_self {α β : Type*} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map fun a => (a, f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem interp_eq (P : Protocol S L R M I σ) (ℓ : L) (B : Block S L R) :
    interp P ℓ B = interpCore P ℓ B (seen ℓ B) (B.preds.map fun C => (C, interp P ℓ C)) := by
  unfold interp
  rw [Block.fold_eq, zip_map_self]

variable (P : Protocol S L R M I σ)

theorem lookup_map_self {C : Block S L R} {l : List (Block S L R)} (h : C ∈ l)
    (f : Block S L R → Res M I σ) : (l.map fun D => (D, f D)).lookup C = some (f C) := by
  induction l with
  | nil => simp at h
  | cons D l ih =>
    by_cases hCD : C = D
    · subst hCD; simp
    · have : C ∈ l := by simpa [hCD] using h
      have hb : (C == D) = false := by simpa using hCD
      simp [List.lookup, hb, ih this]

/-- The start state of line 4. -/
theorem interp_start (ℓ : L) (B : Block S L R) :
    ∃ st₀, (st₀ = P.init ℓ B.n ∨ ∃ C, B.parent? = some C ∧ st₀ = (interp P ℓ C).st) ∧
      interp P ℓ B =
        let reqs := (B.rs.filter fun x => decide (x.1 = ℓ)).map fun x => Input.req x.2
        let inn := if seen ℓ B then inbox P B (B.preds.map fun C => (C, interp P ℓ C)) else []
        let a := P.run st₀ (reqs ++ inn.map Input.recv)
        ⟨a.1, a.2.1, inn, a.2.2⟩ := by
  rw [interp_eq]
  unfold interpCore
  cases hp : B.parent? with
  | none => exact ⟨_, Or.inl rfl, by simp⟩
  | some C =>
    have hC : C ∈ B.preds := (parent?_eq_some hp).1
    refine ⟨(interp P ℓ C).st, Or.inr ⟨C, rfl, rfl⟩, ?_⟩
    simp [lookup_map_self hC]

theorem inn_interp (ℓ : L) (B : Block S L R) :
    (interp P ℓ B).inn =
      if seen ℓ B then inbox P B (B.preds.map fun C => (C, interp P ℓ C)) else [] := by
  obtain ⟨st₀, -, h⟩ := interp_start P ℓ B
  rw [h]

/-- Membership in `B.Ms[in, ℓ]` (line 9). -/
theorem mem_inn {ℓ : L} {B : Block S L R} {m : M} :
    m ∈ (interp P ℓ B).inn ↔
      seen ℓ B = true ∧ P.receiver m = B.n ∧ ∃ C ∈ B.preds, m ∈ (interp P ℓ C).out := by
  rw [inn_interp]
  split_ifs with h
  · simp only [inbox, List.mem_insertionSort, List.mem_dedup, List.mem_flatMap, List.mem_map,
      List.mem_filter, decide_eq_true_eq, h, true_and]
    constructor
    · rintro ⟨_, ⟨C, hC, rfl⟩, hm, hr⟩
      exact ⟨hr, C, hC, hm⟩
    · rintro ⟨hr, C, hC, hm⟩
      exact ⟨_, ⟨C, hC, rfl⟩, hm, hr⟩
  · simp [h]

/-- Lemma A.12: a message in `B.Ms[out, ℓ]` comes from a request for `ℓ` in `B` or an ancestor. -/
theorem out_origin {ℓ : L} {B : Block S L R} {m : M} (hm : m ∈ (interp P ℓ B).out) :
    ∃ B', Relation.ReflTransGen Edge B' B ∧ ∃ r, (ℓ, r) ∈ B'.rs := by
  obtain ⟨st₀, -, h⟩ := interp_start P ℓ B
  rw [h] at hm
  simp only at hm
  by_cases hreq : ∃ r, (ℓ, r) ∈ B.rs
  · exact ⟨B, Relation.ReflTransGen.refl, hreq⟩
  by_cases hs : seen ℓ B = true
  · obtain ⟨C, hC, hr⟩ := seen_iff.1 hs
    exact ⟨C, hC.to_reflTransGen, hr⟩
  · exfalso
    push Not at hreq
    have h1 : (B.rs.filter fun x => decide (x.1 = ℓ)) = [] := by
      rw [List.filter_eq_nil_iff]
      rintro ⟨ℓ', r⟩ hx
      simp only [decide_eq_true_eq]
      rintro rfl
      exact hreq r hx
    simp [h1, hs] at hm

/-- Lemma A.13: the state at a valid block is owned by its builder. -/
theorem owner_interp {owner : σ → S} (hP : P.Owned owner) (ℓ : L) {B : Block S L R}
    (hB : B.Valid) : owner (interp P ℓ B).st = B.n := by
  induction B using wellFounded_edge.induction with
  | _ B ih =>
    obtain ⟨st₀, hst, h⟩ := interp_start P ℓ B
    rw [h]
    simp only
    rw [(hP.run _ _).1]
    rcases hst with rfl | ⟨C, hC, rfl⟩
    · exact hP.init ℓ B.n
    · have hpar := parent?_eq_some hC
      rw [ih C hpar.1 (hB.of_edge hpar.1), hpar.2.1]

/-- Lemma A.14: messages in `B.Ms[out, ℓ]` have sender `B.n`. -/
theorem sender_of_mem_out {owner : σ → S} (hP : P.Owned owner) {ℓ : L} {B : Block S L R}
    (hB : B.Valid) {m : M} (hm : m ∈ (interp P ℓ B).out) : P.sender m = B.n := by
  obtain ⟨st₀, hst, h⟩ := interp_start P ℓ B
  have hown : owner st₀ = B.n := by
    rcases hst with rfl | ⟨C, hC, rfl⟩
    · exact hP.init ℓ B.n
    · have hpar := parent?_eq_some hC
      rw [owner_interp P hP ℓ (hB.of_edge hpar.1), hpar.2.1]
  rw [h] at hm
  rw [← hown]
  exact (hP.run _ _).2 m hm

/-! ### Sending and receiving in the interpretation of a block DAG (Lemma 4.1) -/

/-- In the interpretation of `G`, server `s₁` sends `m` for instance `ℓ`: some block `B ∈ G` built
by `s₁` triggers `m` (line 6 or line 11). -/
def Sends (G : Set (Block S L R)) (ℓ : L) (s₁ : S) (m : M) : Prop :=
  ∃ B ∈ G, B.n = s₁ ∧ m ∈ (interp P ℓ B).out

/-- In the interpretation of `G`, server `s₂` receives `m` for instance `ℓ` (line 11 at a block
built by `s₂`). -/
def Receives (G : Set (Block S L R)) (ℓ : L) (s₂ : S) (m : M) : Prop :=
  ∃ B ∈ G, B.n = s₂ ∧ m ∈ (interp P ℓ B).inn

/-- Lemma 4.1 (1). -/
theorem lemma_4_1_1 {G : Set (Block S L R)} (hG : IsBlockDAG G) (ℓ : L) (s₁ : S) (m : M) :
    Sends P G ℓ s₁ m ↔ ∃ B₁ ∈ G, B₁.n = s₁ ∧ m ∈ (interp P ℓ B₁).out ∧
      ∃ B' ∈ G, (∃ r, (ℓ, r) ∈ B'.rs) ∧ Relation.ReflTransGen Edge B' B₁ := by
  constructor
  · rintro ⟨B, hB, hn, hm⟩
    obtain ⟨B', hB', hr⟩ := out_origin P hm
    exact ⟨B, hB, hn, hm, B', hG.mem_of_reflTransGen hB hB', hr, hB'⟩
  · rintro ⟨B, hB, hn, hm, -⟩
    exact ⟨B, hB, hn, hm⟩

/-- Lemma 4.1 (2). -/
theorem lemma_4_1_2 {G : Set (Block S L R)} (hG : IsBlockDAG G) (ℓ : L) (s₂ : S) (m : M) :
    Receives P G ℓ s₂ m ↔ ∃ B₁ ∈ G, ∃ B₂ ∈ G, Edge B₁ B₂ ∧ B₂.n = s₂ ∧ m ∈ (interp P ℓ B₂).inn ∧
      m ∈ (interp P ℓ B₁).out ∧ P.receiver m = s₂ ∧
      ∃ B' ∈ G, (∃ r, (ℓ, r) ∈ B'.rs) ∧ Relation.ReflTransGen Edge B' B₁ := by
  constructor
  · rintro ⟨B, hB, hn, hm⟩
    obtain ⟨-, hr, C, hC, hmC⟩ := (mem_inn P).1 hm
    obtain ⟨B', hB', hr'⟩ := out_origin P hmC
    have hCG := hG.2 B hB C hC
    exact ⟨C, hCG, B, hB, hC, hn, hm, hmC, hr.trans hn, B', hG.mem_of_reflTransGen hCG hB', hr',
      hB'⟩
  · rintro ⟨-, -, B, hB, -, hn, hm, -⟩
    exact ⟨B, hB, hn, hm⟩

/-- Lemma A.16: what is sent in the interpretation of `G` is sent in the interpretation of every
`G' ⩾ G`. -/
theorem lemma_A_16 {G G' : Set (Block S L R)} (h : G ⊆ G') {ℓ : L} {s₁ : S} {m : M}
    (hs : Sends P G ℓ s₁ m) : Sends P G' ℓ s₁ m := by
  obtain ⟨B, hB, hn, hm⟩ := hs
  exact ⟨B, h hB, hn, hm⟩

theorem receives_mono {G G' : Set (Block S L R)} (h : G ⊆ G') {ℓ : L} {s : S} {m : M}
    (hs : Receives P G ℓ s m) : Receives P G' ℓ s m := by
  obtain ⟨B, hB, hn, hm⟩ := hs
  exact ⟨B, h hB, hn, hm⟩

/-! ### Algorithm 2 as a transition system -/

/-- The variables of Algorithm 2: the set `I` of interpreted blocks, and for every block the values
`PIs`, `Ms` for all labels (`none` = the initial `⊥`/`∅`). -/
structure Trav (S L R M I σ : Type) where
  /-- The blocks with `I[B] = true`. -/
  done : Set (Block S L R)
  /-- The per-block variables. -/
  val : Block S L R → Option (L → Res M I σ)

/-- The initial state: nothing interpreted. -/
def Trav.init : Trav S L R M I σ := ⟨∅, fun _ => none⟩

/-- Line 7 evaluated in the graph `G` itself: a strict ancestor of `B` *in `G`* (along the edges of
`G`) carries a request for `ℓ`. -/
noncomputable def seenIn (G : Set (Block S L R)) (ℓ : L) (B : Block S L R) : Bool :=
  @decide (∃ Bj ∈ G, Relation.TransGen (toGraph G).Adj Bj B ∧ ∃ r, (ℓ, r) ∈ Bj.rs)
    (Classical.propDecidable _)

/-- One iteration of Algorithm 2 on the block DAG `G`: pick an eligible block `B` (line 3: not yet
interpreted, all predecessors interpreted) and interpret it (lines 4–12). -/
def TStep (G : Set (Block S L R)) (t t' : Trav S L R M I σ) : Prop :=
  ∃ B ∈ G, B ∉ t.done ∧ (∀ C ∈ B.preds, C ∈ t.done) ∧
    ∃ vs : List (L → Res M I σ), List.Forall₂ (fun C v => t.val C = some v) B.preds vs ∧
      t' = ⟨insert B t.done, Function.update t.val B
        (some fun ℓ => interpCore P ℓ B (seenIn G ℓ B) (B.preds.zip (vs.map (· ℓ))))⟩

/-- States reachable by Algorithm 2 on `G`. -/
def TReach (G : Set (Block S L R)) : Trav S L R M I σ → Prop :=
  Relation.ReflTransGen (TStep P G) Trav.init

/-- For a block of a block DAG, line 7 evaluated in `G` agrees with the structural `seen`. -/
theorem seenIn_eq {G : Set (Block S L R)} (hG : IsBlockDAG G) {B : Block S L R} (hB : B ∈ G)
    (ℓ : L) : seenIn G ℓ B = seen ℓ B := by
  have key : ∀ C, Relation.TransGen (toGraph G).Adj C B ↔ Relation.TransGen Edge C B := by
    intro C
    constructor
    · intro h
      induction h with
      | single h => exact Relation.TransGen.single h.2
      | tail _ h ih => exact (ih (hG.2 _ h.1 _ h.2)).tail h.2
    · intro h
      induction h using Relation.TransGen.head_induction_on with
      | single h => exact Relation.TransGen.single ⟨hB, h⟩
      | head h h' ih =>
        rename_i a c
        have hc : c ∈ G := hG.mem_of_reflTransGen hB h'.to_reflTransGen
        exact Relation.TransGen.head ⟨hc, h⟩ ih
  rw [Bool.eq_iff_iff, seen_iff, seenIn, @decide_eq_true_iff _ (Classical.propDecidable _)]
  constructor
  · rintro ⟨C, -, hC, hr⟩
    exact ⟨C, (key C).1 hC, hr⟩
  · rintro ⟨C, hC, hr⟩
    exact ⟨C, hG.mem_of_reflTransGen hB hC.to_reflTransGen, (key C).2 hC, hr⟩

/-- The invariant of Algorithm 2. -/
structure TInv (G : Set (Block S L R)) (t : Trav S L R M I σ) : Prop where
  sub : t.done ⊆ G
  closed : ∀ B ∈ t.done, ∀ C ∈ B.preds, C ∈ t.done
  none : ∀ B, B ∉ t.done → t.val B = none
  val : ∀ B ∈ t.done, t.val B = some fun ℓ => interp P ℓ B

theorem TInv.step {G : Set (Block S L R)} (hG : IsBlockDAG G) {t t' : Trav S L R M I σ}
    (hi : TInv P G t) (hs : TStep P G t t') : TInv P G t' := by
  obtain ⟨B, hBG, hBn, hpre, vs, hvs, rfl⟩ := hs
  have hvs' : vs = B.preds.map fun C => fun ℓ => interp P ℓ C := by
    have key : ∀ (l : List (Block S L R)) (ws : List (L → Res M I σ)), (∀ C ∈ l, C ∈ t.done) →
        List.Forall₂ (fun C v => t.val C = some v) l ws → ws = l.map fun C => fun ℓ => interp P ℓ C := by
      intro l ws hl hw
      induction hw with
      | nil => rfl
      | @cons C v l ws h _ ih =>
        simp only [List.map_cons, List.cons.injEq]
        refine ⟨?_, ih fun D hD => hl D (List.mem_cons_of_mem _ hD)⟩
        rw [hi.val C (hl C List.mem_cons_self)] at h
        exact (Option.some.inj h).symm
    exact key _ _ hpre hvs
  subst hvs'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro D (rfl | hD)
    · exact hBG
    · exact hi.sub hD
  · rintro D (rfl | hD) C hC
    · exact Or.inr (hpre C hC)
    · exact Or.inr (hi.closed D hD C hC)
  · intro D hD
    have hDB : D ≠ B := fun h => hD (Or.inl h)
    dsimp only
    rw [Function.update_of_ne hDB]
    exact hi.none D (fun h => hD (Or.inr h))
  · rintro D (rfl | hD)
    · dsimp only
      rw [Function.update_self]
      congr 1
      funext ℓ
      rw [interp_eq, seenIn_eq hG hBG, List.map_map]
      congr 1
      rw [zip_map_self]
      rfl
    · have hDB : D ≠ B := fun h => hBn (h ▸ hD)
      dsimp only
      rw [Function.update_of_ne hDB]
      exact hi.val D hD

theorem TReach.inv {G : Set (Block S L R)} (hG : IsBlockDAG G) {t : Trav S L R M I σ}
    (h : TReach P G t) : TInv P G t := by
  induction h with
  | refl => exact ⟨by simp [Trav.init], by simp [Trav.init], by simp [Trav.init],
      by simp [Trav.init]⟩
  | tail _ hs ih => exact ih.step P hG hs

/-- Lemma A.9: an uninterpreted block still has its initial values. -/
theorem TReach.val_eq_none {G : Set (Block S L R)} (hG : IsBlockDAG G) {t : Trav S L R M I σ}
    (h : TReach P G t) {B : Block S L R} (hB : B ∉ t.done) : t.val B = none :=
  (h.inv P hG).none B hB

/-- The key property of Algorithm 2: an interpreted block holds the canonical values
`interp P ℓ B`, independently of the order of picks and of the block DAG. -/
theorem TReach.val_eq_interp {G : Set (Block S L R)} (hG : IsBlockDAG G)
    {t : Trav S L R M I σ} (h : TReach P G t) {B : Block S L R} (hB : B ∈ t.done) :
    t.val B = some fun ℓ => interp P ℓ B :=
  (h.inv P hG).val B hB

/-- Lemma A.11: once interpreted, a block is never modified again. -/
theorem TStep.val_eq {G : Set (Block S L R)} {t t' : Trav S L R M I σ} (hs : TStep P G t t')
    {B : Block S L R} (hB : B ∈ t.done) : B ∈ t'.done ∧ t'.val B = t.val B := by
  obtain ⟨D, -, hDn, -, -, -, rfl⟩ := hs
  have hBD : B ≠ D := fun h => hDn (h ▸ hB)
  exact ⟨Or.inr hB, Function.update_of_ne hBD _ _⟩

/-- Lemma A.10 (progress): while some block of a finite block DAG is uninterpreted, some block is
eligible. -/
theorem TReach.exists_step {G : Set (Block S L R)} (hG : IsBlockDAG G) {t : Trav S L R M I σ}
    (h : TReach P G t) (hne : ¬ G ⊆ t.done) : ∃ t', TStep P G t t' := by
  have hi := h.inv P hG
  obtain ⟨B, ⟨hBG, hBn⟩, hmin⟩ := wellFounded_edge.has_min (G \ t.done) (by
    obtain ⟨B, hB, hBn⟩ := Set.not_subset.1 hne
    exact ⟨B, hB, hBn⟩)
  have hpre : ∀ C ∈ B.preds, C ∈ t.done := by
    intro C hC
    by_contra hCn
    exact hmin C ⟨hG.2 B hBG C hC, hCn⟩ hC
  refine ⟨_, B, hBG, hBn, hpre, B.preds.map fun C => fun ℓ => interp P ℓ C, ?_, rfl⟩
  rw [List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun C hC => hi.val C (hpre C hC)

theorem TStep.done_ssubset {G : Set (Block S L R)} {t t' : Trav S L R M I σ}
    (hs : TStep P G t t') : t.done ⊂ t'.done ∧ t'.done ⊆ t.done ∪ G := by
  obtain ⟨B, hBG, hBn, -, -, -, rfl⟩ := hs
  refine ⟨Set.ssubset_insert hBn, ?_⟩
  rintro D (rfl | hD)
  · exact Or.inr hBG
  · exact Or.inl hD

/-- Lemma A.10 (termination): on a finite block DAG, Algorithm 2 can always be completed, and every
run reaches a state where every block of `G` is interpreted. -/
theorem TReach.exists_complete {G : Set (Block S L R)} (hG : IsBlockDAG G) (hfin : G.Finite)
    {t : Trav S L R M I σ} (h : TReach P G t) :
    ∃ t', Relation.ReflTransGen (TStep P G) t t' ∧ t'.done = G := by
  have hsub := (h.inv P hG).sub
  have hfin' : (G \ t.done).Finite := hfin.sdiff
  -- induction on the number of uninterpreted blocks
  generalize hk : hfin'.toFinset.card = k
  induction k generalizing t with
  | zero =>
    refine ⟨t, Relation.ReflTransGen.refl, Set.Subset.antisymm hsub ?_⟩
    intro B hB
    by_contra hBn
    have : B ∈ hfin'.toFinset := by simp [hB, hBn]
    rw [Finset.card_eq_zero.1 hk] at this
    simp at this
  | succ k ih =>
    have hne : ¬ G ⊆ t.done := by
      intro hG'
      have : hfin'.toFinset = ∅ := by
        ext B; simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, Finset.notMem_empty, iff_false,
          not_and, not_not]
        exact fun hB => hG' hB
      rw [this] at hk; simp at hk
    obtain ⟨t', hs⟩ := h.exists_step P hG hne
    have h' : TReach P G t' := h.tail hs
    have hsub' := (h'.inv P hG).sub
    obtain ⟨⟨hss, hns⟩, -⟩ := hs.done_ssubset P
    obtain ⟨B, hB', hBn⟩ := Set.exists_of_ssubset ⟨hss, hns⟩
    have hcard : (hfin.sdiff (t := t'.done)).toFinset.card = k := by
      have hlt : (hfin.sdiff (t := t'.done)).toFinset ⊂ hfin'.toFinset := by
        rw [Set.Finite.toFinset_ssubset_toFinset]
        refine ⟨Set.sdiff_subset_sdiff_right hss, fun hc => ?_⟩
        have : B ∈ G \ t'.done := hc ⟨hsub' hB', hBn⟩
        exact this.2 hB'
      have hle : (hfin.sdiff (t := t'.done)).toFinset.card + 1 ≤ hfin'.toFinset.card :=
        Finset.card_lt_card hlt
      -- exactly one block was added
      obtain ⟨D, hDG, hDn, hpreD, vsD, hvsD, htD⟩ := hs
      have hdone : t'.done = insert D t.done := by rw [htD]
      have : hfin'.toFinset = insert D (hfin.sdiff (t := t'.done)).toFinset := by
        ext x
        simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, Finset.mem_insert, hdone,
          Set.mem_insert_iff, not_or]
        constructor
        · rintro ⟨hx, hxn⟩
          by_cases hxD : x = D
          · exact Or.inl hxD
          · exact Or.inr ⟨hx, hxD, hxn⟩
        · rintro (rfl | ⟨hx, -, hxn⟩)
          · exact ⟨hDG, hDn⟩
          · exact ⟨hx, hxn⟩
      rw [this, Finset.card_insert_of_notMem (by simp [hdone])] at hk
      omega
    obtain ⟨t'', h1, h2⟩ := ih h' hsub' (hfin.sdiff) hcard
    exact ⟨t'', Relation.ReflTransGen.head hs h1, h2⟩

/-- Lemma 4.2: if `G ⩽ G'`, then for every `B ∈ G` the interpretations of `G` and of `G'` (by any
two servers, in any order) assign the same `B.PIs[ℓ]`, `B.Ms[out, ℓ]` (and `B.Ms[in, ℓ]`). -/
theorem lemma_4_2 {G G' : Set (Block S L R)} (hG : IsBlockDAG G) (hG' : IsBlockDAG G')
    (hle : toGraph G ≤ toGraph G') {t t' : Trav S L R M I σ} (ht : TReach P G t)
    (ht' : TReach P G' t') (hc : t.done = G) (hc' : t'.done = G') {B : Block S L R}
    (hB : B ∈ G) : t.val B = t'.val B := by
  rw [ht.val_eq_interp P hG (hc ▸ hB), ht'.val_eq_interp P hG' (hc' ▸ hle.1 hB)]

end Podc.BFTInBlockDAG
