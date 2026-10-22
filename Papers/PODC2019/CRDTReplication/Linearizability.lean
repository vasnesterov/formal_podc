import Papers.PODC2019.CRDTReplication.CRDT
import Cslib.Computability.Distributed.SharedMemory.Linearization
import Mathlib.Data.Finset.Card

/-!
# Section III-E: Theorems 1–5 imply linearizability

The paper shows (Lemmas 6–8) that *any* protocol whose learned states satisfy Validity
(Theorem 1), Stability (Theorem 2), Consistency (Theorem 3), Update Stability (Theorem 4) and
Update Visibility (Theorem 5) is linearizable. We state this for an arbitrary well-formed
history `α` of the CRDT object (CSLib `Label`s) together with a map `ls` assigning to each
completed query operation the state it learned (`LearnedHistory`), and prove that `α` has a
linearization in the sense of CSLib (`Cslib.SharedMemory.IsLinearization`).

Update identifiers are assumed unique (as in the paper, "we assume updates to be unique").
Validity is split in two: every update in the causal history of a learned state has been
invoked (`validity_invoked`), and none of them is invoked after the query returned
(`validity_before`).
-/

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/LatticeLin.lean
namespace Podc.CRDTReplication

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {D : CRDT}

/-- The hypotheses of Section III-E on a history `α` with learned states `ls`
(`ls x = some s`: the query operation `x` returned `cmd_q(s)`). -/
structure LearnedHistory (H : D.CausalHistory) (α : List (Label P D.spec))
    (ls : OpId P → Option D.S) : Prop where
  wf : WellFormed α
  ls_query : ∀ x s, ls x = some s → Completed α x ∧ ∃ q, opOf α x = some (CRDT.Cmd.qry q)
  resp_query : ∀ x q r, opOf α x = some (CRDT.Cmd.qry q) → respOf α x = some r →
    ∃ s, ls x = some s ∧ r = CRDT.Res.val (D.query q s)
  resp_upd : ∀ x u r, opOf α x = some (CRDT.Cmd.upd u) → respOf α x = some r →
    r = CRDT.Res.done
  /-- Update identifiers are unique. -/
  unique : ∀ x y u, opOf α x = some (CRDT.Cmd.upd u) → opOf α y = some (CRDT.Cmd.upd u) → x = y
  /-- Theorem 1 (Validity), part 1: updates in a learned state have been invoked. -/
  validity_invoked : ∀ x s, ls x = some s → ∀ u ∈ H.C s, ∃ y, opOf α y = some (CRDT.Cmd.upd u)
  /-- Theorem 1 (Validity), part 2: no update in a learned state is invoked after the query
  returned. -/
  validity_before : ∀ x s, ls x = some s → ∀ u ∈ H.C s, ∀ y,
    opOf α y = some (CRDT.Cmd.upd u) → ¬ Precedes α x y
  /-- Theorem 2 (Stability). -/
  stability : ∀ x y s₁ s₂, Precedes α x y → ls x = some s₁ → ls y = some s₂ → s₁ ≤ s₂
  /-- Theorem 3 (Consistency). -/
  consistency : ∀ x y s₁ s₂, ls x = some s₁ → ls y = some s₂ → s₁ ≤ s₂ ∨ s₂ ≤ s₁
  /-- Theorem 4 (Update Stability). -/
  updStability : ∀ x y z u₁ u₂ s, Precedes α x y → opOf α x = some (CRDT.Cmd.upd u₁) →
    opOf α y = some (CRDT.Cmd.upd u₂) → ls z = some s → u₂ ∈ H.C s → u₁ ∈ H.C s
  /-- Theorem 5 (Update Visibility). -/
  updVisibility : ∀ x y u s, Precedes α x y → opOf α x = some (CRDT.Cmd.upd u) →
    ls y = some s → u ∈ H.C s

/-! ## Proof of Lemmas 6–8

We make the paper's construction concrete. Let `N` be the number of invoked operations and
`idx x` the position of `x` in invocation order (`invIds α`). The learned states form a finite
chain; the *rank* of a state `s` is the number of learned states `t` with `s ⋢ t`, and the rank of
an update command `u` is the number of learned states whose causal history does not contain `u`.
For a learned state `s`, `urank u ≤ rank s ↔ u ∈ C(s)` (`urank_le_rank_iff`). An update `u` gets
level `2 · urank u`, a completed query that learned `s` gets level `2 · rank s + 1`; the
linearization lists all invoked updates and all completed queries sorted by
`level · N + idx` (`linOrder`). -/

section ListAux

/-- In a list sorted strictly by `f`, an element with a smaller `f`-value comes first. -/
lemma sublist_pair_of_pairwise {X : Type} {f : X → ℕ} :
    ∀ {l : List X}, l.Pairwise (fun a b => f a < f b) → ∀ {a b : X}, a ∈ l → b ∈ l →
      f a < f b → [a, b].Sublist l
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, hl, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd hab (lt_irrefl _)
      · exact List.cons_sublist_cons.2 (List.singleton_sublist.2 hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (hl.1 a ha') (by omega)
      · exact (sublist_pair_of_pairwise hl.2 ha' hb' hab).trans (List.sublist_cons_self c l)

/-- In a duplicate-free list, if `[a, b]` is a sublist then `a` has the smaller index. -/
lemma idxOf_lt_of_sublist_pair {X : Type} [DecidableEq X] {l : List X} {a b : X}
    (hl : l.Nodup) (h : [a, b].Sublist l) : l.idxOf a < l.idxOf b := by
  obtain ⟨r₁, r₂, rfl, ha, hb⟩ := sublist_pair_iff.1 h
  have hb' : b ∉ r₁ := fun hb₁ => (List.nodup_append.1 hl).2.2 b hb₁ b hb rfl
  rw [List.idxOf_append_of_mem ha, List.idxOf_append_of_notMem hb']
  have := List.idxOf_lt_length_of_mem ha
  omega

/-- Lexicographic comparison of `m * N + t` with `t < N`. -/
lemma lex_lt {m m' t t' N : ℕ} (ht : t < N) (h : m < m' ∨ m = m' ∧ t < t') :
    m * N + t < m' * N + t' := by
  rcases h with h | ⟨rfl, h⟩
  · have : (m + 1) * N ≤ m' * N := Nat.mul_le_mul_right N h
    rw [Nat.add_mul] at this; omega
  · omega

/-- Legality of a sequential history, checked position by position. -/
lemma seqOK_of_forall {A : ObjSpec} {α : List (Label P A)} :
    ∀ (q : A.State) (L : List (OpId P × A.Op)),
    (∀ L₁ x o L₂, L = L₁ ++ (x, o) :: L₂ → ∀ r, respOf α x = some r →
      (A.δ (A.runOps q (L₁.map Prod.snd)) o).2 = r) → SeqOK α q L
  | _, [], _ => trivial
  | q, (x, o) :: L, h => ⟨fun r hr => h [] x o L rfl r hr,
      seqOK_of_forall _ L fun L₁ x' o' L₂ hL r hr => by
        simpa using h ((x, o) :: L₁) x' o' L₂ (by simp [hL]) r hr⟩

end ListAux

/-- An update command as an operation of the object `D.spec`. -/
abbrev updOp (u : D.U) : D.spec.Op := CRDT.Cmd.upd u

/-- A query command as an operation of the object `D.spec`. -/
abbrev qryOp (q : D.Q) : D.spec.Op := CRDT.Cmd.qry q

lemma updOp_inj {u v : D.U} : updOp v = updOp u ↔ v = u :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩

lemma updOp_ne_qryOp {v : D.U} {q : D.Q} : updOp v = qryOp q ↔ False :=
  ⟨fun h => (by cases h), False.elim⟩

/-- The causal history of the state reached by a sequence of commands: the initial history plus
the update commands of the sequence. -/
lemma CRDT.CausalHistory.C_runOps (H : D.CausalHistory) (s : D.S) (os : List D.spec.Op) :
    H.C (D.spec.runOps s os) = H.C s ∪ {u | updOp u ∈ os} := by
  induction os generalizing s with
  | nil => change H.C s = H.C s ∪ _; simp
  | cons o os ih =>
    change H.C (D.spec.runOps (D.spec.δ s o).1 os) = _
    refine (ih _).trans ?_
    cases o with
    | upd u =>
      change H.C (D.app u s) ∪ _ = H.C s ∪ {w | updOp w ∈ updOp u :: os}
      rw [H.C_app]
      ext v
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, List.mem_cons,
        CRDT.Cmd.upd.injEq]
      tauto
    | qry q =>
      change H.C s ∪ _ = H.C s ∪ {w | updOp w ∈ qryOp q :: os}
      ext v
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, reduceCtorEq,
        false_or]

section Construction

variable (H : D.CausalHistory) (α : List (Label P D.spec)) (ls : OpId P → Option D.S)

/-- The (finitely many) learned states of `α`. -/
def learned : Finset D.S := ((invIds α).filterMap ls).toFinset

/-- The rank of a state: the number of learned states not above it. -/
def rank (s : D.S) : ℕ := ((learned α ls).filter (fun t => ¬ s ≤ t)).card

open Classical in
/-- The rank of an update command: the number of learned states whose causal history does not
contain it. -/
noncomputable def urank (u : D.U) : ℕ := ((learned α ls).filter (fun t => u ∉ H.C t)).card

/-- The level of an operation: `2 · urank u` for an update `u`, `2 · rank s + 1` for a query
that learned `s`. -/
noncomputable def level (x : OpId P) : ℕ :=
  match (opOf α x : Option (CRDT.Cmd D)) with
  | some (.upd u) => 2 * urank H α ls u
  | _ => 2 * (match ls x with | some s => rank α ls s | none => 0) + 1

/-- The sort key of an operation: its level, ties broken by invocation order. -/
noncomputable def key (x : OpId P) : ℕ := level H α ls x * (invIds α).length + (invIds α).idxOf x

/-- The entry of operation `x` in the linearization: updates are kept, pending queries
dropped. -/
def entry (x : OpId P) : Option (OpId P × D.spec.Op) :=
  match (opOf α x : Option (CRDT.Cmd D)) with
  | some (.upd u) => some (x, CRDT.Cmd.upd u)
  | some (.qry q) => if (respOf α x).isSome then some (x, CRDT.Cmd.qry q) else none
  | none => none

/-- The linearization: all invoked updates and completed queries, sorted by `key`. -/
noncomputable def linOrder : List (OpId P × D.spec.Op) :=
  ((invIds α).filterMap (entry α)).mergeSort
    (fun e e' => decide (key H α ls e.1 ≤ key H α ls e'.1))

variable {H α ls}

lemma mem_learned {s : D.S} : s ∈ learned α ls ↔ ∃ x ∈ invIds α, ls x = some s := by
  simp [learned]

lemma rank_mono {s t : D.S} (hst : s ≤ t) : rank α ls s ≤ rank α ls t := by
  apply Finset.card_le_card
  intro r; simp only [Finset.mem_filter]
  exact fun ⟨hr, hsr⟩ => ⟨hr, fun htr => hsr (hst.trans htr)⟩

lemma urank_mono {u₁ u₂ : D.U} (h12 : ∀ s ∈ learned α ls, u₂ ∈ H.C s → u₁ ∈ H.C s) :
    urank H α ls u₁ ≤ urank H α ls u₂ := by
  unfold urank
  apply Finset.card_le_card
  intro t; simp only [Finset.mem_filter]
  exact fun ⟨ht, hu⟩ => ⟨ht, fun hu2 => hu (h12 t ht hu2)⟩

lemma entry_eq_some {x : OpId P} {e : OpId P × D.spec.Op} (he : entry α x = some e) :
    e.1 = x ∧ opOf α x = some e.2 ∧ ∀ q, e.2 = .qry q → Completed α x := by
  unfold entry at he
  split at he
  · next u hu => cases he; exact ⟨rfl, hu, fun _ h => by cases h⟩
  · next q hq =>
    split_ifs at he with hr
    cases he; exact ⟨rfl, hq, fun _ _ => completed_iff_respOf.2 hr⟩
  · simp at he

lemma mem_linOrder {e : OpId P × D.spec.Op} :
    e ∈ linOrder H α ls ↔ e.1 ∈ invIds α ∧ entry α e.1 = some e := by
  unfold linOrder
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, he⟩; obtain ⟨rfl, -⟩ := entry_eq_some he; exact ⟨hx, he⟩
  · exact fun ⟨hx, he⟩ => ⟨_, hx, he⟩

lemma nodup_linOrder : ((linOrder H α ls).map Prod.fst).Nodup := by
  have hM : ((invIds α).filterMap (entry α)).Nodup :=
    (nodup_invIds α).filterMap fun a a' b ha ha' =>
      (entry_eq_some (Option.mem_def.1 ha)).1.symm.trans (entry_eq_some (Option.mem_def.1 ha')).1
  have hM' : (((invIds α).filterMap (entry α)).map Prod.fst).Nodup := by
    refine hM.map_on fun e he e' he' hee => ?_
    obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 he
    obtain ⟨x', -, hx'⟩ := List.mem_filterMap.1 he'
    obtain ⟨rfl, -⟩ := entry_eq_some hx
    obtain ⟨rfl, -⟩ := entry_eq_some hx'
    rw [hee] at hx; exact Option.some_injective _ (hx.symm.trans hx')
  exact ((List.mergeSort_perm _ _).map _).nodup_iff.2 hM'

lemma key_lt_key {x y : OpId P} (hx : x ∈ invIds α)
    (h : level H α ls x < level H α ls y ∨
      level H α ls x = level H α ls y ∧ (invIds α).idxOf x < (invIds α).idxOf y) :
    key H α ls x < key H α ls y :=
  lex_lt (List.idxOf_lt_length_of_mem hx) h

lemma key_inj {x y : OpId P} (hx : x ∈ invIds α) (hy : y ∈ invIds α)
    (h : key H α ls x = key H α ls y) : x = y := by
  rcases lt_trichotomy (level H α ls x) (level H α ls y) with hl | hl | hl
  · exact absurd h (key_lt_key hx (.inl hl)).ne
  · have h1 := List.idxOf_lt_length_of_mem hx
    have h2 := List.idxOf_lt_length_of_mem hy
    unfold key at h; rw [hl] at h
    exact (List.idxOf_inj hx).1 (by omega)
  · exact absurd h (key_lt_key hy (.inl hl)).ne'

lemma pairwise_linOrder :
    (linOrder H α ls).Pairwise (fun e e' => key H α ls e.1 < key H α ls e'.1) := by
  have hs := List.pairwise_mergeSort
    (le := fun e e' : OpId P × D.spec.Op => decide (key H α ls e.1 ≤ key H α ls e'.1))
    (by intro a b c; simp only [decide_eq_true_eq]; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((invIds α).filterMap (entry α))
  have hnd : (linOrder H α ls).Pairwise (fun e e' => e.1 ≠ e'.1) :=
    List.pairwise_map.1 nodup_linOrder
  refine (hs.and hnd).imp_of_mem fun {e e'} he he' ⟨hle, hne⟩ => ?_
  simp only [decide_eq_true_eq] at hle
  exact lt_of_le_of_ne hle fun hk =>
    hne (key_inj (mem_linOrder.1 he).1 (mem_linOrder.1 he').1 hk)

lemma level_upd {x : OpId P} {u : D.U} (hx : opOf α x = some (CRDT.Cmd.upd u)) :
    level H α ls x = 2 * urank H α ls u := by
  unfold level; rw [hx]

lemma level_qry {x : OpId P} {q : D.Q} {s : D.S} (hx : opOf α x = some (CRDT.Cmd.qry q))
    (hs : ls x = some s) : level H α ls x = 2 * rank α ls s + 1 := by
  unfold level; rw [hx, hs]

end Construction

namespace LearnedHistory

variable {H : D.CausalHistory} {α : List (Label P D.spec)} {ls : OpId P → Option D.S}
  (h : LearnedHistory H α ls)
include h

lemma mem_learned_of {x : OpId P} {s : D.S} (hx : ls x = some s) : s ∈ learned α ls :=
  mem_learned.2 ⟨x, (mem_invIds α x).2 (h.wf.invoked_of_completed (h.ls_query x s hx).1), hx⟩

/-- The learned states form a chain (Theorem 3). -/
lemma learned_chain {s t : D.S} (hs : s ∈ learned α ls) (ht : t ∈ learned α ls) :
    s ≤ t ∨ t ≤ s := by
  obtain ⟨x, -, hx⟩ := mem_learned.1 hs
  obtain ⟨y, -, hy⟩ := mem_learned.1 ht
  exact h.consistency x y s t hx hy

/-- The key property of the ranks: for a learned state `s`, `urank u ≤ rank s ↔ u ∈ C(s)`. -/
lemma urank_le_rank_iff {s : D.S} (hs : s ∈ learned α ls) (u : D.U) :
    urank H α ls u ≤ rank α ls s ↔ u ∈ H.C s := by
  classical
  constructor
  · intro hle; by_contra hu
    have hsub : (learned α ls).filter (fun t => ¬ s ≤ t) ⊂
        (learned α ls).filter (fun t => u ∉ H.C t) := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨s, Finset.mem_filter.2 ⟨hs, hu⟩, by simp⟩
      · intro t; simp only [Finset.mem_filter]
        rintro ⟨ht, hst⟩
        refine ⟨ht, fun hut => hu ?_⟩
        rcases h.learned_chain hs ht with h' | h'
        · exact absurd h' hst
        · exact H.C_mono h' hut
    have := Finset.card_lt_card hsub
    exact absurd hle (not_le.2 this)
  · intro hu
    apply Finset.card_le_card
    intro t; simp only [Finset.mem_filter]
    exact fun ⟨ht, hut⟩ => ⟨ht, fun hst => hut (H.C_mono hst hu)⟩

lemma exists_ls {x : OpId P} {q : D.Q} (hq : opOf α x = some (CRDT.Cmd.qry q))
    (hc : Completed α x) : ∃ s, ls x = some s := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
  obtain ⟨s, hs, -⟩ := h.resp_query x q r hq hr
  exact ⟨s, hs⟩

omit h in
lemma exists_opOf {x : OpId P} (hx : Invoked α x) : ∃ o, opOf α x = some o :=
  ⟨_, List.getElem?_eq_getElem hx⟩

omit h in
lemma mem_linOrder_of_upd {y : OpId P} {u : D.U} (hy : opOf α y = some (CRDT.Cmd.upd u)) :
    ((y, CRDT.Cmd.upd u) : OpId P × D.spec.Op) ∈ linOrder H α ls := by
  refine mem_linOrder.2 ⟨(mem_invIds α y).2 (Invoked.of_opOf_eq_some hy), ?_⟩
  simp only [entry, hy]

lemma complete {x : OpId P} (hx : Completed α x) : x ∈ (linOrder H α ls).map Prod.fst := by
  obtain ⟨o, ho⟩ := exists_opOf (h.wf.invoked_of_completed hx)
  cases o with
  | upd u => exact List.mem_map.2 ⟨_, mem_linOrder_of_upd ho, rfl⟩
  | qry q =>
    refine List.mem_map.2 ⟨(x, .qry q), mem_linOrder.2
      ⟨(mem_invIds α x).2 (h.wf.invoked_of_completed hx), ?_⟩, rfl⟩
    simp only [entry, ho, completed_iff_respOf.1 hx, ite_true]

/-- Real-time order is respected by the levels. -/
lemma level_le_of_precedes {a b : OpId P} (hab : Precedes α a b)
    (hb : b ∈ (linOrder H α ls).map Prod.fst) : level H α ls a ≤ level H α ls b := by
  obtain ⟨eb, heb, rfl⟩ := List.mem_map.1 hb
  obtain ⟨-, he⟩ := mem_linOrder.1 heb
  obtain ⟨-, hob, hcb⟩ := entry_eq_some he
  have hca := hab.completed
  obtain ⟨oa, hoa⟩ := exists_opOf (h.wf.invoked_of_completed hca)
  obtain ⟨b, ob⟩ := eb
  simp only at hob hcb ⊢
  cases oa with
  | upd u₁ =>
    cases ob with
    | upd u₂ =>
      rw [level_upd hoa, level_upd hob]
      have := urank_mono (H := H) (α := α) (ls := ls) (u₁ := u₁) (u₂ := u₂) fun s hs hu₂ => by
        obtain ⟨z, -, hz⟩ := mem_learned.1 hs
        exact h.updStability a b z u₁ u₂ s hab hoa hob hz hu₂
      omega
    | qry q =>
      obtain ⟨s, hs⟩ := h.exists_ls hob (hcb q rfl)
      rw [level_upd hoa, level_qry hob hs]
      have := (h.urank_le_rank_iff (h.mem_learned_of hs) u₁).2
        (h.updVisibility a b u₁ s hab hoa hs)
      omega
  | qry q₁ =>
    obtain ⟨s₁, hs₁⟩ := h.exists_ls hoa hca
    cases ob with
    | upd u =>
      rw [level_qry hoa hs₁, level_upd hob]
      have := mt (h.urank_le_rank_iff (h.mem_learned_of hs₁) u).1
        fun hu => h.validity_before a s₁ hs₁ u hu b hob hab
      omega
    | qry q₂ =>
      obtain ⟨s₂, hs₂⟩ := h.exists_ls hob (hcb q₂ rfl)
      rw [level_qry hoa hs₁, level_qry hob hs₂]
      have := rank_mono (α := α) (ls := ls) (h.stability a b s₁ s₂ hab hs₁ hs₂)
      omega

lemma realtime {a b : OpId P} (hab : Precedes α a b)
    (hb : b ∈ (linOrder H α ls).map Prod.fst) :
    [a, b].Sublist ((linOrder H α ls).map Prod.fst) := by
  have hbinv : Invoked α b := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
    exact (mem_invIds α _).1 (mem_linOrder.1 he).1
  have hsub := hab.sublist_invIds hbinv h.wf
  have hidx := idxOf_lt_of_sublist_pair (nodup_invIds α) hsub
  have ha : a ∈ invIds α := hsub.subset (by simp)
  refine sublist_pair_of_pairwise (f := key H α ls) (List.pairwise_map.2 pairwise_linOrder)
    (h.complete hab.completed) hb (key_lt_key ha ?_)
  have := h.level_le_of_precedes hab hb
  omega

/-- The updates linearized before a completed query are exactly those in the causal history of
its learned state. -/
lemma upd_mem_prefix_iff {L₁ L₂ : List (OpId P × D.spec.Op)} {x : OpId P} {q : D.Q}
    {s : D.S} (hL : linOrder H α ls = L₁ ++ (x, .qry q) :: L₂)
    (hq : opOf α x = some (CRDT.Cmd.qry q)) (hs : ls x = some s) (u : D.U) :
    updOp u ∈ L₁.map Prod.snd ↔ u ∈ H.C s := by
  have hsort := (pairwise_linOrder (H := H) (α := α) (ls := ls))
  rw [hL, List.pairwise_append, List.pairwise_cons] at hsort
  have hxL : ((x, CRDT.Cmd.qry q) : OpId P × D.spec.Op) ∈ linOrder H α ls := by
    rw [hL]; simp
  have hx : x ∈ invIds α := (mem_linOrder.1 hxL).1
  have hlx := level_qry (H := H) hq hs
  have hsl := h.mem_learned_of hs
  constructor
  · intro hu
    obtain ⟨e, he, he2⟩ := List.mem_map.1 hu
    have heL : e ∈ linOrder H α ls := by rw [hL]; simp [he]
    have hke : key H α ls e.1 < key H α ls x := hsort.2.2 e he (x, .qry q) (by simp)
    obtain ⟨-, hoe, -⟩ := entry_eq_some (mem_linOrder.1 heL).2
    rw [he2] at hoe
    have hle : level H α ls e.1 ≤ level H α ls x := by
      by_contra hlt
      exact absurd hke (key_lt_key hx (.inl (by omega))).asymm
    rw [level_upd hoe] at hle
    exact (h.urank_le_rank_iff hsl u).1 (by omega)
  · intro hu
    obtain ⟨y, hy⟩ := h.validity_invoked x s hs u hu
    have hyL := mem_linOrder_of_upd (H := H) (ls := ls) hy
    have hlt : key H α ls y < key H α ls x := by
      refine key_lt_key (mem_linOrder.1 hyL).1 (.inl ?_)
      rw [level_upd hy, hlx]
      have := (h.urank_le_rank_iff hsl u).2 hu
      omega
    rw [hL] at hyL
    rcases List.mem_append.1 hyL with h1 | h2
    · exact List.mem_map.2 ⟨_, h1, rfl⟩
    · rcases List.mem_cons.1 h2 with h3 | h3
      · have := congrArg Prod.snd h3; cases this
      · exact absurd (hsort.2.1.1 _ h3) (by simp only; omega)

lemma seq : SeqOK α D.spec.init (linOrder H α ls) := by
  apply seqOK_of_forall
  intro L₁ x o L₂ hL r hr
  have hxL : (x, o) ∈ linOrder H α ls := by rw [hL]; simp
  obtain ⟨-, ho, -⟩ := entry_eq_some (mem_linOrder.1 hxL).2
  cases o with
  | upd u => exact (h.resp_upd x u r ho hr).symm
  | qry q =>
    obtain ⟨s, hs, rfl⟩ := h.resp_query x q r ho hr
    change CRDT.Res.val (D.query q _) = CRDT.Res.val (D.query q s)
    congr 1
    apply H.faithful
    refine (H.C_runOps _ _).trans ?_
    change H.C D.s₀ ∪ _ = _
    rw [H.C_init, Set.empty_union]
    ext u
    exact h.upd_mem_prefix_iff hL ho hs u

/-- The constructed order is a linearization. -/
theorem isLinearization : IsLinearization α (linOrder H α ls) where
  nodup := nodup_linOrder
  op_eq _ hy := (entry_eq_some (mem_linOrder.1 hy).2).2.1
  complete _ hx := h.complete hx
  realtime _ _ hab hb := h.realtime hab hb
  seq := h.seq

end LearnedHistory

/-- **Lemmas 6–8 (Section III-E).** A history whose learned states satisfy Theorems 1–5 is
linearizable. -/
theorem linearizable_of_learnedHistory (H : D.CausalHistory) {α : List (Label P D.spec)}
    {ls : OpId P → Option D.S} (h : LearnedHistory H α ls) : ∃ L, IsLinearization α L :=
  ⟨_, h.isLinearization⟩

end Podc.CRDTReplication
