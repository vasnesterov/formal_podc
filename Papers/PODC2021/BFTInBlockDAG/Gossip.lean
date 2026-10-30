import Papers.PODC2021.BFTInBlockDAG.Block

/-!
# Building the block DAG: Algorithm 1 (with the request buffer of Algorithm 3)

The asynchronous system of Section 3. Servers `S`; the Byzantine servers form the set `Byz`, all
other servers are correct. The network is a set `sent` of point-to-point messages
`(from, to, payload)` that have been sent; a correct server may receive any message sent to it, any
number of times and in any order (so the model covers arbitrary delays, reordering and duplication;
Assumption 1, reliable delivery, is a fairness condition on runs, see `GossipLive.lean`).

**Correct servers** run Algorithm 1; every handler is one atomic event:
* `request s ℓ r`: the user calls `request(ℓ, r)` on `shim(P)` (Algorithm 3, lines 6–7);
* `recv s src (blk B)`: lines 4–5 (put `B` into `blks` unless `B ∈ G`);
* `recv s src (fwd B)`: lines 12–13 (answer a forwarding request if `B ∈ G`);
* `validate s B`: lines 6–9 (for `B ∈ blks` that `s` considers valid: insert it into `G` and add a
  reference to the current block);
* `askFwd s B' B`: lines 10–11 (ask `B'.n` for a missing predecessor `B` of `B' ∈ blks`);
* `disseminate s`: lines 14–18 (seal the current block with all buffered requests, insert it,
  send it to every server, and start the next block). Algorithm 3 lines 10–11 call it repeatedly.

The local block DAG `G` is kept as the list `log` of its blocks in insertion order.

**`valid(s, B)`** (Definition 3.3) is read as: `B` is locally valid (genesis or exactly one parent)
and `s` has already validated (inserted) all predecessors of `B`. This is the only reading under
which line 7 always inserts into a block DAG, as Lemma A.5 claims: with a purely recursive reading
("all predecessors are valid", whether inserted or still in `blks`) line 6 may pick a block before
its predecessor and `G` stops being closed under predecessors.

**Byzantine servers** may send anything, except that they cannot forge signatures: a block they
send must be *authentic* (`Authentic`), i.e. every block with a correct builder in its causal past
was created by that builder.

Ghost variables: `own` (the blocks `s` disseminated) and `reqs` (all requests from the user).

Main results: the invariant `Inv` (`reachable_inv`), which contains Lemma A.4 (`lemma_A_4`),
Lemma A.5 (`lemma_A_5`) and Lemma A.6 (`lemma_A_6`).
-/

set_option linter.unusedSectionVars false

namespace Podc.BFTInBlockDAG

open Block

/-- Network payloads: a block, or a forwarding request `FWD ref(B)`. -/
inductive Payload (S L R : Type) where
  | blk (B : Block S L R)
  | fwd (B : Block S L R)

/-- The local state of a server running Algorithm 1 (and the buffer of Algorithm 3). -/
structure Local (S L R : Type) where
  /-- The block DAG `G`, as the list of its blocks in insertion order. -/
  log : List (Block S L R) := []
  /-- The buffer `blks` of received candidate blocks. -/
  blks : List (Block S L R) := []
  /-- The sequence number `B.k` of the current block `B`. -/
  k : ℕ := 0
  /-- The predecessors `B.preds` of the current block. -/
  preds : List (Block S L R) := []
  /-- The buffer `rqsts` of labelled requests. -/
  rqsts : List (L × R) := []
  /-- Ghost: the blocks disseminated so far, in order. -/
  own : List (Block S L R) := []
  /-- Ghost: all requests received from the user, in order. -/
  reqs : List (L × R) := []

/-- The global state: local states and the set of sent messages `(from, to, payload)`. -/
structure Sys (S L R : Type) where
  /-- Local states. -/
  loc : S → Local S L R
  /-- Messages sent so far. -/
  sent : Set (S × S × Payload S L R)

/-- The initial state. -/
def Sys.init {S L R : Type} : Sys S L R := ⟨fun _ => {}, ∅⟩

/-- Events. -/
inductive Ev (S L R : Type) where
  | request (s : S) (ℓ : L) (r : R)
  | recv (s src : S) (p : Payload S L R)
  | validate (s : S) (B : Block S L R)
  | askFwd (s : S) (B' B : Block S L R)
  | disseminate (s : S)
  | byz (b dst : S) (p : Payload S L R)

variable {S L R : Type} [DecidableEq S] [DecidableEq L] [DecidableEq R]

/-- The local block DAG `G` of a local state. -/
def Local.G (l : Local S L R) : Set (Block S L R) := {B | B ∈ l.log}

/-- The block a server seals at `disseminate` (line 15). -/
def newBlock (s : S) (l : Local S L R) : Block S L R := .mk s l.k l.preds l.rqsts

/-- Replace the local state of `s`. -/
def Sys.upd (σ : Sys S L R) (s : S) (l : Local S L R) : Sys S L R :=
  { σ with loc := Function.update σ.loc s l }

variable (Byz : Set S)

/-- The blocks created by correct servers. -/
def created (σ : Sys S L R) : Set (Block S L R) := {B | ∃ s ∉ Byz, B ∈ (σ.loc s).own}

/-- A block is authentic: every block with a correct builder in its causal past was created by
that builder (signatures cannot be forged). -/
def Authentic (σ : Sys S L R) (B : Block S L R) : Prop :=
  ∀ C, Relation.ReflTransGen Edge C B → C.n ∉ Byz → C ∈ created Byz σ

/-- The guards of the events. -/
def Enabled (σ : Sys S L R) : Ev S L R → Prop
  | .request s _ _ => s ∉ Byz
  | .recv s src p => s ∉ Byz ∧ (src, s, p) ∈ σ.sent
  | .validate s B => s ∉ Byz ∧ B ∈ (σ.loc s).blks ∧ B.LocallyValid ∧
      ∀ C ∈ B.preds, C ∈ (σ.loc s).log
  | .askFwd s B' B => s ∉ Byz ∧ B' ∈ (σ.loc s).blks ∧ B ∈ B'.preds ∧ B ∉ (σ.loc s).blks ∧
      B ∉ (σ.loc s).log
  | .disseminate s => s ∉ Byz
  | .byz b _ p => b ∈ Byz ∧ ∀ B, p = .blk B → Authentic Byz σ B

/-- The effects of the events. -/
def apply (σ : Sys S L R) : Ev S L R → Sys S L R
  | .request s ℓ r => σ.upd s
      { σ.loc s with rqsts := (σ.loc s).rqsts ++ [(ℓ, r)], reqs := (σ.loc s).reqs ++ [(ℓ, r)] }
  | .recv s _ (.blk B) =>
      if B ∈ (σ.loc s).log then σ else σ.upd s { σ.loc s with blks := (σ.loc s).blks.insert B }
  | .recv s src (.fwd B) =>
      if B ∈ (σ.loc s).log then { σ with sent := insert (s, src, .blk B) σ.sent } else σ
  | .validate s B => σ.upd s
      { σ.loc s with log := (σ.loc s).log ++ [B], preds := (σ.loc s).preds ++ [B],
                     blks := (σ.loc s).blks.filter fun C => decide (C ≠ B) }
  | .askFwd s B' B => { σ with sent := insert (s, B'.n, .fwd B) σ.sent }
  | .disseminate s =>
      ⟨Function.update σ.loc s
        { σ.loc s with log := (σ.loc s).log ++ [newBlock s (σ.loc s)], k := (σ.loc s).k + 1,
                       preds := [newBlock s (σ.loc s)], rqsts := [],
                       own := (σ.loc s).own ++ [newBlock s (σ.loc s)] },
       σ.sent ∪ Set.range fun s' => (s, s', .blk (newBlock s (σ.loc s)))⟩
  | .byz b dst p => { σ with sent := insert (b, dst, p) σ.sent }

/-- A step of the system. -/
def Step (σ : Sys S L R) (e : Ev S L R) (σ' : Sys S L R) : Prop :=
  Enabled Byz σ e ∧ σ' = apply σ e

/-- Reachable states. -/
def Reachable : Sys S L R → Prop :=
  Relation.ReflTransGen (fun σ σ' => ∃ e, Step Byz σ e σ') Sys.init

/-! ### The invariant -/

/-- The local invariant of a correct server `s` with local state `l`. -/
structure LInvAt (σ : Sys S L R) (s : S) (l : Local S L R) : Prop where
  /-- Lemma A.5: `G` is a block DAG. -/
  dag : IsBlockDAG l.G
  log_nodup : l.log.Nodup
  preds_sub : ∀ C ∈ l.preds, C ∈ l.log
  own_k : l.own.map Block.k = List.range l.k
  own_n : ∀ D ∈ l.own, D.n = s
  own_sub : ∀ D ∈ l.own, D ∈ l.log
  auth : ∀ B, B ∈ l.log ∨ B ∈ l.blks → Authentic Byz σ B
  disj : ∀ B ∈ l.blks, B ∉ l.log
  par₁ : ∀ C ∈ l.preds, C.n = s → l.own.getLast? = some C
  par₂ : ∀ D, l.own.getLast? = some D → D ∈ l.preds
  /-- Lemma A.6: every block is referenced at most once by the blocks of `s`. -/
  refs_nodup : (l.own.flatMap Block.preds ++ l.preds).Nodup
  ref : ∀ B ∈ l.log, B ∈ l.preds ∨ ∃ D ∈ l.own, B ∈ D.preds
  sent_own : ∀ D ∈ l.own, ∀ s', (s, s', Payload.blk D) ∈ σ.sent
  reqs : l.own.flatMap Block.rs ++ l.rqsts = l.reqs

/-- The local invariant of a correct server `s`. -/
abbrev LInv (σ : Sys S L R) (s : S) : Prop := LInvAt Byz σ s (σ.loc s)

/-- The global invariant. -/
structure Inv (σ : Sys S L R) : Prop where
  loc : ∀ s ∉ Byz, LInv Byz σ s
  sent_auth : ∀ a b B, (a, b, Payload.blk B) ∈ σ.sent → Authentic Byz σ B

variable {Byz}

theorem Authentic.mono {σ σ' : Sys S L R} (h : created Byz σ ⊆ created Byz σ')
    {B : Block S L R} (hB : Authentic Byz σ B) : Authentic Byz σ' B :=
  fun C hC hn => h (hB C hC hn)

theorem Authentic.of_edge {σ : Sys S L R} {B C : Block S L R} (hB : Authentic Byz σ B)
    (hC : Edge C B) : Authentic Byz σ C :=
  fun D hD hn => hB D (hD.tail hC) hn

/-- An authentic block built by a correct server `s` is one of `s`'s own blocks. -/
theorem Inv.mem_own {σ : Sys S L R} (hI : Inv Byz σ) {B : Block S L R} {s : S} (hs : s ∉ Byz)
    (hB : Authentic Byz σ B) (hn : B.n = s) : B ∈ (σ.loc s).own := by
  obtain ⟨s', hs', hB'⟩ := hB B Relation.ReflTransGen.refl (hn ▸ hs)
  have : B.n = s' := (hI.loc s' hs').own_n B hB'
  rw [hn] at this
  subst this
  exact hB'

theorem LInv.k_lt {σ : Sys S L R} {s : S} (h : LInv Byz σ s) {D : Block S L R}
    (hD : D ∈ (σ.loc s).own) : D.k < (σ.loc s).k := by
  have : D.k ∈ (σ.loc s).own.map Block.k := List.mem_map_of_mem hD
  rw [h.own_k] at this
  simpa using this

/-- A block of `G` built by `s` itself is one of its own blocks. -/
theorem Inv.mem_own_of_log {σ : Sys S L R} (hI : Inv Byz σ) {s : S} (hs : s ∉ Byz)
    {B : Block S L R} (hB : B ∈ (σ.loc s).log) (hn : B.n = s) : B ∈ (σ.loc s).own :=
  hI.mem_own hs ((hI.loc s hs).auth B (Or.inl hB)) hn

/-- The new block is not yet in `G`. -/
theorem Inv.newBlock_notMem {σ : Sys S L R} (hI : Inv Byz σ) {s : S} (hs : s ∉ Byz) :
    newBlock s (σ.loc s) ∉ (σ.loc s).log := by
  intro h
  have := (hI.loc s hs).k_lt (hI.mem_own_of_log hs h rfl)
  simp [newBlock] at this

theorem getLast?_own {σ : Sys S L R} {s : S} (h : LInv Byz σ s) (hk : (σ.loc s).k ≠ 0) :
    ∃ D, (σ.loc s).own.getLast? = some D ∧ D.k + 1 = (σ.loc s).k := by
  have h1 := congrArg List.getLast? h.own_k
  rw [List.getLast?_map] at h1
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [hj, List.range_succ, List.getLast?_append, List.getLast?_singleton] at h1
  rw [hj]
  simp only [Option.some_or] at h1
  cases hD : (σ.loc s).own.getLast? with
  | none => rw [hD] at h1; simp at h1
  | some D =>
    rw [hD] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    exact ⟨D, rfl, by omega⟩

/-- Lemma A.4: when a correct server reaches line 16, its block is valid (locally valid, with all
predecessors already in `G`). -/
theorem lemma_A_4 {σ : Sys S L R} (hI : Inv Byz σ) {s : S} (hs : s ∉ Byz) :
    (newBlock s (σ.loc s)).LocallyValid ∧ ∀ C ∈ (newBlock s (σ.loc s)).preds, C ∈ (σ.loc s).log := by
  have h := hI.loc s hs
  refine ⟨?_, fun C hC => h.preds_sub C hC⟩
  by_cases hk : (σ.loc s).k = 0
  · exact Or.inl hk
  · obtain ⟨D, hD, hDk⟩ := getLast?_own h hk
    have hDown : D ∈ (σ.loc s).own := List.mem_of_getLast? hD
    refine Or.inr ⟨D, ⟨h.par₂ D hD, h.own_n D hDown, hDk⟩, fun C hC => ?_⟩
    have := h.par₁ C hC.1 hC.2.1
    rw [hD] at this
    exact (Option.some.inj this).symm

end Podc.BFTInBlockDAG

namespace Podc.BFTInBlockDAG

open Block

variable {S L R : Type} [DecidableEq S] [DecidableEq L] [DecidableEq R] {Byz : Set S}

/-! ### Preservation of the invariant -/

theorem LInvAt.frame {σ σ' : Sys S L R} {s : S} {l : Local S L R} (h : LInvAt Byz σ s l)
    (hc : created Byz σ ⊆ created Byz σ') (hsent : σ.sent ⊆ σ'.sent) : LInvAt Byz σ' s l :=
  { h with
    auth := fun B hB => (h.auth B hB).mono hc
    sent_own := fun D hD s' => hsent (h.sent_own D hD s') }

theorem created_mono {σ σ' : Sys S L R} (h : ∀ s, (σ.loc s).own ⊆ (σ'.loc s).own) :
    created Byz σ ⊆ created Byz σ' := by
  rintro B ⟨s, hs, hB⟩
  exact ⟨s, hs, h s hB⟩

/-- Building the invariant after a step that changes only the local state of `s` (and possibly
grows `sent`). -/
theorem Inv.of_upd {σ σ' : Sys S L R} (hI : Inv Byz σ) {s : S} {l' : Local S L R}
    (hloc : σ'.loc = Function.update σ.loc s l') (hsent : σ.sent ⊆ σ'.sent)
    (hc : created Byz σ ⊆ created Byz σ') (hs : s ∉ Byz → LInvAt Byz σ' s l')
    (hauth : ∀ a b B, (a, b, Payload.blk B) ∈ σ'.sent → (a, b, Payload.blk B) ∉ σ.sent →
      Authentic Byz σ' B) : Inv Byz σ' := by
  refine ⟨fun s' hs' => ?_, fun a b B hB => ?_⟩
  · by_cases h : s' = s
    · subst h
      show LInvAt Byz σ' s' (σ'.loc s')
      rw [hloc, Function.update_self]
      exact hs hs'
    · show LInvAt Byz σ' s' (σ'.loc s')
      rw [hloc, Function.update_of_ne h]
      exact (hI.loc s' hs').frame hc hsent
  · by_cases hB' : (a, b, Payload.blk B) ∈ σ.sent
    · exact (hI.sent_auth a b B hB').mono hc
    · exact hauth a b B hB hB'

/-- Building the invariant after a step that changes only `sent`. -/
theorem Inv.of_sent {σ σ' : Sys S L R} (hI : Inv Byz σ) (hloc : σ'.loc = σ.loc)
    (hsent : σ.sent ⊆ σ'.sent)
    (hauth : ∀ a b B, (a, b, Payload.blk B) ∈ σ'.sent → (a, b, Payload.blk B) ∉ σ.sent →
      Authentic Byz σ B) : Inv Byz σ' := by
  have hc : created Byz σ ⊆ created Byz σ' := created_mono fun s => by rw [hloc]
  refine ⟨fun s hs => ?_, fun a b B hB => ?_⟩
  · show LInvAt Byz σ' s (σ'.loc s)
    rw [hloc]
    exact (hI.loc s hs).frame hc hsent
  · by_cases hB' : (a, b, Payload.blk B) ∈ σ.sent
    · exact (hI.sent_auth a b B hB').mono hc
    · exact (hauth a b B hB hB').mono hc

theorem LInvAt.refs_sub {σ : Sys S L R} {s : S} {l : Local S L R} (h : LInvAt Byz σ s l) :
    ∀ C ∈ l.own.flatMap Block.preds ++ l.preds, C ∈ l.log := by
  intro C hC
  rcases List.mem_append.1 hC with hC | hC
  · obtain ⟨D, hD, hCD⟩ := List.mem_flatMap.1 hC
    exact h.dag.2 D (h.own_sub D hD) C hCD
  · exact h.preds_sub C hC

theorem setOf_mem_append_singleton (l : List (Block S L R)) (B : Block S L R) :
    {x | x ∈ l ++ [B]} = insert B {x | x ∈ l} := by
  ext x; simp [or_comm]

theorem Inv.step_request {σ : Sys S L R} (hI : Inv Byz σ) {s : S} {ℓ : L} {r : R} :
    Inv Byz (apply σ (.request s ℓ r)) := by
  have hc : created Byz σ = created Byz (apply σ (.request s ℓ r)) := by
    ext B; simp only [created, apply, Sys.upd, Set.mem_ofPred_eq]
    refine exists_congr fun s' => and_congr_right fun _ => ?_
    by_cases h : s' = s
    · subst h; simp
    · simp [Function.update_of_ne h]
  refine hI.of_upd rfl subset_rfl hc.subset (fun hs => ?_) (fun a b B h h' => absurd h h')
  have h := hI.loc s hs
  exact { h.frame hc.subset subset_rfl with
    reqs := by simp [← h.reqs] }

theorem Inv.step_recv_blk {σ : Sys S L R} (hI : Inv Byz σ) {s src : S} {B : Block S L R}
    (hen : (src, s, Payload.blk B) ∈ σ.sent) :
    Inv Byz (apply σ (.recv s src (.blk B))) := by
  simp only [apply]
  split_ifs with hB
  · exact hI
  have hc : created Byz σ = created Byz (σ.upd s { σ.loc s with blks := (σ.loc s).blks.insert B }) := by
    ext C; simp only [created, Sys.upd, Set.mem_ofPred_eq]
    refine exists_congr fun s' => and_congr_right fun _ => ?_
    by_cases h : s' = s
    · subst h; simp
    · simp [Function.update_of_ne h]
  refine hI.of_upd rfl subset_rfl hc.subset (fun hs => ?_) (fun a b B h h' => absurd h h')
  have h := (hI.loc s hs).frame hc.subset subset_rfl
  refine { h with auth := ?_, disj := ?_ }
  · rintro C (hC | hC)
    · exact h.auth C (Or.inl hC)
    · rcases List.mem_insert_iff.1 hC with rfl | hC
      · exact (hI.sent_auth _ _ _ hen).mono hc.subset
      · exact h.auth C (Or.inr hC)
  · intro C hC
    rcases List.mem_insert_iff.1 hC with rfl | hC
    · exact hB
    · exact h.disj C hC

theorem Inv.step_recv_fwd {σ : Sys S L R} (hI : Inv Byz σ) {s src : S} {B : Block S L R}
    (hs : s ∉ Byz) : Inv Byz (apply σ (.recv s src (.fwd B))) := by
  simp only [apply]
  split_ifs with hB
  · refine hI.of_sent rfl (Set.subset_insert _ _) fun a b C hC hC' => ?_
    rcases Set.mem_insert_iff.1 hC with h | h
    · simp only [Prod.mk.injEq, Payload.blk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact (hI.loc s hs).auth C (Or.inl hB)
    · exact absurd h hC'
  · exact hI

theorem Inv.step_validate {σ : Sys S L R} (hI : Inv Byz σ) {s : S} {B : Block S L R}
    (hen : Enabled Byz σ (.validate s B)) : Inv Byz (apply σ (.validate s B)) := by
  obtain ⟨hs, hBb, hBv, hBp⟩ := hen
  simp only [apply]
  set l := σ.loc s
  set l' : Local S L R := ⟨l.log ++ [B], l.blks.filter (fun C => decide (C ≠ B)), l.k,
    l.preds ++ [B], l.rqsts, l.own, l.reqs⟩
  have hc : created Byz σ = created Byz (σ.upd s l') := by
    ext C; simp only [created, Sys.upd, Set.mem_ofPred_eq]
    refine exists_congr fun s' => and_congr_right fun _ => ?_
    by_cases h : s' = s
    · subst h; simp [l', l]
    · simp [Function.update_of_ne h]
  refine hI.of_upd rfl subset_rfl hc.subset (fun _ => ?_) (fun a b B h h' => absurd h h')
  have h := (hI.loc s hs).frame hc.subset subset_rfl
  have hBlog : B ∉ l.log := h.disj B hBb
  have hBauth : Authentic Byz σ B := (hI.loc s hs).auth B (Or.inr hBb)
  have hBn : B.n ≠ s := fun hn => hBlog ((hI.loc s hs).own_sub B (hI.mem_own hs hBauth hn))
  refine ⟨?_, ?_, ?_, h.own_k, h.own_n, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.sent_own, h.reqs⟩
  · show IsBlockDAG {x | x ∈ l.log ++ [B]}
    rw [setOf_mem_append_singleton]
    exact h.dag.insert hBv hBp
  · exact List.nodup_append.2 ⟨h.log_nodup, List.nodup_singleton B, by
      intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; rintro rfl; exact hBlog ha⟩
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · exact List.mem_append_left _ (h.preds_sub C hC)
    · exact List.mem_append_right _ hC
  · exact fun D hD => List.mem_append_left _ (h.own_sub D hD)
  · rintro C (hC | hC)
    · rcases List.mem_append.1 hC with hC | hC
      · exact h.auth C (Or.inl hC)
      · rw [List.mem_singleton.1 hC]; exact hBauth.mono hc.subset
    · exact h.auth C (Or.inr (List.mem_of_mem_filter hC))
  · intro C hC hC'
    have hCB : C ≠ B := by simpa using (List.mem_filter.1 hC).2
    rcases List.mem_append.1 hC' with hC' | hC'
    · exact h.disj C (List.mem_of_mem_filter hC) hC'
    · exact hCB (List.mem_singleton.1 hC')
  · intro C hC hCn
    rcases List.mem_append.1 hC with hC | hC
    · exact h.par₁ C hC hCn
    · rw [List.mem_singleton.1 hC] at hCn; exact absurd hCn hBn
  · exact fun D hD => List.mem_append_left _ (h.par₂ D hD)
  · show (l.own.flatMap Block.preds ++ (l.preds ++ [B])).Nodup
    rw [← List.append_assoc]
    exact List.nodup_append.2 ⟨h.refs_nodup, List.nodup_singleton B, by
      intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; rintro rfl
      exact hBlog (h.refs_sub a ha)⟩
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · rcases h.ref C hC with h1 | h1
      · exact Or.inl (List.mem_append_left _ h1)
      · exact Or.inr h1
    · exact Or.inl (List.mem_append_right _ hC)

theorem Inv.step_askFwd {σ : Sys S L R} (hI : Inv Byz σ) {s : S} {B' B : Block S L R} :
    Inv Byz (apply σ (.askFwd s B' B)) :=
  hI.of_sent rfl (Set.subset_insert _ _) fun a b C hC hC' => by
    rcases Set.mem_insert_iff.1 hC with h | h
    · simp at h
    · exact absurd h hC'

theorem Inv.step_byz {σ : Sys S L R} (hI : Inv Byz σ) {b dst : S} {p : Payload S L R}
    (hen : Enabled Byz σ (.byz b dst p)) : Inv Byz (apply σ (.byz b dst p)) :=
  hI.of_sent rfl (Set.subset_insert _ _) fun a b' C hC hC' => by
    rcases Set.mem_insert_iff.1 hC with h | h
    · simp only [Prod.mk.injEq] at h
      exact hen.2 C h.2.2.symm
    · exact absurd h hC'

theorem Inv.step_disseminate {σ : Sys S L R} (hI : Inv Byz σ) {s : S} (hs : s ∉ Byz) :
    Inv Byz (apply σ (.disseminate s)) := by
  set l := σ.loc s
  set B := newBlock s l
  set l' : Local S L R := ⟨l.log ++ [B], l.blks, l.k + 1, [B], [], l.own ++ [B], l.reqs⟩
  have hσ' : apply σ (.disseminate s) =
      ⟨Function.update σ.loc s l', σ.sent ∪ Set.range fun s' => (s, s', Payload.blk B)⟩ := rfl
  rw [hσ']
  set σ' : Sys S L R := ⟨Function.update σ.loc s l', σ.sent ∪ Set.range fun s' => (s, s', .blk B)⟩
  have hc : created Byz σ ⊆ created Byz σ' := created_mono fun s' => by
    by_cases h : s' = s
    · subst h; simp [σ', l', l]
    · simp [σ', Function.update_of_ne h]
  have hBc : B ∈ created Byz σ' := ⟨s, hs, by simp [σ', l']⟩
  have h0 := hI.loc s hs
  have h := h0.frame hc Set.subset_union_left
  have hBlog : B ∉ l.log := hI.newBlock_notMem hs
  have hBauth : Authentic Byz σ' B := by
    intro C hC hCn
    rcases Relation.ReflTransGen.cases_tail hC with rfl | ⟨D, hCD, hD⟩
    · exact hBc
    · exact h.auth D (Or.inl (h0.preds_sub D hD)) C hCD hCn
  have hA4 := lemma_A_4 hI hs
  refine hI.of_upd rfl Set.subset_union_left hc (fun _ => ?_) (fun a b C hC hC' => ?_)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show IsBlockDAG {x | x ∈ l.log ++ [B]}
      rw [setOf_mem_append_singleton]
      exact h.dag.insert hA4.1 hA4.2
    · exact List.nodup_append.2 ⟨h.log_nodup, List.nodup_singleton B, by
        intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; rintro rfl; exact hBlog ha⟩
    · intro C hC
      rw [List.mem_singleton.1 hC]
      exact List.mem_append_right _ (List.mem_singleton_self B)
    · show (l.own ++ [B]).map Block.k = List.range (l.k + 1)
      rw [List.map_append, h.own_k, List.range_succ]
      rfl
    · intro D hD
      rcases List.mem_append.1 hD with hD | hD
      · exact h.own_n D hD
      · rw [List.mem_singleton.1 hD]; rfl
    · intro D hD
      rcases List.mem_append.1 hD with hD | hD
      · exact List.mem_append_left _ (h.own_sub D hD)
      · exact List.mem_append_right _ hD
    · rintro C (hC | hC)
      · rcases List.mem_append.1 hC with hC | hC
        · exact h.auth C (Or.inl hC)
        · rw [List.mem_singleton.1 hC]; exact hBauth
      · exact h.auth C (Or.inr hC)
    · intro C hC hC'
      rcases List.mem_append.1 hC' with hC' | hC'
      · exact h.disj C hC hC'
      · rw [List.mem_singleton.1 hC'] at hC
        exact hBlog (h0.own_sub B (hI.mem_own hs (h0.auth B (Or.inr hC)) rfl))
    · intro C hC _
      rw [List.mem_singleton.1 hC]
      simp [l']
    · intro D hD
      simp only [l', List.getLast?_append, List.getLast?_singleton, Option.some_or] at hD
      rw [← Option.some.inj hD]
      exact List.mem_singleton_self B
    · show ((l.own ++ [B]).flatMap Block.preds ++ [B]).Nodup
      rw [List.flatMap_append, List.flatMap_singleton]
      exact List.nodup_append.2 ⟨h.refs_nodup, List.nodup_singleton B, by
        intro a ha b hb hab; rw [List.mem_singleton] at hb; rw [hab, hb] at ha
        exact hBlog (h.refs_sub _ ha)⟩
    · intro C hC
      rcases List.mem_append.1 hC with hC | hC
      · rcases h.ref C hC with h1 | ⟨D, hD, h1⟩
        · exact Or.inr ⟨B, List.mem_append_right _ (List.mem_singleton_self B), h1⟩
        · exact Or.inr ⟨D, List.mem_append_left _ hD, h1⟩
      · exact Or.inl hC
    · intro D hD s'
      rcases List.mem_append.1 hD with hD | hD
      · exact Or.inl (h0.sent_own D hD s')
      · rw [List.mem_singleton.1 hD]; exact Or.inr ⟨s', rfl⟩
    · show (l.own ++ [B]).flatMap Block.rs ++ [] = l.reqs
      rw [List.append_nil, List.flatMap_append, List.flatMap_singleton, ← h.reqs]
      rfl
  · rcases hC with hC | ⟨s', hs'⟩
    · exact absurd hC hC'
    · simp only [Prod.mk.injEq, Payload.blk.injEq] at hs'
      rw [← hs'.2.2]
      exact hBauth

/-- Every step preserves the invariant. -/
theorem Inv.step {σ σ' : Sys S L R} {e : Ev S L R} (hI : Inv Byz σ) (h : Step Byz σ e σ') :
    Inv Byz σ' := by
  obtain ⟨hen, rfl⟩ := h
  cases e with
  | request s ℓ r => exact hI.step_request
  | recv s src p =>
    cases p with
    | blk B => exact hI.step_recv_blk hen.2
    | fwd B => exact hI.step_recv_fwd hen.1
  | validate s B => exact hI.step_validate hen
  | askFwd s B' B => exact hI.step_askFwd
  | disseminate s => exact hI.step_disseminate hen
  | byz b dst p => exact hI.step_byz hen

theorem inv_init : Inv Byz (Sys.init : Sys S L R) := by
  refine ⟨fun s _ => ?_, fun a b B h => by simp [Sys.init] at h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Sys.init, Local.G, isBlockDAG_empty]

theorem reachable_inv {σ : Sys S L R} (h : Reachable Byz σ) : Inv Byz σ := by
  induction h with
  | refl => exact inv_init
  | tail _ h ih => obtain ⟨e, he⟩ := h; exact ih.step he

/-- Lemma A.5: the local DAG `G` of every correct server is always a block DAG. -/
theorem lemma_A_5 {σ : Sys S L R} (h : Reachable Byz σ) {s : S} (hs : s ∉ Byz) :
    IsBlockDAG (σ.loc s).G ∧ PaperBlockDAG (toGraph (σ.loc s).G) :=
  ⟨((reachable_inv h).loc s hs).dag, ((reachable_inv h).loc s hs).dag.paper⟩

/-- Lemma A.6: a correct server references every block at most once in its blocks (the
concatenation of the predecessor lists of all its disseminated blocks and of its current block has
no duplicates). -/
theorem lemma_A_6 {σ : Sys S L R} (h : Reachable Byz σ) {s : S} (hs : s ∉ Byz) :
    ((σ.loc s).own.flatMap Block.preds ++ (σ.loc s).preds).Nodup :=
  ((reachable_inv h).loc s hs).refs_nodup

end Podc.BFTInBlockDAG
