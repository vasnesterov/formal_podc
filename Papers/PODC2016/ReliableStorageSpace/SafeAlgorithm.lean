import Papers.PODC2016.ReliableStorageSpace.Runs

/-!
# Section 3.1: a safe, wait-free, storage-efficient algorithm (Algorithm 2, Corollary 3)

The paper's Algorithm 2 emulates a *strongly safe*, *wait-free* MWMR register over `n = 2f + k`
fault-prone base objects with a `k`-of-`n` erasure code: every base object stores exactly one piece
(of `D/k` bits) together with a timestamp, so the storage is `nD/k` (Lemma 5).

We define it in the black-box storage model of `Model.lean` (`alg`):

* the code is abstract: piece `i` of value `v` is `enc i v : Fin (2 ^ ℓ)`, and any `k` pieces
  determine the value (`Decodable`);
* timestamps are `⟨num, w⟩` with `w = (c, i)` the write's identifier, ordered lexicographically (the
  paper uses `⟨num, c⟩`; adding the operation index is harmless and makes timestamps unique per write);
* an object stores `none` (initially: timestamp `0`, no block — the model requires objects to start
  without blocks, and the reader returns `v₀` instead of decoding pieces of `v₀`) or a chunk
  `⟨num, w, j⟩` holding the block `(w, j)`;
* `readValue` triggers one read RMW per object and waits for `n - f` responses; a write then triggers
  `update` RMWs (overwrite iff the timestamp is bigger) and waits for `n - f` acknowledgements; a read
  returns the decoded value of the **largest** timestamp of which it has at least `k` pieces, and `v₀`
  if there is none. RMWs are tagged with a phase counter so that late responses are ignored.

Results:
* `objBits_le` (Lemma 5): the base objects store at most `n * ℓ` bits;
* `waitFree` (Lemma 6);
* `stronglySafe` (Lemmas 7–9; Observation 4 is `ots_step`, the quorum intersection is `inter_card`);
* `corollary3`, and `corollary3_replication` (non-vacuity: replication satisfies the hypotheses).

**Deviations from the paper** (details in `differencies.md`):
* line 16 of Algorithm 2 picks *some* timestamp with `≥ k` pieces; we pick the **largest** one. This is
  needed when `k ≤ f`: e.g. replication `n = 3, f = 1, k = 1`: `w₁` stores on objects 1, 2 and returns,
  `w₂` (invoked later) reads objects 1, 2, stores on objects 2, 3 and returns; a later read that hears
  from objects 1, 2 sees one piece of `w₁` and one of `w₂`, and returning `w₁`'s value violates
  (strong) safety. The paper's proof of Lemma 9 overlooks this ("rd reads at least `k` pieces of `v`,
  and thus restores and returns `v`");
* the writer keeps a ghost record `wts` of the timestamps it chose (history variable, used to define
  `σ`); RMWs carry a phase tag and a response is recorded only once per object and phase (the paper
  leaves the matching of responses to phases implicit);
* objects start with timestamp `0` and no piece (instead of pieces of `v₀`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Podc.ReliableStorageSpace.Safe

open Finset Classical
open Podc.ReliableStorageSpace.Alg (Precedes IsWrite Completed lastVal)

/-! ### Definitions: wait-freedom and strong safety -/

section Defs

variable {C N J V : Type}

/-- **Wait-freedom**: in every fair run, every operation of a correct client completes. -/
def WaitFree (A : Alg C N J V) (f : ℕ) : Prop :=
  ∀ ev Fc Fo, A.Fair f ev Fc Fo → ∀ t c, c ∉ Fc → (A.cfg ev t).cur c ≠ none →
    ∃ t' ≥ t, A.Returns ev t' c

/-- **Strong safety** (Section 2.2): "a MWMR register is strongly safe if there exists a linearization
`σw` of the subsequence of `r` consisting of the write operations in `r`, and for every read operation
`rd` that has no concurrent writes in `r`, it is possible to add `rd` at some point in `σw` so as to obtain
a linearization of the subsequence of `r` consisting of the write operations in `r` and `rd`."

For every finite run there is a sequence `σ` of writes (each completed write occurs, real-time order is
respected) such that every completed read `rd` without concurrent writes returns, for every value
assignment, the value of the last write of `σ` among those preceding `rd` (`v₀` if none). Since `rd` has
no concurrent writes and `σ` respects real-time order, the writes of `σ` preceding `rd` form a prefix of
`σ`, so this is exactly "inserting `rd` into `σ`". The sequence `σ` does not depend on the values. -/
def StronglySafe (A : Alg C N J V) (v₀ : V) : Prop :=
  ∀ evs : List (Event C),
    ∃ σ : List (OpId C), σ.Nodup ∧ (∀ w ∈ σ, IsWrite (A.runFrom A.init evs).hist w) ∧
      (∀ w, IsWrite (A.runFrom A.init evs).hist w → Completed (A.runFrom A.init evs).hist w →
        w ∈ σ) ∧
      σ.Pairwise (fun a b => ¬ Precedes (A.runFrom A.init evs).hist b a) ∧
      ∀ (val : OpId C → V) (rd : OpId C) (out : A.Content → V),
        Label.ret rd.1 rd.2 (some out) ∈ (A.runFrom A.init evs).hist →
        (∀ w, IsWrite (A.runFrom A.init evs).hist w →
          Precedes (A.runFrom A.init evs).hist w rd ∨ Precedes (A.runFrom A.init evs).hist rd w) →
        out (A.contents val) =
          lastVal v₀ val (σ.filter (fun w => decide (Precedes (A.runFrom A.init evs).hist w rd)))

/-- A pending RMW other than the executed one stays pending. -/
theorem mem_pend_exec (A : Alg C N J V) {X : A.Config} (hok : A.PendOK X) {c : C} {m : ℕ}
    {p : Pend C N A.R} (hp : A.findP X c m = some p) {q : Pend C N A.R} (hq : q ∈ X.pend)
    (hne : q ≠ p) : q ∈ (A.step X (.exec c m)).pend := by
  rw [Alg.step_exec_some hp]
  refine List.mem_filter.2 ⟨hq, ?_⟩
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_and]
  intro h1 h2
  apply hne
  have := hok.findP_eq hq
  rw [h1, h2, hp] at this
  exact (Option.some.inj this).symm

/-- A label of a run's history was appended by some event of the run. -/
theorem mem_hist_split (A : Alg C N J V) (X : A.Config) (evs : List (Event C))
    {lab : Label C (A.Content → V)} (h : lab ∈ (A.runFrom X evs).hist) :
    lab ∈ X.hist ∨ ∃ pre e post, evs = pre ++ e :: post ∧ lab ∉ (A.runFrom X pre).hist ∧
      lab ∈ (A.step (A.runFrom X pre) e).hist := by
  induction evs generalizing X with
  | nil => exact Or.inl h
  | cons e evs ih =>
    rcases ih (A.step X e) h with h' | ⟨pre, e', post, rfl, h1, h2⟩
    · by_cases hX : lab ∈ X.hist
      · exact Or.inl hX
      · exact Or.inr ⟨[], e, evs, rfl, hX, h'⟩
    · exact Or.inr ⟨e :: pre, e', post, rfl, h1, h2⟩

end Defs

/-! ### The algorithm -/

variable {C V : Type} [LinearOrder C] {n : ℕ}

/-- `k`-of-`n` decodability of a code with pieces `enc i`: any `k` pieces determine the value. -/
def Decodable (k : ℕ) {ℓ : ℕ} (enc : Fin n → V → Fin (2 ^ ℓ)) : Prop :=
  ∀ S : Finset (Fin n), k ≤ S.card → ∀ v v', (∀ i ∈ S, enc i v = enc i v') → v = v'

/-- Timestamps `⟨num, (c, i)⟩`, ordered lexicographically. -/
abbrev Key (C : Type) := ℕ ×ₗ (C ×ₗ ℕ)

/-- The write of a timestamp. -/
def Key.w (κ : Key C) : OpId C := ofLex (ofLex κ).2

/-- A chunk stored in a base object: piece `j` of write `w`, with timestamp `⟨num, w⟩`. -/
structure Chunk (C : Type) (n : ℕ) where
  num : ℕ
  w : OpId C
  j : Fin n

/-- The timestamp of a chunk. -/
def Chunk.key (ch : Chunk C n) : Key C := toLex (ch.num, toLex ch.w)

@[simp] theorem Chunk.key_w (ch : Chunk C n) : ch.key.w = ch.w := rfl

/-- The timestamp of an object state (`⊥` for the initial state). -/
def ots : Option (Chunk C n) → WithBot (Key C)
  | none => ⊥
  | some ch => (ch.key : WithBot (Key C))

/-- RMWs: `rd τ` reads the object; `upd τ ch` stores `ch` iff its timestamp is bigger. `τ` is the tag. -/
inductive Rmw (C : Type) (n : ℕ)
  | rd (tag : ℕ)
  | upd (tag : ℕ) (ch : Chunk C n)

/-- The tag of an RMW. -/
def Rmw.tag : Rmw C n → ℕ
  | .rd τ => τ
  | .upd τ _ => τ

/-- Responses: the object's contents for a read, an acknowledgement for an update. -/
inductive Res (C : Type) (n : ℕ)
  | rdR (tag : ℕ) (x : Option (Chunk C n))
  | ack (tag : ℕ)

/-- Client local state. `tag`: current phase; `upd`: in the update phase of a write; `nxt`: next object
to trigger an RMW on; `resp o`: response of `o` in the current phase; `wts i`: the `num` of the
timestamp chosen by the client's `i`-th operation (a ghost/history variable, never read by the
algorithm's control flow except to build the chunks of the current write). -/
structure Loc (C : Type) (n : ℕ) where
  tag : ℕ
  upd : Bool
  nxt : ℕ
  resp : Fin n → Option (Option (Chunk C n))
  wts : ℕ → ℕ

/-- Blocks of an object state. -/
def cblk : Option (Chunk C n) → Finset (Blk C (Fin n))
  | none => ∅
  | some ch => {(ch.w, ch.j)}

/-- Blocks of a response slot. -/
def sblk : Option (Option (Chunk C n)) → Finset (Blk C (Fin n))
  | none => ∅
  | some x => cblk x

/-- Blocks held by a client: those of the chunks it has read in the current phase. -/
def lblkF (l : Loc C n) : Finset (Blk C (Fin n)) := univ.biUnion (fun o => sblk (l.resp o))

/-- Number of responses of the current phase. -/
def nresp (l : Loc C n) : ℕ := (univ.filter (fun o => (l.resp o).isSome)).card

/-- The largest `num` read in the current phase. -/
def maxNum (l : Loc C n) : ℕ :=
  univ.sup (fun o => match l.resp o with | some (some ch) => ch.num | _ => 0)

/-- The RMW the client triggers on object `o` in the current phase of its operation `(c, i)`. -/
def rmwOf (c : C) (i : ℕ) (op : Op) (l : Loc C n) (o : Fin n) : Rmw C n :=
  if l.upd = true ∧ op = .write then .upd l.tag ⟨l.wts i, (c, i), o⟩ else .rd l.tag

/-- The client's action (Algorithm 2). Phase 1 (`readValue`) triggers a read on every object and waits
for `n - f` responses; then a read returns, and a write picks `num := max + 1` and starts phase 2
(update on every object, wait for `n - f` acknowledgements, return). -/
def actF (f : ℕ) (hn : 0 < n) (c : C) (i : ℕ) (op : Op) (l : Loc C n) :
    Act (Loc C n) (Fin n) (Rmw C n) :=
  if h : l.nxt < n then
    .trigger ⟨l.nxt, h⟩ (rmwOf c i op l ⟨l.nxt, h⟩) { l with nxt := l.nxt + 1 }
  else if n - f ≤ nresp l then
    if l.upd = false ∧ op = .write then
      .trigger ⟨0, hn⟩ (.upd (l.tag + 1) ⟨maxNum l + 1, (c, i), ⟨0, hn⟩⟩)
        { l with tag := l.tag + 1, upd := true, nxt := 1, resp := fun _ => none,
                 wts := Function.update l.wts i (maxNum l + 1) }
    else .ret l
  else .idle

/-- The atomic RMWs (`update` of Algorithm 2, lines 10–12, and `read`). -/
def applyF : Rmw C n → Option (Chunk C n) → Option (Chunk C n) × Res C n
  | .rd τ, x => (x, .rdR τ x)
  | .upd τ ch, x => (if ots x < (ch.key : WithBot (Key C)) then some ch else x, .ack τ)

/-- Receiving a response: recorded iff it belongs to the current phase (and the slot is empty). -/
def recvF (l : Loc C n) (o : Fin n) : Res C n → Loc C n
  | .rdR τ x =>
    if τ = l.tag ∧ l.upd = false ∧ l.resp o = none then
      { l with resp := Function.update l.resp o (some x) } else l
  | .ack τ =>
    if τ = l.tag ∧ l.upd = true ∧ l.resp o = none then
      { l with resp := Function.update l.resp o (some none) } else l

/-- The pieces `j` of timestamp `κ` the client has read. -/
def pcs (l : Loc C n) (κ : Key C) : Finset (Fin n) :=
  univ.filter (fun j => ∃ o ch, l.resp o = some (some ch) ∧ ch.key = κ ∧ ch.j = j)

/-- Timestamps of which the client has read at least `k` pieces. -/
def good (k : ℕ) (l : Loc C n) : Finset (Key C) :=
  univ.biUnion (fun o => match l.resp o with
    | some (some ch) => if k ≤ (pcs l ch.key).card then {ch.key} else ∅
    | _ => ∅)

/-- Decoding: some value satisfying `P`, `v₀` if none. -/
def decodeP (v₀ : V) (P : V → Prop) : V := if h : ∃ v, P v then h.choose else v₀

/-- The value returned by a read (Algorithm 2, lines 15–18): decode the largest timestamp of which at
least `k` pieces were read, `v₀` if there is none. -/
def rdoutF (k ℓ : ℕ) (enc : Fin n → V → Fin (2 ^ ℓ)) (v₀ : V) (l : Loc C n)
    (g : (b : Blk C (Fin n)) → Fin (2 ^ ℓ)) : V :=
  if h : (good k l).Nonempty then
    decodeP v₀ (fun v => ∀ j ∈ pcs l ((good k l).max' h),
      enc j v = g (((good k l).max' h).w, j))
  else v₀

/-- Blocks of an RMW. -/
def rmwBlk : Rmw C n → Finset (Blk C (Fin n))
  | .rd _ => ∅
  | .upd _ ch => cblk (some ch)

/-- Blocks of a response. -/
def resBlk : Res C n → Finset (Blk C (Fin n))
  | .rdR _ x => cblk x
  | .ack _ => ∅

theorem mem_lblkF {l : Loc C n} {b : Blk C (Fin n)} :
    b ∈ lblkF l ↔ ∃ o ch, l.resp o = some (some ch) ∧ b = (ch.w, ch.j) := by
  simp only [lblkF, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨o, ho⟩
    rcases h : l.resp o with _ | _ | ch <;> rw [h] at ho <;> simp [sblk, cblk] at ho
    exact ⟨o, ch, h, ho⟩
  · rintro ⟨o, ch, h, rfl⟩
    exact ⟨o, by simp [h, sblk, cblk]⟩

theorem lblkF_update {l : Loc C n} {o : Fin n} {s : Option (Option (Chunk C n))} :
    lblkF { l with resp := Function.update l.resp o s } ⊆ lblkF l ∪ sblk s := by
  intro b hb
  simp only [lblkF, mem_biUnion, mem_univ, true_and, mem_union] at hb ⊢
  obtain ⟨o', ho'⟩ := hb
  by_cases h : o' = o
  · subst h; simp at ho'; exact Or.inr ho'
  · simp [Function.update_apply, h] at ho'; exact Or.inl ⟨o', ho'⟩

/-- `s ⊆ t ∪ u` for an arbitrary decidability instance (the model is elaborated classically). -/
theorem subset_union_of {α : Type} {inst : DecidableEq α} {s t u : Finset α}
    (h : ∀ b ∈ s, b ∈ t ∨ b ∈ u) : s ⊆ @Union.union _ (@Finset.instUnion α inst) t u := by
  letI := inst
  intro b hb
  exact Finset.mem_union.2 (h b hb)

/-- `Function.update` lemmas for an arbitrary decidability instance (the model's terms use classical
decidability, while this file has `LinearOrder C` and `Fin n`). -/
@[simp] theorem upd_self' {α β : Type} {inst : DecidableEq α} (g : α → β) (a : α) (v : β) :
    @Function.update α (fun _ => β) inst g a v a = v := by
  letI := inst; exact Function.update_self a v g

theorem upd_ne' {α β : Type} {inst : DecidableEq α} (g : α → β) {a a' : α} (v : β) (h : a' ≠ a) :
    @Function.update α (fun _ => β) inst g a v a' = g a' := by
  letI := inst; exact Function.update_of_ne h v g

theorem upd_eq_self' {α β : Type} {inst : DecidableEq α} (g : α → β) (a : α) :
    @Function.update α (fun _ => β) inst g a (g a) = g := by
  letI := inst; exact Function.update_eq_self a g

theorem upd_apply' {α β : Type} {inst : DecidableEq α} (g : α → β) (a a' : α) (v : β) :
    @Function.update α (fun _ => β) inst g a v a' = @ite _ (a' = a) (inst a' a) v (g a') := by
  letI := inst; exact Function.update_apply g a v a'

theorem mem_union_of {α : Type} {inst : DecidableEq α} {s t : Finset α} {b : α} :
    b ∈ @Union.union _ (@Finset.instUnion α inst) s t ↔ b ∈ s ∨ b ∈ t := by
  letI := inst
  exact Finset.mem_union

variable (f k ℓ : ℕ) (enc : Fin n → V → Fin (2 ^ ℓ)) (v₀ : V) (hℓ : 0 < ℓ) (hn : 0 < n)

/-- **Algorithm 2** in the black-box storage model. -/
@[reducible] def alg : Alg C (Fin n) (Fin n) V where
  L := Loc C n
  O := Option (Chunk C n)
  R := Rmw C n
  Res := Res C n
  linit _ := ⟨0, false, 0, fun _ => none, fun _ => 0⟩
  oinit _ := none
  invoke _ _ _ l := { l with tag := l.tag + 1, upd := false, nxt := 0, resp := fun _ => none }
  act c i op l := actF f hn c i op l
  apply := applyF
  recv _ l o res := recvF l o res
  sz _ := ℓ
  enc := enc
  rdout _ l g := rdoutF k ℓ enc v₀ l g
  lblk := lblkF
  oblk := cblk
  rblk := rmwBlk
  resblk := resBlk
  sz_pos _ := hℓ
  linit_blk _ := by ext b; simp [lblkF, sblk]
  oinit_blk _ := rfl
  invoke_blk _ _ _ _ b hb := by simp [lblkF, sblk] at hb
  act_trigger_blk c i op l o r l' h b hb := by
    simp only [actF] at h
    split_ifs at h with h1 h2 h3
    · cases h
      simp only [mem_union] at hb
      rcases hb with hb | hb
      · simp only [rmwOf] at hb
        split_ifs at hb with h4
        · simp [rmwBlk, cblk] at hb; exact Or.inr ⟨h4.2, by rw [hb]⟩
        · simp [rmwBlk] at hb
      · exact Or.inl hb
    · cases h
      simp only [mem_union] at hb
      rcases hb with hb | hb
      · simp [rmwBlk, cblk] at hb; exact Or.inr ⟨h3.2, by rw [hb]⟩
      · simp [lblkF, sblk] at hb
  act_ret_blk c i op l l' h := by
    simp only [actF] at h
    split_ifs at h <;> cases h; exact subset_rfl
  apply_blk r ob := by
    apply subset_union_of
    intro b hb
    rw [mem_union_of] at hb
    cases r with
    | rd τ => simp only [applyF, resBlk] at hb; rcases hb with hb | hb <;> exact Or.inl hb
    | upd τ ch =>
      simp only [applyF, resBlk] at hb
      rcases hb with hb | hb
      · split_ifs at hb
        · exact Or.inr hb
        · exact Or.inl hb
      · simp at hb
  recv_blk c l o res := by
    apply subset_union_of
    intro b hb
    have key : ∀ s, b ∈ lblkF { l with resp := Function.update l.resp o s } →
        b ∈ lblkF l ∨ b ∈ sblk s := fun s hb' => by
      have := lblkF_update hb'
      simpa using this
    cases res with
    | rdR τ x =>
      simp only [recvF] at hb
      split_ifs at hb
      · exact key _ hb
      · exact Or.inl hb
    | ack τ =>
      simp only [recvF] at hb
      split_ifs at hb
      · rcases key _ hb with h | h
        · exact Or.inl h
        · simp [sblk, cblk] at h
      · exact Or.inl hb
  rdout_congr c l g g' h := by
    simp only [rdoutF]
    split_ifs with hne
    · congr 1
      funext v
      apply propext
      apply forall_congr'; intro j; apply imp_congr_right; intro hj
      rw [h]
      simp only [pcs, mem_filter, mem_univ, true_and] at hj
      obtain ⟨o, ch, h1, h2, h3⟩ := hj
      exact mem_lblkF.2 ⟨o, ch, h1, by rw [← h2, ← h3]; rfl⟩
    · rfl

/-! ### Histories -/

section Hist

variable {Out : Type}

/-- Two labels are about the same operation and of the same kind. -/
def SameId : Label C Out → Label C Out → Prop
  | .inv c i _, .inv c' i' _ => c = c' ∧ i = i'
  | .ret c i _, .ret c' i' _ => c = c' ∧ i = i'
  | _, _ => False

theorem precedes_mono {h₁ h₂ : List (Label C Out)} (hp : h₁ <+: h₂) {a b : OpId C}
    (h : Precedes h₁ a b) : Precedes h₂ a b := by
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨i, j, hij, ⟨out, hi⟩, ⟨op, hj⟩⟩ := h
  have hj' : j < h₁.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  refine ⟨i, j, hij, ⟨out, ?_⟩, ⟨op, ?_⟩⟩
  · rw [List.getElem?_append_left (by omega)]; exact hi
  · rw [List.getElem?_append_left hj']; exact hj

theorem precedes_append {h : List (Label C Out)} {lab : Label C Out} {a b : OpId C}
    (hp : Precedes (h ++ [lab]) a b) :
    Precedes h a b ∨ ((∃ op, lab = .inv b.1 b.2 op) ∧ ∃ out, Label.ret a.1 a.2 out ∈ h) := by
  obtain ⟨i, j, hij, ⟨out, hi⟩, ⟨op, hj⟩⟩ := hp
  have hjl : j < h.length + 1 := by
    by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
  have hi' : h[i]? = some (Label.ret a.1 a.2 out) := by
    rwa [List.getElem?_append_left (by omega)] at hi
  by_cases hjh : j < h.length
  · left
    exact ⟨i, j, hij, ⟨out, hi'⟩, ⟨op, by rwa [List.getElem?_append_left hjh] at hj⟩⟩
  · right
    have : j = h.length := by omega
    subst this
    simp at hj
    exact ⟨⟨op, hj⟩, out, List.mem_of_getElem? hi'⟩

theorem mem_of_precedes_left {h : List (Label C Out)} {a b : OpId C} (hp : Precedes h a b) :
    ∃ out, Label.ret a.1 a.2 out ∈ h := by
  obtain ⟨i, j, -, ⟨out, hi⟩, -⟩ := hp
  exact ⟨out, List.mem_of_getElem? hi⟩

theorem mem_of_precedes_right {h : List (Label C Out)} {a b : OpId C} (hp : Precedes h a b) :
    ∃ op, Label.inv b.1 b.2 op ∈ h := by
  obtain ⟨i, j, -, -, ⟨op, hj⟩⟩ := hp
  exact ⟨op, List.mem_of_getElem? hj⟩

/-- In a history without repeated labels, a label determines its position. -/
theorem pos_unique {h : List (Label C Out)} (hpw : h.Pairwise (fun a b => ¬ SameId a b))
    {i j : ℕ} {a b : Label C Out} (hi : h[i]? = some a) (hj : h[j]? = some b) (hab : SameId a b) :
    i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hj' : j < h.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
    have := List.pairwise_iff_getElem.1 hpw i j (by omega) hj' hlt
    rw [List.getElem?_eq_getElem (by omega)] at hi
    rw [List.getElem?_eq_getElem hj'] at hj
    simp only [Option.some.injEq] at hi hj
    rw [hi, hj] at this; exact this hab
  · have hi' : i < h.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
    have := List.pairwise_iff_getElem.1 hpw j i (by omega) hi' hlt
    rw [List.getElem?_eq_getElem (by omega)] at hj
    rw [List.getElem?_eq_getElem hi'] at hi
    simp only [Option.some.injEq] at hi hj
    rw [hi, hj] at this
    apply this
    revert hab; cases a <;> cases b <;> simp [SameId] <;> intros <;> simp_all

theorem mem_writesOf' {h : List (Label C Out)} {w : OpId C} :
    w ∈ Alg.writesOf h ↔ IsWrite h w := by
  unfold Alg.writesOf IsWrite
  simp only [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxw⟩
    rcases x with ⟨c, k, _ | _⟩ | ⟨c, k, o⟩ <;> simp at hxw
    subst hxw
    exact hx
  · intro hw
    exact ⟨_, hw, rfl⟩

theorem lt_of_getElem? {α : Type} {l : List α} {i : ℕ} {a : α} (h : l[i]? = some a) :
    i < l.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h

theorem prefix_getElem? {α : Type} {h₁ h₂ : List α} (hp : h₁ <+: h₂) {i : ℕ} {a : α}
    (h : h₁[i]? = some a) : h₂[i]? = some a := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (lt_of_getElem? h)]; exact h

theorem prefix_getElem?_of_lt {α : Type} {h₁ h₂ : List α} (hp : h₁ <+: h₂) {i : ℕ}
    (hi : i < h₁.length) : h₂[i]? = h₁[i]? := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left hi]

end Hist

/-! ### Lemma 5: storage -/

section Proofs

variable {f k ℓ : ℕ} {enc : Fin n → V → Fin (2 ^ ℓ)} {v₀ : V} {hℓ : 0 < ℓ} {hn : 0 < n}

local notation "𝔸" => alg (C := C) f k ℓ enc v₀ hℓ hn

/-- **Lemma 5.** Every base object stores at most one piece (`ℓ` bits), so the base objects store at
most `n * ℓ` bits (`nD/k` for pieces of `D/k` bits). -/
theorem objBits_le (X : (𝔸).Config) : (𝔸).objBits X ≤ n * ℓ := by
  unfold Alg.objBits
  calc ∑ o, (𝔸).bits ((𝔸).oblk (X.obj o)) ≤ ∑ _o : Fin n, ℓ := by
        apply sum_le_sum
        intro o _
        change (𝔸).bits (cblk (X.obj o)) ≤ ℓ
        rcases X.obj o with _ | ch
        · simp [Alg.bits, cblk]
        · simp [Alg.bits, cblk, alg]
    _ = n * ℓ := by simp

/-! ### Basic facts about steps -/

theorem actF_trigger {c : C} {i : ℕ} {op : Op} {l l' : Loc C n} {o : Fin n} {r : Rmw C n}
    (h : actF f hn c i op l = .trigger o r l') :
    (∃ h : l.nxt < n, o = ⟨l.nxt, h⟩ ∧ r = rmwOf c i op l o ∧ l' = { l with nxt := l.nxt + 1 }) ∨
    (n ≤ l.nxt ∧ n - f ≤ nresp l ∧ l.upd = false ∧ op = .write ∧ o = ⟨0, hn⟩ ∧
      r = .upd (l.tag + 1) ⟨maxNum l + 1, (c, i), ⟨0, hn⟩⟩ ∧
      l' = { l with tag := l.tag + 1, upd := true, nxt := 1, resp := fun _ => none,
                    wts := Function.update l.wts i (maxNum l + 1) }) := by
  unfold actF at h
  split_ifs at h with h1 h2 h3
  · cases h; exact Or.inl ⟨h1, rfl, rfl, rfl⟩
  · cases h; exact Or.inr ⟨by omega, h2, h3.1, h3.2, rfl, rfl, rfl⟩

theorem actF_ret {c : C} {i : ℕ} {op : Op} {l l' : Loc C n} (h : actF f hn c i op l = .ret l') :
    l' = l ∧ n ≤ l.nxt ∧ n - f ≤ nresp l ∧ (l.upd = true ∨ op = .read) := by
  unfold actF at h
  split_ifs at h with h1 h2 h3
  · cases h
    refine ⟨rfl, by omega, h2, ?_⟩
    cases hu : l.upd
    · cases op
      · simp [hu] at h3
      · exact Or.inr rfl
    · exact Or.inl rfl

/-- The timestamp of an object only grows (Observation 4, one step). -/
theorem ots_applyF (r : Rmw C n) (x : Option (Chunk C n)) : ots x ≤ ots (applyF r x).1 := by
  cases r with
  | rd τ => exact le_rfl
  | upd τ ch =>
    simp only [applyF]
    split_ifs with h
    · exact h.le
    · exact le_rfl

theorem ots_step (X : (𝔸).Config) (e : Event C) (o : Fin n) :
    ots (X.obj o) ≤ ots (((𝔸).step X e).obj o) := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o', r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1]
  · simp only [Function.update_apply]
    split_ifs with ho
    · subst ho; exact ots_applyF _ _
    · exact le_rfl

/-! ### Ghost timestamps of writes -/

/-- The timestamp of write `w` (from the writer's ghost variable `wts`). -/
def keyW (X : (𝔸).Config) (w : OpId C) : Key C := toLex ((X.loc w.1).wts w.2, toLex w)

/-- `w` has chosen its timestamp: it is past its `readValue` phase. -/
def PastT (X : (𝔸).Config) (w : OpId C) : Prop :=
  w.2 < X.cnt w.1 ∨ (w.2 = X.cnt w.1 ∧ (X.loc w.1).upd = true ∧ X.cur w.1 = some .write)

/-- A chunk is *valid*: it belongs to a write invoked in the history that has chosen its timestamp, and
carries that timestamp. -/
def ValidCh (X : (𝔸).Config) (ch : Chunk C n) : Prop :=
  IsWrite X.hist ch.w ∧ ch.num = (X.loc ch.w.1).wts ch.w.2 ∧ PastT X ch.w

theorem ValidCh.key_eq {X : (𝔸).Config} {ch : Chunk C n} (h : ValidCh X ch) :
    ch.key = keyW X ch.w := by
  simp [Chunk.key, keyW, h.2.1]

/-- `Y` extends `X`: the history grows and chosen timestamps persist. -/
def Ext (X Y : (𝔸).Config) : Prop :=
  X.hist <+: Y.hist ∧ ∀ w, PastT X w → PastT Y w ∧ (Y.loc w.1).wts w.2 = (X.loc w.1).wts w.2

theorem Ext.refl (X : (𝔸).Config) : Ext X X := ⟨List.prefix_refl _, fun _ h => ⟨h, rfl⟩⟩

theorem Ext.trans {X Y Z : (𝔸).Config} (h1 : Ext X Y) (h2 : Ext Y Z) : Ext X Z :=
  ⟨h1.1.trans h2.1, fun w hw => ⟨(h2.2 w (h1.2 w hw).1).1,
    ((h2.2 w (h1.2 w hw).1).2).trans (h1.2 w hw).2⟩⟩

theorem Ext.keyW_eq {X Y : (𝔸).Config} (h : Ext X Y) {w : OpId C} (hw : PastT X w) :
    keyW Y w = keyW X w := by
  simp [keyW, (h.2 w hw).2]

theorem Ext.validCh {X Y : (𝔸).Config} (h : Ext X Y) {ch : Chunk C n} (hc : ValidCh X ch) :
    ValidCh Y ch :=
  ⟨h.1.subset hc.1, hc.2.1.trans (h.2 _ hc.2.2).2.symm, (h.2 _ hc.2.2).1⟩

theorem Ext.isWrite {X Y : (𝔸).Config} (h : Ext X Y) {w : OpId C} (hw : IsWrite X.hist w) :
    IsWrite Y.hist w := h.1.subset hw

theorem ext_step (X : (𝔸).Config) (e : Event C) : Ext X ((𝔸).step X e) := by
  refine ⟨Alg.hist_step_prefix _ X e, ?_⟩
  rintro ⟨c, i⟩ hw
  rcases Alg.step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o', r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1] <;> simp only [PastT] at hw ⊢
  · exact ⟨hw, trivial⟩
  · exact ⟨hw, trivial⟩
  · by_cases hcc : c = c'
    · subst hcc
      rcases hw with hw | ⟨-, -, hw⟩
      · simp [hw, alg]
      · simp [hc] at hw
    · simp [upd_apply', hcc, hw]
  · by_cases hcc : c = c'
    · subst hcc
      rcases actF_trigger ha with ⟨-, -, -, rfl⟩ | ⟨-, -, hu, -, -, -, rfl⟩
      · simpa using hw
      · rcases hw with hw | ⟨-, hw, -⟩
        · simp [hw, upd_apply', hw.ne]
        · change (X.loc c).upd = true at hw; simp [hw] at hu
    · simp [upd_apply', hcc, hw]
  · by_cases hcc : c = c'
    · subst hcc
      obtain ⟨rfl, -⟩ := actF_ret ha
      simp only [upd_self', upd_apply', ite_true]
      refine ⟨Or.inl ?_, trivial⟩
      rcases hw with hw | ⟨hw, -⟩ <;> omega
    · simp [upd_apply', hcc, hw]
  · by_cases hcc : c = c'
    · subst hcc
      simp only [upd_self']
      have : ((𝔸).recv c (X.loc c) p.obj ((𝔸).apply p.rmw (X.obj p.obj)).2).upd = (X.loc c).upd ∧
          ((𝔸).recv c (X.loc c) p.obj ((𝔸).apply p.rmw (X.obj p.obj)).2).wts = (X.loc c).wts := by
        change (recvF (X.loc c) p.obj _).upd = _ ∧ (recvF (X.loc c) p.obj _).wts = _
        generalize ((𝔸).apply p.rmw (X.obj p.obj)).2 = res
        cases res <;> simp only [recvF] <;> split_ifs <;> simp
      rw [this.1, this.2]
      exact ⟨hw, rfl⟩
    · simp [upd_apply', hcc, hw]

theorem ext_runFrom (X : (𝔸).Config) (evs : List (Event C)) : Ext X ((𝔸).runFrom X evs) := by
  induction evs generalizing X with
  | nil => exact Ext.refl X
  | cons e evs ih => exact (ext_step X e).trans (ih _)

/-! ### The invariant -/

/-- What client `c` knows about object `o` in its current phase: the response if any, otherwise the
object's current contents (which any later response will dominate). -/
def sv (X : (𝔸).Config) (c : C) (o : Fin n) : Option (Chunk C n) := ((X.loc c).resp o).getD (X.obj o)

variable (f) in
/-- The invariant of Algorithm 2. -/
structure Good (X : (𝔸).Config) : Prop where
  pendOK : (𝔸).PendOK X
  curInv : (𝔸).CurInv X
  histRet : ∀ c i out, Label.ret c i out ∈ X.hist → i < X.cnt c
  histInv : ∀ c i op, Label.inv c i op ∈ X.hist → i < X.cnt c ∨ (i = X.cnt c ∧ X.cur c = some op)
  histPw : X.hist.Pairwise (fun a b => ¬ SameId a b)
  rdFlag : ∀ c, X.cur c = some .read → (X.loc c).upd = false
  tagLe : ∀ p ∈ X.pend, Rmw.tag p.rmw ≤ (X.loc p.cl).tag
  pendUpd : ∀ p ∈ X.pend, ∀ τ ch, p.rmw = Rmw.upd τ ch → ch.j = p.obj ∧ ValidCh X ch
  pendCur : ∀ p ∈ X.pend, ∀ op, X.cur p.cl = some op → Rmw.tag p.rmw = (X.loc p.cl).tag →
    p.rmw = rmwOf p.cl (X.cnt p.cl) op (X.loc p.cl) p.obj
  live : ∀ c op, X.cur c = some op → ∀ o : Fin n, o.val < (X.loc c).nxt → (X.loc c).resp o = none →
    ∃ p ∈ X.pend, p.cl = c ∧ p.obj = o ∧ p.rmw = rmwOf c (X.cnt c) op (X.loc c) o
  objV : ∀ o ch, X.obj o = some ch → ch.j = o ∧ ValidCh X ch
  respV : ∀ c o ch, (X.loc c).resp o = some (some ch) → ch.j = o ∧ ValidCh X ch
  ack : ∀ c, X.cur c = some .write → (X.loc c).upd = true → ∀ o, (X.loc c).resp o ≠ none →
    (keyW X (c, X.cnt c) : WithBot (Key C)) ≤ ots (X.obj o)
  cw : ∀ w, IsWrite X.hist w → Completed X.hist w →
    n - f ≤ (univ.filter fun o => (keyW X w : WithBot (Key C)) ≤ ots (X.obj o)).card
  seen : ∀ c op, X.cur c = some op → (X.loc c).upd = false → ∀ w, IsWrite X.hist w →
    Precedes X.hist w (c, X.cnt c) →
    n - f ≤ (univ.filter fun o => (keyW X w : WithBot (Key C)) ≤ ots (sv X c o)).card
  lt : ∀ w₁ w₂, IsWrite X.hist w₁ → IsWrite X.hist w₂ → Precedes X.hist w₁ w₂ → PastT X w₂ →
    keyW X w₁ < keyW X w₂

theorem good_init : Good f (𝔸).init := by
  refine ⟨(𝔸).pendOK_init, (𝔸).curInv_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Alg.init, IsWrite]

theorem inter_card {s t : Finset (Fin n)} : s.card + t.card ≤ n + (s ∩ t).card := by
  have h1 := card_union_add_card_inter s t
  have h2 := card_le_univ (s ∪ t)
  simp only [Fintype.card_fin] at h2
  omega

theorem num_le_maxNum {l : Loc C n} {o : Fin n} {ch : Chunk C n} (h : l.resp o = some (some ch)) :
    ch.num ≤ maxNum l := by
  have := le_sup (f := fun o => match l.resp o with | some (some ch) => ch.num | _ => 0) (mem_univ o)
  simp only [h] at this
  exact this

theorem num_le_of_key_le {num : ℕ} {w : OpId C} {ch : Chunk C n}
    (h : (toLex (num, toLex w) : Key C) ≤ ch.key) : num ≤ ch.num := by
  rw [Chunk.key, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, -⟩ <;> simp at h <;> omega

theorem recvF_fields (l : Loc C n) (o : Fin n) (res : Res C n) :
    (recvF l o res).tag = l.tag ∧ (recvF l o res).upd = l.upd ∧ (recvF l o res).nxt = l.nxt ∧
      (recvF l o res).wts = l.wts := by
  cases res <;> simp only [recvF] <;> split_ifs <;> simp

theorem recvF_resp (l : Loc C n) (o : Fin n) (res : Res C n) (o' : Fin n) :
    (recvF l o res).resp o' = l.resp o' ∨
    (o' = o ∧ l.resp o = none ∧
      ((∃ x, res = .rdR l.tag x ∧ l.upd = false ∧ (recvF l o res).resp o' = some x) ∨
       (res = .ack l.tag ∧ l.upd = true ∧ (recvF l o res).resp o' = some none))) := by
  cases res with
  | rdR τ x =>
    dsimp only [recvF]
    split_ifs with h
    · by_cases ho : o' = o
      · subst ho
        exact Or.inr ⟨rfl, h.2.2, Or.inl ⟨x, by rw [h.1], h.2.1, by simp⟩⟩
      · left; simp [Function.update_of_ne ho]
    · exact Or.inl rfl
  | ack τ =>
    dsimp only [recvF]
    split_ifs with h
    · by_cases ho : o' = o
      · subst ho
        exact Or.inr ⟨rfl, h.2.2, Or.inr ⟨by rw [h.1], h.2.1, by simp⟩⟩
      · left; simp [Function.update_of_ne ho]
    · exact Or.inl rfl

/-! #### Invocation -/

theorem good_inv {X : (𝔸).Config} (hX : Good f X) {c : C} {op : Op} (hc : X.cur c = none) :
    Good f ((𝔸).step X (.inv c op)) := by
  have hok := hX.pendOK.step (.inv c op)
  have hci := (𝔸).curInv_step hX.curInv (.inv c op)
  have hext := ext_step X (.inv c op)
  have hYs := Alg.step_inv_free (A := 𝔸) (op := op) hc
  set Y := (𝔸).step X (.inv c op) with hY
  have hLc : Y.loc c =
      { X.loc c with tag := (X.loc c).tag + 1, upd := false, nxt := 0, resp := fun _ => none } := by
    rw [hYs]; dsimp only; rw [upd_self']
  have hLo : ∀ c', c' ≠ c → Y.loc c' = X.loc c' := fun c' h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hcurc : Y.cur c = some op := by rw [hYs]; dsimp only; rw [upd_self']
  have hcuro : ∀ c', c' ≠ c → Y.cur c' = X.cur c' := fun c' h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hcnt : Y.cnt = X.cnt := by rw [hYs]
  have hobj : Y.obj = X.obj := by rw [hYs]
  have hpend : Y.pend = X.pend := by rw [hYs]
  have hhist : Y.hist = X.hist ++ [.inv c (X.cnt c) op] := by rw [hYs]
  have hwts : ∀ c', (Y.loc c').wts = (X.loc c').wts := by
    intro c'
    by_cases h : c' = c
    · subst h; rw [hLc]
    · rw [hLo c' h]
  have hkey : ∀ w, keyW Y w = keyW X w := by intro w; simp [keyW, hwts]
  have hpast : ∀ w, PastT Y w → PastT X w := by
    rintro ⟨c', i⟩ h
    simp only [PastT, hcnt] at h ⊢
    by_cases hcc : c' = c
    · subst hcc; rw [hLc] at h; simp at h; exact Or.inl h
    · rw [hLo _ hcc, hcuro _ hcc] at h; exact h
  have hIW : ∀ w, IsWrite Y.hist w → (∃ out, Label.ret w.1 w.2 out ∈ X.hist) → IsWrite X.hist w := by
    rintro ⟨c', i⟩ hw ⟨out, hr⟩
    unfold IsWrite at hw ⊢
    rw [hhist, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hw
    · simp at hw; obtain ⟨rfl, rfl, -⟩ := hw
      have := hX.histRet _ _ _ hr; simp at this
  have hIW2 : ∀ w, IsWrite Y.hist w → PastT X w → IsWrite X.hist w := by
    rintro ⟨c', i⟩ hw hp
    unfold IsWrite at hw ⊢
    rw [hhist, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hw
    · simp at hw; obtain ⟨rfl, rfl, -⟩ := hw
      simp [PastT, hc] at hp
  refine ⟨hok, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' i out h
    rw [hhist, List.mem_append] at h
    rcases h with h | h
    · rw [hcnt]; exact hX.histRet _ _ _ h
    · simp at h
  · intro c' i op' h
    rw [hhist, List.mem_append] at h
    rw [hcnt]
    rcases h with h | h
    · rcases hX.histInv _ _ _ h with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · by_cases hcc : c' = c
        · subst hcc; rw [hc] at h2; cases h2
        · exact Or.inr ⟨h1, by rw [hcuro _ hcc]; exact h2⟩
    · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, hcurc⟩
  · rw [hhist]
    refine List.pairwise_append.2 ⟨hX.histPw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    cases a with
    | inv c' i op' =>
      simp only [SameId, not_and]
      rintro rfl rfl
      rcases hX.histInv _ _ _ ha with h | ⟨-, h⟩
      · simp at h
      · rw [hc] at h; cases h
    | ret => simp [SameId]
  · intro c' h
    by_cases hcc : c' = c
    · subst hcc; rw [hLc]
    · rw [hLo _ hcc]; rw [hcuro _ hcc] at h; exact hX.rdFlag _ h
  · intro p hp
    rw [hpend] at hp
    have := hX.tagLe p hp
    by_cases hcc : p.cl = c
    · rw [hcc, hLc]; rw [hcc] at this; simp only; omega
    · rw [hLo _ hcc]; exact this
  · intro p hp τ ch h
    rw [hpend] at hp
    obtain ⟨h1, h2⟩ := hX.pendUpd p hp τ ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro p hp op' hcur htag
    rw [hpend] at hp
    have := hX.tagLe p hp
    by_cases hcc : p.cl = c
    · exfalso; rw [hcc, hLc] at htag; rw [hcc] at this; simp only at htag; omega
    · rw [hLo _ hcc] at htag ⊢; rw [hcuro _ hcc] at hcur; rw [hcnt]
      exact hX.pendCur p hp op' hcur htag
  · intro c' op' hcur o ho hr
    by_cases hcc : c' = c
    · subst hcc; rw [hLc] at ho; simp at ho
    · rw [hLo _ hcc] at ho hr ⊢; rw [hcuro _ hcc] at hcur; rw [hpend, hcnt]
      exact hX.live _ _ hcur o ho hr
  · intro o ch h
    rw [hobj] at h
    obtain ⟨h1, h2⟩ := hX.objV o ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro c' o ch h
    by_cases hcc : c' = c
    · subst hcc; rw [hLc] at h; simp at h
    · rw [hLo _ hcc] at h
      obtain ⟨h1, h2⟩ := hX.respV _ o ch h
      exact ⟨h1, hext.validCh h2⟩
  · intro c' hcur hupd o hr
    by_cases hcc : c' = c
    · subst hcc; rw [hLc] at hupd; simp at hupd
    · rw [hLo _ hcc] at hupd hr; rw [hcuro _ hcc] at hcur; rw [hkey, hobj, hcnt]
      exact hX.ack _ hcur hupd o hr
  · intro w hw ⟨out, hcomp⟩
    rw [hhist, List.mem_append] at hcomp
    rcases hcomp with hcomp | hcomp
    · rw [hobj]; simp only [hkey]
      exact hX.cw w (hIW w hw ⟨out, hcomp⟩) ⟨out, hcomp⟩
    · simp at hcomp
  · intro c' op' hcur hupd w hw hpre
    rw [hhist, hcnt] at hpre
    rcases precedes_append hpre with hp | ⟨⟨op'', hlab⟩, hr⟩
    · by_cases hcc : c' = c
      · subst hcc
        obtain ⟨op3, h3⟩ := mem_of_precedes_right hp
        rcases hX.histInv _ _ _ h3 with h | ⟨-, h⟩
        · simp at h
        · rw [hc] at h; cases h
      · rw [hcuro _ hcc] at hcur; rw [hLo _ hcc] at hupd
        simp only [sv, hLo _ hcc, hobj, hkey]
        exact hX.seen c' op' hcur hupd w (hIW w hw (mem_of_precedes_left hp)) hp
    · simp only [Label.inv.injEq] at hlab
      obtain ⟨rfl, -, -⟩ := hlab
      simp only [sv, hLc, hobj, hkey, Option.getD_none]
      exact hX.cw w (hIW w hw hr) hr
  · intro w₁ w₂ h1 h2 hp hpt
    have hpt' := hpast w₂ hpt
    rw [hhist] at hp
    rcases precedes_append hp with hp | ⟨⟨op'', hlab⟩, -⟩
    · rw [hkey, hkey]
      exact hX.lt w₁ w₂ (hIW w₁ h1 (mem_of_precedes_left hp)) (hIW2 w₂ h2 hpt') hp hpt'
    · obtain ⟨c₂, i₂⟩ := w₂
      simp only [Label.inv.injEq] at hlab
      obtain ⟨rfl, rfl, -⟩ := hlab
      simp [PastT, hc] at hpt'

/-! #### Triggering an RMW within a phase -/

theorem good_trigA {X : (𝔸).Config} (hX : Good f X) {c : C} {op : Op} (hc : X.cur c = some op)
    (hlt : (X.loc c).nxt < n)
    (ha : (𝔸).act c (X.cnt c) op (X.loc c) = .trigger ⟨(X.loc c).nxt, hlt⟩
      (rmwOf c (X.cnt c) op (X.loc c) ⟨(X.loc c).nxt, hlt⟩)
      { X.loc c with nxt := (X.loc c).nxt + 1 }) :
    Good f ((𝔸).step X (.step c)) := by
  have hok := hX.pendOK.step (.step c)
  have hci := (𝔸).curInv_step hX.curInv (.step c)
  have hext := ext_step X (.step c)
  have hYs := Alg.step_step_trigger hc ha
  set Y := (𝔸).step X (.step c) with hY
  have hLc : Y.loc c = { X.loc c with nxt := (X.loc c).nxt + 1 } := by
    rw [hYs]; dsimp only; rw [upd_self']
  have hLo : ∀ c', c' ≠ c → Y.loc c' = X.loc c' := fun c' h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hcur : Y.cur = X.cur := by rw [hYs]
  have hcnt : Y.cnt = X.cnt := by rw [hYs]
  have hobj : Y.obj = X.obj := by rw [hYs]
  have hhist : Y.hist = X.hist := by rw [hYs]
  have hpend : Y.pend = X.pend ++ [⟨c, X.nrmw c, ⟨(X.loc c).nxt, hlt⟩,
      rmwOf c (X.cnt c) op (X.loc c) ⟨(X.loc c).nxt, hlt⟩⟩] := by rw [hYs]
  have hloc : ∀ c', (Y.loc c').upd = (X.loc c').upd ∧ (Y.loc c').wts = (X.loc c').wts ∧
      (Y.loc c').tag = (X.loc c').tag ∧ (Y.loc c').resp = (X.loc c').resp := by
    intro c'
    by_cases h : c' = c
    · subst h; rw [hLc]; exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [hLo c' h]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hkey : ∀ w, keyW Y w = keyW X w := by intro w; simp only [keyW, (hloc _).2.1]
  have hrmw : ∀ c' i op' o', rmwOf c' i op' (Y.loc c') o' = rmwOf c' i op' (X.loc c') o' := by
    intro c' i op' o'; simp only [rmwOf, (hloc c').1, (hloc c').2.1, (hloc c').2.2.1]
  have hpast : ∀ w, PastT Y w ↔ PastT X w := by intro w; simp only [PastT, hcnt, hcur, (hloc _).1]
  have hsv : ∀ c' o', sv Y c' o' = sv X c' o' := by intro c' o'; simp only [sv, (hloc _).2.2.2, hobj]
  refine ⟨hok, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' i out h; rw [hhist] at h; rw [hcnt]; exact hX.histRet _ _ _ h
  · intro c' i op' h; rw [hhist] at h; rw [hcnt, hcur]; exact hX.histInv _ _ _ h
  · rw [hhist]; exact hX.histPw
  · intro c' h; rw [hcur] at h; rw [(hloc c').1]; exact hX.rdFlag c' h
  · intro p hp
    rw [hpend, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · rw [(hloc _).2.2.1]; exact hX.tagLe p hp
    · dsimp only; rw [(hloc c).2.2.1]; unfold rmwOf; split_ifs <;> exact le_rfl
  · intro p hp τ ch h
    rw [hpend, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · obtain ⟨h1, h2⟩ := hX.pendUpd p hp τ ch h
      exact ⟨h1, hext.validCh h2⟩
    · dsimp only at h ⊢
      unfold rmwOf at h
      split_ifs at h with hu
      · simp only [Rmw.upd.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨rfl, ?_, ?_, ?_⟩
        · rw [hhist]; have := hX.curInv c op hc; rw [hu.2] at this; exact this
        · rw [(hloc c).2.1]
        · exact Or.inr ⟨by rw [hcnt], by rw [(hloc c).1]; exact hu.1, by rw [hcur, hc, hu.2]⟩
  · intro p hp op' hcur' htag
    rw [hcur] at hcur'
    rw [hpend, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · rw [(hloc _).2.2.1] at htag; rw [hrmw, hcnt]; exact hX.pendCur p hp op' hcur' htag
    · dsimp only at hcur' ⊢; rw [hc] at hcur'; cases hcur'; rw [hrmw, hcnt]
  · intro c' op' hcur' o' ho' hr
    rw [hcur] at hcur'
    by_cases hcc : c' = c
    · subst hcc
      rw [hLc] at ho' hr
      dsimp only at ho' hr
      by_cases heq : o'.val < (X.loc c').nxt
      · obtain ⟨p, hp, h1, h2, h3⟩ := hX.live c' op' hcur' o' heq hr
        exact ⟨p, by rw [hpend]; exact List.mem_append_left _ hp, h1, h2, by rw [hrmw, hcnt]; exact h3⟩
      · have : o' = ⟨(X.loc c').nxt, hlt⟩ := Fin.ext (by simp only; omega)
        subst this
        refine ⟨_, by rw [hpend]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl,
          ?_⟩
        rw [hc] at hcur'; cases hcur'; rw [hrmw, hcnt]
    · rw [hLo _ hcc] at ho' hr
      obtain ⟨p, hp, h1, h2, h3⟩ := hX.live c' op' hcur' o' ho' hr
      exact ⟨p, by rw [hpend]; exact List.mem_append_left _ hp, h1, h2, by rw [hrmw, hcnt]; exact h3⟩
  · intro o ch h
    rw [hobj] at h
    obtain ⟨h1, h2⟩ := hX.objV o ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro c' o ch h
    rw [(hloc c').2.2.2] at h
    obtain ⟨h1, h2⟩ := hX.respV _ o ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro c' hcur' hupd o hr
    rw [hcur] at hcur'; rw [(hloc _).1] at hupd; rw [(hloc _).2.2.2] at hr
    rw [hkey, hobj, hcnt]; exact hX.ack _ hcur' hupd o hr
  · intro w hw hcomp
    rw [hhist] at hw hcomp
    simp only [hkey, hobj]; exact hX.cw w hw hcomp
  · intro c' op' hcur' hupd w hw hpre
    rw [hcur] at hcur'; rw [(hloc _).1] at hupd; rw [hhist] at hw; rw [hhist, hcnt] at hpre
    simp only [hkey, hsv]; exact hX.seen c' op' hcur' hupd w hw hpre
  · intro w₁ w₂ h1 h2 hp hpt
    rw [hhist] at h1 h2 hp; rw [hpast] at hpt; rw [hkey, hkey]
    exact hX.lt w₁ w₂ h1 h2 hp hpt

/-! #### Phase transition of a write (choice of the timestamp) -/

theorem good_trigB {X : (𝔸).Config} (hX : Good f X) (hq : n < (n - f) + (n - f)) {c : C}
    (hc : X.cur c = some .write) (hu : (X.loc c).upd = false)
    (hcount : n - f ≤ nresp (X.loc c))
    (ha : (𝔸).act c (X.cnt c) .write (X.loc c) = .trigger ⟨0, hn⟩
      (.upd ((X.loc c).tag + 1) ⟨maxNum (X.loc c) + 1, (c, X.cnt c), ⟨0, hn⟩⟩)
      { X.loc c with tag := (X.loc c).tag + 1, upd := true, nxt := 1, resp := fun _ => none,
                     wts := Function.update (X.loc c).wts (X.cnt c) (maxNum (X.loc c) + 1) }) :
    Good f ((𝔸).step X (.step c)) := by
  have hok := hX.pendOK.step (.step c)
  have hci := (𝔸).curInv_step hX.curInv (.step c)
  have hext := ext_step X (.step c)
  have hYs := Alg.step_step_trigger hc ha
  set Y := (𝔸).step X (.step c) with hY
  have hLc : Y.loc c =
      { X.loc c with tag := (X.loc c).tag + 1, upd := true, nxt := 1, resp := fun _ => none,
                     wts := Function.update (X.loc c).wts (X.cnt c) (maxNum (X.loc c) + 1) } := by
    rw [hYs]; dsimp only; rw [upd_self']
  have hLo : ∀ c', c' ≠ c → Y.loc c' = X.loc c' := fun c' h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hcur : Y.cur = X.cur := by rw [hYs]
  have hcnt : Y.cnt = X.cnt := by rw [hYs]
  have hobj : Y.obj = X.obj := by rw [hYs]
  have hhist : Y.hist = X.hist := by rw [hYs]
  have hpend : Y.pend = X.pend ++ [⟨c, X.nrmw c, ⟨0, hn⟩,
      .upd ((X.loc c).tag + 1) ⟨maxNum (X.loc c) + 1, (c, X.cnt c), ⟨0, hn⟩⟩⟩] := by rw [hYs]
  have hkey : ∀ w, w ≠ (c, X.cnt c) → keyW Y w = keyW X w := by
    rintro ⟨c', i⟩ hw
    by_cases hcc : c' = c
    · subst hcc
      have : i ≠ X.cnt c' := fun h => hw (by rw [h])
      simp only [keyW, hLc]
      rw [Function.update_of_ne this]
    · simp only [keyW, hLo _ hcc]
  have hkeyc : keyW Y (c, X.cnt c) = toLex (maxNum (X.loc c) + 1, toLex (c, X.cnt c)) := by
    simp only [keyW, hLc, Function.update_self]
  have hcompl : ∀ w, (∃ out, Label.ret w.1 w.2 out ∈ X.hist) → w ≠ (c, X.cnt c) := by
    rintro ⟨c', i⟩ ⟨out, h⟩ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have := hX.histRet _ _ _ h; simp at this
  refine ⟨hok, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' i out h; rw [hhist] at h; rw [hcnt]; exact hX.histRet _ _ _ h
  · intro c' i op' h; rw [hhist] at h; rw [hcnt, hcur]; exact hX.histInv _ _ _ h
  · rw [hhist]; exact hX.histPw
  · intro c' h
    rw [hcur] at h
    by_cases hcc : c' = c
    · subst hcc; rw [hc] at h; cases h
    · rw [hLo _ hcc]; exact hX.rdFlag c' h
  · intro p hp
    rw [hpend, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · have := hX.tagLe p hp
      by_cases hcc : p.cl = c
      · rw [hcc, hLc]; rw [hcc] at this; dsimp only; omega
      · rw [hLo _ hcc]; exact this
    · dsimp only; rw [hLc]; exact le_rfl
  · intro p hp τ ch h
    rw [hpend, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · obtain ⟨h1, h2⟩ := hX.pendUpd p hp τ ch h
      exact ⟨h1, hext.validCh h2⟩
    · dsimp only at h ⊢
      simp only [Rmw.upd.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨rfl, ?_, ?_, ?_⟩
      · rw [hhist]; exact hX.curInv c _ hc
      · dsimp only; rw [hLc]; dsimp only; rw [Function.update_self]
      · exact Or.inr ⟨by rw [hcnt], by rw [hLc], by rw [hcur, hc]⟩
  · intro p hp op' hcur' htag
    rw [hcur] at hcur'
    rw [hpend, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · have := hX.tagLe p hp
      by_cases hcc : p.cl = c
      · exfalso; rw [hcc, hLc] at htag; rw [hcc] at this; dsimp only at htag; omega
      · rw [hLo _ hcc] at htag ⊢; rw [hcnt]; exact hX.pendCur p hp op' hcur' htag
    · dsimp only at hcur' ⊢; rw [hc] at hcur'; cases hcur'
      rw [hLc, hcnt]; simp [rmwOf]
  · intro c' op' hcur' o' ho' hr
    rw [hcur] at hcur'
    by_cases hcc : c' = c
    · subst hcc
      rw [hLc] at ho'
      dsimp only at ho'
      have : o' = ⟨0, hn⟩ := Fin.ext (by simp only; omega)
      subst this
      refine ⟨_, by rw [hpend]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl,
        ?_⟩
      rw [hc] at hcur'; cases hcur'
      rw [hLc, hcnt]; simp [rmwOf]
    · rw [hLo _ hcc] at ho' hr ⊢
      obtain ⟨p, hp, h1, h2, h3⟩ := hX.live c' op' hcur' o' ho' hr
      exact ⟨p, by rw [hpend]; exact List.mem_append_left _ hp, h1, h2, by rw [hcnt]; exact h3⟩
  · intro o ch h
    rw [hobj] at h
    obtain ⟨h1, h2⟩ := hX.objV o ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro c' o ch h
    by_cases hcc : c' = c
    · subst hcc; rw [hLc] at h; simp at h
    · rw [hLo _ hcc] at h
      obtain ⟨h1, h2⟩ := hX.respV _ o ch h
      exact ⟨h1, hext.validCh h2⟩
  · intro c' hcur' hupd o hr
    rw [hcur] at hcur'
    by_cases hcc : c' = c
    · subst hcc; rw [hLc] at hr; simp at hr
    · rw [hLo _ hcc] at hupd hr
      rw [hkey _ (by simp [hcc]), hobj, hcnt]; exact hX.ack _ hcur' hupd o hr
  · intro w hw hcomp
    rw [hhist] at hw hcomp
    rw [hobj]; simp only [hkey w (hcompl w hcomp)]; exact hX.cw w hw hcomp
  · intro c' op' hcur' hupd w hw hpre
    rw [hcur] at hcur'; rw [hhist] at hw; rw [hhist, hcnt] at hpre
    by_cases hcc : c' = c
    · subst hcc; rw [hLc] at hupd; simp at hupd
    · rw [hLo _ hcc] at hupd
      have : ∀ o, sv Y c' o = sv X c' o := fun o => by simp only [sv, hLo _ hcc, hobj]
      simp only [hkey w (hcompl w (mem_of_precedes_left hpre)), this]
      exact hX.seen c' op' hcur' hupd w hw hpre
  · rintro w₁ ⟨c₂, i₂⟩ h1 h2 hp hpt
    rw [hhist] at h1 h2 hp
    have hw₁ := hcompl w₁ (mem_of_precedes_left hp)
    rw [hkey w₁ hw₁]
    by_cases hw₂ : (c₂, i₂) = (c, X.cnt c)
    · simp only [Prod.mk.injEq] at hw₂
      obtain ⟨rfl, rfl⟩ := hw₂
      rw [hkeyc]
      have hS := hX.seen c₂ _ hc hu w₁ h1 hp
      set S := univ.filter fun o => (keyW X w₁ : WithBot (Key C)) ≤ ots (sv X c₂ o) with hSdef
      set T := univ.filter fun o => ((X.loc c₂).resp o).isSome with hTdef
      have hI := inter_card (s := S) (t := T)
      have hT : n - f ≤ T.card := hcount
      obtain ⟨o, ho⟩ := Finset.card_pos.1 (show 0 < (S ∩ T).card by omega)
      simp only [hSdef, hTdef, mem_inter, mem_filter, mem_univ, true_and] at ho
      obtain ⟨hk, hs⟩ := ho
      rcases hr : (X.loc c₂).resp o with _ | x
      · rw [hr] at hs; cases hs
      · simp only [sv, hr, Option.getD_some] at hk
        rcases x with _ | ch
        · simp [ots] at hk
        · simp only [ots, WithBot.coe_le_coe] at hk
          have h1 := num_le_of_key_le hk
          have h2 := num_le_maxNum hr
          rw [keyW, Prod.Lex.toLex_lt_toLex]
          left; simp only; omega
    · have hpt' : PastT X (c₂, i₂) := by
        simp only [PastT, hcnt, hcur] at hpt ⊢
        by_cases hcc : c₂ = c
        · subst hcc
          rw [hLc] at hpt
          rcases hpt with h | ⟨h, -⟩
          · exact Or.inl h
          · exact absurd (by rw [h]) hw₂
        · rw [hLo _ hcc] at hpt; exact hpt
      rw [hkey _ hw₂]
      exact hX.lt w₁ _ h1 h2 hp hpt'

/-! #### Return -/

theorem good_ret {X : (𝔸).Config} (hX : Good f X) {c : C} {op : Op} {l : Loc C n}
    (hc : X.cur c = some op) (ha : (𝔸).act c (X.cnt c) op (X.loc c) = .ret l) :
    Good f ((𝔸).step X (.step c)) := by
  have hok := hX.pendOK.step (.step c)
  have hci := (𝔸).curInv_step hX.curInv (.step c)
  have hext := ext_step X (.step c)
  have hYs := Alg.step_step_ret hc ha
  obtain ⟨rfl, -, hcount, hflag⟩ := actF_ret ha
  set Y := (𝔸).step X (.step c) with hY
  have hloc : Y.loc = X.loc := by rw [hYs]; dsimp only; exact upd_eq_self' _ _
  have hcurc : Y.cur c = none := by rw [hYs]; dsimp only; rw [upd_self']
  have hcuro : ∀ c', c' ≠ c → Y.cur c' = X.cur c' := fun c' h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hcntc : Y.cnt c = X.cnt c + 1 := by rw [hYs]; dsimp only; rw [upd_self']
  have hcnto : ∀ c', c' ≠ c → Y.cnt c' = X.cnt c' := fun c' h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hcntle : ∀ c', X.cnt c' ≤ Y.cnt c' := by
    intro c'; by_cases h : c' = c
    · subst h; rw [hcntc]; omega
    · rw [hcnto _ h]
  have hobj : Y.obj = X.obj := by rw [hYs]
  have hpend : Y.pend = X.pend := by rw [hYs]
  obtain ⟨out, hhist⟩ : ∃ out, Y.hist = X.hist ++ [.ret c (X.cnt c) out] := ⟨_, by rw [hYs]⟩
  have hkey : ∀ w, keyW Y w = keyW X w := by intro w; simp only [keyW, hloc]
  have hIW : ∀ w, IsWrite Y.hist w ↔ IsWrite X.hist w := by
    intro w; unfold IsWrite; rw [hhist]; simp
  have hwr : IsWrite X.hist (c, X.cnt c) → op = .write ∧ (X.loc c).upd = true := by
    intro h
    rcases hX.histInv _ _ _ h with h | ⟨-, h⟩
    · simp at h
    · rw [hc] at h; cases h
      rcases hflag with h | h
      · exact ⟨rfl, h⟩
      · cases h
  have hprec : ∀ a b, Precedes Y.hist a b → Precedes X.hist a b := by
    intro a b h
    rw [hhist] at h
    rcases precedes_append h with h | ⟨⟨op', h⟩, -⟩
    · exact h
    · cases h
  refine ⟨hok, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' i out' h
    rw [hhist, List.mem_append] at h
    rcases h with h | h
    · exact lt_of_lt_of_le (hX.histRet _ _ _ h) (hcntle c')
    · simp only [List.mem_singleton, Label.ret.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      rw [hcntc]; omega
  · intro c' i op' h
    rw [hhist, List.mem_append] at h
    rcases h with h | h
    · by_cases hcc : c' = c
      · subst hcc
        left; rw [hcntc]
        rcases hX.histInv _ _ _ h with h | ⟨h, -⟩ <;> omega
      · rw [hcnto _ hcc, hcuro _ hcc]; exact hX.histInv _ _ _ h
    · simp at h
  · rw [hhist]
    refine List.pairwise_append.2 ⟨hX.histPw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    cases a with
    | ret c' i out' =>
      simp only [SameId, not_and]
      rintro rfl rfl
      have := hX.histRet _ _ _ ha; simp at this
    | inv => simp [SameId]
  · intro c' h
    by_cases hcc : c' = c
    · subst hcc; rw [hcurc] at h; cases h
    · rw [hloc]; rw [hcuro _ hcc] at h; exact hX.rdFlag _ h
  · intro p hp; rw [hpend] at hp; rw [hloc]; exact hX.tagLe p hp
  · intro p hp τ ch h
    rw [hpend] at hp
    obtain ⟨h1, h2⟩ := hX.pendUpd p hp τ ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro p hp op' hcur' htag
    rw [hpend] at hp; rw [hloc] at htag ⊢
    by_cases hcc : p.cl = c
    · rw [hcc, hcurc] at hcur'; cases hcur'
    · rw [hcuro _ hcc] at hcur'; rw [hcnto _ hcc]; exact hX.pendCur p hp op' hcur' htag
  · intro c' op' hcur' o ho hr
    by_cases hcc : c' = c
    · subst hcc; rw [hcurc] at hcur'; cases hcur'
    · rw [hcuro _ hcc] at hcur'; rw [hloc] at ho hr ⊢; rw [hpend, hcnto _ hcc]
      exact hX.live _ _ hcur' o ho hr
  · intro o ch h
    rw [hobj] at h
    obtain ⟨h1, h2⟩ := hX.objV o ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro c' o ch h
    rw [hloc] at h
    obtain ⟨h1, h2⟩ := hX.respV _ o ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro c' hcur' hupd o hr
    by_cases hcc : c' = c
    · subst hcc; rw [hcurc] at hcur'; cases hcur'
    · rw [hcuro _ hcc] at hcur'; rw [hloc] at hupd hr; rw [hkey, hobj, hcnto _ hcc]
      exact hX.ack _ hcur' hupd o hr
  · rintro ⟨c', i⟩ hw ⟨out', hcomp⟩
    rw [hIW] at hw
    rw [hhist, List.mem_append] at hcomp
    simp only [hkey, hobj]
    rcases hcomp with hcomp | hcomp
    · exact hX.cw _ hw ⟨out', hcomp⟩
    · simp only [List.mem_singleton, Label.ret.injEq] at hcomp
      obtain ⟨rfl, rfl, -⟩ := hcomp
      obtain ⟨rfl, hu⟩ := hwr hw
      refine le_trans hcount (card_le_card ?_)
      intro o ho
      simp only [mem_filter, mem_univ, true_and] at ho ⊢
      exact hX.ack c' hc hu o (by intro h; rw [h] at ho; cases ho)
  · intro c' op' hcur' hupd w hw hpre
    by_cases hcc : c' = c
    · subst hcc; rw [hcurc] at hcur'; cases hcur'
    · rw [hcuro _ hcc] at hcur'; rw [hloc] at hupd; rw [hIW] at hw
      have hpre' := hprec _ _ hpre
      rw [hcnto _ hcc] at hpre'
      have : ∀ o, sv Y c' o = sv X c' o := fun o => by simp only [sv, hloc, hobj]
      simp only [hkey, this]
      exact hX.seen c' op' hcur' hupd w hw hpre'
  · rintro w₁ ⟨c₂, i₂⟩ h1 h2 hp hpt
    rw [hIW] at h1 h2
    rw [hkey, hkey]
    refine hX.lt w₁ _ h1 h2 (hprec _ _ hp) ?_
    simp only [PastT, hloc] at hpt ⊢
    by_cases hcc : c₂ = c
    · subst hcc
      rw [hcntc, hcurc] at hpt
      rcases hpt with h | ⟨-, -, h⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
        · exact Or.inl h
        · obtain ⟨rfl, hu⟩ := hwr h2
          exact Or.inr ⟨rfl, hu, hc⟩
      · cases h
    · rw [hcnto _ hcc, hcuro _ hcc] at hpt; exact hpt

/-! #### An RMW takes effect -/

theorem good_exec {X : (𝔸).Config} (hX : Good f X) {c : C} {m : ℕ} {p : Pend C (Fin n) (𝔸).R}
    (hp : (𝔸).findP X c m = some p) : Good f ((𝔸).step X (.exec c m)) := by
  have hok := hX.pendOK.step (.exec c m)
  have hci := (𝔸).curInv_step hX.curInv (.exec c m)
  have hext := ext_step X (.exec c m)
  have hots := ots_step X (.exec c m)
  have hstay := fun q (hq : q ∈ X.pend) (hne : q ≠ p) => mem_pend_exec (𝔸) hX.pendOK hp hq hne
  obtain ⟨hpmem, hpc, -⟩ := Alg.findP_spec hp
  have hYs := Alg.step_exec_some hp
  set Y := (𝔸).step X (.exec c m) with hY
  set res := (applyF p.rmw (X.obj p.obj)).2 with hres
  have hLc : Y.loc c = recvF (X.loc c) p.obj res := by rw [hYs]; dsimp only; rw [upd_self']
  have hLo : ∀ c', c' ≠ c → Y.loc c' = X.loc c' := fun c' h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hobjp : Y.obj p.obj = (applyF p.rmw (X.obj p.obj)).1 := by
    rw [hYs]; dsimp only; rw [upd_self']
  have hobjo : ∀ o, o ≠ p.obj → Y.obj o = X.obj o := fun o h => by
    rw [hYs]; dsimp only; rw [upd_ne' _ _ h]
  have hcur : Y.cur = X.cur := by rw [hYs]
  have hcnt : Y.cnt = X.cnt := by rw [hYs]
  have hhist : Y.hist = X.hist := by rw [hYs]
  have hsub : ∀ q ∈ Y.pend, q ∈ X.pend := fun q hq => by
    rw [hYs] at hq; exact List.mem_of_mem_filter hq
  have hf : ∀ c', (Y.loc c').tag = (X.loc c').tag ∧ (Y.loc c').upd = (X.loc c').upd ∧
      (Y.loc c').nxt = (X.loc c').nxt ∧ (Y.loc c').wts = (X.loc c').wts := by
    intro c'
    by_cases h : c' = c
    · subst h; rw [hLc]; exact recvF_fields _ _ _
    · rw [hLo c' h]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hresp : ∀ c' o, (Y.loc c').resp o = (X.loc c').resp o ∨
      (c' = c ∧ o = p.obj ∧ (X.loc c).resp p.obj = none ∧
        ((∃ x, res = .rdR (X.loc c).tag x ∧ (X.loc c).upd = false ∧ (Y.loc c).resp o = some x) ∨
         (res = .ack (X.loc c).tag ∧ (X.loc c).upd = true ∧ (Y.loc c).resp o = some none))) := by
    intro c' o
    by_cases h : c' = c
    · subst h
      rw [hLc]
      rcases recvF_resp (X.loc c') p.obj res o with h1 | ⟨h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, h1, h2, h3⟩
    · rw [hLo c' h]; exact Or.inl rfl
  have hkey : ∀ w, keyW Y w = keyW X w := by intro w; simp only [keyW, (hf _).2.2.2]
  have hrmw : ∀ c' i op' o', rmwOf c' i op' (Y.loc c') o' = rmwOf c' i op' (X.loc c') o' := by
    intro c' i op' o'; simp only [rmwOf, (hf c').1, (hf c').2.1, (hf c').2.2.2]
  have hpast : ∀ w, PastT Y w ↔ PastT X w := by
    intro w; simp only [PastT, hcnt, hcur, (hf _).2.1]
  have hrd : ∀ x, res = .rdR (X.loc c).tag x → x = X.obj p.obj := by
    intro x h
    rw [hres] at h
    cases hr : p.rmw with
    | rd τ => rw [hr] at h; simp only [applyF, Res.rdR.injEq] at h; exact h.2.symm
    | upd τ ch => rw [hr] at h; simp [applyF] at h
  have hsv : ∀ c' o, (X.loc c').upd = false → ots (sv X c' o) ≤ ots (sv Y c' o) := by
    intro c' o hu
    rcases hresp c' o with h | ⟨rfl, rfl, h1, ⟨x, hx, -, h3⟩ | ⟨-, h2, -⟩⟩
    · simp only [sv, h]
      rcases (X.loc c').resp o with _ | x
      · exact hots o
      · exact le_rfl
    · simp only [sv, h1, h3, Option.getD_none, Option.getD_some, hrd x hx]; exact le_rfl
    · rw [hu] at h2; cases h2
  refine ⟨hok, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' i out h; rw [hhist] at h; rw [hcnt]; exact hX.histRet _ _ _ h
  · intro c' i op' h; rw [hhist] at h; rw [hcnt, hcur]; exact hX.histInv _ _ _ h
  · rw [hhist]; exact hX.histPw
  · intro c' h; rw [hcur] at h; rw [(hf c').2.1]; exact hX.rdFlag c' h
  · intro q hq; rw [(hf _).1]; exact hX.tagLe q (hsub q hq)
  · intro q hq τ ch h
    obtain ⟨h1, h2⟩ := hX.pendUpd q (hsub q hq) τ ch h
    exact ⟨h1, hext.validCh h2⟩
  · intro q hq op' hcur' htag
    rw [hcur] at hcur'; rw [(hf _).1] at htag; rw [hrmw, hcnt]
    exact hX.pendCur q (hsub q hq) op' hcur' htag
  · intro c' op' hcur' o' ho hr
    rw [hcur] at hcur'; rw [(hf _).2.2.1] at ho
    have hrX : (X.loc c').resp o' = none := by
      rcases hresp c' o' with h | ⟨rfl, rfl, h1, -⟩
      · rw [← h]; exact hr
      · exact h1
    obtain ⟨q, hq, h1, h2, h3⟩ := hX.live c' op' hcur' o' ho hrX
    by_cases hqp : q = p
    · exfalso
      subst hqp
      have hc' : c' = c := h1.symm.trans hpc
      subst hc'; subst h2
      rw [hLc] at hr
      unfold rmwOf at h3
      split_ifs at h3 with hu
      · have : res = .ack (X.loc c').tag := by rw [hres, h3]; simp [applyF]
        rw [this] at hr
        simp [recvF, hrX, hu.1] at hr
      · have hu' : (X.loc c').upd = false := by
          cases hup : (X.loc c').upd
          · rfl
          · cases op'
            · exact absurd ⟨hup, rfl⟩ hu
            · rw [hX.rdFlag _ hcur'] at hup; cases hup
        have : res = .rdR (X.loc c').tag (X.obj q.obj) := by rw [hres, h3]; simp [applyF]
        rw [this] at hr
        simp [recvF, hrX, hu'] at hr
    · exact ⟨q, hstay q hq hqp, h1, h2, by rw [hrmw, hcnt]; exact h3⟩
  · intro o ch h
    by_cases ho : o = p.obj
    · subst ho
      rw [hobjp] at h
      cases hr : p.rmw with
      | rd τ =>
        rw [hr] at h; simp only [applyF] at h
        obtain ⟨h1, h2⟩ := hX.objV _ ch h
        exact ⟨h1, hext.validCh h2⟩
      | upd τ ch' =>
        rw [hr] at h; simp only [applyF] at h
        split_ifs at h
        · cases h
          obtain ⟨h1, h2⟩ := hX.pendUpd p hpmem τ ch hr
          exact ⟨h1, hext.validCh h2⟩
        · obtain ⟨h1, h2⟩ := hX.objV _ ch h
          exact ⟨h1, hext.validCh h2⟩
    · rw [hobjo o ho] at h
      obtain ⟨h1, h2⟩ := hX.objV o ch h
      exact ⟨h1, hext.validCh h2⟩
  · intro c' o ch h
    rcases hresp c' o with h' | ⟨rfl, rfl, -, ⟨x, hx, -, h3⟩ | ⟨-, -, h3⟩⟩
    · rw [h'] at h
      obtain ⟨h1, h2⟩ := hX.respV _ o ch h
      exact ⟨h1, hext.validCh h2⟩
    · rw [h3, hrd x hx] at h
      obtain ⟨h1, h2⟩ := hX.objV _ ch (Option.some.inj h)
      exact ⟨h1, hext.validCh h2⟩
    · rw [h3] at h; cases h
  · intro c' hcur' hupd o hr
    rw [hcur] at hcur'; rw [(hf _).2.1] at hupd; rw [hkey, hcnt]
    rcases hresp c' o with h' | ⟨rfl, rfl, h1, ⟨x, -, h2, -⟩ | ⟨h2, -, -⟩⟩
    · rw [h'] at hr
      exact le_trans (hX.ack _ hcur' hupd o hr) (hots o)
    · rw [hupd] at h2; cases h2
    · -- the acknowledged update was the current write's update on `p.obj`
      have htag : Rmw.tag p.rmw = (X.loc c').tag := by
        rw [hres] at h2
        cases hr : p.rmw with
        | rd τ => rw [hr] at h2; simp [applyF] at h2
        | upd τ ch => rw [hr] at h2; simp only [applyF, Res.ack.injEq] at h2; simp [Rmw.tag, h2]
      have hpc' := hX.pendCur p hpmem .write (by rw [hpc]; exact hcur') (by rw [hpc]; exact htag)
      rw [hpc] at hpc'
      simp only [rmwOf, hupd, and_self, ite_true] at hpc'
      rw [hobjp, hpc']
      simp only [applyF]
      split_ifs with hlt
      · simp [ots, keyW, Chunk.key]
      · push Not at hlt; simpa [keyW, Chunk.key] using hlt
  · intro w hw hcomp
    rw [hhist] at hw hcomp
    refine le_trans (hX.cw w hw hcomp) (card_le_card ?_)
    intro o ho
    simp only [mem_filter, mem_univ, true_and, hkey] at ho ⊢
    exact le_trans ho (hots o)
  · intro c' op' hcur' hupd w hw hpre
    rw [hcur] at hcur'; rw [(hf _).2.1] at hupd; rw [hhist] at hw; rw [hhist, hcnt] at hpre
    refine le_trans (hX.seen c' op' hcur' hupd w hw hpre) (card_le_card ?_)
    intro o ho
    simp only [mem_filter, mem_univ, true_and, hkey] at ho ⊢
    exact le_trans ho (hsv c' o hupd)
  · intro w₁ w₂ h1 h2 hp' hpt
    rw [hhist] at h1 h2 hp'; rw [hpast] at hpt; rw [hkey, hkey]
    exact hX.lt w₁ w₂ h1 h2 hp' hpt

/-! #### The invariant holds in every reachable configuration -/

theorem good_step {X : (𝔸).Config} (hq : n < (n - f) + (n - f)) (hX : Good f X) (e : Event C) :
    Good f ((𝔸).step X e) := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c, op, rfl, hc, -⟩ | ⟨c, op, o, r, l, rfl, hc, ha, -⟩ |
    ⟨c, op, l, rfl, hc, ha, -⟩ | ⟨c, m, p, rfl, hp, -⟩
  · rw [h1]; exact hX
  · rw [h1]; cases hX; constructor <;> assumption
  · exact good_inv hX hc
  · rcases actF_trigger ha with ⟨hlt, rfl, rfl, rfl⟩ | ⟨-, hcount, hu, rfl, rfl, rfl, rfl⟩
    · exact good_trigA hX hc hlt ha
    · exact good_trigB hX hq hc hu hcount ha
  · exact good_ret hX hc ha
  · exact good_exec hX hp

theorem good_runFrom {X : (𝔸).Config} (hq : n < (n - f) + (n - f)) (hX : Good f X)
    (evs : List (Event C)) : Good f ((𝔸).runFrom X evs) := by
  induction evs generalizing X with
  | nil => exact hX
  | cons e evs ih => exact ih (good_step hq hX e)

theorem good_reach (hq : n < (n - f) + (n - f)) (evs : List (Event C)) :
    Good f ((𝔸).runFrom (𝔸).init evs) := good_runFrom hq good_init evs

theorem good_cfg (hq : n < (n - f) + (n - f)) (ev : ℕ → Event C) (t : ℕ) :
    Good f ((𝔸).cfg ev t) := by
  induction t with
  | zero => exact good_init
  | succ t ih => exact good_step hq ih _

/-! ### Strong safety (Lemmas 7–9) -/

/-- Every operation with index below `cnt` was invoked. -/
def HistCnt (X : (𝔸).Config) : Prop := ∀ c i, i < X.cnt c → ∃ op, Label.inv c i op ∈ X.hist

theorem histCnt_step {X : (𝔸).Config} (hX : Good f X) (h : HistCnt X) (e : Event C) :
    HistCnt ((𝔸).step X e) := by
  intro c' i hi
  rcases Alg.step_cases X e with h1 | h1 | ⟨c, op, rfl, hc, h1⟩ | ⟨c, op, o, r, l, rfl, hc, ha, h1⟩ |
    ⟨c, op, l, rfl, hc, ha, h1⟩ | ⟨c, m, p, rfl, hp, h1⟩ <;> rw [h1] at hi ⊢
  · exact h c' i hi
  · exact h c' i hi
  · obtain ⟨op', h'⟩ := h c' i hi; exact ⟨op', List.mem_append_left _ h'⟩
  · exact h c' i hi
  · dsimp only at hi ⊢
    by_cases hcc : c' = c
    · subst hcc
      rw [upd_self'] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · obtain ⟨op', h'⟩ := h c' i hi; exact ⟨op', List.mem_append_left _ h'⟩
      · exact ⟨op, List.mem_append_left _ (hX.curInv _ _ hc)⟩
    · rw [upd_ne' _ _ hcc] at hi
      obtain ⟨op', h'⟩ := h c' i hi; exact ⟨op', List.mem_append_left _ h'⟩
  · exact h c' i hi

theorem histCnt_reach (hq : n < (n - f) + (n - f)) (evs : List (Event C)) :
    HistCnt ((𝔸).runFrom (𝔸).init evs) := by
  suffices ∀ X : (𝔸).Config, Good f X → HistCnt X → HistCnt ((𝔸).runFrom X evs) from
    this _ good_init (fun c i h => by simp [Alg.init] at h)
  induction evs with
  | nil => intro X _ h; exact h
  | cons e evs ih => intro X hX h; exact ih _ (good_step hq hX e) (histCnt_step hX h e)

/-- How a completed read appears in a step. -/
theorem ret_info {X : (𝔸).Config} {e : Event C} {c : C} {i : ℕ} {out : (𝔸).Content → V}
    (hnot : Label.ret c i (some out) ∉ X.hist) (hin : Label.ret c i (some out) ∈ ((𝔸).step X e).hist) :
    e = .step c ∧ X.cur c = some .read ∧ i = X.cnt c ∧ out = (𝔸).rdout c (X.loc c) ∧
      n - f ≤ nresp (X.loc c) ∧
      ((𝔸).step X e).hist = X.hist ++ [Label.ret c i (some out)] := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o, r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1] at hin ⊢
  · exact absurd hin hnot
  · exact absurd hin hnot
  · rw [List.mem_append] at hin
    rcases hin with hin | hin
    · exact absurd hin hnot
    · simp at hin
  · exact absurd hin hnot
  · rw [List.mem_append] at hin
    rcases hin with hin | hin
    · exact absurd hin hnot
    · simp only [List.mem_singleton, Label.ret.injEq] at hin
      obtain ⟨rfl, rfl, hout⟩ := hin
      cases op
      · simp at hout
      · simp only [ite_true, Option.some.injEq] at hout
        obtain ⟨-, -, hcount, -⟩ := actF_ret ha
        exact ⟨rfl, hc, rfl, hout, hcount, by subst hout; simp⟩
  · exact absurd hin hnot

/-- **Lemma 9**, the core: a read with `n - f` responses, all of whose chunks belong to writes that
precede it, returns the value of the preceding write `w` with the biggest timestamp. -/
theorem read_val {X : (𝔸).Config} (hX : Good f X) (hdec : Decodable k enc)
    (hq : n + k ≤ (n - f) + (n - f)) (hk : 1 ≤ k) {c : C} (hc : X.cur c = some .read)
    (hcount : n - f ≤ nresp (X.loc c)) {w : OpId C} (hw : IsWrite X.hist w)
    (hpre : Precedes X.hist w (c, X.cnt c))
    (hmax : ∀ w', IsWrite X.hist w' → keyW X w' ≤ keyW X w) (val : OpId C → V) :
    rdoutF k ℓ enc v₀ (X.loc c) ((𝔸).contents val) = val w := by
  have hu := hX.rdFlag c hc
  have hS := hX.seen c .read hc hu w hw hpre
  set S := univ.filter fun o => (keyW X w : WithBot (Key C)) ≤ ots (sv X c o) with hSdef
  set T := univ.filter fun o => ((X.loc c).resp o).isSome with hTdef
  have hI := inter_card (s := S) (t := T)
  have hT : n - f ≤ T.card := hcount
  have hST : k ≤ (S ∩ T).card := by omega
  have hmem : ∀ o ∈ S ∩ T, ∃ ch, (X.loc c).resp o = some (some ch) ∧ ch.key = keyW X w ∧
      ch.j = o := by
    intro o ho
    simp only [hSdef, hTdef, mem_inter, mem_filter, mem_univ, true_and] at ho
    obtain ⟨hk1, hs⟩ := ho
    rcases hr : (X.loc c).resp o with _ | x
    · rw [hr] at hs; cases hs
    · simp only [sv, hr, Option.getD_some] at hk1
      rcases x with _ | ch
      · simp [ots] at hk1
      · simp only [ots, WithBot.coe_le_coe] at hk1
        obtain ⟨hj, hv⟩ := hX.respV c o ch hr
        have := hmax ch.w hv.1
        rw [← hv.key_eq] at this
        exact ⟨ch, rfl, le_antisymm this hk1, hj⟩
  have hpcs : S ∩ T ⊆ pcs (X.loc c) (keyW X w) := by
    intro o ho
    obtain ⟨ch, h1, h2, h3⟩ := hmem o ho
    simp only [pcs, mem_filter, mem_univ, true_and]
    exact ⟨o, ch, h1, h2, h3⟩
  have hk' : k ≤ (pcs (X.loc c) (keyW X w)).card := le_trans hST (card_le_card hpcs)
  have hgood : keyW X w ∈ good k (X.loc c) := by
    obtain ⟨o, ho⟩ := Finset.card_pos.1 (show 0 < (S ∩ T).card by omega)
    obtain ⟨ch, h1, h2, -⟩ := hmem o ho
    simp only [good, mem_biUnion, mem_univ, true_and]
    refine ⟨o, ?_⟩
    rw [h1]; simp only [h2, if_pos hk', mem_singleton]
  have hle : ∀ κ ∈ good k (X.loc c), κ ≤ keyW X w := by
    intro κ hκ
    simp only [good, mem_biUnion, mem_univ, true_and] at hκ
    obtain ⟨o, ho⟩ := hκ
    rcases hr : (X.loc c).resp o with _ | _ | ch <;> rw [hr] at ho
    · simp at ho
    · simp at ho
    · simp only at ho
      split_ifs at ho
      · rw [mem_singleton] at ho
        subst ho
        obtain ⟨-, hv⟩ := hX.respV c o ch hr
        rw [hv.key_eq]; exact hmax _ hv.1
      · simp at ho
  have hne : (good k (X.loc c)).Nonempty := ⟨_, hgood⟩
  have hmax' : (good k (X.loc c)).max' hne = keyW X w :=
    le_antisymm (hle _ (max'_mem _ _)) (le_max' _ _ hgood)
  unfold rdoutF
  rw [dif_pos hne, hmax']
  unfold decodeP
  have hex : ∃ v, ∀ j ∈ pcs (X.loc c) (keyW X w), enc j v = (𝔸).contents val ((keyW X w).w, j) :=
    ⟨val w, fun j _ => rfl⟩
  rw [dif_pos hex]
  exact hdec _ hk' _ _ (fun j hj => hex.choose_spec j hj)

/-- **Lemma 9**, no preceding write: the read returns `v₀`. -/
theorem read_none {X : (𝔸).Config} (hX : Good f X) {c : C} (hnone : ∀ w, ¬ IsWrite X.hist w)
    (g : (b : Blk C (Fin n)) → Fin (2 ^ ℓ)) : rdoutF k ℓ enc v₀ (X.loc c) g = v₀ := by
  unfold rdoutF
  rw [dif_neg]
  rintro ⟨κ, hκ⟩
  simp only [good, mem_biUnion, mem_univ, true_and] at hκ
  obtain ⟨o, ho⟩ := hκ
  rcases hr : (X.loc c).resp o with _ | _ | ch <;> rw [hr] at ho
  · simp at ho
  · simp at ho
  · exact hnone _ (hX.respV c o ch hr).2.1

theorem getLast?_of_pairwise {l : List (Key C)} (hs : l.Pairwise (· < ·)) {a : Key C} (ha : a ∈ l)
    (hmax : ∀ b ∈ l, b ≤ a) : l.getLast? = some a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.pairwise_cons] at hs
    rcases l with _ | ⟨y, l⟩
    · simp at ha; simp [ha]
    · rw [List.getLast?_cons_cons]
      rcases List.mem_cons.1 ha with rfl | ha'
      · exfalso
        have h1 := hs.1 y (by simp)
        have h2 := hmax y (by simp)
        exact absurd h1 (not_lt.2 h2)
      · exact ih hs.2 ha' (fun b hb => hmax b (List.mem_cons_of_mem _ hb))

/-- **Corollary 3 (safety), Lemmas 7–9.** Algorithm 2 (with `n = 2f + k`, `k ≥ 1`, a `k`-of-`n` code,
and the reader decoding the *largest* timestamp of which it has `k` pieces) emulates a strongly safe
register: `σ` orders the completed writes by timestamp (Definition 2), which respects real-time order
(Lemma 7); a read without concurrent writes returns the value of the preceding write with the largest
timestamp, i.e. of the last write of `σ` preceding it (Lemmas 8 and 9). -/
theorem stronglySafe (hnk : n = 2 * f + k) (hk : 1 ≤ k) (hdec : Decodable k enc) :
    StronglySafe (𝔸) v₀ := by
  have hq : n < (n - f) + (n - f) := by omega
  have hq' : n + k ≤ (n - f) + (n - f) := by omega
  intro evs
  have hG : Good f ((𝔸).runFrom (𝔸).init evs) := good_reach hq evs
  set X := (𝔸).runFrom (𝔸).init evs with hXdef
  set Ks := Finset.sort (((Alg.writesOf X.hist).filter (fun w => Completed X.hist w)).image
    (keyW X)) with hKs
  have hKw : ∀ w, (keyW X w).w = w := fun w => rfl
  have hKs_mem : ∀ κ, κ ∈ Ks ↔ ∃ w, IsWrite X.hist w ∧ Completed X.hist w ∧ keyW X w = κ := by
    intro κ
    rw [hKs, Finset.mem_sort, mem_image]
    simp only [mem_filter, mem_writesOf']
    constructor
    · rintro ⟨w, ⟨h1, h2⟩, h3⟩; exact ⟨w, h1, h2, h3⟩
    · rintro ⟨w, h1, h2, h3⟩; exact ⟨w, ⟨h1, h2⟩, h3⟩
  have hpastX : ∀ w, Completed X.hist w → PastT X w := by
    rintro ⟨c, i⟩ ⟨out, h1⟩; exact Or.inl (hG.histRet _ _ _ h1)
  have hsorted : Ks.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  refine ⟨Ks.map Key.w, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Nodup.map_on ?_ (Finset.sort_nodup _ _)
    intro κ1 h1 κ2 h2 he
    obtain ⟨w1, -, -, rfl⟩ := (hKs_mem κ1).1 h1
    obtain ⟨w2, -, -, rfl⟩ := (hKs_mem κ2).1 h2
    rw [hKw, hKw] at he; rw [he]
  · intro w hw
    rw [List.mem_map] at hw
    obtain ⟨κ, hκ, rfl⟩ := hw
    obtain ⟨w', h1, -, rfl⟩ := (hKs_mem κ).1 hκ
    exact h1
  · intro w h1 h2
    exact List.mem_map.2 ⟨keyW X w, (hKs_mem _).2 ⟨w, h1, h2, rfl⟩, rfl⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hsorted
    intro κ1 κ2 h1 h2 hlt hprec
    obtain ⟨w1, i1, c1, rfl⟩ := (hKs_mem κ1).1 h1
    obtain ⟨w2, i2, -, rfl⟩ := (hKs_mem κ2).1 h2
    rw [hKw, hKw] at hprec
    exact absurd hlt (not_lt.2 (hG.lt w2 w1 i2 i1 hprec (hpastX w1 c1)).le)
  · rintro val ⟨c, i⟩ out hret hnc
    dsimp only at hret
    rcases mem_hist_split (𝔸) (𝔸).init evs hret with h0 | ⟨pre, e, post, hevs, hnot, hin⟩
    · simp [Alg.init] at h0
    have hGY : Good f ((𝔸).runFrom (𝔸).init pre) := good_reach hq pre
    have hHCY : HistCnt ((𝔸).runFrom (𝔸).init pre) := histCnt_reach hq pre
    set Y := (𝔸).runFrom (𝔸).init pre with hYdef
    obtain ⟨rfl, hcY, rfl, hout, hcount, hhistY⟩ := ret_info hnot hin
    have hXeq : X = (𝔸).runFrom ((𝔸).step Y (.step c)) post := by
      rw [hXdef, hevs, Alg.runFrom_append]; rfl
    have hextYX : Ext Y X := by
      have h2 := ext_runFrom ((𝔸).step Y (.step c)) post
      rw [← hXeq] at h2
      exact (ext_step Y _).trans h2
    have hpref : Y.hist ++ [Label.ret c (Y.cnt c) (some out)] <+: X.hist := by
      have h2 := (ext_runFrom ((𝔸).step Y (.step c)) post).1
      rw [← hXeq, hhistY] at h2; exact h2
    have hposret : X.hist[Y.hist.length]? = some (Label.ret c (Y.cnt c) (some out)) :=
      prefix_getElem? hpref (by simp)
    have hYpre : Y.hist <+: X.hist := (List.prefix_append _ _).trans hpref
    obtain ⟨jr, hjr⟩ := List.mem_iff_getElem?.1 (hGY.curInv c .read hcY)
    have hjrX := prefix_getElem? hYpre hjr
    have hjrlt := lt_of_getElem? hjr
    have F2 : ∀ w, Precedes X.hist w (c, Y.cnt c) → Precedes Y.hist w (c, Y.cnt c) := by
      rintro w ⟨i1, j1, hij, ⟨o1, hi1⟩, ⟨op1, hj1⟩⟩
      have := pos_unique hG.histPw hj1 hjrX (by simp [SameId])
      subst this
      refine ⟨i1, j1, hij, ⟨o1, ?_⟩, ⟨_, hjr⟩⟩
      rw [prefix_getElem?_of_lt hYpre (by omega)] at hi1
      exact hi1
    have F1 : ∀ w, IsWrite Y.hist w → Precedes X.hist w (c, Y.cnt c) := by
      intro w hw
      rcases hnc w (hYpre.subset hw) with h1 | ⟨i1, j1, hij, ⟨o1, hi1⟩, ⟨op1, hj1⟩⟩
      · exact h1
      · exfalso
        have h3 := pos_unique hG.histPw hi1 hposret (by simp [SameId])
        obtain ⟨j2, hj2⟩ := List.mem_iff_getElem?.1 hw
        have h4 := pos_unique hG.histPw hj1 (prefix_getElem? hYpre hj2) (by simp [SameId])
        have := lt_of_getElem? hj2
        omega
    have F3 : ∀ w, IsWrite X.hist w → Precedes Y.hist w (c, Y.cnt c) → IsWrite Y.hist w := by
      rintro ⟨c', i'⟩ hw hp
      obtain ⟨o, hr⟩ := mem_of_precedes_left hp
      obtain ⟨op, hinv⟩ := hHCY c' i' (hGY.histRet _ _ _ hr)
      obtain ⟨p1, hp1⟩ := List.mem_iff_getElem?.1 hinv
      obtain ⟨p2, hp2⟩ := List.mem_iff_getElem?.1 hw
      have h5 := prefix_getElem? hYpre hp1
      have := pos_unique hG.histPw h5 hp2 (by simp [SameId])
      subst this
      rw [h5] at hp2
      simp only [Option.some.injEq, Label.inv.injEq] at hp2
      rw [hp2.2.2] at hinv; exact hinv
    have hpastY : ∀ w, Precedes Y.hist w (c, Y.cnt c) → PastT Y w := by
      rintro ⟨c', i'⟩ hp
      obtain ⟨o, hr⟩ := mem_of_precedes_left hp
      exact Or.inl (hGY.histRet _ _ _ hr)
    have hfilt : (Ks.map Key.w).filter (fun w => decide (Precedes X.hist w (c, Y.cnt c))) =
        (Ks.filter (fun κ => decide (Precedes X.hist κ.w (c, Y.cnt c)))).map Key.w := by
      rw [List.filter_map]; rfl
    rw [hfilt, hout]
    change rdoutF k ℓ enc v₀ (Y.loc c) ((𝔸).contents val) = _
    by_cases hne : ∃ w, IsWrite Y.hist w
    · obtain ⟨w₀, hw₀⟩ := hne
      obtain ⟨ws, hws, hmax⟩ := Finset.exists_max_image (Alg.writesOf Y.hist) (keyW Y)
        ⟨w₀, mem_writesOf'.2 hw₀⟩
      rw [mem_writesOf'] at hws
      have hmax' : ∀ w', IsWrite Y.hist w' → keyW Y w' ≤ keyW Y ws :=
        fun w' h => hmax w' (mem_writesOf'.2 h)
      have hpre := F2 _ (F1 _ hws)
      rw [read_val hGY hdec hq' hk hcY hcount hws hpre hmax' val]
      obtain ⟨o5, h5⟩ := mem_of_precedes_left hpre
      have hmemK : keyW X ws ∈ Ks.filter (fun κ => decide (Precedes X.hist κ.w (c, Y.cnt c))) := by
        refine List.mem_filter.2 ⟨(hKs_mem _).2 ⟨ws, hYpre.subset hws, ⟨o5, hYpre.subset h5⟩, rfl⟩,
          ?_⟩
        rw [hKw, decide_eq_true_eq]; exact F1 _ hws
      have hlast := getLast?_of_pairwise (hsorted.filter _) hmemK (by
        intro κ hκ
        rw [List.mem_filter] at hκ
        obtain ⟨hκ1, hκ2⟩ := hκ
        obtain ⟨w, h1, -, rfl⟩ := (hKs_mem κ).1 hκ1
        rw [hKw, decide_eq_true_eq] at hκ2
        have hp := F2 _ hκ2
        have hwY := F3 _ h1 hp
        rw [hextYX.keyW_eq (hpastY _ hp), hextYX.keyW_eq (hpastY _ hpre)]
        exact hmax' _ hwY)
      simp only [lastVal, List.getLast?_map, hlast, Option.map_some, Option.getD_some, hKw]
    · push Not at hne
      rw [read_none (k := k) (v₀ := v₀) (enc := enc) hGY hne ((𝔸).contents val)]
      have : Ks.filter (fun κ => decide (Precedes X.hist κ.w (c, Y.cnt c))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro κ hκ hp
        obtain ⟨w, h1, -, rfl⟩ := (hKs_mem κ).1 hκ
        rw [hKw, decide_eq_true_eq] at hp
        exact hne _ (F3 _ h1 (F2 _ hp))
      rw [this]; rfl

/-! ### Lemma 6: wait-freedom -/

/-- Progress measure of a client's local state within one operation. -/
def mu (l : Loc C n) : ℕ := (if l.upd then 2 * n + 2 else 0) + min l.nxt n + nresp l

theorem nresp_le (l : Loc C n) : nresp l ≤ n := by
  unfold nresp
  exact le_trans (card_filter_le _ _) (by simp)

theorem mu_le (l : Loc C n) : mu l ≤ 4 * n + 2 := by
  have := nresp_le l
  unfold mu; split_ifs <;> omega

theorem nresp_update {l : Loc C n} {o : Fin n} (h : l.resp o = none) (x : Option (Chunk C n)) :
    nresp { l with resp := Function.update l.resp o (some x) } = nresp l + 1 := by
  unfold nresp
  have : (univ.filter fun o' => (Function.update l.resp o (some x) o').isSome) =
      insert o (univ.filter fun o' => (l.resp o').isSome) := by
    ext o'
    by_cases ho : o' = o
    · subst ho; simp
    · simp [Function.update_of_ne ho, ho]
  rw [this, card_insert_of_notMem (by simp [h])]

/-- Within an operation, a client's local state only changes by strictly increasing `mu`. -/
theorem mu_step {X : (𝔸).Config} {c : C} {op : Op} (hc : X.cur c = some op)
    (e : Event C) (hc' : ((𝔸).step X e).cur c ≠ none) :
    ((𝔸).step X e).loc c = X.loc c ∨ mu (X.loc c) < mu (((𝔸).step X e).loc c) := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c', op', rfl, hc'', h1⟩ |
    ⟨c', op', o, r, l, rfl, hc'', ha, h1⟩ | ⟨c', op', l, rfl, hc'', ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;>
    rw [h1] at hc' ⊢
  · exact Or.inl rfl
  · exact Or.inl rfl
  · have : c ≠ c' := by rintro rfl; rw [hc] at hc''; cases hc''
    left; dsimp only; rw [upd_ne' _ _ this]
  · by_cases hcc : c = c'
    · subst hcc
      right; dsimp only; rw [upd_self']
      rcases actF_trigger ha with ⟨hlt, -, -, rfl⟩ | ⟨-, -, hu, -, -, -, rfl⟩
      · have : nresp { X.loc c with nxt := (X.loc c).nxt + 1 } = nresp (X.loc c) := rfl
        simp only [mu, this]; omega
      · have := nresp_le (X.loc c)
        simp only [mu, hu]; simp; omega
    · left; dsimp only; rw [upd_ne' _ _ hcc]
  · by_cases hcc : c = c'
    · subst hcc; dsimp only at hc'; rw [upd_self'] at hc'; exact absurd rfl hc'
    · left; dsimp only; rw [upd_ne' _ _ hcc]
  · by_cases hcc : c = c'
    · subst hcc
      dsimp only; rw [upd_self']
      change recvF (X.loc c) p.obj _ = _ ∨ _ < mu (recvF (X.loc c) p.obj _)
      generalize (applyF p.rmw (X.obj p.obj)).2 = res
      cases res with
      | rdR τ x =>
        dsimp only [recvF]
        split_ifs with h
        · right; simp only [mu, nresp_update h.2.2]; omega
        · exact Or.inl rfl
      | ack τ =>
        dsimp only [recvF]
        split_ifs with h
        · right; simp only [mu, nresp_update h.2.2]; omega
        · exact Or.inl rfl
    · left; dsimp only; rw [upd_ne' _ _ hcc]

/-- While a client does not return, its current operation and counter stay the same. -/
theorem cur_step_stay (X : (𝔸).Config) (e : Event C) (c : C) (h : X.cur c ≠ none)
    (h' : ((𝔸).step X e).cur c ≠ none) :
    ((𝔸).step X e).cur c = X.cur c ∧ ((𝔸).step X e).cnt c = X.cnt c := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c', op', rfl, hc'', h1⟩ |
    ⟨c', op', o, r, l, rfl, hc'', ha, h1⟩ | ⟨c', op', l, rfl, hc'', ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;>
    rw [h1] at h' ⊢
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have : c ≠ c' := by rintro rfl; exact h hc''
    dsimp only; rw [upd_ne' _ _ this]; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have : c ≠ c' := by rintro rfl; dsimp only at h'; rw [upd_self'] at h'; exact h' rfl
    dsimp only; rw [upd_ne' _ _ this, upd_ne' _ _ this]; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- A pending RMW leaves the pending list only by taking effect. -/
theorem pend_exit {X : (𝔸).Config} (hok : (𝔸).PendOK X) {p : Pend C (Fin n) (𝔸).R}
    (hp : p ∈ X.pend) {e : Event C} (hp' : p ∉ ((𝔸).step X e).pend) :
    e = .exec p.cl p.idx ∧ (𝔸).findP X p.cl p.idx = some p := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c', op', rfl, hc'', h1⟩ |
    ⟨c', op', o, r, l, rfl, hc'', ha, h1⟩ | ⟨c', op', l, rfl, hc'', ha, h1⟩ | ⟨c', m, q, rfl, hq, h1⟩ <;>
    rw [h1] at hp'
  · exact absurd hp hp'
  · exact absurd hp hp'
  · exact absurd hp hp'
  · exact absurd (List.mem_append_left _ hp) hp'
  · exact absurd hp hp'
  · by_cases hpq : p = q
    · subst hpq
      obtain ⟨-, rfl, rfl⟩ := Alg.findP_spec hq
      exact ⟨rfl, hq⟩
    · exact absurd (by rw [← h1]; exact mem_pend_exec (𝔸) hok hq hp hpq) hp'

/-- **Lemma 6.** Algorithm 2 is wait-free: an operation of a correct client completes, since every
phase waits for only `n - f` of the `n` base objects, of which at most `f` crash. -/
theorem waitFree (hq : n < (n - f) + (n - f)) : WaitFree (𝔸) f := by
  intro ev Fc Fo hfair t c hcF hcur
  by_contra hcon
  push Not at hcon
  obtain ⟨op, hop⟩ := Option.ne_none_iff_exists'.1 hcur
  set Z := (𝔸).cfg ev with hZ
  have hZs : ∀ s, Z (s + 1) = (𝔸).step (Z s) (ev s) := fun s => rfl
  -- the operation stays outstanding forever
  have hstay : ∀ d, (Z (t + d)).cur c = some op ∧ (Z (t + d)).cnt c = (Z t).cnt c := by
    intro d
    induction d with
    | zero => exact ⟨hop, rfl⟩
    | succ d ih =>
      have hne : (Z (t + d)).cur c ≠ none := by rw [ih.1]; simp
      have hne' : (Z (t + d + 1)).cur c ≠ none := fun h => hcon (t + d) (by omega) ⟨hne, h⟩
      rw [hZs] at hne'
      obtain ⟨h1, h2⟩ := cur_step_stay _ _ c hne hne'
      rw [← add_assoc, hZs, h1, h2]; exact ih
  have hstay' : ∀ s ≥ t, (Z s).cur c = some op ∧ (Z s).cnt c = (Z t).cnt c := by
    intro s hs; obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs; exact hstay d
  have hG : ∀ s, Good f (Z s) := good_cfg hq ev
  have hmu : ∀ s ≥ t, (Z (s + 1)).loc c = (Z s).loc c ∨ mu ((Z s).loc c) < mu ((Z (s + 1)).loc c) := by
    intro s hs
    have := mu_step (hstay' s hs).1 (ev s) (by rw [← hZs, (hstay' (s + 1) (by omega)).1]; simp)
    rwa [← hZs] at this
  have hmono : ∀ s ≥ t, ∀ d, mu ((Z s).loc c) ≤ mu ((Z (s + d)).loc c) := by
    intro s hs d
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      rcases hmu (s + d) (by omega) with h | h
      · rw [← add_assoc, h]; exact ih
      · rw [← add_assoc]; omega
  -- `mu` stabilizes
  obtain ⟨s, hs, hconst⟩ : ∃ s ≥ t, ∀ d, mu ((Z (s + d)).loc c) = mu ((Z s).loc c) := by
    by_contra hno
    push Not at hno
    have : ∀ j, ∃ s ≥ t, mu ((Z t).loc c) + j ≤ mu ((Z s).loc c) := by
      intro j
      induction j with
      | zero => exact ⟨t, le_rfl, le_rfl⟩
      | succ j ih =>
        obtain ⟨s, hs, hj⟩ := ih
        obtain ⟨d, hd⟩ := hno s hs
        have := hmono s hs d
        exact ⟨s + d, by omega, by omega⟩
    obtain ⟨s, -, hj⟩ := this (4 * n + 3)
    have := mu_le ((Z s).loc c)
    omega
  -- hence the local state is constant from `s` on
  have hloc : ∀ d, (Z (s + d)).loc c = (Z s).loc c := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rcases hmu (s + d) (by omega) with h | h
      · rw [← add_assoc, h, ih]
      · have h1 := hconst (d + 1); have h2 := hconst d
        rw [← add_assoc] at h1; omega
  set l := (Z s).loc c with hl
  set i := (Z t).cnt c
  -- `c` is scheduled again after `s`
  obtain ⟨s₁, hs₁, hev⟩ := hfair.cl_live c hcF s
  obtain ⟨d₁, rfl⟩ := Nat.exists_eq_add_of_le hs₁
  have hcur₁ := (hstay' (s + d₁) (by omega))
  have hl₁ := hloc d₁
  have hl₂ := hloc (d₁ + 1)
  rw [← add_assoc, hZs, hev] at hl₂
  by_cases hnxt : l.nxt < n
  · -- it triggers an RMW: the state changes
    have ha : (𝔸).act c ((Z (s + d₁)).cnt c) op ((Z (s + d₁)).loc c) =
        .trigger ⟨l.nxt, hnxt⟩ (rmwOf c i op l ⟨l.nxt, hnxt⟩) { l with nxt := l.nxt + 1 } := by
      rw [hcur₁.2, hl₁]; simp [actF, hnxt]
    rw [Alg.step_step_trigger hcur₁.1 ha] at hl₂
    dsimp only at hl₂; rw [upd_self'] at hl₂
    have := congrArg Loc.nxt hl₂; simp at this
  by_cases hcnt : n - f ≤ nresp l
  · -- it returns or starts the update phase
    rcases hact : actF f hn c i op l with ⟨o, r, l'⟩ | l' | _
    · rcases actF_trigger hact with ⟨h, -⟩ | ⟨-, -, hu, -, -, -, rfl⟩
      · exact hnxt h
      · have ha : (𝔸).act c ((Z (s + d₁)).cnt c) op ((Z (s + d₁)).loc c) = .trigger o r
            { l with tag := l.tag + 1, upd := true, nxt := 1, resp := fun _ => none,
                     wts := Function.update l.wts i (maxNum l + 1) } := by
          rw [hcur₁.2, hl₁]; exact hact
        rw [Alg.step_step_trigger hcur₁.1 ha] at hl₂
        dsimp only at hl₂; rw [upd_self'] at hl₂
        have := congrArg Loc.upd hl₂; simp [hu] at this
    · have ha : (𝔸).act c ((Z (s + d₁)).cnt c) op ((Z (s + d₁)).loc c) = .ret l' := by
        rw [hcur₁.2, hl₁]; exact hact
      refine hcon (s + d₁) (by omega) ⟨by rw [hcur₁.1]; simp, ?_⟩
      show (Z (s + d₁ + 1)).cur c = none
      rw [hZs, hev, Alg.step_step_ret hcur₁.1 ha]; dsimp only; rw [upd_self']
    · simp only [actF, hnxt, hcnt, dif_neg, ite_true, not_false_eq_true] at hact
      split_ifs at hact
  · -- some correct object has not responded; its RMW eventually takes effect
    have hT : (univ.filter fun o => (l.resp o).isSome).card + f < n := by
      unfold nresp at hcnt
      have := hfair.card_le; omega
    obtain ⟨o, ho⟩ : ∃ o, o ∉ Fo ∧ l.resp o = none := by
      by_contra hno
      push Not at hno
      have hsub : (univ : Finset (Fin n)) ⊆ (univ.filter fun o => (l.resp o).isSome) ∪ Fo := by
        intro o _
        by_cases h : o ∈ Fo
        · exact mem_union_right _ h
        · exact mem_union_left _ (by simp [Option.isSome_iff_ne_none, hno o h])
      have := card_le_card hsub
      have := card_union_le (univ.filter fun o => (l.resp o).isSome) Fo
      have := hfair.card_le
      simp at *; omega
    obtain ⟨p, hp, hpc, hpo, hpr⟩ := (hG s).live c op (hstay' s hs).1 o
      (by have := o.isLt; change o.val < l.nxt; omega) ho.2
    obtain ⟨s', hs', hp'⟩ := hfair.rmw_live s p hp (by rw [hpc]; exact hcF) (by rw [hpo]; exact ho.1)
    -- the step at which `p` takes effect
    have : ∀ d, p ∈ (Z s).pend → p ∉ (Z (s + d)).pend →
        ∃ d' < d, p ∈ (Z (s + d')).pend ∧ p ∉ (Z (s + d' + 1)).pend := by
      intro d
      induction d with
      | zero => intro h1 h2; exact absurd h1 h2
      | succ d ih =>
        intro h1 h2
        by_cases h3 : p ∈ (Z (s + d)).pend
        · exact ⟨d, by omega, h3, by rw [← add_assoc] at h2; exact h2⟩
        · obtain ⟨d', hd', h4⟩ := ih h1 h3; exact ⟨d', by omega, h4⟩
    obtain ⟨d', -, hin, hout⟩ := this (s' - s) hp (by rw [Nat.add_sub_cancel' hs']; exact hp')
    rw [hZs] at hout
    obtain ⟨hev', hfind⟩ := pend_exit ((hG _).pendOK) hin hout
    have hl₃ := hloc (d' + 1)
    rw [← add_assoc, hZs, hev', Alg.step_exec_some hfind] at hl₃
    dsimp only at hl₃
    rw [hpc, upd_self'] at hl₃
    have hl₄ := hloc d'
    rw [hl₄] at hl₃
    -- the response is recorded: contradiction
    have hcur₃ := hstay' (s + d') (by omega)
    have hpr' : p.rmw = rmwOf c i op l o := by rw [hpr, (hstay' s hs).2]
    have hobj : p.obj = o := hpo
    change recvF l p.obj (applyF p.rmw ((Z (s + d')).obj p.obj)).2 = l at hl₃
    rw [hpr', hobj] at hl₃
    unfold rmwOf at hl₃
    split_ifs at hl₃ with hu
    · simp only [applyF, recvF, ho.2, hu.1, and_self, ite_true] at hl₃
      have := congrArg (fun l => l.resp o) hl₃; simp [ho.2] at this
    · have hu' : l.upd = false := by
        cases hup : l.upd
        · rfl
        · cases op
          · exact absurd ⟨hup, rfl⟩ hu
          · have := (hG s).rdFlag c (hstay' s hs).1; rw [← hl, hup] at this; cases this
      simp only [applyF, recvF, ho.2, hu', and_self, ite_true] at hl₃
      have := congrArg (fun l => l.resp o) hl₃; simp [ho.2] at this

/-! ### Corollary 3 and non-vacuity -/

/-- **Corollary 3.** With `n = 2f + k` base objects (`k ≥ 1`) and a `k`-of-`n` code with pieces of `ℓ`
bits, Algorithm 2 emulates a strongly safe, wait-free MWMR register, storing at most `n * ℓ` bits in
the base objects (`nD/k = (2f/k + 1)D` for pieces of `D/k` bits). -/
theorem corollary3 (hnk : n = 2 * f + k) (hk : 1 ≤ k) (hdec : Decodable k enc) :
    StronglySafe (𝔸) v₀ ∧ WaitFree (𝔸) f ∧ ∀ X : (𝔸).Config, (𝔸).objBits X ≤ n * ℓ :=
  ⟨stronglySafe hnk hk hdec, waitFree (by omega), objBits_le⟩

end Proofs

/-- Replication (`k = 1`, each piece is the whole value) is a `1`-of-`n` code. -/
theorem decodable_replication (ℓ : ℕ) :
    Decodable (n := n) 1 (fun (_ : Fin n) (v : Fin (2 ^ ℓ)) => v) := by
  intro S hS v v' h
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
  exact h i hi

/-- Non-vacuity: the hypotheses of Corollary 3 are satisfiable, e.g. by replication over
`n = 2f + 1` objects. -/
theorem corollary3_replication (f ℓ : ℕ) (hℓ : 0 < ℓ) (v₀ : Fin (2 ^ ℓ)) :
    StronglySafe (alg (C := C) (n := 2 * f + 1) f 1 ℓ (fun _ v => v) v₀ hℓ (by omega)) v₀ ∧
    WaitFree (alg (C := C) (n := 2 * f + 1) f 1 ℓ (fun _ v => v) v₀ hℓ (by omega)) f :=
  ⟨(corollary3 rfl le_rfl (decodable_replication ℓ)).1,
    (corollary3 rfl le_rfl (decodable_replication ℓ)).2.1⟩

end Podc.ReliableStorageSpace.Safe
