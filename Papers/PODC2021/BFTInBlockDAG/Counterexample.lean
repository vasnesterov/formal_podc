import Papers.PODC2021.BFTInBlockDAG.Embedding

/-!
# Counterexample: no duplication (Lemma 4.3 (2)) and Theorem 5.1 fail under equivocation

Four servers `0, 1, 2, 3` (`n = 3f + 1` with `f = 1`); server `3` is Byzantine. One protocol
instance (`L = Unit`). The protocol `countP` ("count echoes"):
* on any request, a server that has not echoed yet sends `ECHO` to every server;
* on every delivered message it increments a counter; when the counter reaches `2f + 1 = 3` it
  indicates `deliver` (once).
A message is just the pair `(sender, receiver)`.

Over authenticated perfect links (no duplication + authenticity) three deliveries come from three
different senders, at least two of them correct, and correct servers only echo after a request.
So `countP` satisfies the property `Φ`: "if some correct server delivers, then at least two
different correct servers were requested" (`holdsOverAPL_phi`).

In the block DAG embedding, the Byzantine server `3` equivocates with two genesis blocks `Bb₁`,
`Bb₂` (different only in their request). Both are valid, so the correct server `1` references
`Bb₁` in its first block `D₁` and, after receiving `Bb₂`, references `Bb₂` in its second block `D₂`.
Interpreting the DAG, server `1` receives the message `ECHO` from `3` twice: at `D₁` and at `D₂`
(`lemma_4_3_2_false`). With the echo of the only requested correct server `0`, it counts to 3 and
`shim(P)` at server `1` indicates `deliver` (`theorem_5_1_false`), although only one correct
server was ever requested.

The run (`run12`, 12 events of Algorithms 1 and 3 plus two Byzantine sends) is checked to be a
run of the system (`reachable_run12`).
-/

namespace Podc.BFTInBlockDAG.Counterexample

open Podc.BFTInBlockDAG

/-- Messages `ECHO` from `src` to `dst`. -/
structure Msg where
  src : Fin 4
  dst : Fin 4
  deriving DecidableEq

/-- Encoding used for the total order `<_M`. -/
def Msg.code (m : Msg) : ℕ := 4 * m.src.val + m.dst.val

theorem Msg.code_injective : Function.Injective Msg.code := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Msg.code] at h
  have hb := b.isLt; have hd := d.isLt
  have h1 : a.val = c.val := by omega
  have h2 : b.val = d.val := by omega
  simp [Fin.ext h1, Fin.ext h2]

instance : LinearOrder Msg := LinearOrder.lift' Msg.code Msg.code_injective

/-- Local state: owner, counter, echoed, delivered. -/
abbrev St := Fin 4 × ℕ × Bool × Bool

/-- The protocol "count echoes", with a switch `once`: with `once = true` a server echoes only on
its first request; with `once = false` every request triggers the echoes, whatever the state (the
paper's convention that messages triggered by a request do not depend on the state). -/
def countPb (once : Bool) : Protocol (Fin 4) Unit Bool Msg Unit St where
  init _ s := (s, 0, false, false)
  step st i := match i with
    | .req _ => if once && st.2.2.1 then (st, [], []) else
        ((st.1, st.2.1, true, st.2.2.2), [⟨st.1, 0⟩, ⟨st.1, 1⟩, ⟨st.1, 2⟩, ⟨st.1, 3⟩], [])
    | .recv _ => if 3 ≤ st.2.1 + 1 ∧ st.2.2.2 = false then
        ((st.1, st.2.1 + 1, st.2.2.1, true), [], [()])
      else ((st.1, st.2.1 + 1, st.2.2.1, st.2.2.2), [], [])
  sender m := m.src
  receiver m := m.dst

/-- The protocol "count echoes" (echo once). -/
abbrev countP : Protocol (Fin 4) Unit Bool Msg Unit St := countPb true

/-- The stateless variant: every request triggers the echoes. -/
abbrev countP₀ : Protocol (Fin 4) Unit Bool Msg Unit St := countPb false

/-- Messages are stamped with their sender. -/
theorem countPb_owned (b : Bool) : (countPb b).Owned Prod.fst := by
  refine ⟨fun _ _ => rfl, fun st i => ?_, fun st i m hm => ?_⟩
  · cases i <;> simp only [countPb] <;> split_ifs <;> rfl
  · cases i with
    | req r =>
      simp only [countPb] at hm ⊢
      split_ifs at hm
      · simp at hm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> rfl
    | recv m' =>
      simp only [countPb] at hm
      split_ifs at hm <;> simp at hm

/-- Messages are stamped with their sender. -/
theorem countP_owned : countP.Owned Prod.fst := countPb_owned true

theorem run_cons_out (st : St) (i : Input Bool Msg) (is : List (Input Bool Msg)) :
    (countP.run st (i :: is)).2.1 = (countP.step st i).2.1 ++ (countP.run (countP.step st i).1 is).2.1 :=
  rfl

theorem countP_run (st : St) (ins : List (Input Bool Msg)) :
    (countP.run st ins).2.1 = [] ∨
      (st.2.2.1 = false ∧ (countP.run st ins).2.1 = [⟨st.1, 0⟩, ⟨st.1, 1⟩, ⟨st.1, 2⟩, ⟨st.1, 3⟩]) := by
  induction ins generalizing st with
  | nil => simp
  | cons i is ih =>
    obtain ⟨o, c, e, d⟩ := st
    rw [run_cons_out]
    cases i with
    | req r =>
      cases e
      · have h1 : countP.step (o, c, false, d) (.req r) =
            ((o, c, true, d), [⟨o, 0⟩, ⟨o, 1⟩, ⟨o, 2⟩, ⟨o, 3⟩], []) := rfl
        rw [h1]
        right
        refine ⟨rfl, ?_⟩
        rcases ih (o, c, true, d) with h | ⟨h, -⟩
        · rw [h]; rfl
        · simp at h
      · have h1 : countP.step (o, c, true, d) (.req r) = ((o, c, true, d), [], []) := rfl
        rw [h1, List.nil_append]
        exact ih _
    | recv m =>
      obtain ⟨d', h1⟩ : ∃ d', countP.step (o, c, e, d) (.recv m) =
          ((o, c + 1, e, d'), [], if d' = d then [] else [()]) := by
        simp only [countP, countPb]
        split_ifs with h
        · exact ⟨true, by simp [h.2]⟩
        · exact ⟨d, by simp⟩
      rw [h1, List.nil_append]
      exact ih _

/-- `countP` follows the convention that messages are unique: a process never sends the same
message twice. So the counterexample is not caused by duplicate sends of correct processes. -/
theorem countP_sendUnique : SendUnique countP := by
  intro ℓ a ins
  rcases countP_run (countP.init ℓ a) ins with h | ⟨-, h⟩
  · rw [h]; exact List.nodup_nil
  · rw [h]; simp

/-- The Byzantine server. -/
def Byz : Set (Fin 4) := {3}

theorem mem_Byz {s : Fin 4} : s ∈ Byz ↔ s = 3 := Iff.rfl

abbrev Blk := Block (Fin 4) Unit Bool

/-- The genesis block of server `0`, with the request. -/
def B₀ : Blk := .mk 0 0 [] [((), true)]
/-- The two equivocating genesis blocks of the Byzantine server `3`. -/
def Bb₁ : Blk := .mk 3 0 [] [((), true)]
def Bb₂ : Blk := .mk 3 0 [] [((), false)]
/-- The two blocks of the correct server `1`. -/
def D₁ : Blk := .mk 1 0 [B₀, Bb₁] []
def D₂ : Blk := .mk 1 1 [D₁, Bb₂] []

/-- The echo of `3` to `1`. -/
def m₃₁ : Msg := ⟨3, 1⟩

theorem interp_D₁ : interp countP () D₁ = ⟨(1, 2, false, false), [], [⟨0, 1⟩, m₃₁], []⟩ := by
  decide

theorem interp_D₂ : interp countP () D₂ = ⟨(1, 3, false, true), [], [m₃₁], [()]⟩ := by
  decide

/-! ### The run -/

/-- A list of events that can be executed one after the other from `σ`. -/
def RunOK {S L R : Type} [DecidableEq S] [DecidableEq L] [DecidableEq R] (Byz : Set S) :
    Sys S L R → List (Ev S L R) → Prop
  | _, [] => True
  | σ, e :: es => Enabled Byz σ e ∧ RunOK Byz (apply σ e) es

theorem RunOK.reachable {S L R : Type} [DecidableEq S] [DecidableEq L] [DecidableEq R]
    {Byz : Set S} {σ : Sys S L R} {es : List (Ev S L R)} (hσ : Reachable Byz σ)
    (h : RunOK Byz σ es) : Reachable Byz (es.foldl apply σ) := by
  induction es generalizing σ with
  | nil => exact hσ
  | cons e es ih =>
    exact ih (hσ.tail ⟨e, h.1, rfl⟩) h.2

/-- The events of the run. -/
def evs : List (Ev (Fin 4) Unit Bool) :=
  [.request 0 () true, .disseminate 0, .byz 3 1 (.blk Bb₁), .byz 3 1 (.blk Bb₂),
   .recv 1 0 (.blk B₀), .recv 1 3 (.blk Bb₁), .validate 1 B₀, .validate 1 Bb₁, .disseminate 1,
   .recv 1 3 (.blk Bb₂), .validate 1 Bb₂, .disseminate 1]

/-- The final state of the run. -/
def run12 : Sys (Fin 4) Unit Bool := evs.foldl apply Sys.init

theorem authentic_byz_genesis {σ : Sys (Fin 4) Unit Bool} {B : Blk} (hB : B.preds = [])
    (hn : B.n = 3) : Authentic Byz σ B := by
  intro C hC hCn
  rcases Relation.ReflTransGen.cases_tail hC with rfl | ⟨D, -, hD⟩
  · exact absurd (mem_Byz.2 hn) hCn
  · simp [Block.Edge, hB] at hD

theorem reachable_run12 : Reachable Byz run12 := by
  refine RunOK.reachable Relation.ReflTransGen.refl ?_
  simp only [evs, RunOK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals simp only [Enabled, mem_Byz]
  all_goals try decide
  · exact ⟨trivial, fun B h => by cases h; exact authentic_byz_genesis rfl rfl⟩
  · exact ⟨trivial, fun B h => by cases h; exact authentic_byz_genesis rfl rfl⟩
  all_goals refine ⟨by decide, ?_⟩
  all_goals simp (config := {decide := true}) [apply, Sys.upd, Sys.init, newBlock, B₀, Bb₁, Bb₂]

theorem log_run12 : (run12.loc 1).log = [B₀, Bb₁, D₁, Bb₂, D₂] := by decide

/-! ### The property `Φ` holds for `countP` over authenticated perfect links -/

/-- "If some server delivers, then two different servers were requested." -/
def Φ (tr : List (Fin 4 × (Bool ⊕ Unit))) : Prop :=
  (∃ s, (s, Sum.inr ()) ∈ tr) → ∃ s₁ s₂ r₁ r₂, s₁ ≠ s₂ ∧ (s₁, Sum.inl r₁) ∈ tr ∧ (s₂, Sum.inl r₂) ∈ tr

variable {b : Bool}

/-- The number of deliveries at `s` in a trace. -/
def nrecv (s : Fin 4) (tr : List (Fin 4 × Input Bool Msg)) : ℕ :=
  ((recvs tr).filter fun e => decide (e.1 = s)).length

theorem step_req (st : St) (r : Bool) :
    ((countPb b).step st (.req r)).1.1 = st.1 ∧ ((countPb b).step st (.req r)).1.2.1 = st.2.1 ∧
      ((countPb b).step st (.req r)).2.2 = [] := by
  simp only [countPb]; split_ifs <;> simp

theorem step_recv (st : St) (m : Msg) :
    ((countPb b).step st (.recv m)).1.2.1 = st.2.1 + 1 ∧ ((countPb b).step st (.recv m)).2.1 = [] ∧
      (((countPb b).step st (.recv m)).2.2 ≠ [] → 2 ≤ st.2.1) := by
  simp only [countPb]; split_ifs with h <;> simp; omega

theorem recvs_concat (t : List (Fin 4 × Input Bool Msg)) (e : Fin 4 × Input Bool Msg) :
    recvs (t ++ [e]) = recvs t ++ (if e.2.IsRecv then [e] else []) := by
  simp only [recvs, List.filter_append, List.filter_singleton]
  split_ifs with h <;> simp [h]

theorem exec_count (tr : List (Fin 4 × Input Bool Msg)) (s : Fin 4) :
    ((exec (countPb b) () tr).1 s).2.1 = nrecv s tr := by
  induction tr using List.reverseRecOn with
  | nil => rfl
  | append_singleton t e ih =>
    rw [exec_concat]
    simp only [execStep, nrecv, recvs_concat, List.filter_append, List.length_append]
    by_cases hs : s = e.1
    · subst hs
      rw [Function.update_self]
      rcases e with ⟨s, r | m⟩
      · rw [(step_req _ r).2.1, ih]; simp [nrecv, Input.IsRecv]
      · rw [(step_recv _ m).1, ih]; simp [nrecv, Input.IsRecv]
    · rw [Function.update_of_ne hs, ih]
      split_ifs <;> simp [nrecv, Ne.symm hs]

theorem exec_sent (tr : List (Fin 4 × Input Bool Msg)) {s : Fin 4} {m : Msg}
    (h : (s, m) ∈ (exec (countPb b) () tr).2.1) : ∃ r, (s, Input.req r) ∈ tr := by
  induction tr using List.reverseRecOn with
  | nil => simp [exec] at h
  | append_singleton t e ih =>
    rw [exec_concat] at h
    simp only [execStep, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨m', hm', he⟩
    · obtain ⟨r, hr⟩ := ih h
      exact ⟨r, List.mem_append_left _ hr⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases e with ⟨s, r | m''⟩
      · exact ⟨r, List.mem_append_right _ (List.mem_singleton_self _)⟩
      · rw [(step_recv _ m'').2.1] at hm'
        simp at hm'

theorem exec_req (tr : List (Fin 4 × Input Bool Msg)) {s : Fin 4} {r : Bool}
    (h : (s, Input.req r) ∈ tr) : (s, Sum.inl r) ∈ (exec (countPb b) () tr).2.2 := by
  induction tr using List.reverseRecOn with
  | nil => simp at h
  | append_singleton t e ih =>
    rw [exec_concat]
    simp only [execStep, List.mem_append]
    rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inl (ih h))
    · rw [List.mem_singleton] at h
      subst h
      exact Or.inl (Or.inr (by simp))

theorem exec_ind (tr : List (Fin 4 × Input Bool Msg)) {s : Fin 4}
    (h : (s, Sum.inr ()) ∈ (exec (countPb b) () tr).2.2) :
    ∃ t₁ m t₂, tr = t₁ ++ (s, Input.recv m) :: t₂ ∧ 2 ≤ nrecv s t₁ := by
  induction tr using List.reverseRecOn with
  | nil => simp [exec] at h
  | append_singleton t e ih =>
    have hc := exec_count (b := b) t e.1
    rw [exec_concat] at h
    simp only [execStep, List.mem_append, List.mem_map] at h
    rcases h with (h | h) | ⟨i, hi, he⟩
    · obtain ⟨t₁, m, t₂, rfl, h2⟩ := ih h
      exact ⟨t₁, m, t₂ ++ [e], by simp, h2⟩
    · rcases e with ⟨s', _ | _⟩ <;> simp at h
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      rcases e with ⟨s', r | m⟩
      · rw [(step_req _ r).2.2] at hi; simp at hi
      · have h2 := (step_recv ((exec (countPb b) () t).1 s') m).2.2 (List.ne_nil_of_mem hi)
        exact ⟨t, m, [], rfl, by simpa [hc] using h2⟩

theorem holdsOverAPL_phiB (b : Bool) : HoldsOverAPL (countPb b) () Byz Φ := by
  intro tr hsafe hnd ⟨s, hs⟩
  obtain ⟨t₁, m, t₂, rfl, h2⟩ := exec_ind tr hs
  -- the deliveries at `s` up to and including the indication
  set X := (recvs (t₁ ++ [(s, Input.recv m)])).filter fun e => decide (e.1 = s) with hXdef
  have hX : 3 ≤ X.length := by
    rw [hXdef, recvs_concat]
    simp only [nrecv] at h2
    simp [Input.IsRecv, List.filter_append]; omega
  have hXsub : X.Sublist (recvs (t₁ ++ (s, Input.recv m) :: t₂)) := by
    have : t₁ ++ (s, Input.recv m) :: t₂ = (t₁ ++ [(s, Input.recv m)]) ++ t₂ := by simp
    rw [this, recvs, List.filter_append]
    exact List.filter_sublist.trans (List.sublist_append_left _ _)
  have hXnd : X.Nodup := hXsub.nodup hnd
  -- every element of `X` is a delivery at `s` of a message addressed to `s`
  have hXmem : ∀ e ∈ X, ∃ m', e = (s, Input.recv m') ∧ m'.dst = s ∧
      (m'.src ∉ Byz → ∃ r, (m'.src, Input.req r) ∈ t₁ ++ (s, Input.recv m) :: t₂) := by
    intro e he
    have he' := hXsub.subset he
    simp only [hXdef, List.mem_filter, decide_eq_true_eq] at he
    obtain ⟨he1, hes⟩ := he
    simp only [recvs, List.mem_filter, decide_eq_true_eq] at he1
    rcases e with ⟨s', _ | m'⟩
    · exact absurd he1.2 id
    simp only at hes
    subst s'
    refine ⟨m', rfl, ?_⟩
    have hmem : (s, Input.recv m') ∈ t₁ ++ (s, Input.recv m) :: t₂ := by
      simp only [recvs, List.mem_filter] at he'
      exact he'.1
    obtain ⟨u₁, u₂, hu⟩ := List.mem_iff_append.1 hmem
    obtain ⟨hr, ha⟩ := hsafe.2 u₁ s m' u₂ hu
    refine ⟨hr, fun hc => ?_⟩
    obtain ⟨r, hr'⟩ := exec_sent u₁ (ha hc)
    exact ⟨r, hu ▸ List.mem_append_left _ hr'⟩
  -- the senders of `X` are pairwise different, so there are two correct ones
  let src : Fin 4 × Input Bool Msg → Fin 4 := fun e => match e.2 with
    | .recv m' => m'.src
    | .req _ => 0
  have hinj : (X.map src).Nodup := by
    refine List.Nodup.map_on (fun e₁ h₁ e₂ h₂ h => ?_) hXnd
    obtain ⟨m₁, rfl, hd₁, -⟩ := hXmem e₁ h₁
    obtain ⟨m₂, rfl, hd₂, -⟩ := hXmem e₂ h₂
    have : m₁ = m₂ := by
      cases m₁; cases m₂; simp only [src] at h; simp_all
    rw [this]
  have hcard : 2 ≤ ((X.map src).toFinset.erase 3).card := by
    have := List.toFinset_card_of_nodup hinj
    have h3 := Finset.pred_card_le_card_erase (s := (X.map src).toFinset) (a := 3)
    rw [this, List.length_map] at h3
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  have get : ∀ c ∈ (X.map src).toFinset.erase 3, ∃ r,
      (c, Input.req r) ∈ t₁ ++ (s, Input.recv m) :: t₂ := by
    intro c hc
    obtain ⟨hc3, hc⟩ := Finset.mem_erase.1 hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
    obtain ⟨m', rfl, -, hreq⟩ := hXmem e he
    exact hreq hc3
  obtain ⟨r₁, h₁⟩ := get a ha
  obtain ⟨r₂, h₂⟩ := get b hb
  exact ⟨a, b, r₁, r₂, hab, exec_req _ h₁, exec_req _ h₂⟩

theorem holdsOverAPL_phi : HoldsOverAPL countP () Byz Φ := holdsOverAPL_phiB true

/-! ### The counterexamples -/

/-- **Lemma 4.3 (2) is false.** In a reachable state of the system (`n = 4`, `f = 1`), the
correct server `1`, interpreting its own block DAG, receives the same message `m₃₁` (`ECHO` from
the Byzantine server `3` to `1`) for the same instance twice: at its two blocks `D₁ ≠ D₂`.
(The paper's proof claims that a duplicate requires `s₂` to reference the same block twice; here
`s₂ = 1` references two *different*, equivocating blocks `Bb₁`, `Bb₂` of server `3` that trigger
the same message.) -/
theorem lemma_4_3_2_false :
    Reachable Byz run12 ∧ (1 : Fin 4) ∉ Byz ∧ (3 : Fin 4) ∈ Byz ∧
      D₁ ∈ (run12.loc 1).log ∧ D₂ ∈ (run12.loc 1).log ∧ D₁ ≠ D₂ ∧ D₁.n = 1 ∧ D₂.n = 1 ∧
      m₃₁ ∈ (interp countP () D₁).inn ∧ m₃₁ ∈ (interp countP () D₂).inn ∧
      countP.sender m₃₁ = 3 ∧ countP.receiver m₃₁ = 1 := by
  refine ⟨reachable_run12, by simp [mem_Byz], rfl, ?_, ?_, by decide, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · rw [log_run12]; decide
  · rw [log_run12]; decide
  · rw [interp_D₁]; decide
  · rw [interp_D₂]; decide

/-- **Theorem 5.1 is false** (for protocols that rely on the no-duplication property of
authenticated perfect links). The deterministic protocol `countP` satisfies `Φ` ("if some
correct server delivers, then two different correct servers were requested") in every execution
over authenticated perfect links, for `n = 4 = 3f + 1`. But in the reachable state `run12` of the
block DAG embedding, `shim(countP)` at the correct server `1` indicates `deliver`, while the only
server that was ever requested is server `0`. Messages of `countP` carry their sender and are
unique, so only the duplication of the Byzantine server's message is to blame (compare
`theorem_5_1_repaired`). -/
theorem theorem_5_1_false :
    countP.Owned Prod.fst ∧ SendUnique countP ∧
    HoldsOverAPL countP () Byz Φ ∧ Reachable Byz run12 ∧ (1 : Fin 4) ∉ Byz ∧
      ShimIndicates countP run12 1 () () ∧
      ∀ s : Fin 4, (run12.loc s).reqs ≠ [] → s = 0 := by
  refine ⟨countP_owned, countP_sendUnique, holdsOverAPL_phi, reachable_run12, by simp [mem_Byz], ⟨D₂, ?_, rfl, ?_⟩, ?_⟩
  · rw [log_run12]; decide
  · rw [interp_D₂]; decide
  · decide

/-- **Theorem 5.1 is false, also for a protocol whose request handling is stateless** (the paper
assumes, Section 4, that "messages triggered by requests do not depend on the state"). `countP₀`
echoes on every request; it is deterministic, its messages carry their sender, it satisfies `Φ`
over authenticated perfect links, and `shim(countP₀)` at the correct server `1` indicates
`deliver` in the same run `run12`, where only server `0` was requested. (`countP₀` is not
`SendUnique` in general, since a server requested twice echoes twice; in `run12` every process
instance is requested at most once, so each message is sent at most once by its process.) -/
theorem theorem_5_1_false_stateless :
    (∀ st r, (countP₀.step st (.req r)).2.1 = [⟨st.1, 0⟩, ⟨st.1, 1⟩, ⟨st.1, 2⟩, ⟨st.1, 3⟩]) ∧
    countP₀.Owned Prod.fst ∧ HoldsOverAPL countP₀ () Byz Φ ∧ Reachable Byz run12 ∧
      (1 : Fin 4) ∉ Byz ∧ ShimIndicates countP₀ run12 1 () () ∧
      ∀ s : Fin 4, (run12.loc s).reqs ≠ [] → s = 0 := by
  refine ⟨fun _ _ => rfl, countPb_owned false, holdsOverAPL_phiB false, reachable_run12,
    by simp [mem_Byz], ⟨D₂, ?_, rfl, ?_⟩, ?_⟩
  · rw [log_run12]; decide
  · decide
  · decide

end Podc.BFTInBlockDAG.Counterexample
