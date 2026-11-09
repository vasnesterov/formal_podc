import Papers.PODC2017.DelayedTimestamps.LowerBounds
import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
# Section 4 and Appendix A: the inline algorithm (Theorem 1)

Inline timestamps for a vertex cover `C` of the communication graph (Section 4):

* an event of a process in `C` gets the vector clock restricted to `C` (`vect`, computed by the
  merge-and-update algorithm `inlineAlg`: processes in `C` increment their own entry, processes
  outside `C` only merge);
* an event `e` of a process `p_i ∉ C` additionally gets `id = p_i`, `index = index(e)` and a vector
  `next` indexed by `C`: `next[j] = index(inbound(p_j, e))`, the index of the receive event of
  `outbound(p_j, e)` — the first message sent by `p_i` to `p_j` at or after `e` (Section 2) — if
  `p_i` has sent such a message by the query time `t`, and `∞` otherwise (Sections 4.1–4.2: the
  query waits until this index is known).

`query ex t e` is `Q_t(e)`; `InlineTS.lt` is the order `<` of Section 4.4 (cases (i)–(iv)).

* `theorem_1`: Theorem 1 holds for **FIFO** channels.
* `theorem_1_false`: without FIFO channels (the paper only assumes reliable channels) Theorem 1
  fails: `p_1 ∉ C` sends two messages to `p_0 ∈ C` which arrive in reverse order.
* `theorem_1_min`: the repaired algorithm, where `next[j]` is the minimum receive index over all
  messages sent by `p_i` to `p_j` at or after `e` by time `t` (`queryMin`), satisfies Theorem 1
  for arbitrary reliable channels.
* `query_injective`: inline timestamps of distinct events are distinct.
-/

namespace Podc.DelayedTimestamps

open Cslib.Causality

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {P : Type*} [DecidableEq P]

/-- Inline timestamps: `id = none` encodes `⊥` (events of processes in `C`). -/
structure InlineTS (P : Type*) (C : Finset P) where
  /-- The process (outside `C`) of the event, `none` for events of processes in `C`. -/
  id : Option P
  /-- The index of the event at its process. -/
  index : ℕ
  /-- The vector clock restricted to `C`. -/
  vect : C → ℕ
  /-- `next[j]`: index of the first receive at `p_j` caused directly by the process of the event
  at or after the event (`⊤ = ∞`). -/
  next : C → ℕ∞

/-- The order `<` on inline timestamps (Section 4.4). -/
def InlineTS.lt {C : Finset P} (τ₁ τ₂ : InlineTS P C) : Prop :=
  (τ₁.id = τ₂.id ∧ τ₁.id ≠ none ∧ τ₁.index < τ₂.index) ∨
  (τ₁.id = none ∧ τ₂.id = none ∧ τ₁.vect < τ₂.vect) ∨
  (τ₁.id = none ∧ τ₂.id ≠ none ∧ τ₁.vect ≤ τ₂.vect) ∨
  (τ₁.id ≠ none ∧ τ₁.id ≠ τ₂.id ∧ ∃ i, τ₁.next i ≤ (τ₂.vect i : ℕ∞))

variable (C : Finset P)

/-- The `vect` part of the inline algorithm: vector clocks restricted to `C`. -/
def inlineAlg : MergeAlg P (C → ℕ) where
  init := 0
  upd _ a x := if h : a.proc ∈ C then x + Pi.single ⟨a.proc, h⟩ 1 else x

variable {C}

lemma inlineAlg_ts (ex : Exec P) (e : ℕ) (j : C) : (inlineAlg C).ts ex e j = ex.vc e j.1 := by
  have h := MergeAlg.ts_map (A := vcAlg P) (B := inlineAlg C) (fun v j => v j.1)
    (by funext j; simp [vcAlg, inlineAlg])
    (by intro x y; funext j; simp)
    (by
      intro j a x
      funext i
      simp only [vcAlg, inlineAlg]
      split_ifs with h
      · simp only [Pi.add_apply, Pi.single_apply, Subtype.ext_iff]
      · have : (i : P) ≠ a.proc := fun e => h (e ▸ i.2)
        simp [this])
    ex e
  rw [h]
  rfl

/-- `next[q]` of an event `e` of `p` at time `t`, as specified in Sections 2 and 4.2:
`index(inbound(q, e)) = index(recv(outbound(q, e)))`. -/
noncomputable def nextIdx (ex : Exec P) (p q : P) (e t : ℕ) : ℕ∞ :=
  (ex.outbound p q e t).elim ⊤ ex.recvIdx

/-- The repaired `next[q]`: the least receive index of the messages sent by `p` to `q` at
positions in `[e, t]`. -/
noncomputable def nextMin (ex : Exec P) (p q : P) (e t : ℕ) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : e ≤ s ∧ s ≤ t ∧ ex[s]? = some (.send p q)), ex.recvIdx s

/-- `Q_t(e)`: the inline timestamp of event `e` returned by a query at time `t ≥ e`. -/
noncomputable def query (C : Finset P) (ex : Exec P) (t e : ℕ) : InlineTS P C where
  id := match ex.procAt e with
    | some p => if p ∈ C then none else some p
    | none => none
  index := ex.idx e
  vect := (inlineAlg C).ts ex e
  next q := match ex.procAt e with
    | some p => if p ∈ C then ⊤ else nextIdx ex p q e t
    | none => ⊤

/-- The repaired query: `next[q]` is the least receive index (`nextMin`). -/
noncomputable def queryMin (C : Finset P) (ex : Exec P) (t e : ℕ) : InlineTS P C :=
  { query C ex t e with
    next := fun q => match ex.procAt e with
      | some p => if p ∈ C then ⊤ else nextMin ex p q e t
      | none => ⊤ }

section Proofs

variable {ex : Exec P} {G : SimpleGraph P}

/-- The common core of Cases 3 and 4 of the proof of Theorem 1: for `e` at `p ∉ C` and `f` at
another process, `e → f` iff some message sent by `p` at or after `e` (and by time `t`) to a
process `q ∈ C` is received at an event `r` with `index(r) ≤ vect(f)[q]`. -/
lemma hb_iff_exists_send (hwf : ex.WF) (hG : ex.OnGraph G) (hC : G.IsVertexCover (C : Set P))
    {e f t : ℕ} {p : P} (hep : ex.procAt e = some p) (hpC : p ∉ C) (hfp : ex.procAt f ≠ some p)
    (hft : f ≤ t) :
    ex.HB e f ↔ ∃ (q : C) (s r : ℕ), e ≤ s ∧ s ≤ t ∧ ex[s]? = some (.send p q) ∧
      ex[r]? = some (.recv q s) ∧ ex.idx r ≤ ex.vc f q := by
  constructor
  · intro h
    obtain ⟨s, r, q, hs, hsp, hr, hrf⟩ := h.exists_send_out hep hfp
    obtain ⟨q', hq'⟩ := hwf.recv_send hr
    have hq'p : q' = p := by
      have := Exec.procAt_of_get hq'; rw [hsp] at this; cases this; rfl
    subst hq'p
    have hadj : G.Adj q' q := hG hq'
    have hqC : q ∈ C := by
      rcases hC hadj with h | h
      · exact absurd h hpC
      · exact h
    have hrq : ex.procAt r = some q := Exec.procAt_of_get hr
    have hsr : s < r := hwf.recv_lt hr
    have hrf' : r ≤ f := hrf.le hwf
    exact ⟨⟨q, hqC⟩, s, r, hs, by omega, hq', hr, (Exec.idx_le_vc_iff hwf hrq).2 hrf⟩
  · rintro ⟨q, s, r, hs, -, hsend, hr, hidx⟩
    have hrq : ex.procAt r = some q := Exec.procAt_of_get hr
    have hrf := (Exec.idx_le_vc_iff hwf hrq).1 hidx
    have hes : ex.HBeq e s := Exec.hbeq_of_le hs hep (Exec.procAt_of_get hsend)
    exact hes.trans_hb ((Exec.HB.of_step (.msg hr)).trans_hbeq hrf)

lemma query_id_of_mem {t e : ℕ} {p : P} (hep : ex.procAt e = some p) (hpC : p ∈ C) :
    (query C ex t e).id = none := by simp [query, hep, hpC]

lemma query_id_of_not_mem {t e : ℕ} {p : P} (hep : ex.procAt e = some p) (hpC : p ∉ C) :
    (query C ex t e).id = some p := by simp [query, hep, hpC]

lemma vect_lt_iff_hb (hwf : ex.WF) {e f : ℕ} {p p' : P} (hep : ex.procAt e = some p)
    (hpC : p ∈ C) (hfp : ex.procAt f = some p') (hp'C : p' ∈ C) :
    (inlineAlg C).ts ex e < (inlineAlg C).ts ex f ↔ ex.HB e f := by
  constructor
  · intro h
    have hle := h.le ⟨p, hpC⟩
    rw [inlineAlg_ts, inlineAlg_ts, Exec.vc_self hwf hep] at hle
    rcases (Exec.idx_le_vc_iff hwf hep).1 hle with rfl | h'
    · exact absurd h (lt_irrefl _)
    · exact h'
  · intro h
    refine Pi.lt_def.2 ⟨fun j => ?_, ⟨p', hp'C⟩, ?_⟩
    · rw [inlineAlg_ts, inlineAlg_ts]; exact Exec.vc_mono hwf (Or.inr h) j
    · rw [inlineAlg_ts, inlineAlg_ts, Exec.vc_self hwf hfp]
      by_contra hc
      exact Exec.HB.irrefl hwf _
        (h.trans_hbeq ((Exec.idx_le_vc_iff hwf hfp).1 (not_lt.1 hc)))

lemma vect_le_iff_hbeq (hwf : ex.WF) {e f : ℕ} {p : P} (hep : ex.procAt e = some p)
    (hpC : p ∈ C) : (inlineAlg C).ts ex e ≤ (inlineAlg C).ts ex f ↔ ex.HBeq e f := by
  constructor
  · intro h
    have hle := h ⟨p, hpC⟩
    rw [inlineAlg_ts, inlineAlg_ts, Exec.vc_self hwf hep] at hle
    exact (Exec.idx_le_vc_iff hwf hep).1 hle
  · intro h j
    rw [inlineAlg_ts, inlineAlg_ts]; exact Exec.vc_mono hwf h j

/-- Theorem 1 for both versions of `next`, given the core equivalence for case (iv). -/
lemma theorem_1_core (hwf : ex.WF) {e f : ℕ} (he : e < ex.length) (hf : f < ex.length)
    (τ : ℕ → InlineTS P C) (hτ : ∀ g, (τ g).id = (query C ex 0 g).id ∧
      (τ g).index = ex.idx g ∧ (τ g).vect = (inlineAlg C).ts ex g)
    (hiv : ∀ p, ex.procAt e = some p → p ∉ C → ex.procAt f ≠ some p →
      (ex.HB e f ↔ ∃ i, (τ e).next i ≤ ((inlineAlg C).ts ex f i : ℕ∞))) :
    ex.HB e f ↔ (τ e).lt (τ f) := by
  obtain ⟨p, hep⟩ : ∃ p, ex.procAt e = some p :=
    ⟨_, Exec.procAt_of_get (List.getElem?_eq_getElem he)⟩
  obtain ⟨p', hfp⟩ : ∃ p, ex.procAt f = some p :=
    ⟨_, Exec.procAt_of_get (List.getElem?_eq_getElem hf)⟩
  obtain ⟨hide, hinde, hve⟩ := hτ e
  obtain ⟨hidf, hindf, hvf⟩ := hτ f
  unfold InlineTS.lt
  rw [hide, hidf, hinde, hindf, hve, hvf]
  by_cases hpC : p ∈ C
  · rw [query_id_of_mem hep hpC]
    by_cases hp'C : p' ∈ C
    · -- Case 1
      rw [query_id_of_mem hfp hp'C]
      simp only [ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false, true_and,
        and_true, false_or, or_false, reduceCtorEq, Option.some.injEq]
      exact (vect_lt_iff_hb hwf hep hpC hfp hp'C).symm
    · -- Case 2
      rw [query_id_of_not_mem hfp hp'C]
      simp only [ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false, true_and,
        and_true, false_or, or_false, reduceCtorEq, Option.some.injEq]
      rw [vect_le_iff_hbeq hwf hep hpC]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · rw [hep] at hfp; cases hfp; exact absurd hpC hp'C
        · exact h
  · rw [query_id_of_not_mem hep hpC]
    by_cases hpp : p' = p
    · -- Case 4, same process
      subst hpp
      rw [query_id_of_not_mem hfp hpC]
      simp only [ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false, true_and,
        and_true, false_or, or_false, reduceCtorEq, Option.some.injEq]
      constructor
      · intro h
        rcases Exec.hb_total hep hfp with h' | rfl | h'
        · exact Exec.idx_lt_idx (h'.lt hwf) hep hfp
        · exact absurd h (Exec.HB.irrefl hwf _)
        · exact absurd h (Exec.HB.asymm hwf h')
      · intro h
        refine Exec.hb_of_lt ?_ hep hfp
        by_contra hc
        exact absurd h (not_lt.2 ((Exec.idx_le_idx_iff hfp hep).2 (not_lt.1 hc)))
    · -- Cases 3 and 4, different processes
      have hidne : (query C ex 0 f).id ≠ some p := by
        by_cases hp'C : p' ∈ C
        · rw [query_id_of_mem hfp hp'C]; simp
        · rw [query_id_of_not_mem hfp hp'C]; simpa using hpp
      have hfp' : ex.procAt f ≠ some p := by rw [hfp]; simpa using hpp
      have hidne' : ¬ some p = (query C ex 0 f).id := fun h => hidne h.symm
      simp only [ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false, true_and,
        and_true, false_or, or_false, reduceCtorEq, Option.some.injEq]
      simp only [hidne', false_and, false_or, not_false_eq_true, true_and]
      exact hiv p hep hpC hfp'

/-- **Theorem 1** of [Vaidya–Kulkarni], for FIFO channels: for events `e`, `f` and a query time
`t ≥ max(e, f)`, `e → f ↔ Q_t(e) < Q_t(f)`. -/
theorem theorem_1 (hwf : ex.WF) (hG : ex.OnGraph G) (hC : G.IsVertexCover (C : Set P))
    (hfifo : ex.FIFO) {e f t : ℕ} (he : e < ex.length) (hf : f < ex.length) (_het : e ≤ t)
    (hft : f ≤ t) : ex.HB e f ↔ (query C ex t e).lt (query C ex t f) := by
  refine theorem_1_core hwf he hf (query C ex t) (fun g => ⟨by simp [query], rfl, rfl⟩) ?_
  intro p hep hpC hfp
  rw [hb_iff_exists_send hwf hG hC hep hpC hfp hft]
  simp only [query, hep, hpC, ite_false, inlineAlg_ts]
  constructor
  · rintro ⟨q, s, r, hs, hst, hsend, hr, hidx⟩
    refine ⟨q, ?_⟩
    obtain ⟨s', hs'⟩ := Exec.outbound_isSome hs hst hsend
    obtain ⟨h1, h2, h3, h4⟩ := Exec.outbound_spec hs'
    have hss : s' ≤ s := h4 s hs hst hsend
    simp only [nextIdx, hs', Option.elim]
    have hrq : ex.procAt r = some q := Exec.procAt_of_get hr
    rcases hss.lt_or_eq with hlt | rfl
    · obtain ⟨r₁, hr₁, hrecv⟩ := hfifo hlt h3 hsend hr
      rw [Exec.recvIdx_eq hwf hrecv]
      exact_mod_cast ((Exec.idx_le_idx_iff (Exec.procAt_of_get hrecv) hrq).2 hr₁.le).trans hidx
    · rw [Exec.recvIdx_eq hwf hr]
      exact_mod_cast hidx
  · rintro ⟨q, hq⟩
    cases hs : ex.outbound p q e t with
    | none => simp [nextIdx, hs] at hq
    | some s =>
      simp only [nextIdx, hs, Option.elim] at hq
      obtain ⟨h1, h2, h3, -⟩ := Exec.outbound_spec hs
      obtain ⟨r, q', hr, hidx⟩ := Exec.recvIdx_ne_top (ne_top_of_le_ne_top (by simp) hq)
      obtain ⟨q'', hq''⟩ := hwf.recv_send hr
      rw [h3] at hq''
      cases hq''
      rw [hidx] at hq
      exact ⟨q, s, r, h1, h2, h3, hr, by exact_mod_cast hq⟩

/-- **Theorem 1, repaired**: with `next[j]` the least receive index (`queryMin`), Theorem 1
holds for arbitrary (non-FIFO) reliable channels. -/
theorem theorem_1_min (hwf : ex.WF) (hG : ex.OnGraph G) (hC : G.IsVertexCover (C : Set P))
    {e f t : ℕ} (he : e < ex.length) (hf : f < ex.length) (_het : e ≤ t) (hft : f ≤ t) :
    ex.HB e f ↔ (queryMin C ex t e).lt (queryMin C ex t f) := by
  refine theorem_1_core hwf he hf (queryMin C ex t)
    (fun g => ⟨by simp [queryMin, query], rfl, rfl⟩) ?_
  intro p hep hpC hfp
  rw [hb_iff_exists_send hwf hG hC hep hpC hfp hft]
  simp only [queryMin, query, hep, hpC, ite_false, inlineAlg_ts]
  constructor
  · rintro ⟨q, s, r, hs, hst, hsend, hr, hidx⟩
    refine ⟨q, ?_⟩
    refine (iInf₂_le s ⟨hs, hst, hsend⟩).trans ?_
    rw [Exec.recvIdx_eq hwf hr]
    exact_mod_cast hidx
  · rintro ⟨q, hq⟩
    have hlt : nextMin ex p q e t < ((ex.vc f q : ℕ) : ℕ∞) + 1 :=
      lt_of_le_of_lt hq (ENat.lt_add_one_iff (by simp) |>.2 le_rfl)
    simp only [nextMin, iInf_lt_iff] at hlt
    obtain ⟨s, ⟨h1, h2, h3⟩, hs⟩ := hlt
    have hs' : ex.recvIdx s ≤ (ex.vc f q : ℕ∞) := (ENat.lt_add_one_iff (by simp)).1 hs
    obtain ⟨r, q', hr, hidx⟩ := Exec.recvIdx_ne_top (ne_top_of_le_ne_top (by simp) hs')
    obtain ⟨q'', hq''⟩ := hwf.recv_send hr
    rw [h3] at hq''
    cases hq''
    rw [hidx] at hs'
    exact ⟨q, s, r, h1, h2, h3, hr, by exact_mod_cast hs'⟩

/-- Inline timestamps of distinct events are distinct (at any query times). -/
theorem query_injective (hwf : ex.WF) {e f t v : ℕ} (he : e < ex.length) (hf : f < ex.length)
    (hne : e ≠ f) : query C ex t e ≠ query C ex v f := by
  obtain ⟨p, hep⟩ : ∃ p, ex.procAt e = some p :=
    ⟨_, Exec.procAt_of_get (List.getElem?_eq_getElem he)⟩
  obtain ⟨p', hfp⟩ : ∃ p, ex.procAt f = some p :=
    ⟨_, Exec.procAt_of_get (List.getElem?_eq_getElem hf)⟩
  intro h
  have hid := congrArg InlineTS.id h
  have hind := congrArg InlineTS.index h
  have hvec := congrArg InlineTS.vect h
  simp only [query] at hind hvec
  simp only [query, hep, hfp] at hid
  by_cases hpC : p ∈ C
  · simp only [hpC, ite_true] at hid
    have hle := (vect_le_iff_hbeq hwf hep hpC (f := f)).1 hvec.le
    by_cases hp'C : p' ∈ C
    · have hle' := (vect_le_iff_hbeq hwf hfp hp'C (f := e)).1 hvec.ge
      rcases hle with h1 | h1
      · exact hne h1
      · rcases hle' with h2 | h2
        · exact hne h2.symm
        · exact Exec.HB.asymm hwf h1 h2
    · simp only [hp'C, ite_false] at hid; cases hid
  · simp only [hpC, ite_false] at hid
    by_cases hp'C : p' ∈ C
    · simp only [hp'C, ite_true] at hid; cases hid
    · simp only [hp'C, ite_false] at hid
      cases hid
      exact hne (le_antisymm ((Exec.idx_le_idx_iff hep hfp).1 hind.le)
        ((Exec.idx_le_idx_iff hfp hep).1 hind.ge))

end Proofs

/-! ### Counterexample without FIFO channels -/

/-- Two processes, `p_0 ∈ C = {p_0}` and `p_1 ∉ C`: `p_1` sends two messages to `p_0` (events
`0`, `1`); `p_0` receives the second one first (event `2`) and the first one last (event `3`). -/
def nonFifoExec : Exec (Fin 2) := [.send 1 0, .send 1 0, .recv 0 1, .recv 0 0]

lemma nonFifoExec_wf : nonFifoExec.WF := by
  constructor
  · intro j p m h
    have hj : j < 4 := (List.getElem?_eq_some_iff.1 h).1
    interval_cases j <;> simp [nonFifoExec] at h <;> omega
  · intro j p m h
    have hj : j < 4 := (List.getElem?_eq_some_iff.1 h).1
    interval_cases j <;> simp [nonFifoExec] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp [nonFifoExec]
  · intro j j' p p' m h h'
    have hj : j < 4 := (List.getElem?_eq_some_iff.1 h).1
    have hj' : j' < 4 := (List.getElem?_eq_some_iff.1 h').1
    interval_cases j <;> interval_cases j' <;> simp [nonFifoExec] at h h' <;> omega

lemma nonFifoExec_onGraph : nonFifoExec.OnGraph (star 1) := by
  intro j p q h
  have hj : j < 4 := (List.getElem?_eq_some_iff.1 h).1
  interval_cases j <;> simp [nonFifoExec] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    rw [star_adj] <;> decide

lemma star_cover (m : ℕ) : (star m).IsVertexCover (({0} : Finset (Fin (m + 1))) : Set _) := by
  intro i j h
  rcases (star_adj.1 h).2 with h | h <;> simp [h]

lemma nonFifoExec_not_fifo : ¬ nonFifoExec.FIFO := by
  intro h
  obtain ⟨r₁, hr₁, hrecv⟩ := h (s₁ := 0) (s₂ := 1) (r₂ := 2) (p := 1) (q := 0) (by omega) rfl rfl rfl
  interval_cases r₁ <;> simp [nonFifoExec] at hrecv

/-- **Theorem 1 is false without FIFO channels.** In `nonFifoExec` (reliable channels, every
message delivered, star graph, vertex cover `C = {p_0}`), the first event `e` of `p_1`
happened-before the first event `f` of `p_0` (`e → e' → f`, `e'` the second send), but for every
query time `t ≥ 2`, `Q_t(e) ≮ Q_t(f)`: `Q_t(e).next[p_0] = index(recv(e)) = 2` while
`Q_t(f).vect[p_0] = 1`. -/
theorem theorem_1_false (t : ℕ) (ht : 2 ≤ t) :
    nonFifoExec.WF ∧ nonFifoExec.OnGraph (star 1) ∧ (star 1).IsVertexCover (({0} : Finset (Fin 2)) : Set (Fin 2)) ∧
      nonFifoExec.HB 0 2 ∧ ¬ (query {0} nonFifoExec t 0).lt (query {0} nonFifoExec t 2) := by
  refine ⟨nonFifoExec_wf, nonFifoExec_onGraph, star_cover 1, ?_, ?_⟩
  · exact (Exec.HB.of_step (.po (by decide))).trans (.of_step (.msg rfl))
  · have hout : nonFifoExec.outbound 1 0 0 t = some 0 := by
      have hex : ∃ s, 0 ≤ s ∧ s ≤ t ∧ nonFifoExec[s]? = some (.send 1 0) :=
        ⟨0, le_rfl, by omega, rfl⟩
      unfold Exec.outbound
      rw [dite_eq_left_of_eq_true (eq_true hex), Option.some_inj, Nat.find_eq_iff]
      exact ⟨⟨le_rfl, by omega, rfl⟩, fun n hn => by omega⟩
    have hnext : nextIdx nonFifoExec 1 0 0 t = 2 := by
      simp only [nextIdx, hout, Option.elim]
      rw [Exec.recvIdx_eq nonFifoExec_wf (r := 3) (q := 0) rfl]
      decide
    have hvect : (inlineAlg ({0} : Finset (Fin 2))).ts nonFifoExec 2 ⟨0, by simp⟩ = 1 := by
      rw [inlineAlg_ts, Exec.vc_self nonFifoExec_wf (p := 0) (by decide)]
      decide
    unfold InlineTS.lt
    simp only [query]
    have h0 : nonFifoExec.procAt 0 = some 1 := by decide
    have h2 : nonFifoExec.procAt 2 = some 0 := by decide
    rw [h0, h2]
    simp only [Finset.mem_singleton, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, ite_true,
      ne_eq, reduceCtorEq, not_false_eq_true, true_and, false_and, false_or, not_true_eq_false]
    rintro ⟨i, hi⟩
    have hi0 : i = ⟨0, by simp⟩ := Subsingleton.elim _ _
    subst hi0
    rw [hnext, hvect] at hi
    exact absurd hi (by decide)

end Podc.DelayedTimestamps
