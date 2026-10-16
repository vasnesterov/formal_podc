import Papers.PODC2020.AsyncApproxBCDirected.Necessity

/-!
# Full-information algorithms in the asynchronous model

An algorithm whose local state is `(input, history of received messages)` and whose sends are a
function `react v x h` of the history `h` reached (`h = []` for the initial step). All decisions
of such an algorithm are functions of histories, which makes refinement proofs manageable.

* `HistSpec.toAlg` — the corresponding `Algorithm`.
* `hist` — the history of a node in a run; `hist_succ` — it grows by at most one entry per step.
* `chan_inv` — channel invariant: for correct `q → v`, the messages `v` received from `q`
  followed by the channel content are exactly the messages `q` sent to `v`.
* `eventually_received` — in fair runs every message sent between correct nodes is received.
* `exists_fair_extension` — every finite prefix of a run extends to a fair run.
-/

open Finset

-- CSLib candidate (general directed-network / asynchronous Byzantine infrastructure)

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V M : Type*} [DecidableEq V]

/-- A full-information algorithm. -/
structure HistSpec (V M : Type*) where
  /-- Messages sent when the history becomes `h` (`h = []`: the initial step). -/
  react : V → ℝ → List (V × M) → List (V × M)
  /-- Output as a function of the history. -/
  out : V → ℝ → List (V × M) → Option ℝ

/-- A step changes the state of `v` at most by one reception. -/
theorem step_st {S : Type*} (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj]
    (B : Finset V) (C : Config V M S) (e : Event V M) (v : V) :
    (step A G B C e).st v = C.st v ∨ ∃ u m, (step A G B C e).st v = (A.recv v (C.st v) u m).1 := by
  cases e with
  | deliver x y =>
    rcases hc : C.chan x y with _ | ⟨m, rest⟩
    · left; simp [step, hc]
    · by_cases hy : y ∈ B
      · left; simp [step, hc, hy]
      · by_cases hv : v = y
        · subst hv; right; exact ⟨x, m, by simp [step, hc, hy, process, Config.pop]⟩
        · left; simp [step, hc, hy, process, Config.pop, hv]
  | byz x y m =>
    by_cases h : x ∈ B ∧ y ∉ B ∧ G.Adj x y ∧ x ≠ y
    · by_cases hv : v = y
      · subst hv; right; exact ⟨x, m, by rw [step, ite_eq_left_of_eq_true _ _ (eq_true h)]; simp [process]⟩
      · left; rw [step, ite_eq_left_of_eq_true _ _ (eq_true h)]; simp [process, hv]
    · left; simp [step, h]
  | skip => left; rfl

namespace HistSpec

variable (H : HistSpec V M)

/-- The algorithm with states `(input, history)`. -/
def toAlg : Algorithm V M (ℝ × List (V × M)) where
  start v x := ((x, []), H.react v x [])
  recv v s u m := ((s.1, s.2 ++ [(u, m)]), H.react v s.1 (s.2 ++ [(u, m)]))
  out v s := H.out v s.1 s.2

/-- All messages sent by `v` (input `x`) when its history is `h`, in sending order. -/
def allSends (v : V) (x : ℝ) (h : List (V × M)) : List (V × M) :=
  ((List.range (h.length + 1)).map fun k => H.react v x (h.take k)).flatten

theorem allSends_nil (v : V) (x : ℝ) : H.allSends v x [] = H.react v x [] := by
  simp [allSends]

theorem allSends_snoc (v : V) (x : ℝ) (h : List (V × M)) (e : V × M) :
    H.allSends v x (h ++ [e]) = H.allSends v x h ++ H.react v x (h ++ [e]) := by
  simp only [allSends, List.length_append, List.length_singleton]
  rw [List.range_succ, List.map_append, List.flatten_append]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [List.take_append_of_le_length (by omega)]
  · simp [List.take_of_length_le]

/-- Messages sent to `w`. -/
def sentTo (v : V) (x : ℝ) (h : List (V × M)) (w : V) : List M :=
  ((H.allSends v x h).filter fun o => o.1 = w).map Prod.snd

/-- Messages received from `q`. -/
def recvFrom (q : V) (h : List (V × M)) : List M := (h.filter fun o => o.1 = q).map Prod.snd

section Run

variable (G : Digraph V) [DecidableRel G.Adj] (B : Finset V) (inp : V → ℝ) (ev : ℕ → Event V M)

/-- The history of node `v` at time `t`. -/
def hist (t : ℕ) (v : V) : List (V × M) := ((run H.toAlg G B inp ev t).st v).2

theorem fst_st (t : ℕ) (v : V) : ((run H.toAlg G B inp ev t).st v).1 = inp v := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases step_st H.toAlg G B (run H.toAlg G B inp ev t) (ev t) v with h | ⟨u, m, h⟩
    · simp only [run]; rw [h, ih]
    · simp only [run]; rw [h]; exact ih

/-- One step: a history grows by at most one entry. -/
theorem hist_succ (t : ℕ) (v : V) :
    H.hist G B inp ev (t + 1) v = H.hist G B inp ev t v ∨
      ∃ e, H.hist G B inp ev (t + 1) v = H.hist G B inp ev t v ++ [e] := by
  rcases step_st H.toAlg G B (run H.toAlg G B inp ev t) (ev t) v with h | ⟨u, m, h⟩
  · left; simp only [hist, run]; rw [h]
  · right; exact ⟨(u, m), by simp only [hist, run]; rw [h]; rfl⟩

theorem hist_prefix {t t' : ℕ} (h : t ≤ t') (v : V) :
    H.hist G B inp ev t v <+: H.hist G B inp ev t' v := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rcases H.hist_succ G B inp ev _ v with h | ⟨e, h⟩
    · rw [h]; exact ih
    · rw [h]; exact ih.trans (List.prefix_append _ _)

end Run

theorem sendTo_append {G : Digraph V} [DecidableRel G.Adj] {B : Finset V} {y : V}
    (l₁ l₂ : List (V × M)) (b : V) :
    sendTo G B y (l₁ ++ l₂) b = sendTo G B y l₁ b ++ sendTo G B y l₂ b := by
  unfold sendTo; split_ifs <;> simp

section Inv

variable (G : Digraph V) [DecidableRel G.Adj] (B : Finset V) (inp : V → ℝ) (ev : ℕ → Event V M)

theorem st_run (t : ℕ) (v : V) :
    (run H.toAlg G B inp ev t).st v = (inp v, H.hist G B inp ev t v) := by
  ext
  · exact H.fst_st G B inp ev t v
  · rfl

theorem process_st (C : Config V M (ℝ × List (V × M))) (y x : V) (m : M) (w : V) :
    (process H.toAlg G B C y x m).st w =
      if w = y then ((C.st y).1, (C.st y).2 ++ [(x, m)]) else C.st w := by
  by_cases h : w = y
  · subst h; simp [process, toAlg]
  · simp [process, h]

theorem process_chan (C : Config V M (ℝ × List (V × M))) (y x : V) (m : M) (a b : V) :
    (process H.toAlg G B C y x m).chan a b =
      if a = y then C.chan a b ++ sendTo G B y (H.react y (C.st y).1 ((C.st y).2 ++ [(x, m)])) b
      else C.chan a b := by
  simp [process, toAlg]

theorem recvFrom_snoc (q : V) (h : List (V × M)) (x : V) (m : M) :
    recvFrom q (h ++ [(x, m)]) = recvFrom q h ++ (if x = q then [m] else []) := by
  by_cases hx : x = q <;> simp [recvFrom, List.filter_append, hx]

/-- **Channel invariant**: for correct `q ≠ v`, what `v` received from `q`, followed by the
content of the channel `q → v`, is exactly what `q` sent to `v`. -/
theorem chan_inv {q v : V} (hq : q ∉ B) (hqv : q ≠ v) (t : ℕ) :
    recvFrom q (H.hist G B inp ev t v) ++ (run H.toAlg G B inp ev t).chan q v =
      sendTo G B q (H.allSends q (inp q) (H.hist G B inp ev t q)) v := by
  induction t with
  | zero =>
    simp [hist, run, init, toAlg, recvFrom, allSends_nil, hq]
  | succ t ih =>
    have hok := chanOK_run (A := H.toAlg) (G := G) (B := B) inp ev t
    have hst := H.st_run G B inp ev t
    simp only [hist, run] at ih ⊢
    set C := run H.toAlg G B inp ev t with hC
    -- the case where `q` itself receives a message
    have hrecv_q : ∀ (C₁ : Config V M (ℝ × List (V × M))) (x : V) (m : M), C₁.st = C.st →
        C₁.chan q v = C.chan q v →
        recvFrom q ((process H.toAlg G B C₁ q x m).st v).2 ++
            (process H.toAlg G B C₁ q x m).chan q v =
          sendTo G B q (H.allSends q (inp q) ((process H.toAlg G B C₁ q x m).st q).2) v := by
      intro C₁ x m h1 h2
      have hvq : v ≠ q := fun h => hqv h.symm
      rw [H.process_st, H.process_st, H.process_chan, ite_eq_right hvq, ite_eq_left rfl, ite_eq_left rfl, h2, h1,
        ← List.append_assoc, ih, hst, allSends_snoc, sendTo_append]
    cases hev : ev t with
    | skip => simpa [step] using ih
    | deliver x y =>
      rcases hc : C.chan x y with _ | ⟨m, rest⟩
      · simpa [step, hc] using ih
      by_cases hy : y ∈ B
      · simpa [step, hc, hy] using ih
      have hxy : x ≠ y := (hok x y (by simp [hc])).2.2
      simp only [step, hc, hy, ite_false]
      by_cases hqy : q = y
      · subst hqy
        exact hrecv_q _ x m rfl (by simp [Config.pop, Ne.symm hxy])
      rw [H.process_st, H.process_st, H.process_chan, ite_eq_right hqy, ite_eq_right hqy]
      by_cases hvy : v = y
      · subst hvy
        rw [ite_eq_left rfl]
        simp only [Config.pop, and_true]
        rw [recvFrom_snoc]
        by_cases hxq : x = q
        · subst hxq
          rw [ite_eq_left rfl, ite_eq_left rfl, List.append_assoc, List.singleton_append, ← hc]
          exact ih
        · rw [ite_eq_right hxq, ite_eq_right (Ne.symm hxq), List.append_nil]
          exact ih
      · rw [ite_eq_right hvy]
        simp only [Config.pop]
        have : ¬ (q = x ∧ v = y) := fun h => hvy h.2
        rw [ite_eq_right this]
        exact ih
    | byz x y m =>
      by_cases h : x ∈ B ∧ y ∉ B ∧ G.Adj x y ∧ x ≠ y
      swap
      · simpa [step, h] using ih
      rw [step, ite_eq_left_of_eq_true _ _ (eq_true h)]
      by_cases hqy : q = y
      · subst hqy
        exact hrecv_q _ x m rfl rfl
      rw [H.process_st, H.process_st, H.process_chan, ite_eq_right hqy, ite_eq_right hqy]
      by_cases hvy : v = y
      · subst hvy
        have hxq : x ≠ q := fun h' => hq (h' ▸ h.1)
        rw [ite_eq_left rfl, recvFrom_snoc, ite_eq_right hxq, List.append_nil]
        exact ih
      · rw [ite_eq_right hvy]; exact ih

theorem recvFrom_prefix {q v : V} (hq : q ∉ B) (hqv : q ≠ v) (t : ℕ) :
    recvFrom q (H.hist G B inp ev t v) <+:
      sendTo G B q (H.allSends q (inp q) (H.hist G B inp ev t q)) v := by
  rw [← H.chan_inv G B inp ev hq hqv t]; exact List.prefix_append _ _

theorem allSends_prefix {h h' : List (V × M)} (hh : h <+: h') (v : V) (x : ℝ) :
    H.allSends v x h <+: H.allSends v x h' := by
  obtain ⟨l, rfl⟩ := hh
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    rw [← List.append_assoc, allSends_snoc]; exact ih.trans (List.prefix_append _ _)

theorem sendTo_prefix {G : Digraph V} [DecidableRel G.Adj] {B : Finset V} {y : V}
    {l₁ l₂ : List (V × M)} (h : l₁ <+: l₂) (b : V) : sendTo G B y l₁ b <+: sendTo G B y l₂ b := by
  obtain ⟨l, rfl⟩ := h; rw [sendTo_append]; exact List.prefix_append _ _

theorem recvFrom_mono {q v : V} {t t' : ℕ} (h : t ≤ t') :
    recvFrom q (H.hist G B inp ev t v) <+: recvFrom q (H.hist G B inp ev t' v) := by
  obtain ⟨l, hl⟩ := H.hist_prefix G B inp ev h v
  rw [← hl]; simp [recvFrom, List.filter_append]

/-- In a fair run, every message sent from a correct node to a correct out-neighbour is
eventually received. -/
theorem eventually_received (hfair : Fair H.toAlg G B inp ev) {q v : V} (hq : q ∉ B)
    (hv : v ∉ B) (hqv : q ≠ v) (t : ℕ) :
    ∃ t', sendTo G B q (H.allSends q (inp q) (H.hist G B inp ev t q)) v <+:
      recvFrom q (H.hist G B inp ev t' v) := by
  set target := sendTo G B q (H.allSends q (inp q) (H.hist G B inp ev t q)) v
  -- it suffices to receive `target.length` messages
  suffices hlen : ∃ t', target.length ≤ (recvFrom q (H.hist G B inp ev t' v)).length by
    obtain ⟨t', ht'⟩ := hlen
    refine ⟨max t t', ?_⟩
    have h1 : target <+: sendTo G B q (H.allSends q (inp q)
        (H.hist G B inp ev (max t t') q)) v :=
      sendTo_prefix (H.allSends_prefix (H.hist_prefix G B inp ev (le_max_left _ _) q) _ _) _
    have h2 := H.recvFrom_prefix G B inp ev hq hqv (max t t')
    have h3 : target.length ≤ (recvFrom q (H.hist G B inp ev (max t t') v)).length :=
      ht'.trans (H.recvFrom_mono G B inp ev (le_max_right _ _)).length_le
    exact (List.prefix_of_prefix_length_le h1 h2 h3)
  -- induction on the number of missing messages
  suffices key : ∀ n s, target.length ≤ n + (recvFrom q (H.hist G B inp ev s v)).length →
      t ≤ s → ∃ t', target.length ≤ (recvFrom q (H.hist G B inp ev t' v)).length from
    key target.length t (by omega) le_rfl
  intro n
  induction n with
  | zero => intro s hs _; exact ⟨s, by omega⟩
  | succ n ih =>
    intro s hs hts
    by_cases hle0 : target.length ≤ (recvFrom q (H.hist G B inp ev s v)).length
    · exact ⟨s, hle0⟩
    -- the channel is non-empty at time `s`
    have hsent : target <+: sendTo G B q (H.allSends q (inp q) (H.hist G B inp ev s q)) v :=
      sendTo_prefix (H.allSends_prefix (H.hist_prefix G B inp ev hts q) _ _) _
    have hinv := H.chan_inv G B inp ev hq hqv s
    have hne : (run H.toAlg G B inp ev s).chan q v ≠ [] := by
      intro h0
      rw [h0, List.append_nil] at hinv
      have := hsent.length_le
      rw [← hinv] at this
      omega
    obtain ⟨s', hs', hdel⟩ := hfair q v hq hv s hne
    -- either already enough at `s'`, or the delivery at `s'` adds one message
    by_cases hle : target.length ≤ (recvFrom q (H.hist G B inp ev s' v)).length
    · exact ⟨s', hle⟩
    have hmono := (H.recvFrom_mono G B inp ev hs' (q := q) (v := v)).length_le
    have hne' : (run H.toAlg G B inp ev s').chan q v ≠ [] := by
      intro h0
      have hinv' := H.chan_inv G B inp ev hq hqv s'
      rw [h0, List.append_nil] at hinv'
      have hsent' : target <+: sendTo G B q (H.allSends q (inp q) (H.hist G B inp ev s' q)) v :=
        sendTo_prefix (H.allSends_prefix (H.hist_prefix G B inp ev (hts.trans hs') q) _ _) _
      have := hsent'.length_le
      rw [← hinv'] at this
      omega
    obtain ⟨m, rest, hmr⟩ := List.exists_cons_of_ne_nil hne'
    have hstep : H.hist G B inp ev (s' + 1) v = H.hist G B inp ev s' v ++ [(q, m)] := by
      have e1 : run H.toAlg G B inp ev (s' + 1) =
          step H.toAlg G B (run H.toAlg G B inp ev s') (ev s') := rfl
      simp only [hist]
      rw [e1, hdel]
      simp only [step, hmr, hv, ite_false]
      rw [H.process_st, ite_eq_left rfl]
      rfl
    have hlen : (recvFrom q (H.hist G B inp ev (s' + 1) v)).length =
        (recvFrom q (H.hist G B inp ev s' v)).length + 1 := by
      rw [hstep]; simp [recvFrom, List.filter_append]
    exact ih (s' + 1) (by omega) (by omega)

end Inv

section More

variable (G : Digraph V) [DecidableRel G.Adj] (B : Finset V) (inp : V → ℝ) (ev : ℕ → Event V M)

/-- Every received message comes from a different node. -/
theorem hist_sender_ne (t : ℕ) (v : V) : ∀ e ∈ H.hist G B inp ev t v, e.1 ≠ v := by
  induction t with
  | zero => simp [hist, run, init, toAlg]
  | succ t ih =>
    have hok := chanOK_run (A := H.toAlg) (G := G) (B := B) inp ev t
    intro e he
    have e1 : run H.toAlg G B inp ev (t + 1) = step H.toAlg G B (run H.toAlg G B inp ev t) (ev t) :=
      rfl
    simp only [hist] at he ih
    rw [e1] at he
    cases hev : ev t with
    | skip => rw [hev] at he; exact ih e he
    | deliver x y =>
      rw [hev] at he
      simp only [step] at he
      rcases hc : (run H.toAlg G B inp ev t).chan x y with _ | ⟨m, rest⟩
      · rw [hc] at he; exact ih e he
      · rw [hc] at he
        by_cases hy : y ∈ B
        · simp only [hy, ite_true] at he; exact ih e he
        · simp only [hy, ite_false] at he
          rw [H.process_st] at he
          by_cases hvy : v = y
          · subst hvy
            simp only [ite_true, Config.pop, List.mem_append, List.mem_singleton] at he
            rcases he with he | rfl
            · exact ih e he
            · exact (hok x v (by simp [hc])).2.2
          · simp only [hvy, ite_false, Config.pop] at he; exact ih e he
    | byz x y m =>
      rw [hev] at he
      by_cases h : x ∈ B ∧ y ∉ B ∧ G.Adj x y ∧ x ≠ y
      · rw [step, ite_eq_left_of_eq_true _ _ (eq_true h), H.process_st] at he
        by_cases hvy : v = y
        · subst hvy
          simp only [ite_true, List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact ih e he
          · exact h.2.2.2
        · simp only [hvy, ite_false] at he; exact ih e he
      · simp only [step, h, ite_false] at he; exact ih e he

/-- A message received by a correct node from a correct node was sent by it. -/
theorem mem_sent_of_mem_hist {u v : V} (hu : u ∉ B) {t : ℕ} {m : M}
    (hm : (u, m) ∈ H.hist G B inp ev t v) : (v, m) ∈ H.allSends u (inp u) (H.hist G B inp ev t u) := by
  have huv : u ≠ v := H.hist_sender_ne G B inp ev t v _ hm
  have hpre := H.recvFrom_prefix G B inp ev hu huv t
  have hmr : m ∈ recvFrom u (H.hist G B inp ev t v) := by
    simp only [recvFrom, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨(u, m), ⟨hm, rfl⟩, rfl⟩
  have := hpre.subset hmr
  unfold sendTo at this
  split_ifs at this
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at this
    obtain ⟨⟨w, m'⟩, ⟨h1, h2⟩, rfl⟩ := this
    simp only at h2; subst h2; exact h1
  · simp at this

/-- In a fair run, a message sent by a correct node to a correct out-neighbour is received. -/
theorem mem_hist_of_mem_sent (hfair : Fair H.toAlg G B inp ev) {u v : V} (hu : u ∉ B)
    (hv : v ∉ B) (huv : u ≠ v) (hadj : G.Adj u v) {t : ℕ} {m : M}
    (hm : (v, m) ∈ H.allSends u (inp u) (H.hist G B inp ev t u)) :
    ∃ t', (u, m) ∈ H.hist G B inp ev t' v := by
  obtain ⟨t', ht'⟩ := H.eventually_received G B inp ev hfair hu hv huv t
  refine ⟨t', ?_⟩
  have hms : m ∈ sendTo G B u (H.allSends u (inp u) (H.hist G B inp ev t u)) v := by
    simp only [sendTo, hv, not_false_eq_true, hadj, ne_eq, huv, and_self, ite_true, List.mem_map,
      List.mem_filter, decide_eq_true_eq]
    exact ⟨(v, m), ⟨hm, rfl⟩, rfl⟩
  have := ht'.subset hms
  simp only [recvFrom, List.mem_map, List.mem_filter, decide_eq_true_eq] at this
  obtain ⟨⟨w, m'⟩, ⟨h1, h2⟩, rfl⟩ := this
  simp only at h2; subst h2; exact h1

/-- Histories pass through all their prefixes. -/
theorem exists_time_hist (v : V) (t : ℕ) {h : List (V × M)} (hh : h <+: H.hist G B inp ev t v) :
    ∃ t' ≤ t, H.hist G B inp ev t' v = h := by
  induction t with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    have : H.hist G B inp ev 0 v = [] := rfl
    rw [this] at hh ⊢; exact (List.prefix_nil.mp hh).symm
  | succ t ih =>
    rcases H.hist_succ G B inp ev t v with h1 | ⟨e, h1⟩
    · obtain ⟨t', ht', h2⟩ := ih (h1 ▸ hh); exact ⟨t', by omega, h2⟩
    · rw [h1] at hh
      rcases List.prefix_concat_iff.mp hh with h2 | h2
      · exact ⟨t + 1, le_rfl, h1.trans h2.symm⟩
      · obtain ⟨t', ht', h3⟩ := ih h2; exact ⟨t', by omega, h3⟩

end More

end HistSpec

/-! ## Fair extensions -/

theorem roundRobin_hits [Fintype V] (x y : V) (t : ℕ) :
    ∃ t' ≥ t, roundRobin (V := V) (M := M) t' = .deliver x y := by
  have hN : 0 < Fintype.card (V × V) := Fintype.card_pos_iff.mpr ⟨(x, y)⟩
  set i := (Fintype.equivFin (V × V) (x, y)).val
  have hi : i < Fintype.card (V × V) := (Fintype.equivFin (V × V) (x, y)).isLt
  refine ⟨Fintype.card (V × V) * t + i, by nlinarith, ?_⟩
  have hmod : (Fintype.card (V × V) * t + i) % Fintype.card (V × V) = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have h' : (Fintype.equivFin (V × V)).symm
      ⟨(Fintype.card (V × V) * t + i) % Fintype.card (V × V), Nat.mod_lt _ hN⟩ = (x, y) := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext hmod
  simp only [roundRobin, hN, ↓reduceDIte, h']

/-- Every finite prefix of an execution extends to a fair execution. -/
theorem exists_fair_extension [Fintype V] {S : Type*} (A : Algorithm V M S) (G : Digraph V)
    [DecidableRel G.Adj] (B : Finset V) (inp : V → ℝ) (ev : ℕ → Event V M) (T : ℕ) :
    ∃ ev' : ℕ → Event V M, Fair A G B inp ev' ∧
      ∀ t ≤ T, run A G B inp ev' t = run A G B inp ev t := by
  classical
  refine ⟨fun t => if t < T then ev t else roundRobin t, ?_, ?_⟩
  · intro x y _ _ t _
    obtain ⟨t', ht', h⟩ := roundRobin_hits (M := M) x y (max t T)
    refine ⟨t', le_of_max_le_left ht', ?_⟩
    simp only [show ¬ t' < T by have := le_of_max_le_right ht'; omega, ite_false, h]
  · intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [run]
      rw [ih (by omega)]
      simp [show t < T by omega]

end AsyncApproxBCDirected
