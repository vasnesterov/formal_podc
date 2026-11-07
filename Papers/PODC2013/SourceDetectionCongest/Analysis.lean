import Papers.PODC2013.SourceDetectionCongest.Algorithm

/-!
# Analysis of Algorithm 1 (Section 4.2)

Lemma 4.3, Corollary 4.4, Lemma 4.6 and Theorem 1.2, for the general version with `β ≥ 1`
pairs per message (the remark after Theorem 1.2) and with Line 16 either after the loop
(`cap = ⊤`) or in every round (`cap = h`).
-/

namespace Podc.SourceDetectionCongest

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

section Recv

variable {inbox : V → Finset (ℕ ×ₗ V)} {s u : V} {x : ℕ ×ₗ V} {c : ℕ∞}

lemma mem_recvSet : x ∈ recvSet inbox s ↔ (∃ u, x ∈ inbox u) ∧ (ofLex x).2 = s := by
  simp [recvSet]

lemma le_recv (h : ∀ x ∈ recvSet inbox s, c ≤ (((ofLex x).1 + 1 : ℕ) : ℕ∞)) :
    c ≤ recv inbox s := Finset.le_inf h

lemma recv_le (hx : x ∈ inbox u) (hs : (ofLex x).2 = s) :
    recv inbox s ≤ (((ofLex x).1 + 1 : ℕ) : ℕ∞) :=
  inf_le (mem_recvSet.2 ⟨⟨u, hx⟩, hs⟩)

lemma exists_of_recv_ne_top (h : recv inbox s ≠ ⊤) :
    ∃ u x, x ∈ inbox u ∧ (ofLex x).2 = s ∧ recv inbox s = (((ofLex x).1 + 1 : ℕ) : ℕ∞) := by
  have hne : (recvSet inbox s).Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    exact h (by simp [recv, hem])
  obtain ⟨x, hx, heq⟩ := exists_mem_eq_inf _ hne fun x => (((ofLex x).1 + 1 : ℕ) : ℕ∞)
  obtain ⟨⟨u, hu⟩, hs⟩ := mem_recvSet.1 hx
  exact ⟨u, x, hu, hs, heq⟩

end Recv

lemma msg_subset_unsent {β : ℕ} {st : State V} : msg β st ⊆ st.unsent := topk_subset

lemma msg_subset_entries {β : ℕ} {st : State V} : msg β st ⊆ st.entries :=
  msg_subset_unsent.trans State.unsent_subset

/-- With `β = 1` the message is the smallest unsent entry, if any (Line 8: `argmin`). -/
lemma msg_one (st : State V) :
    msg 1 st = if h : st.unsent.Nonempty then {st.unsent.min' h} else ∅ := by
  split_ifs with h
  · ext x
    simp only [msg, mem_topk, Nat.lt_one_iff, card_eq_zero, filter_eq_empty_iff, not_lt,
      mem_singleton]
    constructor
    · rintro ⟨hx, hmin⟩; exact le_antisymm (hmin (min'_mem _ h)) (min'_le _ _ hx)
    · rintro rfl; exact ⟨min'_mem _ h, fun y hy => min'_le _ _ hy⟩
  · rw [not_nonempty_iff_eq_empty] at h
    simp [msg, h, topk]

lemma card_msg_le (β : ℕ) (st : State V) : #(msg β st) ≤ β := by
  rw [msg, card_topk]; exact min_le_left _ _

variable {E : V → V → Prop} [DecidableRel E] {S : Finset V} {β : ℕ} {cap : ℕ∞}

/-- What node `v` receives from `u` in round `t + 1`. -/
noncomputable abbrev inboxAt (E : V → V → Prop) [DecidableRel E] (S : Finset V) (β : ℕ) (cap : ℕ∞)
    (t : ℕ) (v : V) : V → Finset (ℕ ×ₗ V) :=
  fun u => if E u v then msg β (run E S β cap t u) else ∅

lemma run_succ (t : ℕ) (v : V) :
    run E S β cap (t + 1) v = step β cap (run E S β cap t v) (inboxAt E S β cap t v) := rfl

lemma est_succ (t : ℕ) (v s : V) : (run E S β cap (t + 1) v).est s =
    if cap < min ((run E S β cap t v).est s) (recv (inboxAt E S β cap t v) s) then ⊤
    else min ((run E S β cap t v).est s) (recv (inboxAt E S β cap t v) s) := rfl

lemma sent_succ (t : ℕ) (v s : V) : (run E S β cap (t + 1) v).sent s =
    if recv (inboxAt E S β cap t v) s < (run E S β cap t v).est s then false
    else (run E S β cap t v).sent s || decide (toLex (((run E S β cap t v).est s).toNat, s) ∈
      msg β (run E S β cap t v)) := rfl

/-- **Lemma 4.3.** Every entry `(h_s, s)` of `L_v^r` has `s ∈ S` and `h_s ≥ hd(s, v)`. -/
theorem lemma_4_3 : ∀ (r : ℕ) (v s : V), (run E S β cap r v).est s ≠ ⊤ →
    s ∈ S ∧ hd E s v ≤ (run E S β cap r v).est s
  | 0, v, s, h => by
      simp only [run, init] at h ⊢
      split_ifs at h ⊢ with hs
      · obtain ⟨rfl, hv⟩ := hs; exact ⟨hv, by simp⟩
      · exact absurd rfl h
  | r + 1, v, s, h => by
      rw [est_succ] at h ⊢
      split_ifs at h ⊢ with hc
      · exact absurd rfl h
      rcases min_choice ((run E S β cap r v).est s) (recv (inboxAt E S β cap r v) s) with he | he
      · rw [he] at h ⊢; exact lemma_4_3 r v s h
      · rw [he] at h ⊢
        obtain ⟨u, x, hx, hs, heq⟩ := exists_of_recv_ne_top h
        simp only [inboxAt] at hx
        split_ifs at hx with huv
        · obtain ⟨⟨m, s'⟩, rfl⟩ := toLex.surjective x
          simp only [ofLex_toLex] at hs heq
          subst hs
          have hm := State.mem_entries.1 (msg_subset_entries hx)
          obtain ⟨hS, hle⟩ := lemma_4_3 r u s' (by rw [hm]; simp)
          refine ⟨hS, ?_⟩
          rw [heq]
          calc hd E s' v ≤ hd E s' u + 1 := hd_le_succ huv
            _ ≤ m + 1 := by rw [hm] at hle; gcongr
            _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl
        · simp at hx

lemma hd_le_est (r : ℕ) (v s : V) : hd E s v ≤ (run E S β cap r v).est s := by
  by_cases h : (run E S β cap r v).est s = ⊤
  · rw [h]; exact le_top
  · exact (lemma_4_3 r v s h).2

lemma hd_le_recv (r : ℕ) (v s : V) : hd E s v ≤ recv (inboxAt E S β cap r v) s := by
  apply le_recv
  intro x hx
  obtain ⟨⟨u, hu⟩, hs⟩ := mem_recvSet.1 hx
  simp only [inboxAt] at hu
  split_ifs at hu with huv
  · obtain ⟨⟨m, s'⟩, rfl⟩ := toLex.surjective x
    simp only [ofLex_toLex] at hs ⊢
    subst hs
    have hm := State.mem_entries.1 (msg_subset_entries hu)
    have hle := hd_le_est (E := E) (S := S) (β := β) (cap := cap) r u s'
    rw [hm] at hle
    calc hd E s' v ≤ hd E s' u + 1 := hd_le_succ huv
      _ ≤ m + 1 := by gcongr
      _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl
  · simp at hu

/-- Stored distances never exceed `cap`. -/
lemma est_le_cap : ∀ (r : ℕ) (v s : V),
    (run E S β cap r v).est s = ⊤ ∨ (run E S β cap r v).est s ≤ cap
  | 0, v, s => by
      simp only [run, init]
      split_ifs <;> simp
  | r + 1, v, s => by
      rw [est_succ]
      split_ifs with h
      · exact Or.inl rfl
      · exact Or.inr (not_lt.1 h)

/-- Stored distances never increase. -/
lemma est_succ_le (r : ℕ) (v s : V) :
    (run E S β cap (r + 1) v).est s ≤ (run E S β cap r v).est s := by
  rcases est_le_cap (E := E) (S := S) (β := β) (cap := cap) r v s with h | h
  · rw [h]; exact le_top
  · rw [est_succ]
    split_ifs with hc
    · exact absurd hc (not_lt.2 ((min_le_left _ _).trans h))
    · exact min_le_left _ _

lemma est_anti {r r' : ℕ} (h : r ≤ r') (v s : V) :
    (run E S β cap r' v).est s ≤ (run E S β cap r v).est s := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (est_succ_le _ v s).trans ih

/-- Correct entries are never changed (nor deleted). -/
lemma est_eq_hd_of_le {r r' : ℕ} (h : r ≤ r') {v s : V}
    (hr : (run E S β cap r v).est s = hd E s v) : (run E S β cap r' v).est s = hd E s v :=
  le_antisymm (hr ▸ est_anti h v s) (hd_le_est r' v s)

/-- Receiving `(m, s)` from an in-neighbour in round `t + 1` makes the stored distance at most
`m + 1` (if `m + 1 ≤ cap`). -/
lemma est_succ_le_of_recv {t : ℕ} {u v s : V} {m : ℕ} (huv : E u v)
    (hx : toLex (m, s) ∈ msg β (run E S β cap t u)) (hcap : ((m + 1 : ℕ) : ℕ∞) ≤ cap) :
    (run E S β cap (t + 1) v).est s ≤ ((m + 1 : ℕ) : ℕ∞) := by
  have hr : recv (inboxAt E S β cap t v) s ≤ ((m + 1 : ℕ) : ℕ∞) :=
    recv_le (u := u) (x := toLex (m, s)) (by simp [inboxAt, huv, hx]) rfl
  have hmin : min ((run E S β cap t v).est s) (recv (inboxAt E S β cap t v) s) ≤
      ((m + 1 : ℕ) : ℕ∞) := (min_le_right _ _).trans hr
  rw [est_succ]
  split_ifs with hc
  · exact absurd hc (not_lt.2 (hmin.trans hcap))
  · exact hmin

/-- **Corollary 4.4 (first part).** If `v` receives `(hd(s,v) - 1, s)` in round `t + 1` (and
`hd(s,v) ≤ cap`, automatic for `cap = ⊤`), then `(hd(s,v), s) ∈ L_v^{r'}` for all `r' ≥ t + 1`.
If `(hd(s,v), s) ∈ L_v^0`, then it is in all `L_v^{r'}`. -/
theorem corollary_4_4_persist {t : ℕ} {u v s : V} {m : ℕ} (huv : E u v)
    (hx : toLex (m, s) ∈ msg β (run E S β cap t u)) (hm : hd E s v = ((m + 1 : ℕ) : ℕ∞))
    (hcap : hd E s v ≤ cap) {r' : ℕ} (hr' : t + 1 ≤ r') :
    toLex (m + 1, s) ∈ (run E S β cap r' v).entries := by
  rw [State.mem_entries]
  rw [hm] at hcap
  have h1 : (run E S β cap (t + 1) v).est s = hd E s v :=
    le_antisymm (hm ▸ est_succ_le_of_recv huv hx hcap) (hd_le_est _ v s)
  rw [est_eq_hd_of_le hr' h1, hm]

theorem corollary_4_4_persist_init {v s : V} {m : ℕ}
    (h : toLex (m, s) ∈ (run E S β cap 0 v).entries) (r' : ℕ) :
    toLex (m, s) ∈ (run E S β cap r' v).entries := by
  rw [State.mem_entries] at *
  simp only [run, init] at h
  split_ifs at h with hs
  · obtain ⟨rfl, hS⟩ := hs
    have : (m : ℕ∞) = 0 := h.symm
    rw [this]
    have h0 : (run E S β cap 0 s).est s = hd E s s := by simp [run, init, hS]
    rw [est_eq_hd_of_le (Nat.zero_le r') h0, hd_self]
  · exact absurd h.symm (ENat.natCast_ne_top m)

/-! ### The `sent` flags -/

/-- A set flag means that the current entry was sent in an earlier round. -/
lemma sent_spec : ∀ (r : ℕ) (v s : V), (run E S β cap r v).sent s = true →
    (run E S β cap r v).est s ≠ ⊤ →
    ∃ t < r, toLex (((run E S β cap r v).est s).toNat, s) ∈ msg β (run E S β cap t v)
  | 0, v, s, h, _ => by simp [run, init] at h
  | r + 1, v, s, h, hne => by
      rw [sent_succ] at h
      split_ifs at h with hlt
      have hmin : min ((run E S β cap r v).est s) (recv (inboxAt E S β cap r v) s) =
          (run E S β cap r v).est s := min_eq_left (not_lt.1 hlt)
      have hest : (run E S β cap (r + 1) v).est s = (run E S β cap r v).est s := by
        rw [est_succ, hmin] at hne ⊢
        split_ifs at hne ⊢
        · exact absurd rfl hne
        · rfl
      rw [hest]
      rw [hest] at hne
      rcases Bool.or_eq_true_iff.1 h with h1 | h1
      · obtain ⟨t, ht, hm⟩ := sent_spec r v s h1 hne
        exact ⟨t, by omega, hm⟩
      · exact ⟨r, by omega, of_decide_eq_true h1⟩

/-- A correct entry that is marked or being sent stays correct and marked. -/
lemma sent_succ_eq_true {r : ℕ} {v s : V} (hest : (run E S β cap r v).est s = hd E s v)
    (h : (run E S β cap r v).sent s = true ∨
      toLex (((run E S β cap r v).est s).toNat, s) ∈ msg β (run E S β cap r v)) :
    (run E S β cap (r + 1) v).sent s = true := by
  rw [sent_succ]
  split_ifs with hc
  · exact absurd hc (not_lt.2 (hest ▸ hd_le_recv r v s))
  rcases h with h | h
  · simp [h]
  · simp [h]

/-- Once a correct pair has been sent, it stays in `L_v` and marked as sent. -/
lemma sent_persist {t : ℕ} {v s : V} {m : ℕ} (hx : toLex (m, s) ∈ msg β (run E S β cap t v))
    (hm : hd E s v = m) {r : ℕ} (hr : t < r) :
    (run E S β cap r v).sent s = true ∧ (run E S β cap r v).est s = m := by
  have h0 : (run E S β cap t v).est s = hd E s v := by
    rw [hm]; exact State.mem_entries.1 (msg_subset_entries hx)
  induction hr with
  | refl =>
    refine ⟨sent_succ_eq_true h0 (Or.inr ?_), hm ▸ est_eq_hd_of_le (Nat.le_succ t) h0⟩
    rw [h0, hm]; simpa using hx
  | step hle ih =>
    have he : (run E S β cap _ v).est s = hd E s v := hm ▸ ih.2
    exact ⟨sent_succ_eq_true he (Or.inl ih.1), hm ▸ est_eq_hd_of_le (Nat.le_succ _) he⟩

/-! ### Prefixes (Corollary 4.4, second part) -/

omit [DecidableRel E] in
/-- If `top_k(L_v^{(d)}) ⊆ L_v`, then every entry of `L_v` below an element of
`top_k(L_v^{(d)})` belongs to `top_k(L_v^{(d)})`: `top_k(L_v^{(d)})` is a prefix of `L_v`. -/
lemma mem_topk_of_mem_entries {st : State V} {v : V} {d k : ℕ}
    (hst : ∀ s, st.est s ≠ ⊤ → s ∈ S ∧ hd E s v ≤ st.est s)
    (hT : topk k (Lspec E S d v) ⊆ st.entries) {x y : ℕ ×ₗ V}
    (hx : x ∈ topk k (Lspec E S d v)) (hy : y ∈ st.entries) (hyx : y ≤ x) :
    y ∈ topk k (Lspec E S d v) := by
  obtain ⟨⟨e, s'⟩, rfl⟩ := toLex.surjective y
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
  have he := State.mem_entries.1 hy
  obtain ⟨hS, hle⟩ := hst s' (by rw [he]; simp)
  rw [he] at hle
  have hxL := mem_Lspec.1 (topk_subset hx)
  have hem : e ≤ m := by
    rw [Prod.Lex.toLex_le_toLex] at hyx
    rcases hyx with h | ⟨h, -⟩ <;> omega
  have hfin : hd E s' v ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  set h0 := (hd E s' v).toNat with hh0
  have h0e : hd E s' v = h0 := (ENat.natCast_toNat hfin).symm
  have h0le : h0 ≤ e := by rw [h0e] at hle; exact_mod_cast hle
  have hin : toLex (h0, s') ∈ topk k (Lspec E S d v) := by
    refine mem_topk_of_le hx (mem_Lspec.2 ⟨hS, h0e, by omega⟩) ?_
    refine le_trans ?_ hyx
    rw [Prod.Lex.toLex_le_toLex]
    rcases Nat.lt_or_ge h0 e with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, le_rfl⟩
  have := State.mem_entries.1 (hT hin)
  rw [he] at this
  have : e = h0 := by exact_mod_cast this
  rwa [this]

omit [DecidableRel E] in
/-- **Corollary 4.4 (second part, corrected).** If `top_k(L_v^{(h)}) ⊆ L_v`, then
`top_k` of the entries of `L_v` with distance `≤ h` is `top_k(L_v^{(h)})`. (The paper states
`top_k(L_v^r) = top_k(L_v^{(h)})`, which fails when `|L_v^{(h)}| < k` and `L_v^r` has an entry
at distance `> h`, see `Counterexamples.lean`.) -/
lemma output_eq_of_subset {st : State V} {v : V} {h k : ℕ}
    (hst : ∀ s, st.est s ≠ ⊤ → s ∈ S ∧ hd E s v ≤ st.est s)
    (hT : topk k (Lspec E S h v) ⊆ st.entries) :
    output h k st = topk k (Lspec E S h v) := by
  set F := Lspec E S h v
  set G := st.entries.filter fun x => (ofLex x).1 ≤ h
  have hTG : topk k F ⊆ G := by
    intro x hx
    obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
    exact mem_filter.2 ⟨hT hx, (mem_Lspec.1 (topk_subset hx)).2.2⟩
  ext z
  simp only [output]
  constructor
  · intro hz
    obtain ⟨⟨e, s⟩, rfl⟩ := toLex.surjective z
    have hzG := topk_subset hz
    obtain ⟨hzE, hzh⟩ := mem_filter.1 hzG
    simp only [ofLex_toLex] at hzh
    have he := State.mem_entries.1 hzE
    obtain ⟨hS, hle⟩ := hst s (by rw [he]; simp)
    rw [he] at hle
    have hfin : hd E s v ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
    set h0 := (hd E s v).toNat
    have h0e : hd E s v = h0 := (ENat.natCast_toNat hfin).symm
    have h0le : h0 ≤ e := by rw [h0e] at hle; exact_mod_cast hle
    have hF : toLex (h0, s) ∈ F := mem_Lspec.2 ⟨hS, h0e, by omega⟩
    by_cases hin : toLex (h0, s) ∈ topk k F
    · have := State.mem_entries.1 (hT hin)
      rw [he] at this
      have : e = h0 := by exact_mod_cast this
      rwa [this]
    · exfalso
      -- every element of `topk k F` is below `(h0, s) ≤ (e, s)`
      have hlt : ∀ t ∈ topk k F, t < toLex (h0, s) := fun t ht => by
        by_contra hge
        exact hin (mem_topk_of_le ht hF (not_lt.1 hge))
      have hcardF : k ≤ #(F.filter (· < toLex (h0, s))) := by
        by_contra hc; exact hin (mem_topk.2 ⟨hF, by omega⟩)
      have hcardT : #(topk k F) = k := by
        rw [card_topk]
        have := card_le_card (filter_subset (· < toLex (h0, s)) F)
        omega
      have hsub : topk k F ⊆ G.filter (· < toLex (e, s)) := fun t ht =>
        mem_filter.2 ⟨hTG ht, lt_of_lt_of_le (hlt t ht) (by
          rw [Prod.Lex.toLex_le_toLex]
          rcases Nat.lt_or_ge h0 e with h | h
          · exact Or.inl h
          · exact Or.inr ⟨by omega, le_rfl⟩)⟩
      have h1 := card_le_card hsub
      have h2 : #(G.filter (· < toLex (e, s))) < k := (mem_topk.1 hz).2
      omega
  · intro hz
    refine mem_topk.2 ⟨hTG hz, lt_of_le_of_lt (card_le_card fun y hy => ?_) (mem_topk.1 hz).2⟩
    obtain ⟨hyG, hyz⟩ := mem_filter.1 hy
    have hyT := mem_topk_of_mem_entries hst hT hz (mem_filter.1 hyG).1 hyz.le
    exact mem_filter.2 ⟨topk_subset hyT, hyz⟩

end Podc.SourceDetectionCongest
