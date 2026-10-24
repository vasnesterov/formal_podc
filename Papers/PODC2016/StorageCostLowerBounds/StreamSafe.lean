import Papers.PODC2016.StorageCostLowerBounds.StreamInv

/-!
# Safety of the streaming relay

`inv_reach`: the invariant `Inv` holds in every reachable configuration; hence the streaming
relay is atomic and regular.
-/

namespace Podc.StorageCost.Stream

open Cslib.ChannelFailures Cslib.SharedMemory
open Podc.StorageCost.Relay (OkPair)

variable {n B : ℕ} (qs : ℕ) {C : Cfg n B} {α : Hist n B}

/-! ### Frame lemma -/

/-- The invariant depends only on the writer and reader states, the `pf, pa, pd` components of
the servers, pending operations, channels and the received-bit counters. -/
theorem inv_frame {C C' : Cfg n B} {α : Hist n B} (hI : Inv qs C α)
    (hw : ws C' = ws C) (hr : rs C' = rs C)
    (hs : ∀ j, (ss C' j).1 = (ss C j).1 ∧ (ss C' j).2.1 = (ss C j).2.1 ∧
      (ss C' j).2.2.1 = (ss C j).2.2.1)
    (hp : C'.pend = C.pend) (hc : C'.chan = C.chan) (hx : ∀ j, xW C' j = xW C j) :
    Inv qs C' α := by
  have h1 : ∀ j, (ss C' j).1 = (ss C j).1 := fun j => (hs j).1
  have h2 : ∀ j, (ss C' j).2.1 = (ss C j).2.1 := fun j => (hs j).2.1
  have h3 : ∀ j, (ss C' j).2.2.1 = (ss C j).2.2.1 := fun j => (hs j).2.2
  refine ⟨hI.wops, ?_, ?_, ?_, ?_, hI.wresp, ?_, ?_, fun i => ?_, fun i => ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, fun i => ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [TokW, TokQ, CurOk, DAfter, RFOk, hw, hr, h1, h2, h3, hp, hc, hx]
       first
        | exact hI.wK | exact hI.wS | exact hI.wbusy | exact hI.wcur | exact hI.wdone
        | exact hI.wq | exact hI.tokW i | exact hI.fstr i | exact hI.chR | exact hI.rq
        | exact hI.rbusy | exact hI.rbest | exact hI.rval | exact hI.rmax | exact hI.tokQ i
        | exact hI.rcur | exact hI.rf | exact hI.other)

/-- Frame lemma for steps that change only server states and channels: the writer/reader
parts carry over, the channel-dependent fields are supplied. -/
theorem inv_frame2 {C C' : Cfg n B} {α : Hist n B} (hI : Inv qs C α)
    (hw : ws C' = ws C) (hr : rs C' = rs C) (hp : C'.pend = C.pend)
    (tokW : ∀ i, TokW C' α i)
    (fstr : ∀ i, (rs C').got i ++ Fbits (C'.chan (.srv i) .rd) ++ (ss C' i).1.toList =
      (S α).take (xW C' i))
    (chR : ∀ i, ∀ m ∈ C'.chan (.srv i) .rd, (∃ b, m = .F b) ∨ m = .D)
    (tokQ : ∀ i, TokQ C' i) (rcur : (rs C').busy = true → CurOk qs C' α)
    (other : ∀ a b, ¬ OkPair a b → C'.chan a b = []) : Inv qs C' α := by
  refine ⟨hI.wops, ?_, ?_, ?_, ?_, hI.wresp, ?_, ?_, tokW, fstr, chR, ?_, ?_, ?_, ?_, ?_,
    tokQ, rcur, ?_, other⟩
  all_goals simp only [RFOk, hw, hr, hp]
  · exact hI.wK
  · exact hI.wS
  · exact hI.wbusy
  · exact hI.wcur
  · exact hI.wdone
  · exact hI.wq
  · exact hI.rq
  · exact hI.rbusy
  · exact hI.rbest
  · exact hI.rval
  · exact hI.rmax
  · exact hI.rf

/-! ### Basic facts -/

lemma xW_le (hI : Inv qs C α) (i : Fin n) : xW C i ≤ (S α).length := by
  obtain ⟨h1, h2, h3, -, h⟩ := hI.tokW i
  rcases h with ⟨h4, h5, -⟩ | ⟨h4, h5, -⟩ | ⟨h4, h5, -⟩ | ⟨h4, h5, -⟩ <;> omega

lemma length_fstr (hI : Inv qs C α) (i : Fin n) :
    ((rs C).got i).length + (Fbits (C.chan (.srv i) .rd)).length + (ss C i).1.toList.length =
      xW C i := by
  have h := congrArg List.length (hI.fstr i)
  simp only [List.length_append, List.length_take] at h
  rw [h]; exact min_eq_left (xW_le qs hI i)

/-- Every acknowledged bit has been forwarded. -/
lemma ackc_le_fw (hI : Inv qs C α) (i : Fin n) :
    (ws C).ackc i ≤ ((rs C).got i).length + (Fbits (C.chan (.srv i) .rd)).length := by
  have hl := length_fstr qs hI i
  obtain ⟨-, -, -, -, h⟩ := hI.tokW i
  rcases h with ⟨-, h5, -, h7, -⟩ | ⟨-, h5, -, h7, -⟩ | ⟨-, h5, -⟩ | ⟨-, h5, -, h7, -⟩
  · rw [h7] at hl; simp at hl; omega
  · rw [h7] at hl; simp at hl; omega
  · have : (ss C i).1.toList.length ≤ 1 := by cases (ss C i).1 <;> simp
    omega
  · rw [h7] at hl; simp at hl; omega

lemma apply_noop' (C : Cfg n B) (p : Node n) :
    C.apply p (C.loc p, [], none) = (C, []) := by
  rcases C with ⟨loc, pend, chan, sent, dlv⟩
  simp only [Config.apply, Function.update_eq_self, Prod.mk.injEq]
  refine ⟨?_, by simp [respOut]⟩
  have h1 : Function.update pend p (pendAfter (pend p) none) = pend := by
    have : pendAfter (pend p) none = pend p := by cases pend p <;> rfl
    rw [this, Function.update_eq_self]
  simp [h1, msgsTo]

lemma step_deliver_eq (C : Cfg n B) {a b : Node n} {m : Msg} {rest : List Msg}
    (hc : C.chan a b = m :: rest) :
    (alg qs).step C (.deliver a b) =
      (C.pop a b rest).apply b (handle qs b (.recv a m) (C.loc b)) := by
  simp [Algorithm.step, hc, alg]

lemma Fbits_append (l l' : List Msg) : Fbits (l ++ l') = Fbits l ++ Fbits l' := by
  simp [Fbits, List.filterMap_append]

lemma DAfter.append_F {k g : ℕ} {l : List Msg} (h : DAfter k g l) (b : Bool) :
    DAfter k g (l ++ [.F b]) := by
  intro pos hpos
  rcases Nat.lt_or_ge pos l.length with hp | hp
  · rw [List.getElem?_append_left hp] at hpos
    rw [List.take_append_of_le_length hp.le]; exact h pos hpos
  · rw [List.getElem?_append_right hp] at hpos
    rcases hq : pos - l.length with _ | k'
    · rw [hq] at hpos; simp at hpos
    · rw [hq] at hpos; simp at hpos

lemma DAfter.append_D {k g : ℕ} {l : List Msg} (h : DAfter k g l)
    (hk : k ≤ g + (Fbits l).length) : DAfter k g (l ++ [.D]) := by
  intro pos hpos
  rcases Nat.lt_or_ge pos l.length with hp | hp
  · rw [List.getElem?_append_left hp] at hpos
    rw [List.take_append_of_le_length hp.le]; exact h pos hpos
  · rw [List.getElem?_append_right hp] at hpos
    rcases hq : pos - l.length with _ | k'
    · have : pos = l.length := by omega
      subst this
      rw [List.take_append_of_le_length le_rfl, List.take_length]; exact hk
    · rw [hq] at hpos; simp at hpos

lemma nD_append_F (l : List Msg) (b : Bool) : nD (l ++ [.F b]) = nD l := by
  simp [nD, List.count_append]

lemma nD_append_D (l : List Msg) : nD (l ++ [.D]) = nD l + 1 := by
  simp [nD, List.count_append]

/-! ### Congruence of the tokens -/

lemma TokW_congr {C C' : Cfg n B} {α : Hist n B} {i : Fin n} (hw : ws C' = ws C)
    (hx : xW C' i = xW C i) (h1 : C'.chan .wr (.srv i) = C.chan .wr (.srv i))
    (h2 : C'.chan (.srv i) .wr = C.chan (.srv i) .wr) (h3 : (ss C' i).1 = (ss C i).1)
    (h4 : (ss C' i).2.1 = (ss C i).2.1) (h : TokW C α i) : TokW C' α i := by
  unfold TokW at *; rw [hw, hx, h1, h2, h3, h4]; exact h

lemma TokQ_congr2 {C C' : Cfg n B} {i : Fin n} (hr1 : (rs C').sentAt i = (rs C).sentAt i)
    (hr2 : (rs C').q = (rs C).q)
    (h1 : C'.chan .rd (.srv i) = C.chan .rd (.srv i))
    (h2 : nD (C'.chan (.srv i) .rd) = nD (C.chan (.srv i) .rd))
    (h3 : (ss C' i).2.2.1 = (ss C i).2.2.1) (h : TokQ C i) : TokQ C' i := by
  unfold TokQ at *; rw [hr1, hr2, h1, h2, h3]; exact h

lemma DAfter.tail_F {k g : ℕ} {b : Bool} {l : List Msg} (h : DAfter k g (.F b :: l)) :
    DAfter k (g + 1) l := by
  intro pos hpos
  have := h (pos + 1) (by simpa using hpos)
  simp only [List.take_succ_cons, Fbits, List.filterMap_cons] at this
  simp only [Fbits]; simpa [Nat.add_assoc, Nat.add_comm 1] using this

lemma TokQ_congr {C C' : Cfg n B} {i : Fin n} (hr : rs C' = rs C)
    (h1 : C'.chan .rd (.srv i) = C.chan .rd (.srv i))
    (h2 : nD (C'.chan (.srv i) .rd) = nD (C.chan (.srv i) .rd))
    (h3 : (ss C' i).2.2.1 = (ss C i).2.2.1) (h : TokQ C i) : TokQ C' i := by
  unfold TokQ at *; rw [hr, h1, h2, h3]; exact h

/-! ### Spontaneous steps of a server -/

section SrvStep

variable {C' : Cfg n B} {i : Fin n} {outR outW : List Msg}

/-- Common hypotheses: a step of server `i` that changes only its state and appends `outR`,
`outW` to its channels to the reader and to the writer. -/
structure SrvStep (C C' : Cfg n B) (i : Fin n) (outR outW : List Msg) : Prop where
  hw : ws C' = ws C
  hr : rs C' = rs C
  hp : C'.pend = C.pend
  hx : ∀ j, xW C' j = xW C j
  hs : ∀ j, j ≠ i → ss C' j = ss C j
  hch : ∀ x y, C'.chan x y = C.chan x y ++
    (if x = .srv i ∧ y = .rd then outR else []) ++ (if x = .srv i ∧ y = .wr then outW else [])

lemma SrvStep.chan_rd (h : SrvStep C C' i outR outW) (j : Fin n) :
    C'.chan (.srv j) .rd = C.chan (.srv j) .rd ++ (if j = i then outR else []) := by
  rw [h.hch]; by_cases hj : j = i <;> simp [hj]

lemma SrvStep.chan_wr (h : SrvStep C C' i outR outW) (j : Fin n) :
    C'.chan (.srv j) .wr = C.chan (.srv j) .wr ++ (if j = i then outW else []) := by
  rw [h.hch]; by_cases hj : j = i <;> simp [hj]

lemma SrvStep.chan_other (h : SrvStep C C' i outR outW) (x y : Node n)
    (hxy : ¬ ((x = .srv i ∧ y = .rd) ∨ (x = .srv i ∧ y = .wr))) : C'.chan x y = C.chan x y := by
  rw [h.hch]; push Not at hxy
  simp only [List.append_assoc]
  rw [if_neg (fun h' => hxy.1 h'.1 h'.2), if_neg (fun h' => hxy.2 h'.1 h'.2)]; simp

lemma SrvStep.other (hI : Inv qs C α) (h : SrvStep C C' i outR outW) :
    ∀ a b, ¬ OkPair a b → C'.chan a b = [] := by
  intro a b hab
  rw [h.chan_other a b (by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hab trivial)]
  exact hI.other a b hab

/-- A turn-only step. -/
theorem inv_srv_turn (hI : Inv qs C α) (h : SrvStep C C' i [] [])
    (h1 : (ss C' i).1 = (ss C i).1) (h2 : (ss C' i).2.1 = (ss C i).2.1)
    (h3 : (ss C' i).2.2.1 = (ss C i).2.2.1) : Inv qs C' α := by
  refine inv_frame qs hI h.hw h.hr (fun j => ?_) h.hp ?_ h.hx
  · by_cases hj : j = i
    · subst hj; exact ⟨h1, h2, h3⟩
    · rw [h.hs j hj]; exact ⟨rfl, rfl, rfl⟩
  · funext x y; rw [h.hch]; simp

/-- Forwarding the pending bit. -/
theorem inv_srv_F (hI : Inv qs C α) {b : Bool} (h : SrvStep C C' i [.F b] [])
    (hpf : (ss C i).1 = some b) (h1 : (ss C' i).1 = none) (h2 : (ss C' i).2.1 = (ss C i).2.1)
    (h3 : (ss C' i).2.2.1 = (ss C i).2.2.1) : Inv qs C' α := by
  refine inv_frame2 qs hI h.hw h.hr h.hp (fun j => ?_) (fun j => ?_) (fun j m hm => ?_)
    (fun j => ?_) (fun hb => ?_) (h.other qs hI)
  · by_cases hj : j = i
    · subst hj
      have hT := hI.tokW j
      unfold TokW at hT ⊢
      rw [h.hw, h.hx, h.chan_other _ _ (by simp), h.chan_wr, h2, h1]
      simp only [ite_true, List.append_nil]
      obtain ⟨a1, a2, a3, a4, hc⟩ := hT
      refine ⟨a1, a2, a3, a4, ?_⟩
      rcases hc with ⟨-, -, -, h7, -⟩ | ⟨-, -, -, h7, -⟩ | hc | ⟨-, -, -, h7, -⟩
      · rw [hpf] at h7; cases h7
      · rw [hpf] at h7; cases h7
      · exact Or.inr (Or.inr (Or.inl hc))
      · rw [hpf] at h7; cases h7
    · exact TokW_congr h.hw (h.hx j) (h.chan_other _ _ (by simp))
        (by rw [h.chan_wr]; simp [hj]) (by rw [h.hs j hj]) (by rw [h.hs j hj]) (hI.tokW j)
  · rw [h.hr, h.chan_rd, h.hx]
    by_cases hj : j = i
    · subst hj
      have := hI.fstr j
      rw [hpf] at this
      rw [h1]; simpa [Fbits_append, Fbits] using this
    · simp only [hj, ite_false, List.append_nil]; rw [h.hs j hj]; exact hI.fstr j
  · rw [h.chan_rd] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hI.chR j m hm
    · split_ifs at hm <;> simp_all
  · refine TokQ_congr h.hr (h.chan_other _ _ (by simp)) ?_ ?_ (hI.tokQ j)
    · rw [h.chan_rd]; split_ifs <;> simp [nD_append_F]
    · by_cases hj : j = i
      · subst hj; exact h3
      · rw [h.hs j hj]
  · rw [h.hr] at hb
    unfold CurOk; rw [h.hw, h.hr]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    refine ⟨g1, g2, fun hs => ?_⟩
    rw [h.chan_rd]
    split_ifs
    · exact (g3 hs).append_F b
    · simpa using g3 hs

/-- Sending the acknowledgement. -/
theorem inv_srv_A (hI : Inv qs C α) (h : SrvStep C C' i [] [.A])
    (hpf : (ss C i).1 = none) (hpa : (ss C i).2.1 = true) (h1 : (ss C' i).1 = none)
    (h2 : (ss C' i).2.1 = false)
    (h3 : (ss C' i).2.2.1 = (ss C i).2.2.1) : Inv qs C' α := by
  refine inv_frame2 qs hI h.hw h.hr h.hp (fun j => ?_) (fun j => ?_) (fun j m hm => ?_)
    (fun j => ?_) (fun hb => ?_) (h.other qs hI)
  · by_cases hj : j = i
    · subst hj
      have hT := hI.tokW j
      unfold TokW at hT ⊢
      rw [h.hw, h.hx, h.chan_other _ _ (by simp), h.chan_wr, h2, h1]
      simp only [ite_true]
      obtain ⟨a1, a2, a3, a4, hc⟩ := hT
      refine ⟨a1, a2, a3, a4, ?_⟩
      rcases hc with ⟨-, -, -, -, h8, -⟩ | ⟨-, -, -, -, h8, -⟩ | ⟨h5, h6, h7, -, h9⟩ |
        ⟨-, -, -, -, h8, -⟩
      · rw [hpa] at h8; cases h8
      · rw [hpa] at h8; cases h8
      · exact Or.inr (Or.inr (Or.inr ⟨h5, h6, h7, trivial, trivial, by rw [h9]; rfl⟩))
      · rw [hpa] at h8; cases h8
    · exact TokW_congr h.hw (h.hx j) (h.chan_other _ _ (by simp))
        (by rw [h.chan_wr]; simp [hj]) (by rw [h.hs j hj]) (by rw [h.hs j hj]) (hI.tokW j)
  · rw [h.hr, h.chan_rd, h.hx]
    by_cases hj : j = i
    · subst hj
      have := hI.fstr j
      rw [hpf] at this
      rw [h1]; simpa using this
    · simp only [hj, ite_false, List.append_nil]; rw [h.hs j hj]; exact hI.fstr j
  · rw [h.chan_rd] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hI.chR j m hm
    · split_ifs at hm <;> simp_all
  · refine TokQ_congr h.hr (h.chan_other _ _ (by simp)) ?_ ?_ (hI.tokQ j)
    · rw [h.chan_rd]; split_ifs <;> simp
    · by_cases hj : j = i
      · subst hj; exact h3
      · rw [h.hs j hj]
  · rw [h.hr] at hb
    unfold CurOk; rw [h.hw, h.hr]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    refine ⟨g1, g2, fun hs => ?_⟩
    rw [h.chan_rd]
    split_ifs <;> simpa using g3 hs

/-- Sending the answer. -/
theorem inv_srv_D (hI : Inv qs C α) (h : SrvStep C C' i [.D] [])
    (hpd : (ss C i).2.2.1 = true) (h1 : (ss C' i).1 = (ss C i).1)
    (h2 : (ss C' i).2.1 = (ss C i).2.1) (h3 : (ss C' i).2.2.1 = false) : Inv qs C' α := by
  refine inv_frame2 qs hI h.hw h.hr h.hp (fun j => ?_) (fun j => ?_) (fun j m hm => ?_)
    (fun j => ?_) (fun hb => ?_) (h.other qs hI)
  · by_cases hj : j = i
    · subst hj
      exact TokW_congr h.hw (h.hx j) (h.chan_other _ _ (by simp))
        (by rw [h.chan_wr]; simp) h1 h2 (hI.tokW j)
    · exact TokW_congr h.hw (h.hx j) (h.chan_other _ _ (by simp))
        (by rw [h.chan_wr]; simp [hj]) (by rw [h.hs j hj]) (by rw [h.hs j hj]) (hI.tokW j)
  · rw [h.hr, h.chan_rd, h.hx]
    by_cases hj : j = i
    · subst hj
      rw [h1]; simpa [Fbits_append, Fbits] using hI.fstr j
    · simp only [hj, ite_false, List.append_nil]; rw [h.hs j hj]; exact hI.fstr j
  · rw [h.chan_rd] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hI.chR j m hm
    · split_ifs at hm <;> simp_all
  · by_cases hj : j = i
    · subst hj
      have hQ := hI.tokQ j
      unfold TokQ at hQ ⊢
      rw [h.hr, h.chan_other _ _ (by simp), h.chan_rd, h3]
      simp only [ite_true, nD_append_D]
      rcases hQ with ⟨-, -, h8, -⟩ | ⟨k, hk1, hk2, h⟩
      · rw [hpd] at h8; cases h8
      · refine Or.inr ⟨k, hk1, hk2, ?_⟩
        rcases h with ⟨-, h8, -⟩ | ⟨h7, -, h9⟩ | ⟨-, h8, -⟩
        · rw [hpd] at h8; cases h8
        · exact Or.inr (Or.inr ⟨h7, trivial, by rw [h9]⟩)
        · rw [hpd] at h8; cases h8
    · refine TokQ_congr h.hr (h.chan_other _ _ (by simp)) ?_ ?_ (hI.tokQ j)
      · rw [h.chan_rd]; simp [hj]
      · rw [h.hs j hj]
  · rw [h.hr] at hb
    unfold CurOk; rw [h.hw, h.hr]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    refine ⟨g1, g2, fun hs => ?_⟩
    rw [h.chan_rd]
    split_ifs with hji
    · subst hji
      exact (g3 hs).append_D (g1.trans (ackc_le_fw qs hI j))
    · simpa using g3 hs

end SrvStep

lemma tick_srv_facts (C : Cfg n B) (i : Fin n) (c : ℕ) :
    ((alg qs).step C (.tick (.srv i) c)).2 = [] ∧
    SrvStep C ((alg qs).step C (.tick (.srv i) c)).1 i
      (msgsTo (sTick (n := n) (ss C i)).2 .rd) (msgsTo (sTick (n := n) (ss C i)).2 .wr) ∧
    ss ((alg qs).step C (.tick (.srv i) c)).1 i = (sTick (n := n) (ss C i)).1 := by
  have hcl : C.loc (.srv i) = ((C.loc (.srv i)).1, (C.loc (.srv i)).2.1, ss C i) := rfl
  have hstep : (alg qs).step C (.tick (.srv i) c) = C.apply (.srv i)
      (((C.loc (.srv i)).1, (C.loc (.srv i)).2.1, (sTick (n := n) (ss C i)).1),
        (sTick (n := n) (ss C i)).2, none) := by
    simp only [Algorithm.step, alg]; rw [hcl]; rfl
  rw [hstep]
  refine ⟨by simp [Config.apply, respOut], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [ws, Config.apply]
  · simp [rs, Config.apply]
  · funext x; by_cases hx : x = .srv i
    · subst hx; simp [Config.apply, pendAfter]
    · simp [Config.apply, Function.update_of_ne hx]
  · intro j; simp [xW, Config.apply]
  · intro j hj; simp [ss, Config.apply, hj]
  · intro x y
    by_cases hx : x = .srv i
    · subst hx
      rcases y with j | _ | _ <;> simp [Config.apply, msgsTo]
      rcases ss C i with ⟨pf, pa, pd, t⟩
      rcases pf with _ | b <;> rcases pa <;> rcases pd <;> fin_cases t <;> simp [sTick]
    · simp [Config.apply, hx]
  · simp [ss, Config.apply]

theorem inv_tick_srv (hI : Inv qs C α) (i : Fin n) (c : ℕ) :
    Inv qs ((alg qs).step C (.tick (.srv i) c)).1 (α ++ ((alg qs).step C (.tick (.srv i) c)).2) := by
  obtain ⟨hl, h, hsi⟩ := tick_srv_facts qs C i c
  rw [hl, List.append_nil]
  rcases hs : ss C i with ⟨pf, pa, pd, t⟩
  rw [hs] at h hsi
  rcases pf with _ | b <;> rcases pa <;> rcases pd <;> fin_cases t <;>
    simp [sTick, msgsTo] at h hsi
  all_goals first
    | exact inv_srv_turn qs hI h (by simp [hsi, hs]) (by simp [hsi, hs]) (by simp [hsi, hs])
    | exact inv_srv_F qs hI h (by simp [hs]) (by simp [hsi]) (by simp [hsi, hs]) (by simp [hsi, hs])
    | exact inv_srv_A qs hI h (by simp [hs]) (by simp [hs]) (by simp [hsi]) (by simp [hsi])
        (by simp [hsi, hs])
    | exact inv_srv_D qs hI h (by simp [hs]) (by simp [hsi, hs]) (by simp [hsi, hs]) (by simp [hsi])

lemma take_getD {l : List Bool} {a : ℕ} (h : a < l.length) :
    l.take a ++ [l.getD a false] = l.take (a + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]; simp

/-! ### The stream -/

lemma flatten_block (L : List (List Bool)) (hL : ∀ x ∈ L, x.length = B) :
    ∀ t (ht : t < L.length), ((L.flatten).take ((t + 1) * B)).drop (t * B) = L[t] := by
  induction L with
  | nil => intro t ht; simp at ht
  | cons x L ih =>
    intro t ht
    have hx : x.length = B := hL x (by simp)
    have ih' := ih (fun y hy => hL y (by simp [hy]))
    rcases t with _ | t
    · simp [List.take_append_of_le_length (le_of_eq hx.symm), hx]
    · simp only [List.flatten_cons, List.getElem_cons_succ]
      have h1 : (t + 1 + 1) * B = x.length + (t + 1) * B := by rw [hx]; ring
      have h2 : (t + 1) * B = x.length + t * B := by rw [hx]; ring
      rw [h1, List.take_length_add_append, h2, List.drop_length_add_append, ← h2]
      exact ih' t (by simpa using ht)

lemma S_eq (α : Hist n B) : S α = ((opsOf α .wr).map opBits).flatten := by
  simp [S, List.flatMap]

lemma length_opBits {o : RWOp (Val B)} (h : ∃ v, o = .write v) : (opBits o).length = B := by
  obtain ⟨v, rfl⟩ := h; simp [opBits]

lemma S_length (hI : Inv qs C α) : (S α).length = K α * B := by
  rw [S_eq, List.length_flatten, List.map_map]
  have : ∀ o ∈ opsOf α .wr, (List.length ∘ opBits) o = B :=
    fun o ho => length_opBits (hI.wops o ho)
  rw [List.map_congr_left this]; simp [K]

/-- Block `t` (1-based) of the stream decodes to the value of write `t`. -/
lemma decode_block (hI : Inv qs C α) {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ K α) :
    decode (((S α).take (t * B)).drop ((t - 1) * B)) = wv α t := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hlt : t' < (opsOf α .wr).length := by simp [K] at h2; omega
  obtain ⟨v, hv⟩ := hI.wops _ (List.getElem_mem hlt)
  rw [S_eq, Nat.add_sub_cancel, flatten_block _ (by
    intro x hx; obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx; exact length_opBits (hI.wops o ho))
    t' (by simpa using hlt)]
  simp only [List.getElem_map, hv, opBits, decode_bits]
  exact (writeVal_succ (by rw [List.getElem?_eq_getElem hlt, hv])).symm

/-! ### A server receives a message -/

lemma recv_srv_facts (C : Cfg n B) {x : Node n} {i : Fin n} {m : Msg} {rest : List Msg}
    (hc : C.chan x (.srv i) = m :: rest) (s' : SSt)
    (hh : handle qs (.srv i) (.recv x m) (C.loc (.srv i)) =
      (((C.loc (.srv i)).1, (C.loc (.srv i)).2.1, s'), [], none)) :
    ((alg qs).step C (.deliver x (.srv i))).2 = [] ∧
    ws ((alg qs).step C (.deliver x (.srv i))).1 = ws C ∧
    rs ((alg qs).step C (.deliver x (.srv i))).1 = rs C ∧
    ((alg qs).step C (.deliver x (.srv i))).1.pend = C.pend ∧
    (∀ j, ss ((alg qs).step C (.deliver x (.srv i))).1 j = if j = i then s' else ss C j) ∧
    (∀ a b, ((alg qs).step C (.deliver x (.srv i))).1.chan a b =
      if a = x ∧ b = .srv i then rest else C.chan a b) ∧
    (∀ a b, ((alg qs).step C (.deliver x (.srv i))).1.dlv a b =
      if a = x ∧ b = .srv i then C.dlv a b + 1 else C.dlv a b) := by
  rw [step_deliver_eq qs C hc, hh]
  refine ⟨by simp [Config.apply, respOut], by simp [ws, Config.apply, Config.pop],
    by simp [rs, Config.apply, Config.pop], ?_, fun j => ?_, fun a b => ?_, fun a b => ?_⟩
  · funext y; by_cases hy : y = .srv i
    · subst hy; simp [Config.apply, Config.pop, pendAfter]
    · simp [Config.apply, Config.pop, Function.update_of_ne hy]
  · by_cases hj : j = i
    · subst hj; simp [ss, Config.apply]
    · simp [ss, Config.apply, Config.pop, hj]
  · by_cases ha : a = .srv i
    · subst ha; simp [Config.apply, Config.pop, msgsTo]
    · simp [Config.apply, Config.pop, ha]
  · simp [Config.apply, Config.pop]

theorem inv_recv_W (hI : Inv qs C α) {i : Fin n} {b : Bool} {rest : List Msg}
    (hc : C.chan .wr (.srv i) = .W b :: rest) :
    Inv qs ((alg qs).step C (.deliver .wr (.srv i))).1
      (α ++ ((alg qs).step C (.deliver .wr (.srv i))).2) := by
  obtain ⟨a1, a2, a3, a4, hT⟩ := hI.tokW i
  -- the token is the bit in transit
  obtain ⟨hsc, hxa, hch, hpf, hpa, hcA⟩ : (ws C).sentc i = (ws C).ackc i + 1 ∧
      xW C i = (ws C).ackc i ∧ C.chan .wr (.srv i) = [.W ((S α).getD ((ws C).ackc i) false)] ∧
      (ss C i).1 = none ∧ (ss C i).2.1 = false ∧ C.chan (.srv i) .wr = [] := by
    rcases hT with ⟨-, -, h, -⟩ | h | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
    · rw [h] at hc; cases hc
    · exact h
    · rw [h] at hc; cases hc
    · rw [h] at hc; cases hc
  rw [hch] at hc
  simp only [List.cons.injEq, Msg.W.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  set s' : SSt := (some ((S α).getD ((ws C).ackc i) false), true, (ss C i).2.2)
  obtain ⟨hl, hw, hr, hp, hs, hchan, hdlv⟩ := recv_srv_facts qs C hch s' rfl
  rw [hl, List.append_nil]
  set C' := ((alg qs).step C (.deliver .wr (.srv i))).1
  have hx : ∀ j, xW C' j = if j = i then xW C i + 1 else xW C j := by
    intro j; simp only [xW, hdlv]; by_cases hj : j = i <;> simp [hj]
  have hlt : (ws C).ackc i < (S α).length := by omega
  refine inv_frame2 qs hI hw hr hp (fun j => ?_) (fun j => ?_) (fun j m hm => ?_)
    (fun j => ?_) (fun hb => ?_) (fun x y hxy => ?_)
  · by_cases hj : j = i
    · subst hj
      have e1 : xW C' j = (ws C).ackc j + 1 := by rw [hx]; simp [hxa]
      have e2 : C'.chan .wr (.srv j) = [] := by rw [hchan]; simp
      have e3 : C'.chan (.srv j) .wr = [] := by rw [hchan]; simp [hcA]
      have e4 : (ss C' j).2.1 = true := by rw [hs]; simp [s']
      unfold TokW
      rw [hw, e1, e2, e3, e4]
      exact ⟨a1, a2, a3, a4, Or.inr (Or.inr (Or.inl ⟨hsc, rfl, rfl, rfl, rfl⟩))⟩
    · exact TokW_congr hw (by rw [hx]; simp [hj]) (by rw [hchan]; simp [hj])
        (by rw [hchan]; simp) (by rw [hs]; simp [hj]) (by rw [hs]; simp [hj]) (hI.tokW j)
  · rw [hr, hchan, hx, hs]
    simp only [reduceCtorEq, false_and, ite_false]
    by_cases hj : j = i
    · subst hj
      simp only [ite_true, s', Option.toList_some]
      have h := hI.fstr j
      rw [hpf, Option.toList_none, List.append_nil] at h
      rw [h, hxa]
      exact take_getD hlt
    · simp only [hj, ite_false]; exact hI.fstr j
  · rw [hchan] at hm; simp at hm; exact hI.chR j m hm
  · refine TokQ_congr hr (by rw [hchan]; simp) (by rw [hchan]; simp) ?_ (hI.tokQ j)
    rw [hs]; by_cases hj : j = i
    · subst hj; simp [s']
    · simp [hj]
  · rw [hr] at hb
    unfold CurOk; rw [hw, hr]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    exact ⟨g1, g2, fun h => by rw [hchan]; simpa using g3 h⟩
  · rw [hchan]; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact absurd trivial hxy
    · exact hI.other x y hxy

theorem inv_recv_Q (hI : Inv qs C α) {i : Fin n} {rest : List Msg}
    (hc : C.chan .rd (.srv i) = .Q :: rest) :
    Inv qs ((alg qs).step C (.deliver .rd (.srv i))).1
      (α ++ ((alg qs).step C (.deliver .rd (.srv i))).2) := by
  -- the query token is in transit
  obtain ⟨k, hk1, hk2, hch, hpd, hnD⟩ : ∃ k, (rs C).sentAt i = some k ∧ k ≤ (rs C).q ∧
      C.chan .rd (.srv i) = [.Q] ∧ (ss C i).2.2.1 = false ∧ nD (C.chan (.srv i) .rd) = 0 := by
    rcases hI.tokQ i with ⟨-, h, -⟩ | ⟨k, hk1, hk2, ⟨h, h', h''⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩
    · rw [h] at hc; cases hc
    · exact ⟨k, hk1, hk2, h, h', h''⟩
    · rw [h] at hc; cases hc
    · rw [h] at hc; cases hc
  rw [hch] at hc
  simp only [List.cons.injEq, true_and] at hc
  subst hc
  set s' : SSt := ((ss C i).1, (ss C i).2.1, true, (ss C i).2.2.2)
  obtain ⟨hl, hw, hr, hp, hs, hchan, hdlv⟩ := recv_srv_facts qs C hch s' rfl
  rw [hl, List.append_nil]
  set C' := ((alg qs).step C (.deliver .rd (.srv i))).1
  have hx : ∀ j, xW C' j = xW C j := by intro j; simp [xW, hdlv]
  refine inv_frame2 qs hI hw hr hp (fun j => ?_) (fun j => ?_) (fun j m hm => ?_)
    (fun j => ?_) (fun hb => ?_) (fun x y hxy => ?_)
  · exact TokW_congr hw (hx j) (by rw [hchan]; simp) (by rw [hchan]; simp)
      (by rw [hs]; by_cases hj : j = i <;> simp [hj, s'])
      (by rw [hs]; by_cases hj : j = i <;> simp [hj, s']) (hI.tokW j)
  · rw [hr, hchan, hx, hs]
    simp only [reduceCtorEq, false_and, ite_false]
    by_cases hj : j = i
    · subst hj; simpa [s'] using hI.fstr j
    · simp only [hj, ite_false]; exact hI.fstr j
  · rw [hchan] at hm; simp at hm; exact hI.chR j m hm
  · by_cases hj : j = i
    · subst hj
      unfold TokQ
      rw [hr, hchan, hchan, hs]
      simp only [and_self, ite_true, reduceCtorEq, false_and, ite_false, s']
      exact Or.inr ⟨k, hk1, hk2, Or.inr (Or.inl ⟨trivial, trivial, hnD⟩)⟩
    · refine TokQ_congr hr (by rw [hchan]; simp [hj]) (by rw [hchan]; simp) ?_ (hI.tokQ j)
      rw [hs]; simp [hj]
  · rw [hr] at hb
    unfold CurOk; rw [hw, hr]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    exact ⟨g1, g2, fun h => by rw [hchan]; simpa using g3 h⟩
  · rw [hchan]; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact absurd trivial hxy
    · exact hI.other x y hxy

/-! ### The reader receives a forwarded bit -/

lemma succ_div_of_not_dvd {a b : ℕ} (h : ¬ (a + 1) % b = 0) : (a + 1) / b = a / b := by
  rw [Nat.succ_div, ite_eq_right (fun hd => h (Nat.mod_eq_zero_of_dvd hd))]; simp

section RBit
variable (r : RSt n B) (i : Fin n) (b : Bool)
@[simp] lemma rBit_q : (rBit r i b).q = r.q := by simp only [rBit]; split_ifs <;> rfl
@[simp] lemma rBit_busy : (rBit r i b).busy = r.busy := by simp only [rBit]; split_ifs <;> rfl
@[simp] lemma rBit_resp : (rBit r i b).resp = r.resp := by simp only [rBit]; split_ifs <;> rfl
@[simp] lemma rBit_sentAt : (rBit r i b).sentAt = r.sentAt := by
  simp only [rBit]; split_ifs <;> rfl
@[simp] lemma rBit_got : (rBit r i b).got = Function.update r.got i (r.got i ++ [b]) := by
  simp only [rBit]; split_ifs <;> rfl
lemma rBit_best : (rBit r i b).best =
    if (r.got i ++ [b]).length % B = 0 ∧ r.best < (r.got i ++ [b]).length / B then
      (r.got i ++ [b]).length / B else r.best := by
  simp only [rBit]; split_ifs <;> rfl
lemma rBit_val : (rBit r i b).val =
    if (r.got i ++ [b]).length % B = 0 ∧ r.best < (r.got i ++ [b]).length / B then
      decode ((r.got i ++ [b]).drop ((r.got i ++ [b]).length - B)) else r.val := by
  simp only [rBit]; split_ifs <;> rfl
end RBit

theorem inv_recv_F (hB : 0 < B) (hI : Inv qs C α) {i : Fin n} {b : Bool} {rest : List Msg}
    (hc : C.chan (.srv i) .rd = .F b :: rest) :
    Inv qs ((alg qs).step C (.deliver (.srv i) .rd)).1
      (α ++ ((alg qs).step C (.deliver (.srv i) .rd)).2) := by
  rw [step_deliver_eq qs C hc]
  have hcl : C.loc .rd = ((C.loc .rd).1, rs C, (C.loc .rd).2.2) := rfl
  have hh : handle qs .rd (.recv (.srv i) (.F b)) (C.loc .rd) =
      (((C.loc .rd).1, rBit (rs C) i b, (C.loc .rd).2.2), [], none) := by rw [hcl]; rfl
  rw [hh]
  have hl : ((C.pop (.srv i) .rd rest).apply .rd
      (((C.loc .rd).1, rBit (rs C) i b, (C.loc .rd).2.2), [], none)).2 = [] := by
    simp [Config.apply, respOut]
  rw [hl, List.append_nil]
  set C' := ((C.pop (.srv i) .rd rest).apply .rd
    (((C.loc .rd).1, rBit (rs C) i b, (C.loc .rd).2.2), [], none)).1
  have hw : ws C' = ws C := by simp [C', ws, Config.apply, Config.pop]
  have hr : rs C' = rBit (rs C) i b := by simp [C', rs, Config.apply]
  have hs : ∀ j, ss C' j = ss C j := by intro j; simp [C', ss, Config.apply, Config.pop]
  have hp : C'.pend = C.pend := by
    funext x; by_cases hx : x = .rd
    · subst hx; simp [C', Config.apply, Config.pop, pendAfter]
    · simp [C', Config.apply, Config.pop, Function.update_of_ne hx]
  have hx : ∀ j, xW C' j = xW C j := by intro j; simp [C', xW, Config.apply, Config.pop]
  have hchan : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .rd then rest else C.chan x y := by
    intro x y; by_cases hx : x = .rd
    · subst hx; simp [C', Config.apply, Config.pop, msgsTo]
    · simp [C', Config.apply, Config.pop, hx]
  -- the reader's new state
  have hfs := hI.fstr i
  rw [hc] at hfs
  have hp' : (rs C).got i ++ [b] <+: (S α).take (xW C i) := by
    rw [← hfs]; simp [Fbits, List.append_assoc]
  have hlpre : (rs C).got i ++ [b] = (S α).take ((rs C).got i ++ [b]).length := by
    have hle : ((rs C).got i ++ [b]).length ≤ xW C i :=
      hp'.length_le.trans (List.length_take_le _ _)
    have e := List.prefix_iff_eq_take.1 hp'
    rw [List.take_take, min_eq_left hle] at e; exact e
  have hlS : ((rs C).got i ++ [b]).length ≤ (S α).length := by
    have := congrArg List.length hlpre; rw [List.length_take] at this; omega
  have hSK := S_length qs hI
  have hgot : ∀ j, (rs C').got j = if j = i then (rs C).got i ++ [b] else (rs C).got j := by
    intro j; rw [hr, rBit_got]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, hj]
  have hbest : (rs C).best ≤ (rs C').best := by
    rw [hr, rBit_best]; split_ifs with h
    · exact h.2.le
    · exact le_rfl
  have hq : (rs C').q = (rs C).q := by rw [hr, rBit_q]
  have hbusy : (rs C').busy = (rs C).busy := by rw [hr, rBit_busy]
  have hresp : (rs C').resp = (rs C).resp := by rw [hr, rBit_resp]
  have hsent : (rs C').sentAt = (rs C).sentAt := by rw [hr, rBit_sentAt]
  have hnD : nD (C'.chan (.srv i) .rd) = nD (C.chan (.srv i) .rd) := by
    rw [hchan, hc]; simp [nD]
  refine ⟨hI.wops, by rw [hw]; exact hI.wK, by rw [hw]; exact hI.wS, by rw [hw, hp]; exact hI.wbusy,
    by rw [hw]; exact hI.wcur, hI.wresp, by rw [hw]; exact hI.wdone, by rw [hw]; exact hI.wq,
    fun j => ?_, fun j => ?_, fun j m hm => ?_, by rw [hq]; exact hI.rq,
    by rw [hbusy, hp]; exact hI.rbusy, ?_, ?_, fun j => ?_, fun j => ?_, fun hb => ?_, ?_,
    fun x y hxy => ?_⟩
  · exact TokW_congr hw (hx j) (by rw [hchan]; simp) (by rw [hchan]; simp) (by rw [hs])
      (by rw [hs]) (hI.tokW j)
  · rw [hgot, hchan, hx, hs]
    by_cases hj : j = i
    · subst hj
      simpa [Fbits, List.append_assoc] using hfs
    · simp [hj, hI.fstr j]
  · rw [hchan] at hm
    split_ifs at hm with h
    · simp only [Node.srv.injEq, and_true] at h; subst h
      exact hI.chR _ m (by rw [hc]; simp [hm])
    · exact hI.chR j m hm
  · -- best ≤ K
    rw [hr, rBit_best]; split_ifs with h
    · have := Nat.div_le_div_right (c := B) hlS
      rw [hSK, Nat.mul_div_cancel _ hB] at this; exact this
    · exact hI.rbest
  · -- the value of the best block
    rw [hr, rBit_val, rBit_best]; split_ifs with h
    · obtain ⟨hmod, hlt⟩ := h
      set t := ((rs C).got i ++ [b]).length / B with htdef
      have ht : ((rs C).got i ++ [b]).length = t * B :=
        (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm
      have ht1 : 1 ≤ t := by omega
      have htK : t ≤ K α := by
        have := Nat.div_le_div_right (c := B) hlS
        rw [hSK, Nat.mul_div_cancel _ hB] at this; exact this
      rw [← decode_block qs hI ht1 htK]
      have hL : (rs C).got i ++ [b] = (S α).take (t * B) := by rw [← ht]; exact hlpre
      congr 1
      rw [ht, hL, Nat.sub_one_mul]
    · exact hI.rval
  · -- maximality
    rw [hgot]
    split_ifs with hj
    · rw [hr, rBit_best]; split_ifs with h
      · exact le_rfl
      · have hrm := hI.rmax i
        rcases Nat.lt_or_ge (rs C).best (((rs C).got i ++ [b]).length / B) with hlt | hge
        · have hmod : ¬ ((rs C).got i ++ [b]).length % B = 0 := fun hm => h ⟨hm, hlt⟩
          have : ((rs C).got i ++ [b]).length / B = ((rs C).got i).length / B := by
            simp only [List.length_append, List.length_singleton] at hmod ⊢
            exact succ_div_of_not_dvd hmod
          omega
        · exact hge
    · exact (hI.rmax j).trans hbest
  · refine TokQ_congr2 (by rw [hsent]) hq (by rw [hchan]; simp) ?_ (by rw [hs]) (hI.tokQ j)
    by_cases hj : j = i
    · subst hj; exact hnD
    · rw [hchan]; simp [hj]
  · rw [hbusy] at hb
    unfold CurOk; rw [hw, hresp, hq, hsent]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    refine ⟨g1, fun h => (g2 h).trans hbest, fun h => ?_⟩
    rw [hgot, hchan]
    by_cases hji : j = i
    · subst hji
      have := g3 h
      rw [hc] at this
      simpa using this.tail_F
    · simpa [hji] using g3 h
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hrf j hj
    exact ⟨h1, h2.trans hbest, h3⟩
  · rw [hchan]; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact absurd trivial hxy
    · exact hI.other x y hxy

/-! ### The reader receives an answer -/

lemma hist_rd_facts {α β : Hist n B} (hβ : β = [] ∨ ∃ x, β = [.ret .rd x]) :
    (∀ p, opsOf (α ++ β) p = opsOf α p) ∧ respsOf (α ++ β) .wr = respsOf α .wr ∧
    S (α ++ β) = S α ∧ K (α ++ β) = K α ∧ ∀ t, wv (α ++ β) t = wv α t := by
  have hops : ∀ p, opsOf (α ++ β) p = opsOf α p := by
    intro p
    have : opsOf β p = [] := by
      rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [opsOf, Label.invOf]
    simp [this]
  have hrw : respsOf (α ++ β) .wr = respsOf α .wr := by
    rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [Label.retOf]
  exact ⟨hops, hrw, by simp [S, hops], by simp [K, hops], fun t => by simp [wv, hops]⟩

/-- Frame lemma for the reader receiving an answer. -/
theorem inv_rd_frame {C C' : Cfg n B} {α : Hist n B} (hI : Inv qs C α) {i : Fin n}
    {rest out : List Msg} (hc : C.chan (.srv i) .rd = .D :: rest) (β : Hist n B)
    (hβ : β = [] ∨ ∃ x, β = [.ret .rd x]) (hw : ws C' = ws C) (hs : ∀ j, ss C' j = ss C j)
    (hx : ∀ j, xW C' j = xW C j) (hpw : C'.pend .wr = C.pend .wr)
    (hq : (rs C').q = (rs C).q) (hgot : (rs C').got = (rs C).got)
    (hbest : (rs C').best = (rs C).best) (hval : (rs C').val = (rs C).val)
    (hout : ∀ m ∈ out, m = .Q)
    (hch : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .rd then rest
      else if x = .rd ∧ y = .srv i then C.chan x y ++ out else C.chan x y)
    (rbusy : (rs C').busy = true ↔ C'.pend .rd ≠ none)
    (tokQ : ∀ j, TokQ C' j)
    (rcur : (rs C').busy = true → CurOk qs C' (α ++ β))
    (rf : ∃ rf, RFOk C' (α ++ β) rf) :
    Inv qs C' (α ++ β) := by
  obtain ⟨hops, hrw, hS, hK, hwv⟩ := hist_rd_facts (α := α) hβ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j => ?_, fun j => ?_, fun j m hm => ?_, ?_, rbusy,
    ?_, ?_, ?_, tokQ, rcur, rf, fun x y hxy => ?_⟩
  · rw [hops]; exact hI.wops
  · rw [hw, hK]; exact hI.wK
  · rw [hw, hS]; exact hI.wS
  · rw [hw, hpw]; exact hI.wbusy
  · rw [hw, hK, hwv]; exact hI.wcur
  · intro k hk; rw [hrw] at hk
    simp only [respOf, hrw, hwv]; exact hI.wresp k hk
  · rw [hw, hS]; exact hI.wdone
  · rw [hw, hrw]; exact hI.wq
  · have := hI.tokW j
    unfold TokW at this ⊢
    rw [hw, hx, hS, hch, hch, hs]; simpa using this
  · rw [hgot, hch, hx, hs, hS]
    by_cases hj : j = i
    · subst hj
      have := hI.fstr j
      rw [hc] at this
      simpa [Fbits] using this
    · simp [hj, hI.fstr j]
  · rw [hch] at hm
    simp only [reduceCtorEq, false_and, ite_false] at hm
    split_ifs at hm with h1
    · simp only [Node.srv.injEq, and_true] at h1; subst h1
      exact hI.chR _ m (by rw [hc]; simp [hm])
    · exact hI.chR j m hm
  · rw [hq, hops]; exact hI.rq
  · rw [hbest, hK]; exact hI.rbest
  · rw [hval, hbest, hwv]; exact hI.rval
  · intro j; rw [hgot, hbest]; exact hI.rmax j
  · rw [hch]
    have := hI.other x y hxy
    split_ifs with h1 h2
    · obtain ⟨rfl, rfl⟩ := h1; exact absurd trivial hxy
    · obtain ⟨rfl, rfl⟩ := h2; exact absurd trivial hxy
    · exact this

lemma le_best_of_DAfter (hB : 0 < B) (hI : Inv qs C α) {i : Fin n} {rest : List Msg}
    {k : ℕ} (hc : C.chan (.srv i) .rd = .D :: rest)
    (h : DAfter (k * B) ((rs C).got i).length (C.chan (.srv i) .rd)) : k ≤ (rs C).best := by
  have := h 0 (by rw [hc]; rfl)
  simp [Fbits] at this
  exact ((Nat.le_div_iff_mul_le hB).2 this).trans (hI.rmax i)

theorem inv_recv_D (hB : 0 < B) (hq2 : n < 2 * qs) (hI : Inv qs C α) (hacc : Acc α C)
    {i : Fin n} {rest : List Msg} (hc : C.chan (.srv i) .rd = .D :: rest) :
    Inv qs ((alg qs).step C (.deliver (.srv i) .rd)).1
      (α ++ ((alg qs).step C (.deliver (.srv i) .rd)).2) := by
  rw [step_deliver_eq qs C hc]
  set r := rs C with hrdef
  have hcl : C.loc .rd = ((C.loc .rd).1, r, (C.loc .rd).2.2) := rfl
  have hh : handle qs .rd (.recv (.srv i) .D) (C.loc .rd) =
      (((C.loc .rd).1, (rAns qs r i).1, (C.loc .rd).2.2), (rAns qs r i).2.1,
        (rAns qs r i).2.2) := by rw [hcl]; rfl
  rw [hh]
  -- the token of server `i`: the answer
  obtain ⟨j0, hj0, hj0q, hQc, hpd, hnD1⟩ : ∃ j0, r.sentAt i = some j0 ∧ j0 ≤ r.q ∧
      C.chan .rd (.srv i) = [] ∧ (ss C i).2.2.1 = false ∧ nD (C.chan (.srv i) .rd) = 1 := by
    have hD : 0 < nD (C.chan (.srv i) .rd) := by rw [hc]; simp [nD]
    rcases hI.tokQ i with ⟨-, -, -, h⟩ | ⟨k, hk1, hk2, ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨h1, h2, h3⟩⟩
    · omega
    · omega
    · omega
    · exact ⟨k, hk1, hk2, h1, h2, h3⟩
  have hnDr : nD rest = 0 := by rw [hc] at hnD1; simpa [nD] using hnD1
  have hnoD : ∀ k, DAfter k 0 rest ∧ ∀ g, DAfter k g rest := by
    intro k
    have : ∀ g, DAfter k g rest := by
      intro g pos hpos
      have : Msg.D ∈ rest := List.mem_of_getElem? hpos
      have := List.count_pos_iff.2 this
      simp [nD] at hnDr; omega
    exact ⟨this 0, this⟩
  -- the generic post-configuration
  set out := (rAns qs r i).2.1 with hout
  set C' := ((C.pop (.srv i) .rd rest).apply .rd
    (((C.loc .rd).1, (rAns qs r i).1, (C.loc .rd).2.2), out, (rAns qs r i).2.2)).1
  have hw : ws C' = ws C := by simp [C', ws, Config.apply, Config.pop]
  have hr : rs C' = (rAns qs r i).1 := by simp [C', rs, Config.apply]
  have hs : ∀ j, ss C' j = ss C j := by intro j; simp [C', ss, Config.apply, Config.pop]
  have hx : ∀ j, xW C' j = xW C j := by intro j; simp [C', xW, Config.apply, Config.pop]
  have hpw : C'.pend .wr = C.pend .wr := by simp [C', Config.apply, Config.pop]
  have hpr : C'.pend .rd = pendAfter (C.pend .rd) (rAns qs r i).2.2 := by
    simp [C', Config.apply, Config.pop]
  have hlab : ((C.pop (.srv i) .rd rest).apply .rd
      (((C.loc .rd).1, (rAns qs r i).1, (C.loc .rd).2.2), out, (rAns qs r i).2.2)).2 =
      respOut .rd (C.pend .rd) (rAns qs r i).2.2 := by simp [Config.apply, Config.pop]
  rw [hlab]
  have hch : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .rd then rest
      else if x = .rd ∧ y = .srv i then C.chan x y ++ msgsTo out (.srv i) else C.chan x y := by
    intro x y
    by_cases hx : x = .rd
    · subst hx
      by_cases hy : y = .srv i
      · subst hy; simp [C', Config.apply, Config.pop]
      · simp [C', Config.apply, Config.pop, hy]
        simp only [hout, rAns]; split_ifs <;> simp [msgsTo, Ne.symm hy]
    · simp [C', Config.apply, Config.pop, hx]
  have hmsg : ∀ m ∈ msgsTo out (.srv i), m = .Q := by
    intro m hm; simp only [hout, rAns, msgsTo] at hm; split_ifs at hm <;> simp_all
  have hq : (rs C').q = r.q := by rw [hr]; simp only [rAns]; split_ifs <;> rfl
  have hgot : (rs C').got = r.got := by rw [hr]; simp only [rAns]; split_ifs <;> rfl
  have hbest : (rs C').best = r.best := by rw [hr]; simp only [rAns]; split_ifs <;> rfl
  have hval : (rs C').val = r.val := by rw [hr]; simp only [rAns]; split_ifs <;> rfl
  -- tokens of the other servers are unchanged
  have htokQ_ne : ∀ j, j ≠ i → TokQ C' j := by
    intro j hj
    refine TokQ_congr2 (C := C) ?_ hq (by rw [hch]; simp [hj]) (by rw [hch]; simp [hj])
      (by rw [hs]) (hI.tokQ j)
    rw [hr]; simp only [rAns]; split_ifs <;> simp [Function.update_of_ne hj, r]
  have hsent_ne : ∀ j, j ≠ i → (rs C').sentAt j = r.sentAt j := by
    intro j hj; rw [hr]; simp only [rAns]; split_ifs <;> simp [Function.update_of_ne hj]
  have hchi : C'.chan .rd (.srv i) = msgsTo out (.srv i) := by rw [hch]; simp [hQc]
  have hchr : C'.chan (.srv i) .rd = rest := by rw [hch]; simp
  have hchne : ∀ j, j ≠ i → C'.chan (.srv j) .rd = C.chan (.srv j) .rd := by
    intro j hj; rw [hch]; simp [hj]
  have hssi : (ss C' i).2.2.1 = false := by rw [hs]; exact hpd
  -- RFOk is unchanged when the history and `best` are unchanged
  have hrf0 : (∃ rf, RFOk C' α rf) := by
    obtain ⟨rf, hrf⟩ := hI.rf; exact ⟨rf, by simpa [RFOk, hbest] using hrf⟩
  by_cases hb : r.busy = true
  · obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hI.rbusy.1 hb)
    by_cases hf : r.sentAt i = some r.q
    · have hsi : (rs C').sentAt i = none := by rw [hr]; simp only [rAns, hb, hf]; split_ifs <;> simp
      have hout0 : msgsTo out (.srv i) = [] := by
        simp only [hout, rAns, hb, hf]; split_ifs <;> simp [msgsTo]
      have htokQ : ∀ j, TokQ C' j := by
        intro j
        by_cases hj : j = i
        · subst hj; left
          exact ⟨hsi, by rw [hchi, hout0], hssi, by rw [hchr]; exact hnDr⟩
        · exact htokQ_ne j hj
      -- server `i` (if in `G`) has answered after enough forwarded bits
      obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
      have hi : ∀ G : Finset (Fin n), (∀ k ∈ G, lb * B ≤ (ws C).ackc k ∧
          (k ∈ (rs C).resp → lb ≤ (rs C).best) ∧ ((rs C).sentAt k = some (rs C).q →
            DAfter (lb * B) ((rs C).got k).length (C.chan (.srv k) .rd))) →
          i ∈ G → lb ≤ r.best := fun G hG hiG =>
        le_best_of_DAfter qs hB hI hc ((hG i hiG).2.2 hf)
      by_cases hqc : qs ≤ (insert i r.resp).card
      · -- the read returns
        have hR : (rAns qs r i).2.2 = some r.val := by simp [rAns, hb, hf, hqc]
        have hbusy' : (rs C').busy = false := by rw [hr]; simp [rAns, hb, hf, hqc]
        have hresp' : respOut (P := Node n) (A := register (Val B) (fun _ => false)) Node.rd
            (C.pend .rd) (rAns qs r i).2.2 = [Label.ret Node.rd r.val] := by
          rw [hR, ho]; rfl
        rw [hresp']
        have hlbb : lb ≤ r.best := by
          rcases hG with h0 | ⟨G, hGc, hG⟩
          · omega
          · obtain ⟨k, hk⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
              (Finset.subset_univ G) (Finset.subset_univ (insert i r.resp))
              (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
            rw [Finset.mem_inter] at hk
            rcases Finset.mem_insert.1 hk.2 with rfl | hk2
            · exact hi G hG hk.1
            · exact (hG k hk.1).2.1 hk2
        have hcur : (opsOf α .rd).length = (respsOf α .rd).length + 1 := by
          have := hacc .rd
          simp only [pendCount, ho, Option.isNone_some, Bool.false_eq_true, ite_false] at this
          exact this
        set R := (respsOf α .rd).length
        have hRq : R = r.q - 1 := by rw [hrdef, hI.rq]; omega
        have hbK : r.best ≤ K α := hI.rbest
        refine inv_rd_frame qs hI hc _ (Or.inr ⟨_, rfl⟩) hw hs hx hpw hq hgot hbest hval hmsg hch
          ?_ htokQ (fun h => by rw [hbusy'] at h; cases h) ?_
        · rw [hbusy', hpr, ho, hR]; simp [pendAfter]
        · obtain ⟨rf, hrf⟩ := hI.rf
          obtain ⟨-, -, -, hK, hwv⟩ := hist_rd_facts (α := α) (β := [.ret .rd r.val])
            (Or.inr ⟨_, rfl⟩)
          have hRR : (respsOf (α ++ [.ret .rd r.val]) .rd).length = R + 1 := by simp [R]
          refine ⟨Function.update rf R r.best, fun j hj => ?_⟩
          rw [hRR] at hj
          simp only [hwv, hK, hbest]
          have hprd : ∀ x k, k < (opsOf α .rd).length →
              (Precedes (α ++ [.ret .rd r.val]) x (.rd, k) ↔ Precedes α x (.rd, k)) :=
            fun x k hk => precedes_append_iff_of_invoked hk
          have hpwr : ∀ x k, k < K α →
              (Precedes (α ++ [.ret .rd r.val]) x (.wr, k) ↔ Precedes α x (.wr, k)) :=
            fun x k hk => precedes_append_iff_of_invoked hk
          by_cases hjR : j < R
          · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hjR
            rw [Function.update_of_ne (by omega)]
            refine ⟨by rw [respOf_append_of_completed (show Completed α ((Node.rd : Node n), j)
                from hjR)]; exact h1, h2, h3,
              fun h0 hp => h4 h0 ((hpwr _ _ (by omega)).1 hp),
              fun hp => h5 ((hprd _ _ (by omega)).1 hp), fun j' hj' hjj' => ?_⟩
            rw [hRR] at hj'
            by_cases hj'R : j' = R
            · subst hj'R; rw [Function.update_self]; exact h2
            · rw [Function.update_of_ne hj'R]; exact h6 j' (by omega) hjj'
          · have hjR' : j = R := by omega
            subst hjR'
            rw [Function.update_self]
            refine ⟨?_, le_rfl, hbK, fun h0 hp => ?_, fun hp => ?_, fun j' hj' hjj' => ?_⟩
            · simp only [respOf, respsOf_append, respsOf_cons, respsOf_nil, List.append_nil]
              rw [List.getElem?_append_right le_rfl]
              simp only [Label.retOf, ite_true, List.getElem?_cons_zero, Nat.sub_self,
                Option.toList_some, List.filterMap_cons, List.filterMap_nil, Option.some.injEq]
              exact hI.rval
            · have := ((hpwr _ _ (by omega)).1 hp).completed
              simp [Completed, R] at this
            · rw [hprd _ _ (by omega), hRq] at hp
              have := hlb _ hp
              omega
            · rw [hRR] at hj'
              have : j' = R := by omega
              subst this; rw [Function.update_self]
      · -- the answer is recorded
        have hR : (rAns qs r i).2.2 = none := by simp [rAns, hb, hf, hqc]
        have hbusy' : (rs C').busy = true := by rw [hr]; simp [rAns, hb, hf, hqc]
        have hresp' : (rs C').resp = insert i r.resp := by rw [hr]; simp [rAns, hb, hf, hqc]
        have hresp0 : respOut (P := Node n) (A := register (Val B) (fun _ => false)) Node.rd
            (C.pend .rd) (rAns qs r i).2.2 = [] := by rw [hR, ho]; rfl
        rw [hresp0]
        refine inv_rd_frame qs hI hc _ (Or.inl rfl) hw hs hx hpw hq hgot hbest hval hmsg hch
          ?_ htokQ (fun _ => ?_) (by simpa using hrf0)
        · rw [hbusy', hpr, hR]; simp [pendAfter, ho]
        · unfold CurOk
          rw [List.append_nil, hw, hresp', hq, hgot, hbest]
          refine ⟨by omega, lb, hlb, hG.imp_right ?_⟩
          rintro ⟨G, hGc, hG'⟩
          refine ⟨G, hGc, fun k hk => ?_⟩
          obtain ⟨g1, g2, g3⟩ := hG' k hk
          refine ⟨g1, fun hk' => ?_, fun hs' => ?_⟩
          · rcases Finset.mem_insert.1 hk' with rfl | hk'
            · exact hi G hG' hk
            · exact g2 hk'
          · by_cases hki : k = i
            · subst hki; rw [hsi] at hs'; cases hs'
            · rw [hchne k hki]; exact g3 (by rw [← hsent_ne k hki, hs'])
    · -- a stale answer: query again
      have hsi : (rs C').sentAt i = some r.q := by rw [hr]; simp [rAns, hb, hf]
      have hR : (rAns qs r i).2.2 = none := by simp [rAns, hb, hf]
      have hbusy' : (rs C').busy = true := by rw [hr]; simp [rAns, hb, hf]
      have hresp' : (rs C').resp = r.resp := by rw [hr]; simp [rAns, hb, hf]
      have houtQ : msgsTo out (.srv i) = [.Q] := by simp [hout, rAns, hb, hf, msgsTo]
      have hresp0 : respOut (P := Node n) (A := register (Val B) (fun _ => false)) Node.rd
          (C.pend .rd) (rAns qs r i).2.2 = [] := by rw [hR, ho]; rfl
      rw [hresp0]
      have htokQ : ∀ j, TokQ C' j := by
        intro j
        by_cases hj : j = i
        · subst hj; right
          exact ⟨_, hsi, by rw [hq], Or.inl ⟨by rw [hchi, houtQ], hssi, by rw [hchr]; exact hnDr⟩⟩
        · exact htokQ_ne j hj
      refine inv_rd_frame qs hI hc _ (Or.inl rfl) hw hs hx hpw hq hgot hbest hval hmsg hch
        ?_ htokQ (fun _ => ?_) (by simpa using hrf0)
      · rw [hbusy', hpr, hR]; simp [pendAfter, ho]
      · obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
        unfold CurOk
        rw [List.append_nil, hw, hresp', hq, hgot, hbest]
        refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
        rintro ⟨G, hGc, hG'⟩
        refine ⟨G, hGc, fun k hk => ?_⟩
        obtain ⟨g1, g2, g3⟩ := hG' k hk
        refine ⟨g1, g2, fun hs' => ?_⟩
        by_cases hki : k = i
        · subst hki; rw [hchr]; exact (hnoD _).2 _
        · rw [hchne k hki]; exact g3 (by rw [← hsent_ne k hki, hs'])
  · -- not reading: drop the answer
    have hsi : (rs C').sentAt i = none := by rw [hr]; simp [rAns, hb]
    have hR : (rAns qs r i).2.2 = none := by simp [rAns, hb]
    have hbusy' : (rs C').busy = false := by rw [hr]; simp [rAns, hb]
    have hout0 : msgsTo out (.srv i) = [] := by simp [hout, rAns, hb, msgsTo]
    have hresp0 : respOut (P := Node n) (A := register (Val B) (fun _ => false)) Node.rd
        (C.pend .rd) (rAns qs r i).2.2 = [] := by rw [hR]; cases C.pend .rd <;> rfl
    rw [hresp0]
    have htokQ : ∀ j, TokQ C' j := by
      intro j
      by_cases hj : j = i
      · subst hj; left
        exact ⟨hsi, by rw [hchi, hout0], hssi, by rw [hchr]; exact hnDr⟩
      · exact htokQ_ne j hj
    refine inv_rd_frame qs hI hc _ (Or.inl rfl) hw hs hx hpw hq hgot hbest hval hmsg hch
      ?_ htokQ (fun h => by rw [hbusy'] at h; cases h) (by simpa using hrf0)
    · rw [hbusy', hpr, hR]
      have h2 : C.pend .rd = none := by by_contra h; exact hb (hI.rbusy.2 h)
      simp [pendAfter, h2]

/-! ### The writer receives an acknowledgement -/

lemma hist_wr_facts {α β : Hist n B} (hβ : β = [] ∨ ∃ x, β = [.ret .wr x]) :
    (∀ p, opsOf (α ++ β) p = opsOf α p) ∧ respsOf (α ++ β) .rd = respsOf α .rd ∧
    S (α ++ β) = S α ∧ K (α ++ β) = K α ∧ ∀ t, wv (α ++ β) t = wv α t := by
  have hops : ∀ p, opsOf (α ++ β) p = opsOf α p := by
    intro p
    have : opsOf β p = [] := by
      rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [opsOf, Label.invOf]
    simp [this]
  have hrr : respsOf (α ++ β) .rd = respsOf α .rd := by
    rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [Label.retOf]
  exact ⟨hops, hrr, by simp [S, hops], by simp [K, hops], fun t => by simp [wv, hops]⟩

/-- Frame lemma for the writer receiving an acknowledgement. -/
theorem inv_wr_frame {C C' : Cfg n B} {α : Hist n B} (hI : Inv qs C α) (hacc : Acc α C)
    {i : Fin n} {rest out : List Msg} (hc : C.chan (.srv i) .wr = .A :: rest) (β : Hist n B)
    (hβ : β = [] ∨ ∃ x, β = [.ret .wr x]) (hr : rs C' = rs C) (hs : ∀ j, ss C' j = ss C j)
    (hx : ∀ j, xW C' j = xW C j) (hpr : C'.pend .rd = C.pend .rd)
    (hack : ∀ j, (ws C).ackc j ≤ (ws C').ackc j)
    (hout : ∀ m ∈ out, ∃ b, m = .W b)
    (hch : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .wr then rest
      else if x = .wr ∧ y = .srv i then C.chan x y ++ out else C.chan x y)
    (wK : (ws C').K = K α) (wS : (ws C').strm = S α)
    (wbusy : (ws C').busy = true ↔ C'.pend .wr ≠ none)
    (wcur : (ws C').busy = true → (ws C').cur = wv α (K α))
    (wresp : ∀ j < (respsOf (α ++ β) .wr).length,
      respOf (α ++ β) (.wr, j) = some (wv α (j + 1)))
    (wdone : (ws C').busy = true →
      (Finset.univ.filter fun j => (S α).length ≤ (ws C').ackc j).card < qs)
    (wq : qs ≤ (Finset.univ.filter fun j =>
      (respsOf (α ++ β) .wr).length * B ≤ (ws C').ackc j).card)
    (tokW : ∀ j, TokW C' α j) :
    Inv qs C' (α ++ β) := by
  obtain ⟨hops, hrr, hS, hK, hwv⟩ := hist_wr_facts (α := α) hβ
  have hprd : ∀ x k, k < (opsOf α .rd).length →
      (Precedes (α ++ β) x (.rd, k) ↔ Precedes α x (.rd, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpwr : ∀ x k, k < K α → (Precedes (α ++ β) x (.wr, k) ↔ Precedes α x (.wr, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  refine ⟨by rw [hops]; exact hI.wops, by rw [hK]; exact wK, by rw [hS]; exact wS, wbusy,
    by rw [hK, hwv]; exact wcur, fun j hj => by rw [hwv]; exact wresp j hj,
    by rw [hS]; exact wdone, wq, fun j => by unfold TokW; rw [hS]; exact tokW j,
    fun j => ?_, fun j m hm => ?_, by rw [hr, hops]; exact hI.rq,
    by rw [hr, hpr]; exact hI.rbusy, by rw [hr, hK]; exact hI.rbest,
    by rw [hr, hwv]; exact hI.rval, by rw [hr]; exact hI.rmax, fun j => ?_, fun hb => ?_, ?_,
    fun x y hxy => ?_⟩
  · rw [hr, hch, hx, hs, hS]; simpa using hI.fstr j
  · rw [hch] at hm; simp at hm; exact hI.chR j m hm
  · refine TokQ_congr hr ?_ (by rw [hch]; simp) (by rw [hs]) (hI.tokQ j)
    rw [hch]; simp
  · rw [hr] at hb
    unfold CurOk; rw [hr]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    have hq1 : (rs C).q - 1 < (opsOf α .rd).length := by
      have h1 := hacc .rd
      have h2 : C.pend .rd ≠ none := hI.rbusy.1 hb
      simp only [pendCount, Option.isNone_iff_eq_none, h2, ite_false] at h1
      rw [hI.rq]; omega
    refine ⟨hrc, lb, fun m hm => hlb m ((hprd _ _ hq1).1 hm), hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    exact ⟨g1.trans (hack j), g2, fun h => by rw [hch]; simpa using g3 h⟩
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    rw [hrr] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hj
    have hjinv : j < (opsOf α .rd).length := by
      have h1 : (respsOf α .rd).length ≤ (opsOf α .rd).length := by
        rw [hacc .rd]; exact Nat.le_add_right _ _
      omega
    refine ⟨?_, by rw [hr]; exact h2, by rw [hK]; exact h3,
      fun h0 hp => h4 h0 ((hpwr _ _ (by omega)).1 hp),
      fun hp => h5 ((hprd _ _ hjinv).1 hp), fun j' hj' => h6 j' (by rw [hrr] at hj'; exact hj')⟩
    rw [respOf_append_of_completed (show Completed α ((Node.rd : Node n), j) from hj), hwv]
    exact h1
  · rw [hch]
    have := hI.other x y hxy
    split_ifs with h1 h2
    · obtain ⟨rfl, rfl⟩ := h1; exact absurd trivial hxy
    · obtain ⟨rfl, rfl⟩ := h2; exact absurd trivial hxy
    · exact this

theorem inv_recv_A (hI : Inv qs C α) (hacc : Acc α C) {i : Fin n} {rest : List Msg}
    (hc : C.chan (.srv i) .wr = .A :: rest) :
    Inv qs ((alg qs).step C (.deliver (.srv i) .wr)).1
      (α ++ ((alg qs).step C (.deliver (.srv i) .wr)).2) := by
  rw [step_deliver_eq qs C hc]
  set w := ws C with hwdef
  have hcl : C.loc .wr = (w, (C.loc .wr).2.1, (C.loc .wr).2.2) := rfl
  have hh : handle qs .wr (.recv (.srv i) .A) (C.loc .wr) =
      (((wAck qs w i).1, (C.loc .wr).2.1, (C.loc .wr).2.2), (wAck qs w i).2.1,
        (wAck qs w i).2.2) := by rw [hcl]; rfl
  rw [hh]
  -- the token: the acknowledgement in transit
  obtain ⟨a1, a2, a3, a4, hT⟩ := hI.tokW i
  obtain ⟨hsc, hxa, hW0, hpf, hpa, hA⟩ : w.sentc i = w.ackc i + 1 ∧ xW C i = w.ackc i + 1 ∧
      C.chan .wr (.srv i) = [] ∧ (ss C i).1 = none ∧ (ss C i).2.1 = false ∧
      C.chan (.srv i) .wr = [.A] := by
    rcases hT with ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ | h
    · rw [h] at hc; cases hc
    · rw [h] at hc; cases hc
    · rw [h] at hc; cases hc
    · exact h
  rw [hA] at hc; simp only [List.cons.injEq, true_and] at hc; subst hc
  have hSK := hI.wS
  set C' := ((C.pop (.srv i) .wr []).apply .wr
    (((wAck qs w i).1, (C.loc .wr).2.1, (C.loc .wr).2.2), (wAck qs w i).2.1,
      (wAck qs w i).2.2)).1
  have hw : ws C' = (wAck qs w i).1 := by simp [C', ws, Config.apply]
  have hr : rs C' = rs C := by simp [C', rs, Config.apply, Config.pop]
  have hs : ∀ j, ss C' j = ss C j := by intro j; simp [C', ss, Config.apply, Config.pop]
  have hx : ∀ j, xW C' j = xW C j := by intro j; simp [C', xW, Config.apply, Config.pop]
  have hpr : C'.pend .rd = C.pend .rd := by simp [C', Config.apply, Config.pop]
  have hpw : C'.pend .wr = pendAfter (C.pend .wr) (wAck qs w i).2.2 := by
    simp [C', Config.apply, Config.pop]
  have hlab : ((C.pop (.srv i) .wr []).apply .wr
      (((wAck qs w i).1, (C.loc .wr).2.1, (C.loc .wr).2.2), (wAck qs w i).2.1,
        (wAck qs w i).2.2)).2 = respOut Node.wr (C.pend .wr) (wAck qs w i).2.2 := by
    simp [Config.apply, Config.pop]
  rw [hlab]
  set more := decide (w.ackc i + 1 < w.strm.length) with hmore
  set outW : List Msg := if more then [.W (w.strm.getD (w.ackc i + 1) false)] else []
  have hch : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .wr then []
      else if x = .wr ∧ y = .srv i then C.chan x y ++ outW else C.chan x y := by
    intro x y
    by_cases hx : x = .wr
    · subst hx
      by_cases hy : y = .srv i
      · subst hy; simp [C', Config.apply, Config.pop, wAck, outW, hmore]
        split_ifs <;> simp [msgsTo]
      · simp [C', Config.apply, Config.pop, hy, wAck]
        split_ifs <;> simp [msgsTo, Ne.symm hy]
    · simp [C', Config.apply, Config.pop, hx]
  have hout : ∀ m ∈ outW, ∃ b, m = .W b := by
    intro m hm; simp only [outW] at hm; split_ifs at hm <;> simp_all
  -- the new writer state
  have hK' : (ws C').K = w.K := by rw [hw]; simp only [wAck]; split_ifs <;> rfl
  have hS' : (ws C').strm = w.strm := by rw [hw]; simp only [wAck]; split_ifs <;> rfl
  have hcur' : (ws C').cur = w.cur := by rw [hw]; simp only [wAck]; split_ifs <;> rfl
  have hack' : (ws C').ackc = Function.update w.ackc i (w.ackc i + 1) := by
    rw [hw]; simp only [wAck]; split_ifs <;> rfl
  have hsent' : (ws C').sentc =
      if more then Function.update w.sentc i (w.sentc i + 1) else w.sentc := by
    rw [hw]; simp only [wAck, hmore]; split_ifs <;> rfl
  have hackle : ∀ j, w.ackc j ≤ (ws C').ackc j := by
    intro j; rw [hack']; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have htokW : ∀ j, TokW C' α j := by
    intro j
    by_cases hj : j = i
    · subst hj
      unfold TokW
      rw [hack', hsent', hx, hs]
      have e1 : C'.chan .wr (.srv j) = outW := by rw [hch]; simp [hW0]
      have e2 : C'.chan (.srv j) .wr = [] := by rw [hch]; simp
      rw [e1, e2, hpf, hpa]
      simp only [Function.update_self]
      by_cases hm : w.ackc j + 1 < w.strm.length
      · have hm' : more = true := by simp [hmore, hm]
        simp only [hm', ite_true, Function.update_self, outW]
        rw [hSK] at hm
        refine ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inl ⟨by omega, hxa, ?_, trivial, trivial, trivial⟩)⟩
        rw [hSK]
      · have hm' : more = false := by simp [hmore, hm]
        simp only [hm', Bool.false_eq_true, ite_false, outW]
        rw [hSK] at hm
        refine ⟨by omega, by omega, by omega, fun _ => by omega,
          Or.inl ⟨by omega, hxa, trivial, trivial, trivial, trivial⟩⟩
    · have := hI.tokW j
      unfold TokW at this ⊢
      rw [hack', hsent', hx, hs]
      have e1 : C'.chan .wr (.srv j) = C.chan .wr (.srv j) := by rw [hch]; simp [hj]
      have e2 : C'.chan (.srv j) .wr = C.chan (.srv j) .wr := by rw [hch]; simp [hj]
      rw [e1, e2]
      split_ifs <;> simpa [Function.update_of_ne hj] using this
  by_cases hret : w.busy = true ∧
      qs ≤ (Finset.univ.filter fun j => w.strm.length ≤ (Function.update w.ackc i (w.ackc i + 1)) j).card
  · -- the write returns
    have hR : (wAck qs w i).2.2 = some w.cur := by simp [wAck, hret]
    have hb' : (ws C').busy = false := by rw [hw]; simp [wAck, hret]
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hI.wbusy.1 hret.1)
    have hres : respOut (P := Node n) (A := register (Val B) (fun _ => false)) Node.wr
        (C.pend .wr) (wAck qs w i).2.2 = [Label.ret Node.wr w.cur] := by rw [hR, ho]; rfl
    rw [hres]
    have hKc : K α = (respsOf α .wr).length + 1 := by
      have := hacc .wr
      simp only [pendCount, ho, Option.isNone_some, Bool.false_eq_true, ite_false] at this
      exact this
    have hrw : (respsOf (α ++ [Label.ret Node.wr w.cur]) .wr).length = K α := by simp [hKc]
    refine inv_wr_frame qs hI hacc hA _ (Or.inr ⟨_, rfl⟩) hr hs hx hpr hackle hout hch
      (by rw [hK']; exact hI.wK) (by rw [hS']; exact hI.wS) ?_ (by rw [hb']; simp) ?_ ?_ ?_ htokW
    · rw [hb', hpw, hR, ho]; simp [pendAfter]
    · intro j hj
      rw [hrw] at hj
      by_cases hjc : j < (respsOf α .wr).length
      · rw [respOf_append_of_completed (show Completed α ((Node.wr : Node n), j) from hjc)]
        exact hI.wresp j hjc
      · have hj' : j = (respsOf α .wr).length := by omega
        subst hj'
        simp only [respOf, respsOf_append, respsOf_cons, respsOf_nil, List.append_nil]
        rw [List.getElem?_append_right le_rfl]
        simp only [Label.retOf, ite_true, List.getElem?_cons_zero, Nat.sub_self,
          Option.toList_some, List.filterMap_cons, List.filterMap_nil, Option.some.injEq]
        rw [← hKc]; exact hI.wcur hret.1
    · rw [hb']; intro h; cases h
    · rw [hrw, hack']
      have hSKB := S_length qs hI
      rw [hSK] at hret
      rw [← hSKB]; exact hret.2
  · -- no return
    have hR : (wAck qs w i).2.2 = none := by simp [wAck, hret]
    have hb' : (ws C').busy = w.busy := by rw [hw]; simp [wAck, hret]
    have hres : respOut (P := Node n) (A := register (Val B) (fun _ => false)) Node.wr
        (C.pend .wr) (wAck qs w i).2.2 = [] := by rw [hR]; cases C.pend .wr <;> rfl
    rw [hres]
    refine inv_wr_frame qs hI hacc hA _ (Or.inl rfl) hr hs hx hpr hackle hout hch
      (by rw [hK']; exact hI.wK) (by rw [hS']; exact hI.wS) ?_ ?_ ?_ ?_ ?_ htokW
    · rw [hb', hpw, hR]
      have : pendAfter (C.pend .wr) none = C.pend .wr := by cases C.pend .wr <;> rfl
      rw [this]; exact hI.wbusy
    · rw [hb', hcur']; exact hI.wcur
    · simpa using hI.wresp
    · intro hb; rw [hb'] at hb
      rw [hack', ← hSK]
      exact Nat.lt_of_not_le (fun h => hret ⟨hb, h⟩)
    · simp only [List.append_nil]
      exact hI.wq.trans (Finset.card_le_card (fun j => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => h.trans (hackle j)))

/-! ### Invocations -/

lemma msgsTo_filterMap_aux (p : Fin n → Prop) [DecidablePred p] (m : Fin n → Msg)
    (i : Fin n) (L : List (Fin n)) (hL : L.Nodup) :
    msgsTo (L.filterMap fun j => if p j then some (Node.srv j, m j) else none) (.srv i) =
      if i ∈ L ∧ p i then [m i] else [] := by
  induction L with
  | nil => simp [msgsTo]
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    have ih' := ih hL.2
    simp only [List.filterMap_cons]
    by_cases hpa : p a
    · simp only [hpa, ite_true]
      by_cases hai : a = i
      · subst hai
        simp only [msgsTo, List.filter_cons, decide_true, ite_true, List.map_cons] at ih' ⊢
        rw [ih']; simp [hL.1, hpa]
      · simp only [msgsTo, List.filter_cons, Node.srv.injEq, hai, decide_false,
          Bool.false_eq_true, ite_false] at ih' ⊢
        rw [ih']; simp [Ne.symm hai]
    · simp only [hpa, ite_false]
      rw [ih']
      by_cases hai : a = i
      · subst hai; simp [hpa, hL.1]
      · simp [Ne.symm hai]

lemma msgsTo_filterMap_srv (p : Fin n → Prop) [DecidablePred p] (m : Fin n → Msg) (i : Fin n) :
    msgsTo ((List.finRange n).filterMap fun j => if p j then some (Node.srv j, m j) else none)
      (.srv i) = if p i then [m i] else [] := by
  rw [msgsTo_filterMap_aux p m i _ (List.nodup_finRange n)]; simp

lemma msgsTo_filterMap_cl (p : Fin n → Prop) [DecidablePred p] (m : Fin n → Msg) (x : Node n)
    (hx : ∀ j, x ≠ .srv j) :
    msgsTo ((List.finRange n).filterMap fun j => if p j then some (Node.srv j, m j) else none)
      x = [] := by
  simp only [msgsTo, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_filterMap]
  rintro ⟨y, mm⟩ ⟨j, -, hj⟩
  split_ifs at hj
  simp only [Option.some.injEq, Prod.mk.injEq] at hj; obtain ⟨rfl, -⟩ := hj
  simpa using Ne.symm (hx j)

theorem inv_invoke_wr (hB : 0 < B) (hq0 : 0 < qs) (hI : Inv qs C α) (hacc : Acc α C)
    (hp : C.pend .wr = none) (v : Val B) :
    Inv qs ((alg qs).step C (.invoke .wr (.write v))).1
      (α ++ ((alg qs).step C (.invoke .wr (.write v))).2) := by
  have hcl : C.loc .wr = (ws C, (C.loc .wr).2.1, (C.loc .wr).2.2) := rfl
  have hb : (ws C).busy = false := by
    have := hI.wbusy; simp only [hp, ne_eq, not_true_eq_false, iff_false] at this
    simpa using this
  have hstep : (alg qs).step C (.invoke .wr (.write v)) =
      ((({ C with pend := Function.update C.pend .wr (some (.write v)) } : Cfg n B).apply .wr
        (((wInvoke (ws C) v).1, (C.loc .wr).2.1, (C.loc .wr).2.2), (wInvoke (ws C) v).2, none)).1,
        [.inv .wr (.write v)]) := by
    simp only [Algorithm.step, hp, alg]
    rw [hcl]; simp [handle, Config.apply, respOut]
  rw [hstep]
  set C' := (({ C with pend := Function.update C.pend .wr (some (.write v)) } : Cfg n B).apply
    .wr (((wInvoke (ws C) v).1, (C.loc .wr).2.1, (C.loc .wr).2.2), (wInvoke (ws C) v).2, none)).1
  set α' := α ++ [.inv .wr (.write v)]
  have hcK : (respsOf α .wr).length = K α := by
    have := hacc .wr
    simp only [pendCount, hp, Option.isNone_none, ite_true, add_zero] at this
    exact this.symm
  have hops : opsOf α' .wr = opsOf α .wr ++ [.write v] := by simp [α', Label.invOf]
  have hopsr : opsOf α' .rd = opsOf α .rd := by simp [α', Label.invOf]
  have hK : K α' = K α + 1 := by simp [K, hops]
  have hS : S α' = S α ++ bits v := by simp [S, hops, opBits]
  have hwv : ∀ t, t ≤ K α → wv α' t = wv α t := by
    intro t ht; simp only [wv, hops]; exact writeVal_append_of_le ht
  have hwvK : wv α' (K α + 1) = v := by
    simp only [wv, hops]; exact writeVal_succ (by simp [K])
  have hrw : respsOf α' .wr = respsOf α .wr := by simp [α', Label.retOf]
  have hrr : respsOf α' .rd = respsOf α .rd := by simp [α', Label.retOf]
  have hSK := S_length qs hI
  have hw : ws C' = (wInvoke (ws C) v).1 := by simp [C', ws, Config.apply]
  have hr : rs C' = rs C := by simp [C', rs, Config.apply]
  have hs : ∀ j, ss C' j = ss C j := by intro j; simp [C', ss, Config.apply]
  have hx : ∀ j, xW C' j = xW C j := by intro j; simp [C', xW, Config.apply]
  have hpw : C'.pend .wr = some (.write v) := by simp [C', Config.apply, pendAfter]
  have hpr : C'.pend .rd = C.pend .rd := by simp [C', Config.apply]
  have hchW : ∀ j, C'.chan .wr (.srv j) = C.chan .wr (.srv j) ++
      (if (ws C).sentc j = (ws C).ackc j then [.W (((ws C).strm ++ bits v).getD ((ws C).ackc j) false)] else []) := by
    intro j
    simp only [C', Config.apply, ite_true, wInvoke]
    rw [msgsTo_filterMap_srv (fun j => (ws C).sentc j = (ws C).ackc j)
      (fun j => .W (((ws C).strm ++ bits v).getD ((ws C).ackc j) false)) j]
  have hchO : ∀ x y, (x ≠ .wr ∨ ∀ j, y ≠ .srv j) → C'.chan x y = C.chan x y := by
    intro x y hxy
    rcases hxy with hx' | hy
    · simp [C', Config.apply, hx']
    · simp only [C', Config.apply]
      split_ifs with hx'
      · rw [wInvoke]
        rw [msgsTo_filterMap_cl _ _ y hy, List.append_nil]
      · rfl
  have hprd : ∀ x k, k < (opsOf α .rd).length → (Precedes α' x (.rd, k) ↔ Precedes α x (.rd, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpwr : ∀ x k, k < K α → (Precedes α' x (.wr, k) ↔ Precedes α x (.wr, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hxle : ∀ j, xW C j ≤ (S α).length := fun j => xW_le qs hI j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j => ?_, fun j => ?_, fun j m hm => ?_, ?_, ?_, ?_,
    ?_, ?_, fun j => ?_, fun hb' => ?_, ?_, fun x y hxy => ?_⟩
  · intro o ho; rw [hops] at ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hI.wops o ho
    · simp at ho; exact ⟨v, ho⟩
  · rw [hw, hK]; simp [wInvoke, ← hI.wK]
  · rw [hw, hS]; simp [wInvoke, ← hI.wS]
  · rw [hw, hpw]; simp [wInvoke]
  · rw [hw, hK, hwvK]; simp [wInvoke]
  · intro j hj
    rw [hrw] at hj
    rw [respOf_append_of_completed (show Completed α ((Node.wr : Node n), j) from hj),
      hwv _ (by omega)]
    exact hI.wresp j hj
  · intro _
    rw [hw]
    have : (Finset.univ.filter fun j => (S α').length ≤ (wInvoke (ws C) v).1.ackc j) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_le, wInvoke, hS, List.length_append, length_bits]
      obtain ⟨a1, a2, a3, -⟩ := hI.tokW j
      omega
    rw [this]; simpa using hq0
  · rw [hw, hrw]; simpa [wInvoke] using hI.wq
  · -- the token of server `j`
    obtain ⟨a1, a2, a3, a4, hT⟩ := hI.tokW j
    unfold TokW
    rw [hw, hS, hx, hchW, hs, hchO _ _ (Or.inl (by simp))]
    simp only [wInvoke, List.length_append, length_bits]
    by_cases hid : (ws C).sentc j = (ws C).ackc j
    · have ha : (ws C).ackc j = (S α).length := a4 hid
      simp only [hid, ite_true]
      rcases hT with ⟨-, h5, h6, h7, h8, h9⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
      · refine ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inl ⟨trivial, h5, ?_, h7, h8, h9⟩)⟩
        rw [h6, List.nil_append, ← hI.wS]
      · omega
      · omega
      · omega
    · simp only [hid, ite_false, List.append_nil]
      refine ⟨a1, a2, by omega, by intro h; simp_all, ?_⟩
      rcases hT with h | ⟨h4, h5, h6, h7⟩ | h | h
      · exact absurd h.1 hid
      · refine Or.inr (Or.inl ⟨h4, h5, ?_, h7⟩)
        rw [h6, List.getD_append _ _ _ _ (by omega)]
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · rw [hr, hchO _ _ (Or.inl (by simp)), hx, hs, hS, List.take_append_of_le_length (hxle j)]
    exact hI.fstr j
  · rw [hchO _ _ (Or.inl (by simp))] at hm; exact hI.chR j m hm
  · rw [hr, hopsr]; exact hI.rq
  · rw [hr, hpr]; exact hI.rbusy
  · rw [hr, hK]; exact hI.rbest.trans (Nat.le_succ _)
  · rw [hr, hwv _ hI.rbest]; exact hI.rval
  · rw [hr]; exact hI.rmax
  · refine TokQ_congr hr (hchO _ _ (Or.inl (by simp))) (by rw [hchO _ _ (Or.inl (by simp))])
      (by rw [hs]) (hI.tokQ j)
  · rw [hr] at hb'
    unfold CurOk; rw [hr, hw]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb'
    have hq1 : (rs C).q - 1 < (opsOf α .rd).length := by
      have h1 := hacc .rd
      have h2 : C.pend .rd ≠ none := hI.rbusy.1 hb'
      simp only [pendCount, Option.isNone_iff_eq_none, h2, ite_false] at h1
      rw [hI.rq]; omega
    refine ⟨hrc, lb, fun m hm => hlb m ((hprd _ _ hq1).1 hm), hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    exact ⟨by simpa [wInvoke] using g1, g2, fun h => by
      rw [hchO _ _ (Or.inl (by simp))]; exact g3 h⟩
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    rw [hrr] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hj
    have hjinv : j < (opsOf α .rd).length := by
      have h1 : (respsOf α .rd).length ≤ (opsOf α .rd).length := by
        rw [hacc .rd]; exact Nat.le_add_right _ _
      omega
    refine ⟨?_, by rw [hr]; exact h2, by rw [hK]; omega,
      fun h0 hp => h4 h0 ((hpwr _ _ (by omega)).1 hp),
      fun hp => h5 ((hprd _ _ hjinv).1 hp), fun j' hj' => h6 j' (by rw [hrr] at hj'; exact hj')⟩
    rw [respOf_append_of_completed (show Completed α ((Node.rd : Node n), j) from hj),
      hwv _ h3]
    exact h1
  · have := hI.other x y hxy
    by_cases hxw : x = .wr
    · subst hxw
      rcases y with j | _ | _
      · exact absurd trivial hxy
      · rw [hchO _ _ (Or.inr (by simp))]; exact this
      · rw [hchO _ _ (Or.inr (by simp))]; exact this
    · rw [hchO _ _ (Or.inl hxw)]; exact this

lemma DAfter_of_nD {k g : ℕ} {l : List Msg} (h : nD l = 0) : DAfter k g l := by
  intro pos hpos
  have : Msg.D ∈ l := List.mem_of_getElem? hpos
  have := List.count_pos_iff.2 this
  simp [nD] at h; omega

theorem inv_invoke_rd (hq0 : 0 < qs) (hI : Inv qs C α) (hacc : Acc α C)
    (hp : C.pend .rd = none) :
    Inv qs ((alg qs).step C (.invoke .rd .read)).1
      (α ++ ((alg qs).step C (.invoke .rd .read)).2) := by
  have hcl : C.loc .rd = ((C.loc .rd).1, rs C, (C.loc .rd).2.2) := rfl
  have hstep : (alg qs).step C (.invoke .rd .read) =
      ((({ C with pend := Function.update C.pend .rd (some .read) } : Cfg n B).apply .rd
        (((C.loc .rd).1, (rInvoke (rs C)).1, (C.loc .rd).2.2), (rInvoke (rs C)).2, none)).1,
        [.inv .rd .read]) := by
    simp only [Algorithm.step, hp, alg]
    rw [hcl]; simp [handle, Config.apply, respOut]
  rw [hstep]
  set C' := (({ C with pend := Function.update C.pend .rd (some .read) } : Cfg n B).apply .rd
    (((C.loc .rd).1, (rInvoke (rs C)).1, (C.loc .rd).2.2), (rInvoke (rs C)).2, none)).1
  set α' := α ++ [.inv .rd (.read : RWOp (Val B))]
  have hopsw : opsOf α' .wr = opsOf α .wr := by simp [α', Label.invOf]
  have hopsr : opsOf α' .rd = opsOf α .rd ++ [.read] := by simp [α', Label.invOf]
  have hK : K α' = K α := by simp [K, hopsw]
  have hS : S α' = S α := by simp [S, hopsw]
  have hwv : ∀ t, wv α' t = wv α t := by intro t; simp [wv, hopsw]
  have hrw : respsOf α' .wr = respsOf α .wr := by simp [α', Label.retOf]
  have hrr : respsOf α' .rd = respsOf α .rd := by simp [α', Label.retOf]
  have hw : ws C' = ws C := by simp [C', ws, Config.apply]
  have hr : rs C' = (rInvoke (rs C)).1 := by simp [C', rs, Config.apply]
  have hs : ∀ j, ss C' j = ss C j := by intro j; simp [C', ss, Config.apply]
  have hx : ∀ j, xW C' j = xW C j := by intro j; simp [C', xW, Config.apply]
  have hpw : C'.pend .wr = C.pend .wr := by simp [C', Config.apply]
  have hpr : C'.pend .rd = some .read := by simp [C', Config.apply, pendAfter]
  have hchQ : ∀ j, C'.chan .rd (.srv j) = C.chan .rd (.srv j) ++
      (if (rs C).sentAt j = none then [.Q] else []) := by
    intro j
    simp only [C', Config.apply, ite_true, rInvoke]
    rw [msgsTo_filterMap_srv (fun j => (rs C).sentAt j = none) (fun _ => .Q) j]
  have hchO : ∀ x y, (x ≠ .rd ∨ ∀ j, y ≠ .srv j) → C'.chan x y = C.chan x y := by
    intro x y hxy
    rcases hxy with hx' | hy
    · simp [C', Config.apply, hx']
    · simp only [C', Config.apply]
      split_ifs with hx'
      · rw [rInvoke, msgsTo_filterMap_cl _ _ y hy, List.append_nil]
      · rfl
  have hprd : ∀ x k, k < (opsOf α .rd).length → (Precedes α' x (.rd, k) ↔ Precedes α x (.rd, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpwr : ∀ x k, k < K α → (Precedes α' x (.wr, k) ↔ Precedes α x (.wr, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hrq : (rs C).q = (opsOf α .rd).length := hI.rq
  refine ⟨by rw [hopsw]; exact hI.wops, by rw [hw, hK]; exact hI.wK, by rw [hw, hS]; exact hI.wS,
    by rw [hw, hpw]; exact hI.wbusy, by rw [hw, hK, hwv]; exact hI.wcur, ?_,
    by rw [hw, hS]; exact hI.wdone, by rw [hw, hrw]; exact hI.wq, fun j => ?_, fun j => ?_,
    fun j m hm => ?_, ?_, ?_, ?_, ?_, ?_, fun j => ?_, fun _ => ?_, ?_, fun x y hxy => ?_⟩
  · intro j hj
    rw [hrw] at hj
    rw [respOf_append_of_completed (show Completed α ((Node.wr : Node n), j) from hj), hwv]
    exact hI.wresp j hj
  · have := hI.tokW j
    unfold TokW at this ⊢
    rw [hw, hS, hx, hs, hchO _ _ (Or.inl (by simp)), hchO _ _ (Or.inl (by simp))]
    exact this
  · rw [hr, hchO _ _ (Or.inl (by simp)), hx, hs, hS]; exact hI.fstr j
  · rw [hchO _ _ (Or.inl (by simp))] at hm; exact hI.chR j m hm
  · rw [hr, hopsr]; simp [rInvoke, hrq]
  · rw [hr, hpr]; simp [rInvoke]
  · rw [hr, hK]; exact hI.rbest
  · rw [hr, hwv]; exact hI.rval
  · rw [hr]; exact hI.rmax
  · have hT := hI.tokQ j
    unfold TokQ at hT ⊢
    rw [hr, hchQ, hs, hchO _ _ (Or.inl (by simp))]
    simp only [rInvoke]
    rcases hT with ⟨h1, h2, h3, h4⟩ | ⟨k, h1, h2, h3⟩
    · right
      refine ⟨(rs C).q + 1, by simp [h1], le_rfl, Or.inl ⟨?_, h3, h4⟩⟩
      simp [h1, h2]
    · right
      refine ⟨k, by simp [h1], by omega, ?_⟩
      simpa [h1] using h3
  · unfold CurOk
    rw [hr, hw]
    simp only [rInvoke, Finset.card_empty, Nat.add_sub_cancel, Finset.notMem_empty, false_imp_iff,
      true_and]
    refine ⟨hq0, (respsOf α .wr).length, fun m hm => ?_, Or.inr ?_⟩
    · rw [hrq] at hm
      exact (precedes_append_inv_iff.1 hm)
    · refine ⟨Finset.univ.filter fun k => (respsOf α .wr).length * B ≤ (ws C).ackc k, hI.wq,
        fun k hk => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨hk, fun hsk => ?_⟩
      rw [hchO _ _ (Or.inl (by simp))]
      apply DAfter_of_nD
      rcases hI.tokQ k with ⟨-, -, -, h4⟩ | ⟨k', h1, h2, -⟩
      · exact h4
      · split_ifs at hsk with h0
        · rw [h0] at h1; cases h1
        · rw [h1] at hsk; simp at hsk; omega
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    rw [hrr] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hj
    have hjinv : j < (opsOf α .rd).length := by
      have h1 : (respsOf α .rd).length ≤ (opsOf α .rd).length := by
        rw [hacc .rd]; exact Nat.le_add_right _ _
      omega
    refine ⟨?_, by rw [hr]; exact h2, by rw [hK]; exact h3,
      fun h0 hp => h4 h0 ((hpwr _ _ (by omega)).1 hp),
      fun hp => h5 ((hprd _ _ hjinv).1 hp), fun j' hj' => h6 j' (by rw [hrr] at hj'; exact hj')⟩
    rw [respOf_append_of_completed (show Completed α ((Node.rd : Node n), j) from hj), hwv]
    exact h1
  · have := hI.other x y hxy
    by_cases hxr : x = .rd
    · subst hxr
      rcases y with j | _ | _
      · exact absurd trivial hxy
      · rw [hchO _ _ (Or.inr (by simp))]; exact this
      · rw [hchO _ _ (Or.inr (by simp))]; exact this
    · rw [hchO _ _ (Or.inl hxr)]; exact this

/-! ### The step lemma -/

theorem inv_step (hB : 0 < B) (hq2 : n < 2 * qs) (hI : Inv qs C α) (hacc : Acc α C)
    (e : Event (Node n) (register (Val B) (fun _ => false))) (he : EvOk e) :
    Inv qs ((alg qs).step C e).1 (α ++ ((alg qs).step C e).2) := by
  have hq0 : 0 < qs := by omega
  cases e with
  | invoke p o =>
    rcases hp : C.pend p with _ | o'
    · rcases he p o rfl with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩
      · exact inv_invoke_wr qs hB hq0 hI hacc hp v
      · exact inv_invoke_rd qs hq0 hI hacc hp
    · have : (alg qs).step C (.invoke p o) = (C, []) := by simp [Algorithm.step, hp]
      rw [this, List.append_nil]; exact hI
  | tick p c =>
    rcases p with i | _ | _
    · exact inv_tick_srv qs hI i c
    · have : (alg qs).step C (.tick .wr c) = (C, []) := by
        simp only [Algorithm.step, alg]
        have h := apply_noop' C .wr
        rcases hl : C.loc .wr with ⟨w, r, s⟩
        rw [hl] at h; exact h
      rw [this, List.append_nil]; exact hI
    · have : (alg qs).step C (.tick .rd c) = (C, []) := by
        simp only [Algorithm.step, alg]
        have h := apply_noop' C .rd
        rcases hl : C.loc .rd with ⟨w, r, s⟩
        rw [hl] at h; exact h
      rw [this, List.append_nil]; exact hI
  | deliver a b =>
    rcases hc : C.chan a b with _ | ⟨m, rest⟩
    · have : (alg qs).step C (.deliver a b) = (C, []) := by simp [Algorithm.step, hc]
      rw [this, List.append_nil]; exact hI
    have hne : C.chan a b ≠ [] := by simp [hc]
    have hok : OkPair a b := by by_contra h; exact hne (hI.other a b h)
    rcases a with i | _ | _ <;> rcases b with j | _ | _ <;> simp only [OkPair] at hok
    · -- server → writer: an acknowledgement
      obtain ⟨-, -, -, -, hT⟩ := hI.tokW i
      have : m = .A := by
        rcases hT with ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩
        all_goals rw [h] at hc; simp_all
      subst this; exact inv_recv_A qs hI hacc hc
    · -- server → reader
      rcases hI.chR i m (by rw [hc]; simp) with ⟨b, rfl⟩ | rfl
      · exact inv_recv_F qs hB hI hc
      · exact inv_recv_D qs hB hq2 hI hacc hc
    · -- writer → server
      obtain ⟨-, -, -, -, hT⟩ := hI.tokW j
      obtain ⟨b, rfl⟩ : ∃ b, m = .W b := by
        rcases hT with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
        all_goals rw [h] at hc
        all_goals simp only [List.cons.injEq, reduceCtorEq] at hc
        exact ⟨_, hc.1.symm⟩
      exact inv_recv_W qs hI hc
    · -- reader → server
      have : m = .Q := by
        rcases hI.tokQ j with ⟨-, h, -⟩ | ⟨k, -, -, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩
        all_goals rw [h] at hc; simp_all
      subst this; exact inv_recv_Q qs hI hc

/-- The invariant holds in every reachable configuration (SWSR environment). -/
theorem inv_reach (hq2 : n < 2 * qs) (hqn : qs ≤ n) (hB : 0 < B)
    (E : List (Event (Node n) (register (Val B) (fun _ => false)))) (hE : ∀ e ∈ E, EvOk e) :
    Inv qs ((alg qs).run (alg qs).initCfg E) ((alg qs).hist (alg qs).initCfg E) := by
  induction E using List.reverseRecOn with
  | nil => exact inv_init qs hqn
  | append_singleton E e ih =>
    have ih' := ih (fun e' he' => hE e' (by simp [he']))
    rw [Algorithm.run_append, Algorithm.hist_append]
    have := inv_step qs hB hq2 ih' (acc_hist _ E) e (hE e (by simp))
    simpa [Algorithm.hist] using this


/-! ### Atomicity and regularity -/

theorem readsFrom (hq2 : n < 2 * qs) (hqn : qs ≤ n) (hB : 0 < B)
    (E : List (Event (Node n) (register (Val B) (fun _ => false)))) (hE : ∀ e ∈ E, EvOk e) :
    ∃ rf, SWSRReadsFrom ((alg qs).hist (alg qs).initCfg E) Node.wr Node.rd rf := by
  have hI := inv_reach qs hq2 hqn hB E hE
  obtain ⟨rf, hrf⟩ := hI.rf
  refine ⟨rf, ⟨by simp, wellFormed_hist _ E, fun p o ho => ?_, fun j v x hop hres => ?_,
    fun k hk => (hrf k hk).1, fun k hk => (hrf k hk).2.2.2.1, fun k hk => (hrf k hk).2.2.2.2.1,
    fun k k' hkk' hk' _ => (hrf k (by omega)).2.2.2.2.2 k' hk' hkk'.le⟩⟩
  · exact hE _ (mem_opsOf_hist _ ho) p o rfl
  · have hj : j < (respsOf ((alg qs).hist (alg qs).initCfg E) .wr).length := by
      by_contra h; simp [respOf, List.getElem?_eq_none (not_lt.1 h)] at hres
    rw [hI.wresp j hj] at hres
    simp only [Option.some.injEq] at hres
    rw [← hres]
    exact writeVal_succ hop

/-- **The streaming relay is atomic** (for `qs ≤ n < 2 qs`, `B > 0`). -/
theorem isAtomic (hq2 : n < 2 * qs) (hqn : qs ≤ n) (hB : 0 < B) :
    IsAtomic (alg (n := n) (B := B) qs) := by
  intro E hE
  obtain ⟨rf, h⟩ := readsFrom qs hq2 hqn hB E hE
  exact ⟨_, h.isLinearization⟩

/-- **The streaming relay is regular.** -/
theorem isRegular (hq2 : n < 2 * qs) (hqn : qs ≤ n) (hB : 0 < B) :
    IsRegular (alg (n := n) (B := B) qs) := by
  intro E hE k hk
  obtain ⟨rf, h⟩ := readsFrom qs hq2 hqn hB E hE
  exact ⟨rf k, h.read_val k hk, h.not_future k hk, h.not_overwritten k hk⟩

end Podc.StorageCost.Stream
