import Papers.PODC2021.StabilizingLEDynamic.LE.Defs

/-!
# Algorithm `LE`: local properties of one round

Characterizations of the state after one round `roundLE me s mb`, for every processing order
`mb` of the received records (Remark 4 and the local facts used in Lemmas 2–7).
-/

namespace StabilizingLEDynamic.LE

open Classical

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ}

/-! ### The loop acts componentwise -/

theorem foldl_body (me : ι) (mb : List (Rcd ι Δ)) (M : Finset (Rcd ι Δ)) (L G : MapT ι Δ) :
    mb.foldl (body me) (M, L, G) =
      (mb.foldl (bodyM me) M, mb.foldl (bodyL me) L, mb.foldl (bodyG me) G) := by
  induction mb generalizing M L G with
  | nil => rfl
  | cons r mb ih => simp only [List.foldl_cons]; exact ih _ _ _

theorem loop_eq (me : ι) (mb : List (Rcd ι Δ)) (s : St ι Δ) :
    loop me mb s = (mb.foldl (bodyM me) s.msgs, mb.foldl (bodyL me) (decAll me (initL me s.L)),
      mb.foldl (bodyG me) (decAll me (initG me (initL me s.L) s.G))) :=
  foldl_body _ _ _ _ _

/-! ### `msgs` part of the loop -/

theorem subset_foldl_bodyM (me : ι) (mb : List (Rcd ι Δ)) (M : Finset (Rcd ι Δ)) :
    M ⊆ mb.foldl (bodyM me) M := by
  induction mb generalizing M with
  | nil => exact le_rfl
  | cons r mb ih =>
    refine subset_trans ?_ (ih _)
    unfold bodyM; split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl

theorem mem_foldl_bodyM {me : ι} {mb : List (Rcd ι Δ)} {M : Finset (Rcd ι Δ)} {r : Rcd ι Δ}
    (h : r ∈ mb.foldl (bodyM me) M) : r ∈ M ∨ (r ∈ mb ∧ r.id ≠ me) := by
  induction mb generalizing M with
  | nil => exact Or.inl h
  | cons r' mb ih =>
    rcases ih h with h | h
    · unfold bodyM at h; split_ifs at h with hc
      · rcases Finset.mem_insert.mp h with h | h
        · subst h; exact Or.inr ⟨List.mem_cons_self, hc.1⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩

theorem exists_foldl_bodyM {me : ι} {mb : List (Rcd ι Δ)} {M : Finset (Rcd ι Δ)} {r : Rcd ι Δ}
    (hr : r ∈ mb) (hid : r.id ≠ me) :
    ∃ r' ∈ mb.foldl (bodyM me) M, r'.id = r.id ∧ r'.ttl = r.ttl := by
  induction mb generalizing M with
  | nil => simp at hr
  | cons r' mb ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst h
      simp only [List.foldl_cons]
      have : ∃ r'' ∈ bodyM me M r, r''.id = r.id ∧ r''.ttl = r.ttl := by
        unfold bodyM; split_ifs with hc
        · exact ⟨r, Finset.mem_insert_self _ _, rfl, rfl⟩
        · push Not at hc; exact hc hid
      obtain ⟨r'', h1, h2⟩ := this
      exact ⟨r'', subset_foldl_bodyM me mb _ h1, h2⟩
    · exact ih h

/-! ### Finite-map helpers -/

theorem incr_f (me : ι) (M : MapT ι Δ) (k : ι) :
    (incr me M).f k = if k = me then (M.f k).map (fun e => (e.1 + 1, e.2)) else M.f k := by
  simp only [incr, FMap.modify_f]
  cases M.f k <;> by_cases h : k = me <;> simp [h]

theorem incr_f_ne {me k : ι} (h : k ≠ me) (M : MapT ι Δ) : (incr me M).f k = M.f k := by
  rw [incr_f, if_neg h]

/-- Increment of the suspicion value. -/
def incE (e : Entry Δ) : Entry Δ := (e.1 + 1, e.2)

theorem bodyL_f (me : ι) (L : MapT ι Δ) (r : Rcd ι Δ) (k : ι) :
    (bodyL me L r).f k =
      if r.id = me then L.f k
      else if k = me then (if r.lsps.f me = none then (L.f me).map incE else L.f me)
      else if k = r.id ∧ (L.f k = none ∨ ∃ e, L.f k = some e ∧ e.2 < r.ttl)
        then some (suspOf r.lsps k, r.ttl) else L.f k := by
  unfold bodyL
  by_cases hr : r.id = me
  · simp [hr]
  simp only [hr, if_false]
  by_cases hk : k = me
  · subst hk
    have hne : r.id ≠ k := hr
    have : (if L.f r.id = none ∨ ∃ e, L.f r.id = some e ∧ e.2 < r.ttl
        then L.set r.id (some (suspOf r.lsps r.id, r.ttl)) else L).f k = L.f k := by
      split_ifs <;> simp [Ne.symm hne]
    simp only [if_true]
    by_cases h1 : r.lsps.f k = none
    · simp only [h1, if_true]; rw [incr_f, if_pos rfl, this]; rfl
    · simp only [h1, if_false]; exact this
  · simp only [hk, if_false]
    have h1 : ∀ M : MapT ι Δ, (if r.lsps.f me = none then incr me M else M).f k = M.f k := by
      intro M; split_ifs <;> simp [incr_f_ne hk]
    rw [h1]
    by_cases hkr : k = r.id
    · subst hkr
      by_cases hc : (L.f r.id = none ∨ ∃ e, L.f r.id = some e ∧ e.2 < r.ttl)
      · rw [if_pos hc, if_pos ⟨rfl, hc⟩, FMap.set_f, if_pos rfl]
      · rw [if_neg hc, if_neg (fun h => hc h.2)]
    · simp only [hkr, false_and, if_false]
      split_ifs <;> simp [hkr]

theorem bodyG_f (me : ι) (G : MapT ι Δ) (r : Rcd ι Δ) (k : ι) :
    (bodyG me G r).f k =
      if r.id = me then G.f k
      else if k = me then (if r.lsps.f me = none then (G.f me).map incE else G.f me)
      else if r.lsps.f k ≠ none then some (suspOf r.lsps k, Fin.last Δ) else G.f k := by
  unfold bodyG
  by_cases hr : r.id = me
  · simp [hr]
  simp only [hr, if_false]
  by_cases hk : k = me
  · subst hk
    simp only [if_true]
    by_cases h1 : r.lsps.f k = none
    · simp only [h1, if_true]; rw [incr_f, if_pos rfl]; simp [FMap.ofSub]; rfl
    · simp [h1, FMap.ofSub]
  · simp only [hk, if_false]
    split_ifs <;> simp_all [incr_f_ne hk, FMap.ofSub]

/-! ### `Lstable` part of the loop -/

theorem foldl_bodyL_ne {me k : ι} (hk : k ≠ me) {mb : List (Rcd ι Δ)} {L : MapT ι Δ}
    {e : Entry Δ} (h : (mb.foldl (bodyL me) L).f k = some e) :
    L.f k = some e ∨ ∃ r ∈ mb, r.id = k ∧ e = (suspOf r.lsps k, r.ttl) := by
  induction mb generalizing L with
  | nil => exact Or.inl h
  | cons r mb ih =>
    rcases ih h with h | ⟨r', hr', h'⟩
    · rw [bodyL_f] at h
      simp only [hk, if_false] at h
      split_ifs at h with h1 h2
      · exact Or.inl h
      · obtain ⟨rfl, -⟩ := h2; cases h
        exact Or.inr ⟨r, List.mem_cons_self, rfl, rfl⟩
      · exact Or.inl h
    · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', h'⟩

/-- Monotonicity of the timer of `k ≠ me` along the loop. -/
theorem foldl_bodyL_mono {me k : ι} (hk : k ≠ me) {mb : List (Rcd ι Δ)} {L : MapT ι Δ}
    {e : Entry Δ} (h : L.f k = some e) :
    ∃ e', (mb.foldl (bodyL me) L).f k = some e' ∧ e.2 ≤ e'.2 := by
  induction mb generalizing L e with
  | nil => exact ⟨e, h, le_rfl⟩
  | cons r mb ih =>
    simp only [List.foldl_cons]
    suffices ∃ e', (bodyL me L r).f k = some e' ∧ e.2 ≤ e'.2 by
      obtain ⟨e', h1, h2⟩ := this
      obtain ⟨e'', h3, h4⟩ := ih h1
      exact ⟨e'', h3, h2.trans h4⟩
    rw [bodyL_f]
    simp only [hk, if_false]
    split_ifs with h1 h2
    · exact ⟨e, h, le_rfl⟩
    · obtain ⟨-, h2 | ⟨e0, he0, hlt⟩⟩ := h2
      · rw [h] at h2; cases h2
      · rw [h] at he0; cases he0; exact ⟨_, rfl, le_of_lt hlt⟩
    · exact ⟨e, h, le_rfl⟩

theorem foldl_bodyL_recv {me : ι} {mb : List (Rcd ι Δ)} {L : MapT ι Δ} {r : Rcd ι Δ}
    (hr : r ∈ mb) (hid : r.id ≠ me) :
    ∃ e, (mb.foldl (bodyL me) L).f r.id = some e ∧ r.ttl ≤ e.2 := by
  induction mb generalizing L with
  | nil => simp at hr
  | cons a mb ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst h
      simp only [List.foldl_cons]
      have : ∃ e, (bodyL me L r).f r.id = some e ∧ r.ttl ≤ e.2 := by
        rw [bodyL_f]
        simp only [hid, if_false, true_and]
        split_ifs with hc
        · exact ⟨_, rfl, le_rfl⟩
        · push Not at hc
          obtain ⟨e0, he0⟩ := Option.ne_none_iff_exists'.mp hc.1
          exact ⟨e0, he0, hc.2 e0 he0⟩
      obtain ⟨e, h1, h2⟩ := this
      obtain ⟨e', h3, h4⟩ := foldl_bodyL_mono (mb := mb) hid h1
      exact ⟨e', h3, h2.trans h4⟩
    · exact ih h

/-- Number of received records (from others) that do not contain `me` (line 18). -/
noncomputable def nIncr (me : ι) (mb : List (Rcd ι Δ)) : ℕ :=
  mb.countP fun r => r.id ≠ me ∧ r.lsps.f me = none

theorem nIncr_cons (me : ι) (r : Rcd ι Δ) (mb : List (Rcd ι Δ)) :
    nIncr me (r :: mb) = nIncr me mb + if r.id ≠ me ∧ r.lsps.f me = none then 1 else 0 := by
  simp [nIncr, List.countP_cons]

theorem foldl_bodyL_me (me : ι) (mb : List (Rcd ι Δ)) (L : MapT ι Δ) :
    (mb.foldl (bodyL me) L).f me = (L.f me).map (fun e => (e.1 + nIncr me mb, e.2)) := by
  induction mb generalizing L with
  | nil => simp [nIncr]
  | cons r mb ih =>
    rw [List.foldl_cons, ih, bodyL_f, nIncr_cons]
    by_cases hr : r.id = me
    · simp [hr]
    by_cases h1 : r.lsps.f me = none
    · simp only [hr, h1, if_true, if_false, not_false_eq_true, and_self]
      cases L.f me <;> simp [incE, Nat.add_assoc, Nat.add_comm 1, hr]
    · simp only [hr, h1, if_true, if_false, and_false]
      cases L.f me <;> simp

/-! ### `Gstable` part of the loop -/

theorem foldl_bodyG_ne {me k : ι} (hk : k ≠ me) {mb : List (Rcd ι Δ)} {G : MapT ι Δ}
    {e : Entry Δ} (h : (mb.foldl (bodyG me) G).f k = some e) :
    G.f k = some e ∨ ∃ r ∈ mb, r.id ≠ me ∧ r.lsps.f k ≠ none ∧
      e = (suspOf r.lsps k, Fin.last Δ) := by
  induction mb generalizing G with
  | nil => exact Or.inl h
  | cons r mb ih =>
    rcases ih h with h | ⟨r', hr', h'⟩
    · rw [bodyG_f] at h
      simp only [hk, if_false] at h
      split_ifs at h with h1 h2
      · exact Or.inl h
      · cases h; exact Or.inr ⟨r, List.mem_cons_self, h1, h2, rfl⟩
      · exact Or.inl h
    · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem foldl_bodyG_mono {me k : ι} (hk : k ≠ me) {mb : List (Rcd ι Δ)} {G : MapT ι Δ}
    {σ : ℕ} (h : G.f k = some (σ, Fin.last Δ)) :
    ∃ σ', (mb.foldl (bodyG me) G).f k = some (σ', Fin.last Δ) := by
  induction mb generalizing G σ with
  | nil => exact ⟨σ, h⟩
  | cons r mb ih =>
    simp only [List.foldl_cons]
    have : ∃ σ', (bodyG me G r).f k = some (σ', Fin.last Δ) := by
      rw [bodyG_f]
      simp only [hk, if_false]
      split_ifs
      · exact ⟨σ, h⟩
      · exact ⟨_, rfl⟩
      · exact ⟨σ, h⟩
    obtain ⟨σ', h'⟩ := this
    exact ih h'

theorem foldl_bodyG_recv {me k : ι} (hk : k ≠ me) {mb : List (Rcd ι Δ)} {G : MapT ι Δ}
    {r : Rcd ι Δ} (hr : r ∈ mb) (hid : r.id ≠ me) (hkr : r.lsps.f k ≠ none) :
    ∃ σ, (mb.foldl (bodyG me) G).f k = some (σ, Fin.last Δ) := by
  induction mb generalizing G with
  | nil => simp at hr
  | cons a mb ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst h
      simp only [List.foldl_cons]
      apply foldl_bodyG_mono hk (σ := suspOf r.lsps k)
      rw [bodyG_f]
      simp [hk, hid, hkr]
    · exact ih h

theorem foldl_bodyG_me (me : ι) (mb : List (Rcd ι Δ)) (G : MapT ι Δ) :
    (mb.foldl (bodyG me) G).f me = (G.f me).map (fun e => (e.1 + nIncr me mb, e.2)) := by
  induction mb generalizing G with
  | nil => simp [nIncr]
  | cons r mb ih =>
    rw [List.foldl_cons, ih, bodyG_f, nIncr_cons]
    by_cases hr : r.id = me
    · simp [hr]
    by_cases h1 : r.lsps.f me = none
    · simp only [hr, h1, if_true, if_false, not_false_eq_true, and_self]
      cases G.f me <;> simp [incE, Nat.add_assoc, Nat.add_comm 1, hr]
    · simp only [hr, h1, if_true, if_false, and_false]
      cases G.f me <;> simp

/-! ### The other lines -/

theorem initL_f_ne {me k : ι} (hk : k ≠ me) (L : MapT ι Δ) : (initL me L).f k = L.f k := by
  unfold initL; split_ifs <;> simp [hk]

/-- The suspicion value of `me` after line 4. -/
noncomputable def baseSusp (me : ι) (L : MapT ι Δ) : ℕ :=
  if h : ∃ σ, L.f me = some (σ, Fin.last Δ) then h.choose else 0

theorem initL_f_me (me : ι) (L : MapT ι Δ) :
    (initL me L).f me = some (baseSusp me L, Fin.last Δ) := by
  unfold initL baseSusp
  split_ifs with h
  · exact h.choose_spec
  · simp

theorem baseSusp_eq {me : ι} {L : MapT ι Δ} {σ : ℕ} (h : L.f me = some (σ, Fin.last Δ)) :
    baseSusp me L = σ := by
  have h' : ∃ σ, L.f me = some (σ, Fin.last Δ) := ⟨σ, h⟩
  unfold baseSusp; rw [dif_pos h']
  have := h'.choose_spec
  have h2 : (some (h'.choose, Fin.last Δ) : Option (Entry Δ)) = some (σ, Fin.last Δ) :=
    this.symm.trans h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.1

theorem initG_f_ne {me k : ι} (hk : k ≠ me) (L G : MapT ι Δ) : (initG me L G).f k = G.f k := by
  unfold initG; split_ifs <;> simp [hk]

theorem initG_f_me (me : ι) (L G : MapT ι Δ) {b : ℕ} (hL : L.f me = some (b, Fin.last Δ)) :
    (initG me L G).f me = L.f me := by
  unfold initG
  split_ifs with h
  · obtain ⟨σ, h1, h2⟩ := h
    rw [h1, hL]; simp only [suspOf, hL] at h2; rw [h2]
  · simp

theorem decAll_f (me : ι) (M : MapT ι Δ) (k : ι) :
    (decAll me M).f k = if k = me then M.f k
      else (M.f k).map fun e => if e.2.val ≠ 0 then (e.1, dec e.2) else e := by
  simp only [decAll, FMap.modify_f]
  cases M.f k <;> by_cases hk : k = me <;> simp [hk] <;> split_ifs <;> simp_all

theorem purge_f (M : MapT ι Δ) (k : ι) :
    (purge M).f k = (M.f k).bind fun e => if e.2.val = 0 then none else some e := rfl

/-! ### The state after one round -/

variable (me : ι) (s : St ι Δ) (mb : List (Rcd ι Δ))

theorem roundLE_L_me (hΔ : 1 ≤ Δ) :
    (roundLE me s mb).L.f me = some (baseSusp me s.L + nIncr me mb, Fin.last Δ) := by
  simp only [roundLE, loop_eq, purge_f, foldl_bodyL_me, decAll_f, if_pos rfl, initL_f_me]
  simp; omega

theorem roundLE_G_me (hΔ : 1 ≤ Δ) : (roundLE me s mb).G.f me = (roundLE me s mb).L.f me := by
  rw [roundLE_L_me me s mb hΔ]
  simp only [roundLE, loop_eq, purge_f, foldl_bodyG_me, decAll_f, if_pos rfl,
    initG_f_me me _ _ (initL_f_me me s.L), initL_f_me]
  simp; omega

theorem roundLE_lid : (roundLE me s mb).lid = leaderOf me (roundLE me s mb).G := rfl

theorem roundLE_L_ne {k : ι} (hk : k ≠ me) {e : Entry Δ} (h : (roundLE me s mb).L.f k = some e) :
    1 ≤ e.2.val ∧ ((∃ r ∈ mb, r.id = k ∧ e = (suspOf r.lsps k, r.ttl)) ∨
      ∃ e0, s.L.f k = some e0 ∧ e0.1 = e.1 ∧ e0.2.val = e.2.val + 1) := by
  simp only [roundLE, loop_eq, purge_f] at h
  obtain ⟨e1, he1, h2⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h2 with h0
  cases h2
  refine ⟨by omega, ?_⟩
  rcases foldl_bodyL_ne hk he1 with h3 | h3
  · right
    rw [decAll_f, if_neg hk, initL_f_ne hk] at h3
    obtain ⟨e0, he0, h4⟩ := Option.map_eq_some_iff.mp h3
    refine ⟨e0, he0, ?_⟩
    split_ifs at h4 with h5
    · subst h4; simp [dec]; omega
    · subst h4; exact absurd h0 (by simpa using h5)
  · exact Or.inl h3

theorem roundLE_L_recv {r : Rcd ι Δ} (hr : r ∈ mb) (hid : r.id ≠ me) (httl : 1 ≤ r.ttl.val) :
    ∃ e, (roundLE me s mb).L.f r.id = some e ∧ r.ttl ≤ e.2 := by
  obtain ⟨e, h1, h2⟩ := foldl_bodyL_recv (L := decAll me (initL me s.L)) hr hid
  refine ⟨e, ?_, h2⟩
  simp only [roundLE, loop_eq, purge_f, h1, Option.bind_some]
  rw [if_neg]; rw [Fin.le_def] at h2; omega

theorem roundLE_G_ne {k : ι} (hk : k ≠ me) {e : Entry Δ} (h : (roundLE me s mb).G.f k = some e) :
    1 ≤ e.2.val ∧ ((∃ r ∈ mb, r.id ≠ me ∧ r.lsps.f k ≠ none ∧
      e = (suspOf r.lsps k, Fin.last Δ)) ∨
      ∃ e0, s.G.f k = some e0 ∧ e0.1 = e.1 ∧ e0.2.val = e.2.val + 1) := by
  simp only [roundLE, loop_eq, purge_f] at h
  obtain ⟨e1, he1, h2⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h2 with h0
  cases h2
  refine ⟨by omega, ?_⟩
  rcases foldl_bodyG_ne hk he1 with h3 | h3
  · right
    rw [decAll_f, if_neg hk, initG_f_ne hk] at h3
    obtain ⟨e0, he0, h4⟩ := Option.map_eq_some_iff.mp h3
    refine ⟨e0, he0, ?_⟩
    split_ifs at h4 with h5
    · subst h4; simp [dec]; omega
    · subst h4; exact absurd h0 (by simpa using h5)
  · exact Or.inl h3

theorem roundLE_G_recv (hΔ : 1 ≤ Δ) {k : ι} (hk : k ≠ me) {r : Rcd ι Δ} (hr : r ∈ mb)
    (hid : r.id ≠ me) (hkr : r.lsps.f k ≠ none) :
    ∃ σ, (roundLE me s mb).G.f k = some (σ, Fin.last Δ) := by
  obtain ⟨σ, h1⟩ := foldl_bodyG_recv (G := decAll me (initG me (initL me s.L) s.G)) hk hr hid hkr
  refine ⟨σ, ?_⟩
  simp only [roundLE, loop_eq, purge_f, h1, Option.bind_some]
  rw [if_neg]; simp; omega

theorem roundLE_msgs {r : Rcd ι Δ} :
    r ∈ (roundLE me s mb).msgs ↔ r = ⟨me, (roundLE me s mb).L, Fin.last Δ⟩ ∨
      ∃ r0 ∈ mb.foldl (bodyM me) s.msgs, r0.ttl.val ≠ 0 ∧ r0.lsps.f r0.id ≠ none ∧
        r = { r0 with ttl := dec r0.ttl } := by
  simp only [roundLE, finalMsgs, loop_eq, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro (h | ⟨r0, ⟨h1, h2, h3⟩, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r0, h1, h2, h3, h4.symm⟩
  · rintro (h | ⟨r0, h1, h2, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r0, ⟨h1, h2, h3⟩, h4.symm⟩

/-- Line 27: the elected identifier is the smallest one among those with minimum suspicion. -/
theorem leaderOf_eq {me ℓ : ι} {M : MapT ι Δ} {m : ℕ} (hℓ : ∃ τ, M.f ℓ = some (m, τ))
    (hmin : ∀ k e, M.f k = some e → m ≤ e.1 ∧ (e.1 = m → ℓ ≤ k)) : leaderOf me M = ℓ := by
  obtain ⟨τ, hτ⟩ := hℓ
  have hℓd : ℓ ∈ M.dom := by simp [hτ]
  have hsusp : ∀ k ∈ M.dom, m ≤ suspOf M k := by
    intro k hk
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (FMap.mem_dom.mp hk)
    simp only [suspOf, he]; exact (hmin k e he).1
  have hne : M.dom.Nonempty := ⟨ℓ, hℓd⟩
  unfold leaderOf
  rw [dif_pos hne]
  simp only
  have hm : (M.dom.image (suspOf M)).min' (hne.image _) = m := by
    apply le_antisymm
    · apply Finset.min'_le; exact Finset.mem_image.mpr ⟨ℓ, hℓd, by simp [suspOf, hτ]⟩
    · apply Finset.le_min'
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      exact hsusp k hk
  have hℓf : ℓ ∈ M.dom.filter fun k => suspOf M k = m := by
    rw [Finset.mem_filter]; exact ⟨hℓd, by simp [suspOf, hτ]⟩
  simp only [hm]
  rw [dif_pos ⟨ℓ, hℓf⟩]
  apply le_antisymm
  · exact Finset.min'_le _ _ hℓf
  · apply Finset.le_min'
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (FMap.mem_dom.mp hk.1)
    have := hk.2; simp only [suspOf, he] at this
    exact ((hmin k e he).2 this)

/-- Timers of `Lstable` decrease by at most one per round (for `k ≠ me`). -/
theorem roundLE_L_keep {k : ι} (hk : k ≠ me) {e : Entry Δ} (h : s.L.f k = some e)
    (h2 : 2 ≤ e.2.val) : ∃ e', (roundLE me s mb).L.f k = some e' ∧ e.2.val ≤ e'.2.val + 1 := by
  have h0 : (decAll me (initL me s.L)).f k = some (e.1, dec e.2) := by
    rw [decAll_f, if_neg hk, initL_f_ne hk, h, Option.map_some,
      if_pos (show (e.2 : ℕ) ≠ 0 by omega)]
  obtain ⟨e', h1, h3⟩ := foldl_bodyL_mono (mb := mb) hk h0
  refine ⟨e', ?_, ?_⟩
  · simp only [roundLE, loop_eq, purge_f, h1, Option.bind_some]
    rw [if_neg]; rw [Fin.le_def] at h3; simp [dec] at h3; omega
  · rw [Fin.le_def] at h3; simp [dec] at h3; omega

theorem foldl_bodyG_mono' {me k : ι} (hk : k ≠ me) {mb : List (Rcd ι Δ)} {G : MapT ι Δ}
    {e : Entry Δ} (h : G.f k = some e) :
    ∃ e', (mb.foldl (bodyG me) G).f k = some e' ∧ e.2 ≤ e'.2 := by
  induction mb generalizing G e with
  | nil => exact ⟨e, h, le_rfl⟩
  | cons r mb ih =>
    simp only [List.foldl_cons]
    have : ∃ e', (bodyG me G r).f k = some e' ∧ e.2 ≤ e'.2 := by
      rw [bodyG_f]
      simp only [hk, if_false]
      split_ifs
      · exact ⟨e, h, le_rfl⟩
      · exact ⟨_, rfl, Fin.le_last _⟩
      · exact ⟨e, h, le_rfl⟩
    obtain ⟨e', h1, h2⟩ := this
    obtain ⟨e'', h3, h4⟩ := ih h1
    exact ⟨e'', h3, h2.trans h4⟩

/-- Timers of `Gstable` decrease by at most one per round (for `k ≠ me`). -/
theorem roundLE_G_keep {k : ι} (hk : k ≠ me) {e : Entry Δ} (h : s.G.f k = some e)
    (h2 : 2 ≤ e.2.val) : ∃ e', (roundLE me s mb).G.f k = some e' ∧ e.2.val ≤ e'.2.val + 1 := by
  have h0 : (decAll me (initG me (initL me s.L) s.G)).f k = some (e.1, dec e.2) := by
    rw [decAll_f, if_neg hk, initG_f_ne hk, h, Option.map_some,
      if_pos (show (e.2 : ℕ) ≠ 0 by omega)]
  obtain ⟨e', h1, h3⟩ := foldl_bodyG_mono' (mb := mb) hk h0
  refine ⟨e', ?_, ?_⟩
  · simp only [roundLE, loop_eq, purge_f, h1, Option.bind_some]
    rw [if_neg]; rw [Fin.le_def] at h3; simp [dec] at h3; omega
  · rw [Fin.le_def] at h3; simp [dec] at h3; omega

end StabilizingLEDynamic.LE
