import Papers.PODC2020.DetectableSpace.Basic

/-!
# Reasoning about durable detectable linearizations

* `peel_head`: an operation that returned before every other operation of `L` was invoked is
  the first element of `L`;
* sequential histories `seqHist n H rs` (operations of `H` executed one after the other, with
  identifiers `n, n+1, …` and responses `rs`) and `peel_seq`: every linearization of a history
  containing a sequential segment begins (after the earlier part) with that segment, in order,
  with the responses prescribed by the specification;
* `seq_exec`: with weak obstruction-freedom and correctness, every sequential history can be
  executed from a quiescent reachable configuration.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

variable {P : Type} {O : ObjSpec}

/-- The first element of a linearization. -/
theorem peel_head {h : List (HEv P O.Op O.Resp)} {L : List (ℕ × O.Op)}
    (hrt : L.Pairwise (fun x y => ¬ Prec h y.1 x.1)) {x : ℕ × O.Op} (hx : x ∈ L)
    {h₁ h₂ : List (HEv P O.Op O.Resp)} (hh : h = h₁ ++ h₂)
    (hres : ∃ r c, HEv.res x.1 r c ∈ h₁)
    (hinv : ∀ y ∈ L, y ≠ x → ∃ p, HEv.inv y.1 p y.2 ∈ h₂) : ∃ L', L = x :: L' := by
  cases L with
  | nil => simp at hx
  | cons y L0 =>
    by_cases hyx : y = x
    · exact ⟨L0, by rw [hyx]⟩
    · exfalso
      have hx0 : x ∈ L0 := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hyx
        · exact h
      rw [List.pairwise_cons] at hrt
      obtain ⟨p, hp⟩ := hinv y (by simp) hyx
      exact hrt.1 x hx0 ⟨h₁, h₂, hh, hres, p, y.2, hp⟩

lemma Legal.cons {h : List (HEv P O.Op O.Resp)} {σ : O.State} {a : ℕ} {o : O.Op}
    {L : List (ℕ × O.Op)} (hl : Legal O h σ ((a, o) :: L)) :
    (∀ r c, HEv.res a (some r) c ∈ h → r = (O.δ σ o).2) ∧ Legal O h (O.δ σ o).1 L := hl

lemma Legal.mono {h h' : List (HEv P O.Op O.Resp)}
    (hh : ∀ a r c, HEv.res a (some r) c ∈ h' → HEv.res a (some r) c ∈ h) :
    ∀ {σ : O.State} {L : List (ℕ × O.Op)}, Legal O h σ L → Legal O h' σ L := by
  intro σ L
  induction L generalizing σ with
  | nil => intro; trivial
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    intro hl
    exact ⟨fun r c hr => hl.1 r c (hh _ _ _ hr), ih hl.2⟩

lemma Legal.append {h : List (HEv P O.Op O.Resp)} :
    ∀ {σ : O.State} {L L' : List (ℕ × O.Op)}, Legal O h σ (L ++ L') →
      Legal O h (O.runOps σ (L.map Prod.snd)) L' := by
  intro σ L L'
  induction L generalizing σ with
  | nil => intro hl; simpa using hl
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    intro hl
    exact ih hl.2

/-! ### Sequential segments -/

/-- History of the operations `H` executed sequentially, with identifiers `n, n+1, …` and
responses `rs`. -/
def seqHist : ℕ → List (P × O.Op) → List O.Resp → List (HEv P O.Op O.Resp)
  | n, x :: H, r :: rs => .inv n x.1 x.2 :: .res n (some r) false :: seqHist (n + 1) H rs
  | _, _, _ => []

/-- The sequential order of the operations of `H` with identifiers `n, n+1, …`. -/
def seqL : ℕ → List (P × O.Op) → List (ℕ × O.Op)
  | _, [] => []
  | n, x :: H => (n, x.2) :: seqL (n + 1) H

/-- Responses of the operations `H` executed sequentially from `σ`. -/
def specResps (σ : O.State) : List (P × O.Op) → List O.Resp
  | [] => []
  | x :: H => (O.δ σ x.2).2 :: specResps (O.δ σ x.2).1 H

lemma mem_seqHist_inv {n : ℕ} {H : List (P × O.Op)} {rs : List O.Resp} {a : ℕ} {p : P}
    {o : O.Op} (h : HEv.inv a p o ∈ seqHist n H rs) : n ≤ a ∧ a < n + H.length := by
  induction H generalizing n rs with
  | nil => simp [seqHist] at h
  | cons x H ih =>
    cases rs with
    | nil => simp [seqHist] at h
    | cons r rs =>
      simp only [seqHist, List.mem_cons, reduceCtorEq, false_or] at h
      rcases h with h | h
      · simp only [HEv.inv.injEq] at h; obtain ⟨rfl, -, -⟩ := h; simp
      · have := ih h; simp only [List.length_cons]; omega

/-- **Peeling a sequential segment** off a linearization. -/
theorem peel_seq {h : List (HEv P O.Op O.Resp)}
    (hU : ∀ a p o p' o', HEv.inv a p o ∈ h → HEv.inv a p' o' ∈ h → o = o') :
    ∀ (H : List (P × O.Op)) (rs : List O.Resp) (n : ℕ) (hpre t : List (HEv P O.Op O.Resp))
      (σ : O.State) (L : List (ℕ × O.Op)),
      rs.length = H.length →
      h = hpre ++ seqHist n H rs ++ t →
      (∀ a p o, HEv.inv a p o ∈ hpre → a < n) →
      (∀ a p o, HEv.inv a p o ∈ t → n + H.length ≤ a) →
      (L.map Prod.fst).Nodup →
      L.Pairwise (fun x y => ¬ Prec h y.1 x.1) →
      Legal O h σ L →
      (∀ y ∈ L, ∃ p, HEv.inv y.1 p y.2 ∈ h) →
      (∀ y ∈ L, n ≤ y.1) →
      (∀ a r c, HEv.res a (some r) c ∈ h → n ≤ a → a ∈ L.map Prod.fst) →
      ∃ L', L = seqL n H ++ L' ∧ (∀ y ∈ L', n + H.length ≤ y.1) ∧
        Legal O h (O.runOps σ (H.map Prod.snd)) L' ∧ rs = specResps σ H := by
  intro H
  induction H with
  | nil =>
    intro rs n hpre t σ L hlen _ _ _ _ _ hleg _ hge _
    have : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this
    exact ⟨L, rfl, by simpa using hge, by simpa using hleg, rfl⟩
  | cons x H ih =>
    intro rs n hpre t σ L hlen hh hpre_lt ht_ge hnd hrt hleg hinv hge hmem
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hh' : h = (hpre ++ [.inv n x.1 x.2, .res n (some r) false]) ++
          (seqHist (n + 1) H rs ++ t) := by
        rw [hh]; simp [seqHist]
      -- the operation `n` is in `L`
      have hn : n ∈ L.map Prod.fst := hmem n r false (by rw [hh']; simp) le_rfl
      obtain ⟨y, hyL, hyn⟩ := List.mem_map.1 hn
      have hy : y = (n, x.2) := by
        obtain ⟨p, hp⟩ := hinv y hyL
        rw [hyn] at hp
        exact Prod.ext hyn (hU n p y.2 x.1 x.2 hp (by rw [hh']; simp))
      -- where are the other invocations
      have hloc : ∀ z ∈ L, z ≠ (n, x.2) → ∃ p, HEv.inv z.1 p z.2 ∈ seqHist (n + 1) H rs ++ t := by
        intro z hz hzn
        obtain ⟨p, hp⟩ := hinv z hz
        refine ⟨p, ?_⟩
        rw [hh'] at hp
        rcases List.mem_append.1 hp with hp | hp
        · exfalso
          rcases List.mem_append.1 hp with hp | hp
          · have := hpre_lt _ _ _ hp; have := hge z hz; omega
          · simp only [List.mem_cons, HEv.inv.injEq, reduceCtorEq, List.mem_nil_iff,
              or_false] at hp
            obtain ⟨h1, -, h3⟩ := hp
            exact hzn (Prod.ext h1 h3)
        · exact hp
      obtain ⟨L1, rfl⟩ := peel_head hrt (hy ▸ hyL) hh' ⟨some r, false, by simp⟩ hloc
      obtain ⟨hr, hleg1⟩ := Legal.cons hleg
      have hr' := hr r false (by rw [hh']; simp)
      have hnd1 : (L1.map Prod.fst).Nodup := (List.nodup_cons.1 (by simpa using hnd)).2
      have hnL1 : n ∉ L1.map Prod.fst := (List.nodup_cons.1 (by simpa using hnd)).1
      have hge1 : ∀ z ∈ L1, n + 1 ≤ z.1 := by
        intro z hz
        have h1 := hge z (by simp [hz])
        have h2 : z.1 ≠ n := fun h => hnL1 (List.mem_map.2 ⟨z, hz, h⟩)
        omega
      obtain ⟨L', hL', hge', hleg', hrs⟩ := ih rs (n + 1)
        (hpre ++ [.inv n x.1 x.2, .res n (some r) false]) t (O.δ σ x.2).1 L1 hlen
        (by rw [hh']; simp)
        (by
          intro a p o ha
          rcases List.mem_append.1 ha with ha | ha
          · have := hpre_lt a p o ha; omega
          · simp at ha; omega)
        (by intro a p o ha; have := ht_ge a p o ha; simp at this; omega)
        hnd1 (List.pairwise_cons.1 hrt).2 hleg1
        (fun z hz => hinv z (by simp [hz])) hge1
        (by
          intro a r' c ha hna
          have := hmem a r' c ha (by omega)
          simp only [List.map_cons, List.mem_cons] at this
          rcases this with h | h
          · omega
          · exact h)
      refine ⟨L', by simp [hL', seqL], ?_, ?_, ?_⟩
      · intro z hz; have := hge' z hz; simp; omega
      · simpa using hleg'
      · simp [specResps, hr', hrs]

/-! ### Building linearizations incrementally

Lemmas for proofs that an algorithm is durably linearizable and detectable: maintain a
linearization `L` of the history so far and extend it event by event. -/

section Incremental

variable {h : List (HEv P O.Op O.Resp)} {L : List (ℕ × O.Op)}

lemma prec_append_of_ne {h δ : List (HEv P O.Op O.Resp)} {a b : ℕ}
    (hδ : ∀ c q o, HEv.inv c q o ∈ δ → c ≠ b)
    (hp : Prec (h ++ δ) a b) (_hb : ∃ q o, HEv.inv b q o ∈ h) : Prec h a b := by
  obtain ⟨h₁, h₂, he, ⟨r, c, hr⟩, q, o, hq⟩ := hp
  rcases List.append_eq_append_iff.1 he with ⟨m, _, hm2⟩ | ⟨m, hm1, hm2⟩
  · exfalso; exact hδ b q o (by rw [hm2]; exact List.mem_append_right _ hq) rfl
  · rw [hm2] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact ⟨h₁, m, hm1, ⟨r, c, hr⟩, q, o, hq⟩
    · exact absurd rfl (hδ b q o hq)

/-- (S1) Appending events containing no response and no invocation of a linearized
operation preserves a linearization. -/
lemma DLin.append_noRes {σ : O.State} (hd : DLin O h σ L) (δ : List (HEv P O.Op O.Resp))
    (hδr : ∀ a r c, HEv.res a r c ∉ δ) (hδi : ∀ a q o, HEv.inv a q o ∈ δ → a ∉ L.map Prod.fst) :
    DLin O (h ++ δ) σ L where
  nodup := hd.nodup
  inv_of_mem x hx := by
    obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, List.mem_append_left _ hp⟩
  mem_of_res a r c ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.mem_of_res a r c ha
    · exact absurd ha (hδr a _ c)
  not_mem_of_fail a c ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.not_mem_of_fail a c ha
    · exact absurd ha (hδr a _ c)
  rt := by
    refine hd.rt.imp_of_mem (fun {x y} hx _ hxy hp => hxy ?_)
    refine prec_append_of_ne ?_ hp ?_
    · intro c q o hc hcx
      exact hδi c q o hc (List.mem_map.2 ⟨x, hx, hcx.symm⟩)
    · obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, x.2, hp⟩
  legal := Legal.mono (fun a r c ha => by
    rcases List.mem_append.1 ha with ha | ha
    · exact ha
    · exact absurd ha (hδr a _ c)) hd.legal

/-- (S3) Linearizing a pending operation (invoked, without a response) at the end. -/
lemma DLin.push {σ : O.State} (hd : DLin O h σ L) (a : ℕ) (q : P) (o : O.Op)
    (hinv : HEv.inv a q o ∈ h) (hnr : ∀ r c, HEv.res a r c ∉ h) (hnL : a ∉ L.map Prod.fst) :
    DLin O h σ (L ++ [(a, o)]) where
  nodup := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨hd.nodup, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact fun h => hnL (h ▸ hx)
  inv_of_mem x hx := by
    rcases List.mem_append.1 hx with hx | hx
    · exact hd.inv_of_mem x hx
    · simp at hx; subst hx; exact ⟨q, hinv⟩
  mem_of_res a' r c ha := by
    have := hd.mem_of_res a' r c ha; simp only [List.map_append, List.mem_append]; exact .inl this
  not_mem_of_fail a' c ha := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
      not_or]
    refine ⟨hd.not_mem_of_fail a' c ha, ?_⟩
    rintro rfl; exact hnr _ _ ha
  rt := by
    refine List.pairwise_append.2 ⟨hd.rt, by simp, ?_⟩
    intro x _ y hy
    simp at hy; subst hy
    rintro ⟨h₁, h₂, he, ⟨r, c, hr⟩, -⟩
    exact hnr r c (he ▸ List.mem_append_left _ hr)
  legal := by
    have key : ∀ (σ : O.State) (L : List (ℕ × O.Op)), Legal O h σ L →
        Legal O h σ (L ++ [(a, o)]) := by
      intro σ L
      induction L generalizing σ with
      | nil => intro _; exact ⟨fun r c hr => absurd hr (hnr _ c), trivial⟩
      | cons x L ih =>
        obtain ⟨b, o'⟩ := x
        intro hl; exact ⟨hl.1, ih _ hl.2⟩
    exact key σ L hd.legal

/-- Legality of the last element. -/
lemma Legal.append_single {σ : O.State} (hl : Legal O h σ (L ++ [(a, o)]))
    {r : O.Resp} {c : Bool} (hr : HEv.res a (some r) c ∈ h) :
    r = (O.δ (O.runOps σ (L.map Prod.snd)) o).2 :=
  (Legal.append hl).1 r c hr

/-- (S4) Appending the response of a linearized operation whose sequential response matches. -/
lemma DLin.append_res {σ : O.State} (hd : DLin O h σ L) (a : ℕ) (r : Option O.Resp) (c : Bool)
    (hL : a ∈ L.map Prod.fst ↔ r.isSome)
    (hresp : ∀ r', r = some r' → ∀ L₁ o L₂, L = L₁ ++ (a, o) :: L₂ →
      r' = (O.δ (O.runOps σ (L₁.map Prod.snd)) o).2) :
    DLin O (h ++ [.res a r c]) σ L where
  nodup := hd.nodup
  inv_of_mem x hx := by
    obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, List.mem_append_left _ hp⟩
  mem_of_res a' r' c' ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.mem_of_res a' r' c' ha
    · simp at ha; obtain ⟨rfl, rfl, rfl⟩ := ha; exact hL.2 rfl
  not_mem_of_fail a' c' ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.not_mem_of_fail a' c' ha
    · simp at ha; obtain ⟨rfl, rfl, rfl⟩ := ha; intro h'; simpa using hL.1 h'
  rt := by
    refine hd.rt.imp_of_mem (fun {x y} hx _ hxy hp => hxy ?_)
    refine prec_append_of_ne (by simp) hp ?_
    obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, x.2, hp⟩
  legal := by
    have key : ∀ (σ : O.State) (L₀ : List (ℕ × O.Op)), Legal O h σ L₀ →
        (∀ r', r = some r' → ∀ L₁ o L₂, L₀ = L₁ ++ (a, o) :: L₂ →
          r' = (O.δ (O.runOps σ (L₁.map Prod.snd)) o).2) →
        Legal O (h ++ [.res a r c]) σ L₀ := by
      intro σ L₀
      induction L₀ generalizing σ with
      | nil => intro _ _; trivial
      | cons x L₀ ih =>
        obtain ⟨b, o'⟩ := x
        intro hl hr'
        refine ⟨fun r'' c'' hr'' => ?_, ih _ hl.2 ?_⟩
        · rcases List.mem_append.1 hr'' with hr'' | hr''
          · exact hl.1 r'' c'' hr''
          · simp at hr''; obtain ⟨rfl, rfl, rfl⟩ := hr''
            simpa using hr' r'' rfl [] o' L₀ rfl
        · intro r' hr L₁ o L₂ hL₀
          have := hr' r' hr ((b, o') :: L₁) o L₂ (by simp [hL₀])
          simpa using this
    exact key σ L hd.legal hresp

/-- Removing a pending entry whose operation does not change the state at its position. -/
lemma DLin.erase_mid {σ : O.State} {L₁ L₂ : List (ℕ × O.Op)} {a : ℕ} {o : O.Op}
    (hd : DLin O h σ (L₁ ++ (a, o) :: L₂)) (hnr : ∀ r c, HEv.res a r c ∉ h)
    (hro : (O.δ (O.runOps σ (L₁.map Prod.snd)) o).1 = O.runOps σ (L₁.map Prod.snd)) :
    DLin O h σ (L₁ ++ L₂) where
  nodup := by
    have := hd.nodup
    simp only [List.map_append, List.map_cons] at this ⊢
    exact this.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  inv_of_mem x hx := hd.inv_of_mem x (by
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx))
  mem_of_res b r c hb := by
    have := hd.mem_of_res b r c hb
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at this ⊢
    rcases this with h1 | rfl | h1
    · exact .inl h1
    · exact absurd hb (hnr _ _)
    · exact .inr h1
  not_mem_of_fail b c hb := by
    have := hd.not_mem_of_fail b c hb
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons, not_or] at this ⊢
    exact ⟨this.1, this.2.2⟩
  rt := hd.rt.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  legal := by
    have key : ∀ (σ : O.State) (L₁ : List (ℕ × O.Op)), Legal O h σ (L₁ ++ (a, o) :: L₂) →
        (O.δ (O.runOps σ (L₁.map Prod.snd)) o).1 = O.runOps σ (L₁.map Prod.snd) →
        Legal O h σ (L₁ ++ L₂) := by
      intro σ L₁
      induction L₁ generalizing σ with
      | nil =>
        intro hl hro
        have h2 := hl.2
        simp only [List.map_nil, ObjSpec.runOps_nil] at hro
        rwa [hro] at h2
      | cons x L₁ ih =>
        obtain ⟨b, o'⟩ := x
        intro hl hro
        exact ⟨hl.1, ih _ hl.2 (by simpa using hro)⟩
    exact key σ L₁ hd.legal hro

/-- Removing pending entries whose operations are read-only (never change the state). -/
lemma DLin.filter_ro {σ : O.State} (hd : DLin O h σ L) (f : ℕ × O.Op → Bool)
    (hf : ∀ x ∈ L, f x = false → O.ReadOnly x.2 ∧ ∀ r c, HEv.res x.1 r c ∉ h) :
    DLin O h σ (L.filter f) where
  nodup := hd.nodup.sublist ((List.filter_sublist).map _)
  inv_of_mem x hx := hd.inv_of_mem x (List.mem_of_mem_filter hx)
  mem_of_res b r c hb := by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hd.mem_of_res b r c hb)
    refine List.mem_map.2 ⟨y, List.mem_filter.2 ⟨hy, ?_⟩, rfl⟩
    by_contra hfy
    exact (hf y hy (by simpa using hfy)).2 _ _ hb
  not_mem_of_fail b c hb hm := hd.not_mem_of_fail b c hb
    (by obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
        exact List.mem_map.2 ⟨y, List.mem_of_mem_filter hy, rfl⟩)
  rt := hd.rt.sublist List.filter_sublist
  legal := by
    have key : ∀ (σ : O.State) (L : List (ℕ × O.Op)),
        (∀ x ∈ L, f x = false → O.ReadOnly x.2) → Legal O h σ L → Legal O h σ (L.filter f) := by
      intro σ L
      induction L generalizing σ with
      | nil => intro _ _; trivial
      | cons x L ih =>
        obtain ⟨b, o'⟩ := x
        intro hro hl
        by_cases hfx : f (b, o') = true
        · rw [List.filter_cons_of_pos hfx]
          exact ⟨hl.1, ih _ (fun y hy => hro y (List.mem_cons_of_mem _ hy)) hl.2⟩
        · rw [List.filter_cons_of_neg hfx]
          have h1 := hro (b, o') (by simp) (by simpa using hfx)
          have h2 := ih _ (fun y hy => hro y (List.mem_cons_of_mem _ hy)) hl.2
          rwa [h1 σ] at h2
    exact key σ L (fun x hx hfx => (hf x hx hfx).1) hd.legal

end Incremental

/-! ### Executing sequential histories -/

namespace RImpl

variable [DecidableEq P] (A : RImpl O P)

/-- All processes are idle. -/
def Quiescent (C : A.Cfg) : Prop := ∀ x, C.ps x = .idle

lemma step1_inv_idle (C : A.Cfg) (p : P) (o : O.Op) (h : C.ps p = .idle) :
    A.step1 C (.inv p o) = (⟨C.sh, Function.update C.pv p (A.aux p o (C.pv p)),
      Function.update C.ps p (.run C.cnt o false (A.start p o)), C.cnt + 1⟩, [.inv C.cnt p o]) := by
  simp [step1, h]

/-- With weak obstruction-freedom and correctness, a sequential history can be executed from a
quiescent reachable configuration; operations return values (not `fail`). -/
theorem seq_exec (hwof : A.WeakOF) (hcor : A.DurLinDet) :
    ∀ (H : List (P × O.Op)) (es₀ : List (Ev P O.Op)), A.Quiescent (A.exec A.init es₀).1 →
    ∃ es rs, rs.length = H.length ∧ (∀ e ∈ es, ∀ x, (∀ y ∈ H, y.1 ≠ x) → e.Free x) ∧
      (A.exec (A.exec A.init es₀).1 es).2 = seqHist (A.exec A.init es₀).1.cnt H rs ∧
      A.Quiescent (A.exec (A.exec A.init es₀).1 es).1 ∧
      (A.exec (A.exec A.init es₀).1 es).1.cnt = (A.exec A.init es₀).1.cnt + H.length := by
  intro H
  induction H with
  | nil =>
    intro es₀ hq
    exact ⟨[], [], rfl, by simp, by simp [seqHist], by simpa using hq, by simp⟩
  | cons x H ih =>
    obtain ⟨p, o⟩ := x
    intro es₀ hq
    set C := (A.exec A.init es₀).1 with hC
    have hC1 : (A.exec A.init (es₀ ++ [.inv p o])).1 = (A.step1 C (.inv p o)).1 := by
      rw [exec_fst_append, exec_singleton]
    have hps1 : (A.step1 C (.inv p o)).1.ps p = .run C.cnt o false (A.start p o) := by
      rw [step1_inv_idle A C p o (hq p)]; simp
    have hoth1 : ∀ y, y ≠ p → (A.step1 C (.inv p o)).1.ps y = .idle := by
      intro y hy
      rw [step1_inv_idle A C p o (hq p)]; simp [Function.update_of_ne hy, hq y]
    obtain ⟨k, hk⟩ := hwof _ ⟨_, hC1⟩ p hoth1
    obtain ⟨r, hr⟩ := A.solo_hist p k _ _ _ _ _ hps1 hk
    -- the response is not `fail`
    have hsome : ∃ r', r = some r' := by
      cases r with
      | some r' => exact ⟨r', rfl⟩
      | none =>
        exfalso
        apply (hcor (es₀ ++ [.inv p o] ++ solo p k)).2 C.cnt
        rw [exec_snd_append, exec_snd_append, exec_fst_append, exec_singleton, hr]
        simp
    obtain ⟨r', rfl⟩ := hsome
    set es₁ := es₀ ++ [.inv p o] ++ solo p k with hes₁
    have hC2 : (A.exec A.init es₁).1 = (A.exec (A.step1 C (.inv p o)).1 (solo p k)).1 := by
      rw [hes₁, exec_fst_append, hC1]
    have hq2 : A.Quiescent (A.exec A.init es₁).1 := by
      intro y
      rw [hC2]
      by_cases hy : y = p
      · rw [hy]; exact hk
      · rw [(A.exec_solo_other _ hy k).1]; exact hoth1 y hy
    have hcnt2 : (A.exec A.init es₁).1.cnt = C.cnt + 1 := by
      rw [hC2, exec_solo_cnt, step1_inv_idle A C p o (hq p)]
    obtain ⟨es', rs', hlen, hfree, hhist, hq', hcnt'⟩ := ih es₁ hq2
    refine ⟨[.inv p o] ++ solo p k ++ es', r' :: rs', by simp [hlen], ?_, ?_, ?_, ?_⟩
    · intro e he y hy
      simp only [List.mem_append, List.mem_singleton] at he
      have hpy : p ≠ y := hy (p, o) (by simp)
      rcases he with (rfl | he) | he
      · exact hpy
      · simp only [solo, List.mem_replicate] at he; rw [he.2]; exact hpy
      · exact hfree e he y (fun z hz => hy z (by simp [hz]))
    · have e1 : (A.exec C ([.inv p o] ++ solo p k)).1 = (A.exec A.init es₁).1 := by
        rw [hes₁, List.append_assoc, exec_fst_append (es := es₀)]
      rw [exec_snd_append, e1, hhist, hcnt2, exec_snd_append, exec_singleton, hr]
      simp [seqHist, step1_inv_idle A C p o (hq p)]
    · have e1 : (A.exec C ([.inv p o] ++ solo p k ++ es')).1 =
          (A.exec (A.exec A.init es₁).1 es').1 := by
        rw [exec_fst_append, hes₁, List.append_assoc, exec_fst_append (es := es₀)]
      rw [e1]; exact hq'
    · have e1 : (A.exec C ([.inv p o] ++ solo p k ++ es')).1 =
          (A.exec (A.exec A.init es₁).1 es').1 := by
        rw [exec_fst_append, hes₁, List.append_assoc, exec_fst_append (es := es₀)]
      rw [e1, hcnt', hcnt2]; simp; omega

end RImpl

end Papers.PODC2020.DetectableSpace
