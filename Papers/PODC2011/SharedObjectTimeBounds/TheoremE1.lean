import Papers.PODC2011.SharedObjectTimeBounds.TheoremC1

/-!
# Theorem E.1 of Chapter IV: a self-commuting operation and a pure accessor

`|OP| + |AOP| ≥ d + min {ε, u, d/3}` for an immediately self-commuting `OP` and a pure accessor
`AOP` with the distinguishing properties A, B, C (e.g. enqueue/peek; push/peek on a stack, claimed by the
thesis, is not an instance: `stack_push_peek_not_E1`).

"Pure accessor" is used with its intended meaning `NonMutator` (see `Spec.lean`: under the
literal Definitions D.1/D.4 no operation type is a pure accessor); only the non-mutator part is
needed. "One of the below is legal while the other one is illegal" is `¬ (_ ↔ _)`.
-/

namespace Podc.SharedObjectTimeBounds

open Cslib.TimedMP

namespace E1

noncomputable section

open C1

variable {P I R M : Type*}

/-! ### List helpers -/

theorem pair_order {α : Type*} {x y : α} : ∀ {L : List α}, x ∈ L → y ∈ L → x ≠ y →
    [x, y].Sublist L ∨ [y, x].Sublist L
  | [], hx, _, _ => by simp at hx
  | a :: L, hx, hy, hxy => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hxy
      · exact Or.inl (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hy'))
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact Or.inr (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hx'))
      · rcases pair_order hx' hy' hxy with h | h
        · exact Or.inl (List.Sublist.cons a h)
        · exact Or.inr (List.Sublist.cons a h)

theorem sub3 {α : Type*} {x y z : α} : ∀ {L : List α}, [x, y].Sublist L → [y, z].Sublist L →
    L.Nodup → [x, y, z].Sublist L
  | [], h, _, _ => by simp at h
  | a :: L, h1, h2, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    by_cases hax : x = a
    · have hyx : y ≠ a := fun e => by
        have := hnd.sublist h1
        rw [hax, e] at this
        simp at this
      rw [hax]
      exact List.cons_sublist_cons.mpr (sublist_pair_cons h2 hyx)
    · have h1' := sublist_pair_cons h1 hax
      have hya : y ≠ a := fun e => hnd'.1 (e ▸ h1'.subset (by simp))
      exact List.Sublist.cons a (sub3 h1' (sublist_pair_cons h2 hya) hnd'.2)

theorem filter_mem_eq {α : Type*} [DecidableEq α] {X L : List α} (h : X.Sublist L)
    (hnd : L.Nodup) : L.filter (fun c => decide (c ∈ X)) = X := by
  induction h with
  | slnil => rfl
  | cons a h ih =>
    have hnd' := List.nodup_cons.mp hnd
    have ha : a ∉ _ := fun ha => hnd'.1 (h.subset ha)
    rw [List.filter_cons_of_neg (by simpa using ha)]
    exact ih hnd'.2
  | cons_cons a h ih =>
    have hnd' := List.nodup_cons.mp hnd
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    conv_rhs => rw [← ih hnd'.2]
    apply List.filter_congr
    intro c hc
    have : c ≠ a := fun e => hnd'.1 (e ▸ hc)
    simp [this]

/-- Keeping a sublist `X` of a legal linearization and dropping only accessor instances keeps
legality. -/
theorem extract {α : Type*} [DecidableEq α] {legal : List (I × R) → Prop}
    (hpc : PrefixClosed legal) {AOP : I → Prop} (hacc : NonMutator legal AOP) (f : α → I × R)
    {ρ : List (I × R)} {L X : List α} (hL : legal (ρ ++ L.map f)) (hnd : L.Nodup)
    (hX : X.Sublist L) (hdrop : ∀ c ∈ L, c ∉ X → AOP (f c).1) : legal (ρ ++ X.map f) := by
  have := legal_filter_of_nonMutator hpc hacc f (fun c => decide (c ∈ X)) L ρ hL
    (fun c hc hk => hdrop c hc (by simpa using hk))
  rwa [filter_mem_eq hX hnd] at this

/-- Determinism and "one is legal, the other is illegal": if `y ∘ (a.1, r)` is legal then
`x ∘ (a.1, r)` is illegal. -/
theorem det_flip {legal : List (I × R) → Prop} (hdet : Deterministic legal)
    {x y : List (I × R)} {a : I × R} (h : ¬ (legal (x ++ [a]) ↔ legal (y ++ [a]))) {r : R}
    (hy : legal (y ++ [(a.1, r)])) : ¬ legal (x ++ [(a.1, r)]) := by
  intro hx
  by_cases hxa : legal (x ++ [a])
  · have e := hdet x a.1 r a.2 hx hxa
    subst e
    exact h ⟨fun _ => by simpa using hy, fun _ => hxa⟩
  · have hya : legal (y ++ [a]) := by tauto
    have e := hdet y a.1 r a.2 hy hya
    subst e
    exact hxa (by simpa using hx)

/-! ### Scenarios -/

/-- Runs depend on the invocations only through their set. -/
theorem isRun_of_mem (A : Algorithm P I R M) {s s' : Scenario P I} (hoff : s.off = s'.off)
    (hdel : s.delay = s'.delay) (hc : ∀ c, c ∈ s.calls ↔ c ∈ s'.calls)
    {H : P → Set (ℝ × InEv P I M)} (h : IsRun A s H) : IsRun A s' H := by
  have hs : ∀ p, step A s H p = step A s' H p := by
    intro p
    simp only [step, Scenario.callEv, Scenario.recvEv, hc, hoff, hdel]
  refine ⟨fun p => (h.1 p).trans (hs p), ?_⟩
  obtain ⟨T, hT⟩ := h.2
  exact ⟨T, fun p e he => by rw [← hoff]; exact hT p e he⟩

theorem scen_adm {d u ε : ℝ} (hu : 0 ≤ u) {off : P → ℝ} (hoff : ∀ p q, |off p - off q| ≤ ε)
    {D : P → P → ℝ} (hD : ∀ q r, d - u ≤ D q r ∧ D q r ≤ d) (p₀ : P) (g : ℝ)
    (ρ : List (I × R)) (cont : List (Call P I)) (t : ℝ) :
    (scen off p₀ g ρ cont d t D).Admissible d u ε := by
  refine ⟨fun q r σ => ?_, hoff⟩
  simp only [scen, dl]
  split_ifs
  · constructor <;> linarith
  · exact hD q r

variable [DecidableEq P]

theorem D2_comm (i j : P) (d m : ℝ) : D2 j i d m = D2 i j d m := by
  funext q r
  unfold D2
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- The continuation of `R₁` (`t₁ = t₂ = t`, `τ₁ = τ₂ = τ`, `τ₃ = τ + m`) and of `R₂`
(`t₂ = t + m`, `τ₂ = τ + m`): `p_i` invokes `b₁` then `e₁`, `p_j` invokes `b₂` then `e₂`, `p_k`
invokes `e₃`. -/
def clist (i j k : P) (N : ℕ) (t₁ t₂ τ₁ τ₂ τ₃ : ℝ) (b₁ b₂ e₁ e₂ e₃ : I) : List (Call P I) :=
  [⟨i, N, t₁, b₁⟩, ⟨j, N, t₂, b₂⟩, ⟨i, N + 1, τ₁, e₁⟩, ⟨j, N + 1, τ₂, e₂⟩, ⟨k, N, τ₃, e₃⟩]

/-- The continuation of `R₂⁻` (`R₂` without the operations of `p_j`). -/
def clistm (i k : P) (N : ℕ) (t₁ τ₁ τ₃ : ℝ) (b₁ e₁ e₃ : I) : List (Call P I) :=
  [⟨i, N, t₁, b₁⟩, ⟨i, N + 1, τ₁, e₁⟩, ⟨k, N, τ₃, e₃⟩]

omit [DecidableEq P] in
theorem clist_swap_mem (i j k : P) (N : ℕ) (t τ τ' : ℝ) (b₁ b₂ e₁ e₂ e₃ : I) (c : Call P I) :
    c ∈ clist i j k N t t τ τ τ' b₁ b₂ e₁ e₂ e₃ ↔ c ∈ clist j i k N t t τ τ τ' b₂ b₁ e₂ e₁ e₃ := by
  simp only [clist, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Step 2 of the proof of Theorem E.1 (`restart` + shifting, as `step2_agree` of Theorem C.1):
`R₂` (offsets `off1 j m`, delays `D1`) and `R₁` (offsets `0`, delays `D2`), whose continuations
agree after shifting `p_j` by `-m`, have the same outputs at clock times in `[t, C p)` with
`C i = t + d - m`, `C j = t + 2d - 2m`, `C p = t + 2d - m` otherwise. -/
theorem restart_shift [Finite P] (A : Algorithm P I R M) {d u ε : ℝ}
    (hHO : HistoryOblivious A d u ε) {i j p₀ : P} (hij : i ≠ j) {m t g Tρ : ℝ}
    (hd : 0 < d) (hm0 : 0 ≤ m) (hm : 3 * m ≤ d) (ρ : List (I × R))
    (hT : Tρ + d + m ≤ t) (htρ : ρ.length * g ≤ t) (hg : 0 < g)
    {cont1 cont2 : List (Call P I)}
    (hc1 : ∀ c ∈ cont1, t - off1 j m c.p ≤ c.t) (hc2 : ∀ c ∈ cont2, t ≤ c.t)
    (hcc : cont2 = cont1.map fun c => { c with t := c.t + off1 j m c.p })
    {Hr1 Hr2 : P → Set (ℝ × InEv P I M)}
    (hr1 : RhoRun A d u ε (off1 j m) p₀ g ρ Tρ Hr1) (hr2 : RhoRun A d u ε 0 p₀ g ρ Tρ Hr2)
    {H1 H2 : P → Set (ℝ × InEv P I M)}
    (hH1 : IsRun A (scen (off1 j m) p₀ g ρ cont1 d t (D1 i j d m)) H1)
    (hH2 : IsRun A (scen 0 p₀ g ρ cont2 d t (D2 i j d m)) H2) :
    ∀ p (o : ℝ × OutEv P R M), t ≤ o.1 →
      o.1 < (if p = i then t + d - m else if p = j then t + 2 * d - 2 * m else t + 2 * d - m) →
      (o ∈ A.beh p (H1 p) ↔ o ∈ A.beh p (H2 p)) := by
  set s1 := (scen (off1 j m) p₀ g ρ cont1 d t (D1 i j d m) : Scenario P I) with hs1
  set s2 := (scen 0 p₀ g ρ cont2 d t (D2 i j d m) : Scenario P I) with hs2
  set s := s1.shift (off1 j m) with hs
  have hHs : IsRun A s H1 := IsRun.shift A hH1 _
  have hsoff : ∀ p, s.off p = 0 := fun p => by simp [hs, Scenario.shift, hs1, scen]
  have hoff : s.off = s2.off := funext fun p => by rw [hsoff]; rfl
  have hsdel : ∀ q r σ, t ≤ σ →
      s.delay q r σ = D1 i j d m q r + off1 j m r - off1 j m q := by
    intro q r σ hσ
    simp only [hs, Scenario.shift, hs1, scen]
    rw [dl_of_ge]
    linarith [(off1_bounds j hm0 q).2]
  have hsdel_le : ∀ q r σ, s.delay q r σ ≤ d + m := by
    intro q r σ
    simp only [hs, Scenario.shift, hs1, scen]
    have := dl_le (d := d) (t := t) (fun q r => D1_le i j d m hm0 q r) q r (σ - off1 j m q)
    linarith [(off1_bounds j hm0 r).2, (off1_bounds j hm0 q).1]
  have hγ : s.MinDelay (d - 2 * m) := by
    refine ⟨by linarith, fun q r σ => ?_⟩
    simp only [hs, Scenario.shift, hs1, scen]
    have := dl_ge (d := d) (t := t) (γ := d - m) (by linarith)
      (fun q r => D1_ge i j d m hm0 q r) q r (σ - off1 j m q)
    linarith [(off1_bounds j hm0 r).1, (off1_bounds j hm0 q).2]
  set C : P → ℝ := fun p =>
    if p = i then t + d - m else if p = j then t + 2 * d - 2 * m else t + 2 * d - m with hC
  have key := restart A hHO s s2 hoff hHs hH2 hγ (rho (off1 j m) p₀ g ρ d) (rho 0 p₀ g ρ d)
    hr1.adm hr2.adm hr1.run hr2.run hr1.wf hr2.wf hr1.solo hr2.solo (fun _ => t)
    (agree_rho A hd (off1_le j hm0) (fun q r => by
        linarith [D1_ge i j d m hm0 q r, (off1_bounds j hm0 r).1])
      (fun r => by linarith [(off1_bounds j hm0 r).1]) hc1 hH1 hr1.run)
    (agree_rho A hd (fun _ => le_rfl) (fun q r => by
        simp only [neg_zero]; linarith [D2_ge i j d m hm0 q r])
      (fun r => by simp only [neg_zero]; linarith)
      (fun c hc => by simpa using hc2 c hc) hH2 hr2.run)
    (fun p => ⟨fun e he => by
        have := (hr1.fin p).1 e he; linarith [(off1_bounds j hm0 p).2],
      fun o ho => by have := (hr1.fin p).2 o ho; linarith [(off1_bounds j hm0 p).2]⟩)
    (fun p => ⟨fun e he => by have := (hr2.fin p).1 e he; simp at this; linarith,
      fun o ho => by have := (hr2.fin p).2 o ho; simp at this; linarith⟩)
    (fun q r σ m' ho => by
      have h1 := (hr1.fin q).2 _ ho
      have := hsdel_le q r σ
      simp only at h1
      rw [hsoff, hsoff, sub_zero, sub_zero]
      linarith [(off1_bounds j hm0 q).2])
    (fun q r σ m' ho => by
      have h1 := (hr2.fin q).2 _ ho
      simp only [Pi.zero_apply, sub_zero] at h1
      have := dl_le (d := d) (t := t) (fun q r => D2_le i j d m hm0 q r) q r σ
      rw [hsoff, hsoff, sub_zero, sub_zero]
      simp only [hs2, scen] at this ⊢
      linarith)
    C ?_ ?_ ?_
  · intro p o h1 h2
    exact key.2 p o h1 (by rw [hsoff, sub_zero]; exact h2)
  · -- invocations
    intro p e h1 h2
    rw [Scenario.callEv_shift, hs1, hs2,
      callEv_scen hg htρ p e (by linarith [(off1_bounds j hm0 p).2]),
      callEv_scen hg htρ p e (by simp; linarith)]
    simp only [Pi.zero_apply, add_zero, hcc, List.mem_map]
    constructor
    · rintro ⟨c, hc, rfl, rfl⟩
      exact ⟨_, ⟨c, hc, rfl⟩, rfl, rfl⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl, rfl⟩
      exact ⟨c, hc, rfl, rfl⟩
  · -- delays in the windows
    intro q r σ hσ hσC
    rw [hsoff, sub_zero] at hσ
    rw [hsdel q r σ hσ]
    have e2 : s2.delay q r σ = D2 i j d m q r := dl_of_ge hσ q r
    rw [e2]
    simp only [hC, D1, D2, off1] at hσC ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;>
      first | linarith | (right; constructor <;> linarith) | (constructor <;> linarith)
  · -- the cut is causally closed
    intro q r σ hσ
    have hCt : t ≤ C q := by simp only [hC]; split_ifs <;> linarith
    have hσt : t ≤ σ := le_trans hCt hσ
    rw [hsdel q r σ hσt]
    have e2 : s2.delay q r σ = D2 i j d m q r := dl_of_ge hσt q r
    rw [e2]
    simp only [hC, D1, D2, off1] at hσ ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;> (try constructor) <;> linarith

/-- Step 2.2b of the proof of Theorem E.1 (as `alone_agree` of Theorem C.1): in runs with offsets
`off1 j m` and delays `D1` whose continuations differ only by invocations of `p_j` at times
`≥ t + m`, the process `p_i` has the same inputs before `t + d + m`. -/
theorem alone_gen [Finite P] (A : Algorithm P I R M) {i j p₀ : P} (hij : i ≠ j) {d m t g : ℝ}
    (hd : 0 < d) (hm0 : 0 ≤ m) (hm : 3 * m ≤ d) (ρ : List (I × R))
    {cont cont' : List (Call P I)} (hsame : ∀ c : Call P I, c.p ≠ j → (c ∈ cont ↔ c ∈ cont'))
    (hj : ∀ c ∈ cont, c.p = j → t + m ≤ c.t) (hj' : ∀ c ∈ cont', c.p = j → t + m ≤ c.t)
    {H H' : P → Set (ℝ × InEv P I M)}
    (hH : IsRun A (scen (off1 j m) p₀ g ρ cont d t (D1 i j d m)) H)
    (hH' : IsRun A (scen (off1 j m) p₀ g ρ cont' d t (D1 i j d m)) H') :
    ∀ e : ℝ × InEv P I M, e.1 < t + d + m → (e ∈ H i ↔ e ∈ H' i) := by
  set C : P → ℝ := fun p => if p = i then t + d + m else if p = j then t + m else t + d with hC
  have hγ : (scen (off1 j m) p₀ g ρ cont d t (D1 i j d m) : Scenario P I).MinDelay (d - m) := by
    refine ⟨by linarith, fun q r σ => dl_ge (by linarith) (fun q r => ?_) q r σ⟩
    rcases D1_eq i j d m q r with h | h <;> rw [h]; linarith
  have key := agree_of_cut A
    (scen (off1 j m) p₀ g ρ cont d t (D1 i j d m))
    (scen (off1 j m) p₀ g ρ cont' d t (D1 i j d m))
    rfl hH hH' hγ C ?_ (fun _ _ _ _ => Or.inl rfl) ?_
  · intro e he
    exact key i e (by simp [scen, C, off1_ne m hij]; linarith)
  · intro p e he
    have side : ∀ c : Call P I, t + m ≤ c.t → c.p = p →
        e = (c.t + off1 j m p, InEv.inv c.k c.a) → c.p ≠ j := by
      intro c hct hp he' hcj
      rw [he'] at he
      simp only [scen, add_sub_cancel_right] at he
      rw [← hp, hcj] at he
      simp only [hC, Ne.symm hij, ↓reduceIte] at he
      linarith
    simp only [Scenario.callEv, scen, Set.mem_ofPred_eq, List.mem_append]
    constructor
    · rintro ⟨c, hc | hc, hp, he'⟩
      · exact ⟨c, Or.inl hc, hp, he'⟩
      · by_cases hcj : c.p = j
        · exact absurd hcj (side c (hj c hc hcj) hp he')
        · exact ⟨c, Or.inr ((hsame c hcj).mp hc), hp, he'⟩
    · rintro ⟨c, hc | hc, hp, he'⟩
      · exact ⟨c, Or.inl hc, hp, he'⟩
      · by_cases hcj : c.p = j
        · exact absurd hcj (side c (hj' c hc hcj) hp he')
        · exact ⟨c, Or.inr ((hsame c hcj).mpr hc), hp, he'⟩
  · have hCt : ∀ q, t ≤ C q := fun q => by
      simp only [C]; split_ifs <;> linarith
    intro q r σ hσ
    simp only [scen]
    rw [dl_of_ge (le_trans (hCt q) hσ)]
    simp only [C, D1] at hσ ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;> (try constructor) <;> linarith

omit [DecidableEq P] in
/-- Well-formedness from per-operation time bounds (a variant of `wf_of_spaced`). -/
theorem wf_of_spaced' [Finite P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    {d u ε γ : ℝ} (hcor : Correct A legal d u ε)
    (s : Scenario P I) (hadm : s.Admissible d u ε) (hγ : s.MinDelay γ) (hnd : s.calls.Nodup)
    (hid : ∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.k = c'.k → c = c')
    (hsp : ∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c ≠ c' → c.t < c'.t →
      ∃ (Q : I → Prop) (B : ℝ), TimeBound A d u ε Q B ∧ Q c.a ∧ c.t + B < c'.t)
    (htm : ∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.t = c'.t → c = c') :
    ∀ H, IsRun A s H → WF A s H := by
  refine wf_of_trunc A _ s le_rfl hγ hnd hid htm ?_
  intro c hc c' hc' hp ht H₀ hH₀ hwf₀
  have hc₀ : c ∈ (s.trunc c'.t).calls := List.mem_filter.mpr ⟨hc, by simpa using ht⟩
  obtain ⟨rt, ret, hr, -⟩ := hcor _ H₀ (trunc_admissible hadm _) hH₀ hwf₀
  obtain ⟨h1, h2, -⟩ := hr c hc₀
  have hne : c ≠ c' := by rintro rfl; exact lt_irrefl _ ht
  obtain ⟨Q, B, hQB, hQ, hlt⟩ := hsp c hc c' hc' hp hne ht
  refine ⟨rt c, ret c, h2, h1, ?_⟩
  have := hQB _ H₀ (trunc_admissible hadm _) hH₀ hwf₀ c hc₀ hQ _ _ h2
  linarith

omit [DecidableEq P] in
/-- Well-formedness of a `ρ`-phase followed by a continuation whose operations of the same
process are spaced by their time bounds (a variant of `wf_rho_cont`). -/
theorem wf_gen [Finite P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    {d u ε Bop g γ : ℝ} (hcor : Correct A legal d u ε)
    (hB : TimeBound A d u ε (fun _ => True) Bop) (hg : Bop < g) (hg0 : 0 < g) {p₀ : P}
    {ρ : List (I × R)} {cont : List (Call P I)} (hnd' : cont.Nodup)
    (hid' : ∀ c ∈ cont, ∀ c' ∈ cont, c.p = c'.p → c.k = c'.k → c = c')
    (htm' : ∀ c ∈ cont, ∀ c' ∈ cont, c.p = c'.p → c.t = c'.t → c = c')
    (hsp' : ∀ c ∈ cont, ∀ c' ∈ cont, c.p = c'.p → c ≠ c' → c.t < c'.t →
      ∃ (Q : I → Prop) (B : ℝ), TimeBound A d u ε Q B ∧ Q c.a ∧ c.t + B < c'.t)
    (hck : ∀ c ∈ cont, ρ.length ≤ c.k) (hct : ∀ c ∈ cont, ρ.length * g ≤ c.t)
    (s : Scenario P I) (hs : s.calls = rhoCalls p₀ g ρ ++ cont) (hadm : s.Admissible d u ε)
    (hγ : s.MinDelay γ) : ∀ H, IsRun A s H → WF A s H := by
  have hρk : ∀ c ∈ rhoCalls p₀ g ρ, c.k < ρ.length := fun c hc => (mem_rhoCalls hc).2.1
  have hρt : ∀ c ∈ rhoCalls p₀ g ρ, c.t + Bop < ρ.length * g := fun c hc => by
    rw [(mem_rhoCalls hc).2.2]
    have : ((c.k + 1 : ℕ) : ℝ) ≤ ρ.length := by exact_mod_cast hρk c hc
    push_cast at this; nlinarith
  have hρt' : ∀ c ∈ rhoCalls p₀ g ρ, c.t < ρ.length * g := fun c hc => by
    rw [(mem_rhoCalls hc).2.2]
    have : ((c.k + 1 : ℕ) : ℝ) ≤ ρ.length := by exact_mod_cast hρk c hc
    push_cast at this; nlinarith
  have hρρ : ∀ c ∈ rhoCalls p₀ g ρ, ∀ c' ∈ rhoCalls p₀ g ρ, c.k = c'.k → c = c' := by
    intro c hc c' hc' hk
    by_contra hne
    have hpw : (rhoCalls p₀ g ρ).Pairwise (fun a b => a.k ≠ b.k) :=
      (pairwise_rhoCallsFrom 0 ρ).imp fun h => Nat.ne_of_lt h
    have : Std.Symm (fun a b : Call P I => a.k ≠ b.k) := ⟨fun a b h => Ne.symm h⟩
    exact hpw.forall hc hc' hne hk
  refine wf_of_spaced' A hcor s hadm hγ ?_ ?_ ?_ ?_
  · rw [hs]
    refine List.nodup_append.mpr ⟨nodup_rhoCalls p₀ g ρ, hnd', ?_⟩
    intro a ha b hb hab; subst hab; have := hρk a ha; have := hck a hb; omega
  · intro c hc c' hc' hp hk
    rw [hs, List.mem_append] at hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · exact hρρ c hc c' hc' hk
    · have := hρk c hc; have := hck c' hc'; omega
    · have := hρk c' hc'; have := hck c hc; omega
    · exact hid' c hc c' hc' hp hk
  · intro c hc c' hc' hp hne ht
    rw [hs, List.mem_append] at hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · refine ⟨fun _ => True, Bop, hB, trivial, ?_⟩
      rw [(mem_rhoCalls hc).2.2, (mem_rhoCalls hc').2.2] at ht ⊢
      have hk : c.k ≠ c'.k := fun h => hne (hρρ c hc c' hc' h)
      have hk' : c.k < c'.k := by
        rcases Nat.lt_or_gt_of_ne hk with h | h
        · exact h
        · exfalso
          have : (c'.k : ℝ) < c.k := by exact_mod_cast h
          nlinarith
      have : ((c.k + 1 : ℕ) : ℝ) ≤ c'.k := by exact_mod_cast hk'
      push_cast at this; nlinarith
    · exact ⟨fun _ => True, Bop, hB, trivial, by have := hρt c hc; have := hct c' hc'; linarith⟩
    · exfalso; have := hρt' c' hc'; have := hct c hc; linarith
    · exact hsp' c hc c' hc' hp hne ht
  · intro c hc c' hc' hp ht
    rw [hs, List.mem_append] at hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · rw [(mem_rhoCalls hc).2.2, (mem_rhoCalls hc').2.2] at ht
      have : (c.k : ℝ) = c'.k := by
        rcases mul_eq_mul_right_iff.mp ht with h | h
        · exact h
        · linarith
      exact hρρ c hc c' hc' (by exact_mod_cast this)
    · exfalso; have := hρt' c hc; have := hct c' hc'; linarith
    · exfalso; have := hρt' c' hc'; have := hct c hc; linarith
    · exact htm' c hc c' hc' hp ht

omit [DecidableEq P] in
/-- Well-formedness of the runs `R₁` and `R₂`. -/
theorem wf_clist [Finite P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    {d u ε Bop g γ B₁ : ℝ} {OP : I → Prop} (hcor : Correct A legal d u ε)
    (hBop : TimeBound A d u ε (fun _ => True) Bop) (hg : Bop < g) (hg0 : 0 < g)
    (hB₁ : TimeBound A d u ε OP B₁) {p₀ i j k : P} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {ρ : List (I × R)} {t₁ t₂ τ₁ τ₂ τ₃ : ℝ} {b₁ b₂ e₁ e₂ e₃ : I} (hb₁ : OP b₁) (hb₂ : OP b₂)
    (h1 : t₁ + B₁ < τ₁) (h2 : t₂ + B₁ < τ₂) (h1' : t₁ < τ₁) (h2' : t₂ < τ₂)
    (ht₁ : ρ.length * g ≤ t₁) (ht₂ : ρ.length * g ≤ t₂) (ht₃ : ρ.length * g ≤ τ₃)
    (s : Scenario P I)
    (hs : s.calls = rhoCalls p₀ g ρ ++ clist i j k ρ.length t₁ t₂ τ₁ τ₂ τ₃ b₁ b₂ e₁ e₂ e₃)
    (hadm : s.Admissible d u ε) (hγ : s.MinDelay γ) : ∀ H, IsRun A s H → WF A s H := by
  refine wf_gen A hcor hBop hg hg0 ?_ ?_ ?_ ?_ ?_ ?_ s hs hadm hγ
  · simp [clist, hij, hik, hjk, Ne.symm hij]
  · intro c hc c' hc' hp hk
    simp only [clist, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  · intro c hc c' hc' hp ht
    simp only [clist, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  · intro c hc c' hc' hp hne ht
    simp only [clist, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl | rfl <;>
      simp_all <;> first | linarith | exact ⟨OP, B₁, hB₁, by assumption, by linarith⟩
  · intro c hc
    simp only [clist, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro c hc
    simp only [clist, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp <;> linarith

omit [DecidableEq P] in
/-- Well-formedness of the run `R₂⁻`. -/
theorem wf_clistm [Finite P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    {d u ε Bop g γ B₁ : ℝ} {OP : I → Prop} (hcor : Correct A legal d u ε)
    (hBop : TimeBound A d u ε (fun _ => True) Bop) (hg : Bop < g) (hg0 : 0 < g)
    (hB₁ : TimeBound A d u ε OP B₁) {p₀ i k : P} (hik : i ≠ k)
    {ρ : List (I × R)} {t₁ τ₁ τ₃ : ℝ} {b₁ e₁ e₃ : I} (hb₁ : OP b₁)
    (h1 : t₁ + B₁ < τ₁) (h1' : t₁ < τ₁)
    (ht₁ : ρ.length * g ≤ t₁) (ht₃ : ρ.length * g ≤ τ₃)
    (s : Scenario P I)
    (hs : s.calls = rhoCalls p₀ g ρ ++ clistm i k ρ.length t₁ τ₁ τ₃ b₁ e₁ e₃)
    (hadm : s.Admissible d u ε) (hγ : s.MinDelay γ) : ∀ H, IsRun A s H → WF A s H := by
  refine wf_gen A hcor hBop hg hg0 ?_ ?_ ?_ ?_ ?_ ?_ s hs hadm hγ
  · simp [clistm, hik]
  · intro c hc c' hc' hp hk
    simp only [clistm, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;> simp_all
  · intro c hc c' hc' hp ht
    simp only [clistm, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;> simp_all
  · intro c hc c' hc' hp hne ht
    simp only [clistm, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;>
      simp_all <;> first | linarith | exact ⟨OP, B₁, hB₁, by assumption, by linarith⟩
  · intro c hc
    simp only [clistm, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp
  · intro c hc
    simp only [clistm, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp <;> linarith

/-- **Step 2 of the proof of Theorem E.1** (the case "`ρ ∘ op'_2 ∘ op'_1 ∘ aop'_3` legal" of
Step 1; the other case is the instance with `i ↔ j`, `o₁ ↔ o₂`, `a₁ ↔ a₂`, A ↔ B). Given the run
`R₁` (offsets `0`, delays `D2 i j`), in which `p_j`'s `op'_2` returns `o₂` and `p_k`'s `aop'_3`
returns `r₃` with `ρ ∘ o₁ ∘ o₂ ∘ (a₃.1, r₃)` illegal, the runs `R₂` and `R₂⁻` give a
contradiction. -/
theorem core [Fintype P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    (hpc : PrefixClosed legal) (hdet : Deterministic legal) {d u ε : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) (hcor : Correct A legal d u ε) {Bop : ℝ}
    (hBop : TimeBound A d u ε (fun _ => True) Bop) (hHO : HistoryOblivious A d u ε)
    {OP AOP : I → Prop} (hacc : NonMutator legal AOP) {ρ : List (I × R)} (hρ : legal ρ)
    {o₁ o₂ a₁ a₂ a₃ : I × R} (h₁ : OP o₁.1) (h₂ : OP o₂.1)
    (ha₁ : AOP a₁.1) (ha₂ : AOP a₂.1) (ha₃ : AOP a₃.1)
    (hl1 : legal (ρ ++ [o₁])) (hl21 : legal (ρ ++ [o₂, o₁]))
    (hA : ¬ (legal (ρ ++ [o₁, a₁]) ↔ legal (ρ ++ [o₂, o₁, a₁])))
    {r₃ : R} (hill : ¬ legal (ρ ++ [o₁, o₂, (a₃.1, r₃)]))
    {B₁ B₂ : ℝ} (hB₁ : TimeBound A d u ε OP B₁) (hB₂ : TimeBound A d u ε AOP B₂)
    (hB10 : 0 ≤ B₁) (hB20 : 0 ≤ B₂)
    {i j k p₀ : P} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {m t g Tρ τ : ℝ} (hm0 : 0 ≤ m) (hm3 : 3 * m ≤ d) (hmu : m ≤ u) (hmε : m ≤ ε)
    (hg0 : 0 < g) (hgB : Bop < g)
    (hT : Tρ + d + m ≤ t) (htρ : ρ.length * g ≤ t) (hτ1 : t + B₁ < τ)
    (hτ2 : τ + B₂ < t + d + m)
    {Hr1 Hr2 : P → Set (ℝ × InEv P I M)}
    (hr1 : RhoRun A d u ε (off1 j m) p₀ g ρ Tρ Hr1) (hr2 : RhoRun A d u ε 0 p₀ g ρ Tρ Hr2)
    {H1 : P → Set (ℝ × InEv P I M)}
    (hH1 : IsRun A (scen 0 p₀ g ρ (clist i j k ρ.length t t τ τ (τ + m) o₁.1 o₂.1 a₁.1 a₂.1 a₃.1)
      d t (D2 i j d m)) H1)
    {σ₂ σ₃ : ℝ} (hσ₂ : t ≤ σ₂) (hσ₂' : σ₂ ≤ t + B₁)
    (hR₂ : (σ₂, OutEv.resp ρ.length o₂.2) ∈ A.beh j (H1 j))
    (hσ₃ : τ + m ≤ σ₃) (hσ₃' : σ₃ ≤ τ + m + B₂)
    (hR₃ : (σ₃, OutEv.resp ρ.length r₃) ∈ A.beh k (H1 k)) : False := by
  classical
  set N := ρ.length with hN
  have hNg : (N : ℝ) * g ≤ t := htρ
  have hd' : 0 < d - m := by linarith
  have hsk : ∀ p q, |off1 j m p - off1 j m q| ≤ ε := fun p q =>
    (off1_skew j hm0 p q).trans hmε
  have hD1 : ∀ q r, d - u ≤ D1 i j d m q r ∧ D1 i j d m q r ≤ d := fun q r =>
    ⟨by linarith [D1_ge i j d m hm0 q r], D1_le i j d m hm0 q r⟩
  -- the run `R₂`
  set c2 := clist i j k N t (t + m) τ (τ + m) (τ + m) o₁.1 o₂.1 a₁.1 a₂.1 a₃.1 with hc2
  set s2 := (scen (off1 j m) p₀ g ρ c2 d t (D1 i j d m) : Scenario P I) with hs2
  have hγ2 : s2.MinDelay (d - m) :=
    ⟨hd', fun q r σ => dl_ge (by linarith) (D1_ge i j d m hm0) q r σ⟩
  have ha2 : s2.Admissible d u ε := scen_adm hu hsk hD1 p₀ g ρ c2 t
  obtain ⟨H2, hH2⟩ := exists_run A s2 hγ2
  have hw2 : WF A s2 H2 := wf_clist A hcor hBop hgB hg0 hB₁ hij hik hjk h₁ h₂ hτ1
    (by linarith) (by linarith) (by linarith) hNg (hNg.trans (by linarith))
    (hNg.trans (by linarith)) s2 rfl ha2 hγ2 H2 hH2
  obtain ⟨rt2, ret2, hr2c, -, L2, hL2p, hL2nd, hL2l, hL2rt⟩ := contLin A hpc hdet hcor hBop hgB
    hg0 hρ (cont := c2) (by
      intro c hc
      simp only [hc2, clist, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact hNg.trans (by dsimp only; linarith))
    s2 rfl ha2
    hH2 hw2
  -- the run `R₂⁻`
  set c2m := clistm i k N t τ (τ + m) o₁.1 a₁.1 a₃.1 with hc2m
  set s2m := (scen (off1 j m) p₀ g ρ c2m d t (D1 i j d m) : Scenario P I) with hs2m
  have hγ2m : s2m.MinDelay (d - m) :=
    ⟨hd', fun q r σ => dl_ge (by linarith) (D1_ge i j d m hm0) q r σ⟩
  have ha2m : s2m.Admissible d u ε := scen_adm hu hsk hD1 p₀ g ρ c2m t
  obtain ⟨H2m, hH2m⟩ := exists_run A s2m hγ2m
  have hw2m : WF A s2m H2m := wf_clistm A hcor hBop hgB hg0 hB₁ hik h₁ hτ1 (by linarith) hNg
    (hNg.trans (by linarith)) s2m rfl ha2m hγ2m H2m hH2m
  obtain ⟨rtm, retm, hrmc, -, Lm, hLmp, hLmnd, hLml, hLmrt⟩ := contLin A hpc hdet hcor hBop hgB
    hg0 hρ (cont := c2m) (by
      intro c hc
      simp only [hc2m, clistm, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> exact hNg.trans (by dsimp only; linarith)) s2m rfl ha2m
    hH2m hw2m
  -- calls
  set x1 : Call P I := ⟨i, N, t, o₁.1⟩ with hx1
  set x2 : Call P I := ⟨j, N, t + m, o₂.1⟩ with hx2
  set y1 : Call P I := ⟨i, N + 1, τ, a₁.1⟩ with hy1
  set y3 : Call P I := ⟨k, N, τ + m, a₃.1⟩ with hy3
  have mx1 : x1 ∈ c2 := by simp [hc2, clist, hx1]
  have mx2 : x2 ∈ c2 := by simp [hc2, clist, hx2]
  have my1 : y1 ∈ c2 := by simp [hc2, clist, hy1]
  have my3 : y3 ∈ c2 := by simp [hc2, clist, hy3]
  have ms : ∀ c ∈ c2, c ∈ s2.calls := fun c hc => List.mem_append_right _ hc
  have mmx1 : x1 ∈ c2m := by simp [hc2m, clistm, hx1]
  have mmy1 : y1 ∈ c2m := by simp [hc2m, clistm, hy1]
  have mms : ∀ c ∈ c2m, c ∈ s2m.calls := fun c hc => List.mem_append_right _ hc
  -- Step 2 (restart): `R₂` agrees with `R₁` at `p_j` and `p_k`
  have hag := restart_shift A hHO hij hd hm0 hm3 ρ hT htρ hg0 (cont1 := c2)
    (cont2 := clist i j k N t t τ τ (τ + m) o₁.1 o₂.1 a₁.1 a₂.1 a₃.1)
    (by
      intro c hc
      simp only [hc2, clist, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;>
        simp [off1, hij, Ne.symm hjk] <;> linarith)
    (by
      intro c hc
      simp only [clist, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp <;> linarith)
    (by simp [hc2, clist, off1, hij, Ne.symm hjk])
    hr1 hr2 hH2 hH1
  have hRx2 : RespAt A s2 H2 x2 (σ₂ + m) o₂.2 := by
    have := (hag j (σ₂, OutEv.resp N o₂.2) hσ₂
      (by simp [Ne.symm hij]; linarith)).mpr hR₂
    unfold RespAt
    simp only [hs2, scen, hx2, off1_self]
    convert this using 2
    ring
  have hRy3 : RespAt A s2 H2 y3 σ₃ r₃ := by
    have := (hag k (σ₃, OutEv.resp N r₃) (by linarith)
      (by simp [Ne.symm hik, Ne.symm hjk]; linarith)).mpr hR₃
    unfold RespAt
    simpa [hs2, scen, hy3, off1_ne m (Ne.symm hjk)] using this
  have ex2 : ret2 x2 = o₂.2 := ((hr2c _ (ms _ mx2)).2.2 _ _ hRx2).2.symm
  have ey3 : ret2 y3 = r₃ := ((hr2c _ (ms _ my3)).2.2 _ _ hRy3).2.symm
  -- Step 2.2b: in `R₂⁻`, `ρ ∘ o₁ ∘ aop''_1` is legal
  have hbm := hB₁ _ H2m ha2m hH2m hw2m _ (mms _ mmx1) h₁ _ _ (hrmc _ (mms _ mmx1)).2.1
  have hsubm : [x1, y1].Sublist Lm := hLmrt x1 mmx1 y1 mmy1 (by simp [hx1, hy1] at hbm ⊢; linarith)
  have hlm := extract hpc hacc (fun c => (c.a, retm c)) hLml hLmnd hsubm (by
    intro c hc hX
    rw [hLmp.mem_iff] at hc
    simp only [hc2m, clistm, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp [hx1, hy1] at hX
    · simp [hx1, hy1] at hX
    · exact ha₃)
  simp only [List.map_cons, List.map_nil, hx1, hy1] at hlm
  have em1 : retm x1 = o₁.2 := hdet ρ o₁.1 _ _ (hpc _ [_] (by simpa using hlm)) (by simpa using hl1)
  rw [em1] at hlm
  have hby1 := hB₂ _ H2m ha2m hH2m hw2m _ (mms _ mmy1) ha₁ _ _ (hrmc _ (mms _ mmy1)).2.1
  have hal := alone_gen A hij hd hm0 hm3 ρ (cont := c2m) (cont' := c2) (g := g) (p₀ := p₀)
    (by
      intro c hcj
      simp only [hc2m, hc2, clistm, clist, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl | rfl) <;> simp
      · rintro (rfl | rfl | rfl | rfl | rfl)
        · simp
        · exact absurd rfl hcj
        · simp
        · exact absurd rfl hcj
        · simp)
    (by
      intro c hc hcj
      simp only [hc2m, clistm, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        first | exact absurd hcj hij | exact absurd hcj (Ne.symm hjk))
    (by
      intro c hc hcj
      simp only [hc2, clist, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd hcj hij | exact absurd hcj (Ne.symm hjk) | exact le_rfl |
          (dsimp only; linarith))
    hH2m hH2
  have hRy1 : RespAt A s2 H2 y1 (rtm y1) (retm y1) :=
    (respAt_congr (s := s2m) (s' := s2) rfl (T := t + d + m)
      (fun e he => hal e (by simpa [hs2m, scen, hy1, off1_ne m hij] using he))
      (by simp [hy1] at hby1; linarith)).mp (hrmc _ (mms _ mmy1)).2.1
  have ey1 : ret2 y1 = retm y1 := ((hr2c _ (ms _ my1)).2.2 _ _ hRy1).2.symm
  have hbad : ¬ legal (ρ ++ [o₂, o₁, (a₁.1, retm y1)]) := by
    have h := det_flip hdet (x := ρ ++ [o₂, o₁]) (y := ρ ++ [o₁]) (a := a₁)
      (fun h => hA (by simpa using h.symm)) (r := retm y1) (by simpa using hlm)
    simpa using h
  -- the linearization of `R₂`
  -- the linearization of `R₂`
  have hb1 := hB₁ _ H2 ha2 hH2 hw2 _ (ms _ mx1) h₁ _ _ (hr2c _ (ms _ mx1)).2.1
  have hb2 := hB₁ _ H2 ha2 hH2 hw2 _ (ms _ mx2) h₂ _ _ (hr2c _ (ms _ mx2)).2.1
  have hx12 : x1 ≠ x2 := by simp [hx1, hx2, hij]
  have hdrop : ∀ X : List (Call P I), (∀ c ∈ c2, c ∉ X → AOP c.a) →
      ∀ c ∈ L2, c ∉ X → AOP ((fun c => (c.a, ret2 c)) c).1 :=
    fun X h c hc hX => h c (hL2p.mem_iff.mp hc) hX
  rcases pair_order (hL2p.mem_iff.mpr mx1) (hL2p.mem_iff.mpr mx2) hx12 with h12 | h21
  · -- `op''_1` before `op'_2`: `ρ ∘ o₁ ∘ o₂ ∘ aop'_3` would be legal
    have h23 : [x2, y3].Sublist L2 :=
      hL2rt x2 mx2 y3 my3 (by simp [hx2, hy3] at hb2 ⊢; linarith)
    have hl := extract hpc hacc (fun c => (c.a, ret2 c)) hL2l hL2nd (sub3 h12 h23 hL2nd)
      (hdrop _ (by
        intro c hc hX
        simp only [hc2, clist, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        · simp [hx1] at hX
        · simp [hx2] at hX
        · exact ha₁
        · exact ha₂
        · simp [hy3] at hX))
    simp only [List.map_cons, List.map_nil] at hl
    rw [ex2, ey3] at hl
    have hl' : legal (ρ ++ [(o₁.1, ret2 x1), (o₂.1, o₂.2), (a₃.1, r₃)]) := hl
    have e1 : ret2 x1 = o₁.2 :=
      hdet ρ o₁.1 _ _ (hpc _ [(o₂.1, o₂.2), (a₃.1, r₃)] (by simpa using hl'))
        (by simpa using hl1)
    rw [e1] at hl'
    exact hill (by simpa using hl')
  · -- `op'_2` before `op''_1`: `ρ ∘ o₂ ∘ o₁ ∘ aop''_1` would be legal
    have h1y : [x1, y1].Sublist L2 :=
      hL2rt x1 mx1 y1 my1 (by simp [hx1, hy1] at hb1 ⊢; linarith)
    have hl := extract hpc hacc (fun c => (c.a, ret2 c)) hL2l hL2nd (sub3 h21 h1y hL2nd)
      (hdrop _ (by
        intro c hc hX
        simp only [hc2, clist, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        · simp [hx1] at hX
        · simp [hx2] at hX
        · simp [hy1] at hX
        · exact ha₂
        · exact ha₃))
    simp only [List.map_cons, List.map_nil] at hl
    rw [ex2, ey1] at hl
    have hl' : legal (ρ ++ [(o₂.1, o₂.2), (o₁.1, ret2 x1), (a₁.1, retm y1)]) := hl
    have e1 : ret2 x1 = o₁.2 :=
      hdet (ρ ++ [o₂]) o₁.1 _ _ (hpc _ [(a₁.1, retm y1)] (by simpa using hl'))
        (by simpa using hl21)
    rw [e1] at hl'
    exact hbad (by simpa using hl')

end

end E1

open E1 C1 in
/-- **Theorem E.1 of Chapter IV** of the thesis (Wang–Welch–Lee, PODC 2011). -/
theorem theorem_E1 [Fintype P] [DecidableEq P] (A : Algorithm P I R M)
    {legal : List (I × R) → Prop} (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    {d u ε : ℝ} (hd : 0 < d) (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (hcor : Correct A legal d u ε) {Bop : ℝ} (hBop : TimeBound A d u ε (fun _ => True) Bop)
    (hfin : FiniteRuns A d u ε) (hHO : HistoryOblivious A d u ε)
    (hn : 3 ≤ Fintype.card P) {OP AOP : I → Prop} (hsc : ImmSelfCommuting legal OP)
    (hacc : NonMutator legal AOP) (ρ : List (I × R)) (o₁ o₂ a₁ a₂ a₃ : I × R)
    (h₁ : OP o₁.1) (h₂ : OP o₂.1) (ha₁ : AOP a₁.1) (ha₂ : AOP a₂.1) (ha₃ : AOP a₃.1)
    (hA : ¬ (legal (ρ ++ [o₁, a₁]) ↔ legal (ρ ++ [o₂, o₁, a₁])))
    (hB : ¬ (legal (ρ ++ [o₂, a₂]) ↔ legal (ρ ++ [o₁, o₂, a₂])))
    (hC : ¬ (legal (ρ ++ [o₁, o₂, a₃]) ↔ legal (ρ ++ [o₂, o₁, a₃])))
    {B₁ B₂ : ℝ} (hB₁ : TimeBound A d u ε OP B₁) (hB₂ : TimeBound A d u ε AOP B₂) :
    d + min ε (min u (d / 3)) ≤ B₁ + B₂ := by
  classical
  by_contra hlt
  push Not at hlt
  set m := min ε (min u (d / 3)) with hmdef
  have hm0 : 0 ≤ m := le_min hε (le_min hu (by linarith))
  have hmε : m ≤ ε := min_le_left _ _
  have hmu : m ≤ u := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : 3 * m ≤ d := by
    have := (min_le_right ε _).trans (min_le_right u (d / 3)); linarith
  obtain ⟨i, j, k, hij, hik, hjk⟩ := Fintype.two_lt_card_iff.mp (by omega : 2 < Fintype.card P)
  have hρ : legal ρ := by
    by_cases h : legal (ρ ++ [o₁, o₂, a₃])
    · exact hpc ρ _ h
    · exact hpc ρ [o₂, o₁, a₃] (by tauto)
  set g := max Bop 0 + 1 with hgdef
  have hg0 : 0 < g := by have := le_max_right Bop 0; linarith
  have hgB : Bop < g := by have := le_max_left Bop 0; linarith
  set N := ρ.length with hN
  have sk0 : ∀ p q, |(0 : P → ℝ) p - (0 : P → ℝ) q| ≤ ε := fun p q => by simpa using hε
  have skj : ∀ p q, |off1 j m p - off1 j m q| ≤ ε := fun p q => (off1_skew j hm0 p q).trans hmε
  have ski : ∀ p q, |off1 i m p - off1 i m q| ≤ ε := fun p q => (off1_skew i hm0 p q).trans hmε
  -- the `ρ`-only runs
  obtain ⟨T0, Hr0, hr0⟩ := rho_run A hpc hdet hcor hBop hfin hgB hg0 hd hu sk0 i hρ
  obtain ⟨TJ, HrJ, hrJ⟩ := rho_run A hpc hdet hcor hBop hfin hgB hg0 hd hu skj i hρ
  obtain ⟨TI, HrI, hrI⟩ := rho_run A hpc hdet hcor hBop hfin hgB hg0 hd hu ski i hρ
  set Tρ := max (max T0 TJ) TI with hTρ
  have hT0 : T0 ≤ Tρ := (le_max_left _ _).trans (le_max_left _ _)
  have hTJ : TJ ≤ Tρ := (le_max_right _ _).trans (le_max_left _ _)
  have hTI : TI ≤ Tρ := le_max_right _ _
  set t := |Tρ| + N * g + d + 2 * m + 1 with htdef
  have hNg : 0 ≤ (N : ℝ) * g := by positivity
  have hT : Tρ + d + m ≤ t := by have := le_abs_self Tρ; linarith
  have htρ : (N : ℝ) * g ≤ t := by have := abs_nonneg Tρ; linarith
  -- totality (an operation alone after `ρ` gets a legal answer) and `0 ≤ B₁`
  have tot : ∀ a : I, ∃ r : R, legal (ρ ++ [(a, r)]) ∧ (OP a → 0 ≤ B₁) := by
    intro a
    obtain ⟨H, hH, hw, ha⟩ := scen_run A hcor hBop hgB hg0 hu sk0 (D := fun _ _ => d)
      (fun _ _ => ⟨by linarith, le_rfl⟩) hd le_rfl (fun _ _ => le_rfl) (p₀ := i) (ρ := ρ)
      (cont := [⟨i, N, t, a⟩]) (by simp) (by simp [hN]) (by simpa using htρ) t
    obtain ⟨rt, ret, hr, -, L, hLp, -, hLl, -⟩ := contLin A hpc hdet hcor hBop hgB hg0 hρ
      (cont := [⟨i, N, t, a⟩]) (by simpa using htρ) _ rfl ha hH hw
    have hmem : (⟨i, N, t, a⟩ : Call P I) ∈
        (scen 0 i g ρ [⟨i, N, t, a⟩] d t fun _ _ => d : Scenario P I).calls := by simp [scen]
    refine ⟨ret ⟨i, N, t, a⟩, ?_, fun hOP => ?_⟩
    · rw [List.perm_singleton.mp hLp] at hLl; simpa using hLl
    · have h1 : t ≤ rt ⟨i, N, t, a⟩ := (hr _ hmem).1
      have h2 : rt ⟨i, N, t, a⟩ ≤ t + B₁ := hB₁ _ H ha hH hw _ hmem hOP _ _ (hr _ hmem).2.1
      linarith
  have hB10 : 0 ≤ B₁ := ((tot o₁.1).choose_spec).2 h₁
  -- Step 0 (a gap in the thesis): both `ρ ∘ o₁ ∘ o₂` and `ρ ∘ o₂ ∘ o₁` are legal
  have both : legal (ρ ++ [o₁, o₂]) ∧ legal (ρ ++ [o₂, o₁]) := by
    obtain ⟨r1, hr1, -⟩ := tot o₁.1
    obtain ⟨r2, hr2, -⟩ := tot o₂.1
    by_cases h : legal (ρ ++ [o₁, o₂, a₃])
    · have l12 : legal (ρ ++ [o₁, o₂]) := hpc _ [a₃] (by simpa using h)
      have l1 : legal (ρ ++ [o₁]) := hpc _ [o₂] (by simpa using l12)
      have hc := (hsc.comm (o₁ := o₁) (o₂ := (o₂.1, r2)) h₁ h₂ l1 hr2).1
      have e : r2 = o₂.2 :=
        hdet (ρ ++ [o₁]) o₂.1 r2 o₂.2 (by simpa using hc) (by simpa using l12)
      subst e
      exact hsc.comm h₁ h₂ l1 (by simpa using hr2)
    · have h' : legal (ρ ++ [o₂, o₁, a₃]) := by tauto
      have l21 : legal (ρ ++ [o₂, o₁]) := hpc _ [a₃] (by simpa using h')
      have l2 : legal (ρ ++ [o₂]) := hpc _ [o₁] (by simpa using l21)
      have hc := (hsc.comm (o₁ := o₂) (o₂ := (o₁.1, r1)) h₂ h₁ l2 hr1).1
      have e : r1 = o₁.2 :=
        hdet (ρ ++ [o₂]) o₁.1 r1 o₁.2 (by simpa using hc) (by simpa using l21)
      subst e
      exact (hsc.comm h₂ h₁ l2 (by simpa using hr1)).symm
  obtain ⟨hl12, hl21⟩ := both
  have hl1 : legal (ρ ++ [o₁]) := hpc _ [o₂] (by simpa using hl12)
  have hl2 : legal (ρ ++ [o₂]) := hpc _ [o₁] (by simpa using hl21)
  -- the run `R₁`
  set η := (d + m - (B₁ + B₂)) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set τ := t + B₁ + η with hτ
  set c1 := clist i j k N t t τ τ (τ + m) o₁.1 o₂.1 a₁.1 a₂.1 a₃.1 with hc1
  set s1 := (scen 0 i g ρ c1 d t (D2 i j d m) : Scenario P I) with hs1
  have hD2 : ∀ q r, d - u ≤ D2 i j d m q r ∧ D2 i j d m q r ≤ d := fun q r =>
    ⟨by linarith [D2_ge i j d m hm0 q r], D2_le i j d m hm0 q r⟩
  have hγ1 : s1.MinDelay (d - m) :=
    ⟨by linarith, fun q r σ => dl_ge (by linarith) (D2_ge i j d m hm0) q r σ⟩
  have ha1 : s1.Admissible d u ε := scen_adm hu sk0 hD2 i g ρ c1 t
  obtain ⟨H1, hH1⟩ := exists_run A s1 hγ1
  have hw1 : WF A s1 H1 := wf_clist A hcor hBop hgB hg0 hB₁ hij hik hjk h₁ h₂ (by linarith)
    (by linarith) (by linarith) (by linarith) htρ htρ (htρ.trans (by linarith)) s1 rfl ha1 hγ1
    H1 hH1
  obtain ⟨rt1, ret1, hr1c, -, L1, hL1p, hL1nd, hL1l, hL1rt⟩ := contLin A hpc hdet hcor hBop hgB
    hg0 hρ (cont := c1) (by
      intro c hc
      simp only [hc1, clist, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact htρ.trans (by dsimp only; linarith))
    s1 rfl ha1 hH1 hw1
  set x1 : Call P I := ⟨i, N, t, o₁.1⟩ with hx1
  set x2 : Call P I := ⟨j, N, t, o₂.1⟩ with hx2
  set y3 : Call P I := ⟨k, N, τ + m, a₃.1⟩ with hy3
  have mx1 : x1 ∈ c1 := by simp [hc1, clist, hx1]
  have mx2 : x2 ∈ c1 := by simp [hc1, clist, hx2]
  have my3 : y3 ∈ c1 := by simp [hc1, clist, hy3]
  have ms : ∀ c ∈ c1, c ∈ s1.calls := fun c hc => List.mem_append_right _ hc
  have t1a : t ≤ rt1 x1 := (hr1c _ (ms _ mx1)).1
  have t1b : rt1 x1 ≤ t + B₁ := hB₁ _ H1 ha1 hH1 hw1 _ (ms _ mx1) h₁ _ _ (hr1c _ (ms _ mx1)).2.1
  have t2a : t ≤ rt1 x2 := (hr1c _ (ms _ mx2)).1
  have t2b : rt1 x2 ≤ t + B₁ := hB₁ _ H1 ha1 hH1 hw1 _ (ms _ mx2) h₂ _ _ (hr1c _ (ms _ mx2)).2.1
  have t3a : τ + m ≤ rt1 y3 := (hr1c _ (ms _ my3)).1
  have t3b : rt1 y3 ≤ τ + m + B₂ :=
    hB₂ _ H1 ha1 hH1 hw1 _ (ms _ my3) ha₃ _ _ (hr1c _ (ms _ my3)).2.1
  have hB20 : 0 ≤ B₂ := by linarith
  have hR1 : (rt1 x1 + (0 : P → ℝ) i, OutEv.resp N (ret1 x1)) ∈ A.beh i (H1 i) :=
    (hr1c _ (ms _ mx1)).2.1
  have hR2 : (rt1 x2 + (0 : P → ℝ) j, OutEv.resp N (ret1 x2)) ∈ A.beh j (H1 j) :=
    (hr1c _ (ms _ mx2)).2.1
  have hR3 : (rt1 y3 + (0 : P → ℝ) k, OutEv.resp N (ret1 y3)) ∈ A.beh k (H1 k) :=
    (hr1c _ (ms _ my3)).2.1
  simp only [Pi.zero_apply, add_zero] at hR1 hR2 hR3
  have hdrop : ∀ X : List (Call P I), x1 ∈ X → x2 ∈ X → y3 ∈ X →
      ∀ c ∈ L1, c ∉ X → AOP ((fun c => (c.a, ret1 c)) c).1 := by
    intro X h1 h2 h3 c hc hX
    rw [hL1p.mem_iff] at hc
    simp only [hc1, clist, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact absurd h1 hX
    · exact absurd h2 hX
    · exact ha₁
    · exact ha₂
    · exact absurd h3 hX
  have hx12 : x1 ≠ x2 := by simp [hx1, hx2, hij]
  rcases pair_order (hL1p.mem_iff.mpr mx1) (hL1p.mem_iff.mpr mx2) hx12 with h12 | h21
  · -- Step 1, case `ρ ∘ o₁ ∘ o₂ ∘ aop'_3` legal: the instance of `core` with `i ↔ j`
    have h23 : [x2, y3].Sublist L1 := hL1rt x2 mx2 y3 my3 (by show rt1 x2 < τ + m; linarith)
    have hl := extract hpc hacc (fun c => (c.a, ret1 c)) hL1l hL1nd (sub3 h12 h23 hL1nd)
      (hdrop _ (by simp) (by simp) (by simp))
    simp only [List.map_cons, List.map_nil] at hl
    have hl' : legal (ρ ++ [(o₁.1, ret1 x1), (o₂.1, ret1 x2), (a₃.1, ret1 y3)]) := hl
    have e1 : ret1 x1 = o₁.2 := hdet ρ o₁.1 _ _
      (hpc _ [(o₂.1, ret1 x2), (a₃.1, ret1 y3)] (by simpa using hl')) (by simpa using hl1)
    rw [e1] at hl' hR1
    have e2 : ret1 x2 = o₂.2 := hdet (ρ ++ [o₁]) o₂.1 _ _
      (hpc _ [(a₃.1, ret1 y3)] (by simpa using hl')) (by simpa using hl12)
    rw [e2] at hl'
    have hill : ¬ legal (ρ ++ [o₂, o₁, (a₃.1, ret1 y3)]) := by
      have h := det_flip hdet (x := ρ ++ [o₂, o₁]) (y := ρ ++ [o₁, o₂]) (a := a₃)
        (fun h => hC (by simpa using h.symm)) (r := ret1 y3) (by simpa using hl')
      simpa using h
    have hH1' : IsRun A (scen 0 i g ρ (clist j i k N t t τ τ (τ + m) o₂.1 o₁.1 a₂.1 a₁.1 a₃.1)
        d t (D2 j i d m)) H1 :=
      isRun_of_mem A (s := s1) (s' := scen 0 i g ρ
        (clist j i k N t t τ τ (τ + m) o₂.1 o₁.1 a₂.1 a₁.1 a₃.1) d t (D2 j i d m)) rfl
        (by simp only [hs1, scen, D2_comm]) (by
        intro c
        simp only [hs1, hc1, scen, List.mem_append, clist_swap_mem]) hH1
    exact core A hpc hdet hd hu hcor hBop hHO hacc hρ h₂ h₁ ha₂ ha₁ ha₃ hl2 hl12 hB hill hB₁ hB₂
      hB10 hB20 (Ne.symm hij) hjk hik hm0 hm3 hmu hmε hg0 hgB hT htρ (by linarith)
      (by linarith) (hrI Tρ hTI) (hr0 Tρ hT0) hH1' t1a t1b hR1 t3a t3b hR3
  · -- Step 1, case `ρ ∘ o₂ ∘ o₁ ∘ aop'_3` legal
    have h13 : [x1, y3].Sublist L1 := hL1rt x1 mx1 y3 my3 (by show rt1 x1 < τ + m; linarith)
    have hl := extract hpc hacc (fun c => (c.a, ret1 c)) hL1l hL1nd (sub3 h21 h13 hL1nd)
      (hdrop _ (by simp) (by simp) (by simp))
    simp only [List.map_cons, List.map_nil] at hl
    have hl' : legal (ρ ++ [(o₂.1, ret1 x2), (o₁.1, ret1 x1), (a₃.1, ret1 y3)]) := hl
    have e2 : ret1 x2 = o₂.2 := hdet ρ o₂.1 _ _
      (hpc _ [(o₁.1, ret1 x1), (a₃.1, ret1 y3)] (by simpa using hl')) (by simpa using hl2)
    rw [e2] at hl' hR2
    have e1 : ret1 x1 = o₁.2 := hdet (ρ ++ [o₂]) o₁.1 _ _
      (hpc _ [(a₃.1, ret1 y3)] (by simpa using hl')) (by simpa using hl21)
    rw [e1] at hl'
    have hill : ¬ legal (ρ ++ [o₁, o₂, (a₃.1, ret1 y3)]) := by
      have h := det_flip hdet (x := ρ ++ [o₁, o₂]) (y := ρ ++ [o₂, o₁]) (a := a₃)
        (by simpa using hC) (r := ret1 y3) (by simpa using hl')
      simpa using h
    exact core A hpc hdet hd hu hcor hBop hHO hacc hρ h₁ h₂ ha₁ ha₂ ha₃ hl1 hl21 hA hill hB₁ hB₂
      hB10 hB20 hij hik hjk hm0 hm3 hmu hmε hg0 hgB hT htρ (by linarith)
      (by linarith) (hrJ Tρ hTJ) (hr0 Tρ hT0) hH1 t2a t2b hR2 t3a t3b hR3

end Podc.SharedObjectTimeBounds
