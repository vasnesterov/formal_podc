import Papers.PODC2017.DelayedTimestamps.LowerBounds

/-!
# Appendix B.2: an online algorithm with `n − 1` real entries

The algorithm of Appendix B.2 for the star graph, generalized to any graph with a cut vertex `c`
playing the role of the central process `p_0` (this is the upper bound claimed at the end of
Appendix B.3.2). Vectors are indexed by the processes other than `c` (`n − 1` entries). Each
process keeps a vector `v` (initially `0`); at each event it merges the vector piggybacked on a
received message (pointwise max) and then applies `update`:

* a process `p_k ≠ c` sets `v[k] := ⌊v[k] + 1⌋` (the next integer);
* the cut vertex `c` replaces every `v[j]` by "any value in the open interval
  `(v[j], ⌊v[j] + 1⌋)`" — modelled by an arbitrary choice function `pick` (which may depend on the
  position of the event, the coordinate and the old value) with `x < pick x < ⌊x⌋ + 1`.

The paper omits the correctness proof ("straightforward"). We prove it (`starAlg_captures`):
`⌊v[k]⌋` is the vector clock entry of `p_k` (`floor_ts`), and an event `e` of `c` is detected via
a coordinate `i` in another component of `G − c` than the process of `f`, whose value can reach
`f` only through `c` (`ts_cut_invariant`).
-/

namespace Podc.DelayedTimestamps

open Cslib.Causality

set_option linter.unusedSectionVars false

variable {P : Type*} [DecidableEq P] (c : P)

/-- The coordinates: processes other than `c`. -/
abbrev Coord := {p : P // p ≠ c}

/-- The algorithm of Appendix B.2 (`c` = the central process, `pick` = the choice of a value in
the open interval at `c`). -/
noncomputable def starAlg (pick : ℕ → Coord c → ℝ → ℝ) : MergeAlg P (Coord c → ℝ) where
  init := 0
  upd j a w := if h : a.proc = c then fun i => pick j i (w i)
    else Function.update w ⟨a.proc, h⟩ (⌊w ⟨a.proc, h⟩⌋ + 1)

/-- The integer shadow of `starAlg`: the vector clock restricted to processes other than `c`. -/
def shadowAlg : MergeAlg P (Coord c → ℤ) where
  init := 0
  upd _ a w := if h : a.proc = c then w else Function.update w ⟨a.proc, h⟩ (w ⟨a.proc, h⟩ + 1)

variable {c} {pick : ℕ → Coord c → ℝ → ℝ}

/-- `pick` chooses a value in the open interval `(x, ⌊x + 1⌋)`. -/
def PickSpec (pick : ℕ → Coord c → ℝ → ℝ) : Prop :=
  ∀ j i x, x < pick j i x ∧ pick j i x < ⌊x⌋ + 1

lemma shadow_eq_vc (ex : Exec P) (j : ℕ) (i : Coord c) :
    (shadowAlg c).ts ex j i = (ex.vc j i.1 : ℤ) := by
  have h := MergeAlg.ts_map (A := vcAlg P) (B := shadowAlg c) (fun v i => (v i.1 : ℤ))
    (by funext i; simp [vcAlg, shadowAlg])
    (by intro x y; funext i; simp)
    (by
      intro j a x
      funext i
      simp only [vcAlg, shadowAlg, Pi.add_apply]
      split_ifs with h
      · rw [Pi.single_eq_of_ne (by rw [h]; exact i.2)]; simp
      · by_cases hi : i = ⟨a.proc, h⟩
        · subst hi; simp
        · rw [Function.update_of_ne hi, Pi.single_eq_of_ne (fun e => hi (Subtype.ext e))]
          simp)
    ex j
  rw [h]; rfl

lemma floor_ts (hpick : PickSpec pick) (ex : Exec P) (j : ℕ) (i : Coord c) :
    ⌊(starAlg c pick).ts ex j i⌋ = (ex.vc j i.1 : ℤ) := by
  have h := MergeAlg.ts_map (A := starAlg c pick) (B := shadowAlg c) (fun w i => ⌊w i⌋)
    (by funext i; simp [starAlg, shadowAlg])
    (by intro x y; funext i; exact Int.floor_mono.map_max)
    (by
      intro j a x
      funext i
      simp only [starAlg, shadowAlg]
      split_ifs with h
      · exact Int.floor_eq_iff.2 ⟨(Int.floor_le _).trans (hpick j i (x i)).1.le,
          (hpick j i (x i)).2⟩
      · by_cases hi : i = ⟨a.proc, h⟩
        · subst hi; simp
        · simp [Function.update_of_ne hi])
    ex j
  rw [← shadow_eq_vc]
  exact (congrFun h i).symm

lemma starAlg_upd_lt [Nontrivial P] (hpick : PickSpec pick) (j : ℕ) (a : Act P)
    (w : Coord c → ℝ) : w < (starAlg c pick).upd j a w := by
  simp only [starAlg]
  split_ifs with h
  · obtain ⟨p, hp⟩ := exists_ne c
    exact Pi.lt_def.2 ⟨fun i => (hpick j i (w i)).1.le, ⟨p, hp⟩, (hpick j _ _).1⟩
  · refine Pi.lt_def.2 ⟨fun i => ?_, ⟨a.proc, h⟩, ?_⟩
    · by_cases hi : i = ⟨a.proc, h⟩
      · subst hi; simp [(Int.lt_floor_add_one _).le]
      · simp [Function.update_of_ne hi]
    · simp [Int.lt_floor_add_one]

variable {ex : Exec P}

lemma starAlg_nonneg (hpick : PickSpec pick) (j : ℕ) : 0 ≤ (starAlg c pick).ts ex j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < ex.length
    · rw [(starAlg c pick).ts_eq ex (List.getElem?_eq_getElem hj)]
      have h0 : 0 ≤ (starAlg c pick).inVal ex j := by
        unfold MergeAlg.inVal
        cases h : ex.prev j with
        | none => exact le_rfl
        | some i => exact ih i (Exec.prev_spec h).1
      have hm := h0.trans (MergeAlg.inVal_le_merged (A := starAlg c pick) ex j)
      refine hm.trans fun i => ?_
      simp only [starAlg]
      split_ifs with h
      · exact (hpick _ _ _).1.le
      · by_cases hi : i = ⟨ex[j].proc, h⟩
        · subst hi; simp [(Int.lt_floor_add_one _).le]
        · simp [Function.update_of_ne hi]
    · rw [(starAlg c pick).ts_of_length_le ex (not_lt.1 hj)]
      exact le_rfl

/-- At an event of `c`, every coordinate strictly exceeds the merged value. -/
lemma merged_lt_of_center (hpick : PickSpec pick) {e : ℕ} (he : ex.procAt e = some c)
    (i : Coord c) : (starAlg c pick).merged ex e i < (starAlg c pick).ts ex e i := by
  obtain ⟨a, ha, hac⟩ := Exec.procAt_eq_some.1 he
  rw [(starAlg c pick).ts_eq ex ha]
  simp only [starAlg, hac, ↓reduceDIte]
  exact (hpick _ _ _).1

/-- Information about a coordinate `i` lying in another component of `G − c` than `x` reaches
the events of `x` only through `c`. -/
lemma ts_cut_invariant {G : SimpleGraph P} (hwf : ex.WF) (hG : ex.OnGraph G) (f : ℕ) {x : P}
    (hx : x ≠ c) (hfx : ex.procAt f = some x) (i : Coord c)
    (hxi : ¬ G.ReachableAvoiding {c} x i.1) :
    (starAlg c pick).ts ex f i = 0 ∨
      ∃ g, ex.procAt g = some c ∧ ex.HBeq g f ∧
        (starAlg c pick).ts ex f i ≤ (starAlg c pick).ts ex g i := by
  induction f using Nat.strong_induction_on generalizing x with
  | _ f ih =>
    obtain ⟨a, ha, rfl⟩ := Exec.procAt_eq_some.1 hfx
    have hxi' : i ≠ ⟨a.proc, hx⟩ := by
      rintro rfl
      exact hxi ⟨.nil, by simpa using hx⟩
    have hts : (starAlg c pick).ts ex f i = (starAlg c pick).merged ex f i := by
      rw [(starAlg c pick).ts_eq ex ha]
      simp [starAlg, hx, Function.update_of_ne hxi']
    -- the value inherited from the previous event of `x`
    have hin : (starAlg c pick).inVal ex f i = 0 ∨
        ∃ g, ex.procAt g = some c ∧ ex.HBeq g f ∧
          (starAlg c pick).inVal ex f i ≤ (starAlg c pick).ts ex g i := by
      unfold MergeAlg.inVal
      cases h : ex.prev f with
      | none => left; rfl
      | some p =>
        obtain ⟨h1, -, h3, -⟩ := Exec.prev_spec h
        rcases ih p h1 hx (h3.trans hfx) hxi with h0 | ⟨g, hg1, hg2, hg3⟩
        · left; exact h0
        · exact Or.inr ⟨g, hg1, Or.inr (hg2.trans_hb (.of_step (.po h))), hg3⟩
    rw [hts]
    unfold MergeAlg.merged
    rw [ha]
    match a, ha, hx, hxi, hxi', hin with
    | .send _ _, _, _, _, _, hin => exact hin
    | .comp _, _, _, _, _, hin => exact hin
    | .recv x m, ha, hx, hxi, hxi', hin =>
      simp only [hwf.recv_lt ha, ite_true, Pi.sup_apply]
      obtain ⟨y, hy⟩ := hwf.recv_send ha
      have hadj : G.Adj y x := hG hy
      -- the value carried by the message
      have hmsg : (starAlg c pick).ts ex m i = 0 ∨
          ∃ g, ex.procAt g = some c ∧ ex.HBeq g f ∧
            (starAlg c pick).ts ex m i ≤ (starAlg c pick).ts ex g i := by
        by_cases hyc : y = c
        · subst hyc
          exact Or.inr ⟨m, Exec.procAt_of_get hy, Or.inr (.of_step (.msg ha)), le_rfl⟩
        · have hyi : ¬ G.ReachableAvoiding {c} y i.1 := by
            rintro ⟨p, hp⟩
            refine hxi ⟨.cons hadj.symm p, fun z hz => ?_⟩
            rcases List.mem_cons.1 (by simpa using hz) with rfl | hz
            · simpa using hx
            · exact hp z hz
          rcases ih m (hwf.recv_lt ha) hyc (Exec.procAt_of_get hy) hyi with h0 | ⟨g, hg1, hg2, hg3⟩
          · exact Or.inl h0
          · exact Or.inr ⟨g, hg1, Or.inr (hg2.trans_hb (.of_step (.msg ha))), hg3⟩
      rcases le_total ((starAlg c pick).inVal ex f i) ((starAlg c pick).ts ex m i) with h | h
      · rw [max_eq_right h]; exact hmsg
      · rw [max_eq_left h]; exact hin

/-- `c` is a cut vertex: every other process is separated (in `G − c`) from some process. -/
def IsCutVertex (G : SimpleGraph P) (c : P) : Prop :=
  ∀ x, x ≠ c → ∃ i, i ≠ c ∧ ¬ G.ReachableAvoiding {c} x i

/-- If `τ(e) ≤ τ(f)` then `e = f` or `e → f`. -/
lemma hbeq_of_ts_le [Nontrivial P] {G : SimpleGraph P} (hcut : IsCutVertex G c)
    (hpick : PickSpec pick) (hwf : ex.WF) (hG : ex.OnGraph G) {e f : ℕ} (he : e < ex.length)
    (hf : f < ex.length) (hle : (starAlg c pick).ts ex e ≤ (starAlg c pick).ts ex f) :
    ex.HBeq e f := by
  obtain ⟨x, hx⟩ : ∃ x, ex.procAt e = some x :=
    ⟨_, Exec.procAt_of_get (List.getElem?_eq_getElem he)⟩
  obtain ⟨z, hz⟩ : ∃ z, ex.procAt f = some z :=
    ⟨_, Exec.procAt_of_get (List.getElem?_eq_getElem hf)⟩
  by_cases hxc : x = c
  · rw [hxc] at hx
    by_cases hzc : z = c
    · rw [hzc] at hz
      rcases Exec.hb_total hx hz with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd (lt_of_lt_of_le (MergeAlg.hb_lt hwf (starAlg_upd_lt hpick) h) hle)
          (lt_irrefl _)
    · obtain ⟨i, hic, hzi⟩ := hcut z hzc
      rcases ts_cut_invariant (pick := pick) hwf hG f hzc hz ⟨i, hic⟩ hzi with
        h0 | ⟨g, hg1, hg2, hg3⟩
      · have h1 := merged_lt_of_center hpick hx ⟨i, hic⟩
        have h3 : (0 : ℝ) ≤ (starAlg c pick).merged ex e ⟨i, hic⟩ :=
          ((le_trans (by
            unfold MergeAlg.inVal
            cases h : ex.prev e with
            | none => exact le_rfl
            | some p => exact starAlg_nonneg hpick p)
            (MergeAlg.inVal_le_merged (A := starAlg c pick) ex e)) ⟨i, hic⟩)
        have := hle ⟨i, hic⟩
        linarith
      · rcases Exec.hb_total hx hg1 with h | rfl | h
        · exact Or.inr (h.trans_hbeq hg2)
        · exact hg2
        · have h1 := MergeAlg.le_merged_of_hb hwf
            (fun j a w => (starAlg_upd_lt hpick j a w).le) h ⟨i, hic⟩
          have h2 := merged_lt_of_center hpick hx ⟨i, hic⟩
          have := hle ⟨i, hic⟩
          linarith
  · have h := floor_ts hpick ex e ⟨x, hxc⟩
    have h' := floor_ts hpick ex f ⟨x, hxc⟩
    have hfl := Int.floor_le_floor (hle ⟨x, hxc⟩)
    rw [h, h'] at hfl
    rw [← Exec.idx_le_vc_iff hwf hx, ← Exec.vc_self hwf hx]
    exact_mod_cast hfl

/-- **Appendix B.2** (correctness, omitted in the paper), generalized to a cut vertex `c`: the
timestamps are distinct and capture causality. -/
theorem starAlg_captures [Nontrivial P] {G : SimpleGraph P} (hcut : IsCutVertex G c)
    (hpick : PickSpec pick) (hwf : ex.WF) (hG : ex.OnGraph G) :
    CapturesCausality ex ((starAlg c pick).ts ex) := by
  intro e f he hf
  refine ⟨⟨MergeAlg.hb_lt hwf (starAlg_upd_lt hpick), fun h => ?_⟩, fun hne h => ?_⟩
  · rcases hbeq_of_ts_le hcut hpick hwf hG he hf h.le with rfl | h'
    · exact absurd h (lt_irrefl _)
    · exact h'
  · rcases hbeq_of_ts_le hcut hpick hwf hG he hf h.le with rfl | h1
    · exact hne rfl
    · exact Exec.HB.irrefl hwf _ (h1.trans_hbeq (hbeq_of_ts_le hcut hpick hwf hG hf he h.ge))

/-- The algorithm of Appendix B.2 as an online algorithm (it is distributed by construction). -/
noncomputable def starOnline (c : P) (pick : ℕ → Coord c → ℝ → ℝ) : Exec P → (Coord c → ℝ) :=
  fun l => (starAlg c pick).ts l (l.length - 1)

theorem starOnline_isOnline [Nontrivial P] {G : SimpleGraph P} (hcut : IsCutVertex G c)
    (hpick : PickSpec pick) : IsOnlineTimestamping G (starOnline c pick) := by
  intro ex hwf hG i j hi hj
  have h := starAlg_captures hcut hpick hwf hG i j hi hj
  have e1 := (starAlg c pick).ts_eq_onlineTs ex hi
  have e2 := (starAlg c pick).ts_eq_onlineTs ex hj
  change _ = onlineTs (starOnline c pick) ex i at e1
  change _ = onlineTs (starOnline c pick) ex j at e2
  rwa [← e1, ← e2]

/-- A valid choice: the midpoint of the interval. -/
noncomputable def midPick (c : P) : ℕ → Coord c → ℝ → ℝ := fun _ _ x => (x + (⌊x⌋ + 1)) / 2

lemma midPick_spec : PickSpec (midPick c) := by
  intro j i x
  have := Int.lt_floor_add_one x
  simp only [midPick]
  constructor <;> linarith

/-! ### The star graph with `n ≥ 3` -/

lemma star_isCutVertex {m : ℕ} (hm : 2 ≤ m) : IsCutVertex (star m) 0 := by
  intro x hx
  obtain ⟨i, hi0, hix⟩ : ∃ i : Fin (m + 1), i ≠ 0 ∧ i ≠ x := by
    by_cases h : x = ⟨1, by omega⟩
    · exact ⟨⟨2, by omega⟩, by simp [Fin.ext_iff], by subst h; simp [Fin.ext_iff]⟩
    · exact ⟨⟨1, by omega⟩, by simp [Fin.ext_iff], Ne.symm h⟩
  refine ⟨i, hi0, ?_⟩
  rintro ⟨p, hp⟩
  cases p with
  | nil => exact hix rfl
  | cons h q =>
    rcases star_adj.1 h with ⟨-, h0 | h0⟩
    · exact hx h0
    · subst h0
      exact hp _ (by simp) rfl

/-- Reindexing the coordinates by a bijection preserves the order and distinctness. -/
lemma isOnline_comp_equiv {ι κ α : Type*} [Preorder α] {G : SimpleGraph P}
    {A : Exec P → (κ → α)} (hA : IsOnlineTimestamping G A) (σ : ι ≃ κ) :
    IsOnlineTimestamping G (fun l => A l ∘ σ) := by
  have hle : ∀ v w : κ → α, v ∘ σ ≤ w ∘ σ ↔ v ≤ w := fun v w =>
    ⟨fun h k => by simpa using h (σ.symm k), fun h i => h (σ i)⟩
  have hlt : ∀ v w : κ → α, v ∘ σ < w ∘ σ ↔ v < w := fun v w => by
    simp only [lt_iff_le_not_ge, hle]
  intro ex hwf hG i j hi hj
  obtain ⟨h1, h2⟩ := hA ex hwf hG i j hi hj
  refine ⟨h1.trans (hlt _ _).symm, fun hne h => h2 hne ?_⟩
  exact (σ.surjective.injective_comp_right) h

/-- **Appendix B.2**: for the star graph with `n = m + 1 ≥ 3` processes there is an online
algorithm with real-valued vectors of length `n − 1 = m`; together with `lemma_1`, `n − 1` is
tight. -/
theorem appendix_B2 (m : ℕ) (hm : 2 ≤ m) :
    ∃ A : Exec (Fin (m + 1)) → (Fin m → ℝ), IsOnlineTimestamping (star m) A := by
  have : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  let σ : Fin m ≃ Coord (0 : Fin (m + 1)) :=
    { toFun := fun k => ⟨k.succ, Fin.succ_ne_zero k⟩
      invFun := fun p => p.1.pred p.2
      left_inv := fun k => by simp
      right_inv := fun p => by simp }
  exact ⟨_, isOnline_comp_equiv (starOnline_isOnline (star_isCutVertex hm) midPick_spec) σ⟩

/-- Appendix B.2 for `n = 2`: vectors of length `2` are necessary and sufficient. -/
theorem appendix_B2_two {α : Type*} [LinearOrder α] {s : ℕ} (A : Exec (Fin 2) → (Fin s → α))
    (hA : IsOnlineTimestamping (star 1) A) : 2 ≤ s ∧
    IsOnlineTimestamping (star 1) (fun l : Exec (Fin 2) => l.vc (l.length - 1)) :=
  ⟨two_le_of_ne (star 1) (u := 0) (v := 1) (by decide) A hA, vectorClock_isOnline _⟩

end Podc.DelayedTimestamps
