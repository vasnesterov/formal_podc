import Papers.PODC2025.BAWithPredictions.Plurality

/-!
# Graded consensus and conciliation with a core set (Sections 7.1 and 7.2)

The two building blocks of Algorithm 5 of [BDEG25], verified at the level of one instance:

* **Algorithm 3** (graded consensus with core set, two rounds): `gcB` (the value `b_i` set after
  round 1, lines 3–6) and `gcOut` (the returned pair after round 2, lines 9–16).
* **Algorithm 4** (conciliation with core set, one round): `conc` (lines 2–6).

Each instance is described by the *receptions* of the honest processes: `r1 i j`, `r2 i j`
(`rc i j` for conciliation) is what the honest `p_i` received from `p_j`. The honest senders'
messages are received exactly as sent (the synchronous model), messages from faulty senders are
arbitrary. The paper's assumption on the listening sets is `CoreSet`: `|L_i| ≤ 3k + 1` (the paper
has `= 3k + 1`) and a core set `G` of at least `2k + 1` honest processes contained in every honest
`L_i`.

* Lemmas 7, 8, 9 of [BDEG25]: `lemma7`, `lemma8` (strong unanimity), `lemma9` (coherence).
* Lemmas 10–14 of [BDEG25]: `lemma10`, `lemma11`, `lemma12`, `lemma13` (agreement), `lemma14`
  (strong unanimity).

Choices for under-specified points of the paper:
* "a value which occurs at least `m` times" (`thr`): an arbitrary such value (by choice). For
  `m = 2k + 1` it is unique because `|L_i| ≤ 3k + 1`; for `m = k + 1` (Algorithm 3, line 14) it need
  not be unique, and Lemma 9 holds for every choice.
* Conciliation: the paths from `y` to `z` include the trivial path (`y = z`), and `m_i[z]` is
  only used for `z ∈ T_i ∩ L_i` (the paper's line 4 "`y ∈ L_y`" is read as "`y ∈ T_i`"). If
  `T_i ∩ L_i = ∅` (impossible under the core-set assumption) `p_i` returns its own input.

[BDEG25]: Ben-David, Dzulfikar, Ellen, Gilbert, *Byzantine Agreement with Predictions*, PODC 2025.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions.Unauth

open Finset

/-! ### Thresholds -/

section Threshold

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- Some value `w` such that `some w` occurs at least `m` times among the values of `f` on `X`
(`none` if there is none). -/
noncomputable def thr (X : Finset ι) (f : ι → Option α) (m : ℕ) : Option α := by
  classical
  exact if h : ∃ w, m ≤ cnt X f (some w) then some h.choose else none

theorem thr_spec {X : Finset ι} {f : ι → Option α} {m : ℕ} {w : α} (h : thr X f m = some w) :
    m ≤ cnt X f (some w) := by
  unfold thr at h
  split_ifs at h with h'
  · cases h; exact h'.choose_spec

theorem thr_none {X : Finset ι} {f : ι → Option α} {m : ℕ} (h : thr X f m = none) (w : α) :
    cnt X f (some w) < m := by
  unfold thr at h
  split_ifs at h with h'
  push Not at h'
  exact h' w

theorem thr_eq {X : Finset ι} {f : ι → Option α} {m : ℕ} {w : α} (hw : m ≤ cnt X f (some w))
    (hu : ∀ w', w' ≠ w → cnt X f (some w') < m) : thr X f m = some w := by
  cases h : thr X f m with
  | none => exact absurd hw (not_le.mpr (thr_none h w))
  | some w' =>
    by_contra hne
    have := hu w' (fun e => hne (by rw [e]))
    have := thr_spec h
    omega

theorem cnt_mono {X Y : Finset ι} (h : X ⊆ Y) (f : ι → α) (a : α) : cnt X f a ≤ cnt Y f a :=
  card_le_card (filter_subset_filter _ h)

theorem cnt_le_cnt_add (X Y : Finset ι) (f : ι → α) (a : α) :
    cnt Y f a ≤ cnt X f a + (Y \ X).card := by
  unfold cnt
  calc (Y.filter fun j => f j = a).card ≤ ((X.filter fun j => f j = a) ∪ (Y \ X)).card := by
        refine card_le_card fun j hj => ?_
        simp only [mem_filter, mem_union, mem_sdiff] at hj ⊢
        by_cases hx : j ∈ X
        · exact Or.inl ⟨hx, hj.2⟩
        · exact Or.inr ⟨hj.1, hx⟩
    _ ≤ _ := card_union_le _ _

theorem cnt_congr {X : Finset ι} {f g : ι → α} (h : ∀ j ∈ X, f j = g j) (a : α) :
    cnt X f a = cnt X g a := by
  unfold cnt
  congr 1
  exact filter_congr fun j hj => by rw [h j hj]

theorem cnt_le_card (X : Finset ι) (f : ι → α) (a : α) : cnt X f a ≤ X.card :=
  card_le_card (filter_subset _ _)

theorem cnt_eq_card {X : Finset ι} {f : ι → α} {a : α} (h : ∀ j ∈ X, f j = a) :
    cnt X f a = X.card := by
  unfold cnt; rw [filter_true_of_mem h]

end Threshold

variable {P V : Type*} [Fintype P] [LinearOrder P] [LinearOrder V]

/-! ### The core-set assumption -/

/-- The assumptions of Algorithms 3 and 4 of [BDEG25] on the listening sets `L i`: every honest
listening set has at most `3k + 1` elements, and `G` is a core set: at least `2k + 1` honest
processes contained in every honest listening set. -/
structure CoreSet (F : Finset P) (k : ℕ) (L : P → Finset P) (G : Finset P) : Prop where
  card_L : ∀ i ∉ F, (L i).card ≤ 3 * k + 1
  G_honest : ∀ j ∈ G, j ∉ F
  card_G : 2 * k + 1 ≤ G.card
  G_sub : ∀ i ∉ F, G ⊆ L i

namespace CoreSet

variable {F : Finset P} {k : ℕ} {L : P → Finset P} {G : Finset P}

/-- `|L_i - G| ≤ k`. -/
theorem card_sdiff (hC : CoreSet F k L G) {i : P} (hi : i ∉ F) : (L i \ G).card ≤ k := by
  rw [card_sdiff_of_subset (hC.G_sub i hi)]
  have := hC.card_L i hi; have := hC.card_G; omega

theorem mem_self (hC : CoreSet F k L G) {j : P} (hj : j ∈ G) : j ∈ L j :=
  hC.G_sub j (hC.G_honest j hj) hj

end CoreSet

/-! ### Algorithm 3: graded consensus with core set -/

/-- Algorithm 3 of [BDEG25], lines 3–6: the value `b_i` (`none` = `⊥`) after round 1, given the
round-1 values `r1 j` received from each `p_j` (only those from `L` count). -/
noncomputable def gcB (k : ℕ) (L : Finset P) (r1 : P → Option V) : Option V :=
  thr L r1 (2 * k + 1)

/-- Algorithm 3 of [BDEG25], lines 9–16: the returned pair (value, grade) given the input `v`, the
value `b` after round 1 and the round-2 values `r2 j` received from each `p_j`. -/
noncomputable def gcOut (k : ℕ) (L : Finset P) (v : V) (b : Option V) (r2 : P → Option V) :
    V × Bool :=
  match b with
  | some w => (w, decide (2 * k + 1 ≤ cnt L r2 (some w)))
  | none => ((thr L r2 (k + 1)).getD v, false)

theorem gcOut_some (k : ℕ) (L : Finset P) (v w : V) (r2 : P → Option V) :
    gcOut k L v (some w) r2 = (w, decide (2 * k + 1 ≤ cnt L r2 (some w))) := rfl

theorem gcOut_none (k : ℕ) (L : Finset P) (v : V) (r2 : P → Option V) :
    gcOut k L v none r2 = ((thr L r2 (k + 1)).getD v, false) := rfl

section GC

variable {F : Finset P} {k : ℕ} {L : P → Finset P} {G : Finset P} {v : P → V}
  {r1 r2 : P → P → Option V}

/-- Round 1 of Algorithm 3: each honest `p_i` receives `v_j` from every honest `p_j` with
`j ∈ L_j` (line 2) and nothing from the other honest processes. -/
def GCRound1 (F : Finset P) (L : P → Finset P) (v : P → V) (r1 : P → P → Option V) : Prop :=
  ∀ i ∉ F, ∀ j ∉ F, r1 i j = if j ∈ L j then some (v j) else none

/-- Round 2 of Algorithm 3: each honest `p_i` receives `b_j` from every honest `p_j` with
`j ∈ L_j` and `b_j ≠ ⊥` (line 8). -/
def GCRound2 (F : Finset P) (k : ℕ) (L : P → Finset P) (r1 r2 : P → P → Option V) : Prop :=
  ∀ i ∉ F, ∀ j ∉ F, r2 i j = if j ∈ L j then gcB k (L j) (r1 j) else none

/-- The number of members of the core set with input `w`. -/
private theorem cnt_r1 (hC : CoreSet F k L G) (h1 : GCRound1 F L v r1) {i : P} (hi : i ∉ F)
    (w : V) :
    cnt G (fun j => some (v j)) (some w) ≤ cnt (L i) (r1 i) (some w) ∧
      cnt (L i) (r1 i) (some w) ≤ cnt G (fun j => some (v j)) (some w) + k := by
  have he : cnt G (r1 i) (some w) = cnt G (fun j => some (v j)) (some w) :=
    cnt_congr (fun j hj => by
      rw [h1 i hi j (hC.G_honest j hj), ite_eq_left (hC.mem_self hj)]) _
  have h2 := cnt_mono (hC.G_sub i hi) (r1 i) (some w)
  have h3 := cnt_le_cnt_add G (L i) (r1 i) (some w)
  have h4 := hC.card_sdiff hi
  omega

private theorem gcB_cnt (hC : CoreSet F k L G) (h1 : GCRound1 F L v r1) {i : P} (hi : i ∉ F)
    {w : V} (hb : gcB k (L i) (r1 i) = some w) :
    k + 1 ≤ cnt G (fun j => some (v j)) (some w) := by
  have := thr_spec hb
  have := (cnt_r1 hC h1 hi w).2
  omega

/-- **Lemma 7 of [BDEG25].** All honest processes that set `b_i ≠ ⊥` (line 5) set it to the same
value. -/
theorem lemma7 (hC : CoreSet F k L G) (h1 : GCRound1 F L v r1) {i i' : P} (hi : i ∉ F)
    (hi' : i' ∉ F) {w w' : V} (hb : gcB k (L i) (r1 i) = some w)
    (hb' : gcB k (L i') (r1 i') = some w') : w = w' := by
  by_contra hne
  have e1 := gcB_cnt hC h1 hi hb
  have e2 := thr_spec hb'
  have e3 := (cnt_r1 hC h1 hi' w).1
  have e4 := cnt_add_cnt_le (X := L i') (f := r1 i') (w := some w) (w' := some w')
    (by simpa using hne)
  have e5 := hC.card_L i' hi'
  omega

/-- **Lemma 8 of [BDEG25] (strong unanimity).** If every honest process has input `w`, they all
return `(w, 1)`. -/
theorem lemma8 (hC : CoreSet F k L G) (h1 : GCRound1 F L v r1) (h2 : GCRound2 F k L r1 r2)
    {w : V} (hv : ∀ i ∉ F, v i = w) :
    ∀ i ∉ F, gcOut k (L i) (v i) (gcB k (L i) (r1 i)) (r2 i) = (w, true) := by
  have hG : cnt G (fun j => some (v j)) (some w) = G.card :=
    cnt_eq_card fun j hj => by rw [hv j (hC.G_honest j hj)]
  have hb : ∀ i ∉ F, gcB k (L i) (r1 i) = some w := by
    intro i hi
    have e1 := (cnt_r1 hC h1 hi w).1
    have e2 := hC.card_G
    have e3 := hC.card_L i hi
    refine thr_eq (by omega) fun w' hw' => ?_
    have := cnt_add_cnt_le (X := L i) (f := r1 i) (w := some w) (w' := some w')
      (by simpa using hw'.symm)
    omega
  intro i hi
  rw [hb i hi, gcOut_some]
  have : cnt G (r2 i) (some w) = G.card := cnt_eq_card fun j hj => by
    rw [h2 i hi j (hC.G_honest j hj), ite_eq_left (hC.mem_self hj), hb j (hC.G_honest j hj)]
  have := cnt_mono (hC.G_sub i hi) (r2 i) (some w)
  have := hC.card_G
  simp only [Prod.mk.injEq, true_and, decide_eq_true_eq]
  omega

/-- **Lemma 9 of [BDEG25] (coherence).** If an honest process returns grade `1`, then every
honest process returns the same value. -/
theorem lemma9 (hC : CoreSet F k L G) (h1 : GCRound1 F L v r1) (h2 : GCRound2 F k L r1 r2)
    {i : P} (hi : i ∉ F) (hg : (gcOut k (L i) (v i) (gcB k (L i) (r1 i)) (r2 i)).2 = true) :
    ∀ i' ∉ F, (gcOut k (L i') (v i') (gcB k (L i') (r1 i')) (r2 i')).1 =
      (gcOut k (L i) (v i) (gcB k (L i) (r1 i)) (r2 i)).1 := by
  -- `p_i` set `b_i = w` and received `w` at least `2k + 1` times in round 2
  cases hb : gcB k (L i) (r1 i) with
  | none => rw [hb, gcOut_none] at hg; exact absurd hg (by simp)
  | some w =>
    rw [hb] at hg; rw [gcOut_some] at hg ⊢
    simp only [decide_eq_true_eq] at hg
    intro i' hi'
    -- the core set members' round-2 values
    have hG2 : ∀ w', cnt (L i') (r2 i') (some w') ≤
        cnt G (fun j => gcB k (L j) (r1 j)) (some w') + k ∧
        cnt G (fun j => gcB k (L j) (r1 j)) (some w') ≤ cnt (L i') (r2 i') (some w') := by
      intro w'
      have he : cnt G (r2 i') (some w') = cnt G (fun j => gcB k (L j) (r1 j)) (some w') :=
        cnt_congr (fun j hj => by
          rw [h2 i' hi' j (hC.G_honest j hj), ite_eq_left (hC.mem_self hj)]) _
      have := cnt_mono (hC.G_sub i' hi') (r2 i') (some w')
      have := cnt_le_cnt_add G (L i') (r2 i') (some w')
      have := hC.card_sdiff hi'
      omega
    have hGi : cnt G (r2 i) (some w) = cnt G (fun j => gcB k (L j) (r1 j)) (some w) :=
      cnt_congr (fun j hj => by
        rw [h2 i hi j (hC.G_honest j hj), ite_eq_left (hC.mem_self hj)]) _
    have hw : k + 1 ≤ cnt G (fun j => gcB k (L j) (r1 j)) (some w) := by
      have := cnt_le_cnt_add G (L i) (r2 i) (some w)
      have := hC.card_sdiff hi
      omega
    -- no core-set member has another value (Lemma 7)
    have hother : ∀ w', w' ≠ w → cnt G (fun j => gcB k (L j) (r1 j)) (some w') = 0 := by
      intro w' hw'
      unfold cnt
      rw [card_eq_zero, filter_eq_empty_iff]
      intro j hj hbj
      exact hw' (lemma7 hC h1 hi (hC.G_honest j hj) hb hbj).symm
    cases hb' : gcB k (L i') (r1 i') with
    | some w' => rw [gcOut_some]; exact lemma7 hC h1 hi' hi hb' hb
    | none =>
      rw [gcOut_none]
      have : thr (L i') (r2 i') (k + 1) = some w := by
        refine thr_eq ((hG2 w).2.trans' hw) fun w' hw' => ?_
        have := (hG2 w').1
        rw [hother w' hw'] at this
        omega
      rw [this]; rfl

end GC

/-! ### Algorithm 4: conciliation with core set -/

section Conc

/-- The set `T_i` of processes from which a message was received. -/
def cT (rc : P → Option (V × Finset P)) : Finset P := univ.filter fun y => (rc y).isSome

/-- The edges of the graph `(T_i, E_i)`: `(y, z)` with `y ≠ z`, `y, z ∈ T_i` and `y ∈ L_z`, where
`L_z` is the set received from `p_z`. -/
def cedge (rc : P → Option (V × Finset P)) (y z : P) : Prop :=
  y ≠ z ∧ (rc y).isSome ∧ ∃ a, rc z = some a ∧ y ∈ a.2

/-- There is a path (possibly trivial) from `y` to `z` in `(T_i, E_i)`. -/
def creach (rc : P → Option (V × Finset P)) (y z : P) : Prop :=
  Relation.ReflTransGen (cedge rc) y z

/-- The value `v_y` received from `p_y` (`d` if none). -/
def cval (rc : P → Option (V × Finset P)) (d : V) (y : P) : V := ((rc y).map Prod.fst).getD d

/-- The set of `y ∈ T_i` with a path from `y` to `z`. -/
noncomputable def cfrom (rc : P → Option (V × Finset P)) (z : P) : Finset P := by
  classical
  exact (cT rc).filter fun y => creach rc y z

theorem mem_cfrom {rc : P → Option (V × Finset P)} {y z : P} :
    y ∈ cfrom rc z ↔ (rc y).isSome ∧ creach rc y z := by
  unfold cfrom cT; simp

/-- Algorithm 4 of [BDEG25], line 4: `m_i[z]`, the minimum of the values `v_y` over the
`y ∈ T_i` with a path from `y` to `z` (`d` if there is none, which does not happen for
`z ∈ T_i`). -/
noncomputable def cmin (rc : P → Option (V × Finset P)) (d : V) (z : P) : V :=
  if h : (cfrom rc z).Nonempty then (cfrom rc z).inf' h (cval rc d) else d

/-- **Algorithm 4 of [BDEG25]** (conciliation with core set), lines 2–6: the returned value,
given the own listening set `L`, the own input `d`, and the received pairs `rc j = (v_j, L_j)`. -/
noncomputable def conc (L : Finset P) (d : V) (rc : P → Option (V × Finset P)) : V :=
  plur (cT rc ∩ L) (cmin rc d) d

variable {F : Finset P} {k : ℕ} {L : P → Finset P} {G : Finset P} {v : P → V}
  {rc : P → P → Option (V × Finset P)}

/-- The round of Algorithm 4: each honest `p_i` receives `(v_j, L_j)` from every honest `p_j`
with `j ∈ L_j` (line 1) and nothing from the other honest processes. -/
def CRound (F : Finset P) (L : P → Finset P) (v : P → V) (rc : P → P → Option (V × Finset P)) :
    Prop :=
  ∀ i ∉ F, ∀ j ∉ F, rc i j = if j ∈ L j then some (v j, L j) else none

/-- **Lemma 10 of [BDEG25]** (with the transfer used in Lemma 12). Assume `L_j ⊆ H` for honest
`j`. If the honest `p_i` has a path from `y` to an honest `z ∈ T_i`, then `y` is honest,
`y ∈ T_i`, and the same path exists in the graph of every honest `p_i'`. -/
theorem lemma10 (hL : ∀ i ∉ F, ∀ j ∈ L i, j ∉ F) (hr : CRound F L v rc) {i i' : P} (hi : i ∉ F)
    (hi' : i' ∉ F) {y z : P} (hyz : creach (rc i) y z) (hz : z ∉ F) (hzT : (rc i z).isSome) :
    y ∉ F ∧ (rc i y).isSome ∧ (rc i' y).isSome ∧ creach (rc i') y z := by
  have hT' : ∀ x, x ∉ F → (rc i x).isSome → (rc i' x).isSome := fun x hx h => by
    rw [hr i hi x hx] at h
    rw [hr i' hi' x hx]
    split_ifs at h ⊢ <;> simp_all
  induction hyz using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨hz, hzT, hT' _ hz hzT, Relation.ReflTransGen.refl⟩
  | @head y w hyw _ ih =>
    obtain ⟨hwF, hwT, -, hw'⟩ := ih
    obtain ⟨hne, hyT, a, ha, hya⟩ := hyw
    rw [hr i hi w hwF] at ha
    split_ifs at ha with hww
    cases ha
    have hyF := hL w hwF y hya
    refine ⟨hyF, hyT, hT' _ hyF hyT, Relation.ReflTransGen.head ⟨hne, hT' _ hyF hyT, ?_⟩ hw'⟩
    exact ⟨(v w, L w), by rw [hr i' hi' w hwF, ite_eq_left hww], hya⟩

/-- **Lemma 11 of [BDEG25].** For `j, j'` in the core set, `m_i[j] = m_i[j']`. -/
theorem lemma11 (hC : CoreSet F k L G) (hr : CRound F L v rc) {i : P} (hi : i ∉ F) (d : V)
    {j j' : P} (hj : j ∈ G) (hj' : j' ∈ G) : cmin (rc i) d j = cmin (rc i) d j' := by
  have hsome : ∀ x ∈ G, rc i x = some (v x, L x) := fun x hx => by
    rw [hr i hi x (hC.G_honest x hx), ite_eq_left (hC.mem_self hx)]
  have hedge : ∀ x ∈ G, ∀ x' ∈ G, creach (rc i) x x' := by
    intro x hx x' hx'
    by_cases h : x = x'
    · subst h; exact Relation.ReflTransGen.refl
    · refine Relation.ReflTransGen.single ⟨h, by simp [hsome x hx], (v x', L x'),
        hsome x' hx', hC.G_sub x' (hC.G_honest x' hx') hx⟩
  have : cfrom (rc i) j = cfrom (rc i) j' := by
    ext y
    simp only [mem_cfrom]
    exact ⟨fun h => ⟨h.1, h.2.trans (hedge j hj j' hj')⟩,
      fun h => ⟨h.1, h.2.trans (hedge j' hj' j hj)⟩⟩
  unfold cmin; rw [this]

/-- **Lemma 12 of [BDEG25].** For `j` in the core set, all honest processes compute the same
`m_i[j]`, provided `L_i ⊆ H` for all honest `i`. -/
theorem lemma12 (hC : CoreSet F k L G) (hL : ∀ i ∉ F, ∀ j ∈ L i, j ∉ F) (hr : CRound F L v rc)
    {i i' : P} (hi : i ∉ F) (hi' : i' ∉ F) (d d' : V) {j : P} (hj : j ∈ G) :
    cmin (rc i) d j = cmin (rc i') d' j := by
  have hjF := hC.G_honest j hj
  have hT : ∀ x, x ∉ F → (rc x j).isSome := fun x hx => by
    rw [hr x hx j hjF, ite_eq_left (hC.mem_self hj)]; rfl
  have hset : cfrom (rc i) j = cfrom (rc i') j := by
    ext y
    simp only [mem_cfrom]
    exact ⟨fun h => (lemma10 hL hr hi hi' h.2 hjF (hT i hi)).2.2,
      fun h => (lemma10 hL hr hi' hi h.2 hjF (hT i' hi')).2.2⟩
  have hval : ∀ y ∈ cfrom (rc i) j, cval (rc i) d y = cval (rc i') d' y := by
    intro y hy
    rw [mem_cfrom] at hy
    have hyF := (lemma10 hL hr hi hi' hy.2 hjF (hT i hi)).1
    have h1 := hy.1
    rw [hr i hi y hyF] at h1
    unfold cval
    rw [hr i hi y hyF, hr i' hi' y hyF]
    split_ifs at h1 ⊢ <;> simp_all
  unfold cmin
  have hne : (cfrom (rc i) j).Nonempty :=
    ⟨j, mem_cfrom.mpr ⟨hT i hi, Relation.ReflTransGen.refl⟩⟩
  rw [dite_eq_left hne, dite_eq_left (hset ▸ hne)]
  rw [Finset.inf'_congr hne hset hval]

private theorem conc_eq_cmin (hC : CoreSet F k L G) (hr : CRound F L v rc) {i : P}
    (hi : i ∉ F) (d : V) {j : P} (hj : j ∈ G) : conc (L i) d (rc i) = cmin (rc i) d j := by
  unfold conc
  apply plur_eq_of_majority
  have hsub : G ⊆ cT (rc i) ∩ L i := fun x hx => by
    refine mem_inter.mpr ⟨?_, hC.G_sub i hi hx⟩
    simp only [cT, mem_filter, mem_univ, true_and]
    rw [hr i hi x (hC.G_honest x hx), ite_eq_left (hC.mem_self hx)]; rfl
  have h1 : cnt G (cmin (rc i) d) (cmin (rc i) d j) = G.card :=
    cnt_eq_card fun x hx => lemma11 hC hr hi d hx hj
  have h2 := cnt_mono hsub (cmin (rc i) d) (cmin (rc i) d j)
  have h3 := card_le_card (inter_subset_right (s₁ := cT (rc i)) (s₂ := L i))
  have h4 := hC.card_L i hi
  have h5 := hC.card_G
  omega

/-- **Lemma 13 of [BDEG25] (agreement).** If `L_i ⊆ H` for all honest `i`, all honest processes
return the same value from conciliation. -/
theorem lemma13 (hC : CoreSet F k L G) (hL : ∀ i ∉ F, ∀ j ∈ L i, j ∉ F) (hr : CRound F L v rc)
    {i i' : P} (hi : i ∉ F) (hi' : i' ∉ F) :
    conc (L i) (v i) (rc i) = conc (L i') (v i') (rc i') := by
  obtain ⟨j, hj⟩ : G.Nonempty := by rw [← card_pos]; have := hC.card_G; omega
  rw [conc_eq_cmin hC hr hi _ hj, conc_eq_cmin hC hr hi' _ hj]
  exact lemma12 hC hL hr hi hi' _ _ hj

/-- **Lemma 14 of [BDEG25] (strong unanimity).** If `L_i ⊆ H` for all honest `i` and every honest
process has input `w`, they all return `w` from conciliation. -/
theorem lemma14 (hC : CoreSet F k L G) (hL : ∀ i ∉ F, ∀ j ∈ L i, j ∉ F) (hr : CRound F L v rc)
    {w : V} (hv : ∀ i ∉ F, v i = w) : ∀ i ∉ F, conc (L i) (v i) (rc i) = w := by
  intro i hi
  obtain ⟨j, hj⟩ : G.Nonempty := by rw [← card_pos]; have := hC.card_G; omega
  have hjF := hC.G_honest j hj
  rw [conc_eq_cmin hC hr hi _ hj]
  have hne : (cfrom (rc i) j).Nonempty := ⟨j, mem_cfrom.mpr ⟨by
    rw [hr i hi j hjF, ite_eq_left (hC.mem_self hj)]; rfl, Relation.ReflTransGen.refl⟩⟩
  unfold cmin
  rw [dite_eq_left hne]
  refine le_antisymm ((inf'_le _ (mem_cfrom.mpr ⟨?_, Relation.ReflTransGen.refl⟩)).trans_eq ?_)
    (le_inf' _ _ fun y hy => ?_)
  · rw [hr i hi j hjF, ite_eq_left (hC.mem_self hj)]; rfl
  · unfold cval; rw [hr i hi j hjF, ite_eq_left (hC.mem_self hj)]; simp [hv j hjF]
  · rw [mem_cfrom] at hy
    have hyF := (lemma10 hL hr hi hi hy.2 hjF (by
      rw [hr i hi j hjF, ite_eq_left (hC.mem_self hj)]; rfl)).1
    unfold cval
    rw [hr i hi y hyF]
    have h1 := hy.1
    rw [hr i hi y hyF] at h1
    split_ifs at h1 ⊢ <;> simp_all

end Conc

end BAWithPredictions.Unauth
