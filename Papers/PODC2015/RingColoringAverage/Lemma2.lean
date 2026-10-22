import Papers.PODC2015.RingColoringAverage.Model

/-!
# Lemma 2: radius regularity of minimal 4-colouring algorithms

Paper, Lemma 2: if `A` is minimal for 4-colouring and `x`, `y` are two nodes separated by `k`
nodes, then every node strictly between `x` and `y` has radius at most
`max {r(x), r(y)} + k`.

We follow the paper's proof. Let `M = max {r(x), r(y)}` and `T = M + k` (the threshold). The
pattern `N` is the window of identifiers `[x - M, y + M]` of the ring `R₀`. The modified
algorithm `A'` (`Lemma2.alg`) behaves like `A`, except that a node `u` that

* has not stopped before radius `T` under `A`,
* sees `2T + 1` distinct identifiers at radius `T` (the ring has at least `2T + 1` nodes), and
* sees the pattern `N` around itself with itself at offset `d ∈ [1, k]` from (the copy of) `x`,

stops at radius `T` and chooses a colour different from the colours of its neighbours that
stopped before `T` under `A`; if some neighbour did not stop before `T`, the colour is taken in
`{0, 1}` if `d` is even and in `{2, 3}` if `d` is odd (`Lemma2.pick`).

`A'` is a valid 4-colouring algorithm (`Lemma2.alg_valid`) that never uses a larger radius than
`A` (`Lemma2.radAt_alg_le`) and uses radius `T` at every node between `x` and `y` whose
`A`-radius exceeds `T` (`Lemma2.radAt_alg_eq`); minimality of `A` gives the lemma
(`lemma_2`).

**Difference with the paper.** We assume that the ring has at least `2T + 1` nodes (so that the
views of radius `T` do not wrap around the ring). This is the only case used in Lemma 3 and
Theorem 1 (there all relevant radii are small compared with `n`).
-/

namespace Podc.RingColoringAverage

open Classical

namespace Lemma2

/-- Colour choice of a modified node: avoid the colours `lc`, `rc` of the neighbours that stopped
early (`none` = the neighbour did not stop before the threshold); if some neighbour did not stop
early, use the class `{0, 1}` (`p = false`, even offset) or `{2, 3}` (`p = true`, odd offset). -/
def pick (p : Bool) (lc rc : Option (Fin 4)) : Fin 4 :=
  ((List.finRange 4).find? (fun c => decide (lc ≠ some c ∧ rc ≠ some c ∧
    ((lc = none ∨ rc = none) → c.val / 2 = if p then 1 else 0)))).getD 0

theorem pick_spec : ∀ (p : Bool) (lc rc : Option (Fin 4)),
    lc ≠ some (pick p lc rc) ∧ rc ≠ some (pick p lc rc) ∧
    ((lc = none ∨ rc = none) → (pick p lc rc).val / 2 = if p then 1 else 0) := by
  decide

/-- Shift a view by `a`: the view of the node at offset `a`. -/
def sh (a : ℤ) (f : ℤ → ℕ) : ℤ → ℕ := fun j => f (j + a)

theorem sh_view (R : IdRing) (u a : ℤ) : sh a (R.view u) = R.view (u + a) := by
  funext j; simp [sh, IdRing.view]; ring_nf

variable (A : Alg (Fin 4)) (R₀ : IdRing) (x : ℤ) (k M : ℕ)

/-- `f` sees the pattern `R₀.id (x + i)`, `i ∈ [-M, k + 1 + M]`, with itself at offset `d` from
the copy of `x`. -/
def MatchAt (f : ℤ → ℕ) (d : ℤ) : Prop :=
  ∀ i : ℤ, -(M : ℤ) ≤ i → i ≤ k + 1 + M → f (i - d) = R₀.id (x + i)

/-- The `2T + 1` identifiers of the window `[-T, T]` are pairwise distinct. -/
def Distinct (f : ℤ → ℕ) : Prop :=
  ∀ i j : ℤ, |i| ≤ (M + k : ℕ) → |j| ≤ (M + k : ℕ) → f i = f j → i = j

/-- `A` stops strictly before the threshold `T = M + k`. -/
def Early (f : ℤ → ℕ) : Prop := ∃ s < M + k, (A.out s f).isSome

/-- The node is modified by `A'`. -/
def Mod (f : ℤ → ℕ) : Prop :=
  ¬ Early A k M f ∧ Distinct k M f ∧ ∃ d : ℤ, 1 ≤ d ∧ d ≤ k ∧ MatchAt R₀ x k M f d

/-- The offset of a modified node is odd. -/
def OddM (f : ℤ → ℕ) : Prop := ∃ d : ℤ, 1 ≤ d ∧ d ≤ k ∧ Odd d ∧ MatchAt R₀ x k M f d

/-- Colour of the neighbour at offset `a` if it stops early under `A`. -/
noncomputable def nbr (f : ℤ → ℕ) (a : ℤ) : Option (Fin 4) :=
  if Early A k M (sh a f) then some (A.output (sh a f)) else none

/-- Colour of a modified node. -/
noncomputable def rule (f : ℤ → ℕ) : Fin 4 :=
  pick (decide (OddM R₀ x k M f)) (nbr A k M f (-1)) (nbr A k M f 1)

/-! ### Locality of the ingredients -/

variable {A R₀ x k M}

theorem matchAt_congr {f g : ℤ → ℕ} (h : AgreeOn (M + k) f g) {d : ℤ} (hd1 : 1 ≤ d)
    (hdk : d ≤ k) : MatchAt R₀ x k M f d ↔ MatchAt R₀ x k M g d := by
  have key : ∀ i : ℤ, -(M : ℤ) ≤ i → i ≤ k + 1 + M → f (i - d) = g (i - d) := fun i h1 h2 =>
    h _ (by rw [abs_le]; push_cast; constructor <;> omega)
  exact forall_congr' fun i => imp_congr_right fun h1 => imp_congr_right fun h2 => by
    rw [key i h1 h2]

theorem distinct_congr {f g : ℤ → ℕ} (h : AgreeOn (M + k) f g) :
    Distinct k M f ↔ Distinct k M g := by
  unfold Distinct
  exact forall_congr' fun i => forall_congr' fun j => imp_congr_right fun hi =>
    imp_congr_right fun hj => by rw [h i hi, h j hj]

theorem early_congr {f g : ℤ → ℕ} (h : AgreeOn (M + k) f g) :
    Early A k M f ↔ Early A k M g := by
  unfold Early
  exact exists_congr fun s => and_congr_right fun hs => by
    rw [A.out_congr s f g (h.mono hs.le)]

theorem agreeOn_sh {f g : ℤ → ℕ} {s : ℕ} (h : AgreeOn (s + 1) f g) {a : ℤ} (ha : |a| ≤ 1) :
    AgreeOn s (sh a f) (sh a g) := fun j hj => h _ (by
  push_cast; exact (abs_add_le _ _).trans (add_le_add hj ha))

theorem nbr_congr {f g : ℤ → ℕ} (h : AgreeOn (M + k) f g) {a : ℤ} (ha : |a| ≤ 1) :
    nbr A k M f a = nbr A k M g a := by
  unfold nbr
  by_cases he : Early A k M (sh a f)
  · obtain ⟨s, hs, hso⟩ := he
    have hsh : AgreeOn s (sh a f) (sh a g) := agreeOn_sh (h.mono (by omega)) ha
    have hstop : A.Stops (sh a f) := ⟨s, hso⟩
    have hrad : A.rad (sh a f) ≤ s := Alg.rad_le hso
    have he' : Early A k M (sh a g) := ⟨s, hs, by rw [← A.out_congr s _ _ hsh]; exact hso⟩
    rw [ite_eq_left ⟨s, hs, hso⟩, ite_eq_left he',
      Alg.output_eq_of_agreeOn (hsh.mono hrad) hstop le_rfl]
  · have he' : ¬ Early A k M (sh a g) := by
      rintro ⟨s, hs, hso⟩
      exact he ⟨s, hs, by
        rw [A.out_congr s _ _ (agreeOn_sh (h.mono (by omega)) ha)]; exact hso⟩
    rw [ite_eq_right he, ite_eq_right he']

theorem mod_congr {f g : ℤ → ℕ} (h : AgreeOn (M + k) f g) :
    Mod A R₀ x k M f ↔ Mod A R₀ x k M g := by
  unfold Mod
  rw [early_congr h, distinct_congr h]
  exact and_congr_right fun _ => and_congr_right fun _ => exists_congr fun d =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, (matchAt_congr h h1 h2).1 h3⟩,
     fun ⟨h1, h2, h3⟩ => ⟨h1, h2, (matchAt_congr h h1 h2).2 h3⟩⟩

theorem oddM_congr {f g : ℤ → ℕ} (h : AgreeOn (M + k) f g) :
    OddM R₀ x k M f ↔ OddM R₀ x k M g :=
  exists_congr fun _ =>
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, (matchAt_congr h h1 h2).1 h4⟩,
     fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, (matchAt_congr h h1 h2).2 h4⟩⟩

theorem rule_congr {f g : ℤ → ℕ} (h : AgreeOn (M + k) f g) :
    rule A R₀ x k M f = rule A R₀ x k M g := by
  unfold rule
  rw [nbr_congr h (by norm_num), nbr_congr h (by norm_num)]
  simp only [oddM_congr h]

variable (A R₀ x k M)

/-- The modified algorithm `A'` of the proof of Lemma 2. -/
noncomputable def alg : Alg (Fin 4) where
  out r f := if r = M + k ∧ Mod A R₀ x k M f then some (rule A R₀ x k M f) else A.out r f
  out_congr r f g h := by
    by_cases hr : r = M + k
    · subst hr
      simp only [mod_congr h, rule_congr h, A.out_congr _ f g h]
    · simp only [hr, false_and, ite_false, A.out_congr r f g h]

variable {A R₀ x k M}

/-! ### Behaviour of `A'` -/

theorem alg_out_of_not_mod {f : ℤ → ℕ} (h : ¬ Mod A R₀ x k M f) (r : ℕ) :
    (alg A R₀ x k M).out r f = A.out r f := by
  simp [alg, h]

theorem alg_of_not_mod {f : ℤ → ℕ} (h : ¬ Mod A R₀ x k M f) :
    ((alg A R₀ x k M).Stops f ↔ A.Stops f) ∧ (alg A R₀ x k M).rad f = A.rad f ∧
      (alg A R₀ x k M).output f = A.output f := by
  simp [Alg.Stops, Alg.rad, Alg.output, alg_out_of_not_mod h]

theorem not_early_iff_le_rad {f : ℤ → ℕ} (hf : A.Stops f) :
    ¬ Early A k M f ↔ M + k ≤ A.rad f := by
  constructor
  · intro h; by_contra hlt; exact h ⟨_, not_le.1 hlt, Alg.rad_spec hf⟩
  · rintro h ⟨s, hs, hso⟩; exact absurd ((Alg.rad_le hso).trans_lt hs) (not_lt.2 h)

theorem alg_of_mod {f : ℤ → ℕ} (h : Mod A R₀ x k M f) :
    (alg A R₀ x k M).Stops f ∧ (alg A R₀ x k M).rad f = M + k ∧
      (alg A R₀ x k M).output f = rule A R₀ x k M f := by
  have hT : (alg A R₀ x k M).out (M + k) f = some (rule A R₀ x k M f) := by simp [alg, h]
  have hlt : ∀ s < M + k, (alg A R₀ x k M).out s f = none := by
    intro s hs
    have : ¬ (A.out s f).isSome := fun hso => h.1 ⟨s, hs, hso⟩
    simp [alg, hs.ne, Option.not_isSome_iff_eq_none.1 this]
  have hstop : (alg A R₀ x k M).Stops f := ⟨M + k, by simp [hT]⟩
  have hrad : (alg A R₀ x k M).rad f = M + k := by
    refine le_antisymm (Alg.rad_le (by simp [hT])) ?_
    by_contra hlt'
    have := Alg.rad_spec hstop
    rw [hlt _ (not_le.1 hlt')] at this
    simp at this
  exact ⟨hstop, hrad, by simp [Alg.output, hrad, hT]⟩

/-! ### Facts about views of ring nodes -/

theorem distinct_view_iff (R : IdRing) (u : ℤ) :
    Distinct k M (R.view u) ↔ 2 * (M + k) + 1 ≤ R.n := by
  constructor
  · intro h
    by_contra hn
    rw [not_le] at hn
    have hn0 := R.n_pos
    have h1 := h (-((M + k : ℕ) : ℤ)) (-((M + k : ℕ) : ℤ) + R.n)
      (by rw [abs_le]; push_cast; constructor <;> omega)
      (by rw [abs_le]; push_cast; constructor <;> omega)
      (by simp only [IdRing.view_apply, ← add_assoc]; exact (R.periodic _).symm)
    omega
  · intro hn i j hi hj he
    by_contra hne
    refine R.id_ne_of_lt (i := u + i) (j := u + j) (by omega) ?_ he
    have : |u + i - (u + j)| ≤ |i| + |j| := by
      rw [show u + i - (u + j) = i + -j by ring]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    push_cast at hi hj
    omega

theorem matchAt_succ {R : IdRing} {u d : ℤ} (h : MatchAt R₀ x k M (R.view u) d) :
    MatchAt R₀ x k M (R.view (u + 1)) (d + 1) := fun i h1 h2 => by
  rw [← h i h1 h2]; simp only [IdRing.view_apply]; ring_nf

theorem matchAt_pred {R : IdRing} {u d : ℤ} (h : MatchAt R₀ x k M (R.view (u + 1)) d) :
    MatchAt R₀ x k M (R.view u) (d - 1) := fun i h1 h2 => by
  rw [← h i h1 h2]; simp only [IdRing.view_apply]; ring_nf

theorem matchAt_unique {f : ℤ → ℕ} (hf : Distinct k M f) {d₁ d₂ : ℤ}
    (h₁ : MatchAt R₀ x k M f d₁) (h₂ : MatchAt R₀ x k M f d₂) (h₁1 : 1 ≤ d₁) (h₁k : d₁ ≤ k)
    (h₂1 : 1 ≤ d₂) (h₂k : d₂ ≤ k) : d₁ = d₂ := by
  have e1 := h₁ 0 (by omega) (by omega)
  have e2 := h₂ 0 (by omega) (by omega)
  have := hf (0 - d₁) (0 - d₂) (by rw [abs_le]; push_cast; constructor <;> omega)
    (by rw [abs_le]; push_cast; constructor <;> omega) (e1.trans e2.symm)
  omega

/-- The copies of `x` (`e = 0`) and `y` (`e = k + 1`) seen by a node matching the pattern have
the same `M`-views as `x` and `y` in `R₀`. -/
theorem agreeOn_end {R : IdRing} {u d : ℤ} (h : MatchAt R₀ x k M (R.view u) d) {e : ℤ}
    (he : e = 0 ∨ e = k + 1) : AgreeOn M (R.view (u - d + e)) (R₀.view (x + e)) := by
  intro j hj
  rw [abs_le] at hj
  have := h (e + j) (by omega) (by omega)
  simp only [IdRing.view_apply] at this ⊢
  rw [show u - d + e + j = u + (e + j - d) by ring, this, add_assoc]

variable (hA : A.Valid) (hk : 1 ≤ k) (hMx : A.radAt R₀ x ≤ M)
  (hMy : A.radAt R₀ (x + (k + 1)) ≤ M)
include hA hk hMx hMy

theorem early_end {R : IdRing} {u d : ℤ} (h : MatchAt R₀ x k M (R.view u) d) {e : ℤ}
    (he : e = 0 ∨ e = k + 1) : Early A k M (R.view (u - d + e)) := by
  have hle : A.radAt R₀ (x + e) ≤ M := by rcases he with rfl | rfl <;> simpa
  obtain ⟨hs, hr, -⟩ := Alg.rad_eq_of_agreeOn (agreeOn_end h he).symm (hA.stops R₀ _) hle
  exact ⟨_, by unfold Alg.radAt at hle; omega, Alg.rad_spec hs⟩

omit hA hk hMx hMy in
theorem nbr_view (R : IdRing) (u a : ℤ) :
    nbr A k M (R.view u) a =
      if Early A k M (R.view (u + a)) then some (A.output (R.view (u + a))) else none := by
  unfold nbr; rw [sh_view]

omit hA hk hMx hMy in
theorem oddM_iff {f : ℤ → ℕ} (hf : Distinct k M f) {d : ℤ} (hd : MatchAt R₀ x k M f d)
    (h1 : 1 ≤ d) (h2 : d ≤ k) : OddM R₀ x k M f ↔ Odd d :=
  ⟨fun ⟨_, h1', h2', ho, hm⟩ => matchAt_unique hf hm hd h1' h2' h1 h2 ▸ ho,
   fun ho => ⟨d, h1, h2, ho, hd⟩⟩

/-- `A'` is a valid 4-colouring algorithm. -/
theorem alg_valid : (alg A R₀ x k M).Valid where
  stops R u := by
    by_cases h : Mod A R₀ x k M (R.view u)
    · exact (alg_of_mod h).1
    · exact (alg_of_not_mod h).1.2 (hA.stops R u)
  proper R u := by
    have hu1 : u + 1 + -1 = u := by ring
    unfold Alg.outAt
    by_cases hf : Mod A R₀ x k M (R.view u) <;> by_cases hg : Mod A R₀ x k M (R.view (u + 1))
    · -- both modified
      obtain ⟨hfe, hfd, d, hd1, hdk, hdm⟩ := hf
      obtain ⟨hge, hgd, d', hd'1, hd'k, hd'm⟩ := hg
      have hdk' : d ≠ k := by
        rintro rfl
        apply hge
        have := early_end hA hk hMx hMy hdm (e := k + 1) (Or.inr rfl)
        rwa [show u - k + (k + 1) = u + 1 by ring] at this
      have hd' : d' = d + 1 := matchAt_unique hgd hd'm (matchAt_succ hdm) hd'1 hd'k (by omega)
        (by omega)
      rw [(alg_of_mod ⟨hfe, hfd, d, hd1, hdk, hdm⟩).2.2,
        (alg_of_mod ⟨hge, hgd, d', hd'1, hd'k, hd'm⟩).2.2]
      unfold rule
      rw [nbr_view R u 1, nbr_view R (u + 1) (-1), hu1, ite_eq_right hge, ite_eq_right hfe]
      intro heq
      have s1 := (pick_spec (decide (OddM R₀ x k M (R.view u))) (nbr A k M (R.view u) (-1))
        none).2.2 (Or.inr rfl)
      have s2 := (pick_spec (decide (OddM R₀ x k M (R.view (u + 1)))) none
        (nbr A k M (R.view (u + 1)) 1)).2.2 (Or.inl rfl)
      rw [heq, s2] at s1
      rw [oddM_iff hfd hdm hd1 hdk, oddM_iff hgd hd'm hd'1 hd'k, hd'] at s1
      rcases Int.even_or_odd d with he | ho
      · have : ¬ Odd d := Int.not_odd_iff_even.2 he
        have : Odd (d + 1) := he.add_one
        simp_all
      · have : ¬ Odd (d + 1) := Int.not_odd_iff_even.2 ho.add_one
        simp_all
    · -- `u` modified, `u + 1` not
      obtain ⟨hfe, hfd, d, hd1, hdk, hdm⟩ := hf
      have hge : Early A k M (R.view (u + 1)) := by
        by_cases hdk' : d = k
        · subst hdk'
          have := early_end hA hk hMx hMy hdm (e := k + 1) (Or.inr rfl)
          rwa [show u - k + (k + 1) = u + 1 by ring] at this
        · by_contra hne
          exact hg ⟨hne, (distinct_view_iff R _).2 ((distinct_view_iff R u).1 hfd), d + 1,
            by omega, by omega, matchAt_succ hdm⟩
      rw [(alg_of_mod ⟨hfe, hfd, d, hd1, hdk, hdm⟩).2.2, (alg_of_not_mod hg).2.2]
      unfold rule
      rw [nbr_view (u := u) (a := 1), ite_eq_left hge]
      have := (pick_spec (decide (OddM R₀ x k M (R.view u))) (nbr A k M (R.view u) (-1))
        (some (A.output (R.view (u + 1))))).2.1
      exact fun h => this (congrArg some h.symm)
    · -- `u + 1` modified, `u` not
      obtain ⟨hge, hgd, d, hd1, hdk, hdm⟩ := hg
      have hfe : Early A k M (R.view u) := by
        by_cases hd1' : d = 1
        · subst hd1'
          have := early_end hA hk hMx hMy hdm (e := 0) (Or.inl rfl)
          rwa [show u + 1 - 1 + 0 = u by ring] at this
        · by_contra hne
          exact hf ⟨hne, (distinct_view_iff R _).2 ((distinct_view_iff R (u + 1)).1 hgd), d - 1,
            by omega, by omega, matchAt_pred hdm⟩
      rw [(alg_of_mod ⟨hge, hgd, d, hd1, hdk, hdm⟩).2.2, (alg_of_not_mod hf).2.2]
      unfold rule
      rw [nbr_view (u := u + 1) (a := -1), hu1, ite_eq_left hfe]
      have := (pick_spec (decide (OddM R₀ x k M (R.view (u + 1))))
        (some (A.output (R.view u))) (nbr A k M (R.view (u + 1)) 1)).1
      exact fun h => this (congrArg some h)
    · rw [(alg_of_not_mod hf).2.2, (alg_of_not_mod hg).2.2]
      exact hA.proper R u

omit hk hMx hMy in
/-- `A'` never uses a larger radius than `A`. -/
theorem radAt_alg_le (R : IdRing) (u : ℤ) : (alg A R₀ x k M).radAt R u ≤ A.radAt R u := by
  unfold Alg.radAt
  by_cases h : Mod A R₀ x k M (R.view u)
  · rw [(alg_of_mod h).2.1]
    exact (not_early_iff_le_rad (hA.stops R u)).1 h.1
  · rw [(alg_of_not_mod h).2.1]

omit hk hMx hMy in
/-- At a node between `x` and `y` with `A`-radius larger than `T`, `A'` uses radius `T`. -/
theorem radAt_alg_eq (hn : 2 * (M + k) + 1 ≤ R₀.n) {j : ℤ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hT : M + k < A.radAt R₀ (x + j)) : (alg A R₀ x k M).radAt R₀ (x + j) = M + k := by
  refine (alg_of_mod ⟨?_, (distinct_view_iff R₀ _).2 hn, j, hj1, hjk, ?_⟩).2.1
  · exact (not_early_iff_le_rad (hA.stops R₀ _)).2 hT.le
  · intro i _ _
    simp only [IdRing.view_apply]; ring_nf

end Lemma2

variable {A : Alg (Fin 4)}

/-- **Lemma 2** of [Feuilloley, PODC 2015]. Let `A` be a minimal 4-colouring algorithm, and `x`,
`y = x + k + 1` two nodes separated by `k` nodes. Then every node `x + j`, `1 ≤ j ≤ k`, between
them has radius at most `max {r(x), r(y)} + k`. (We assume the ring has at least
`2 (max {r(x), r(y)} + k) + 1` nodes.) -/
theorem lemma_2 (hA : A.IsMinimal) (R : IdRing) (x : ℤ) (k : ℕ)
    (hn : 2 * (max (A.radAt R x) (A.radAt R (x + (k + 1))) + k) + 1 ≤ R.n)
    (j : ℤ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    A.radAt R (x + j) ≤ max (A.radAt R x) (A.radAt R (x + (k + 1))) + k := by
  set M := max (A.radAt R x) (A.radAt R (x + (k + 1)))
  have hk : 1 ≤ k := by omega
  by_contra hT
  rw [not_le] at hT
  have hv := Lemma2.alg_valid (R₀ := R) (x := x) hA.1 hk (le_max_left _ _) (le_max_right _ _)
  have heq := hA.2 _ hv (Lemma2.radAt_alg_le hA.1) R (x + j)
  rw [Lemma2.radAt_alg_eq hA.1 hn hj1 hjk hT] at heq
  omega

end Podc.RingColoringAverage
