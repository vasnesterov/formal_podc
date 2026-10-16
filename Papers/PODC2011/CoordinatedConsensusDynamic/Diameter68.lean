import Papers.PODC2011.CoordinatedConsensusDynamic.StaticPathDefs

/-!
# Theorem 6.8: a static graph of diameter `D` on which deciding takes `Ω(nD/Δ)` rounds

The paper only sketches the proof and never specifies the graph `H`. We take

* the path `0 — 1 — ⋯ — (n-1)`,
* a *left star*: node `a` is joined to every node `x < a`,
* a *right star*: node `b` is joined to every node `y > b`,

with `b - a = D - 2`, so `H` has diameter `≤ D` (`hGraph_walk`): every node is within one hop of
the segment `[a, b]`, whose ends are `D - 2` apart. All round graphs we use are the path plus a
subset of the two stars, so they are connected.

`ex n a b σ p q` is the execution (inputs `σ`) whose round-`r` graph is the path, plus the left
star if `r ≤ p`, plus the right star if `r ≤ q`. `ex σ t t` is "static `H` up to time `t`, then
static path"; `ex σ 0 0` is the static path. With `T` the time at which indistinguishability is
measured and `h = b - a + 1`:

* (`stepL`) deleting the left star from the rounds `(p', p]` is invisible to node `n - 1` at time
  `T` provided the right star is only present up to round `q ≤ p' + h` and `T ≤ n - 1 - a`:
  information leaving the left star in round `> p'` travels along the path at speed `1` and
  reaches the right star at node `b` only after its last round `q`;
* (`stepR`) symmetrically, deleting the right star from rounds `(q', q]` is invisible to node `0`
  provided `p ≤ q' + h` and `T ≤ b`.

Alternating the two steps (each moves the higher of `p, q` to `(the lower) - h`) reaches the
static path in `⌈t/h⌉ + 1` steps (`walk_to_path`); two more steps flip the inputs of the two
halves of the path (`flipHi`, `flipLo`), which requires `2T + 2 ≤ n`. Lemma 6.4 then gives:
no node decides by time `t` as soon as `t + (⌈t/(D-1)⌉ + 3) Δ ≤ n/2 - 1` (`theorem_6_8`), i.e.
already for `t (D - 1 + Δ) + 4Δ(D - 1) ≤ (D - 1)(n/2 - 1)` (`theorem_6_8'`), which is
`Ω(nD/Δ)` for `D = O(Δ)` (and `Ω(n)` for `D ≥ Δ`). This matches the upper bound
`≈ nD/(D+Δ) + Δ` of the dynamic diameter-based protocol up to a constant factor.
-/

namespace CoordCons

namespace Diameter68

open DGraph Relation

/-! ### The graphs -/

/-- Edges of the path `0 — 1 — ⋯ — (n-1)`. -/
def pathE (n x y : ℕ) : Prop := x < n ∧ y < n ∧ (x + 1 = y ∨ y + 1 = x)

/-- Edges of the left star: `a` is joined to every `x < a`. -/
def starL (a x y : ℕ) : Prop := (x = a ∧ y < a) ∨ (y = a ∧ x < a)

/-- Edges of the right star: `b` is joined to every `y` with `b < y < n`. -/
def starR (n b x y : ℕ) : Prop := (x = b ∧ b < y ∧ y < n) ∨ (y = b ∧ b < x ∧ x < n)

/-- The static graph `H` of Theorem 6.8: the path plus both stars. -/
def hAdj (n a b x y : ℕ) : Prop := pathE n x y ∨ starL a x y ∨ starR n b x y

/-- The execution whose round-`r` graph is the path, plus the left star if `r ≤ p`, plus the
right star if `r ≤ q`. -/
def ex (n a b : ℕ) (σ : ℕ → Bool) (p q : ℕ) : DGraph Bool where
  V := Finset.range n
  input := σ
  N := n
  adj r x y := pathE n x y ∨ (r ≤ p ∧ starL a x y) ∨ (r ≤ q ∧ starR n b x y)

theorem starL_le {a x y : ℕ} (h : starL a x y) : x ≤ a ∧ y ≤ a := by
  unfold starL at h; omega

theorem starR_ge {n b x y : ℕ} (h : starR n b x y) : b ≤ x ∧ b ≤ y := by
  unfold starR at h; omega

theorem path_conn_zero {n : ℕ} : ∀ x, x < n → ReflTransGen (pathE n) 0 x := by
  intro x
  induction x with
  | zero => intro _; exact ReflTransGen.refl
  | succ x ih =>
    intro hx
    exact (ih (by omega)).tail ⟨by omega, hx, Or.inl rfl⟩

theorem ex_valid {n a b : ℕ} (σ : ℕ → Bool) (p q : ℕ) (hab : a ≤ b) (hbn : b < n) :
    (ex n a b σ p q).Valid where
  nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  mem r x y h := by
    simp only [ex, Finset.mem_range]
    rcases h with h | ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨h.1, h.2.1⟩
    · have := starL_le h; omega
    · unfold starR at h; omega
  symm r x y h := by
    simp only [ex] at h ⊢
    unfold pathE starL starR at *
    omega
  irrefl r x h := by
    simp only [ex] at h
    unfold pathE starL starR at h
    omega
  conn r _ x hx y hy := by
    simp only [ex, Finset.mem_range] at hx hy
    have hs : ∀ u v, pathE n u v → pathE n v u := fun u v h => by unfold pathE at *; omega
    have h1 := (path_conn_zero x hx).symm_of hs
    have h2 := path_conn_zero (n := n) y hy
    exact ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ (h1.trans h2)

theorem ex_knownN {n a b : ℕ} (σ : ℕ → Bool) (p q : ℕ) (hab : a ≤ b) (hbn : b < n) :
    KnownN n (ex n a b σ p q) :=
  ⟨ex_valid σ p q hab hbn, Finset.card_range n, rfl⟩

theorem mem_ex {n a b : ℕ} {σ : ℕ → Bool} {p q x : ℕ} : x ∈ (ex n a b σ p q).V ↔ x < n :=
  Finset.mem_range

/-! ### The two deletion steps -/

/-- **Deleting the left star** from rounds `(p', p]` is not noticed by node `n - 1` at time `T`,
provided the right star is present only up to round `q ≤ p' + (b - a + 1)` and
`T + a + 1 ≤ n`. -/
theorem stepL {n a b T p p' q : ℕ} (σ : ℕ → Bool) (hab : a ≤ b) (hbn : b < n) (hpp : p' ≤ p)
    (hq : q ≤ p' + (b - a + 1)) (hT : T + a + 1 ≤ n) :
    Indist (ex n a b σ p' q) (ex n a b σ p q) (n - 1) T := by
  have hG := ex_valid σ p' q hab hbn
  have hu : n - 1 ∈ (ex n a b σ p' q).V := mem_ex.2 (by omega)
  refine indist_of_agree hG hu rfl (fun w hw => ⟨mem_ex.2 (mem_ex.1 ((hw.mem_iff hG).2 hu)), rfl⟩)
    ?_
  intro w s hr x
  simp only [ex]
  by_cases h1 : s + 1 ≤ p'
  · simp [h1, show s + 1 ≤ p by omega]
  by_cases h2 : p < s + 1
  · simp [show ¬ s + 1 ≤ p by omega, h1]
  -- the round `s + 1` lies in `(p', p]`: `w` is not in the left star
  have hw : a < w := by
    by_contra hwa
    have key := StaticPath.reach_inv (P := fun τ y => y + (s + 1) ≤ a + τ) hr (by omega)
      (fun τ y z hτ hτT hP hyz => by
        rcases hyz with rfl | hyz
        · omega
        · rcases hyz with hp | ⟨hr', -⟩ | ⟨hr', hst⟩
          · unfold pathE at hp; omega
          · omega
          · have := starR_ge hst; omega)
    omega
  have : ¬ starL a x w := fun h => by have := starL_le h; omega
  simp [this]

/-- **Deleting the right star** from rounds `(q', q]` is not noticed by node `0` at time `T`,
provided the left star is present only up to round `p ≤ q' + (b - a + 1)` and `T ≤ b`. -/
theorem stepR {n a b T p q q' : ℕ} (σ : ℕ → Bool) (hab : a ≤ b) (hbn : b < n) (hqq : q' ≤ q)
    (hp : p ≤ q' + (b - a + 1)) (hT : T ≤ b) :
    Indist (ex n a b σ p q') (ex n a b σ p q) 0 T := by
  have hG := ex_valid σ p q' hab hbn
  have hu : 0 ∈ (ex n a b σ p q').V := mem_ex.2 (by omega)
  refine indist_of_agree hG hu rfl (fun w hw => ⟨mem_ex.2 (mem_ex.1 ((hw.mem_iff hG).2 hu)), rfl⟩)
    ?_
  intro w s hr x
  simp only [ex]
  by_cases h1 : s + 1 ≤ q'
  · simp [h1, show s + 1 ≤ q by omega]
  by_cases h2 : q < s + 1
  · simp [show ¬ s + 1 ≤ q by omega, h1]
  -- the round `s + 1` lies in `(q', q]`: `w` is not in the right star
  have hw : w < b := by
    by_contra hwb
    have key := StaticPath.reach_inv (P := fun τ y => b + (s + 1) ≤ y + τ) hr (by omega)
      (fun τ y z hτ hτT hP hyz => by
        rcases hyz with rfl | hyz
        · omega
        · rcases hyz with hp' | ⟨hr', hst⟩ | ⟨hr', -⟩
          · unfold pathE at hp'; omega
          · have := starL_le hst; omega
          · omega)
    omega
  have : ¬ starR n b x w := fun h => by have := starR_ge h; omega
  simp [this]

/-! ### Flipping inputs on the static path -/

/-- On the static path, node `n - 1` does not see the inputs of nodes `< n - 1 - T` by time
`T`. -/
theorem flipHi {n a b T : ℕ} {σ σ' : ℕ → Bool} (hab : a ≤ b) (hbn : b < n)
    (hσ : ∀ x, n - 1 - T ≤ x → σ x = σ' x) :
    Indist (ex n a b σ 0 0) (ex n a b σ' 0 0) (n - 1) T := by
  have hG := ex_valid σ 0 0 hab hbn
  have hu : n - 1 ∈ (ex n a b σ 0 0).V := mem_ex.2 (by omega)
  refine indist_of_agree hG hu rfl (fun w hw => ⟨mem_ex.2 (mem_ex.1 ((hw.mem_iff hG).2 hu)),
    hσ w ?_⟩) (fun _ _ _ _ => Iff.rfl)
  have key := StaticPath.reach_inv (P := fun τ y => y ≤ w + τ) hw (by omega)
    (fun τ y z hτ hτT hP hyz => by
      rcases hyz with rfl | hyz
      · omega
      · rcases hyz with hp' | ⟨hr', -⟩ | ⟨hr', -⟩
        · unfold pathE at hp'; omega
        · omega
        · omega)
  omega

/-- On the static path, node `0` does not see the inputs of nodes `> T` by time `T`. -/
theorem flipLo {n a b T : ℕ} {σ σ' : ℕ → Bool} (hab : a ≤ b) (hbn : b < n)
    (hσ : ∀ x, x ≤ T → σ x = σ' x) :
    Indist (ex n a b σ 0 0) (ex n a b σ' 0 0) 0 T := by
  have hG := ex_valid σ 0 0 hab hbn
  have hu : 0 ∈ (ex n a b σ 0 0).V := mem_ex.2 (by omega)
  refine indist_of_agree hG hu rfl (fun w hw => ⟨mem_ex.2 (mem_ex.1 ((hw.mem_iff hG).2 hu)),
    hσ w ?_⟩) (fun _ _ _ _ => Iff.rfl)
  have key := StaticPath.reach_inv (P := fun τ y => w ≤ y + τ) hw (by omega)
    (fun τ y z hτ hτT hP hyz => by
      rcases hyz with rfl | hyz
      · omega
      · rcases hyz with hp' | ⟨hr', -⟩ | ⟨hr', -⟩
        · unfold pathE at hp'; omega
        · omega
        · omega)
  omega

/-! ### The walk -/

/-- From `ex σ p q` with `|p - q| ≤ h` (`h = b - a + 1`) and `min p q ≤ k h`, the static path
`ex σ 0 0` is reached by a walk of length `k + 1` in the similarity graph at time `T`. -/
theorem walk_to_path {n a b T : ℕ} (σ : ℕ → Bool) (hab : a ≤ b) (hbn : b < n)
    (hT1 : T + a + 1 ≤ n) (hT2 : T ≤ b) (k : ℕ) :
    ∀ p q, p ≤ q + (b - a + 1) → q ≤ p + (b - a + 1) → min p q ≤ k * (b - a + 1) →
      Walk (KnownN n) T (k + 1) (ex n a b σ p q) (ex n a b σ 0 0) := by
  have hK : ∀ p q, KnownN n (ex n a b σ p q) := fun p q => ex_knownN σ p q hab hbn
  induction k with
  | zero =>
    intro p q hpq hqp hm
    rcases Nat.le_total p q with h | h
    · obtain rfl : p = 0 := by simp at hm; omega
      exact Walk.single ⟨hK _ _, hK _ _, _,
        (stepR (T := T) σ hab hbn (Nat.zero_le q) (by omega) hT2).symm⟩
    · obtain rfl : q = 0 := by simp at hm; omega
      exact Walk.single ⟨hK _ _, hK _ _, _,
        (stepL (T := T) σ hab hbn (Nat.zero_le p) (by omega) hT1).symm⟩
  | succ k ih =>
    intro p q hpq hqp hm
    rcases Nat.le_total p q with h | h
    · have s := (stepR (T := T) (p := p) (q := q) (q' := p - (b - a + 1)) σ hab hbn (by omega)
        (by omega) hT2).symm
      have w := ih p (p - (b - a + 1)) (by omega) (by omega)
        (by rw [min_eq_left h] at hm; rw [Nat.add_mul, one_mul] at hm
            exact (min_le_right _ _).trans (by omega))
      exact StaticPath.Walk.cast ((Walk.single ⟨hK _ _, hK _ _, _, s⟩).append w) (by omega)
    · have s := (stepL (T := T) (p := p) (p' := q - (b - a + 1)) (q := q) σ hab hbn (by omega)
        (by omega) hT1).symm
      have w := ih (q - (b - a + 1)) q (by omega) (by omega)
        (by rw [min_eq_right h] at hm; rw [Nat.add_mul, one_mul] at hm
            exact (min_le_left _ _).trans (by omega))
      exact StaticPath.Walk.cast ((Walk.single ⟨hK _ _, hK _ _, _, s⟩).append w) (by omega)

/-- From `H` for `t` rounds followed by the path, to the static path with all inputs `v`:
a walk of length `⌈t/h⌉ + 3` at time `T`. -/
theorem walk_to_uniform {n a b T : ℕ} (σ : ℕ → Bool) (v : Bool) (hab : a ≤ b) (hbn : b < n)
    (hT1 : T + a + 1 ≤ n) (hT2 : T ≤ b) (hT3 : 2 * T + 2 ≤ n) (t : ℕ) :
    Walk (KnownN n) T ((t + (b - a + 1) - 1) / (b - a + 1) + 3) (ex n a b σ t t)
      (ex n a b (fun _ => v) 0 0) := by
  have hK : ∀ σ p q, KnownN n (ex n a b σ p q) := fun σ p q => ex_knownN σ p q hab hbn
  set h := b - a + 1 with hh
  have hh1 : 1 ≤ h := by omega
  have hk : t ≤ (t + h - 1) / h * h := by
    have h2 := Nat.div_add_mod (t + h - 1) h
    have h3 := Nat.mod_lt (t + h - 1) (show 0 < h by omega)
    rw [mul_comm] at h2
    omega
  have w1 := walk_to_path σ hab hbn hT1 hT2 ((t + h - 1) / h) t t (by omega) (by omega)
    (by simpa using hk)
  let σ1 : ℕ → Bool := fun x => if x < n - 1 - T then v else σ x
  have s1 : Indist (ex n a b σ 0 0) (ex n a b σ1 0 0) (n - 1) T :=
    flipHi hab hbn fun x hx => by simp only [σ1]; rw [ite_eq_right (by omega)]
  have s2 : Indist (ex n a b σ1 0 0) (ex n a b (fun _ => v) 0 0) 0 T :=
    flipLo hab hbn fun x hx => by simp only [σ1]; rw [ite_eq_left (by omega)]
  exact StaticPath.Walk.cast ((w1.append (Walk.single ⟨hK _ _ _, hK _ _ _, _, s1⟩)).append
    (Walk.single ⟨hK _ _ _, hK _ _ _, _, s2⟩)) (by omega)

/-! ### The diameter of `H` -/

/-- `H` as a simple graph on `ℕ` (only the nodes `0, …, n-1` have edges). -/
def hGraph (n a b : ℕ) : SimpleGraph ℕ where
  Adj := hAdj n a b
  symm := ⟨fun x y h => by unfold hAdj pathE starL starR at *; omega⟩
  loopless := ⟨fun x h => by unfold hAdj pathE starL starR at h; omega⟩

theorem hGraph_adj_lt {n a b x y : ℕ} (hab : a ≤ b) (hbn : b < n) (h : (hGraph n a b).Adj x y) :
    x < n ∧ y < n := by
  change hAdj n a b x y at h
  unfold hAdj pathE starL starR at h; omega

/-- Walks along the path. -/
theorem path_walk {n a b : ℕ} : ∀ d x, x + d < n →
    ∃ w : (hGraph n a b).Walk x (x + d), w.length = d := by
  intro d
  induction d with
  | zero => intro x _; exact ⟨.nil, rfl⟩
  | succ d ih =>
    intro x hx
    obtain ⟨w, hw⟩ := ih (x + 1) (by omega)
    have hadj : (hGraph n a b).Adj x (x + 1) := Or.inl ⟨by omega, by omega, Or.inl rfl⟩
    rw [show x + (d + 1) = x + 1 + d by omega]
    exact ⟨.cons hadj w, by simp [hw]⟩

theorem path_walk' {n a b x y : ℕ} (hx : x < n) (hy : y < n) :
    ∃ w : (hGraph n a b).Walk x y, w.length ≤ max x y - min x y := by
  rcases Nat.le_total x y with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨w, hw⟩ := path_walk (a := a) (b := b) d x hy
    exact ⟨w, by omega⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨w, hw⟩ := path_walk (a := a) (b := b) d y hx
    exact ⟨w.reverse, by simp [hw]⟩

/-- Every node is within one hop of the segment `[a, b]`. -/
theorem to_core {n a b x : ℕ} (hab : a ≤ b) (hx : x < n) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∃ w : (hGraph n a b).Walk x c, w.length ≤ 1 := by
  by_cases h1 : x < a
  · have hadj : (hGraph n a b).Adj x a := Or.inr (Or.inl (Or.inr ⟨rfl, h1⟩))
    exact ⟨a, le_rfl, hab, .cons hadj .nil, by simp⟩
  by_cases h2 : b < x
  · have hadj : (hGraph n a b).Adj x b := Or.inr (Or.inr (Or.inr ⟨rfl, h2, hx⟩))
    exact ⟨b, hab, le_rfl, .cons hadj .nil, by simp⟩
  exact ⟨x, by omega, by omega, .nil, by simp⟩

/-- `H` has diameter at most `b - a + 2`. -/
theorem hGraph_walk {n a b x y : ℕ} (hab : a ≤ b) (hbn : b < n) (hx : x < n) (hy : y < n) :
    ∃ w : (hGraph n a b).Walk x y, w.length ≤ b - a + 2 := by
  obtain ⟨c, hc1, hc2, w1, hw1⟩ := to_core hab hx
  obtain ⟨d, hd1, hd2, w2, hw2⟩ := to_core hab hy
  obtain ⟨w, hw⟩ := path_walk' (a := a) (b := b) (show c < n by omega) (show d < n by omega)
  refine ⟨(w1.append w).append w2.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

/-! ### Theorem 6.8 -/

/-- The parameters: `T = n/2 - 1`, `b = T`, `a = T + 2 - D`. -/
abbrev parT (n : ℕ) : ℕ := n / 2 - 1

/-- **Theorem 6.8** of [KMO11], explicit form. For `2 ≤ D ≤ n/2 + 1` there is a static graph `H`
on `{0, …, n-1}` of diameter at most `D` such that, for every `Δ`-coordinated consensus
algorithm (with `n` known), every execution `G` on `{0, …, n-1}` whose communication graph is `H`
in all rounds `1, …, t`, and every node `u`: `u` has not decided by time `t`, provided
`t + (⌈t/(D-1)⌉ + 3) Δ ≤ n/2 - 1`. -/
theorem theorem_6_8 {n D' : ℕ} (hD : 2 ≤ D') (hDn : D' ≤ n / 2 + 1) :
    ∃ H : SimpleGraph ℕ, (∀ x y, H.Adj x y → x < n ∧ y < n) ∧
      (∀ x y, x < n → y < n → ∃ w : H.Walk x y, w.length ≤ D') ∧
      ∀ (Δ : ℕ) (D : Decision Bool), Consensus (KnownN n) D → Coordinated (KnownN n) Δ D →
        ∀ G : DGraph Bool, KnownN n G → G.V = Finset.range n →
        ∀ t, (∀ r, 1 ≤ r → r ≤ t → G.adj r = H.Adj) →
          t + ((t + D' - 2) / (D' - 1) + 3) * Δ ≤ n / 2 - 1 →
          ∀ u ∈ G.V, D G u t = none := by
  set T := n / 2 - 1 with hTdef
  set b := T with hb
  set a := T + 2 - D' with ha
  have hab : a ≤ b := by omega
  have hbn : b < n := by omega
  have hh : b - a + 1 = D' - 1 := by omega
  refine ⟨hGraph n a b, fun x y h => hGraph_adj_lt hab hbn h, fun x y hx hy => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hGraph_walk hab hbn hx hy
    exact ⟨w, by omega⟩
  intro Δ D hD hC G hG hV t hadj ht u hu
  -- reduce to the execution `ex σ t t` (locality)
  have hind : Indist G (ex n a b G.input t t) u t := by
    refine indist_of_agree hG.1 hu hG.2.2 (fun w hw => ⟨?_, rfl⟩) ?_
    · have := (hw.mem_iff hG.1).2 hu
      rw [hV] at this
      exact this
    · intro w s hr x
      have hst := hr.le
      rw [hadj (s + 1) (by omega) hst]
      simp only [ex, hGraph, hAdj, show s + 1 ≤ t from hst, true_and]
  rw [hD.loc _ _ _ _ hind]
  have hu' : u ∈ (ex n a b G.input t t).V := by rw [hV] at hu; exact hu
  have hT1 : T + a + 1 ≤ n := by omega
  have hT2 : T ≤ b := le_rfl
  have hT3 : 2 * T + 2 ≤ n := by omega
  have w0 := walk_to_uniform G.input false hab hbn hT1 hT2 hT3 t
  have w1 := walk_to_uniform G.input true hab hbn hT1 hT2 hT3 t
  rw [hh, show t + (D' - 1) - 1 = t + D' - 2 by omega] at w0 w1
  exact lemma_6_4 hD hC (ex_knownN _ t t hab hbn) w0 w1 ht ht (fun _ _ => rfl) (fun _ _ => rfl)
    u hu'

/-- **Theorem 6.8**, the `Ω(nD/Δ)` form: no node decides by time `t` as long as
`t (D - 1 + Δ) + 4Δ(D - 1) ≤ (D - 1)(n/2 - 1)`, i.e. until time
`≈ (D - 1)(n/2 - 1 - 4Δ)/(D - 1 + Δ)`, which is `≥ (D - 1)(n/2 - 1 - 4Δ)/(2Δ)` for
`D ≤ Δ + 1`. -/
theorem theorem_6_8' {n D' : ℕ} (hD : 2 ≤ D') (hDn : D' ≤ n / 2 + 1) :
    ∃ H : SimpleGraph ℕ, (∀ x y, H.Adj x y → x < n ∧ y < n) ∧
      (∀ x y, x < n → y < n → ∃ w : H.Walk x y, w.length ≤ D') ∧
      ∀ (Δ : ℕ) (D : Decision Bool), Consensus (KnownN n) D → Coordinated (KnownN n) Δ D →
        ∀ G : DGraph Bool, KnownN n G → G.V = Finset.range n →
        ∀ t, (∀ r, 1 ≤ r → r ≤ t → G.adj r = H.Adj) →
          t * (D' - 1 + Δ) + 4 * Δ * (D' - 1) ≤ (D' - 1) * (n / 2 - 1) →
          ∀ u ∈ G.V, D G u t = none := by
  obtain ⟨H, h1, h2, h3⟩ := theorem_6_8 hD hDn
  refine ⟨H, h1, h2, fun Δ D hD hC G hG hV t hadj ht => h3 Δ D hD hC G hG hV t hadj ?_⟩
  set h := D' - 1 with hh
  have hpos : 0 < h := by omega
  set k := (t + D' - 2) / h with hk
  have hkh : k * h ≤ t + h - 1 := by
    have h2 : k * h ≤ t + D' - 2 := Nat.div_mul_le_self _ _
    omega
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  have : h * ((k + 3) * Δ) ≤ (t + h - 1 + 3 * h) * Δ := by
    rw [show h * ((k + 3) * Δ) = (k * h + 3 * h) * Δ by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  have e : (t + h - 1 + 3 * h) * Δ ≤ t * Δ + 4 * Δ * h := by
    rw [show 4 * Δ * h = (4 * h) * Δ by ring, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_add]
  nlinarith

end Diameter68

end CoordCons
