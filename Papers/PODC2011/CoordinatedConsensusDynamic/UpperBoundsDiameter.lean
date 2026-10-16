import Papers.PODC2011.CoordinatedConsensusDynamic.UpperBounds

/-!
# The dynamic-diameter-based protocol (Section 6, after Lemma 6.3)

* `DiamLit`: Definition 3 read literally ("for all `t' ≤ t` and `u, v`:
  `(u, max{0, t' - D}) ↝ (v, t')`"). At `t' = 0` this demands `(u, 0) ↝ (v, 0)`, i.e. `u = v`, so
  **no execution with `n ≥ 2` has any finite dynamic diameter** (`not_diamLit`).
* `DiamUpTo`: the corrected definition (only `t'` with `D ≤ t' ≤ t`).
* `diamProtocol`: at time `n - kΔ - 1` a node decides `f(x̄)` if it knows the input assignment
  `x̄` and knows that, for some `D` with `(k-1)D ≤ n - kΔ - 1`, the graph had dynamic diameter
  `≤ D` up to time `(k-1)D`. It is an instance of the approximate `Δ`-ladder
  (`diamProtocol_solves`).
* Running time: `diamProtocol_decides` — in an execution of dynamic diameter `D` (up to time
  `kD`) every node has decided by `n - kΔ - 1` whenever `k(D + Δ) < n` (and `k ≤ kmax`);
  `diamProtocol_time` — hence by time `t < nD/(D+Δ) + Δ`.
  The paper's sharper claim that the nodes stop at `n - kmax·Δ - 1` for
  `kmax = ⌊n/(D + Δ)⌋` (under `(kmax - 1)D < n - kmax·Δ - 1`) is false:
  `diamProtocol_counterexample` (clique, `n = 4`, `D = Δ = 1`, `kmax = 2`: nobody decides at
  time `1`).
-/

namespace CoordCons

open DGraph Relation

variable {α : Type*}

/-! ### Dynamic diameter -/

/-- Definition 3, read literally: dynamic diameter `D` up to time `T`. -/
def DiamLit (G : DGraph α) (D T : ℕ) : Prop :=
  ∀ t' ≤ T, ∀ a ∈ G.V, ∀ b ∈ G.V, G.Reach a (t' - D) b t'

/-- The literal Definition 3 is vacuous: with two or more nodes no dynamic graph has a finite
dynamic diameter up to any time (the condition at `t' = 0` asks `(a, 0) ↝ (b, 0)`). -/
theorem not_diamLit {G : DGraph α} (h : 1 < G.V.card) (D T : ℕ) : ¬ DiamLit G D T := by
  intro hd
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
  have := hd 0 (Nat.zero_le _) a ha b hb
  rw [Nat.zero_sub] at this
  exact hab this.same_time

/-- Corrected Definition 3: dynamic diameter `≤ D` up to time `T`, i.e. `(a, t' - D) ↝ (b, t')`
for all `a, b` and all `D ≤ t' ≤ T`. -/
def DiamUpTo (G : DGraph α) (D T : ℕ) : Prop :=
  ∀ t', D ≤ t' → t' ≤ T → ∀ a ∈ G.V, ∀ b ∈ G.V, G.Reach a (t' - D) b t'

variable {G H : DGraph α} {D T T' : ℕ}

theorem DiamUpTo.mono (h : DiamUpTo G D T) (hT : T' ≤ T) : DiamUpTo G D T' :=
  fun t' h1 h2 => h t' h1 (le_trans h2 hT)

/-- The dynamic diameter up to `T` is determined by the views of all nodes at time `T`. -/
theorem DiamUpTo.congr (hV : G.V = H.V) (h : ∀ b ∈ G.V, Indist G H b T)
    (hd : DiamUpTo G D T) : DiamUpTo H D T := by
  intro t' h1 h2 a ha b hb
  rw [← hV] at ha hb
  exact ((h b hb).mono h2).reach_iff.1 (hd t' h1 h2 a ha b hb)

/-! ### The protocol -/

/-- If `w` has heard from every node's time-`T` state by time `s`, then every execution of the
same count that `w` cannot distinguish has the same nodes, the same inputs, and the same views
at time `T`. -/
theorem knownN_transfer {n : ℕ} {G H : DGraph α} (hG : KnownN n G) (hH : KnownN n H) {w s : ℕ}
    (h : Indist G H w s) (hr : ∀ b ∈ G.V, G.Reach b T w s) :
    H.V = G.V ∧ (∀ b ∈ G.V, H.input b = G.input b) ∧ ∀ b ∈ G.V, Indist G H b T := by
  have ib : ∀ b ∈ G.V, Indist G H b T := fun b hb => (h.reach (hr b hb)).2
  have sub : G.V ⊆ H.V := fun b hb => (ib b hb).mem_right
  refine ⟨(Finset.eq_of_subset_of_card_le sub (by rw [hH.2.1, hG.2.1])).symm,
    fun b hb => (ib b hb).zero.2.2.1.symm, ib⟩

theorem KnownN.self {n : ℕ} {G : DGraph α} (hG : KnownN n G) : KnownN G.N G :=
  ⟨hG.1, hG.2.1.trans hG.2.2.symm, rfl⟩

/-- Admissible decision functions: `f(x̄)` depends only on the inputs of the nodes, and
`f(0ⁿ) = 0`, `f(1ⁿ) = 1`. -/
structure GoodF (f : Finset ℕ → (ℕ → Bool) → Bool) : Prop where
  congr : ∀ V x y, (∀ a ∈ V, x a = y a) → f V x = f V y
  const : ∀ V : Finset ℕ, V.Nonempty → ∀ x b, (∀ a ∈ V, x a = b) → f V x = b

/-- Level-`k` decision formula of the dynamic-diameter protocol, evaluated at time
`n - kΔ - 1`: `u` knows the input assignment `x̄` (and `f(x̄) = v`), and knows that for some `D`
with `(k-1)D ≤ n - kΔ - 1` the graph had dynamic diameter `≤ D` up to time `(k-1)D`.
(For `k ∈ {0, 1}` the second conjunct is trivial: take `D = 1`.) -/
def PhiDiam (Δ : ℕ) (f : Finset ℕ → (ℕ → Bool) → Bool) (k : ℕ) (v : Bool) (G : DGraph Bool)
    (u : ℕ) : Prop :=
  (∃ V x, Knows (KnownN G.N) G u (G.N - k * Δ - 1)
      (fun H => H.V = V ∧ ∀ y ∈ V, H.input y = x y) ∧ f V x = v) ∧
    Knows (KnownN G.N) G u (G.N - k * Δ - 1)
      (fun H => ∃ D, (k - 1) * D ≤ G.N - k * Δ - 1 ∧ DiamUpTo H D ((k - 1) * D))

/-- The dynamic-diameter-based protocol. -/
noncomputable def diamProtocol (Δ kmax : ℕ) (f : Finset ℕ → (ℕ → Bool) → Bool) : Decision Bool :=
  ladder Δ kmax (PhiDiam Δ f)

section

variable {f : Finset ℕ → (ℕ → Bool) → Bool} {G : DGraph Bool}

/-- `w` knows the input assignment once it has heard from everyone. -/
theorem knows_inputs {n : ℕ} (hG : KnownN n G) {w s T : ℕ} (hr : ∀ b ∈ G.V, G.Reach b T w s) :
    Knows (KnownN G.N) G w s (fun H => H.V = G.V ∧ ∀ y ∈ G.V, H.input y = G.input y) := by
  intro H hH hGH
  rw [hG.2.2] at hH
  obtain ⟨h1, h2, -⟩ := knownN_transfer hG hH hGH hr
  exact ⟨h1, h2⟩

theorem reach_all_of_diam {D T : ℕ} (hd : DiamUpTo G D T) {w s t' : ℕ} (hw : w ∈ G.V)
    (h1 : D ≤ t') (h2 : t' ≤ T) (hs : t' ≤ s) : ∀ b ∈ G.V, G.Reach b (t' - D) w s :=
  fun b hb => (hd t' h1 h2 b hb w hw).trans (Reach.self hs)

/-- The hypotheses of Lemma 6.3 hold for the dynamic-diameter protocol, with
`A = v` meaning `f(x̄) = v`. -/
theorem diam_spec (n Δ kmax : ℕ) (hf : GoodF f) :
    LadderSpec (KnownN n) Δ kmax (PhiDiam Δ f) (fun G => f G.V G.input) where
  loc k v G H u h := by
    have hN := h.N_eq
    unfold PhiDiam
    rw [← hN]
    simp only [knows_congr h]
  N_pos G hG := by
    rw [hG.2.2, ← hG.2.1]; exact Finset.card_pos.2 hG.1.nonempty
  val_valid G hG := by
    by_contra hne
    have hc := hf.const G.V hG.1.nonempty G.input (!f G.V G.input) (fun a ha => by
      cases h : G.input a <;> cases h' : f G.V G.input <;>
        first | rfl | exact absurd ⟨a, ha, by rw [h, h']⟩ hne)
    cases h : f G.V G.input <;> rw [h] at hc <;> simp at hc
  consistency G hG u hu v h := by
    obtain ⟨⟨V, x, hk, hfv⟩, -⟩ := h
    obtain ⟨hV, hx⟩ := hk G hG.self (Indist.refl hG.1 hu _)
    subst hV
    rw [← hfv]
    exact hf.congr _ _ _ hx
  timeliness G hG u hu := by
    have hr : ∀ b ∈ G.V, G.Reach b 0 u (G.N - 0 * Δ - 1) := by
      intro b hb
      have hp := past_eq_V hG.1 hu (s := 0) (t := G.N - 0 * Δ - 1)
        (by rw [hG.2.2, ← hG.2.1]; have := Finset.card_pos.2 hG.1.nonempty; simp; omega)
      exact (mem_past.1 (hp ▸ hb)).2
    refine ⟨f G.V G.input, ⟨G.V, G.input, knows_inputs hG hr, rfl⟩, ?_⟩
    intro H _ _
    exact ⟨1, by simp, fun t' h1 h2 => by simp at h2; omega⟩
  coordination G hG k hk1 hk hkN u hu v h w hw := by
    obtain ⟨⟨V, x, hkn, hfv⟩, hkd⟩ := h
    obtain ⟨hV, hx⟩ := hkn G hG.self (Indist.refl hG.1 hu _)
    subst hV
    obtain ⟨D, hD, hd⟩ := hkd G hG.self (Indist.refl hG.1 hu _)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hD hd ⊢
    have e : (j + 1) * Δ = j * Δ + Δ := by ring
    rw [e] at hkN hD
    -- every node's state at time `(j-1)D` has reached `w` by time `n - jΔ - 1`
    have hr : ∀ b ∈ G.V, G.Reach b ((j - 1) * D) w (G.N - j * Δ - 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · intro b hb
        have hp := past_eq_V hG.1 hw (s := 0) (t := G.N - 0 * Δ - 1)
          (by rw [hG.2.2, ← hG.2.1]; have := Finset.card_pos.2 hG.1.nonempty; simp; omega)
        have := (mem_past.1 (hp ▸ hb : b ∈ G.past w (G.N - 0 * Δ - 1) 0)).2
        simpa using this
      · have hjD : D ≤ j * D := Nat.le_mul_of_pos_left D hj
        have e2 : j * D - D = (j - 1) * D := by
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; rw [add_mul, one_mul, Nat.add_sub_cancel]
        rw [← e2]
        exact reach_all_of_diam hd hw hjD le_rfl (by omega)
    have hle : (j - 1) * D ≤ j * D := Nat.mul_le_mul_right D (by omega)
    refine ⟨⟨G.V, x, ?_, hfv⟩, ?_⟩
    · intro H hH hGH
      rw [hG.2.2] at hH
      obtain ⟨h1, h2, -⟩ := knownN_transfer hG hH hGH hr
      exact ⟨h1, fun y hy => (h2 y hy).trans (hx y hy)⟩
    · intro H hH hGH
      rw [hG.2.2] at hH
      obtain ⟨h1, -, h3⟩ := knownN_transfer hG hH hGH hr
      exact ⟨D, by omega, (hd.mono hle).congr h1.symm h3⟩

/-- **The dynamic-diameter protocol solves `Δ`-coordinated consensus** (count known), for any
`f` with `f(0ⁿ) = 0`, `f(1ⁿ) = 1`. -/
theorem diamProtocol_solves (n Δ kmax : ℕ) (hf : GoodF f) :
    Consensus (KnownN n) (diamProtocol Δ kmax f) ∧
      Coordinated (KnownN n) Δ (diamProtocol Δ kmax f) :=
  ladder_solves (diam_spec n Δ kmax hf)

/-- **Running time (what is true).** If the execution has (corrected) dynamic diameter `≤ D` up
to time `kD`, `1 ≤ k ≤ kmax` and `k(D + Δ) < n`, then every node has decided by time
`n - kΔ - 1`. (The level-`k` rule needs every node's state at time `(k-1)D` to reach `u`, which
takes until time `kD`; hence `k(D+Δ) ≤ n - 1` rather than the paper's `(k-1)D ≤ n - kΔ - 1`.) -/
theorem diamProtocol_decides {n Δ kmax D k : ℕ} (hG : KnownN n G) (hk1 : 1 ≤ k) (hk : k ≤ kmax)
    (hkn : k * (D + Δ) + 1 ≤ n) (hd : DiamUpTo G D (k * D)) :
    ∀ u ∈ G.V, (diamProtocol Δ kmax f G u (n - k * Δ - 1)).isSome := by
  intro u hu
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e1 : (j + 1) * (D + Δ) = (j + 1) * D + (j + 1) * Δ := by ring
  have e2 : (j + 1) * D - D = j * D := by rw [add_mul, one_mul, Nat.add_sub_cancel]
  have hr : ∀ b ∈ G.V, G.Reach b (j * D) u (n - (j + 1) * Δ - 1) := by
    rw [← e2]
    exact reach_all_of_diam hd hu (by nlinarith) le_rfl (by omega)
  refine firstFire_isSome (ladderRule_isSome (v := f G.V G.input)
    ⟨j + 1, hk, by rw [hG.2.2]; omega, ?_⟩) le_rfl
  simp only [PhiDiam, Nat.add_sub_cancel, hG.2.2]
  refine ⟨⟨G.V, G.input, ?_, rfl⟩, ?_⟩
  · intro H hH hGH
    obtain ⟨h1, h2, -⟩ := knownN_transfer hG hH hGH hr
    exact ⟨h1, h2⟩
  · intro H hH hGH
    obtain ⟨h1, -, h3⟩ := knownN_transfer hG hH hGH hr
    exact ⟨D, by omega, (hd.mono (by nlinarith)).congr h1.symm h3⟩

/-- **Running time, `nD/(D+Δ) + Δ` form.** In an execution of (corrected) dynamic diameter
`D ≥ 1` (up to time `n`), with `kmax ≥ ⌊(n-1)/(D+Δ)⌋`, every node has decided by time
`t = n - ⌊(n-1)/(D+Δ)⌋·Δ - 1`, and `t·(D+Δ) < nD + Δ(D+Δ)`, i.e. `t < nD/(D+Δ) + Δ`. -/
theorem diamProtocol_time {n Δ kmax D : ℕ} (hf : GoodF f) (hG : KnownN n G) (hD : 1 ≤ D)
    (hd : DiamUpTo G D n) (hk : (n - 1) / (D + Δ) ≤ kmax) :
    (∀ u ∈ G.V, (diamProtocol Δ kmax f G u (n - (n - 1) / (D + Δ) * Δ - 1)).isSome) ∧
      (n - (n - 1) / (D + Δ) * Δ - 1) * (D + Δ) < n * D + Δ * (D + Δ) := by
  set q := (n - 1) / (D + Δ) with hq
  set r := (n - 1) % (D + Δ) with hr
  have hdm : (D + Δ) * q + r = n - 1 := Nat.div_add_mod _ _
  have hrlt : r < D + Δ := Nat.mod_lt _ (by omega)
  have hn : 1 ≤ n := by rw [← hG.2.1]; exact Finset.card_pos.2 hG.1.nonempty
  have ht : n - q * Δ - 1 = q * D + r := by
    have : (D + Δ) * q = q * D + q * Δ := by ring
    omega
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos q with h0 | hq1
    · intro u hu
      rw [h0, zero_mul, Nat.sub_zero]
      obtain ⟨v, hv⟩ := (diam_spec n Δ kmax hf).timeliness G hG u hu
      refine firstFire_isSome (ladderRule_isSome (v := v) ⟨0, Nat.zero_le _, ?_, hv⟩) le_rfl
      rw [hG.2.2]; omega
    · have hqD : q * (D + Δ) + 1 ≤ n := by
        have : q * (D + Δ) = (D + Δ) * q := by ring
        omega
      exact diamProtocol_decides hG hq1 hk hqD (hd.mono (by nlinarith))
  · rw [ht]
    have hn' : n = (D + Δ) * q + r + 1 := by omega
    rw [hn']
    nlinarith

/-- With `Δ ≥ n` the protocol never decides before time `n - 1`, so its running time is not
`O(nD/Δ)` there (cf. the abstract's `min{O(nD/Δ), n - Ω(nΔ/D)}`). -/
theorem diamProtocol_eq_none_of_le {Δ kmax : ℕ} {u t : ℕ} (hΔ : G.N ≤ Δ) (ht : t + 1 < G.N) :
    diamProtocol Δ kmax f G u t = none :=
  ladder_eq_none_of_le hΔ ht

end

/-! ### Counterexample to the paper's running-time claim -/

/-- The complete graph on `{0,1,2,3}` in every round, all inputs `false`, `N = 4`. -/
def clique4 : DGraph Bool where
  V := Finset.range 4
  input := fun _ => false
  N := 4
  adj := fun _ x y => x < 4 ∧ y < 4 ∧ x ≠ y

/-- As `clique4`, except that round `1` is the star centred at `u`. -/
def star4 (u : ℕ) : DGraph Bool where
  V := Finset.range 4
  input := fun _ => false
  N := 4
  adj := fun r x y => (r = 1 → x = u ∨ y = u) ∧ x < 4 ∧ y < 4 ∧ x ≠ y

theorem clique4_knownN : KnownN 4 clique4 := by
  refine ⟨⟨⟨0, by simp [clique4]⟩, ?_, ?_, ?_, ?_⟩, by simp [clique4], rfl⟩
  · intro r x y h; simp only [clique4, Finset.mem_range] at h ⊢; omega
  · intro r x y h; simp only [clique4] at h ⊢; omega
  · intro r x h; simp [clique4] at h
  · intro r _ x hx y hy
    simp only [clique4, Finset.mem_range] at hx hy
    by_cases hxy : x = y
    · subst hxy; exact ReflTransGen.refl
    · exact ReflTransGen.single ⟨hx, hy, hxy⟩

theorem star4_knownN {u : ℕ} (hu : u < 4) : KnownN 4 (star4 u) := by
  refine ⟨⟨⟨0, by simp [star4]⟩, ?_, ?_, ?_, ?_⟩, by simp [star4], rfl⟩
  · intro r x y h; simp only [star4, Finset.mem_range] at h ⊢; omega
  · intro r x y h; simp only [star4] at h ⊢
    exact ⟨fun hr => (h.1 hr).symm, h.2.2.1, h.2.1, fun e => h.2.2.2 e.symm⟩
  · intro r x h; simp [star4] at h
  · intro r _ x hx y hy
    simp only [star4, Finset.mem_range] at hx hy
    by_cases hxy : x = y
    · subst hxy; exact ReflTransGen.refl
    by_cases hxu : x = u
    · subst hxu; exact ReflTransGen.single ⟨fun _ => Or.inl rfl, hx, hy, hxy⟩
    by_cases hyu : y = u
    · subst hyu; exact ReflTransGen.single ⟨fun _ => Or.inr rfl, hx, hy, hxy⟩
    exact ReflTransGen.head (b := u) ⟨fun _ => Or.inr rfl, hx, hu, hxu⟩
      (ReflTransGen.single ⟨fun _ => Or.inl rfl, hu, hy, fun e => hyu e.symm⟩)

/-- The clique has (corrected) dynamic diameter `1` at all times, and satisfies the paper's
constraint `(kmax - 1)D ≤ n - kmax·Δ - 1` with `kmax = ⌊n/(D+Δ)⌋ = 2`. -/
theorem clique4_diam (T : ℕ) : DiamUpTo clique4 1 T ∧ (2 - 1) * 1 ≤ 4 - 2 * 1 - 1 ∧
    2 = 4 / (1 + 1) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro t' h1 _ a ha b hb
  simp only [clique4, Finset.mem_range] at ha hb
  obtain ⟨s, rfl⟩ : ∃ s, t' = s + 1 := ⟨t' - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  by_cases hab : a = b
  · subst hab; exact Reach.step .refl (Or.inl rfl)
  · exact Reach.step .refl (Or.inr ⟨ha, hb, hab⟩)

/-- **Counterexample** to "if `kmax ≥ ⌊n/(D+Δ)⌋`, nodes can stop as early as time
`n - kmax·Δ - 1`": in the clique with `n = 4`, `D = Δ = 1`, `kmax = 2`, no node has decided at
time `n - kmax·Δ - 1 = 1` (whatever `f`): at time `1` node `u` cannot exclude that round `1` was
a star centred at `u`, whose dynamic diameter up to time `1` is not `≤ 1`. -/
theorem diamProtocol_counterexample (f : Finset ℕ → (ℕ → Bool) → Bool) :
    ∀ u ∈ clique4.V, diamProtocol 1 2 f clique4 u (4 - 2 * 1 - 1) = none := by
  intro u hu
  have hu4 : u < 4 := by simpa [clique4] using hu
  cases h : diamProtocol 1 2 f clique4 u (4 - 2 * 1 - 1) with
  | none => rfl
  | some v =>
  exfalso
  obtain ⟨s, hs, hs'⟩ := exists_of_firstFire h
  obtain ⟨k, hk, hkN, hΦ⟩ := ladderRule_eq_some hs'
  have hN : clique4.N = 4 := rfl
  rw [hN] at hkN
  obtain ⟨rfl, rfl⟩ : s = 1 ∧ k = 2 := by omega
  obtain ⟨-, hkd⟩ := hΦ
  -- `u` cannot distinguish the clique from the star centred at `u`
  have hind : Indist clique4 (star4 u) u 1 := by
    refine indist_of_agree clique4_knownN.1 hu rfl ?_ ?_
    · intro w hw
      exact ⟨by simpa [star4, clique4] using (hw.mem_iff clique4_knownN.1).2 hu, rfl⟩
    · intro w s hw x
      have hs1 := hw.le
      obtain rfl : s = 0 := by omega
      obtain rfl := hw.same_time
      simp [clique4, star4]
  obtain ⟨D, hD, hd⟩ := hkd (star4 u) (star4_knownN hu4) hind
  simp only [hN] at hD
  have ha : (u + 1) % 4 ∈ (star4 u).V := by simp [star4]; omega
  have hb : (u + 2) % 4 ∈ (star4 u).V := by simp [star4]; omega
  have hab : (u + 1) % 4 ≠ (u + 2) % 4 := by omega
  rcases Nat.lt_or_ge D 1 with hD0 | hD1
  · obtain rfl : D = 0 := by omega
    have := hd 0 le_rfl (by simp) _ ha _ hb
    exact hab this.same_time
  · obtain rfl : D = 1 := by omega
    have := hd 1 le_rfl (by simp) _ ha _ hb
    obtain ⟨y, hy, hr⟩ := this.front (by omega)
    obtain rfl := hr.same_time
    rcases hy with hy | hy
    · exact hab hy
    · have h1 := hy.1 rfl
      omega

/-! ### A counterexample satisfying the paper's strict constraint -/

/-- Undirected edge relation given by a list of pairs. -/
def ed (L : List (ℕ × ℕ)) (x y : ℕ) : Prop := (x, y) ∈ L ∨ (y, x) ∈ L

instance (L : List (ℕ × ℕ)) : DecidableRel (ed L) := fun _ _ => by unfold ed; infer_instance

/-- The static graph with edges `01, 02, 03, 14, 24, 35, 45` (diameter `2`). -/
def E6 : List (ℕ × ℕ) := [(0,1), (0,2), (0,3), (1,4), (2,4), (3,5), (4,5)]
/-- Round 2 of the indistinguishable execution. -/
def E6r2 : List (ℕ × ℕ) := [(0,1), (0,2), (0,3), (3,5), (4,5)]
/-- Round 3 of the indistinguishable execution. -/
def E6r3 : List (ℕ × ℕ) := [(1,2), (1,4), (0,3), (3,5), (4,5)]

/-- The static diameter-`2` graph on six nodes, all inputs `false`, `N = 6`. -/
def g6 : DGraph Bool where
  V := Finset.range 6
  input := fun _ => false
  N := 6
  adj := fun _ => ed E6

/-- As `g6`, but rounds 2 and 3 are changed away from node `3`'s causal past at time `3`, so
that node `2` has not heard from node `5` by time `3`. -/
def h6 : DGraph Bool where
  V := Finset.range 6
  input := fun _ => false
  N := 6
  adj := fun r => if r = 2 then ed E6r2 else if r = 3 then ed E6r3 else ed E6

theorem ed_lt {L : List (ℕ × ℕ)} (hL : ∀ p ∈ L, p.1 < 6 ∧ p.2 < 6 ∧ p.1 ≠ p.2) {x y : ℕ}
    (h : ed L x y) : x < 6 ∧ y < 6 ∧ x ≠ y := by
  rcases h with h | h
  · exact hL _ h
  · obtain ⟨h1, h2, h3⟩ := hL _ h; exact ⟨h2, h1, fun e => h3 e.symm⟩

theorem valid_of_lists {G : DGraph Bool} (hV : G.V = Finset.range 6)
    (hL : ∀ r, ∃ L : List (ℕ × ℕ), G.adj r = ed L ∧ (∀ p ∈ L, p.1 < 6 ∧ p.2 < 6 ∧ p.1 ≠ p.2) ∧
      ∀ x < 6, ReflTransGen (ed L) x 0) : G.Valid := by
  refine ⟨⟨0, by simp [hV]⟩, fun r x y h => ?_, fun r x y h => ?_, fun r x h => ?_,
    fun r _ x hx y hy => ?_⟩
  · obtain ⟨L, hE, hl, -⟩ := hL r
    rw [hE] at h
    have := ed_lt hl h
    simp only [hV, Finset.mem_range]; exact ⟨this.1, this.2.1⟩
  · obtain ⟨L, hE, -, -⟩ := hL r
    rw [hE] at h ⊢; exact h.symm
  · obtain ⟨L, hE, hl, -⟩ := hL r
    rw [hE] at h; exact (ed_lt hl h).2.2 rfl
  · obtain ⟨L, hE, -, hc⟩ := hL r
    rw [hE]
    simp only [hV, Finset.mem_range] at hx hy
    exact (hc x hx).trans ((hc y hy).symm_of (fun a b h => Or.symm h))

theorem e6_conn : ∀ x < 6, ReflTransGen (ed E6) x 0 := by
  intro x hx
  interval_cases x
  · exact .refl
  · exact .single (by decide)
  · exact .single (by decide)
  · exact .single (by decide)
  · exact .head (b := 1) (by decide) (.single (by decide))
  · exact .head (b := 3) (by decide) (.single (by decide))

theorem e6r2_conn : ∀ x < 6, ReflTransGen (ed E6r2) x 0 := by
  intro x hx
  interval_cases x
  · exact .refl
  · exact .single (by decide)
  · exact .single (by decide)
  · exact .single (by decide)
  · exact .head (b := 5) (by decide) (.head (b := 3) (by decide) (.single (by decide)))
  · exact .head (b := 3) (by decide) (.single (by decide))

theorem e6r3_conn : ∀ x < 6, ReflTransGen (ed E6r3) x 0 := by
  intro x hx
  have h4 : ReflTransGen (ed E6r3) 4 0 :=
    .head (b := 5) (by decide) (.head (b := 3) (by decide) (.single (by decide)))
  interval_cases x
  · exact .refl
  · exact .head (b := 4) (by decide) h4
  · exact .head (b := 1) (by decide) (.head (b := 4) (by decide) h4)
  · exact .single (by decide)
  · exact h4
  · exact .head (b := 3) (by decide) (.single (by decide))

theorem g6_knownN : KnownN 6 g6 :=
  ⟨valid_of_lists rfl (fun _ => ⟨E6, rfl, by decide, e6_conn⟩), by simp [g6], rfl⟩

theorem h6_knownN : KnownN 6 h6 := by
  refine ⟨valid_of_lists rfl (fun r => ?_), by simp [h6], rfl⟩
  by_cases h2 : r = 2
  · exact ⟨E6r2, by simp [h6, h2], by decide, e6r2_conn⟩
  by_cases h3 : r = 3
  · exact ⟨E6r3, by simp [h6, h3], by decide, e6r3_conn⟩
  · exact ⟨E6, by simp [h6, h2, h3], by decide, e6_conn⟩

/-- `g6` has (corrected) dynamic diameter `≤ 2` at all times (it is a static graph of
diameter `2`). -/
theorem g6_diam (T : ℕ) : DiamUpTo g6 2 T := by
  intro t' h2 _ a ha b hb
  simp only [g6, Finset.mem_range] at ha hb
  have hmid : ∀ a < 6, ∀ b < 6, ∃ m < 6, (a = m ∨ ed E6 a m) ∧ (m = b ∨ ed E6 m b) := by decide
  obtain ⟨m, -, h1, h2'⟩ := hmid a ha b hb
  obtain ⟨s, rfl⟩ : ∃ s, t' = s + 2 := ⟨t' - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  exact .step (.step .refl h1) h2'

/-- Node `3` cannot distinguish `g6` from `h6` at time `3`. -/
theorem g6_h6_indist : Indist g6 h6 3 3 := by
  have hbound : ∀ {L : List (ℕ × ℕ)}, (∀ p ∈ L, p.1 < 6 ∧ p.2 < 6 ∧ p.1 ≠ p.2) →
      ∀ x w, ed L x w → x < 6 := fun hl x w h => (ed_lt hl h).1
  refine indist_of_agree g6_knownN.1 (by simp [g6]) rfl
    (fun w hw => ⟨by simpa [g6, h6] using (hw.mem_iff g6_knownN.1).2 (by simp [g6]), rfl⟩) ?_
  intro w s hw x
  have hs := hw.le
  by_cases hs1 : s + 1 = 1
  · simp [g6, h6, hs1]
  by_cases hs2 : s + 1 = 2
  · -- `w ∈ {0, 3, 5}`
    obtain ⟨y, hy, hr⟩ := (hs2 ▸ hw).front (by omega)
    obtain rfl := hr.same_time
    have hw' : w = 0 ∨ w = 3 ∨ w = 5 := by
      rcases hy with rfl | hy
      · right; left; rfl
      · have hy' : ed E6 w 3 := hy
        have := (ed_lt (L := E6) (by decide) hy').1
        clear hw hy
        interval_cases w <;> revert hy' <;> decide
    simp only [g6, h6, hs2, if_true]
    have key : ∀ w ∈ [0, 3, 5], ∀ x < 6, (ed E6 x w ↔ ed E6r2 x w) := by decide
    by_cases hx : x < 6
    · exact key w (by rcases hw' with rfl | rfl | rfl <;> simp) x hx
    · exact iff_of_false (fun h => hx (hbound (by decide) x w h))
        (fun h => hx (hbound (by decide) x w h))
  · have hs3 : s + 1 = 3 := by omega
    obtain rfl : w = 3 := (hs3 ▸ hw).same_time
    simp only [g6, h6, hs3, show (3 : ℕ) ≠ 2 by decide, if_false, if_true]
    have key : ∀ x < 6, (ed E6 x 3 ↔ ed E6r3 x 3) := by decide
    by_cases hx : x < 6
    · exact key x hx
    · exact iff_of_false (fun h => hx (hbound (by decide) x 3 h))
        (fun h => hx (hbound (by decide) x 3 h))

/-- The nodes of `h6` that may have heard from node `5` by time `τ`. -/
abbrev hold6 (τ x : ℕ) : Prop :=
  x < 6 ∧ (τ = 0 → x = 5) ∧ (τ = 1 → x = 3 ∨ x = 4 ∨ x = 5) ∧
    (τ = 2 → x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5) ∧ (τ = 3 → x ≠ 2)

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- In `h6`, node `2` has not heard from node `5` by time `3`. -/
theorem h6_not_reach : ¬ h6.Reach 5 0 2 3 := by
  have a1 : h6.adj 1 = ed E6 := by simp [h6]
  have a2 : h6.adj 2 = ed E6r2 := by simp [h6]
  have a3 : h6.adj 3 = ed E6r3 := by simp [h6]
  have hstep : ∀ τ < 3, ∀ x < 6, ∀ y < 6, (x = y ∨ h6.adj (τ + 1) x y) →
      hold6 τ x → hold6 (τ + 1) y := by
    intro τ hτ
    interval_cases τ
    · rw [a1]; simp only [hold6, ed, E6]; decide
    · rw [a2]; simp only [hold6, ed, E6r2]; decide
    · rw [a3]; simp only [hold6, ed, E6r3]; decide
  have key : ∀ {v s u t : ℕ}, h6.Reach v s u t → hold6 s v → t ≤ 3 → hold6 t u := by
    intro v s u t h h0 ht
    induction h with
    | refl => exact h0
    | @step w u t hr hwu ih =>
      have hw := ih (by omega)
      have hu : u < 6 := by
        rcases hwu with rfl | hwu
        · exact hw.1
        · have := (h6_knownN.1.mem _ _ _ hwu).2; simpa [h6] using this
      exact hstep t (by omega) w hw.1 u hu hwu hw
  intro h
  exact (key h ⟨by norm_num, fun _ => rfl, by omega, by omega, by omega⟩ le_rfl).2.2.2.2 rfl rfl

/-- `h6` has dynamic diameter `> D` up to time `D` for every `D ≤ 3`. -/
theorem h6_not_diam {D : ℕ} (hD : D ≤ 3) : ¬ DiamUpTo h6 D D := by
  intro hd
  have h0 : (0 : ℕ) ∈ h6.V := by simp [h6]
  have h1 : (1 : ℕ) ∈ h6.V := by simp [h6]
  have h2 : (2 : ℕ) ∈ h6.V := by simp [h6]
  have h5 : (5 : ℕ) ∈ h6.V := by simp [h6]
  interval_cases D
  · exact absurd (hd 0 le_rfl le_rfl 0 h0 1 h1).same_time (by decide)
  · have := hd 1 le_rfl le_rfl 0 h0 5 h5
    obtain ⟨y, hy, hr⟩ := this.front (by norm_num)
    obtain rfl := hr.same_time
    rcases hy with hy | hy
    · exact absurd hy (by decide)
    · exact absurd hy (by simp [h6]; decide)
  · exact h6_not_reach (hd 2 le_rfl le_rfl 5 h5 2 h2).stay
  · exact h6_not_reach (hd 3 le_rfl le_rfl 5 h5 2 h2)

/-- **Counterexample meeting the paper's strict constraint.** `n = 6`, `D = 2`, `Δ = 1`,
`kmax = 2 = ⌊n/(D+Δ)⌋`, with `(kmax - 1)D < n - kmax·Δ - 1` (`2 < 3`), and a static graph of
diameter `2`. Node `3` has not decided at time `n - kmax·Δ - 1 = 3`: it cannot exclude an
execution in which node `2` has not heard from node `5` by time `3`. -/
theorem diamProtocol_counterexample_strict (f : Finset ℕ → (ℕ → Bool) → Bool) :
    (∀ T, DiamUpTo g6 2 T) ∧ (2 - 1) * 2 < 6 - 2 * 1 - 1 ∧ 6 / (2 + 1) ≤ 2 ∧
      diamProtocol 1 2 f g6 3 (6 - 2 * 1 - 1) = none := by
  refine ⟨g6_diam, by norm_num, by norm_num, ?_⟩
  cases h : diamProtocol 1 2 f g6 3 (6 - 2 * 1 - 1) with
  | none => rfl
  | some v =>
  exfalso
  obtain ⟨s, hs, hs'⟩ := exists_of_firstFire h
  obtain ⟨k, hk, hkN, hΦ⟩ := ladderRule_eq_some hs'
  have hN : g6.N = 6 := rfl
  rw [hN] at hkN
  obtain ⟨rfl, rfl⟩ : s = 3 ∧ k = 2 := by omega
  obtain ⟨-, hkd⟩ := hΦ
  obtain ⟨D, hD, hd⟩ := hkd h6 h6_knownN (by simpa [hN] using g6_h6_indist)
  simp only [hN] at hD
  exact h6_not_diam (D := D) (by omega) (by simpa using hd)

end CoordCons
