import Papers.PODC2011.CoordinatedConsensusDynamic.StaticPathDefs

/-!
# Lemma 6.5: from a path to the cycle without being noticed

Closing the path `P_k` into the cycle `C` for `a` rounds and then switching to `P_{k+s}` for `b`
rounds cannot be noticed by the first node `u_{k+s+1}` of `P_{k+s}` within `b` rounds, provided
`a ≤ s` and `a + b + s < n`.

Differences with the paper: the paper names the node `u_{k+s-1}`; the correct node is `u_{k+s+1}`
(for `s ≥ 0`); `u_{k+s-1}` lies in the arc `u_{k-a+1}, …, u_{k+a}` of nodes that may already know
about the missing edge at time `t - b` whenever `s ≤ a + 1` (counterexample
`lemma_6_5_paper_node_false`). For `s < 0` the paper's hypothesis `a + b < n - s` is too weak
(it must be `a + b < n - |s|`): `lemma_6_5_neg_false` gives an instance satisfying all of the
paper's hypotheses in which *every* node distinguishes the two executions. Only `s ≥ 0` is used
(Lemma 6.6), so we state the lemma for `s : ℕ`; the hypotheses `b < t ≤ n - 1` are not needed.
-/

namespace CoordCons

namespace StaticPath

open DGraph

/-- Distance (along `P_k`) from the missing edge `{u_k, u_{k+1}}` of `P_k`. -/
def dcut (n k y : ℕ) : ℕ := min (pos n k y) (n - 1 - pos n k y)

theorem dcut_cyc {n k x y : ℕ} (hn : 3 ≤ n) (h : cyc n x y) : dcut n k y ≤ dcut n k x + 1 := by
  rw [cyc_iff k hn] at h
  have := pos_lt (n := n) (k := k) (x := x) (by omega)
  have := pos_lt (n := n) (k := k) (x := y) (by omega)
  unfold dcut
  omega

/-- A node close to the missing edge of `P_k` is far from the start of `P_{k+s}`. -/
theorem pos_shift_far {n k s a y : ℕ} (hy : y < n) (hd : dcut n k y < a) (has : a ≤ s)
    (han : a + s < n) : n ≤ pos n (k + s) y + s + a := by
  have := pos_lt (n := n) (k := k) (x := y) (by omega)
  rw [pos_add hy (by omega)]
  unfold dcut at hd
  split_ifs <;> omega

/-- **Lemma 6.5** of [KMO11] (for `s ≥ 0`, with the indistinguishing node corrected to
`u_{k+s+1}`, the first node of `P_{k+s}`). `G = exec n σ g` and `G' = exec n σ g'` agree up to
round `t - b - a`; in rounds `(t-b-a, t-b]` `G` is the cycle and `G'` is `P_k`; in rounds
`(t-b, t]` both are `P_{k+s}`. -/
theorem lemma_6_5 {n k s a b t : ℕ} (σ : ℕ → Bool) {g g' : ℕ → ℕ → ℕ → Prop} (hn : 3 ≤ n)
    (hg : IsCP n g) (has : a ≤ s) (hab : a + b + s < n)
    (hpre : ∀ r, 1 ≤ r → r ≤ t - b - a → g r = g' r)
    (hmid : ∀ r, t - b - a < r → r ≤ t - b → g r = cyc n ∧ g' r = path n k)
    (hsuf : ∀ r, t - b < r → r ≤ t → g r = path n (k + s) ∧ g' r = path n (k + s)) :
    Indist (exec n σ g) (exec n σ g') ((k + s + 1) % n) t := by
  have hG := exec_valid σ hn hg
  have hu : (k + s + 1) % n ∈ (exec n σ g).V := Finset.mem_range.2 (Nat.mod_lt _ (by omega))
  refine indist_of_agree hG hu rfl (fun w hw => ⟨(hw.mem_iff hG).2 hu, rfl⟩) ?_
  intro w r' hr x
  have hrt := hr.le
  change g (r' + 1) x w ↔ g' (r' + 1) x w
  by_cases h1 : r' + 1 ≤ t - b - a
  · rw [hpre _ (by omega) h1]
  by_cases h2 : t - b < r' + 1
  · rw [(hsuf _ h2 hrt).1, (hsuf _ h2 hrt).2]
  obtain ⟨e1, e2⟩ := hmid (r' + 1) (by omega) (by omega)
  rw [e1, e2]
  have hw : w < n := by simpa [exec] using (hr.mem_iff hG).2 hu
  have hpw := pos_lt (n := n) (k := k) (x := w) (by omega)
  apply cyc_iff_path hn
  all_goals
    intro hcut
    -- the information about the missing edge cannot reach `u_{k+s+1}` by time `t`
    have key := reach_inv (P := fun τ y => y < n ∧ (τ ≤ t - b → dcut n k y + (r' + 1) ≤ τ) ∧
        (t - b ≤ τ → n + (t - b) ≤ pos n (k + s) y + τ + s + a)) hr ?base ?step
    · have := pos_first (n := n) (k := k + s) (by omega)
      rw [show k + s + 1 = k + s + 1 from rfl, this] at key
      omega
    case base =>
      have hd : dcut n k w = 0 := by unfold dcut; omega
      refine ⟨hw, fun _ => by omega, fun h => ?_⟩
      have := pos_shift_far (k := k) (s := s) hw (a := a) (by omega) has (by omega)
      omega
    case step =>
      intro τ y z hτ hτt ⟨hy, hP1, hP2⟩ hyz
      have hz : z < n := by
        rcases hyz with rfl | hyz
        · exact hy
        · exact (hg.lt hyz).2
      have hP1' : τ + 1 ≤ t - b → dcut n k z + (r' + 1) ≤ τ + 1 := by
        intro hτb
        have : dcut n k z ≤ dcut n k y + 1 := by
          rcases hyz with rfl | hyz
          · omega
          · change g (τ + 1) y z at hyz
            rw [(hmid (τ + 1) (by omega) hτb).1] at hyz
            exact dcut_cyc hn hyz
        have := hP1 (by omega)
        omega
      refine ⟨hz, hP1', fun hτb => ?_⟩
      by_cases hτb' : t - b ≤ τ
      · have : pos n (k + s) y ≤ pos n (k + s) z + 1 := by
          rcases hyz with rfl | hyz
          · omega
          · change g (τ + 1) y z at hyz
            rw [(hsuf (τ + 1) (by omega) (by omega)).1] at hyz
            exact path_pos_le hyz
        have := hP2 hτb'
        omega
      · have := hP1' (by omega)
        have := pos_shift_far (k := k) (s := s) hz (a := a) (by omega) has (by omega)
        omega

/-! ### The paper's statement of Lemma 6.5 is wrong as written -/

section Counterexamples

/-- Round graphs of the counterexample to the paper's node index (`n = 6`, `k = 0`, `s = 2`,
`a = 1`, `b = 2`, `t = 3`): `G` is `C` in round `1` and `P_2` afterwards. -/
def cexG : ℕ → ℕ → ℕ → Prop := fun r => if r ≤ 1 then cyc 6 else path 6 2

/-- `G'` is `P_0` in round `1` and `P_2` afterwards. -/
def cexG' : ℕ → ℕ → ℕ → Prop := fun r => if r ≤ 1 then path 6 0 else path 6 2

theorem isCP_cexG : IsCP 6 cexG := fun r => by
  unfold cexG; split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨2, rfl⟩

theorem isCP_cexG' : IsCP 6 cexG' := fun r => by
  unfold cexG'; split_ifs
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨2, rfl⟩

/-- The paper's Lemma 6.5 names node `u_{k+s-1}`. With `n = 6, k = 0, s = 2, a = 1, b = 2,
t = 3` (all hypotheses of the paper hold: `a ≤ |s|`, `a + b < n - s`, `b < t ≤ n - 1`) node
`u_{k+s-1} = u_1` *does* distinguish the two executions (it is an endpoint of the missing edge),
while the corrected node `u_{k+s+1} = u_3` does not. -/
theorem lemma_6_5_paper_node_false (σ : ℕ → Bool) :
    ¬ Indist (exec 6 σ cexG) (exec 6 σ cexG') 1 3 ∧
      Indist (exec 6 σ cexG) (exec 6 σ cexG') 3 3 := by
  constructor
  · intro h
    have h1 := (h.mono (show 1 ≤ 3 by norm_num)).2.1 0
    have : cexG 1 0 1 ↔ cexG' 1 0 1 := h1
    simp only [cexG, cexG', le_refl, ite_true] at this
    revert this
    unfold cyc path pos
    decide
  · have := lemma_6_5 σ (n := 6) (k := 0) (s := 2) (a := 1) (b := 2) (t := 3) (g := cexG)
      (g' := cexG') (by norm_num) isCP_cexG (by norm_num) (by norm_num)
      (fun r h1 h2 => by omega)
      (fun r h1 h2 => by
        obtain rfl : r = 1 := by omega
        simp [cexG, cexG'])
      (fun r h1 h2 => by
        simp only [cexG, cexG']
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact ⟨rfl, rfl⟩)
    simpa using this

/-- Round graphs of the counterexample for `s < 0` (`n = 6`, `k = 0`, `s = -2`, `a = 2`, `b = 4`,
`t = 5`): `G` is `C` in round `1` and `P_{k+s} = P_4` afterwards. -/
def cexN : ℕ → ℕ → ℕ → Prop := fun r => if r ≤ 1 then cyc 6 else path 6 4

/-- `G'` is `P_0` in round `1` and `P_4` afterwards. -/
def cexN' : ℕ → ℕ → ℕ → Prop := fun r => if r ≤ 1 then path 6 0 else path 6 4

theorem isCP_cexN : IsCP 6 cexN := fun r => by
  unfold cexN; split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨4, rfl⟩

theorem isCP_cexN' : IsCP 6 cexN' := fun r => by
  unfold cexN'; split_ifs
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨4, rfl⟩

/-- For `s < 0` the paper's hypothesis `a + b < n - s` is too weak. With `n = 6, k = 0, s = -2,
a = 2, b = 4, t = 5` all hypotheses of the paper's Lemma 6.5 hold (`a ≤ |s|`, `a + b = 6 < 8 =
n - s`, `b < t ≤ n - 1`; the executions agree on the first `max(0, t-b-a) = 0` rounds, differ as
`C` vs `P_k` in round `1 = t - b`, and are `P_{k+s} = P_4` in rounds `2..5`), yet **every** node
distinguishes `(G, 5)` from `(G', 5)`. (The correct hypothesis is `a + b < n - |s|`.) -/
theorem lemma_6_5_neg_false (σ : ℕ → Bool) :
    ∀ u, ¬ Indist (exec 6 σ cexN) (exec 6 σ cexN') u 5 := by
  intro u h
  have hu : u < 6 := by simpa [exec] using h.mem_left
  have adj : ∀ r x y, 2 ≤ r → path 6 4 x y → (exec 6 σ cexN).adj r x y := fun r x y hr hp => by
    change cexN r x y
    simp only [cexN]; rw [ite_eq_right (by omega)]; exact hp
  have st : ∀ {x y r}, path 6 4 x y → 1 ≤ r →
      (exec 6 σ cexN).Reach 1 1 x r → (exec 6 σ cexN).Reach 1 1 y (r + 1) :=
    fun hp hr h => .step h (Or.inr (adj _ _ _ (by omega) hp))
  have hp : ∀ x y, (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 5) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨
      (x = 3 ∧ y = 4) → path 6 4 x y := by
    intro x y hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (unfold path pos; decide)
  have r0 : (exec 6 σ cexN).Reach 1 1 1 1 := .refl
  have hr : (exec 6 σ cexN).Reach 1 1 u 5 := by
    interval_cases u
    · exact (st (hp 1 0 (by simp)) le_rfl r0).trans (Reach.self (by norm_num))
    · exact Reach.self (by norm_num)
    · exact (st (hp 1 2 (by simp)) le_rfl r0).trans (Reach.self (by norm_num))
    · exact (st (hp 2 3 (by simp)) (by norm_num) (st (hp 1 2 (by simp)) le_rfl r0)).trans
        (Reach.self (by norm_num))
    · exact (st (hp 3 4 (by simp)) (by norm_num) (st (hp 2 3 (by simp)) (by norm_num)
        (st (hp 1 2 (by simp)) le_rfl r0))).trans (Reach.self (by norm_num))
    · exact (st (hp 0 5 (by simp)) (by norm_num) (st (hp 1 0 (by simp)) le_rfl r0)).trans
        (Reach.self (by norm_num))
  have := h.adj_iff (s := 0) hr 0
  change cexN 1 0 1 ↔ cexN' 1 0 1 at this
  simp only [cexN, cexN', le_refl, ite_true] at this
  revert this
  unfold cyc path pos
  decide

end Counterexamples

end StaticPath

end CoordCons
