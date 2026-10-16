import Papers.PODC2011.CoordinatedConsensusDynamic.StaticPathLemma66

/-!
# Theorem 6.7: lower bound for `Δ`-coordinated consensus on the static line

With `T = n - 1 - β`, starting from the static line `P_k` with an arbitrary input assignment we
repeat `⌈n/β⌉` times: flip the inputs of the first `β` nodes of the current path to `v` (one step:
the last node of the path cannot distinguish by time `T`), then rotate the path by `β` with
Lemma 6.6 (the transformed suffix is the whole execution). This joins `(P_k, T)` to an execution
with all inputs `v` by a walk of length `⌈n/β⌉ · 3^(m+1)` (`n ≤ 2^m β`), and Lemma 6.4 yields that
no node decides by time `T - ⌈n/β⌉ · 3^(m+1) · Δ`.

The paper uses `T = n - 2β - 1`; `T = n - β - 1` works as well (the last node of `P_j` is at
distance `n - β` from the flipped nodes, and Lemma 6.6 only needs `T ≤ n - 1 - β`).
-/

namespace CoordCons

namespace StaticPath

open DGraph

/-- Flipping the inputs of the first `β` nodes of `P_j` to `v` is not noticed by the last node
`u_j` of `P_j` by time `n - 1 - β`. -/
theorem flip_indist {n j β : ℕ} (hn : 3 ≤ n) (hβn : β < n) {σ σ' : ℕ → Bool}
    (hσ : ∀ x, x < n → β ≤ pos n j x → σ x = σ' x) :
    Indist (staticLine n j σ) (staticLine n j σ') (j % n) (n - 1 - β) := by
  have hG := (staticLine_knownN j σ hn).1
  have hu : j % n ∈ (staticLine n j σ).V := Finset.mem_range.2 (Nat.mod_lt _ (by omega))
  refine indist_of_agree hG hu rfl (fun w hw => ?_) (fun _ _ _ _ => Iff.rfl)
  have hw' : w < n := by simpa [staticLine, exec] using (hw.mem_iff hG).2 hu
  refine ⟨Finset.mem_range.2 hw', hσ w hw' ?_⟩
  have key := reach_inv (P := fun τ y => y < n ∧ pos n j y ≤ pos n j w + τ) hw
    ⟨hw', by omega⟩ (fun τ x y _ _ ⟨hx, hP⟩ hxy => by
      rcases hxy with rfl | hxy
      · exact ⟨hx, by omega⟩
      · exact ⟨hxy.2.1, by have := path_pos_le' hxy; omega⟩)
  have := pos_last (n := n) (k := j) (by omega)
  rw [this] at key
  omega

/-- The input assignments of the walk: in phase `i` the first `β` nodes of `P_{k+iβ}` get `v`. -/
def flipInputs (n k β : ℕ) (v : Bool) (σ : ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => σ
  | i + 1 => fun x => if pos n (k + i * β) x < β then v else flipInputs n k β v σ i x

theorem flipInputs_eq {n k β : ℕ} {v : Bool} {σ : ℕ → Bool} (hn : 0 < n) :
    ∀ i x, x < n → pos n k x < i * β → flipInputs n k β v σ i x = v := by
  intro i
  induction i with
  | zero => intro x _ h; simp at h
  | succ i ih =>
    intro x hx h
    simp only [flipInputs]
    split_ifs with h'
    · rfl
    · by_cases hi : pos n k x < i * β
      · exact ih x hx hi
      · exfalso
        have := pos_lt (n := n) (k := k) (x := x) hn
        rw [pos_add hx (by omega), ite_eq_left (by omega)] at h'
        rw [add_mul] at h
        omega

/-- The walk of the proof of Theorem 6.7, after `i` phases. -/
theorem phase_walk {n β m k : ℕ} (σ : ℕ → Bool) (v : Bool) (hn : 3 ≤ n) (hβ : 1 ≤ β)
    (hβn : β < n) (hm : n ≤ 2 ^ m * β) :
    ∀ i, Walk (KnownN n) (n - 1 - β) (i * 3 ^ (m + 1)) (staticLine n k σ)
      (staticLine n (k + i * β) (flipInputs n k β v σ i)) := by
  intro i
  induction i with
  | zero => rw [zero_mul, zero_mul, add_zero]; exact Walk.nil _
  | succ i ih =>
    have hf := flip_indist (j := k + i * β) (β := β) hn hβn
      (σ := flipInputs n k β v σ i) (σ' := flipInputs n k β v σ (i + 1))
      (fun x _ hx => by simp only [flipInputs]; rw [ite_eq_right (by omega)])
    have s1 : Walk (KnownN n) (n - 1 - β) 1 _ _ :=
      Walk.single ⟨staticLine_knownN _ _ hn, staticLine_knownN _ _ hn, _, hf⟩
    have w2 := lemma_6_6 (flipInputs n k β v σ (i + 1)) (t := n - 1 - β) (k := k + i * β)
      (k' := k + i * β + β) (g := fun _ => path n (k + i * β))
      (g' := fun _ => path n (k + i * β + β)) hn hβ hβn hm (isCP_const_path _ _)
      (isCP_const_path _ _) (fun r h1 h2 => by omega) (fun r _ _ => ⟨rfl, rfl⟩)
    have w := (ih.append s1).append w2
    rw [show k + i * β + β = k + (i + 1) * β by ring] at w
    refine Walk.cast w ?_
    have := Nat.one_le_pow (m + 1) 3 (by norm_num)
    rw [add_mul]
    omega

theorem le_ceil_div_mul {n β : ℕ} (hβ : 1 ≤ β) : n ≤ (n + β - 1) / β * β := by
  have h2 := Nat.div_add_mod (n + β - 1) β
  have h3 := Nat.mod_lt (n + β - 1) (show 0 < β by omega)
  rw [mul_comm] at h2
  omega

/-- From the static line with any input assignment there is a walk of length
`⌈n/β⌉ · 3^(m+1)` at time `n - 1 - β` to an execution in which all inputs are `v`. -/
theorem walk_to_uniform {n β m k : ℕ} (σ : ℕ → Bool) (v : Bool) (hn : 3 ≤ n) (hβ : 1 ≤ β)
    (hβn : β < n) (hm : n ≤ 2 ^ m * β) :
    ∃ G, Walk (KnownN n) (n - 1 - β) ((n + β - 1) / β * 3 ^ (m + 1)) (staticLine n k σ) G ∧
      ∀ w ∈ G.V, G.input w = v := by
  refine ⟨_, phase_walk (k := k) σ v hn hβ hβn hm ((n + β - 1) / β), fun w hw => ?_⟩
  have hw : w < n := Finset.mem_range.1 hw
  have := pos_lt (n := n) (k := k) (x := w) (by omega)
  have := le_ceil_div_mul (n := n) hβ
  exact flipInputs_eq (by omega) _ w hw (by omega)

/-- **Theorem 6.7** of [KMO11] (explicit, non-asymptotic form). In the system where `n` is known,
for every `Δ`-coordinated consensus algorithm (given as a view-based decision rule `D`), every
input assignment `σ`, every static line `P_k` and every `1 ≤ β < n` and `m` with `n ≤ 2^m β`: no
node has decided by any time `t` with `t + ⌈n/β⌉ · 3^(m+1) · Δ ≤ n - 1 - β`. -/
theorem theorem_6_7 {n β m Δ : ℕ} {D : Decision Bool} (hD : Consensus (KnownN n) D)
    (hC : Coordinated (KnownN n) Δ D) (hn : 3 ≤ n) (hβ : 1 ≤ β) (hβn : β < n)
    (hm : n ≤ 2 ^ m * β) (k : ℕ) (σ : ℕ → Bool) {t : ℕ}
    (ht : t + (n + β - 1) / β * 3 ^ (m + 1) * Δ ≤ n - 1 - β) :
    ∀ u ∈ (staticLine n k σ).V, D (staticLine n k σ) u t = none := by
  obtain ⟨G₀, w₀, h₀⟩ := walk_to_uniform (k := k) σ false hn hβ hβn hm
  obtain ⟨G₁, w₁, h₁⟩ := walk_to_uniform (k := k) σ true hn hβ hβn hm
  exact lemma_6_4 hD hC (staticLine_knownN k σ hn) w₀ w₁ ht ht h₀ h₁

/-- Theorem 6.7 with the paper's `ℓ_β = ⌈log₂(n/β)⌉`. -/
theorem theorem_6_7_clog {n β Δ : ℕ} {D : Decision Bool} (hD : Consensus (KnownN n) D)
    (hC : Coordinated (KnownN n) Δ D) (hn : 3 ≤ n) (hβ : 1 ≤ β) (hβn : β < n)
    (k : ℕ) (σ : ℕ → Bool) {t : ℕ}
    (ht : t + (n + β - 1) / β * 3 ^ (ellBeta n β + 1) * Δ ≤ n - 1 - β) :
    ∀ u ∈ (staticLine n k σ).V, D (staticLine n k σ) u t = none :=
  theorem_6_7 hD hC hn hβ hβn (le_two_pow_ellBeta hβ) k σ ht

end StaticPath

end CoordCons
