import Papers.PODC2020.LongLivedSnapshotsPolylog.WaitFreeIter
import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# Wait-freedom of Algorithm 1 (Lemmas 3.4 and 3.5)

Baïg, Hendler, Milani, Travers, *Long-Lived Snapshots with Polylogarithmic Amortized Step
Complexity* (PODC 2020), Section 3.2.

* `lemma_3_4`: along a segment of an `ℓ`-bounded-increment execution in which the high-order bits
  `Q = ⌊MR_left/m⌋ + ⌊MR_right/m⌋` grow by `K` (which is what `K` unsuccessful iterations of a
  `CompScan` guarantee, see `MainInv`), at least `((K - 2)m + 2)/ℓ` `WriteMax` steps occur.
* `iterations_le` (Lemma 3.5): every `CompScan` performs at most `2X + K` loop iterations,
  where `2nℓ < (K - 2)m`.
* `steps_le`: every operation performs at most `(2X + K)(n + 9) + 1` base-object accesses.
* `waitFreeOn_BIExec`: Algorithm 1 is wait-free on the `ℓ`-bounded-increment executions.
-/

namespace Podc.LongLivedSnapshotsPolylog.WaitFree

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

variable {n m X : ℕ}

lemma mul_Q_le_V (C : Cfg n) : m * Q m C ≤ V C := by
  simp only [Q_def, V, Nat.mul_add]
  exact Nat.add_le_add (Nat.mul_div_le _ _) (Nat.mul_div_le _ _)

lemma V_le_mul_Q (hm : 0 < m) (C : Cfg n) : V C + 2 ≤ m * Q m C + 2 * m := by
  simp only [Q_def, V, Nat.mul_add]
  have h1 := Nat.div_add_mod (mrL C) m
  have h2 := Nat.div_add_mod (mrR C) m
  have h3 := Nat.mod_lt (mrL C) hm
  have h4 := Nat.mod_lt (mrR C) hm
  omega

/-- **Lemma 3.4** (counting part). Along a segment `γ`, from `C₀` to `C₁`, of an
`ℓ`-bounded-increment execution `α`, if the high-order bits `Q` grow by `K ≥ 2` then at least
`((K - 2) m + 2) / ℓ` `WriteMax` steps (i.e. `MaxUpdate`s) occur in the segment. -/
theorem lemma_3_4 {ℓ K : ℕ} (hm : 0 < m) (hK : 2 ≤ K) {α : List (Lbl n)} {Cα : Cfg n}
    (hα : (alg1 n m X).run α = some Cα) (hBI : BIExec n m X ℓ α)
    {β₀ γ : List (Lbl n)} {C₀ C₁ : Cfg n} (hp : β₀ ++ γ <+: α)
    (h₀ : (alg1 n m X).run β₀ = some C₀) (h₁ : (alg1 n m X).runFrom C₀ γ = some C₁)
    (hQ : Q m C₀ + K ≤ Q m C₁) :
    (K - 2) * m + 2 ≤ ℓ * (wr m X C₀ γ).length := by
  have hV := V_le_of_seg hα hBI γ β₀ C₀ C₁ hp h₀ h₁
  have e1 := mul_Q_le_V (m := m) C₁
  have e2 := V_le_mul_Q hm C₀
  have e3 : m * (Q m C₀ + K) ≤ m * Q m C₁ := Nat.mul_le_mul_left _ hQ
  rw [Nat.mul_add] at e3
  have e4 : (K - 2) * m + 2 * m = m * K := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hK, Nat.mul_comm]
  omega

/-- **Core of Lemma 3.5.** If `2nℓ < (K - 2) m` and `Q` grows by `K` along a segment (from
`C₀` to `C₁`) of an `ℓ`-bounded-increment execution, then some `H[k].ts` grows by at least `2`
along the segment: by Lemma 3.4 at least `2n + 1` `WriteMax` steps occur, so some process performs
three of them, and Observation 5 applies to the two `CompScan`s in between. -/
theorem good_of_Q {ℓ K : ℕ} (hK : 2 * n * ℓ < (K - 2) * m) {α : List (Lbl n)} {Cα : Cfg n}
    (hα : (alg1 n m X).run α = some Cα) (hBI : BIExec n m X ℓ α)
    {β₀ β₁ : List (Lbl n)} {C₀ C₁ : Cfg n} (hp : β₀ <+: β₁) (hp' : β₁ <+: α)
    (h₀ : (alg1 n m X).run β₀ = some C₀) (h₁ : (alg1 n m X).run β₁ = some C₁)
    (hQ : Q m C₀ + K ≤ Q m C₁) : Good C₀ C₁ := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hK
    · exact h
  have hK2 : 2 ≤ K := by
    by_contra h
    have : K - 2 = 0 := by omega
    rw [this, Nat.zero_mul] at hK; omega
  obtain ⟨γ, rfl⟩ := hp
  have h₁' : (alg1 n m X).runFrom C₀ γ = some C₁ := by
    rw [Impl.run, Impl.runFrom_append] at h₁
    rw [Impl.run] at h₀
    rwa [h₀, Option.bind_some] at h₁
  have h34 := lemma_3_4 hm hK2 hα hBI hp' h₀ h₁' hQ
  have hW : 2 * n + 1 ≤ (wr m X C₀ γ).length := by
    by_contra h
    have : ℓ * (wr m X C₀ γ).length ≤ ℓ * (2 * n) := Nat.mul_le_mul_left _ (by omega)
    have e : ℓ * (2 * n) = 2 * n * ℓ := Nat.mul_comm _ _
    omega
  obtain ⟨j, hj⟩ := exists_three hW
  exact good_of_three_writes h₀ h₁' hj

/-! ### The number of iterations -/

/-- The iteration counter `c` of the current `CompScan` (`0` outside `CompScan`): the
`CompScan` is in its `(c + 1)`-st loop iteration. -/
def iterCount : PC n → ℕ
  | .rdR1 cs => cs.c
  | .rdL cs _ => cs.c
  | .rdR2 cs _ _ => cs.c
  | .upL cs _ _ => cs.c
  | .upR cs _ _ => cs.c
  | .scanMA cs _ _ => cs.c
  | .chkL cs _ _ _ => cs.c
  | .chkR cs _ _ _ => cs.c
  | .wH cs _ => cs.c
  | .col cs _ _ _ => cs.c
  | _ => 0

/-- The counter is at most `X + K`, or no multiple of `X` lies in `[X + K, c)` (so a second
collect, which returns, happened at the first multiple of `X` that is `≥ X + K`). -/
def CBound (X K c : ℕ) : Prop := c ≤ X + K ∨ ∀ j, X + K ≤ j → j < c → j % X ≠ 0

lemma cbound_le (hX : 0 < X) (hK : 1 ≤ K) {c : ℕ} (h : CBound X K c) : c + 1 ≤ 2 * X + K := by
  rcases h with h | h
  · omega
  · by_contra hc
    have h1 := Nat.div_mul_le_self (X + K - 1) X
    have h2 := Nat.lt_div_mul_add (a := X + K - 1) hX
    generalize (X + K - 1) / X = q at h1 h2
    have h3 : X + K - 1 + 1 = X + K := by omega
    have := h (q * X + X) (by omega) (by omega)
    exact this (by rw [← Nat.succ_mul, Nat.mul_mod_left])

lemma cbound_afterFail (hK : 1 ≤ K) {i : Fin n} {cs : CS n} (h : CBound X K cs.c) :
    CBound X K (iterCount (afterFail X i cs)) := by
  unfold afterFail
  split_ifs with h1 h2
  · exact h
  · exact h
  · simp only [iterCount]
    rcases Nat.lt_or_ge cs.c (X + K) with h3 | h3
    · left; omega
    · right
      intro j hj1 hj2
      have hXc : X < cs.c := by omega
      rcases Nat.lt_or_ge j cs.c with h4 | h4
      · rcases h with h | h
        · omega
        · exact h j hj1 h4
      · have : j = cs.c := by omega
        subst this; exact fun h' => h2 ⟨hXc, h'⟩

lemma findHelp_ne_none {h0 h1 : Fin n → HEntry} {k : Fin n} (h : (h0 k).1 + 1 < (h1 k).1) :
    findHelp h0 h1 ≠ none := by
  simp only [findHelp, ne_eq, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq,
    not_forall, not_not]
  exact ⟨k, List.mem_finRange k, h⟩

lemma cbound_tau {K : ℕ} (hK1 : 1 ≤ K) {β : List (Lbl n)} {C C' : Cfg n} {i : Fin n}
    (hB : Basic C) (hβ : (alg1 n m X).run β = some C)
    (hs : (alg1 n m X).step C (.tau i) = some C') (hP : PInv m X β C (C.loc i).pc)
    (h : CBound X K (iterCount (C.loc i).pc))
    (hgood : ∀ β₀ β₁ C₀ C₁, β₀ <+: β₁ → β₁ <+: β → (alg1 n m X).run β₀ = some C₀ →
      (alg1 n m X).run β₁ = some C₁ → Q m C₀ + K ≤ Q m C₁ → Good C₀ C₁) :
    CBound X K (iterCount (C'.loc i).pc) := by
  rcases hpc : (C.loc i).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
    ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
    ⟨cs, first, k, acc⟩ | r
  all_goals rw [hpc] at h hP
  all_goals simp [Impl.step, act, hpc] at hs
  all_goals obtain ⟨-, rfl⟩ := hs
  all_goals simp only [Function.update_self]
  all_goals simp only [iterCount] at h
  · left; simp [iterCount, csInit]
  · left; simp [iterCount, csInit]
  · simpa [iterCount] using h
  · simpa [iterCount] using h
  · split_ifs
    · simpa [iterCount] using h
    · exact cbound_afterFail hK1 h
  · simpa [iterCount] using h
  · simpa [iterCount] using h
  · simpa [iterCount] using h
  · split_ifs
    · simpa [iterCount] using h
    · exact cbound_afterFail hK1 h
  · split_ifs
    · simpa [iterCount] using h
    · exact cbound_afterFail hK1 h
  · unfold retOf; split_ifs <;> left <;> simp [iterCount]
  · by_cases hk : k.1 + 1 < n
    · simpa [hk, iterCount] using h
    · simp only [hk, ↓reduceDIte]
      cases first
      · simp only [afterCollect, Bool.false_eq_true, ↓reduceIte]
        split
        · unfold retOf; split_ifs <;> left <;> simp [iterCount]
        · rename_i hnone
          simp only [iterCount]
          left
          by_contra hc
          simp only [PInv] at hP
          obtain ⟨-, h0, hh0, β₀, C₀, β₁, C₁, hp, hp', r0, r1, hts, hQ, hacc⟩ := hP
          obtain ⟨k0, hk0⟩ := hgood β₀ β₁ C₀ C₁ hp hp' r0 r1 (by omega)
          have hm1 := (run_mono_of_prefix hp' r1 hβ).2.2
          have e2 : tsOf C₁ k0 ≤ (Function.update acc k (C.mem (Obj.help k)) k0).1 := by
            by_cases hk0' : k0 = k
            · subst hk0'; rw [Function.update_self, hB.1 k0]; exact hm1 k0
            · rw [Function.update_of_ne hk0']
              refine hacc k0 ?_
              rcases lt_or_gt_of_ne hk0' with h' | h'
              · exact h'
              · exfalso; simp only [Fin.lt_def] at h'; omega
          have := hts k0
          rw [hh0, Option.bind_some] at hnone
          exact findHelp_ne_none (k := k0) (by omega) hnone
      · simp only [PInv] at hP
        simp only [afterCollect, ↓reduceIte, iterCount]
        left; omega

/-- **Lemma 3.5, iteration bound** (invariant form): in every prefix of an `ℓ`-bounded-increment
execution with `2nℓ < (K - 2)m`, every iteration counter satisfies `CBound`. -/
theorem cbound_run {ℓ K : ℕ} (hK : 2 * n * ℓ < (K - 2) * m) {α : List (Lbl n)} {Cα : Cfg n}
    (hα : (alg1 n m X).run α = some Cα) (hBI : BIExec n m X ℓ α) {β : List (Lbl n)}
    {C : Cfg n} (hp : β <+: α) (hβ : (alg1 n m X).run β = some C) (i : Fin n) :
    CBound X K (iterCount (C.loc i).pc) := by
  have hK1 : 1 ≤ K := by
    by_contra h
    have : K - 2 = 0 := by omega
    rw [this, Nat.zero_mul] at hK; omega
  refine Impl.run_induction (I := alg1 n m X)
    (Q := fun β C => β <+: α → ∀ i, CBound X K (iterCount (C.loc i).pc))
    (fun _ i => Or.inl (by simp [Impl.initCfg, iterCount])) (fun β C x C' hβ ih hs hp i => ?_)
    hβ hp i
  have hpβ : β <+: α := (List.prefix_append _ _).trans hp
  have ih := ih hpβ
  by_cases hx : x.proc = i
  · cases x with
    | tau p =>
      simp only [Label.proc] at hx; subst hx
      exact cbound_tau hK1 (basic_run hβ) hβ hs (mainInv_run hβ p) (ih p)
        (fun β₀ β₁ C₀ C₁ h1 h2 r0 r1 hQ => good_of_Q hK hα hBI h1 (h2.trans hpβ) r0 r1 hQ)
    | inv p o =>
      simp only [Label.proc] at hx; subst hx
      obtain ⟨-, -, -, hl, -⟩ := Impl.step_inv hs
      rw [hl, Function.update_self]
      left; cases o <;> simp [iterCount, csInit]
    | ret p r =>
      simp only [Label.proc] at hx; subst hx
      obtain ⟨-, -, -, l, hact, hl⟩ := Impl.step_ret hs
      rw [hl, Function.update_self, act_ret_idle hact]
      left; simp [iterCount]
  · rw [(Impl.step_other hs hx).1]
    exact ih i

/-- **Lemma 3.5** (iterations). Let `X ≥ 1` be the helping period and `K` such that
`2nℓ < (K - 2)m` (the paper: `⌈(K - 2)m/ℓ⌉ ≥ 2n + 1`). In every `ℓ`-bounded-increment execution
(for both `MR_left` and `MR_right`), every `CompScan` instance performs at most `2X + K` loop
iterations (the paper: `K + 2⌈n/log² m⌉`): the iteration counter `c` of every process satisfies
`c + 1 ≤ 2X + K`. -/
theorem iterations_le {ℓ K : ℕ} (hX : 0 < X) (hK : 2 * n * ℓ < (K - 2) * m)
    {α : List (Lbl n)} {C : Cfg n} (hα : (alg1 n m X).run α = some C)
    (hBI : BIExec n m X ℓ α) (i : Fin n) : iterCount (C.loc i).pc + 1 ≤ 2 * X + K := by
  have hK1 : 1 ≤ K := by
    by_contra h
    have : K - 2 = 0 := by omega
    rw [this, Nat.zero_mul] at hK; omega
  exact cbound_le hX hK1 (cbound_run hK hα hBI (List.prefix_refl _) hα i)

/-! ### Step complexity and wait-freedom -/

/-- A bound on the number of remaining base-object accesses of the current operation, when the
iteration counter never exceeds `N`: each iteration takes at most `n + 9` accesses (8 accesses
of lines 10–18 plus either the write of line 21 or a collect of `n` reads). -/
def mu (n N : ℕ) : PC n → ℕ
  | .idle => 0
  | .retV _ => 0
  | .wm _ _ => (N + 1) * (n + 9) + 1
  | .rdR1 cs => (N - cs.c) * (n + 9) + n + 8
  | .rdL cs _ => (N - cs.c) * (n + 9) + n + 7
  | .rdR2 cs _ _ => (N - cs.c) * (n + 9) + n + 6
  | .upL cs _ _ => (N - cs.c) * (n + 9) + n + 5
  | .upR cs _ _ => (N - cs.c) * (n + 9) + n + 4
  | .scanMA cs _ _ => (N - cs.c) * (n + 9) + n + 3
  | .chkL cs _ _ _ => (N - cs.c) * (n + 9) + n + 2
  | .chkR cs _ _ _ => (N - cs.c) * (n + 9) + n + 1
  | .wH _ _ => 1
  | .col cs _ k _ => (N - cs.c) * (n + 9) + (n - k.1)

lemma mu_next {N c : ℕ} (h : c + 1 ≤ N) :
    (N - (c + 1)) * (n + 9) + n + 8 < (N - c) * (n + 9) + 1 := by
  have : (N - c) * (n + 9) = (N - (c + 1)) * (n + 9) + (n + 9) := by
    rw [show N - c = N - (c + 1) + 1 by omega, Nat.succ_mul]
  omega

lemma mu_afterFail {N : ℕ} {i : Fin n} {cs : CS n}
    (h : iterCount (afterFail X i cs) ≤ N) :
    mu n N (afterFail X i cs) < (N - cs.c) * (n + 9) + n + 1 := by
  unfold afterFail at h ⊢
  split_ifs at h ⊢ <;> simp only [mu, iterCount] at h ⊢
  · omega
  · omega
  · have := mu_next (n := n) h; omega

/-- The potential decreases at every access of a process whose counter stays `≤ N`. -/
lemma mu_tau {N : ℕ} {C C' : Cfg n} {i : Fin n} (hs : (alg1 n m X).step C (.tau i) = some C')
    (h' : iterCount (C'.loc i).pc ≤ N) :
    mu n N (C'.loc i).pc < mu n N (C.loc i).pc := by
  have hn : 0 < n := i.pos
  rcases hpc : (C.loc i).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
    ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
    ⟨cs, first, k, acc⟩ | r
  all_goals simp [Impl.step, act, hpc] at hs
  all_goals obtain ⟨-, rfl⟩ := hs
  all_goals simp only [Function.update_self] at h' ⊢
  · simp only [mu, csInit, Nat.sub_zero, Nat.add_mul, Nat.one_mul]; omega
  · simp only [mu, csInit, Nat.sub_zero, Nat.add_mul, Nat.one_mul]; omega
  · simp only [mu]; omega
  · simp only [mu]; omega
  · split_ifs at h' ⊢
    · simp only [mu]; omega
    · exact lt_of_lt_of_le (mu_afterFail h') (by simp only [mu]; omega)
  · simp only [mu]; omega
  · simp only [mu]; omega
  · simp only [mu]; omega
  · split_ifs at h' ⊢
    · simp only [mu]; omega
    · exact lt_of_lt_of_le (mu_afterFail h') (by simp only [mu]; omega)
  · split_ifs at h' ⊢
    · simp only [mu]; omega
    · exact lt_of_lt_of_le (mu_afterFail h') (by simp only [mu]; omega)
  · unfold retOf; split_ifs <;> simp [mu]
  · have hk := k.2
    by_cases hk' : k.1 + 1 < n
    · simp only [hk', ↓reduceDIte, mu]; omega
    · simp only [hk', ↓reduceDIte] at h' ⊢
      cases first
      · simp only [afterCollect, Bool.false_eq_true, ↓reduceIte] at h' ⊢
        rcases hc : cs.h0.bind (fun h0 => findHelp h0 (Function.update acc k (C.mem (Obj.help k))))
          with _ | v
        · simp only [hc, mu, iterCount] at h' ⊢
          have := mu_next (n := n) h'; omega
        · unfold retOf; split_ifs <;> simp [mu] <;> omega
      · simp only [afterCollect, ↓reduceIte, mu, iterCount] at h' ⊢
        have := mu_next (n := n) h'; omega

lemma iterCount_le_of_prefix {ℓ K : ℕ} (hX : 0 < X) (hK : 2 * n * ℓ < (K - 2) * m)
    {α β : List (Lbl n)} {Cα C : Cfg n} (hα : (alg1 n m X).run α = some Cα)
    (hBI : BIExec n m X ℓ α) (hp : β <+: α) (hβ : (alg1 n m X).run β = some C) (i : Fin n) :
    iterCount (C.loc i).pc ≤ 2 * X + K - 1 := by
  have hK1 : 1 ≤ K := by
    by_contra h
    have : K - 2 = 0 := by omega
    rw [this, Nat.zero_mul] at hK; omega
  have := cbound_le hX hK1 (cbound_run hK hα hBI hp hβ i)
  omega

/-- The potential `mu` does not increase while `p` is pending, and decreases at its accesses. -/
lemma mu_step {ℓ K : ℕ} (hX : 0 < X) (hK : 2 * n * ℓ < (K - 2) * m)
    {α β : List (Lbl n)} {Cα C C' : Cfg n} {x : Lbl n} (hα : (alg1 n m X).run α = some Cα)
    (hBI : BIExec n m X ℓ α) (hp : β ++ [x] <+: α) (hβ : (alg1 n m X).run β = some C)
    (hs : (alg1 n m X).step C x = some C') {p : Fin n} (hpe : C.pend p ≠ none)
    (hpe' : C'.pend p ≠ none) :
    mu n (2 * X + K - 1) (C'.loc p).pc ≤ mu n (2 * X + K - 1) (C.loc p).pc ∧
      (x = .tau p → mu n (2 * X + K - 1) (C'.loc p).pc < mu n (2 * X + K - 1) (C.loc p).pc) := by
  rcases (alg1 n m X).step_tau_or_other hs hpe hpe' with rfl | ⟨hq, hloc⟩
  · have hβ' : (alg1 n m X).run (β ++ [.tau p]) = some C' := by
      rw [Impl.run_concat, hβ, Option.bind_some, hs]
    have := mu_tau hs (iterCount_le_of_prefix hX hK hα hBI hp hβ' p)
    exact ⟨this.le, fun _ => this⟩
  · rw [hloc]
    exact ⟨le_rfl, fun h => absurd (by rw [h]; rfl) hq⟩

/-- **Lemma 3.5** (wait-freedom). For a helping period `X ≥ 1` and `K` with `2nℓ < (K - 2)m`,
Algorithm 1 is wait-free on the `ℓ`-bounded-increment executions: in every infinite execution all
of whose prefixes are `ℓ`-bounded-increment for `MR_left` and `MR_right`, a process with a pending
operation takes only finitely many steps. -/
theorem waitFreeOn_BIExec {ℓ K : ℕ} (hX : 0 < X) (hK : 2 * n * ℓ < (K - 2) * m) :
    (alg1 n m X).WaitFreeOn (BIExec n m X ℓ) :=
  (alg1 n m X).waitFreeOn_of_runPotential (fun p _ C => mu n (2 * X + K - 1) (C.loc p).pc)
    fun _p α _C x C' hα hE hs hpe hpe' => by
      have hα' : (alg1 n m X).run (α ++ [x]) = some C' := by
        rw [Impl.run_concat, hα, Option.bind_some, hs]
      exact mu_step hX hK hα' hE (List.prefix_refl _) hα hs hpe hpe'

/-- **Step complexity of Algorithm 1** (consequence of Lemma 3.5). For `X ≥ 1` and
`2nℓ < (K - 2)m`, in every `ℓ`-bounded-increment execution `α ++ inv p o :: γ` in which the
operation `o` of `p` has not returned during `γ`, `p` performed at most `(2X + K)(n + 9) + 1`
base-object accesses in `γ`. -/
theorem steps_le {ℓ K : ℕ} (hX : 0 < X) (hK : 2 * n * ℓ < (K - 2) * m)
    {α γ : List (Lbl n)} {p : Fin n} {o : MAOp} {C : Cfg n}
    (hrun : (alg1 n m X).run (α ++ .inv p o :: γ) = some C)
    (hBI : BIExec n m X ℓ (α ++ .inv p o :: γ)) (hret : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ (2 * X + K) * (n + 9) + 1 := by
  have hrun' := hrun
  rw [Impl.run, Impl.runFrom_append] at hrun'
  cases h₀ : (alg1 n m X).runFrom (alg1 n m X).initCfg α with
  | none => simp [h₀] at hrun'
  | some C₀ =>
    simp only [h₀, Option.bind_some, Impl.runFrom_cons] at hrun'
    cases h₁ : (alg1 n m X).step C₀ (.inv p o) with
    | none => simp [h₁] at hrun'
    | some C₁ =>
      simp only [h₁, Option.bind_some] at hrun'
      obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv h₁
      have hr₁ : (alg1 n m X).run (α ++ [.inv p o]) = some C₁ := by
        rw [Impl.run_concat, Impl.run, h₀, Option.bind_some, h₁]
      have key := (alg1 n m X).countP_isTauOf_add_le_of_cfgPotential p
        (fun C => mu n (2 * X + K - 1) (C.loc p).pc) γ C₁ C hrun' (by simp [hpend]) hret
        (fun β x D D' hβx hD hs hpD hpD' => by
          have hD' : (alg1 n m X).run (α ++ [.inv p o] ++ β) = some D := by
            rw [Impl.run, Impl.runFrom_append]; rw [Impl.run] at hr₁; rw [hr₁, Option.bind_some, hD]
          refine mu_step hX hK hrun hBI ?_ hD' hs hpD hpD'
          obtain ⟨δ, hδ⟩ := hβx
          exact ⟨δ, by rw [← hδ]; simp⟩)
      have hinv : mu n (2 * X + K - 1) (C₁.loc p).pc ≤ (2 * X + K) * (n + 9) + 1 := by
        rw [hloc, Function.update_self]
        have e : 2 * X + K - 1 + 1 = 2 * X + K := by
          have hK1 : 1 ≤ K := by
            by_contra h
            have : K - 2 = 0 := by omega
            rw [this, Nat.zero_mul] at hK; omega
          omega
        have e2 : (2 * X + K - 1) * (n + 9) + (n + 9) = (2 * X + K) * (n + 9) := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, e]
        cases o <;> simp only [mu, csInit, Nat.sub_zero, e] <;> omega
      omega

end Podc.LongLivedSnapshotsPolylog.WaitFree
