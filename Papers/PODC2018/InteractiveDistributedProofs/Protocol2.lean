import Papers.PODC2018.InteractiveDistributedProofs.Protocol1

/-!
# Protocol 2: the `O(n log n)`-bit dAM protocol for `Sym` (Section 3.2)

Every node first sends a hash index `i_v ∈ ZMod p`; then the prover sends every node

* broadcast part `(ρ, i, r) ∈ Perm V × ZMod p × V` (the whole permutation, the root's index, the
  root), compared with all neighbours, and
* unicast part `(t_v, d_v, a_v, b_v) ∈ V × Fin n × ZMod p × ZMod p`.

The verification is the one of Protocol 1 with `ρ_u := ρ(u)`: once the copies of `ρ` agree on the
neighbourhood (`verify2`), `{ρ_u(u) | u ∈ N(v)} = ρ(N(v))`, which is the paper's line 3. We formalize the
repaired line 2 (`excl = true`, root excluded from `C(v)`); the literal line 2 has the same defect as in
Protocol 1 (`K_n` is rejected).

## The gap in the soundness proof and its repair

The paper fixes a root `r₀` and union-bounds over the `n^n` maps `σ : V → V`, getting a failure
probability `< 1/3` for that root. But in a dAM protocol the prover names the root (and the index
`i = i_r` it must echo) *after* seeing all challenges, so it may pick any of the `n` nodes whose index
happens to be bad; the union bound must also run over `r`, which costs a factor `n` and breaks the
paper's arithmetic. The statement survives: `ρ` is broadcast as a permutation, so the union bound runs
over `n · n!` pairs `(r, σ)` with `σ r ≠ r`, and `2 · n · n! · (n² - 1)/p < 1/3` for
`p ≥ 10 n^{n+2}` because `n! ≤ n^{n-1}` (`soundness`, `theorem_3_5`).

## Main results

* `theorem_3_5`: Protocol 2 decides `Sym` on connected graphs for every prime `p ≥ 10 n^{n+2}`.
* `theorem_1_3`: `Sym ∈ dAM[O(n log n)]`.
-/

open Finset Cslib.Probability

namespace Podc.InteractiveDistributedProofs.Protocol2

open Protocol1

variable {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}

/-- Broadcast part `(ρ, i, r)`. -/
abbrev Bc (V : Type*) (p : ℕ) := Equiv.Perm V × ZMod p × V
/-- Unicast part `(t_v, d_v, a_v, b_v)`. -/
abbrev Uc (V : Type*) [Fintype V] (p : ℕ) := V × Fin (Fintype.card V) × ZMod p × ZMod p
/-- The prover's response to a node. -/
abbrev Resp (V : Type*) [Fintype V] (p : ℕ) := Bc V p × Uc V p

/-- The permutation copy received by a node. -/
def perm (y : ZMod p × Resp V p) : Equiv.Perm V := y.2.1.1

/-- Translate what node `u` received into the message format of Protocol 1 (`ρ_u := ρ(u)`). -/
def toMsg (y : ZMod p × Resp V p) (u : V) : Msg V p :=
  ((y.2.1.2.2, y.2.1.1 u, y.2.2.1, y.2.2.2.1), y.1, (y.2.1.2.1, y.2.2.2.2.1, y.2.2.2.2.2))

/-- The verification of Protocol 2 at `v`: the copies of `ρ` agree on `N(v)`, and the checks of
Protocol 1 (lines 1–4 with `ρ_u = ρ(u)`) pass. -/
def verify2 (excl : Bool) (v : V) (nb : Finset V) (x : V → ZMod p × Resp V p) : Prop :=
  (∀ u ∈ nb, perm (x u) = perm (x v)) ∧ verify excl v nb fun u => toMsg (x u) u

theorem verify2_congr (excl : Bool) (v : V) (nb : Finset V) (hv : v ∈ nb)
    (x y : V → ZMod p × Resp V p) (hxy : ∀ u ∈ nb, x u = y u) :
    verify2 excl v nb x ↔ verify2 excl v nb y := by
  unfold verify2
  rw [verify_congr excl v nb hv (fun u => toMsg (x u) u) (fun u => toMsg (y u) u)
    fun u hu => by simp only [hxy u hu]]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun u hu => by rw [← hxy u hu, ← hxy v hv]; exact h1 u hu, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun u hu => by rw [hxy u hu, hxy v hv]; exact h1 u hu, h2⟩

variable [Nonempty V]

/-- A default value (never read). -/
noncomputable def dflt2 : ZMod p × Resp V p :=
  (0, (1, 0, Classical.arbitrary V), (Classical.arbitrary V, ⟨0, Fintype.card_pos⟩, 0, 0))

/-- **Protocol 2**. -/
noncomputable def protocol (p : ℕ) (excl : Bool) : AMProtocol V (ZMod p) (Resp V p) where
  out v w := verify2 excl v (viewNbhd w) fun u => (w u).getD dflt2

theorem out_mask (excl : Bool) (G : SimpleGraph V) (v : V) (x : V → ZMod p × Resp V p) :
    (protocol p excl).out v (mask G v x) ↔ verify2 excl v (cnbhd G v) x := by
  show verify2 excl v (viewNbhd (mask G v x)) _ ↔ _
  rw [viewNbhd_mask]
  exact verify2_congr excl v _ (self_mem_cnbhd v) _ _ fun u hu => by
    rw [mask_apply_of_mem x hu]; rfl

/-! ### Soundness -/

/-- The bad event for a root `r` and a permutation `σ`, as a function of the root's index `s`. -/
def Bad (G : SimpleGraph V) (r : V) (σ : Equiv.Perm V) (s : ZMod p) : Prop :=
  σ r ≠ r ∧ (polyHash s (adjSum (ZMod p) G) = polyHash s (permSum (ZMod p) G σ) ∨
    polyHash s (adjSum (ZMod p) G) = polyHash s (0 : V × V → ZMod p))

/-- Acceptance implies that some root's index is bad for some permutation. -/
theorem accept_imp_bad {excl : Bool} {G : SimpleGraph V} (hG : G.Connected)
    {P : (V → ZMod p) → V → Resp V p} {c : V → ZMod p}
    (hacc : (protocol p excl).Accepts G P c) :
    ∃ rσ ∈ (univ : Finset (V × Equiv.Perm V)), Bad G rσ.1 rσ.2 (c rσ.1) := by
  set x : V → ZMod p × Resp V p := fun u => (c u, P c u)
  have hv : ∀ v, verify2 excl v (cnbhd G v) x := fun v => (out_mask excl G v x).1 (hacc v)
  have hperm : ∀ u v, perm (x u) = perm (x v) :=
    eq_of_connected hG _ fun u v huv => ((hv u).1 v (mem_cnbhd.2 (Or.inr huv))).symm
  set x' : V → Msg V p := fun u => toMsg (x u) u
  obtain ⟨hρ, hcol⟩ := collision_of_verify hG (x := x') fun v => (hv v).2
  set r := xroot x'
  set σ := perm (x (Classical.arbitrary V))
  have hrho : (fun u => rho (x' u)) = ⇑σ := by
    funext u
    show perm (x u) u = σ u
    rw [hperm u]
  refine ⟨(r, σ), mem_univ _, ?_, ?_⟩
  · have : rho (x' r) = σ r := congrFun hrho r
    rw [← this]; exact hρ
  · rw [← hrho]
    exact hcol

open Classical in
theorem card_bad_le [Fact p.Prime] {G : SimpleGraph V} (hS : ¬ Sym G) (r : V)
    (σ : Equiv.Perm V) :
    #(univ.filter (Bad (p := p) G r σ)) ≤ 2 * (Fintype.card V ^ 2 - 1) := by
  classical
  by_cases hσ : σ r = r
  · have : univ.filter (Bad (p := p) G r σ) = ∅ := by
      ext s; simp [Bad, hσ]
    rw [this]; simp
  · have hne : (⇑σ : V → V) ≠ id := fun h => hσ (by rw [h]; rfl)
    have hAB : adjSum (ZMod p) G ≠ permSum (ZMod p) G σ := adjSum_ne_permSum hS hne
    have hA0 : adjSum (ZMod p) G ≠ 0 := adjSum_ne_zero
    have h1 := card_collision_le (p := p) hAB
    have h2 := card_collision_le (p := p) hA0
    rw [Fintype.card_prod, ← sq] at h1 h2
    have hsplit : univ.filter (Bad (p := p) G r σ) ⊆
        (univ.filter fun s : ZMod p =>
          polyHash s (adjSum (ZMod p) G) = polyHash s (permSum (ZMod p) G σ)) ∪
        (univ.filter fun s : ZMod p =>
          polyHash s (adjSum (ZMod p) G) = polyHash s (0 : V × V → ZMod p)) := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bad] at hs
      rcases hs.2 with h | h <;> simp [h]
    have := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    omega

/-- `n! ≤ n^(n-1)`. -/
theorem factorial_le_pow_pred (n : ℕ) : n.factorial ≤ n ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · calc (k + 1) * k.factorial ≤ (k + 1) * k ^ (k - 1) := Nat.mul_le_mul_left _ ih
        _ ≤ (k + 1) * (k + 1) ^ (k - 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) _)
        _ = (k + 1) ^ k := by
          rw [← pow_succ']; congr 1; omega

/-- **Soundness** of Protocol 2 with the union bound over roots and permutations. -/
theorem soundness_bound [Fact p.Prime] (excl : Bool) {G : SimpleGraph V} (hG : G.Connected)
    (hS : ¬ Sym G) (P : (V → ZMod p) → V → Resp V p) :
    (protocol p excl).accProb G P ≤
      (Fintype.card V * (Fintype.card V).factorial * (2 * (Fintype.card V ^ 2 - 1)) : ℕ) / p := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc (protocol p excl).accProb G P
      ≤ uprob fun c : V → ZMod p =>
          ∃ rσ ∈ (univ : Finset (V × Equiv.Perm V)), Bad G rσ.1 rσ.2 (c rσ.1) :=
        uprob_mono fun c h => accept_imp_bad hG h
    _ ≤ ∑ rσ : V × Equiv.Perm V, uprob fun c : V → ZMod p => Bad G rσ.1 rσ.2 (c rσ.1) :=
        uprob_exists_le _ _
    _ = ∑ rσ : V × Equiv.Perm V, uprob (Bad (p := p) G rσ.1 rσ.2) := by
        refine Finset.sum_congr rfl fun rσ _ => ?_
        exact uprob_coord rσ.1 _
    _ ≤ ∑ _rσ : V × Equiv.Perm V, ((2 * (Fintype.card V ^ 2 - 1) : ℕ) : ℝ) / p := by
        refine Finset.sum_le_sum fun rσ _ => ?_
        rw [uprob_eq_card_filter, ZMod.card, div_le_div_iff_of_pos_right hp0]
        exact_mod_cast card_bad_le (p := p) hS rσ.1 rσ.2
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm]
        rw [nsmul_eq_mul, mul_div_assoc']
        push_cast
        ring

theorem soundness [Fact p.Prime] (excl : Bool) (hp : 10 * Fintype.card V ^ (Fintype.card V + 2) ≤ p)
    {G : SimpleGraph V} (hG : G.Connected) (hS : ¬ Sym G) (P : (V → ZMod p) → V → Resp V p) :
    (protocol p excl).accProb G P < 1 / 3 := by
  refine (soundness_bound excl hG hS P).trans_lt ?_
  set n := Fintype.card V
  have hn : 1 ≤ n := Fintype.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [div_lt_div_iff₀ hp0 (by norm_num)]
  have hf := factorial_le_pow_pred n
  -- `n · n! · (n² - 1) < n · n^(n-1) · n² = n^(n+2)`
  have h1 : n * n.factorial * (n ^ 2 - 1) < n ^ (n + 2) := by
    have h2 : n ^ 2 - 1 < n ^ 2 := by
      have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
      omega
    calc n * n.factorial * (n ^ 2 - 1) ≤ n * n ^ (n - 1) * (n ^ 2 - 1) := by gcongr
      _ < n * n ^ (n - 1) * n ^ 2 := by
          apply Nat.mul_lt_mul_of_pos_left h2; positivity
      _ = n ^ (n + 2) := by
          rw [← pow_succ', ← pow_add]; congr 1; omega
  have h3 : n * n.factorial * (2 * (n ^ 2 - 1)) * 3 < 1 * p := by
    have : n * n.factorial * (2 * (n ^ 2 - 1)) = 2 * (n * n.factorial * (n ^ 2 - 1)) := by ring
    omega
  exact_mod_cast h3

/-! ### Completeness -/

/-- The honest dAM prover: it reuses the honest dMAM prover of Protocol 1 (all of whose first-round
data is fixed in advance anyway) and broadcasts the whole automorphism. -/
noncomputable def honest2 {G : SimpleGraph V} (hG : G.Connected) (σ : Equiv.Perm V) {r tr : V}
    {excl : Bool} (htr : excl = true ∨ tr ∉ cnbhd G r) : (V → ZMod p) → V → Resp V p :=
  fun c u =>
    let P := Protocol1.honest (p := p) hG σ htr
    ((σ, c r, r), ((P.first u).2.2.1, (P.first u).2.2.2, (P.second c u).2.1, (P.second c u).2.2))

theorem completeness_one [NeZero p] {G : SimpleGraph V} (hG : G.Connected) {σ : Equiv.Perm V}
    (hσ : IsAut G σ) {r tr : V} (hr : σ r ≠ r) {excl : Bool}
    (htr : excl = true ∨ tr ∉ cnbhd G r) :
    (protocol p excl).accProb G (honest2 (p := p) hG σ htr) = 1 := by
  have hall : ∀ c, (protocol p excl).Accepts G (honest2 (p := p) hG σ htr) c := by
    intro c v
    rw [out_mask]
    refine ⟨fun u _ => rfl, ?_⟩
    exact honest_verify (p := p) hG hσ hr htr c v
  unfold AMProtocol.accProb
  rw [show (protocol p excl).Accepts G (honest2 (p := p) hG σ htr) = fun _ => True from
    funext fun c => propext ⟨fun _ => trivial, fun _ => hall c⟩]
  simp [uprob_true, NeZero.ne p]

/-- **Theorem 3.5**: for a prime `p ≥ 10 n^{n+2}`, Protocol 2 decides `Sym` on connected graphs. -/
theorem theorem_3_5 [Fact p.Prime] (hp : 10 * Fintype.card V ^ (Fintype.card V + 2) ≤ p) :
    (protocol (V := V) p true).Decides (fun G => G.Connected) Sym := by
  intro G hG
  refine ⟨fun ⟨ρ, hρ, hne⟩ => ?_, fun hS P => soundness true hp hG hS P⟩
  obtain ⟨r, hr⟩ : ∃ r, ρ r ≠ r := by
    by_contra h; push Not at h; exact hne (funext h)
  let σ : Equiv.Perm V := Equiv.ofBijective ρ hρ.1
  have hσ : IsAut G σ := hρ
  exact ⟨honest2 (p := p) hG σ (r := r) (tr := r) (Or.inl rfl), by
    rw [completeness_one hG hσ hr]; norm_num⟩

/-- **Theorem 1.3**: `Sym ∈ dAM[O(n log n)]` — challenge and response alphabets have at most
`2^{30 n (log₂ n + 1)}` symbols. -/
theorem theorem_1_3 :
    InDAM (fun _ _ _ G => Sym G) (fun n => 30 * n * (Nat.log 2 n + 1)) := by
  intro V _ _ _
  set n := Fintype.card V with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (10 * n ^ (n + 2)) (by positivity)
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨ZMod p, Resp V p, inferInstance, inferInstance, protocol p true, ?_, ?_,
    theorem_3_5 hlt.le⟩
  all_goals
    beta_reduce
    set L := Nat.log 2 n + 1
    have hL : n < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) n
    have hL1 : 1 ≤ L := by omega
    have hpow : ∀ k, n ^ k ≤ 2 ^ (L * k) := fun k => by
      rw [pow_mul]; exact Nat.pow_le_pow_left hL.le k
    have hp' : p ≤ 2 ^ (5 * L + L * (n + 2)) := by
      have h2 : (2 : ℕ) ^ 5 ≤ 2 ^ (5 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc p ≤ 2 * (10 * n ^ (n + 2)) := hle
        _ ≤ 2 ^ 5 * n ^ (n + 2) := by omega
        _ ≤ 2 ^ (5 * L) * 2 ^ (L * (n + 2)) := Nat.mul_le_mul h2 (hpow _)
        _ = _ := by rw [← pow_add]
  · rw [ZMod.card]
    exact hp'.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  · simp only [Resp, Bc, Uc, Fintype.card_prod, Fintype.card_perm, ZMod.card, Fintype.card_fin]
    have hfac : n.factorial ≤ 2 ^ (L * n) := (Nat.factorial_le_pow n).trans (hpow n)
    calc n.factorial * (p * n) * (n * (n * (p * p)))
        ≤ 2 ^ (L * n) * (2 ^ (5 * L + L * (n + 2)) * 2 ^ (L * 1)) *
          (2 ^ (L * 1) * (2 ^ (L * 1) * (2 ^ (5 * L + L * (n + 2)) *
            2 ^ (5 * L + L * (n + 2))))) := by
          have h1 : n ≤ 2 ^ (L * 1) := by simpa using hpow 1
          gcongr
      _ = 2 ^ (L * (4 * n + 9) + 15 * L) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (30 * n * L) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

end Podc.InteractiveDistributedProofs.Protocol2
