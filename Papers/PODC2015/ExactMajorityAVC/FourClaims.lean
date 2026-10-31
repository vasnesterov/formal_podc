import Papers.PODC2015.ExactMajorityAVC.FourModel

/-!
# Claims B.2–B.5 of Appendix B

For a protocol `P` on the four states satisfying the correctness properties `Correct P γ`:

* `claim_B_2`: two initial configurations of the same size with different numbers of agents in
  `S0` have disjoint sets of reachable configurations (Claim B.2);
* `corollary_B_3`: from an initial configuration containing both `S0` and `S1`, the
  configurations "all `S0`" and "all `S1`" are unreachable (Corollary B.3);
* `gamma_S0`, `gamma_S1`, `gamma_X_ne_gamma_Y`: `γ(S0) = 0`, `γ(S1) = 1`, `γ(X) ≠ γ(Y)`;
* `claim_B_4`: for each output `i`, `C_i` contains a configuration with at least two agents in
  `S i` and two in the other state of output `i` (Claim B.4);
* `claim_B_5`: two agents in states with the same output either keep or swap their states
  (Claim B.5). This part does not need the symmetry hypothesis: it holds for both orientations.
-/

namespace Podc.ExactMajorityAVC.Four

open Cslib.PopulationProtocol Q4 Multiset

variable {P : Protocol Q4} {γ : Q4 → Bool}

lemma cfg_true (a b : ℕ) : cfg true a b = cfg false b a := by
  simp [cfg, add_comm]

lemma card_cfg (i : Bool) (a b : ℕ) : card (cfg i a b) = a + b := by simp [cfg]

/-- **Claim B.2.** Initial configurations of the same size with different numbers of agents in
`S0` have no common reachable configuration. -/
theorem claim_B_2 (hC : Correct P γ) {a b a' b' : ℕ} (hn : a + b = a' + b') (ha : a ≠ a')
    {r : Multiset Q4} (h : Reach P (cfg false a b) r) (h' : Reach P (cfg false a' b') r) : False := by
  -- without loss of generality `a > a'`
  wlog hlt : a' < a generalizing a b a' b'
  · exact this hn.symm (Ne.symm ha) h' h (by omega)
  -- the extra agents: `n - 1 - a'` in `S0`, `a'` in `S1`
  set E := cfg false (a + b - 1 - a') a'
  have h1 : Reach P (cfg false (a + (a + b - 1 - a')) (b + a')) (r + E) := by
    simpa [cfg, E, replicate_add, add_comm, add_left_comm, add_assoc] using h.add_right E
  have h2 : Reach P (cfg true (a' + b') (a' + (a + b - 1 - a'))) (r + E) := by
    rw [cfg_true]
    simpa [cfg, E, replicate_add, add_comm, add_left_comm, add_assoc] using h'.add_right E
  obtain ⟨c, hc, habs⟩ := hC.live false _ _ (by omega) _ h1
  exact hC.safe true _ _ (by omega) _ (h2.trans hc) habs

/-- Claim B.2 for initial configurations described from the side of output `i`. -/
theorem claim_B_2' (hC : Correct P γ) (i : Bool) {a b a' b' : ℕ} (hn : a + b = a' + b')
    (ha : a ≠ a') {r : Multiset Q4} (h : Reach P (cfg i a b) r) (h' : Reach P (cfg i a' b') r) :
    False := by
  cases i
  · exact claim_B_2 hC hn ha h h'
  · rw [cfg_true] at h h'; exact claim_B_2 hC (by omega) (by omega) h h'

/-- **Corollary B.3.** From an initial configuration with agents in both `S i` and `S (!i)`,
the configuration with all agents in `S i` is unreachable. -/
theorem corollary_B_3 (hC : Correct P γ) (i : Bool) {a b : ℕ} (hb : 1 ≤ b)
    (h : Reach P (cfg i a b) (replicate (a + b) (S i))) : False :=
  claim_B_2' hC i (a' := a + b) (b' := 0) (by omega) (by omega) h
    (by rw [show cfg i (a + b) 0 = replicate (a + b) (S i) by simp [cfg]])

/-- Configurations of one agent cannot change. -/
lemma reach_singleton {q : Q4} {c : Multiset Q4} (h : Reach P {q} c) : c = {q} := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨t, -, ht⟩ := hs
    have := ht.two_le_card
    simp at this

/-- `γ(S i) = i` (a single agent in `S i` must output `i`). -/
theorem gamma_S (hC : Correct P γ) (i : Bool) : γ (S i) = i := by
  obtain ⟨c, hc, habs⟩ := hC.live i 1 0 (by omega) _ .refl
  have : c = {S i} := reach_singleton (by simpa [cfg] using hc)
  subst this
  exact habs.mem _ (mem_singleton_self _)

lemma eq_replicate_of_forall {c : Multiset Q4} {s : Q4} (h : ∀ q ∈ c, q = s) :
    c = replicate (card c) s := eq_replicate.2 ⟨rfl, h⟩

/-- **`γ(X) ≠ γ(Y)`** (first case of the proof of Theorem B.1, with `n = 3`). -/
theorem gamma_X_ne_gamma_Y (hC : Correct P γ) : γ X ≠ γ Y := by
  intro hXY
  have h0 := gamma_S hC false
  have h1 := gamma_S hC true
  simp only [S_false, S_true] at h0 h1
  -- the majority `i := !γ X` can only be output by `S i`
  have key : ∀ i : Bool, γ X = !i → False := by
    intro i hi
    obtain ⟨c, hc, habs⟩ := hC.live i 2 1 (by omega) _ .refl
    have hall : ∀ q ∈ c, q = S i := by
      intro q hq
      have hq' := habs.mem q hq
      cases q <;> cases i <;> simp only [hi, ← hXY, h0, h1] at hq' <;> first | rfl | simp at hq'
    have := eq_replicate_of_forall hall
    rw [hc.card_eq, card_cfg] at this
    exact corollary_B_3 hC i (by omega) (this ▸ hc)
  exact key (!γ X) (by simp)

/-! ### Claims B.4 and B.5 -/

section Side

/-- The data of one "side" `i` of the protocol: `s = S i` and the other state `x` with output
`i`; every state of output `i` is `s` or `x`. -/
structure Side (γ : Q4 → Bool) (i : Bool) (x : Q4) : Prop where
  ne : x ≠ S i
  gx : γ x = i
  cover : ∀ q, γ q = i → q = S i ∨ q = x

variable {i : Bool} {x : Q4}

/-- Two-state configurations `k · s + l · x`. -/
def two (s x : Q4) (k l : ℕ) : Multiset Q4 := replicate k s + replicate l x

lemma card_two (s x : Q4) (k l : ℕ) : card (two s x k l) = k + l := by simp [two]

lemma eq_two {s x : Q4} (hsx : x ≠ s) {c : Multiset Q4} (h : ∀ q ∈ c, q = s ∨ q = x) :
    c = two s x (count s c) (count x c) := by
  ext r
  rw [two, count_add, count_replicate, count_replicate]
  by_cases hrs : r = s
  · subst hrs; simp [hsx]
  · by_cases hrx : r = x
    · subst hrx; simp [Ne.symm hrs]
    · simp only [show ¬ s = r from Ne.symm hrs, show ¬ x = r from Ne.symm hrx, ↓reduceIte,
        add_zero]
      exact count_eq_zero.2 fun hr => (h r hr).elim hrs hrx

/-- Absorbing configurations of output `i` only contain `s` and `x`. -/
lemma Side.mem (hs : Side γ i x) {c : Multiset Q4} (habs : Absorbing P γ i c) :
    ∀ q ∈ c, q = S i ∨ q = x := fun q hq => hs.cover q (habs.mem q hq)

lemma Side.eq_two (hs : Side γ i x) {c : Multiset Q4} (habs : Absorbing P γ i c) :
    c = two (S i) x (count (S i) c) (count x c) := Four.eq_two hs.ne (hs.mem habs)

/-- An absorbing configuration of output `i` reachable from `cfg i a b` (`b < a`). -/
lemma exists_abs (hC : Correct P γ) (hs : Side γ i x) {a b : ℕ} (hab : b < a) :
    ∃ k l, Reach P (cfg i a b) (two (S i) x k l) ∧ Absorbing P γ i (two (S i) x k l) ∧
      k + l = a + b := by
  obtain ⟨c, hc, habs⟩ := hC.live i a b hab _ .refl
  have he := hs.eq_two habs
  refine ⟨_, _, he ▸ hc, he ▸ habs, ?_⟩
  rw [← card_two, ← he, hc.card_eq, card_cfg]

/-- Moreover, if `1 ≤ b`, it is not "all `s`". -/
lemma exists_abs' (hC : Correct P γ) (hs : Side γ i x) {a b : ℕ} (hab : b < a) (hb : 1 ≤ b) :
    ∃ k l, Reach P (cfg i a b) (two (S i) x k l) ∧ Absorbing P γ i (two (S i) x k l) ∧
      k + l = a + b ∧ 1 ≤ l := by
  obtain ⟨k, l, hr, habs, hkl⟩ := exists_abs hC hs hab
  refine ⟨k, l, hr, habs, hkl, ?_⟩
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    exact (corollary_B_3 hC i hb (by rw [← hkl]; simpa [two] using hr)).elim
  · exact hl

/-- **Claim B.4.** `C_i` contains a configuration with at least two agents in `S i` and at least
two in `x` (proof with `n = 9`). -/
theorem claim_B_4 (hC : Correct P γ) (hs : Side γ i x) :
    ∃ k l, 2 ≤ k ∧ 2 ≤ l ∧ Absorbing P γ i (two (S i) x k l) := by
  by_contra hne
  push Not at hne
  have key : ∀ b, 1 ≤ b → b < 9 - b → ∃ k, Reach P (cfg i (9 - b) b) (two (S i) x k (9 - k)) ∧
      (k = 0 ∨ k = 1 ∨ k = 8) := by
    intro b hb hlt
    obtain ⟨k, l, hr, habs, hkl, hl⟩ := exists_abs' hC hs hlt hb
    refine ⟨k, by rwa [show 9 - k = l by omega], ?_⟩
    by_cases hk : 2 ≤ k
    · have := hne k l hk
      by_cases hl2 : 2 ≤ l
      · exact absurd habs (this hl2)
      · omega
    · omega
  obtain ⟨k1, r1, h1⟩ := key 1 le_rfl (by omega)
  obtain ⟨k2, r2, h2⟩ := key 2 (by omega) (by omega)
  obtain ⟨k3, r3, h3⟩ := key 3 (by omega) (by omega)
  obtain ⟨k4, r4, h4⟩ := key 4 (by omega) (by omega)
  have B2 := fun {a b a' b' : ℕ} (hn : a + b = a' + b') (ha : a ≠ a') {r : Multiset Q4}
    (h : Reach P (cfg i a b) r) (h' : Reach P (cfg i a' b') r) => claim_B_2' hC i hn ha h h'
  -- pigeonhole: two of `k1, …, k4 ∈ {0, 1, 8}` coincide
  rcases (by omega : k1 = k2 ∨ k1 = k3 ∨ k1 = k4 ∨ k2 = k3 ∨ k2 = k4 ∨ k3 = k4) with
    h | h | h | h | h | h <;> subst h
  · exact B2 (by omega) (by omega) r1 r2
  · exact B2 (by omega) (by omega) r1 r3
  · exact B2 (by omega) (by omega) r1 r4
  · exact B2 (by omega) (by omega) r2 r3
  · exact B2 (by omega) (by omega) r2 r4
  · exact B2 (by omega) (by omega) r3 r4

/-- One interaction, in multiset form. -/
lemma step_pair {p q : Q4} {m m' : Multiset Q4} (hpq : ({p, q} : Multiset Q4) = m)
    (h : pair (P.δ p q) = m') (r : Multiset Q4) : MStep (trans P) (m + r) (m' + r) := by
  have h1 : m + r = p ::ₘ q ::ₘ r := by rw [← hpq]; simp [insert_eq_cons]
  have h2 : m' + r = (P.δ p q).1 ::ₘ (P.δ p q).2 ::ₘ r := by
    rw [← h]; simp [pair, insert_eq_cons]
  rw [h1, h2]; exact step_of p q r

section Pump

variable {s x p q : Q4}

lemma two_succ_succ (k l : ℕ) : two s x (k + 1) (l + 1) = {s, x} + two s x k l := by
  simp only [two]; ms_eq

lemma two_succ_left (k l : ℕ) : two s x (k + 2) l = {s, s} + two s x k l := by
  simp only [two]; ms_eq

lemma two_succ_right (k l : ℕ) : two s x k (l + 2) = {x, x} + two s x k l := by
  simp only [two]; ms_eq

lemma pair_comm' (a b : Q4) : ({a, b} : Multiset Q4) = {b, a} := by ms_eq

/-- `s + x → x + x`, repeatedly. -/
lemma pump_sx_xx (hpq : ({p, q} : Multiset Q4) = {s, x}) (h : pair (P.δ p q) = {x, x}) :
    ∀ k l, Reach P (two s x k (l + 1)) (two s x 0 (k + l + 1)) := by
  intro k
  induction k with
  | zero => intro l; simp only [zero_add]; exact .refl
  | succ k ih =>
    intro l
    have := step_pair (P := P) hpq h (two s x k l)
    rw [← two_succ_succ, ← two_succ_right] at this
    exact (Relation.ReflTransGen.single this).trans (by
      have := ih (l + 1); rwa [show k + (l + 1) + 1 = k + 1 + l + 1 by omega] at this)

/-- `s + x → s + s`, repeatedly. -/
lemma pump_sx_ss (hpq : ({p, q} : Multiset Q4) = {s, x}) (h : pair (P.δ p q) = {s, s}) :
    ∀ l k, Reach P (two s x (k + 1) l) (two s x (k + l + 1) 0) := by
  intro l
  induction l with
  | zero => intro k; exact .refl
  | succ l ih =>
    intro k
    have := step_pair (P := P) hpq h (two s x k l)
    rw [← two_succ_succ, ← two_succ_left] at this
    exact (Relation.ReflTransGen.single this).trans (by
      have := ih (k + 1); rwa [show k + 1 + l + 1 = k + (l + 1) + 1 by omega] at this)

/-- `x + x → s + x`, repeatedly. -/
lemma pump_xx_sx (hpq : ({p, q} : Multiset Q4) = {x, x}) (h : pair (P.δ p q) = {s, x}) :
    ∀ l k, Reach P (two s x k (l + 1)) (two s x (k + l) 1) := by
  intro l
  induction l with
  | zero => intro k; exact .refl
  | succ l ih =>
    intro k
    have := step_pair (P := P) hpq h (two s x k l)
    rw [← two_succ_right, ← two_succ_succ] at this
    exact (Relation.ReflTransGen.single this).trans (by
      have := ih (k + 1); rwa [show k + 1 + l = k + (l + 1) by omega] at this)

/-- `x + x → s + s`, repeatedly. -/
lemma pump_xx_ss (hpq : ({p, q} : Multiset Q4) = {x, x}) (h : pair (P.δ p q) = {s, s}) (r : ℕ) :
    ∀ j k, Reach P (two s x k (2 * j + r)) (two s x (k + 2 * j) r) := by
  intro j
  induction j with
  | zero => intro k; simp only [Nat.mul_zero, zero_add, add_zero]; exact .refl
  | succ j ih =>
    intro k
    have := step_pair (P := P) hpq h (two s x k (2 * j + r))
    rw [← two_succ_right, ← two_succ_left] at this
    rw [show 2 * (j + 1) + r = 2 * j + r + 2 by omega]
    exact (Relation.ReflTransGen.single this).trans (by
      have := ih (k + 2); rwa [show k + 2 + 2 * j = k + 2 * (j + 1) by omega] at this)

/-- `s + s → s + x`, repeatedly. -/
lemma pump_ss_sx (hpq : ({p, q} : Multiset Q4) = {s, s}) (h : pair (P.δ p q) = {s, x}) :
    ∀ k l, Reach P (two s x (k + 1) l) (two s x 1 (k + l)) := by
  intro k
  induction k with
  | zero => intro l; simp only [zero_add]; exact .refl
  | succ k ih =>
    intro l
    have := step_pair (P := P) hpq h (two s x k l)
    rw [← two_succ_left, ← two_succ_succ] at this
    exact (Relation.ReflTransGen.single this).trans (by
      have := ih (l + 1); rwa [show k + (l + 1) = k + 1 + l by omega] at this)

/-- `s + s → x + x`, repeatedly. -/
lemma pump_ss_xx (hpq : ({p, q} : Multiset Q4) = {s, s}) (h : pair (P.δ p q) = {x, x}) (r : ℕ) :
    ∀ j l, Reach P (two s x (2 * j + r) l) (two s x r (l + 2 * j)) := by
  intro j
  induction j with
  | zero => intro l; simp only [Nat.mul_zero, zero_add, add_zero]; exact .refl
  | succ j ih =>
    intro l
    have := step_pair (P := P) hpq h (two s x (2 * j + r) l)
    rw [← two_succ_left, ← two_succ_right] at this
    rw [show 2 * (j + 1) + r = 2 * j + r + 2 by omega]
    exact (Relation.ReflTransGen.single this).trans (by
      have := ih (l + 2); rwa [show l + 2 + 2 * j = l + 2 * (j + 1) by omega] at this)

end Pump

lemma two_split (s x : Q4) (k l : ℕ) {p q : Q4} (hp : p = s ∨ p = x) (hq : q = s ∨ q = x) :
    ∃ r, two s x (k + 2) (l + 2) = p ::ₘ q ::ₘ r := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
  · exact ⟨two s x k (l + 2), by simp only [two]; ms_eq⟩
  · exact ⟨two s x (k + 1) (l + 1), by simp only [two]; ms_eq⟩
  · exact ⟨two s x (k + 1) (l + 1), by simp only [two]; ms_eq⟩
  · exact ⟨two s x (k + 2) l, by simp only [two]; ms_eq⟩

/-- First part of the proof of Claim B.5: two agents with output `i` interact into two agents
with output `i` (they are both present in the mixed absorbing configuration of Claim B.4). -/
lemma out_closed (hC : Correct P γ) (hs : Side γ i x) {p q : Q4} (hp : γ p = i) (hq : γ q = i) :
    pair (P.δ p q) = {S i, S i} ∨ pair (P.δ p q) = {S i, x} ∨ pair (P.δ p q) = {x, x} := by
  obtain ⟨k, l, hk, hl, habs⟩ := claim_B_4 hC hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hl
  have hp' := hs.cover p hp
  have hq' := hs.cover q hq
  obtain ⟨r, hr⟩ := two_split (S i) x k l hp' hq'
  have hstep := step_of (P := P) p q r
  rw [← hr] at hstep
  have h1 := habs _ (.single hstep) (P.δ p q).1 (by simp)
  have h2 := habs _ (.single hstep) (P.δ p q).2 (by simp)
  rcases hs.cover _ h1 with e1 | e1 <;> rcases hs.cover _ h2 with e2 | e2 <;>
    simp [pair, e1, e2, pair_comm' x (S i)]

lemma two_zero_right (s x : Q4) (k : ℕ) : two s x k 0 = replicate k s := by simp [two]

/-- Claim B.5 for `[S i, x]` (either orientation). -/
lemma claim_B_5_sx (hC : Correct P γ) (hs : Side γ i x) {p q : Q4}
    (hpq : ({p, q} : Multiset Q4) = {S i, x}) : pair (P.δ p q) = {S i, x} := by
  have hmem : ∀ r ∈ ({S i, x} : Multiset Q4), γ r = i := by
    intro r hr; simp only [insert_eq_cons, mem_cons, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact gamma_S hC i
    · exact hs.gx
  have hp := hmem p (hpq ▸ by simp)
  have hq := hmem q (hpq ▸ by simp)
  obtain ⟨kO, lO, hO, -, hkO, hlO⟩ := exists_abs' hC hs (a := 4) (b := 1) (by omega) le_rfl
  obtain ⟨kT, lT, hT, -, hkT, hlT⟩ := exists_abs' hC hs (a := 3) (b := 2) (by omega) (by omega)
  rcases out_closed hC hs hp hq with h | h | h
  · -- `[s, x] → [s, s]`: the configurations of `C_i` reached must be "all `x`"
    have key : ∀ {a b k l : ℕ}, 1 ≤ b → Reach P (cfg i a b) (two (S i) x k l) → k + l = a + b →
        k = 0 := by
      intro a b k l hb hr hkl
      by_contra hk
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_iff_ne_zero.2 hk)
      have := hr.trans (pump_sx_ss hpq h l k')
      rw [two_zero_right, show k' + l + 1 = a + b by omega] at this
      exact corollary_B_3 hC i hb this
    have hk0 := key le_rfl hO hkO
    have hk0' := key (by omega) hT hkT
    subst hk0 hk0'
    obtain rfl : lO = 5 := by omega
    obtain rfl : lT = 5 := by omega
    exact (claim_B_2' hC i (by omega) (by omega) hO hT).elim
  · exact h
  · -- `[s, x] → [x, x]`: both reach "all `x`"
    obtain ⟨lO, rfl⟩ := Nat.exists_eq_add_of_le' hlO
    obtain ⟨lT, rfl⟩ := Nat.exists_eq_add_of_le' hlT
    have h1 := hO.trans (pump_sx_xx hpq h kO lO)
    have h2 := hT.trans (pump_sx_xx hpq h kT lT)
    rw [show kO + lO + 1 = 5 by omega] at h1
    rw [show kT + lT + 1 = 5 by omega] at h2
    exact (claim_B_2' hC i (by omega) (by omega) h1 h2).elim

/-- Claim B.5 for `[x, x]`. -/
lemma claim_B_5_xx (hC : Correct P γ) (hs : Side γ i x) : pair (P.δ x x) = {x, x} := by
  obtain ⟨kO, lO, hO, -, hkO, hlO⟩ := exists_abs' hC hs (a := 4) (b := 1) (by omega) le_rfl
  obtain ⟨kT, lT, hT, -, hkT, hlT⟩ := exists_abs' hC hs (a := 3) (b := 2) (by omega) (by omega)
  rcases out_closed hC hs hs.gx hs.gx with h | h | h
  · -- `[x, x] → [s, s]`: the parity of `#x` is invariant
    have key : ∀ {a b k l : ℕ}, 1 ≤ b → Reach P (cfg i a b) (two (S i) x k l) → k + l = a + b →
        Reach P (cfg i a b) (two (S i) x (a + b - 1) 1) := by
      intro a b k l hb hr hkl
      have hp := pump_xx_ss rfl h (l % 2) (l / 2) k
      rw [Nat.div_add_mod] at hp
      have hpar := hr.trans hp
      rcases Nat.mod_two_eq_zero_or_one l with h0 | h1
      · rw [h0, two_zero_right, show k + 2 * (l / 2) = a + b by omega] at hpar
        exact (corollary_B_3 hC i hb hpar).elim
      · rwa [h1, show k + 2 * (l / 2) = a + b - 1 by omega] at hpar
    exact (claim_B_2' hC i (by omega) (by omega) (key le_rfl hO hkO)
      (key (a := 3) (b := 2) (by omega) hT hkT)).elim
  · -- `[x, x] → [s, x]`: both reach `4 s + x`
    obtain ⟨lO, rfl⟩ := Nat.exists_eq_add_of_le' hlO
    obtain ⟨lT, rfl⟩ := Nat.exists_eq_add_of_le' hlT
    have h1 := hO.trans (pump_xx_sx rfl h lO kO)
    have h2 := hT.trans (pump_xx_sx rfl h lT kT)
    rw [show kO + lO = 4 by omega] at h1
    rw [show kT + lT = 4 by omega] at h2
    exact (claim_B_2' hC i (by omega) (by omega) h1 h2).elim
  · exact h

/-- The pigeonhole step of Claim B.5 for `[s, s]` (`n = 7`). -/
lemma pigeon7 (hC : Correct P γ) (x : Q4)
    (key : ∀ a b, b < a → a + b = 7 → ∃ e, e ≤ 1 ∧ Reach P (cfg i a b) (two (S i) x e (7 - e))) :
    False := by
  obtain ⟨e1, he1, r1⟩ := key 6 1 (by omega) rfl
  obtain ⟨e2, he2, r2⟩ := key 5 2 (by omega) rfl
  obtain ⟨e3, he3, r3⟩ := key 4 3 (by omega) rfl
  rcases (by omega : e1 = e2 ∨ e1 = e3 ∨ e2 = e3) with h' | h' | h' <;> subst h'
  · exact claim_B_2' hC i (by omega) (by omega) r1 r2
  · exact claim_B_2' hC i (by omega) (by omega) r1 r3
  · exact claim_B_2' hC i (by omega) (by omega) r2 r3

/-- Claim B.5 for `[s, s]` (proof with `n = 7`). -/
lemma claim_B_5_ss (hC : Correct P γ) (hs : Side γ i x) :
    pair (P.δ (S i) (S i)) = {S i, S i} := by
  have hg := gamma_S hC i
  rcases out_closed hC hs hg hg with h | h | h
  · exact h
  · -- `[s, s] → [s, x]`: `#s` decreases to `min(#s, 1)`
    refine (pigeon7 (i := i) hC x fun a b hab h7 => ?_).elim
    obtain ⟨k, l, hr, -, hkl⟩ := exists_abs hC hs hab
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact ⟨0, by omega, by rwa [show 7 - 0 = l by omega]⟩
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
      have := hr.trans (pump_ss_sx rfl h k' l)
      exact ⟨1, le_rfl, by rwa [show 7 - 1 = k' + l by omega]⟩
  · -- `[s, s] → [x, x]`: the parity of `#s` is invariant
    refine (pigeon7 (i := i) hC x fun a b hab h7 => ?_).elim
    obtain ⟨k, l, hr, -, hkl⟩ := exists_abs hC hs hab
    have hp := pump_ss_xx rfl h (k % 2) (k / 2) l
    rw [Nat.div_add_mod] at hp
    exact ⟨k % 2, by omega, by rw [show 7 - k % 2 = l + 2 * (k / 2) by omega]; exact hr.trans hp⟩

/-- **Claim B.5.** Two agents whose states have the same output `i` keep or swap their states
(for both orientations of the interaction). -/
theorem claim_B_5 (hC : Correct P γ) (hs : Side γ i x) {p q : Q4} (hp : γ p = i)
    (hq : γ q = i) : pair (P.δ p q) = {p, q} := by
  rcases hs.cover p hp with rfl | rfl <;> rcases hs.cover q hq with rfl | rfl
  · exact claim_B_5_ss hC hs
  · exact claim_B_5_sx hC hs rfl
  · rw [claim_B_5_sx hC hs (pair_comm' _ _)]; exact pair_comm' _ _
  · exact claim_B_5_xx hC hs

end Side

end Podc.ExactMajorityAVC.Four
