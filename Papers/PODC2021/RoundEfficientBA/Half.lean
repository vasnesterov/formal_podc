import Papers.PODC2021.RoundEfficientBA.Proxcensus

/-!
# Proxcensus for `t < n/2` with threshold signatures (Section 3.3.2, Lemmas 3.4–3.6)

Protocol `Prox_{2r-1}` (`r ≥ 3` rounds) with an `(n-t)`-out-of-`n` unique threshold signature
scheme, treated as an ideal primitive.

## Model

Values in a finite domain `D`; parties `P`, `n = |P|`. A certificate `Σ` on `v` is formed from
`n - t` signature shares on `v`, a certificate `Ω` on `v` from `n - t` shares `ω` on `v`. Since
signatures are unique, a set `{(v, Σ)}` of valid certificates is represented by the set of
certified values (`Finset D`); invalid certificates are discarded by the receiver (`I_k` in the
paper), so the adversary can only send certificates it can *form*.

Adaptive corruption at round granularity: `A.cr q` is the round from which `q` is corrupted
(`q` follows the protocol in the rounds `k < A.cr q`; a party with `A.cr q > r` is honest at the
end). In a round in which `q` is corrupted the adversary chooses `q`'s messages (strongly rushing:
this includes replacing the message of a party it corrupts in that round). It may use
* in round 1: signature shares of corrupted parties on any values (`A.sh1 q i`);
* in round 2: shares `ω` of corrupted parties on any values (`A.wsh q i`), and certificates `Σ`
  (`A.sig 2 q i`);
* in rounds `k ≥ 2`: certificates `Σ` on values `v` with at least `n - t` shares available
  (`consSig`: shares sent in round 1 by parties honest in round 1, plus the keys of all parties
  corrupted by round `k`), and in rounds `k ≥ 3` certificates `Ω` likewise (`consOm`).

The protocol (paper's pseudocode):
* round 1: send a share on the input; `S¹ = {v | ≥ n-t shares on v received}`;
* `ω` is a share on the own input `x`, sent in round 2 iff `S¹ = {x}`;
* round 2: send `S¹` and `ω`; `S² = ⋃ received S¹`; `Ω² = {x}` if `≥ n-t` shares `ω` on `x` were
  received (`Ω` is only formed on the own input, lines 11–12), else `∅`;
* rounds `k = 3 … r`: send `S^{k-1}`, `Ω^{k-1}`; `S^k`, `Ω^k` = unions of the received sets;
* output: `(z, j)` for the largest `j ∈ [1, r-1]` with `z ∈ S^{r-j}`, `z ∈ Ω^{r-j+1}` and
  `S^{j+1} ⊆ {z}`; otherwise `(d₀, 0)` (the paper's default `0`).

Every party sends to itself, so the sets of a party honest in round `k+1` grow from round `k` to
round `k+1`.

## Results

* `half_validity` (**Lemma 3.5**) and `two_run_cons` (**Lemma 3.6**), together `half_isProx`
  (**Lemma 3.4**): for `2t < n`, `r ≥ 3` and at most `t` corruptions, the outputs of the parties
  honest at the end form a `(2r-1)`-slot Proxcensus.
-/

namespace RoundEfficientBA.Half

variable {P D : Type*} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]

/-- The adversary's choices (see the module docstring). -/
structure Adv (P D : Type*) where
  /-- `q` follows the protocol in the rounds `k < cr q`. -/
  cr : P → ℕ
  /-- Round 1: values on which the corrupted `q` gives signature shares to `i`. -/
  sh1 : P → P → Finset D
  /-- Round `k ≥ 2`: values with a certificate `Σ` sent by the corrupted `q` to `i`. -/
  sig : ℕ → P → P → Finset D
  /-- Round 2: values on which the corrupted `q` gives shares `ω` to `i`. -/
  wsh : P → P → Finset D
  /-- Round `k ≥ 3`: values with a certificate `Ω` sent by the corrupted `q` to `i`. -/
  om : ℕ → P → P → Finset D

variable (n t : ℕ) (x : P → D) (A : Adv P D)

/-- `S¹` of party `i`: the values with at least `n - t` shares received in round 1. -/
def S1 (i : P) : Finset D :=
  Finset.univ.filter fun v => n - t ≤
    (Finset.univ.filter fun q => (1 < A.cr q ∧ x q = v) ∨ (A.cr q ≤ 1 ∧ v ∈ A.sh1 q i)).card

/-- Party `q` sends the share `ω` (on its input) in round 2: its `S¹` is exactly `{x q}`. -/
def SignsOm (q : P) : Prop := S1 n t x A q = {x q}

instance (q : P) : Decidable (SignsOm n t x A q) := by unfold SignsOm; infer_instance

/-- The sets `S^k` (`k ≥ 1`). -/
def S : ℕ → P → Finset D
  | 0, _ => ∅
  | 1, i => S1 n t x A i
  | k + 2, i =>
    (Finset.univ.filter fun q => k + 2 < A.cr q).biUnion (fun q => S (k + 1) q) ∪
      (Finset.univ.filter fun q => A.cr q ≤ k + 2).biUnion (fun q => A.sig (k + 2) q i)

/-- `Ω²` of party `i`: its own input, if at least `n - t` shares `ω` on it were received. -/
def Om2 (i : P) : Finset D :=
  if n - t ≤ (Finset.univ.filter fun q =>
      (2 < A.cr q ∧ SignsOm n t x A q ∧ x q = x i) ∨ (A.cr q ≤ 2 ∧ x i ∈ A.wsh q i)).card
  then {x i} else ∅

/-- The sets `Ω^k` (`k ≥ 2`). -/
def Om : ℕ → P → Finset D
  | 0, _ => ∅
  | 1, _ => ∅
  | 2, i => Om2 n t x A i
  | k + 3, i =>
    (Finset.univ.filter fun q => k + 3 < A.cr q).biUnion (fun q => Om (k + 2) q) ∪
      (Finset.univ.filter fun q => A.cr q ≤ k + 3).biUnion (fun q => A.om (k + 3) q i)

/-- The values on which a certificate `Σ` can be formed in round `k`. -/
def consSig (k : ℕ) : Finset D :=
  Finset.univ.filter fun v => n - t ≤
    (Finset.univ.filter fun q => (1 < A.cr q ∧ x q = v) ∨ A.cr q ≤ k).card

/-- The values on which a certificate `Ω` can be formed in round `k`. -/
def consOm (k : ℕ) : Finset D :=
  Finset.univ.filter fun v => n - t ≤
    (Finset.univ.filter fun q => (2 < A.cr q ∧ SignsOm n t x A q ∧ x q = v) ∨ A.cr q ≤ k).card

/-- The adversary only sends certificates it can form, and corrupts at most `t` parties during
the `r` rounds. -/
structure Valid (r : ℕ) : Prop where
  sig_le : ∀ k q i, 2 ≤ k → A.cr q ≤ k → A.sig k q i ⊆ consSig n t x A k
  om_le : ∀ k q i, 3 ≤ k → A.cr q ≤ k → A.om k q i ⊆ consOm n t x A k
  budget : (Finset.univ.filter fun q => A.cr q ≤ r).card ≤ t

/-- The output condition for grade `j` and value `z` (line 20 of the protocol). -/
def OutCond (r : ℕ) (i : P) (j : ℕ) (z : D) : Prop :=
  z ∈ S n t x A (r - j) i ∧ z ∈ Om n t x A (r - j + 1) i ∧ S n t x A (j + 1) i ⊆ {z}

instance (r : ℕ) (i : P) (j : ℕ) (z : D) : Decidable (OutCond n t x A r i j z) := by
  unfold OutCond; infer_instance

/-- Grade `j ∈ [1, r-1]` is achieved by some value. -/
def GradeOk (r : ℕ) (i : P) (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ r - 1 ∧ ∃ z, OutCond n t x A r i j z

instance (r : ℕ) (i : P) : DecidablePred (GradeOk n t x A r i) := by
  intro j; unfold GradeOk; infer_instance

/-- The output grade: the largest achieved grade (`0` if none). -/
def outGrade (r : ℕ) (i : P) : ℕ := Nat.findGreatest (GradeOk n t x A r i) (r - 1)

variable [LinearOrder D]

/-- The output `(y, g)` of party `i` (`d₀` = default value for grade `0`). If several values satisfy
the condition of the output grade, the least one is taken (in fact it is unique). -/
def out (r : ℕ) (d₀ : D) (i : P) : D × ℕ :=
  if h : GradeOk n t x A r i (outGrade n t x A r i) then
    ((Finset.univ.filter fun z => OutCond n t x A r i (outGrade n t x A r i) z).min'
      ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2.2.choose_spec⟩⟩, outGrade n t x A r i)
  else (d₀, 0)

end RoundEfficientBA.Half

namespace RoundEfficientBA.Half

variable {P D : Type*} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
variable {n t : ℕ} {x : P → D} {A : Adv P D}

/-! ### Unfolding -/

lemma S_succ (k : ℕ) (hk : 1 ≤ k) (i : P) :
    S n t x A (k + 1) i =
      (Finset.univ.filter fun q => k + 1 < A.cr q).biUnion (fun q => S n t x A k q) ∪
        (Finset.univ.filter fun q => A.cr q ≤ k + 1).biUnion (fun q => A.sig (k + 1) q i) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rfl

lemma Om_succ (k : ℕ) (hk : 2 ≤ k) (i : P) :
    Om n t x A (k + 1) i =
      (Finset.univ.filter fun q => k + 1 < A.cr q).biUnion (fun q => Om n t x A k q) ∪
        (Finset.univ.filter fun q => A.cr q ≤ k + 1).biUnion (fun q => A.om (k + 1) q i) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  rfl

/-- An honest sender forwards its set `S^k` in round `k + 1`. -/
lemma mem_S_forward {k : ℕ} (hk : 1 ≤ k) {q : P} (hq : k + 1 < A.cr q) {v : D}
    (hv : v ∈ S n t x A k q) (i : P) : v ∈ S n t x A (k + 1) i := by
  rw [S_succ k hk]
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨q, by simp [hq], hv⟩)

/-- An honest sender forwards its set `Ω^k` in round `k + 1`. -/
lemma mem_Om_forward {k : ℕ} (hk : 2 ≤ k) {q : P} (hq : k + 1 < A.cr q) {v : D}
    (hv : v ∈ Om n t x A k q) (i : P) : v ∈ Om n t x A (k + 1) i := by
  rw [Om_succ k hk]
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨q, by simp [hq], hv⟩)

/-- The sets of a party that is honest up to round `k'` grow up to round `k'`. -/
lemma S_mono {i : P} {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k') (hi : k' < A.cr i) :
    S n t x A k i ⊆ S n t x A k' i := by
  induction k', hkk using Nat.le_induction with
  | base => exact le_rfl
  | succ k' hk' ih =>
    intro v hv
    exact mem_S_forward (by omega) hi (ih (by omega) hv) i

/-! ### Counting -/

/-- From `n - t ≤ |{q | a q ∨ b q}|` and `|{q | b q}| ≤ t < n - t` some `q` satisfies `a`. -/
lemma exists_of_card_or {a b : P → Prop} [DecidablePred a] [DecidablePred b]
    (h : n - t ≤ (Finset.univ.filter fun q => a q ∨ b q).card)
    (hb : (Finset.univ.filter fun q => b q).card ≤ t) (hnt : 2 * t < n) : ∃ q, a q := by
  by_contra hne
  push_neg at hne
  have : (Finset.univ.filter fun q => a q ∨ b q) ⊆ Finset.univ.filter fun q => b q := by
    intro q hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hq.resolve_left (hne q)
  have := Finset.card_le_card this
  omega

lemma card_cr_le_mono {r k : ℕ} (hk : k ≤ r) :
    (Finset.univ.filter fun q => A.cr q ≤ k).card ≤ (Finset.univ.filter fun q => A.cr q ≤ r).card :=
  Finset.card_le_card (fun q hq => by simp only [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, by omega⟩)

/-- Every certificate `Ω` in an `Ω^k` (`2 ≤ k ≤ r`) was backed by an honest share `ω`: some party
honest in round 2 with input `v` had `S¹ = {v}`. -/
lemma Om_signer {r : ℕ} (hv : Valid n t x A r) (hnt : 2 * t < n) {k : ℕ} (hk2 : 2 ≤ k)
    (hkr : k ≤ r) {i : P} {v : D} (hvk : v ∈ Om n t x A k i) :
    ∃ q, 2 < A.cr q ∧ SignsOm n t x A q ∧ x q = v := by
  induction k, hk2 using Nat.le_induction generalizing i with
  | base =>
    change v ∈ Om2 n t x A i at hvk
    unfold Om2 at hvk
    split_ifs at hvk with h
    · rw [Finset.mem_singleton] at hvk
      subst hvk
      exact exists_of_card_or h (le_trans (Finset.card_le_card (fun q hq => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq.1)
        |>.trans (card_cr_le_mono (A := A) (by omega))) hv.budget) hnt
    · simp at hvk
  | succ k hk ih =>
    rw [Om_succ k hk] at hvk
    rcases Finset.mem_union.1 hvk with h | h
    · obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 h
      exact ih (by omega) hq
    · obtain ⟨q, hq, hq'⟩ := Finset.mem_biUnion.1 h
      have hq := (Finset.mem_filter.1 hq).2
      have := hv.om_le (k + 1) q i (by omega) hq hq'
      simp only [consOm, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact exists_of_card_or this ((card_cr_le_mono (A := A) (by omega)).trans hv.budget) hnt

/-! ### The output -/

variable [LinearOrder D]

lemma outGrade_le (r : ℕ) (i : P) : outGrade n t x A r i ≤ r - 1 := Nat.findGreatest_le _

lemma le_outGrade {r : ℕ} {i : P} {j : ℕ} (h : GradeOk n t x A r i j) :
    j ≤ outGrade n t x A r i := Nat.le_findGreatest h.2.1 h

lemma out_snd (r : ℕ) (d₀ : D) (i : P) : (out n t x A r d₀ i).2 = outGrade n t x A r i := by
  unfold out
  split_ifs with h
  · rfl
  · by_contra hne
    have hpos : 0 < outGrade n t x A r i := by
      have : (0 : ℕ) ≠ outGrade n t x A r i := hne
      omega
    obtain ⟨j, hj⟩ : ∃ j, GradeOk n t x A r i j := by
      by_contra hn
      push_neg at hn
      have : outGrade n t x A r i = 0 :=
        Nat.findGreatest_eq_zero_iff.2 (fun k _ _ => hn k)
      omega
    exact h (Nat.findGreatest_spec (P := GradeOk n t x A r i) hj.2.1 hj)

lemma out_cond {r : ℕ} {d₀ : D} {i : P} (h : 1 ≤ (out n t x A r d₀ i).2) :
    OutCond n t x A r i (out n t x A r d₀ i).2 (out n t x A r d₀ i).1 := by
  unfold out at h ⊢
  split_ifs at h ⊢ with hg
  · dsimp only
    exact (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter
      fun z : D => OutCond n t x A r i (outGrade n t x A r i) z) _)).2
  · simp at h

/-! ### Lemma 3.6 (consistency)

We prove consistency in a slightly stronger *two-run* form: the runs of two adversaries `A`, `B`
with the same corruption times that produce the same sets `S^k`, `Ω^k` before the last round `r`
(e.g. two adversaries that agree up to round `r - 1`) give consistent outputs. With `A = B` this is
Lemma 3.6; the two-run form is what is needed when the coin is tossed in parallel to the last
round (`two_run_cons`). -/

section TwoRuns

variable {B : Adv P D} {r : ℕ}

/-- **Lemma 3.6, first part (two runs)**: the grades of parties honest at the end differ by at
most one. -/
lemma grade_ge2 (d₀ : D) (hcr : A.cr = B.cr)
    (hS : ∀ k < r, ∀ q, S n t x A k q = S n t x B k q)
    (hO : ∀ k < r, ∀ q, Om n t x A k q = Om n t x B k q)
    {i j : P} (hi : r < A.cr i) (hj : r < A.cr j) :
    (out n t x A r d₀ i).2 ≤ (out n t x B r d₀ j).2 + 1 := by
  by_contra hcon
  have hg : 2 ≤ (out n t x A r d₀ i).2 := by omega
  obtain ⟨h1, h2, h3⟩ := out_cond (show 1 ≤ (out n t x A r d₀ i).2 by omega)
  set g := (out n t x A r d₀ i).2 with hgdef
  set z := (out n t x A r d₀ i).1
  have hgr : g ≤ r - 1 := by rw [hgdef, out_snd]; exact outGrade_le r i
  have hok : GradeOk n t x B r j (g - 1) := by
    refine ⟨by omega, by omega, z, ?_, ?_, ?_⟩
    · rw [hS (r - g) (by omega) i] at h1
      have := mem_S_forward (A := B) (k := r - g) (by omega) (by rw [← hcr]; omega) h1 j
      rwa [show r - g + 1 = r - (g - 1) by omega] at this
    · rw [hO (r - g + 1) (by omega) i] at h2
      have := mem_Om_forward (A := B) (k := r - g + 1) (by omega) (by rw [← hcr]; omega) h2 j
      rwa [show r - g + 1 + 1 = r - (g - 1) + 1 by omega] at this
    · intro w hw
      rw [show g - 1 + 1 = g by omega, ← hS g (by omega) j] at hw
      exact h3 (mem_S_forward (k := g) (by omega) (by omega) hw i)
  have := le_outGrade hok
  rw [← out_snd r d₀ j] at this
  omega

/-- **Lemma 3.6, second part (two runs)**: parties honest at the end with positive grades agree on
the value. -/
lemma val_eq2 (hvA : Valid n t x A r) (hnt : 2 * t < n) (d₀ : D) (hcr : A.cr = B.cr)
    (hS : ∀ k < r, ∀ q, S n t x A k q = S n t x B k q)
    {i j : P} (hj : r < A.cr j) (hgi : 1 ≤ (out n t x A r d₀ i).2)
    (hgj : 1 ≤ (out n t x B r d₀ j).2) : (out n t x A r d₀ i).1 = (out n t x B r d₀ j).1 := by
  obtain ⟨-, h2, -⟩ := out_cond hgi
  obtain ⟨-, -, h3⟩ := out_cond hgj
  have hgr : (out n t x A r d₀ i).2 ≤ r - 1 := by rw [out_snd]; exact outGrade_le r i
  have hgr' : (out n t x B r d₀ j).2 ≤ r - 1 := by rw [out_snd]; exact outGrade_le r j
  obtain ⟨q, hq2, hqs, hqx⟩ := Om_signer hvA hnt (k := r - (out n t x A r d₀ i).2 + 1)
    (by omega) (by omega) h2
  have hS1 : (out n t x A r d₀ i).1 ∈ S n t x A 1 q := by
    change _ ∈ S1 n t x A q
    rw [hqs, ← hqx]; exact Finset.mem_singleton_self _
  rw [hS 1 (by omega) q] at hS1
  have hS2 := mem_S_forward (A := B) (k := 1) le_rfl (by rw [← hcr]; exact hq2) hS1 j
  have := h3 (S_mono (A := B) (i := j) (by omega) (by omega) (by rw [← hcr]; omega) hS2)
  exact Finset.mem_singleton.1 this

/-- Two runs as above give pairwise consistent outputs (`Prox_{2r-1}`) for parties honest at the
end (the same party in both runs included). -/
lemma two_run_cons (hr : 1 ≤ r) (hvA : Valid n t x A r) (hnt : 2 * t < n) (d₀ : D)
    (hcr : A.cr = B.cr) (hS : ∀ k < r, ∀ q, S n t x A k q = S n t x B k q)
    (hO : ∀ k < r, ∀ q, Om n t x A k q = Om n t x B k q)
    {i j : P} (hi : r < A.cr i) (hj : r < A.cr j) :
    ProxCons (2 * r - 1) (out n t x A r d₀ i) (out n t x B r d₀ j) := by
  refine ⟨grade_ge2 d₀ hcr hS hO hi hj, ?_, fun h1 h2 => val_eq2 hvA hnt d₀ hcr hS hj h1 h2,
    fun h => absurd h (by omega)⟩
  exact grade_ge2 (A := B) (B := A) d₀ hcr.symm (fun k hk q => (hS k hk q).symm)
    (fun k hk q => (hO k hk q).symm) (by rw [← hcr]; exact hj) (by rw [← hcr]; exact hi)

end TwoRuns

/-! ### Lemma 3.5 (validity) -/

lemma S1_sub {r : ℕ} (hr : 1 ≤ r) (hv : Valid n t x A r) (hnt : 2 * t < n) {v : D}
    (hx : ∀ q, r < A.cr q → x q = v) (i : P) : S n t x A 1 i ⊆ {v} := by
  intro w hw
  change w ∈ S1 n t x A i at hw
  simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  by_contra hne
  rw [Finset.mem_singleton] at hne
  have : (Finset.univ.filter fun q => (1 < A.cr q ∧ x q = w) ∨ (A.cr q ≤ 1 ∧ w ∈ A.sh1 q i)) ⊆
      Finset.univ.filter fun q => A.cr q ≤ r := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    by_contra hqr
    rcases hq with hq | hq
    · exact hne (hq.2 ▸ hx q (by omega))
    · omega
  have := (Finset.card_le_card this).trans hv.budget
  omega

lemma consSig_sub {r : ℕ} (hv : Valid n t x A r) (hnt : 2 * t < n) {v : D}
    (hx : ∀ q, r < A.cr q → x q = v) {k : ℕ} (hk : k ≤ r) : consSig n t x A k ⊆ {v} := by
  intro w hw
  simp only [consSig, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  by_contra hne
  rw [Finset.mem_singleton] at hne
  have : (Finset.univ.filter fun q => (1 < A.cr q ∧ x q = w) ∨ A.cr q ≤ k) ⊆
      Finset.univ.filter fun q => A.cr q ≤ r := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    by_contra hqr
    rcases hq with hq | hq
    · exact hne (hq.2 ▸ hx q (by omega))
    · omega
  have := (Finset.card_le_card this).trans hv.budget
  omega

lemma S_sub {r : ℕ} (hv : Valid n t x A r) (hnt : 2 * t < n) {v : D}
    (hx : ∀ q, r < A.cr q → x q = v) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ r) (i : P) :
    S n t x A k i ⊆ {v} := by
  induction k, hk1 using Nat.le_induction generalizing i with
  | base => exact S1_sub (by omega) hv hnt hx i
  | succ k hk' ih =>
    rw [S_succ k hk']
    refine Finset.union_subset (Finset.biUnion_subset.2 fun q _ => ih (by omega) q)
      (Finset.biUnion_subset.2 fun q hq => (hv.sig_le (k + 1) q i (by omega)
        (Finset.mem_filter.1 hq).2).trans (consSig_sub hv hnt hx hk))

lemma card_honest {r : ℕ} (hv : Valid n t x A r) (hn : Fintype.card P = n) :
    n - t ≤ (Finset.univ.filter fun q => r < A.cr q).card := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun q => A.cr q ≤ r)
  simp only [Finset.card_univ, not_le] at this
  have := hv.budget
  omega

/-- **Lemma 3.5 (validity).** If all parties honest at the end have input `v`, they all output
`(v, r - 1)` (the maximal grade of `Prox_{2r-1}`). -/
theorem half_validity {r : ℕ} (hr : 3 ≤ r) (hn : Fintype.card P = n) (hv : Valid n t x A r)
    (hnt : 2 * t < n) (d₀ : D) {v : D} (hx : ∀ q, r < A.cr q → x q = v) {i : P}
    (hi : r < A.cr i) : out n t x A r d₀ i = (v, r - 1) := by
  have hhon := card_honest hv hn
  -- every party has `S¹ = {v}`
  have hS1 : ∀ q, S1 n t x A q = {v} := by
    intro q
    apply Finset.Subset.antisymm (S1_sub (by omega) hv hnt hx q)
    rw [Finset.singleton_subset_iff]
    change v ∈ S1 n t x A q
    unfold S1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine le_trans hhon (Finset.card_le_card fun q' hq' => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq' ⊢
    exact Or.inl ⟨by omega, hx q' hq'⟩
  have hOm2 : v ∈ Om n t x A 2 i := by
    change v ∈ Om2 n t x A i
    unfold Om2
    rw [if_pos, hx i hi]
    · exact Finset.mem_singleton_self _
    · refine le_trans hhon (Finset.card_le_card fun q' hq' => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq' ⊢
      refine Or.inl ⟨by omega, ?_, by rw [hx q' hq', hx i hi]⟩
      unfold SignsOm; rw [hS1, hx q' hq']
  have hcond : OutCond n t x A r i (r - 1) v := by
    refine ⟨?_, ?_, ?_⟩
    · rw [show r - (r - 1) = 1 by omega]
      change v ∈ S1 n t x A i; rw [hS1]; exact Finset.mem_singleton_self _
    · rwa [show r - (r - 1) + 1 = 2 by omega]
    · rw [show r - 1 + 1 = r by omega]; exact S_sub hv hnt hx (by omega) le_rfl i
  have hok : GradeOk n t x A r i (r - 1) := ⟨by omega, le_rfl, v, hcond⟩
  have hg : (out n t x A r d₀ i).2 = r - 1 := by
    rw [out_snd]; exact le_antisymm (outGrade_le r i) (le_outGrade hok)
  refine Prod.ext ?_ hg
  have := out_cond (show 1 ≤ (out n t x A r d₀ i).2 by omega)
  rw [hg] at this
  have h1 := this.1
  rw [show r - (r - 1) = 1 by omega] at h1
  exact Finset.mem_singleton.1 (S1_sub (by omega) hv hnt hx i h1)

/-- **Lemma 3.4.** For `2t < n`, `r ≥ 3` and an adversary corrupting at most `t` parties, the
outputs of the parties honest at the end (`Hend = {q | r < A.cr q}`) form a `(2r-1)`-slot
Proxcensus. -/
theorem half_isProx {r : ℕ} (hr : 3 ≤ r) (hn : Fintype.card P = n) (hv : Valid n t x A r)
    (hnt : 2 * t < n) (d₀ : D) :
    IsProx (2 * r - 1) x {q | r < A.cr q} (out n t x A r d₀) := by
  have hG : maxGrade (2 * r - 1) = r - 1 := by unfold maxGrade; omega
  refine ⟨fun p _ => ?_, fun v hx p hp => ?_, fun p hp q hq => ?_⟩
  · rw [hG, out_snd]; exact outGrade_le r p
  · rw [hG]; exact half_validity hr hn hv hnt d₀ hx hp
  · exact two_run_cons (by omega) hv hnt d₀ rfl (fun _ _ _ => rfl) (fun _ _ _ => rfl) hp hq

end RoundEfficientBA.Half
