import Papers.PODC2021.RoundEfficientBA.Proxcensus

/-!
# The expansion step `Prox_s → Prox_{2s-1}` for `t < n/3` (Section 3.3.1, Lemmas 3.1, 3.2)

One round of the protocol `Prox_{2s-1}`: every party echoes its `Prox_s` output `(z, h)`, and
computes its new output from the multiset of echoes it received. This file treats the step
abstractly: a receiver is described by its counting function `cnt A` = the number of received
echoes satisfying the predicate `A`; for an honest receiver, `cnt A` lies between the number of
honest echoes satisfying `A` and that number plus `f` (the number of Byzantine parties).

## The output rule

We index the conditions of the paper's output determination by a *half-level* `m ∈ [b, 2G]`
(`s = 2k + b`, `G = ⌊(s-1)/2⌋`). On the *ray* of a value `z` the old slots are the levels
`L = 0, …, G` (`OnRay`; for odd `s`, level `0` is the common grade-0 slot of all values, which is the
paper's set `S₀`). Then
* odd `m = 2g+1`: `|S_{z,g} ∪ S_{z,g+1}| ≥ n-t ∧ |S_{z,g+1}| ≥ θ` (paper: grade `2g+2-b`; for odd
  `s` and `g = 0` this is line 7 of the protocol),
* even `m = 2g < 2G`: `|S_{z,g} ∪ S_{z,g+1}| ≥ n-t ∧ |S_{z,g}| ≥ θ` (paper: grade `2g+1-b`),
* `m = 2G`: `|S_{z,G}| ≥ n-t` (paper: line 17, grade `2G+1-b`),

and the new grade of condition `m` is `m + 1 - b`. The paper's loop overwrites the output with
every satisfied condition in increasing order of grade, so the output is the condition with the
largest `m` (`expandOut`). The paper uses the threshold `θ = n - 2t`.

## Results

* `expand_isProx` (**Lemmas 3.1 and 3.2, corrected**): with `θ = t + 1`, if the honest old outputs
  form an `s`-slot Proxcensus, the new outputs form a `(2s-1)`-slot Proxcensus, for every `n > 3t`.
* `expand_isProx_paper`: for `n = 3t + 1` the paper's threshold `n - 2t` equals `t + 1`, so the
  paper's protocol is correct in that case.
* `lemma32_counterexample`: for `n = 5`, `t = 1` (so `n > 3t + 1`) the paper's threshold
  `θ = n - 2t = 3` breaks consistency: from four honest `Prox_5` outputs `(0,1),(0,1),(0,2),(0,2)`
  two honest receivers obtain grades `3` and `0` in `Prox_9`.
-/

namespace RoundEfficientBA

variable {D : Type*}

/-! ### Definitions -/

/-- The echoed pair `e` lies on the ray of `z` at level `L`: it has grade `L`, and value `z` unless
`s` is odd and `L = 0` (the grade-0 slot of odd `s` is common to all values). -/
def onRay [DecidableEq D] (s : ℕ) (z : D) (L : ℕ) (e : D × ℕ) : Bool :=
  decide (e.2 = L ∧ (e.1 = z ∨ (s % 2 = 1 ∧ L = 0)))

/-- The echoed pair lies on the ray of `z` at level `L` or `L + 1`. -/
def onPair [DecidableEq D] (s : ℕ) (z : D) (L : ℕ) (e : D × ℕ) : Bool :=
  onRay s z L e || onRay s z (L + 1) e

/-- The condition with half-level `m` for value `z` (see the module docstring); `cnt A` is the
number of received echoes satisfying `A`, `θ` the "dominant slot" threshold (`n - 2t` in the
paper). -/
def Cond [DecidableEq D] (s n t θ : ℕ) (cnt : (D × ℕ → Bool) → ℕ) (z : D) (m : ℕ) : Prop :=
  if m % 2 = 1 then n - t ≤ cnt (onPair s z (m / 2)) ∧ θ ≤ cnt (onRay s z (m / 2 + 1))
  else if m / 2 = maxGrade s then n - t ≤ cnt (onRay s z (maxGrade s))
  else n - t ≤ cnt (onPair s z (m / 2)) ∧ θ ≤ cnt (onRay s z (m / 2))

instance [DecidableEq D] (s n t θ : ℕ) (cnt : (D × ℕ → Bool) → ℕ) (z : D) (m : ℕ) :
    Decidable (Cond s n t θ cnt z m) := by
  unfold Cond; infer_instance

/-- Condition `m` is a condition of the protocol and holds for some value. -/
def Fires [DecidableEq D] (s n t θ : ℕ) (cnt : (D × ℕ → Bool) → ℕ) (m : ℕ) : Prop :=
  s % 2 ≤ m ∧ m ≤ 2 * maxGrade s ∧ ∃ z, Cond s n t θ cnt z m

instance [Fintype D] [DecidableEq D] (s n t θ : ℕ) (cnt : (D × ℕ → Bool) → ℕ) :
    DecidablePred (Fires s n t θ cnt) := by
  intro m; unfold Fires; infer_instance

/-- The largest half-level whose condition holds (`0` if none). -/
def topLevel [Fintype D] [DecidableEq D] (s n t θ : ℕ) (cnt : (D × ℕ → Bool) → ℕ) : ℕ :=
  Nat.findGreatest (Fires s n t θ cnt) (2 * maxGrade s)

/-- The output of the expansion step (output determination of protocol `Prox_{2s-1}`): the value
and grade of the satisfied condition of largest grade; if several values satisfy it, the least one
(the paper leaves this choice open; for `n > 3t` the value is unique anyway). Without a satisfied
condition the grade is `0` and the value is the party's own old value (the paper uses the default
`0`; for grade `0` of an odd number of slots the value is irrelevant). -/
def expandOut [Fintype D] [LinearOrder D] (s n t θ : ℕ) (own : D × ℕ)
    (cnt : (D × ℕ → Bool) → ℕ) : D × ℕ :=
  if h : Fires s n t θ cnt (topLevel s n t θ cnt) then
    ((Finset.univ.filter fun z => Cond s n t θ cnt z (topLevel s n t θ cnt)).min'
        ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2.2.choose_spec⟩⟩,
      topLevel s n t θ cnt + 1 - s % 2)
  else (own.1, 0)

/-! ### Basic facts about `expandOut` -/

section Out

variable [Fintype D] [LinearOrder D] {s n t θ : ℕ} {cnt : (D × ℕ → Bool) → ℕ}

lemma expandOut_of_fires (own : D × ℕ) (h : ∃ m, Fires s n t θ cnt m) :
    Fires s n t θ cnt (topLevel s n t θ cnt) ∧
      (∀ m, Fires s n t θ cnt m → m ≤ topLevel s n t θ cnt) ∧
      Cond s n t θ cnt (expandOut s n t θ own cnt).1 (topLevel s n t θ cnt) ∧
      (expandOut s n t θ own cnt).2 = topLevel s n t θ cnt + 1 - s % 2 := by
  obtain ⟨m, hm⟩ := h
  have hspec : Fires s n t θ cnt (topLevel s n t θ cnt) :=
    Nat.findGreatest_spec (P := Fires s n t θ cnt) hm.2.1 hm
  have hle : ∀ m, Fires s n t θ cnt m → m ≤ topLevel s n t θ cnt :=
    fun m hm => Nat.le_findGreatest hm.2.1 hm
  refine ⟨hspec, hle, ?_, ?_⟩
  · unfold expandOut
    rw [dif_pos hspec]
    dsimp only
    exact (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter
      fun z : D => Cond s n t θ cnt z (topLevel s n t θ cnt)) _)).2
  · unfold expandOut
    rw [dif_pos hspec]

lemma expandOut_of_not_fires (own : D × ℕ) (h : ¬ ∃ m, Fires s n t θ cnt m) :
    expandOut s n t θ own cnt = (own.1, 0) := by
  unfold expandOut
  rw [dif_neg (fun h' => h ⟨_, h'⟩)]

end Out

/-! ### Honest counts -/

section Counting

variable {P : Type*}

/-- The number of honest parties (in `H`) whose old output satisfies `A`. -/
def hcnt (H : Finset P) (o : P → D × ℕ) (A : D × ℕ → Bool) : ℕ := (H.filter fun p => A (o p)).card

lemma hcnt_pos {H : Finset P} {o : P → D × ℕ} {A : D × ℕ → Bool} (h : 0 < hcnt H o A) :
    ∃ p ∈ H, A (o p) = true := by
  unfold hcnt at h
  obtain ⟨p, hp⟩ := Finset.card_pos.1 h
  exact ⟨p, (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2⟩

lemma hcnt_mono {H : Finset P} {o : P → D × ℕ} {A B : D × ℕ → Bool}
    (h : ∀ p ∈ H, A (o p) = true → B (o p) = true) : hcnt H o A ≤ hcnt H o B := by
  unfold hcnt
  exact Finset.card_le_card (fun p hp => by
    simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, h p hp.1 hp.2⟩)

lemma hcnt_all {H : Finset P} {o : P → D × ℕ} {A : D × ℕ → Bool}
    (h : ∀ p ∈ H, A (o p) = true) : hcnt H o A = H.card := by
  unfold hcnt
  rw [Finset.filter_true_of_mem h]

lemma hcnt_le_card (H : Finset P) (o : P → D × ℕ) (A : D × ℕ → Bool) : hcnt H o A ≤ H.card :=
  Finset.card_filter_le _ _

lemma hcnt_add_le {H : Finset P} {o : P → D × ℕ} {A B : D × ℕ → Bool}
    (h : ∀ p ∈ H, A (o p) = true → B (o p) = true → False) :
    hcnt H o A + hcnt H o B ≤ H.card := by
  classical
  unfold hcnt
  rw [← Finset.card_union_of_disjoint]
  · exact Finset.card_le_card (fun p hp => by
      simp only [Finset.mem_union, Finset.mem_filter] at hp; rcases hp with hp | hp <;> exact hp.1)
  · rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter] at hp hp'
    exact h p hp.1 hp.2 hp'.2

lemma hcnt_add_eq {H : Finset P} {o : P → D × ℕ} {A B : D × ℕ → Bool}
    (hdis : ∀ p ∈ H, A (o p) = true → B (o p) = true → False)
    (hcov : ∀ p ∈ H, A (o p) = true ∨ B (o p) = true) :
    hcnt H o A + hcnt H o B = H.card := by
  classical
  unfold hcnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hp; rcases hcov p hp with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
  · rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter] at hp hp'
    exact hdis p hp.1 hp.2 hp'.2

end Counting

/-! ### Structure of consistent honest outputs -/

section Structure

variable {P : Type*} [DecidableEq D]

lemma onRay_iff (s : ℕ) (z : D) (L : ℕ) (e : D × ℕ) :
    onRay s z L e = true ↔ e.2 = L ∧ (e.1 = z ∨ (s % 2 = 1 ∧ L = 0)) := by
  simp [onRay]

lemma onPair_iff (s : ℕ) (z : D) (L : ℕ) (e : D × ℕ) :
    onPair s z L e = true ↔ onRay s z L e = true ∨ onRay s z (L + 1) e = true := by
  simp [onPair]

/-- Pairwise consistent honest outputs either lie on one ray at two adjacent levels, or (even `s`
only) all have grade `0`. -/
lemma structure_of_cons {s : ℕ} {H : Finset P} {o : P → D × ℕ} (hne : H.Nonempty)
    (hc : ∀ p ∈ H, ∀ q ∈ H, ProxCons s (o p) (o q)) :
    (∃ z L, ∀ p ∈ H, onRay s z L (o p) = true ∨ onRay s z (L + 1) (o p) = true) ∨
      (s % 2 = 0 ∧ ∀ p ∈ H, (o p).2 = 0) := by
  by_cases hpos : ∃ p ∈ H, 1 ≤ (o p).2
  · obtain ⟨p1, hp1, hg1⟩ := hpos
    obtain ⟨pm, hpm, hmin⟩ := Finset.exists_min_image H (fun p => (o p).2) hne
    refine Or.inl ⟨(o p1).1, (o pm).2, fun q hq => ?_⟩
    have hmq := hmin q hq
    obtain ⟨h2, -, -, -⟩ := hc q hq pm hpm
    obtain ⟨-, -, h3, h4⟩ := hc p1 hp1 q hq
    simp only [onRay_iff]
    have hlev : (o q).2 = (o pm).2 ∨ (o q).2 = (o pm).2 + 1 := by omega
    by_cases hq1 : 1 ≤ (o q).2
    · have := h3 hg1 hq1
      rcases hlev with h | h
      · exact Or.inl ⟨h, Or.inl this.symm⟩
      · exact Or.inr ⟨h, Or.inl this.symm⟩
    · have hq0 : (o q).2 = 0 := by omega
      have hpm0 : (o pm).2 = 0 := by omega
      rcases Nat.mod_two_eq_zero_or_one s with hs | hs
      · exact Or.inl ⟨by omega, Or.inl (h4 hs (by omega)).symm⟩
      · exact Or.inl ⟨by omega, Or.inr ⟨hs, hpm0⟩⟩
  · push_neg at hpos
    rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · exact Or.inr ⟨hs, fun p hp => by have := hpos p hp; omega⟩
    · obtain ⟨p0, -⟩ := hne
      refine Or.inl ⟨(o p0).1, 0, fun q hq => Or.inl ?_⟩
      simp only [onRay_iff]
      exact ⟨by have := hpos q hq; omega, by simp [hs]⟩

end Structure

/-! ### General facts about the output -/

section OutFacts

variable [Fintype D] [LinearOrder D] {s n t θ : ℕ} {cnt : (D × ℕ → Bool) → ℕ}

lemma maxGrade_expand (hs : 1 ≤ s) : maxGrade (2 * s - 1) = 2 * maxGrade s + 1 - s % 2 := by
  unfold maxGrade; omega

lemma expandOut_grade_le (own : D × ℕ) :
    (expandOut s n t θ own cnt).2 ≤ 2 * maxGrade s + 1 - s % 2 := by
  by_cases h : ∃ m, Fires s n t θ cnt m
  · obtain ⟨hf, -, -, he⟩ := expandOut_of_fires own h
    rw [he]; have := hf.2.1; omega
  · rw [expandOut_of_not_fires own h]; exact Nat.zero_le _

lemma expandOut_eq_of_grade_zero (own : D × ℕ) (h0 : (expandOut s n t θ own cnt).2 = 0) :
    expandOut s n t θ own cnt = (own.1, 0) := by
  by_cases h : ∃ m, Fires s n t θ cnt m
  · obtain ⟨hf, -, -, he⟩ := expandOut_of_fires own h
    rw [he] at h0; have := hf.1; have := Nat.mod_two_eq_zero_or_one s; omega
  · exact expandOut_of_not_fires own h

end OutFacts

/-! ### One receiver, honest outputs on one ray -/

section Receiver

variable {P : Type*} [Fintype D] [LinearOrder D]
variable {s n t f : ℕ} {H : Finset P} {o : P → D × ℕ} {cnt : (D × ℕ → Bool) → ℕ}

/-- The number of Byzantine contributions is at most `f`. -/
lemma hcnt_ge_of_cnt (hhi : ∀ A, cnt A ≤ hcnt H o A + f) {A : D × ℕ → Bool} {k : ℕ}
    (h : k ≤ cnt A) : k ≤ hcnt H o A + f := le_trans h (hhi A)

omit [Fintype D] [LinearOrder D] in
lemma ray_lev [DecidableEq D] {z : D} {L : ℕ}
    (hray : ∀ p ∈ H, onRay s z L (o p) = true ∨ onRay s z (L + 1) (o p) = true) :
    ∀ p ∈ H, (o p).2 = L ∨ (o p).2 = L + 1 := by
  intro p hp
  rcases hray p hp with h | h <;> simp only [onRay_iff] at h
  · exact Or.inl h.1
  · exact Or.inr h.1

omit [Fintype D] [LinearOrder D] in
lemma ray_val [DecidableEq D] {z : D} {L : ℕ}
    (hray : ∀ p ∈ H, onRay s z L (o p) = true ∨ onRay s z (L + 1) (o p) = true) :
    ∀ p ∈ H, (1 ≤ (o p).2 ∨ s % 2 = 0) → (o p).1 = z := by
  intro p hp h1
  rcases hray p hp with h | h <;> simp only [onRay_iff] at h
  · rcases h.2 with h' | h'
    · exact h'
    · omega
  · rcases h.2 with h' | h'
    · exact h'
    · omega

/-- Upper bound: every satisfied condition is on the ray of `z`, at half-level at most `2L + 1`,
or `2L + 2` if at least `t + 1` honest outputs are on level `L + 1`. -/
lemma ray_upper (ht : 3 * t < n) (hf : f ≤ t)
    {z : D} {L : ℕ} (hray : ∀ p ∈ H, onRay s z L (o p) = true ∨ onRay s z (L + 1) (o p) = true)
    (hhi : ∀ A, cnt A ≤ hcnt H o A + f) {z' : D} {m : ℕ} (hb : s % 2 ≤ m) (hm : m ≤ 2 * maxGrade s)
    (hc : Cond s n t (t + 1) cnt z' m) :
    z' = z ∧ m ≤ (if t + 1 ≤ hcnt H o (onRay s z (L + 1)) then 2 * L + 1 else 2 * L) + 1 := by
  have hlev := ray_lev hray
  have hval := ray_val hray
  have hlt : f < t + 1 := by omega
  unfold Cond at hc
  split_ifs at hc with h1 h2
  · -- odd `m`
    have := hcnt_ge_of_cnt hhi hc.2
    obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z' (m / 2 + 1)) by omega)
    rw [onRay_iff] at hpA
    have hz' : (o p).1 = z' := by rcases hpA.2 with h | h; · exact h
                                  · omega
    have hz : (o p).1 = z := hval p hp (Or.inl (by omega))
    refine ⟨hz'.symm.trans hz, ?_⟩
    have := hlev p hp
    split_ifs <;> omega
  · -- `m = 2G`
    have := hcnt_ge_of_cnt hhi hc
    obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z' (maxGrade s)) by omega)
    rw [onRay_iff] at hpA
    have hz' : (o p).1 = z' := by
      rcases hpA.2 with h | h
      · exact h
      · omega
    have hz : (o p).1 = z := hval p hp (by omega)
    have hzz : z' = z := hz'.symm.trans hz
    refine ⟨hzz, ?_⟩
    subst hzz
    have := hlev p hp
    split_ifs with hc'
    · omega
    · -- `G = L + 1` would give `t + 1` honest outputs on level `L + 1`
      by_contra hcon
      have hGL : maxGrade s = L + 1 := by omega
      have h5 := hcnt_ge_of_cnt hhi hc
      rw [hGL] at h5
      omega
  · -- even `m < 2G`
    have h3 := hcnt_ge_of_cnt hhi hc.2
    obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z' (m / 2)) by omega)
    rw [onRay_iff] at hpA
    have hz' : (o p).1 = z' := by
      rcases hpA.2 with h | h
      · exact h
      · omega
    have hz : (o p).1 = z := hval p hp (by omega)
    have hzz : z' = z := hz'.symm.trans hz
    refine ⟨hzz, ?_⟩
    subst hzz
    have := hlev p hp
    split_ifs with hc'
    · omega
    · by_contra hcon
      have hm2 : m / 2 = L + 1 := by omega
      have h4 := hcnt_ge_of_cnt hhi hc.1
      rw [hm2] at h4
      have h5 : hcnt H o (onPair s z' (L + 1)) ≤ hcnt H o (onRay s z' (L + 1)) := by
        apply hcnt_mono
        intro q hq hA
        rw [onPair_iff, onRay_iff, onRay_iff] at hA
        rw [onRay_iff]
        have := hlev q hq
        rcases hA with h | h
        · exact h
        · omega
      omega

/-- Lower bound: the condition with half-level `2L + 1` (if at least `t + 1` honest outputs are on
level `L + 1`) or `2L` (otherwise) holds. -/
lemma ray_lower (ht : 3 * t < n) (hf : f ≤ t) (hHn : H.card + f = n)
    (hG : ∀ p ∈ H, (o p).2 ≤ maxGrade s)
    {z : D} {L : ℕ} (hray : ∀ p ∈ H, onRay s z L (o p) = true ∨ onRay s z (L + 1) (o p) = true)
    (hlo : ∀ A, hcnt H o A ≤ cnt A) (hb : s % 2 ≤ (if t + 1 ≤ hcnt H o (onRay s z (L + 1)) then 2 * L + 1 else 2 * L)) :
    Fires s n t (t + 1) cnt
      (if t + 1 ≤ hcnt H o (onRay s z (L + 1)) then 2 * L + 1 else 2 * L) := by
  have hlev := ray_lev hray
  have hsum : hcnt H o (onRay s z L) + hcnt H o (onRay s z (L + 1)) = H.card := by
    apply hcnt_add_eq
    · intro p _ h1 h2; rw [onRay_iff] at h1 h2; omega
    · exact hray
  have hall : hcnt H o (onPair s z L) = H.card :=
    hcnt_all (fun p hp => by rw [onPair_iff]; exact hray p hp)
  have hpair := hlo (onPair s z L)
  split_ifs at hb ⊢ with hc
  · refine ⟨hb, ?_, z, ?_⟩
    · obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z (L + 1)) by omega)
      rw [onRay_iff] at hpA
      have := hG p hp
      omega
    · unfold Cond
      have e1 : (2 * L + 1) % 2 = 1 := by omega
      have e2 : (2 * L + 1) / 2 = L := by omega
      rw [if_pos e1, e2]
      exact ⟨by omega, le_trans hc (hlo _)⟩
  · have ha : t + 1 ≤ hcnt H o (onRay s z L) := by omega
    obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z L) by omega)
    rw [onRay_iff] at hpA
    have hLG : L ≤ maxGrade s := by have := hG p hp; omega
    refine ⟨hb, by omega, z, ?_⟩
    unfold Cond
    have e1 : ¬ (2 * L) % 2 = 1 := by omega
    have e2 : (2 * L) / 2 = L := by omega
    rw [if_neg e1, e2]
    split_ifs with hLG'
    · -- `L = G`: nobody is on level `G + 1`
      have hc0 : hcnt H o (onRay s z (L + 1)) = 0 := by
        unfold hcnt
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro q hq hA
        rw [onRay_iff] at hA
        have := hG q hq
        omega
      rw [← hLG']
      have := hlo (onRay s z L)
      omega
    · exact ⟨by omega, le_trans ha (hlo _)⟩

/-- Summary for one receiver: with `M` as in `ray_lower`, the grade lies in
`[M + 1 - b, M + 2 - b]`, and a positive grade comes with the value `z`. -/
lemma ray_receiver (ht : 3 * t < n) (hf : f ≤ t) (hHn : H.card + f = n)
    (hG : ∀ p ∈ H, (o p).2 ≤ maxGrade s)
    {z : D} {L : ℕ} (hray : ∀ p ∈ H, onRay s z L (o p) = true ∨ onRay s z (L + 1) (o p) = true)
    (hlo : ∀ A, hcnt H o A ≤ cnt A) (hhi : ∀ A, cnt A ≤ hcnt H o A + f) (own : D × ℕ) :
    (if t + 1 ≤ hcnt H o (onRay s z (L + 1)) then 2 * L + 1 else 2 * L) + 1 - s % 2 ≤
        (expandOut s n t (t + 1) own cnt).2 ∧
      (expandOut s n t (t + 1) own cnt).2 ≤
        (if t + 1 ≤ hcnt H o (onRay s z (L + 1)) then 2 * L + 1 else 2 * L) + 2 - s % 2 ∧
      (1 ≤ (expandOut s n t (t + 1) own cnt).2 → (expandOut s n t (t + 1) own cnt).1 = z) := by
  have hlow := fun hb => ray_lower (cnt := cnt) ht hf hHn hG hray hlo hb
  have hup := fun {z' : D} {m : ℕ} => ray_upper (cnt := cnt) (z' := z') (m := m) ht hf hray hhi
  set M := (if t + 1 ≤ hcnt H o (onRay s z (L + 1)) then 2 * L + 1 else 2 * L) with hM
  have hb := Nat.mod_two_eq_zero_or_one s
  by_cases hfire : ∃ m, Fires s n t (t + 1) cnt m
  · obtain ⟨hf', hmax, hcond, he⟩ := expandOut_of_fires (s := s) (n := n) (t := t) (θ := t + 1)
      own hfire
    obtain ⟨hz, hle⟩ := hup hf'.1 hf'.2.1 hcond
    refine ⟨?_, ?_, fun _ => hz⟩
    · rw [he]
      by_cases hbm : s % 2 ≤ M
      · have := hmax _ (hlow hbm)
        omega
      · omega
    · rw [he]; omega
  · have he := expandOut_of_not_fires (s := s) (n := n) (t := t) (θ := t + 1) own hfire
    rw [he]
    refine ⟨?_, Nat.zero_le _, fun h => absurd h (by simp)⟩
    by_contra hcon
    exact hfire ⟨_, hlow (by simp only at hcon; omega)⟩

end Receiver

/-! ### One receiver, all honest outputs of grade 0 (even `s`) -/

section Zero

variable {P : Type*} [Fintype D] [LinearOrder D]
variable {s n t f : ℕ} {H : Finset P} {o : P → D × ℕ} {cnt : (D × ℕ → Bool) → ℕ}

lemma zero_receiver (ht : 3 * t < n) (hf : f ≤ t) (hHn : H.card + f = n)
    (hs0 : s % 2 = 0) (h0 : ∀ p ∈ H, (o p).2 = 0)
    (hhi : ∀ A, cnt A ≤ hcnt H o A + f) (own : D × ℕ) :
    (expandOut s n t (t + 1) own cnt).2 ≤ 1 ∧
      ((expandOut s n t (t + 1) own cnt).2 = 1 →
        n - t ≤ hcnt H o (onPair s (expandOut s n t (t + 1) own cnt).1 0) + f) := by
  by_cases hfire : ∃ m, Fires s n t (t + 1) cnt m
  · obtain ⟨hf', -, hcond, he⟩ := expandOut_of_fires (s := s) (n := n) (t := t) (θ := t + 1)
      own hfire
    set m := topLevel s n t (t + 1) cnt
    set z' := (expandOut s n t (t + 1) own cnt).1
    -- the top level is `0`
    have hm0 : m = 0 ∧ n - t ≤ hcnt H o (onPair s z' 0) + f := by
      unfold Cond at hcond
      split_ifs at hcond with h1 h2
      · have := hcnt_ge_of_cnt hhi hcond.2
        obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z' (m / 2 + 1)) by omega)
        rw [onRay_iff] at hpA
        have := h0 p hp
        omega
      · have := hcnt_ge_of_cnt hhi hcond
        obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z' (maxGrade s)) by omega)
        rw [onRay_iff] at hpA
        have hp0 := h0 p hp
        have hm : m = 0 := by omega
        refine ⟨hm, le_trans this (Nat.add_le_add_right (hcnt_mono fun q _ hA => ?_) _)⟩
        rw [onPair_iff]; left; rw [← show maxGrade s = 0 by omega]; exact hA
      · have := hcnt_ge_of_cnt hhi hcond.2
        obtain ⟨p, hp, hpA⟩ := hcnt_pos (show 0 < hcnt H o (onRay s z' (m / 2)) by omega)
        rw [onRay_iff] at hpA
        have := h0 p hp
        have hm : m = 0 := by omega
        refine ⟨hm, ?_⟩
        have := hcnt_ge_of_cnt hhi hcond.1
        rw [show m / 2 = 0 by omega] at this
        exact this
    rw [he, hm0.1, hs0]
    exact ⟨le_refl _, fun _ => hm0.2⟩
  · rw [expandOut_of_not_fires own hfire]
    exact ⟨Nat.zero_le _, fun h => absurd h (by simp)⟩

end Zero

/-! ### Lemmas 3.1 and 3.2 -/

section Main

variable {P : Type*} [Fintype D] [LinearOrder D]

/-- **Lemmas 3.1 and 3.2 (corrected threshold).** Let `n > 3t`, let the honest parties `H`
(`|H| + f = n`, `f ≤ t` Byzantine parties) hold outputs `o` of an `s`-slot Proxcensus
(`s ≥ 1`), and let every honest receiver `p` count the received echoes with `cnt p`, which sees
every honest echo and at most `f` further ones. Then the outputs of the expansion step with
threshold `θ = t + 1` form a `(2s-1)`-slot Proxcensus (validity and consistency). -/
theorem expand_isProx {s n t f : ℕ} (hs : 1 ≤ s) (ht : 3 * t < n) (hf : f ≤ t)
    {x : P → D} {H : Finset P} (hHn : H.card + f = n) {o : P → D × ℕ}
    (ho : IsProx s x (H : Set P) o) (cnt : P → (D × ℕ → Bool) → ℕ)
    (hlo : ∀ p ∈ H, ∀ A, hcnt H o A ≤ cnt p A) (hhi : ∀ p ∈ H, ∀ A, cnt p A ≤ hcnt H o A + f) :
    IsProx (2 * s - 1) x (H : Set P) (fun p => expandOut s n t (t + 1) (o p) (cnt p)) := by
  have hG : ∀ p ∈ H, (o p).2 ≤ maxGrade s := fun p hp => ho.grade_le p hp
  have hne : H.Nonempty := Finset.card_pos.1 (by omega)
  have hodd : ¬ (2 * s - 1) % 2 = 0 := by omega
  refine ⟨fun p _ => ?_, fun v hv p hp => ?_, fun p hp q hq => ?_⟩
  · rw [maxGrade_expand hs]; exact expandOut_grade_le _
  · -- validity
    have hov : ∀ q ∈ H, o q = (v, maxGrade s) := fun q hq => ho.validity v hv q hq
    have hray : ∀ q ∈ H, onRay s v (maxGrade s) (o q) = true ∨
        onRay s v (maxGrade s + 1) (o q) = true := by
      intro q hq; left; rw [hov q hq, onRay_iff]; exact ⟨rfl, Or.inl rfl⟩
    have hc0 : hcnt H o (onRay s v (maxGrade s + 1)) = 0 := by
      unfold hcnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q hq hA; rw [hov q hq, onRay_iff] at hA; simp at hA
    obtain ⟨h1, -, h3⟩ := ray_receiver ht hf hHn hG hray (hlo p hp) (hhi p hp) (o p)
    have h2 := expandOut_grade_le (s := s) (n := n) (t := t) (θ := t + 1) (cnt := cnt p) (o p)
    simp only [hc0] at h1
    have hgr : (expandOut s n t (t + 1) (o p) (cnt p)).2 = 2 * maxGrade s + 1 - s % 2 := by
      split_ifs at h1 <;> omega
    rw [maxGrade_expand hs]
    by_cases hpos : 1 ≤ (expandOut s n t (t + 1) (o p) (cnt p)).2
    · exact Prod.ext (h3 hpos) hgr
    · have h0 : (expandOut s n t (t + 1) (o p) (cnt p)).2 = 0 := by omega
      rw [expandOut_eq_of_grade_zero _ h0, hov p hp] at *
      exact Prod.ext rfl (by simp only; omega)
  · -- consistency
    refine ⟨?_, ?_, ?_, fun h => absurd h hodd⟩
    all_goals
      rcases structure_of_cons hne ho.consistency with ⟨z, L, hray⟩ | ⟨hs0, h0⟩
      · obtain ⟨a1, a2, a3⟩ := ray_receiver ht hf hHn hG hray (hlo p hp) (hhi p hp) (o p)
        obtain ⟨b1, b2, b3⟩ := ray_receiver ht hf hHn hG hray (hlo q hq) (hhi q hq) (o q)
        first
        | (split_ifs at a1 a2 b1 b2 <;> omega)
        | (intro h1 h2; rw [a3 h1, b3 h2])
      · obtain ⟨a1, a2⟩ := zero_receiver ht hf hHn hs0 h0 (hhi p hp) (o p)
        obtain ⟨b1, b2⟩ := zero_receiver ht hf hHn hs0 h0 (hhi q hq) (o q)
        first
        | omega
        | (intro h1 h2
           by_contra hne'
           have e1 := a2 (by omega)
           have e2 := b2 (by omega)
           have := hcnt_add_le (H := H) (o := o)
             (A := onPair s (expandOut s n t (t + 1) (o p) (cnt p)).1 0)
             (B := onPair s (expandOut s n t (t + 1) (o q) (cnt q)).1 0) (by
               intro r _ hA hB
               rw [onPair_iff, onRay_iff, onRay_iff] at hA hB
               apply hne'
               rcases hA with hA | hA <;> rcases hB with hB | hB <;>
                 · rcases hA.2 with hA' | hA' <;> rcases hB.2 with hB' | hB' <;>
                     first | exact hA'.symm.trans hB' | omega)
           omega)

/-- For `n = 3t + 1` the paper's threshold `n - 2t` is `t + 1`: **Lemmas 3.1 and 3.2** hold for
the protocol exactly as written. -/
theorem expand_isProx_paper {s t f : ℕ} (hs : 1 ≤ s) (hf : f ≤ t)
    {x : P → D} {H : Finset P} (hHn : H.card + f = 3 * t + 1) {o : P → D × ℕ}
    (ho : IsProx s x (H : Set P) o) (cnt : P → (D × ℕ → Bool) → ℕ)
    (hlo : ∀ p ∈ H, ∀ A, hcnt H o A ≤ cnt p A) (hhi : ∀ p ∈ H, ∀ A, cnt p A ≤ hcnt H o A + f) :
    IsProx (2 * s - 1) x (H : Set P)
      (fun p => expandOut s (3 * t + 1) t (3 * t + 1 - 2 * t) (o p) (cnt p)) := by
  have : 3 * t + 1 - 2 * t = t + 1 := by omega
  rw [this]
  exact expand_isProx hs (by omega) hf hHn ho cnt hlo hhi

end Main

end RoundEfficientBA

namespace RoundEfficientBA

/-! ### Counting received echoes -/

section View

variable {P D : Type*} [Fintype P] [DecidableEq P]

/-- The number of received echoes (`view q` = what was received from `q`) satisfying `A`. -/
def viewCnt (view : P → Option (D × ℕ)) (A : D × ℕ → Bool) : ℕ :=
  (Finset.univ.filter fun q => (view q).any A).card

/-- A receiver that gets the honest echoes right sees between `hcnt` and `hcnt + (n - |H|)`
echoes satisfying any predicate. -/
lemma viewCnt_bounds {H : Finset P} {o : P → D × ℕ} {view : P → Option (D × ℕ)}
    (hv : ∀ q ∈ H, view q = some (o q)) (A : D × ℕ → Bool) :
    hcnt H o A ≤ viewCnt view A ∧ viewCnt view A ≤ hcnt H o A + (Finset.univ \ H).card := by
  unfold hcnt viewCnt
  constructor
  · apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [hv q hq.1]; simpa using hq.2
  · calc (Finset.univ.filter fun q => (view q).any A).card
        ≤ ((H.filter fun p => A (o p)) ∪ (Finset.univ \ H)).card := by
          apply Finset.card_le_card
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_sdiff] at hq ⊢
          by_cases hqH : q ∈ H
          · left; rw [hv q hqH] at hq; simpa [hqH] using hq
          · right; exact hqH
      _ ≤ _ := Finset.card_union_le _ _

end View

/-! ### Counterexample to Lemma 3.2 with the paper's threshold `n - 2t` (`n = 5`, `t = 1`) -/

section Counterexample

/-- Honest `Prox_5` outputs `(0,1), (0,1), (0,2), (0,2)` of parties `0, …, 3`; party `4` is
Byzantine. -/
def cexOld : Fin 5 → Bool × ℕ := ![(false, 1), (false, 1), (false, 2), (false, 2), (false, 0)]

/-- Mixed inputs (so validity of `Prox_5` is vacuous). -/
def cexInput : Fin 5 → Bool := ![false, false, false, true, false]

def cexH : Finset (Fin 5) := {0, 1, 2, 3}

/-- Party `0` receives the Byzantine echo `(0, 2)`; the others receive nothing from party `4`. -/
def cexView (p : Fin 5) : Fin 5 → Option (Bool × ℕ) :=
  fun q => if q = 4 then (if p = 0 then some (false, 2) else none) else some (cexOld q)

lemma cex_isProx5 : IsProx 5 cexInput (cexH : Set (Fin 5)) cexOld := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp; simp only [cexH, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl | rfl | rfl <;> decide
  · intro v hv
    have h0 := hv 0 (by simp [cexH]); have h3 := hv 3 (by simp [cexH])
    simp [cexInput] at h0 h3; exact absurd (h0.symm.trans h3) (by decide)
  · intro p hp q hq
    simp only [cexH, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> decide

lemma cex_view (p : Fin 5) : ∀ q ∈ cexH, cexView p q = some (cexOld q) := by
  intro q hq; simp [cexH] at hq; rcases hq with rfl | rfl | rfl | rfl <;> rfl

lemma cex_out0 : (expandOut 5 5 1 (5 - 2 * 1) (cexOld 0) (viewCnt (cexView 0))).2 = 3 := by
  decide

lemma cex_out1 : (expandOut 5 5 1 (5 - 2 * 1) (cexOld 1) (viewCnt (cexView 1))).2 = 0 := by
  decide

/-- **Lemma 3.2 is false for `n > 3t + 1`** with the paper's threshold `n - 2t`: for `n = 5`, `t = 1`
(one Byzantine party), honest `Prox_5` outputs satisfying Definition 2.2, and honest receivers
that see all honest echoes (plus one Byzantine echo or none), the outputs of the expansion step
have grades `3` and `0`, violating `|gᵢ - gⱼ| ≤ 1` of `Prox_9`. All hypotheses of
`expand_isProx` hold except that the threshold is `n - 2t = 3` instead of `t + 1 = 2`. -/
theorem lemma32_counterexample :
    IsProx 5 cexInput (cexH : Set (Fin 5)) cexOld ∧
      cexH.card + 1 = 5 ∧
      (∀ p ∈ cexH, ∀ A, hcnt cexH cexOld A ≤ viewCnt (cexView p) A ∧
        viewCnt (cexView p) A ≤ hcnt cexH cexOld A + 1) ∧
      ¬ IsProx (2 * 5 - 1) cexInput (cexH : Set (Fin 5))
        (fun p => expandOut 5 5 1 (5 - 2 * 1) (cexOld p) (viewCnt (cexView p))) := by
  refine ⟨cex_isProx5, by decide, fun p _ A => ?_, fun h => ?_⟩
  · have := viewCnt_bounds (cex_view p) A
    have hc : (Finset.univ \ cexH).card = 1 := by decide
    rw [hc] at this; exact this
  · have := (h.consistency 0 (by simp [cexH]) 1 (by simp [cexH])).1
    simp only [cex_out0, cex_out1] at this
    omega

end Counterexample

end RoundEfficientBA
