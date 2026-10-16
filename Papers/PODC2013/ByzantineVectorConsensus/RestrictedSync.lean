import Papers.PODC2013.ByzantineVectorConsensus.Iterative

/-!
# Restricted synchronous round structure (Section 4, Theorem 6, synchronous case)

Section 4 of the paper considers algorithms with a *restricted round structure*. In the synchronous
case, in round `t + 1` every process

1. transmits its current vector state `v_i[t]` to all processes and receives a vector from every
   process (a missing message is replaced by a default value), and
2. computes `v_i[t+1]` as a function of `v_i[t]` and the received vectors.

`RestrictedAlg P d` is exactly this class (the update may depend on the round number and on the
process), `SyncExec` the adversary's choices (faulty set, inputs, and the vector each faulty
process sends to each process in each round), and `RestrictedAlg.Solves f T ε K` says that after
`T` rounds the states of the correct processes are valid and pairwise `ε`-close, in every
execution with at most `f` faults and correct inputs in `K`.

* `theorem_6_sync_restricted`: the Section 4 algorithm (Step 2 of Section 3.2 with `B_i = P`) is a
  restricted algorithm solving approximate BVC when `n ≥ (d + 2) f + 1` (sufficiency in
  Theorem 6).
* `theorem_6_sync_necessity_false`: **the necessity claim of Theorem 6 (synchronous case) is false
  as stated.** Nothing restricts the update function, and a single vector of reals can encode any
  amount of real data (`(Fin 4 → ℝ²) ↪ ℝ²`). So the state can carry a full-information history:
  for `n = 4`, `d = 2`, `f = 1` (where `(d + 2) f + 1 = 5 > n`) the restricted algorithm
  "round 1: store the received vector of inputs; round 2: for each `k`, take the majority of the
  values for `k` relayed by the three other processes (OM(1) of Lamport–Shostak–Pease), then
  output the chosen point of `Γ`" solves even *exact* BVC in 2 rounds.
  `theorem_6_sync_necessity_false'` is a variant whose update ignores the round number (inputs in
  `[0, 1]²`, encodings outside it, so the own state tells the rounds apart). Letting `upd` depend on
  the round number is harmless anyway: synchronous processes know it.
  The claim presumably needs an extra restriction (e.g. the new state must lie in the convex hull
  of the received states, as in iterative algorithms à la [Vaidya, Tseng, Liang 2012]), which the
  paper does not state and under which we have not formalized anything.
-/

open Finset Module Cardinal

namespace ByzantineVectorConsensus

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P] {d : ℕ}

/-- A restricted synchronous algorithm (Section 4): `upd t i v r` is the new state of process
`i` after round `t + 1` with old state `v` and received vectors `r`. -/
structure RestrictedAlg (P : Type*) (d : ℕ) where
  upd : ℕ → P → Vec d → (P → Vec d) → Vec d

/-- The adversary's choices in a synchronous execution of a restricted algorithm. -/
structure SyncExec (P : Type*) (d : ℕ) where
  faulty : Finset P
  inp : P → Vec d
  /-- `byz t i k`: the vector that `i` receives in round `t + 1` from the faulty process `k`. -/
  byz : ℕ → P → P → Vec d

namespace RestrictedAlg

variable (A : RestrictedAlg P d) (E : SyncExec P d)

/-- The states of all processes after `t` rounds (meaningful for correct ones). -/
def state : ℕ → P → Vec d
  | 0 => E.inp
  | t + 1 => fun i => A.upd t i (state t i) (fun k => if k ∈ E.faulty then E.byz t i k else state t k)

/-- `A` solves approximate BVC (agreement up to `ε` in every coordinate, validity) after `T`
rounds, with at most `f` faults and correct inputs in `K`. -/
def Solves (f T : ℕ) (ε : ℝ) (K : Set (Vec d)) : Prop :=
  ∀ E : SyncExec P d, E.faulty.card ≤ f → (∀ k ∉ E.faulty, E.inp k ∈ K) →
    ∀ i ∉ E.faulty, ∀ j ∉ E.faulty,
      A.state E T i ∈ convexHull ℝ (E.inp '' {k | k ∉ E.faulty}) ∧
      ∀ l, |A.state E T i l - A.state E T j l| ≤ ε

end RestrictedAlg

/-! ### Sufficiency -/

/-- The Section 4 synchronous algorithm: Step 2 of Section 3.2 applied to all received vectors. -/
noncomputable def iterAlg (P : Type*) [DecidableEq P] [Fintype P] (d f s : ℕ) :
    RestrictedAlg P d :=
  ⟨fun _ _ _ r => RoundExec.update f s univ r⟩

/-- The `RoundExec` of a synchronous execution (`B_i = P`). -/
def SyncExec.toRoundExec (E : SyncExec P d) : RoundExec P d :=
  ⟨E.faulty, E.inp, fun _ _ => univ, E.byz⟩

theorem iterAlg_state (f s : ℕ) (E : SyncExec P d) (t : ℕ) :
    (iterAlg P d f s).state E t = E.toRoundExec.state f s t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext i
    simp only [RestrictedAlg.state, RoundExec.state, ih]
    rfl

/-- **Theorem 6 (synchronous case), sufficiency**, in the restricted model: for
`n ≥ (d + 2) f + 1` and inputs in `[ν, U]^d`, the Section 4 algorithm solves approximate BVC
(with strict `< ε` agreement) after `rounds n (n - f) ν U ε` rounds. -/
theorem theorem_6_sync_restricted {f : ℕ} (hn : (d + 2) * f < Fintype.card P) {ν U ε : ℝ}
    (hε : 0 < ε) :
    (iterAlg P d f (Fintype.card P - f)).Solves f
      (RoundExec.rounds (Fintype.card P) (Fintype.card P - f) ν U ε) ε
      {v | ∀ l, ν ≤ v l ∧ v l ≤ U} := by
  intro E hf hK i hi j hj
  have := theorem_6_sync (E := E.toRoundExec) hn (fun _ _ => rfl) hf hε hK i hi j hj
  rw [iterAlg_state]
  refine ⟨?_, fun l => (this.2 l).le⟩
  have hset : ({k | k ∉ E.faulty} : Set P) = ↑E.toRoundExec.correct := by
    ext k; simp [RoundExec.mem_correct, SyncExec.toRoundExec]
  rw [hset]; exact this.1

/-! ### The necessity claim is false: a 2-round restricted algorithm for `n = 4`, `d = 2`,
`f = 1` -/

/-- `(Fin 4 → ℝ²)` injects into `ℝ²` (both have the cardinality of the continuum). -/
theorem exists_enc : Nonempty ((Fin 4 → Vec 2) ↪ Vec 2) := by
  have h0 : ∀ n : ℕ, n ≠ 0 → 𝔠 ^ (n : Cardinal) = 𝔠 := fun n hn => by
    rw [Cardinal.power_natCast]
    exact Cardinal.power_nat_eq Cardinal.aleph0_le_continuum (Nat.one_le_iff_ne_zero.2 hn)
  have h1 : #(Fin 4 → Fin 2 → ℝ) = 𝔠 := by
    simp only [Cardinal.mk_pi, Cardinal.mk_real, Cardinal.prod_const, Cardinal.mk_fin,
      Cardinal.lift_id]
    rw [h0 2 (by norm_num), h0 4 (by norm_num)]
  have h2 : #(Fin 2 → ℝ) = 𝔠 := by
    simp only [Cardinal.mk_pi, Cardinal.mk_real, Cardinal.prod_const, Cardinal.mk_fin,
      Cardinal.lift_id]
    exact h0 2 (by norm_num)
  rw [← Cardinal.le_def, h1, h2]

/-- An injective encoding of a vector of four points into `ℝ²`. -/
noncomputable def enc₀ : (Fin 4 → Vec 2) ↪ Vec 2 := Classical.choice exists_enc

/-- The encoding used by the algorithms; its first coordinate is `> 1`, so encodings are never
inputs from the box `[0, 1]²` (used by the round-independent variant). -/
noncomputable def enc (w : Fin 4 → Vec 2) : Vec 2 := ![Real.exp (enc₀ w 0) + 1, enc₀ w 1]

/-- Its left inverse. -/
noncomputable def dec (u : Vec 2) : Fin 4 → Vec 2 :=
  Function.invFun enc₀ ![Real.log (u 0 - 1), u 1]

theorem dec_enc (w : Fin 4 → Vec 2) : dec (enc w) = w := by
  have : (![Real.log (enc w 0 - 1), enc w 1] : Vec 2) = enc₀ w := by
    ext i; fin_cases i <;> simp [enc]
  simp only [dec]; rw [this]
  exact Function.leftInverse_invFun enc₀.injective w

theorem one_lt_enc (w : Fin 4 → Vec 2) : 1 < enc w 0 := by
  simp [enc, Real.exp_pos]

/-- Majority of three values (the first one if it agrees with another one, else the second). -/
noncomputable def maj3 (a b c : Vec 2) : Vec 2 := by
  classical
  exact if a = b ∨ a = c then a else b

theorem maj3_eq {a b c x : Vec 2} (h : (a = x ∧ b = x) ∨ (a = x ∧ c = x) ∨ (b = x ∧ c = x)) :
    maj3 a b c = x := by
  classical
  unfold maj3
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- OM(1)-style vote for the input of `k`: the majority of the values relayed by the three other
processes. -/
noncomputable def vote (r : Fin 4 → Vec 2) (k : Fin 4) : Vec 2 :=
  maj3 (dec (r (k + 1)) k) (dec (r (k + 2)) k) (dec (r (k + 3)) k)

/-- The full-information restricted algorithm: round 1 stores the received inputs, round 2 votes
and outputs the chosen point of `Γ` (`f = 1`); later rounds keep the state. -/
noncomputable def fullInfoAlg : RestrictedAlg (Fin 4) 2 :=
  ⟨fun t _ v r => if t = 0 then enc r else if t = 1 then gammaPt 1 univ (vote r) else v⟩

theorem fin4_others (k j : Fin 4) (h : j ≠ k) : j = k + 1 ∨ j = k + 2 ∨ j = k + 3 := by
  revert k j; decide

theorem fin4_ne : ∀ k : Fin 4, k + 1 ≠ k + 2 ∧ k + 1 ≠ k + 3 ∧ k + 2 ≠ k + 3 ∧
    k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 3 ≠ k := by decide

/-- With at most one faulty process, the votes of two correct processes agree, and the vote for a
correct process is its input. -/
theorem vote_spec (E : SyncExec (Fin 4) 2) (hf : E.faulty.card ≤ 1) (i : Fin 4)
    (s1 : Fin 4 → Vec 2)
    (hs1 : ∀ j ∉ E.faulty, s1 j = enc (fun k => if k ∈ E.faulty then E.byz 0 j k else E.inp k)) :
    let r : Fin 4 → Vec 2 := fun k => if k ∈ E.faulty then E.byz 1 i k else s1 k
    (∀ k ∉ E.faulty, vote r k = E.inp k) ∧
    (∀ k ∈ E.faulty, vote r k = maj3 (E.byz 0 (k + 1) k) (E.byz 0 (k + 2) k)
      (E.byz 0 (k + 3) k)) := by
  intro r
  have hr : ∀ j ∉ E.faulty, ∀ k, dec (r j) k = if k ∈ E.faulty then E.byz 0 j k else E.inp k := by
    intro j hj k; simp [r, hj, hs1 j hj, dec_enc]
  -- at most one faulty process
  have one : ∀ a ∈ E.faulty, ∀ b ∈ E.faulty, a = b := by
    intro a ha b hb
    by_contra hab
    have : 1 < E.faulty.card := Finset.one_lt_card.2 ⟨a, ha, b, hb, hab⟩
    omega
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · unfold vote
    apply maj3_eq
    have hk' : ∀ j ∉ E.faulty, dec (r j) k = E.inp k := fun j hj => by rw [hr j hj k]; simp [hk]
    by_cases h1 : k + 1 ∈ E.faulty
    · have h2 : k + 2 ∉ E.faulty := fun h => (fin4_ne k).1 (one _ h1 _ h)
      have h3 : k + 3 ∉ E.faulty := fun h => (fin4_ne k).2.1 (one _ h1 _ h)
      exact Or.inr (Or.inr ⟨hk' _ h2, hk' _ h3⟩)
    · by_cases h2 : k + 2 ∈ E.faulty
      · have h3 : k + 3 ∉ E.faulty := fun h => (fin4_ne k).2.2.1 (one _ h2 _ h)
        exact Or.inr (Or.inl ⟨hk' _ h1, hk' _ h3⟩)
      · exact Or.inl ⟨hk' _ h1, hk' _ h2⟩
  · have hc : ∀ j, j ≠ k → j ∉ E.faulty := fun j hjk hj => hjk (one _ hj _ hk)
    unfold vote
    rw [hr _ (hc _ (fin4_ne k).2.2.2.1), hr _ (hc _ (fin4_ne k).2.2.2.2.1),
      hr _ (hc _ (fin4_ne k).2.2.2.2.2)]
    simp [hk]

/-- A restricted algorithm whose round-1 states are the encodings of the received inputs and whose
round-2 states are the chosen point of `Γ` of the OM(1) votes solves exact BVC in two rounds
(`n = 4`, `f = 1`), for inputs in `K`. -/
theorem solves_of_states (A : RestrictedAlg (Fin 4) 2) (K : Set (Vec 2))
    (hA : ∀ E : SyncExec (Fin 4) 2, (∀ k ∉ E.faulty, E.inp k ∈ K) →
      (∀ j ∉ E.faulty, A.state E 1 j =
        enc (fun k => if k ∈ E.faulty then E.byz 0 j k else E.inp k)) ∧
      ∀ i ∉ E.faulty, A.state E 2 i =
        gammaPt 1 univ (vote fun k => if k ∈ E.faulty then E.byz 1 i k else A.state E 1 k)) :
    A.Solves 1 2 0 K := by
  intro E hf hK i hi j hj
  obtain ⟨h1, h2⟩ := hA E hK
  -- the decision of a correct process
  have hdec : ∀ i ∉ E.faulty, A.state E 2 i =
      gammaPt 1 univ (fun k => if k ∈ E.faulty then
        maj3 (E.byz 0 (k + 1) k) (E.byz 0 (k + 2) k) (E.byz 0 (k + 3) k) else E.inp k) := by
    intro i hi
    have hv := vote_spec E hf i (A.state E 1) h1
    simp only at hv
    rw [h2 i hi]
    congr 1
    funext k
    by_cases hk : k ∈ E.faulty
    · rw [hv.2 k hk]; simp [hk]
    · rw [hv.1 k hk]; simp [hk]
  rw [hdec i hi, hdec j hj]
  refine ⟨?_, fun l => by simp⟩
  set S : Fin 4 → Vec 2 := fun k => if k ∈ E.faulty then
    maj3 (E.byz 0 (k + 1) k) (E.byz 0 (k + 2) k) (E.byz 0 (k + 3) k) else E.inp k
  have hmem : gammaPt 1 univ S ∈ GammaOn 1 univ S :=
    gammaPt_mem S (by rw [finrank_fin_fun]; decide)
  set T := univ.filter fun k : Fin 4 => k ∉ E.faulty
  have hT : (univ : Finset (Fin 4)).card - 1 ≤ T.card := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin 4)))
      (fun q => q ∈ E.faulty)
    have h2 : (univ.filter fun q => q ∈ E.faulty) = E.faulty := by ext; simp
    rw [h2] at h1
    simp only [T]
    omega
  refine convexHull_mono ?_ (GammaOn_subset_convexHull (subset_univ T) hT hmem)
  rintro _ ⟨k, hk, rfl⟩
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, T] at hk
  exact ⟨k, hk, by simp [S, hk]⟩

/-- **The necessity part of Theorem 6 (synchronous case) is false as stated**: for `n = 4`,
`d = 2`, `f = 1` we have `n < (d + 2) f + 1`, yet a restricted synchronous algorithm solves
approximate BVC — even exact BVC (`ε = 0`), for arbitrary real inputs — in two rounds. -/
theorem theorem_6_sync_necessity_false :
    Fintype.card (Fin 4) < (2 + 2) * 1 + 1 ∧ fullInfoAlg.Solves 1 2 0 Set.univ := by
  refine ⟨by decide, solves_of_states _ _ fun E _ => ⟨fun j _ => ?_, fun i _ => ?_⟩⟩
  · simp [RestrictedAlg.state, fullInfoAlg]
  · change fullInfoAlg.upd 1 i _ _ = _
    simp [fullInfoAlg]

/-- A variant of the counterexample whose update function does **not** use the round number:
the own state tells the rounds apart (inputs lie in the box `[0, 1]²`, encodings have first
coordinate `> 1`). -/
noncomputable def fullInfoAlg' : RestrictedAlg (Fin 4) 2 :=
  ⟨fun _ _ v r => if v 0 ≤ 1 then enc r else gammaPt 1 univ (vote r)⟩

/-- The round-independent counterexample: with inputs in `[0, 1]²` (the setting of Section 3.2
with `ν = 0`, `U = 1`), `fullInfoAlg'` (whose update ignores the round number) solves exact BVC in
two rounds for `n = 4`, `d = 2`, `f = 1`. -/
theorem theorem_6_sync_necessity_false' :
    Fintype.card (Fin 4) < (2 + 2) * 1 + 1 ∧
      fullInfoAlg'.Solves 1 2 0 {v | ∀ l, 0 ≤ v l ∧ v l ≤ 1} := by
  have h1 : ∀ E : SyncExec (Fin 4) 2, (∀ k ∉ E.faulty, E.inp k ∈ {v : Vec 2 | ∀ l, 0 ≤ v l ∧ v l ≤ 1}) →
      ∀ j ∉ E.faulty, fullInfoAlg'.state E 1 j =
        enc (fun k => if k ∈ E.faulty then E.byz 0 j k else E.inp k) := by
    intro E hK j hj
    have := (hK j hj 0).2
    change fullInfoAlg'.upd 0 j (E.inp j) _ = _
    simp only [fullInfoAlg', this, ite_true]
    rfl
  refine ⟨by decide, solves_of_states _ _ fun E hK => ⟨h1 E hK, fun i hi => ?_⟩⟩
  change fullInfoAlg'.upd 1 i _ _ = _
  have hgt : ¬ (fullInfoAlg'.state E 1 i 0 ≤ 1) := by
    rw [h1 E hK i hi]; exact not_le.2 (one_lt_enc _)
  exact ite_eq_right_of_eq_false _ _ (eq_false hgt)

end ByzantineVectorConsensus
