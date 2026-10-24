import Papers.PODC2016.UnbeatableSetConsensus.Views

/-!
# Constructing indistinguishable runs

* `modify r K R M`: make the processes of `K` correct and let the processes that crash in round
  `M + 1` reach the sets `R p` in that round. If `K` is alive at `M`, nothing changes before
  round `M + 1` (`modify_deliv_lt`); round `M + 1` is described by `modify_deliv_last`.
* `chainRun r x L w u` (**Lemma 2** of the paper): given witnesses `w ℓ b` (`ℓ ≤ L`, `b ∈ ι`)
  hidden from `⟨x, m⟩`, the run in which `w 0 b` gets input `u b`, each `w ℓ b` (`ℓ < L`) crashes
  in round `ℓ + 1` sending only to `w (ℓ + 1) b` (the last column `w L b` crashes in round `L + 1`
  sending to nobody), and each `w ℓ b` receives in round `ℓ` exactly what `x` receives plus the
  message of `w (ℓ - 1) b`. Then `x` has the same view at `m` (`chainRun_sameView`), the value
  `u b` travels along column `b` (`chainRun_mem_vals`), the witnesses see nothing else that `x`
  does not see (`chainRun_vals_subset`), and the other columns stay hidden from them
  (`chainRun_hidden`).
* `decided_mem_vals`: knowledge of preconditions for Validity — a process can only decide a value
  it has seen.
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Finset

variable {P : Type*}

/-! ### Making processes correct and changing the last-round reach sets -/

section Modify

-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash/Model.lean (run surgery)
/-- Make the processes in `K` correct; processes crashing in round `M + 1` reach `R p` then. -/
noncomputable def modify (r : Run P) (K : Set P) (R : P → Set P) (M : ℕ) : Run P := by
  classical exact
  { input := r.input
    crash := fun p => if p ∈ K then none else r.crash p
    reach := fun p => if r.crash p = some (M + 1) then R p else r.reach p }

variable {r : Run P} {K : Set P} {R : P → Set P} {M : ℕ}

@[simp] lemma modify_input : (modify r K R M).input = r.input := rfl

lemma modify_crash_of_mem {p : P} (hp : p ∈ K) : (modify r K R M).crash p = none := by
  simp [modify, hp]

lemma modify_crash_of_not_mem {p : P} (hp : p ∉ K) : (modify r K R M).crash p = r.crash p := by
  simp [modify, hp]

lemma modify_not_faulty {p : P} (hp : p ∈ K) : ¬ (modify r K R M).Faulty p := by
  rw [not_faulty_iff]; exact modify_crash_of_mem hp

lemma modify_faulty {p : P} (h : (modify r K R M).Faulty p) : r.Faulty p := by
  by_cases hp : p ∈ K
  · exact absurd h (modify_not_faulty hp)
  · unfold SyncCrash.Run.Faulty at h ⊢; rwa [modify_crash_of_not_mem hp] at h

lemma modify_alive {p : P} {s : ℕ} (h : r.Alive p s) : (modify r K R M).Alive p s := by
  by_cases hp : p ∈ K
  · exact alive_of_crash_none (modify_crash_of_mem hp) s
  · intro c hc; rw [modify_crash_of_not_mem hp] at hc; exact h c hc

lemma modify_admissible [Fintype P] {t : ℕ} {D : Set ℕ} (h : Adm t D r) :
    Adm t D (modify r K R M) := by
  refine ⟨⟨le_trans (card_le_card fun p hp => ?_) h.1.1, fun p c hc => ?_⟩, h.2⟩
  · rw [SyncCrash.Run.mem_faulty] at hp ⊢; exact modify_faulty hp
  · by_cases hp : p ∈ K
    · rw [modify_crash_of_mem hp] at hc; cases hc
    · rw [modify_crash_of_not_mem hp] at hc; exact h.1.2 p c hc

/-- Before round `M + 1` nothing changes (if the processes made correct are alive at `M`). -/
lemma modify_deliv_lt (hK : ∀ p ∈ K, r.Alive p M) {s : ℕ} (hs : s < M) (q p : P) :
    (modify r K R M).Deliv q p s ↔ r.Deliv q p s := by
  by_cases hq : q ∈ K
  · simp only [deliv_of_crash_none (modify_crash_of_mem hq), true_iff]
    exact deliv_of_alive_succ ((hK q hq).mono hs) p
  · rw [deliv_iff, deliv_iff]
    simp only [SyncCrash.Run.Alive, modify_crash_of_not_mem hq]
    have : (modify r K R M).reach q = if r.crash q = some (M + 1) then R q else r.reach q := by
      simp [modify]
    rw [this]
    by_cases hc : r.crash q = some (M + 1)
    · simp only [hc, Option.some.injEq, ite_true]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, fun h3 => by omega⟩
    · simp [hc]

/-- Round `M + 1`. -/
lemma modify_deliv_last (q p : P) :
    (modify r K R M).Deliv q p M ↔
      q ∈ K ∨ (r.Alive q M ∧ ¬ (r.crash q = some (M + 1) ∧ p ∉ R q)) := by
  by_cases hq : q ∈ K
  · simp [deliv_of_crash_none (modify_crash_of_mem hq), hq]
  · rw [deliv_iff]
    simp only [SyncCrash.Run.Alive, modify_crash_of_not_mem hq, hq, false_or]
    have : (modify r K R M).reach q = if r.crash q = some (M + 1) then R q else r.reach q := by
      simp [modify]
    rw [this]
    by_cases hc : r.crash q = some (M + 1)
    · simp [hc]
    · simp [hc]

/-- Views up to time `M` do not change. -/
lemma modify_sameView (hK : ∀ p ∈ K, r.Alive p M) {s : ℕ} (hs : s ≤ M) (i : P) :
    SameView r (modify r K R M) i s :=
  sameView_of_prefix (r := r) (r' := modify r K R M) (m := s) (fun _ => rfl) (fun s' hs' w q => (modify_deliv_lt hK (by omega) w q).symm) i

/-- The view of `x` at time `M + 1` does not change if the processes made correct reached `x` in
round `M + 1` anyway and the new reach sets agree with the old ones on `x`. -/
lemma modify_sameView_last {x : P} (hK : ∀ p ∈ K, r.Alive p M)
    (hKx : ∀ p ∈ K, p ≠ x → r.Deliv p x M)
    (hR : ∀ q, r.crash q = some (M + 1) → (x ∈ R q ↔ x ∈ r.reach q)) :
    SameView r (modify r K R M) x (M + 1) := by
  refine sameView_of_agree (fun _ _ => rfl) (fun h s hs q hq => ?_)
  have hsM : s + 1 ≤ M + 1 := hs.le
  rcases Nat.lt_or_eq_of_le hsM with hlt | heq
  · exact (modify_deliv_lt hK (by omega) q h).symm
  · obtain rfl : s = M := by omega
    obtain rfl : h = x := seen_same_time hs
    rw [modify_deliv_last, deliv_iff]
    constructor
    · intro hd
      by_cases hqK : q ∈ K
      · exact Or.inl hqK
      · refine Or.inr ⟨hd.1, fun ⟨hc, hx⟩ => hd.2 ⟨hc, fun hx' => hx ((hR q hc).2 hx')⟩⟩
    · rintro (hqK | ⟨h1, h2⟩)
      · exact hKx q hqK hq
      · exact ⟨h1, fun ⟨hc, hx⟩ => h2 ⟨hc, fun hx' => hx ((hR q hc).1 hx')⟩⟩

end Modify

/-- A node seen one round later by another process sent it a message in that round. -/
lemma Seen.deliv_of_succ {r : Run P} {j x : P} {M : ℕ} (hs : Seen r j M x (M + 1)) (hne : j ≠ x) :
    r.Deliv j x M := by
  rcases (seen_succ_iff le_rfl).1 hs with h | ⟨q, hq, h⟩
  · exact absurd (seen_same_time h) hne
  · obtain rfl := seen_same_time h; exact hq.2

/-! ### Knowledge of preconditions for Validity -/

section KoP

variable [Fintype P] {k t : ℕ} {D : Set ℕ}

/-- Replace the inputs of all processes not seen at time `0` by `a`. -/
noncomputable def replaceUnseen (r : Run P) (i : P) (m a : ℕ) : Run P := by
  classical exact { r with input := fun p => if Seen r p 0 i m then r.input p else a }

omit [Fintype P] in
lemma replaceUnseen_sameView (r : Run P) (i : P) (m a : ℕ) :
    SameView r (replaceUnseen r i m a) i m := by
  classical
  refine sameView_of_agree (fun q hq => ?_) (fun q s _ w _ => Iff.rfl)
  simp [replaceUnseen, hq]

/-- **Knowledge of preconditions** (Theorem 4) for Validity: in a protocol satisfying Validity, a
process decides only on a value it has seen (`D` must contain two values). -/
theorem decided_mem_vals {Q : Protocol P} (hQ : SolvesSetConsensus k t D Q) {a b : ℕ}
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) {r : Run P} (hr : Adm t D r) {i : P} {m u : ℕ}
    (hd : DecidesAt Q r i m u) : u ∈ vals r i m := by
  classical
  set c := if u = a then b else a
  have hcu : c ≠ u := by
    simp only [c]; split_ifs with h
    · rw [h]; exact Ne.symm hab
    · exact Ne.symm h
  set r' := replaceUnseen r i m c
  have hsv := replaceUnseen_sameView r i m c
  have hr' : Adm t D r' := by
    refine ⟨hr.1, fun p => ?_⟩
    simp only [r', replaceUnseen]
    split_ifs
    · exact hr.2 p
    · simp only [c]; split_ifs <;> assumption
  have hd' : DecidesAt Q r' i m u := (hsv.decidesAt_iff Q le_rfl Iff.rfl).1 hd
  obtain ⟨j, hj⟩ := hQ.validity r' hr' i m u hd'
  by_cases hs : Seen r j 0 i m
  · refine mem_vals.2 ⟨j, hs, ?_⟩
    simpa [r', replaceUnseen, hs] using hj
  · simp [r', replaceUnseen, hs] at hj; exact absurd hj hcu

/-- A process that is high when it decides decides a high value. -/
theorem decided_ge_of_not_low {Q : Protocol P} (hQ : SolvesSetConsensus k t D Q) {a b : ℕ}
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) {r : Run P} (hr : Adm t D r) {i : P} {m u : ℕ}
    (hd : DecidesAt Q r i m u) (hl : ¬ Low k r i m) : k ≤ u :=
  not_low_iff.1 hl u (decided_mem_vals hQ ha hb hab hr hd)

end KoP

/-! ### The chain construction (Lemma 2) -/

section Chain

variable {ι : Type*}

/-- The position `(ℓ, b)` of a witness `p = w ℓ b` (`ℓ ≤ L`), `none` for other processes. -/
noncomputable def pos (L : ℕ) (w : ℕ → ι → P) (p : P) : Option (ℕ × ι) := by
  classical exact
  if h : ∃ ℓb : ℕ × ι, ℓb.1 ≤ L ∧ w ℓb.1 ℓb.2 = p then some h.choose else none

/-- The run of **Lemma 2** (see the module docstring). -/
noncomputable def chainRun (r : Run P) (x : P) (L : ℕ) (w : ℕ → ι → P) (u : ι → ℕ) : Run P where
  input p := match pos L w p with
    | some (0, b) => u b
    | _ => r.input p
  crash p := match pos L w p with
    | some (ℓ, _) => some (ℓ + 1)
    | none => r.crash p
  reach p := match pos L w p with
    | some (ℓ, b) => {q | ℓ < L ∧ q = w (ℓ + 1) b}
    | none => {q | ((∃ c b, r.crash p = some c ∧ c ≤ L ∧ w c b = q) ∧ x ∈ r.reach p) ∨
        (¬ (∃ c b, r.crash p = some c ∧ c ≤ L ∧ w c b = q) ∧ q ∈ r.reach p)}

/-- The hypotheses of Lemma 2: witnesses of a hidden capacity of `⟨x, m⟩` at the times `≤ L`. -/
structure ChainHyp (r : Run P) (x : P) (m L : ℕ) (w : ℕ → ι → P) : Prop where
  le : L ≤ m
  inj : ∀ ℓ ≤ L, Function.Injective (w ℓ)
  hidden : ∀ ℓ ≤ L, ∀ b, Hidden r x m (w ℓ b) ℓ

variable {r : Run P} {x : P} {m L : ℕ} {w : ℕ → ι → P} {u : ι → ℕ}

lemma crash_chainRun_of_none {p : P} (h : pos L w p = none) :
    (chainRun r x L w u).crash p = r.crash p := by
  simp [chainRun, h]

namespace ChainHyp

variable (H : ChainHyp r x m L w)
include H

lemma w_eq {ℓ ℓ' : ℕ} {b b' : ι} (hℓ : ℓ ≤ L) (hℓ' : ℓ' ≤ L) (he : w ℓ b = w ℓ' b') :
    ℓ = ℓ' ∧ b = b' := by
  have h1 := H.hidden ℓ hℓ b
  have h2 := H.hidden ℓ' hℓ' b'
  rw [he] at h1
  obtain rfl := h1.time_eq h2 (hℓ.trans H.le) (hℓ'.trans H.le)
  exact ⟨rfl, H.inj ℓ hℓ he⟩

lemma pos_w {ℓ : ℕ} (hℓ : ℓ ≤ L) (b : ι) : pos L w (w ℓ b) = some (ℓ, b) := by
  classical
  have hex : ∃ ℓb : ℕ × ι, ℓb.1 ≤ L ∧ w ℓb.1 ℓb.2 = w ℓ b := ⟨(ℓ, b), hℓ, rfl⟩
  unfold pos
  rw [dite_eq_left hex]
  have hspec := hex.choose_spec
  have e := H.w_eq hspec.1 hℓ hspec.2
  exact congrArg some (Prod.ext e.1 e.2)

set_option linter.unusedSectionVars false in
lemma pos_eq_some {p : P} {ℓ : ℕ} {b : ι} (h : pos L w p = some (ℓ, b)) :
    ℓ ≤ L ∧ w ℓ b = p := by
  classical
  unfold pos at h
  split_ifs at h with hex
  obtain ⟨h1, h2⟩ := hex.choose_spec
  rw [Option.some.injEq] at h
  rw [h] at h1 h2
  exact ⟨h1, h2⟩

lemma pos_eq_none {p : P} (h : pos L w p = none) (ℓ : ℕ) (hℓ : ℓ ≤ L) (b : ι) : w ℓ b ≠ p := by
  rintro rfl; rw [H.pos_w hℓ b] at h; cases h

lemma not_w_of_seen {p : P} {ℓ : ℕ} (hs : Seen r p ℓ x m) (hℓ : ℓ ≤ L) (b : ι) : w ℓ b ≠ p := by
  rintro rfl; exact (H.hidden ℓ hℓ b).1 hs

/-! Crash pattern of the chain run. -/

lemma crash_w {ℓ : ℕ} (hℓ : ℓ ≤ L) (b : ι) :
    (chainRun r x L w u).crash (w ℓ b) = some (ℓ + 1) := by
  simp [chainRun, H.pos_w hℓ b]


lemma alive_w {ℓ : ℕ} (hℓ : ℓ ≤ L) (b : ι) : (chainRun r x L w u).Alive (w ℓ b) ℓ :=
  (alive_of_crash_some (H.crash_w hℓ b)).2 (Nat.lt_succ_self ℓ)

lemma deliv_w {ℓ s : ℕ} (hℓ : ℓ ≤ L) (b : ι) (q : P) :
    (chainRun r x L w u).Deliv (w ℓ b) q s ↔ s < ℓ ∨ (s = ℓ ∧ ℓ < L ∧ q = w (ℓ + 1) b) := by
  rw [deliv_of_crash_some (H.crash_w hℓ b)]
  have : (chainRun r x L w u).reach (w ℓ b) = {q | ℓ < L ∧ q = w (ℓ + 1) b} := by
    simp [chainRun, H.pos_w hℓ b]
  rw [this]
  simp only [Set.mem_ofPred_eq, add_lt_add_iff_right, add_left_inj]

set_option linter.unusedSectionVars false in
open Classical in
/-- The delivery pattern of a non-witness: as in `r`, except that the witnesses of time `s + 1`
receive its round-`s + 1` message iff `x` does. -/
lemma deliv_of_none {p : P} (h : pos L w p = none) (q : P) (s : ℕ) :
    (chainRun r x L w u).Deliv p q s ↔
      if ∃ b, s + 1 ≤ L ∧ w (s + 1) b = q then r.Deliv p x s else r.Deliv p q s := by
  classical
  have hreach : (chainRun r x L w u).reach p =
      {q | ((∃ c b, r.crash p = some c ∧ c ≤ L ∧ w c b = q) ∧ x ∈ r.reach p) ∨
        (¬ (∃ c b, r.crash p = some c ∧ c ≤ L ∧ w c b = q) ∧ q ∈ r.reach p)} := by
    simp [chainRun, h]
  rw [deliv_iff, deliv_iff, deliv_iff]
  simp only [SyncCrash.Run.Alive, crash_chainRun_of_none h, hreach, Set.mem_ofPred_eq]
  split_ifs with hq
  · obtain ⟨b, hb, rfl⟩ := hq
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, fun ⟨h3, h4⟩ => h2 ⟨h3, ?_⟩⟩
      rintro (⟨-, h5⟩ | ⟨h5, -⟩)
      · exact h4 h5
      · exact h5 ⟨s + 1, b, h3, hb, rfl⟩
    · rintro ⟨h1, h2⟩; refine ⟨h1, fun ⟨h3, h4⟩ => h2 ⟨h3, ?_⟩⟩
      intro h5; exact h4 (Or.inl ⟨⟨s + 1, b, h3, hb, rfl⟩, h5⟩)
  · constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, fun ⟨h3, h4⟩ => h2 ⟨h3, ?_⟩⟩
      rintro (⟨⟨c, b, hc, hcL, rfl⟩, -⟩ | ⟨-, h5⟩)
      · rw [h3] at hc; cases hc; exact hq ⟨b, hcL, rfl⟩
      · exact h4 h5
    · rintro ⟨h1, h2⟩; refine ⟨h1, fun ⟨h3, h4⟩ => h2 ⟨h3, ?_⟩⟩
      intro h5
      refine h4 (Or.inr ⟨?_, h5⟩)
      rintro ⟨c, b, hc, hcL, rfl⟩
      rw [h3] at hc; cases hc; exact hq ⟨b, hcL, rfl⟩

lemma input_w0 (b : ι) : (chainRun r x L w u).input (w 0 b) = u b := by
  simp [chainRun, H.pos_w (Nat.zero_le L) b]

lemma input_of_not_w0 {p : P} (hp : ∀ b, w 0 b ≠ p) : (chainRun r x L w u).input p = r.input p := by
  simp only [chainRun]
  split
  · next b h => exact absurd (H.pos_eq_some h).2 (hp b)
  · rfl

/-! The properties of Lemma 2. -/

/-- **Lemma 2**, `r'_i(m) = r_i(m)`. -/
theorem sameView : SameView r (chainRun r x L w u) x m := by
  refine sameView_of_agree (fun q hq => ?_) (fun q s hq w' hw' => ?_)
  · exact (H.input_of_not_w0 fun b => H.not_w_of_seen hq (Nat.zero_le L) b).symm
  · have hsm : s + 1 ≤ m := hq.le
    cases hpos : pos L w w' with
    | some ℓb =>
      obtain ⟨ℓ, b⟩ := ℓb
      obtain ⟨hℓ, rfl⟩ := H.pos_eq_some hpos
      rw [H.deliv_w hℓ b]
      have hh := H.hidden ℓ hℓ b
      constructor
      · intro hd
        rcases Nat.lt_trichotomy s ℓ with hlt | rfl | hgt
        · exact Or.inl hlt
        · exact absurd ((seen_of_deliv (Ne.symm hw').symm hd).trans hq) hh.1
        · obtain ⟨c, hc, hcle⟩ := hh.crash_le (by omega)
          exact absurd (hd.1 c hc) (by omega)
      · rintro (hlt | ⟨rfl, hL, rfl⟩)
        · exact hh.deliv hlt hq (Ne.symm hw')
        · exact absurd hq (H.hidden (s + 1) hL b).1
    | none =>
      rw [H.deliv_of_none hpos, ite_eq_right]
      rintro ⟨b, hb, rfl⟩
      exact (H.hidden (s + 1) hb b).1 hq

lemma ne_succ {ℓ : ℕ} (hℓ : ℓ < L) (b : ι) : w ℓ b ≠ w (ℓ + 1) b := by
  intro he; have := (H.w_eq hℓ.le hℓ he).1; omega

/-- **Lemma 2 (a)**: the value `u b` travels along column `b`. -/
theorem mem_vals [Fintype P] {ℓ : ℕ} (hℓ : ℓ ≤ L) (b : ι) : u b ∈ vals (chainRun r x L w u) (w ℓ b) ℓ := by
  induction ℓ with
  | zero => rw [vals_zero, H.input_w0]; exact Finset.mem_singleton_self _
  | succ ℓ ih =>
    refine vals_subset_succ_of_comm ⟨H.ne_succ hℓ b, ?_⟩ (ih (by omega))
    rw [H.deliv_w (by omega) b]
    exact Or.inr ⟨rfl, hℓ, rfl⟩

/-- **Lemma 2 (b)**: the column-`b` witnesses see only `u b` besides what `x` sees. -/
theorem vals_subset [Fintype P] {ℓ : ℕ} (hℓ : ℓ ≤ L) (b : ι) :
    vals (chainRun r x L w u) (w ℓ b) ℓ ⊆ insert (u b) (vals r x ℓ) := by
  have hsv := H.sameView (u := u)
  induction ℓ with
  | zero => rw [vals_zero, H.input_w0]; simp
  | succ ℓ ih =>
    intro v hv
    have hm : ℓ + 1 ≤ m := hℓ.trans H.le
    have hxv : vals (chainRun r x L w u) x (ℓ + 1) = vals r x (ℓ + 1) :=
      ((hsv.mono hm).vals_eq).symm
    have hh := H.hidden (ℓ + 1) hℓ b
    have hne : w (ℓ + 1) b ≠ x := hh.ne hm
    rcases mem_vals_succ.1 hv with hv | ⟨q, hq, hv⟩
    · -- the witness's own state at time `ℓ` is seen by `⟨x, m⟩`, and reached `x`
      have hs := hh.seen_pred hm
      rw [← (hsv.of_seen hs).vals_eq] at hv
      have hd : r.Deliv (w (ℓ + 1) b) x ℓ := hh.deliv (Nat.lt_succ_self ℓ) (seen_self hm) hne.symm
      exact mem_insert_of_mem (vals_subset_succ_of_comm ⟨hne, hd⟩ hv)
    · by_cases hqw : q = w ℓ b
      · subst hqw
        rcases mem_insert.1 (ih (by omega) hv) with h | h
        · exact h ▸ mem_insert_self _ _
        · exact mem_insert_of_mem (vals_mono (Nat.le_succ ℓ) h)
      · -- any other sender also reached `x`
        apply mem_insert_of_mem
        rw [← hxv]
        by_cases hqx : q = x
        · subst hqx; exact vals_mono (Nat.le_succ ℓ) hv
        refine vals_subset_succ_of_comm ⟨hqx, ?_⟩ hv
        have hd := hq.2
        cases hpos : pos L w q with
        | some ℓb =>
          obtain ⟨ℓ'', b''⟩ := ℓb
          obtain ⟨hℓ'', rfl⟩ := H.pos_eq_some hpos
          rw [H.deliv_w hℓ'' b''] at hd ⊢
          rcases hd with hlt | ⟨rfl, -, he⟩
          · exact Or.inl hlt
          · obtain ⟨-, rfl⟩ := H.w_eq hℓ hℓ he
            exact absurd rfl hqw
        | none =>
          rw [H.deliv_of_none hpos, ite_eq_left ⟨b, hℓ, rfl⟩] at hd
          rw [H.deliv_of_none hpos, ite_eq_right]
          · exact hd
          · rintro ⟨b', hb', he⟩
            exact (H.hidden (ℓ + 1) hb' b').1 (he ▸ seen_self hm)

/-- Only the column-`b'` witnesses (at times `≤ L`) see a column-`b'` witness. -/
theorem seen_w {ℓ' s : ℕ} {b' : ι} {y : P} (_hℓ' : ℓ' ≤ L)
    (hs : Seen (chainRun r x L w u) (w ℓ' b') ℓ' y s) (hsL : s ≤ L) :
    ∃ s', ℓ' ≤ s' ∧ s' ≤ s ∧ y = w s' b' := by
  have := DynNet.Journey.of_inv (P := fun τ a => τ ≤ L → ∃ s', ℓ' ≤ s' ∧ s' ≤ τ ∧ a = w s' b') hs
    (fun _ => ⟨ℓ', le_rfl, le_rfl, rfl⟩) ?_
  · exact this hsL
  intro τ a c _ _ ih hac hτ
  obtain ⟨s', h1, h2, rfl⟩ := ih (by omega)
  rcases hac with rfl | hac
  · exact ⟨s', h1, by omega, rfl⟩
  · have hd := hac.2
    rw [H.deliv_w (by omega) b'] at hd
    rcases hd with hlt | ⟨rfl, -, rfl⟩
    · omega
    · exact ⟨τ + 1, by omega, le_rfl, rfl⟩

/-- A witness of column `b'` at time `ℓ'` is hidden from every node `⟨y, ℓ⟩` (`ℓ' ≤ ℓ ≤ L`) that
is not a column-`b'` witness. -/
theorem hidden_of_not_w {ℓ ℓ' : ℕ} {b' : ι} {y : P} (hℓ : ℓ ≤ L) (hℓ' : ℓ' ≤ ℓ)
    (hy : ∀ s ≤ ℓ, y ≠ w s b') : Hidden (chainRun r x L w u) y ℓ (w ℓ' b') ℓ' := by
  refine hidden_of_alive (H.alive_w (by omega) b') fun hs => ?_
  obtain ⟨s', -, h2, rfl⟩ := H.seen_w (by omega) hs hℓ
  exact hy s' h2 rfl

/-- **Lemma 2 (c)**: the other columns witness a hidden capacity of the column-`b` witnesses. -/
theorem hidden_col {ℓ ℓ' : ℕ} {b b' : ι} (hℓ : ℓ ≤ L) (hℓ' : ℓ' ≤ ℓ) (hbb : b ≠ b') :
    Hidden (chainRun r x L w u) (w ℓ b) ℓ (w ℓ' b') ℓ' :=
  H.hidden_of_not_w hℓ hℓ' fun s hs he => hbb (H.w_eq hℓ (by omega) he).2

/-- The faulty processes of the chain run: those of `r` and the last column. -/
theorem faulty_of {p : P} (hp : (chainRun r x L w u).Faulty p) :
    r.Faulty p ∨ ∃ b, w L b = p := by
  cases hpos : pos L w p with
  | some ℓb =>
    obtain ⟨ℓ, b⟩ := ℓb
    obtain ⟨hℓ, rfl⟩ := H.pos_eq_some hpos
    rcases Nat.lt_or_eq_of_le hℓ with hlt | rfl
    · exact Or.inl ((H.hidden ℓ hℓ b).faulty (by have := H.le; omega))
    · exact Or.inr ⟨b, rfl⟩
  | none =>
    left; unfold SyncCrash.Run.Faulty at hp ⊢; rwa [crash_chainRun_of_none hpos] at hp

theorem crash_pos {p : P} {c : ℕ} [Fintype P] {t : ℕ} {D : Set ℕ} (hr : Adm t D r)
    (hc : (chainRun r x L w u).crash p = some c) : 1 ≤ c := by
  cases hpos : pos L w p with
  | some ℓb =>
    obtain ⟨ℓ, b⟩ := ℓb
    obtain ⟨hℓ, rfl⟩ := H.pos_eq_some hpos
    rw [H.crash_w hℓ b] at hc; cases hc; omega
  | none => rw [crash_chainRun_of_none hpos] at hc; exact hr.1.2 p c hc

/-- Processes seen at time `L` by `⟨x, m⟩` are not witnesses. -/
theorem pos_none_of_seen {p : P} {s : ℕ} (hs : Seen r p s x m) (hsL : L ≤ s) :
    pos L w p = none := by
  cases hpos : pos L w p with
  | none => rfl
  | some ℓb =>
    obtain ⟨hℓ, rfl⟩ := H.pos_eq_some hpos
    exact absurd (hs.mono_left (by omega)) (H.hidden _ hℓ _).1

theorem crash_of_seen {p : P} {s : ℕ} (hs : Seen r p s x m) (hsL : L ≤ s) :
    (chainRun r x L w u).crash p = r.crash p :=
  crash_chainRun_of_none (H.pos_none_of_seen hs hsL)

theorem alive_iff_of_seen {p : P} {s s' : ℕ} (hs : Seen r p s x m) (hsL : L ≤ s) :
    (chainRun r x L w u).Alive p s' ↔ r.Alive p s' := by
  simp only [SyncCrash.Run.Alive, H.crash_of_seen hs hsL]

omit H in
theorem input_mem [Fintype P] {t : ℕ} {D : Set ℕ} (hr : Adm t D r) (hu : ∀ b, u b ∈ D) (p : P) :
    (chainRun r x L w u).input p ∈ D := by
  simp only [chainRun]
  split
  · exact hu _
  · exact hr.2 p

/-- The chain run is admissible when the last column is at a time `< m`. -/
theorem adm [Fintype P] {t : ℕ} {D : Set ℕ} (hr : Adm t D r) (hu : ∀ b, u b ∈ D) (hLm : L < m) :
    Adm t D (chainRun r x L w u) := by
  refine ⟨⟨le_trans (card_le_card fun p hp => ?_) hr.1.1, fun p c hc => H.crash_pos hr hc⟩,
    ChainHyp.input_mem hr hu⟩
  rw [SyncCrash.Run.mem_faulty] at hp ⊢
  rcases H.faulty_of hp with h | ⟨b, rfl⟩
  · exact h
  · exact (H.hidden L le_rfl b).faulty hLm

end ChainHyp

end Chain

end Podc.UnbeatableSetConsensus
