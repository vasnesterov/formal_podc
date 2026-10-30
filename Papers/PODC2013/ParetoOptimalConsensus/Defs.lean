import Papers.PODC2016.UnbeatableSetConsensus.Unbeatable
import Papers.PODC2016.UnbeatableSetConsensus.UPmin

/-!
# Castañeda–Gonczarowski–Moses, *Good, Better, Best! — Unbeatable Protocols for Consensus and
Set Consensus* (PODC 2013 BA, full version arXiv 1311.6902): common definitions

We reuse the model of the companion formalization `Papers.PODC2016.UnbeatableSetConsensus`
(same authors, same model): synchronous message passing with crash failures, full-information
protocols, an adversary `α = (v⃗, F)` is a `Run P`, a protocol is a view-invariant decision rule.

Consensus is the case `k = 1` of nonuniform `k`-set consensus (`SolvesSetConsensus 1 t bin`), with
binary inputs `bin = {0, 1}`.

This file adds:
* `Knows`: knowledge `K_i φ` (Definition 2) in the system of a full-information protocol: `φ` holds
  in every admissible run in which `i` is alive with the same view (for full-information protocols
  the decision history is a function of the view, so the system does not depend on the protocol);
* `HiddenPath` (§1): a sequence `j₀, …, j_m` with `⟨j_ℓ, ℓ⟩` hidden from `⟨i, m⟩`; it exists iff
  the hidden capacity is `≥ 1` (`hiddenPath_iff`);
* the protocols `P_a` (the early-stopping protocol `P0` of §3 for `a = 0`) and `Opt_a`
  (`Opt0` for `a = 0`, `Opt1` for `a = 1`);
* transfer of all notions between protocols that agree on admissible runs (`EqOnAdm`).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

/-- Binary initial values `V = {0, 1}`. -/
def bin : Set ℕ := {0, 1}

lemma mem_bin {v : ℕ} : v ∈ bin ↔ v = 0 ∨ v = 1 := Iff.rfl

lemma zero_mem_bin : (0 : ℕ) ∈ bin := Or.inl rfl
lemma one_mem_bin : (1 : ℕ) ∈ bin := Or.inr rfl

lemma one_sub_mem_bin {a : ℕ} (ha : a ∈ bin) : 1 - a ∈ bin := by
  rcases ha with rfl | rfl <;> simp [bin]

lemma one_sub_ne {a : ℕ} (ha : a ∈ bin) : 1 - a ≠ a := by
  rcases ha with rfl | rfl <;> simp

lemma eq_or_eq_one_sub {a v : ℕ} (ha : a ∈ bin) (hv : v ∈ bin) : v = a ∨ v = 1 - a := by
  rcases ha with rfl | rfl <;> rcases hv with rfl | rfl <;> simp

variable {P : Type*}

/-- **Knowledge** (Definition 2) for full-information protocols in the context `γ = (D^n, Crash(t))`,
at a point where `i` is alive: `K_i φ` holds at `(r, m)` iff `φ` holds in every admissible run in
which `i` is alive at `m` with the same view (the local state of a live process is its view; that
of a crashed process is `⊥`). -/
def Knows [Fintype P] (t : ℕ) (D : Set ℕ) (r : Run P) (i : P) (m : ℕ) (φ : Run P → Prop) : Prop :=
  ∀ r', Adm t D r' → SameView r r' i m → r'.Alive i m → φ r'

-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- There is a **hidden path** w.r.t. `⟨i, m⟩`: processes `j₀, …, j_m` with `⟨j_ℓ, ℓ⟩` hidden from
`⟨i, m⟩` for all `ℓ ≤ m`. -/
def HiddenPath (r : Run P) (i : P) (m : ℕ) : Prop :=
  ∃ b : ℕ → P, ∀ ℓ ≤ m, Hidden r i m (b ℓ) ℓ

lemma hiddenPath_iff_of_sameView {r r' : Run P} {i : P} {m : ℕ} (h : SameView r r' i m) :
    HiddenPath r i m ↔ HiddenPath r' i m := by
  unfold HiddenPath
  simp only [h.hidden_iff]

lemma hiddenPath_iff [Fintype P] {r : Run P} {i : P} {m : ℕ} :
    HiddenPath r i m ↔ 1 ≤ hc r i m := by
  classical
  rw [le_hc_iff]
  constructor
  · rintro ⟨b, hb⟩ ℓ hℓ
    exact card_pos.2 ⟨b ℓ, mem_hiddenAt.2 (hb ℓ hℓ)⟩
  · intro h
    have : ∀ ℓ, ∃ q : P, ℓ ≤ m → Hidden r i m q ℓ := by
      intro ℓ
      by_cases hℓ : ℓ ≤ m
      · obtain ⟨q, hq⟩ := card_pos.1 (h ℓ hℓ)
        exact ⟨q, fun _ => mem_hiddenAt.1 hq⟩
      · exact ⟨i, fun h => absurd h hℓ⟩
    choose b hb using this
    exact ⟨b, fun ℓ hℓ => hb ℓ hℓ⟩

lemma not_hiddenPath_iff [Fintype P] {r : Run P} {i : P} {m : ℕ} :
    ¬ HiddenPath r i m ↔ ∃ ℓ ≤ m, ∀ q, ¬ Hidden r i m q ℓ := by
  classical
  rw [hiddenPath_iff, not_le, hc_lt_iff]
  refine exists_congr fun ℓ => and_congr_right fun _ => ?_
  rw [Nat.lt_one_iff, card_eq_zero, eq_empty_iff_forall_notMem]
  simp only [mem_hiddenAt]

/-! ### Values in a binary run -/

section Bin

variable [Fintype P] {t : ℕ} {r : Run P} {i : P} {m : ℕ}

lemma mem_bin_of_mem_vals (hr : Adm t bin r) {v : ℕ} (hv : v ∈ vals r i m) : v ∈ bin := by
  obtain ⟨j, -, rfl⟩ := mem_vals.1 hv
  exact hr.2 j

/-- In a binary run, a process that has not seen `a` has seen `1 - a`. -/
lemma one_sub_mem_vals (hr : Adm t bin r) {a : ℕ} (ha : a ∈ bin) (hna : a ∉ vals r i m) :
    1 - a ∈ vals r i m := by
  obtain ⟨v, hv⟩ := vals_nonempty r i m
  rcases eq_or_eq_one_sub ha (mem_bin_of_mem_vals hr hv) with rfl | rfl
  · exact absurd hv hna
  · exact hv

omit [Fintype P] in
-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- If `⟨i, m⟩` has no hidden path, it sees (at time `0`) everything that any correct process
ever sees: the key fact behind the "no hidden path" decision rules. -/
lemma seen_of_not_hidden {ℓ : ℕ} (hℓ : ℓ ≤ m) (hnh : ∀ q, ¬ Hidden r i m q ℓ) {j : P}
    (hj : ¬ r.Faulty j) {m' : ℕ} {q : P} {s : ℕ} (hs : Seen r q s j m') (hsℓ : s ≤ ℓ) :
    Seen r q s i m := by
  rcases le_or_gt ℓ m' with hlm | hlm
  · obtain ⟨h, hqh, hhj⟩ := hs.through hsℓ hlm
    have hha : r.Alive h ℓ := hhj.alive (SyncCrash.Run.alive_of_not_faulty hj m')
    have : Seen r h ℓ i m := by
      by_contra hns
      exact hnh h (hidden_of_alive hha hns)
    exact hqh.trans this
  · by_cases hji : j = i
    · subst hji; exact hs.mono_right (by omega)
    · exact hs.trans ((seen_of_deliv hji (SyncCrash.Run.deliv_of_not_faulty hj i m')).mono_right
        (by omega))

lemma vals_subset_of_not_hidden {ℓ : ℕ} (hℓ : ℓ ≤ m) (hnh : ∀ q, ¬ Hidden r i m q ℓ) {j : P}
    (hj : ¬ r.Faulty j) (m' : ℕ) : vals r j m' ⊆ vals r i m := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := mem_vals.1 hv
  exact mem_vals.2 ⟨q, seen_of_not_hidden hℓ hnh hj hq (Nat.zero_le ℓ), rfl⟩

/-- A process that does not know `a` at `m` but knows it at `m + 1` has a hidden path at `m`
(the chain that brings `a`). -/
lemma hiddenPath_of_first {a M : ℕ} (hn : a ∉ vals r i M) (hy : a ∈ vals r i (M + 1)) :
    HiddenPath r i M := by
  obtain hv | ⟨q, hq, hqv⟩ := mem_vals_succ.1 hy
  · exact absurd hv hn
  have hqa : r.Alive q M := hq.2.1
  have : ∀ ℓ, ∃ h : P, ℓ ≤ M → Hidden r i M h ℓ := by
    intro ℓ
    by_cases hℓ : ℓ ≤ M
    · obtain ⟨h, hs, hhv⟩ := exists_seen_of_mem_vals hqv hℓ
      refine ⟨h, fun _ => hidden_of_alive (hs.alive hqa) fun hsi => hn ?_⟩
      exact vals_subset_of_seen hsi hhv
    · exact ⟨i, fun h => absurd h hℓ⟩
  choose b hb using this
  exact ⟨b, fun ℓ hℓ => hb ℓ hℓ⟩

/-- With a hidden path at `m`, at least `m` processes crash (`c · m ≤ f` for `c = 1`). -/
lemma le_faulty_of_hiddenPath (h : HiddenPath r i m) : m ≤ r.faulty.card := by
  have := mul_le_card_faulty (hiddenPath_iff.1 h)
  omega

/-- A value is first learnt at a time `≤ f + 1`. -/
lemma first_le {a M : ℕ} (hn : a ∉ vals r i M) (hy : a ∈ vals r i (M + 1)) :
    M ≤ r.faulty.card :=
  le_faulty_of_hiddenPath (hiddenPath_of_first hn hy)

/-- At time `f + 1` there is no hidden path. -/
lemma not_hiddenPath_faulty : ¬ HiddenPath r i (r.faulty.card + 1) := fun h => by
  have := le_faulty_of_hiddenPath h; omega

end Bin

/-! ### Comparing protocols that agree on admissible runs -/

section Transfer

variable [Fintype P] {t k : ℕ} {D : Set ℕ}

/-- Two protocols take the same decisions on admissible runs. -/
def EqOnAdm (t : ℕ) (D : Set ℕ) (Q₁ Q₂ : Protocol P) : Prop :=
  ∀ r, Adm t D r → ∀ i m, Q₁.dec r i m = Q₂.dec r i m

variable {Q₁ Q₂ Q₃ : Protocol P}

lemma EqOnAdm.decidesAt_iff (h : EqOnAdm t D Q₁ Q₂) {r : Run P} (hr : Adm t D r) {i : P}
    {m v : ℕ} : DecidesAt Q₁ r i m v ↔ DecidesAt Q₂ r i m v := by
  unfold DecidesAt
  simp only [h r hr]

lemma EqOnAdm.decidesBy_iff (h : EqOnAdm t D Q₁ Q₂) {r : Run P} (hr : Adm t D r) {i : P}
    {m : ℕ} : DecidesBy Q₁ r i m ↔ DecidesBy Q₂ r i m := by
  unfold DecidesBy
  simp only [h.decidesAt_iff hr]

lemma EqOnAdm.symm (h : EqOnAdm t D Q₁ Q₂) : EqOnAdm t D Q₂ Q₁ :=
  fun r hr i m => (h r hr i m).symm

lemma EqOnAdm.solves (h : EqOnAdm t D Q₁ Q₂) (hs : SolvesSetConsensus k t D Q₁) :
    SolvesSetConsensus k t D Q₂ where
  decision r hr i hi := by
    obtain ⟨m, v, hv⟩ := hs.decision r hr i hi
    exact ⟨m, v, (h.decidesAt_iff hr).1 hv⟩
  validity r hr i m v hv := hs.validity r hr i m v ((h.decidesAt_iff hr).2 hv)
  agreement r hr := by
    have := hs.agreement r hr
    simpa only [h.decidesAt_iff hr] using this

lemma EqOnAdm.dominates_left (h : EqOnAdm t D Q₁ Q₂) (hd : Dominates t D Q₁ Q₃) :
    Dominates t D Q₂ Q₃ :=
  fun r hr i m v hv => (h.decidesBy_iff hr).1 (hd r hr i m v hv)

lemma EqOnAdm.dominates_right (h : EqOnAdm t D Q₁ Q₂) (hd : Dominates t D Q₃ Q₁) :
    Dominates t D Q₃ Q₂ :=
  fun r hr i m v hv => hd r hr i m v ((h.decidesAt_iff hr).2 hv)

lemma EqOnAdm.unbeatable (h : EqOnAdm t D Q₁ Q₂) (hu : Unbeatable k t D Q₁) :
    Unbeatable k t D Q₂ :=
  ⟨h.solves hu.1, fun Q hQ hdom =>
    h.dominates_left (hu.2 Q hQ (h.symm.dominates_right hdom))⟩

/-- Two protocols have the same decisions (time and value) on admissible runs. -/
def SameDecisions (t : ℕ) (D : Set ℕ) (Q₁ Q₂ : Protocol P) : Prop :=
  ∀ r, Adm t D r → ∀ i m v, DecidesAt Q₁ r i m v ↔ DecidesAt Q₂ r i m v

lemma EqOnAdm.sameDecisions (h : EqOnAdm t D Q₁ Q₂) : SameDecisions t D Q₁ Q₂ :=
  fun _ hr _ _ _ => h.decidesAt_iff hr

lemma SameDecisions.symm (h : SameDecisions t D Q₁ Q₂) : SameDecisions t D Q₂ Q₁ :=
  fun r hr i m v => (h r hr i m v).symm

lemma SameDecisions.decidesBy_iff (h : SameDecisions t D Q₁ Q₂) {r : Run P} (hr : Adm t D r)
    {i : P} {m : ℕ} : DecidesBy Q₁ r i m ↔ DecidesBy Q₂ r i m := by
  unfold DecidesBy
  simp only [h r hr]

lemma SameDecisions.solves (h : SameDecisions t D Q₁ Q₂) (hs : SolvesSetConsensus k t D Q₁) :
    SolvesSetConsensus k t D Q₂ where
  decision r hr i hi := by
    obtain ⟨m, v, hv⟩ := hs.decision r hr i hi
    exact ⟨m, v, (h r hr i m v).1 hv⟩
  validity r hr i m v hv := hs.validity r hr i m v ((h r hr i m v).2 hv)
  agreement r hr := by
    have := hs.agreement r hr
    simpa only [h r hr] using this

lemma SameDecisions.dominates_left (h : SameDecisions t D Q₁ Q₂) (hd : Dominates t D Q₁ Q₃) :
    Dominates t D Q₂ Q₃ :=
  fun r hr i m v hv => (h.decidesBy_iff hr).1 (hd r hr i m v hv)

lemma SameDecisions.dominates_right (h : SameDecisions t D Q₁ Q₂) (hd : Dominates t D Q₃ Q₁) :
    Dominates t D Q₃ Q₂ :=
  fun r hr i m v hv => hd r hr i m v ((h r hr i m v).2 hv)

lemma SameDecisions.unbeatable (h : SameDecisions t D Q₁ Q₂) (hu : Unbeatable k t D Q₁) :
    Unbeatable k t D Q₂ :=
  ⟨h.solves hu.1, fun Q hQ hdom =>
    h.dominates_left (hu.2 Q hQ (h.symm.dominates_right hdom))⟩

omit [Fintype P] in
lemma DecidesBy.mono' {Q : Protocol P} {r : Run P} {i : P} {m m' : ℕ} (h : DecidesBy Q r i m)
    (hm : m ≤ m') : DecidesBy Q r i m' := by
  obtain ⟨n, hn, v, hv⟩ := h
  exact ⟨n, hn.trans hm, v, hv⟩

lemma Dominates.trans (h₁ : Dominates t D Q₁ Q₂) (h₂ : Dominates t D Q₂ Q₃) :
    Dominates t D Q₁ Q₃ := by
  intro r hr i m v hv
  obtain ⟨n, hn, w, hw⟩ := h₂ r hr i m v hv
  exact DecidesBy.mono' (h₁ r hr i n w hw) hn

lemma Dominates.refl : Dominates t D Q₁ Q₁ :=
  fun _ _ _ _ v hv => ⟨_, le_rfl, v, hv⟩

end Transfer

/-! ### Agreement for consensus -/

/-- With `k = 1`, two correct processes decide the same value. -/
lemma agree_of_le_one [Fintype P] {t : ℕ} {D : Set ℕ} {Q : Protocol P}
    (hQ : SolvesSetConsensus 1 t D Q) {r : Run P} (hr : Adm t D r) {i j : P} {m m' v w : ℕ}
    (hi : ¬ r.Faulty i) (hj : ¬ r.Faulty j) (hv : DecidesAt Q r i m v)
    (hw : DecidesAt Q r j m' w) : v = w :=
  Set.encard_le_one_iff.1 (hQ.agreement r hr) v w ⟨i, m, hi, hv⟩ ⟨j, m', hj, hw⟩

/-- Knowledge of preconditions for Validity in a binary context: decided values have been seen. -/
lemma dec_mem_vals' [Fintype P] {k t : ℕ} {Q : Protocol P} (hQ : SolvesSetConsensus k t bin Q)
    {r : Run P} (hr : Adm t bin r) {i : P} {m u : ℕ} (hd : DecidesAt Q r i m u) :
    u ∈ vals r i m :=
  decided_mem_vals hQ zero_mem_bin one_mem_bin zero_ne_one hr hd

/-! ### The protocols `P_a` and `Opt_a` -/

open Classical in
/-- **Protocol `P_a`** (`P0` of §3 for `a = 0`): decide `a` once `K_i ∃a`, otherwise decide
`1 - a` at time `t + 1`. -/
noncomputable def pA [Fintype P] (a t : ℕ) : Protocol P where
  dec r i m := if a ∈ vals r i m then some a else if m = t + 1 then some (1 - a) else none
  dec_congr r r' i m h := by simp only [h.vals_eq]

open Classical in
/-- **Protocol `Opt_a`** (`Opt0` of §3 for `a = 0`, `Opt1` for `a = 1`): decide `a` once `K_i ∃a`,
otherwise decide `1 - a` as soon as there is no hidden path. -/
noncomputable def optA [Fintype P] (a : ℕ) : Protocol P where
  dec r i m := if a ∈ vals r i m then some a else if ¬ HiddenPath r i m then some (1 - a) else none
  dec_congr r r' i m h := by simp only [h.vals_eq, hiddenPath_iff_of_sameView h]

/-- `P0`. -/
noncomputable abbrev p0 [Fintype P] (t : ℕ) : Protocol P := pA 0 t
/-- `Opt0`. -/
noncomputable abbrev opt0 [Fintype P] : Protocol P := optA 0
/-- `Opt1`. -/
noncomputable abbrev opt1 [Fintype P] : Protocol P := optA 1

section Protocols

variable [Fintype P] {a t : ℕ} {r : Run P} {i : P} {m v : ℕ}

lemma optA_dec_eq_none : (optA a).dec r i m = none ↔ a ∉ vals r i m ∧ HiddenPath r i m := by
  unfold ParetoOptimalConsensus.optA; simp only
  split_ifs <;> simp_all

lemma decidesAt_optA (h : DecidesAt (optA a) r i m v) :
    (a ∈ vals r i m ∧ v = a) ∨ (a ∉ vals r i m ∧ ¬ HiddenPath r i m ∧ v = 1 - a) := by
  have h2 := h.2.1
  unfold UnbeatableSetConsensus.Protocol.dec ParetoOptimalConsensus.optA at h2
  simp only at h2
  split_ifs at h2 with h3 h4
  · cases h2; exact Or.inl ⟨h3, rfl⟩
  · cases h2; exact Or.inr ⟨h3, h4, rfl⟩

lemma decidesAt_pA (h : DecidesAt (pA a t) r i m v) :
    (a ∈ vals r i m ∧ v = a) ∨ (a ∉ vals r i m ∧ m = t + 1 ∧ v = 1 - a) := by
  have h2 := h.2.1
  unfold UnbeatableSetConsensus.Protocol.dec ParetoOptimalConsensus.pA at h2
  simp only at h2
  split_ifs at h2 with h3 h4
  · cases h2; exact Or.inl ⟨h3, rfl⟩
  · cases h2; exact Or.inr ⟨h3, h4, rfl⟩

lemma optA_dec_ne_none_of_mem (ha : a ∈ vals r i m) : (optA a).dec r i m ≠ none := by
  rw [Ne, optA_dec_eq_none]; tauto

lemma optA_dec_ne_none_of_not_hiddenPath (hh : ¬ HiddenPath r i m) :
    (optA a).dec r i m ≠ none := by
  rw [Ne, optA_dec_eq_none]; tauto

/-- `Opt_a`: every process alive at `f + 1` has decided by then. -/
lemma optA_decidesBy_faulty (ha : r.Alive i (r.faulty.card + 1)) :
    DecidesBy (optA a) r i (r.faulty.card + 1) :=
  decidesBy_of_dec ha (optA_dec_ne_none_of_not_hiddenPath not_hiddenPath_faulty)

/-- **`Opt_a` solves consensus** (for every `t`), with decisions by time `f + 1`. -/
theorem optA_solves (ha : a ∈ bin) : SolvesSetConsensus 1 t bin (optA a : Protocol P) where
  decision r _ i hi := by
    obtain ⟨m', -, v, hv⟩ := optA_decidesBy_faulty (a := a) (SyncCrash.Run.alive_of_not_faulty hi _)
    exact ⟨m', v, hv⟩
  validity r hr i m v hv := by
    rcases decidesAt_optA hv with ⟨h1, rfl⟩ | ⟨h1, -, rfl⟩
    · obtain ⟨j, -, hj⟩ := mem_vals.1 h1; exact ⟨j, hj⟩
    · obtain ⟨j, -, hj⟩ := mem_vals.1 (one_sub_mem_vals hr ha h1); exact ⟨j, hj⟩
  agreement r hr := by
    classical
    rw [Nat.cast_one, Set.encard_le_one_iff]
    rintro v w ⟨i, m, hi, hv⟩ ⟨j, m', hj, hw⟩
    -- a value `1 - a` decided by the no-hidden-path rule excludes any correct holder of `a`
    have key : ∀ {i j : P} {m m' : ℕ}, ¬ r.Faulty j → DecidesAt (optA a) r i m (1 - a) →
        DecidesAt (optA a) r j m' a → False := by
      intro i j m m' hj hi hja
      rcases decidesAt_optA hi with ⟨-, h⟩ | ⟨hn, hh, -⟩
      · exact one_sub_ne ha h
      rcases decidesAt_optA hja with ⟨hm, -⟩ | ⟨-, -, h⟩
      · obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 hh
        exact hn (vals_subset_of_not_hidden hℓ hnh hj m' hm)
      · exact one_sub_ne ha h.symm
    have hva : v = a ∨ v = 1 - a := by
      rcases decidesAt_optA hv with ⟨-, h⟩ | ⟨-, -, h⟩ <;> simp [h]
    have hwa : w = a ∨ w = 1 - a := by
      rcases decidesAt_optA hw with ⟨-, h⟩ | ⟨-, -, h⟩ <;> simp [h]
    rcases hva with rfl | rfl <;> rcases hwa with rfl | rfl
    · rfl
    · exact (key hi hw hv).elim
    · exact (key hj hv hw).elim
    · rfl

end Protocols

end Podc.ParetoOptimalConsensus
