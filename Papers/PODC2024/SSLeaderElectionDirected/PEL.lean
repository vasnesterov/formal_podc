import Papers.PODC2024.SSLeaderElectionDirected.Rounds

/-!
# Algorithm PEL = E ∘ A ∘ MI (Section 4.3): definition, termination and stabilization time

The three layers are instances of C-MAI composed by hierarchical collateral composition: a process
executes the action of `A` only if `MI` is disabled at it, and the action of `E` only if both `MI`
and `A` are disabled at it.

* `MI = C-MAI(IDSET, <, Id)`;
* `A = C-MAI(𝔹, <, I_A)` with `I_A(p) = (∀ q ∈ Γ⁻(p), q.MI.M = p.MI.M)`;
* `E = C-MAI(𝔹 × IDSET, <_lex, I_E)`. The paper uses `I_E(p) = (¬ p.A.M, p.MI.M)`
  (`fixed = false`). We also consider `I_E(p) = (¬ p.A.M, p.Id)` (`fixed = true`), which makes the
  leader the *only* process with input `(0, mid)`, as required by the unison algorithm of Section 5
  (see `Unison.lean`). Both variants solve leader election.

Main results here: `silent` (termination, from Lemma 1 + Theorem 1 in the paper) and `terminal_within`
(the stabilization time `3α + 3MAD + 6` rounds of Theorem 3, from Corollary 1 + Theorem 2).
We do not formalize the generic composition results (Lemma 1, Corollary 1); we prove their
instances for PEL directly: each layer is a `CMAI.Run` whose inputs become constant once the lower
layers have stabilized, and every round of PEL is a round of each such layer.
-/

set_option linter.unusedSectionVars false

open Cslib.SelfStabilization Relation

namespace Papers.PODC2024.SSLeaderElectionDirected

open CMAI

/-- The local state of a process in PEL: the states of its three C-MAI instances. -/
@[ext] structure PState (ID : Type*) (α : ℕ) where
  /-- instance `MI` (minimum identifier) -/
  mi : CState ID α
  /-- instance `A` (agreement bit) -/
  a : CState Bool α
  /-- instance `E` (election) -/
  e : CState (Bool ×ₗ ID) α

namespace PEL

variable {V : Type*} [Fintype V] (G : Digraph V) {ID : Type*} [LinearOrder ID] (α : ℕ)

/-- The `MI` part of a configuration. -/
def miC (γ : V → PState ID α) : V → CState ID α := fun q => (γ q).mi
/-- The `A` part of a configuration. -/
def aC (γ : V → PState ID α) : V → CState Bool α := fun q => (γ q).a
/-- The `E` part of a configuration. -/
def eC (γ : V → PState ID α) : V → CState (Bool ×ₗ ID) α := fun q => (γ q).e

variable {α}

open Classical in
/-- `I_A(p) = (∀ q ∈ Γ⁻(p), q.MI.M = p.MI.M)`. -/
noncomputable def IA (γ : V → PState ID α) (p : V) : Bool :=
  decide (∀ q, G.Adj q p → (γ q).mi.1.M = (γ p).mi.1.M)

/-- `I_E(p) = (¬ p.A.M, p.MI.M)` (paper, `fixed = false`) or `(¬ p.A.M, p.Id)` (`fixed = true`). -/
def IE (fixed : Bool) (ι : V → ID) (γ : V → PState ID α) (p : V) : Bool ×ₗ ID :=
  toLex (!(γ p).a.1.M, if fixed then ι p else (γ p).mi.1.M)

variable (α)

/-- `MI` is enabled at `p`. -/
def EnMI (ι : V → ID) (γ : V → PState ID α) (p : V) : Prop :=
  Enabled (CMAI.next G α ι) (miC α γ) p
/-- `A` is enabled at `p`. -/
def EnA (γ : V → PState ID α) (p : V) : Prop :=
  Enabled (CMAI.next G α (IA G γ)) (aC α γ) p
/-- `E` is enabled at `p`. -/
def EnE (fixed : Bool) (ι : V → ID) (γ : V → PState ID α) (p : V) : Prop :=
  Enabled (CMAI.next G α (IE fixed ι γ)) (eC α γ) p

open Classical in
/-- Algorithm PEL = E ∘ A ∘ MI (hierarchical collateral composition). -/
noncomputable def next (fixed : Bool) (ι : V → ID) (γ : V → PState ID α) (p : V) : PState ID α :=
  if EnMI G α ι γ p then { γ p with mi := CMAI.next G α ι (miC α γ) p }
  else if EnA G α γ p then { γ p with a := CMAI.next G α (IA G γ) (aC α γ) p }
  else { γ p with e := CMAI.next G α (IE fixed ι γ) (eC α γ) p }

variable {α} in
/-- The leader appointed by `p`: `L(p) = p.E.M.R`. -/
def leader (γ : V → PState ID α) (p : V) : ID := (ofLex (γ p).e.1.M).2

variable {G α} {fixed : Bool} {ι : V → ID}

theorem not_enabled_iff {next' : (V → CState ID α) → V → CState ID α} {γ : V → CState ID α}
    {p : V} : ¬ Enabled next' γ p ↔ next' γ p = γ p := by
  simp [Enabled]

theorem next_mi (γ : V → PState ID α) (p : V) :
    (next G α fixed ι γ p).mi = CMAI.next G α ι (miC α γ) p := by
  unfold next
  split_ifs with h1 h2
  · rfl
  · simp only [EnMI, Enabled, ne_eq, not_not] at h1; exact h1.symm
  · simp only [EnMI, Enabled, ne_eq, not_not] at h1; exact h1.symm

open Classical in
theorem next_a (γ : V → PState ID α) (p : V) :
    (next G α fixed ι γ p).a =
      if EnMI G α ι γ p then (γ p).a else CMAI.next G α (IA G γ) (aC α γ) p := by
  unfold next
  split_ifs with h1 h2
  · rfl
  · rfl
  · simp only [EnA, Enabled, ne_eq, not_not] at h2; exact h2.symm

open Classical in
theorem next_e (γ : V → PState ID α) (p : V) :
    (next G α fixed ι γ p).e =
      if EnMI G α ι γ p ∨ EnA G α γ p then (γ p).e
      else CMAI.next G α (IE fixed ι γ) (eC α γ) p := by
  by_cases h1 : EnMI G α ι γ p
  · simp [next, h1]
  · by_cases h2 : EnA G α γ p
    · simp [next, h1, h2]
    · simp [next, h1, h2]

theorem next_eq_of_not (γ : V → PState ID α) (p : V) (h1 : ¬ EnMI G α ι γ p)
    (h2 : ¬ EnA G α γ p) (h3 : ¬ EnE G α fixed ι γ p) : next G α fixed ι γ p = γ p := by
  simp only [EnE, Enabled, ne_eq, not_not] at h3
  unfold next
  rw [ite_eq_right h1, ite_eq_right h2]
  ext1 <;> simp [h3, eC]

theorem enabled_iff {γ : V → PState ID α} {p : V} :
    Enabled (next G α fixed ι) γ p ↔ EnMI G α ι γ p ∨ EnA G α γ p ∨ EnE G α fixed ι γ p := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h (next_eq_of_not γ p hc.1 hc.2.1 hc.2.2)
  · intro h heq
    have hmi := congrArg PState.mi heq
    have ha := congrArg PState.a heq
    have he := congrArg PState.e heq
    rw [next_mi] at hmi
    rw [next_a] at ha
    rw [next_e] at he
    rcases h with h | h | h
    · exact h hmi
    · have h1 : ¬ EnMI G α ι γ p := fun h1 => h1 hmi
      rw [ite_eq_right h1] at ha
      exact h ha
    · have h1 : ¬ EnMI G α ι γ p := fun h1 => h1 hmi
      rw [ite_eq_right h1] at ha
      have h2 : ¬ EnA G α γ p := fun h2 => h2 ha
      rw [ite_eq_right (by tauto)] at he
      exact h he

theorem terminal_iff {γ : V → PState ID α} :
    Terminal (next G α fixed ι) γ ↔ Terminal (CMAI.next G α ι) (miC α γ) ∧
      Terminal (CMAI.next G α (IA G γ)) (aC α γ) ∧
      Terminal (CMAI.next G α (IE fixed ι γ)) (eC α γ) := by
  have key : ∀ p, next G α fixed ι γ p = γ p ↔
      ¬ EnMI G α ι γ p ∧ ¬ EnA G α γ p ∧ ¬ EnE G α fixed ι γ p := fun p => by
    have := (enabled_iff (G := G) (α := α) (fixed := fixed) (ι := ι) (γ := γ) (p := p)).not
    simp only [Enabled, ne_eq, not_not, not_or] at this
    exact this
  simp only [Terminal, key]
  simp only [EnMI, EnA, EnE, Enabled, ne_eq, not_not]
  constructor
  · intro h; exact ⟨fun p => (h p).1, fun p => (h p).2.1, fun p => (h p).2.2⟩
  · intro h p; exact ⟨h.1 p, h.2.1 p, h.2.2 p⟩

theorem IA_congr {γ γ' : V → PState ID α} (h : ∀ q, (γ q).mi = (γ' q).mi) :
    IA G γ = IA G γ' := by
  funext p; simp [IA, h]

theorem IE_congr {γ γ' : V → PState ID α} (h1 : ∀ q, (γ q).mi = (γ' q).mi)
    (h2 : ∀ q, (γ q).a = (γ' q).a) : IE fixed ι γ = IE fixed ι γ' := by
  funext p; simp [IE, h1, h2]

/-! ### Each layer is a run of C-MAI -/

variable {e : ℕ → V → PState ID α} {S : ℕ → Set V}

theorem runEnabled_mi_iff {t : ℕ} {p : V} :
    RunEnabled G α (fun _ => ι) (fun t q => (e t q).mi.1) t p ↔ EnMI G α ι (e t) p :=
  CMAI.enabled_iff.symm

theorem runEnabled_a_iff {t : ℕ} {p : V} :
    RunEnabled G α (fun t => IA G (e t)) (fun t q => (e t q).a.1) t p ↔ EnA G α (e t) p :=
  CMAI.enabled_iff.symm

theorem runEnabled_e_iff {t : ℕ} {p : V} :
    RunEnabled G α (fun t => IE fixed ι (e t)) (fun t q => (e t q).e.1) t p ↔
      EnE G α fixed ι (e t) p :=
  CMAI.enabled_iff.symm

theorem runMI (h : IsUnfairRun (next G α fixed ι) e S) :
    Run G α (fun _ => ι) (fun t q => (e t q).mi.1) S where
  move t p hp := by rw [h.move t p hp, next_mi]; rfl
  stay t p hp := by rw [h.stay t p hp]

/-- Processes that execute (or might execute) the action of `A` at step `t`. -/
def moversA (ι : V → ID) (e : ℕ → V → PState ID α) (S : ℕ → Set V) (t : ℕ) : Set V :=
  {p | p ∈ S t ∧ ¬ EnMI G α ι (e t) p}

/-- Processes that execute (or might execute) the action of `E` at step `t`. -/
def moversE (ι : V → ID) (e : ℕ → V → PState ID α) (S : ℕ → Set V) (t : ℕ) : Set V :=
  {p | p ∈ S t ∧ ¬ EnMI G α ι (e t) p ∧ ¬ EnA G α (e t) p}

theorem runA (h : IsUnfairRun (next G α fixed ι) e S) :
    Run G α (fun t => IA G (e t)) (fun t q => (e t q).a.1) (moversA (G := G) ι e S) where
  move t p hp := by rw [h.move t p hp.1, next_a, ite_eq_right hp.2]; rfl
  stay t p hp := by
    by_cases hS : p ∈ S t
    · have hmi : EnMI G α ι (e t) p := by
        by_contra hc; exact hp ⟨hS, hc⟩
      rw [h.move t p hS, next_a, ite_eq_left hmi]
    · rw [h.stay t p hS]

theorem runE (h : IsUnfairRun (next G α fixed ι) e S) :
    Run G α (fun t => IE fixed ι (e t)) (fun t q => (e t q).e.1) (moversE (G := G) ι e S) where
  move t p hp := by
    rw [h.move t p hp.1, next_e, ite_eq_right (by rintro (h' | h') <;> [exact hp.2.1 h'; exact hp.2.2 h'])]
    rfl
  stay t p hp := by
    by_cases hS : p ∈ S t
    · have hor : EnMI G α ι (e t) p ∨ EnA G α (e t) p := by
        by_contra hc; push Not at hc; exact hp ⟨hS, hc.1, hc.2⟩
      rw [h.move t p hS, next_e, ite_eq_left hor]
    · rw [h.stay t p hS]

/-! ### Termination (silence) -/

/-- **Termination part of Theorem 3** (Lemma 1 + Theorem 1 of the paper, specialised): every
execution of PEL under the distributed unfair daemon is finite. -/
theorem silent (h : IsUnfairRun (next G α fixed ι) e S) :
    ∃ t, Terminal (next G α fixed ι) (e t) := by
  obtain ⟨T1, -, h1⟩ := (runMI h).eventually_const (T := 0) (fun _ _ => rfl)
  have hmi : ∀ t, T1 ≤ t → ∀ q, (e t q).mi = (e T1 q).mi := fun t ht q =>
    Subtype.ext (congrFun (h1 t ht) q)
  obtain ⟨T2, hT12, h2⟩ := (runA h).eventually_const (T := T1)
    (fun t ht => IA_congr (hmi t ht))
  have ha : ∀ t, T2 ≤ t → ∀ q, (e t q).a = (e T2 q).a := fun t ht q =>
    Subtype.ext (congrFun (h2 t ht) q)
  obtain ⟨T3, hT23, h3⟩ := (runE h).eventually_const (T := T2)
    (fun t ht => IE_congr (fun q => (hmi t (by omega) q).trans (hmi T2 hT12 q).symm) (ha t ht))
  refine ⟨T3, h.terminal_of_const fun t ht => funext fun p => PState.ext ?_ ?_ ?_⟩
  · exact (hmi t (by omega) p).trans (hmi T3 (by omega) p).symm
  · exact (ha t (by omega) p).trans (ha T3 (by omega) p).symm
  · exact Subtype.ext (congrFun (h3 t ht) p)

/-! ### Stabilization time -/

/-- **Time part of Theorem 3** (Corollary 1 + Theorem 2 of the paper, specialised): if
`MAD ≤ m ≤ α`, every execution of PEL under the distributed unfair daemon is terminal after at most
`3α + 3m + 6` rounds (for any round boundaries `r`, in particular the paper's rounds). -/
theorem terminal_within (h : IsUnfairRun (next G α fixed ι) e S) {m : ℕ} (hm : MADLe G m)
    (hmα : m ≤ α) {r : ℕ → ℕ} (hr : RoundBounds (next G α fixed ι) e S r) :
    ∀ t, r (3 * (α + m + 2)) ≤ t → Terminal (next G α fixed ι) (e t) := by
  set X := α + m + 2
  have hrmono := hr.mono
  have hα : MADLe G α := hm.mono hmα
  -- layer MI
  have hMI := (runMI h).target_within (T := 0) (fun _ _ => rfl) (fun t _ p => (e t p).mi.2) hm hmα
    hr.1 (fun i => ⟨(hr.2 i).1, fun p hp => by
      obtain ⟨u, h1, h2, h3⟩ := (hr.2 i).2 p (enabled_iff.mpr (Or.inl (runEnabled_mi_iff.mp hp)))
      refine ⟨u, h1, h2, h3.imp_right fun h' h'' => h' (enabled_iff.mpr (Or.inl (runEnabled_mi_iff.mp h'')))⟩⟩)
  have hmi : ∀ t, r X ≤ t → ∀ q, (e t q).mi = (e (r X) q).mi := fun t ht q =>
    Subtype.ext ((hMI t ht q).trans (hMI (r X) le_rfl q).symm)
  have hnMI : ∀ t, r X ≤ t → ∀ p, ¬ EnMI G α ι (e t) p := by
    intro t ht p hen
    apply hen
    have hK : (fun q => (miC α (e t) q).1) = target G ι := funext (hMI t ht)
    show CMAI.next G α ι (miC α (e t)) p = miC α (e t) p
    apply Subtype.ext
    show bestKey G α ι (fun q => (miC α (e t) q).1) p = (miC α (e t) p).1
    rw [hK]; exact (bestKey_target hα p).trans (hMI t ht p).symm
  -- layer A
  have hA := (runA h).target_within (T := r X) (fun t ht => IA_congr (hmi t ht))
    (fun t _ p => (e t p).a.2) hm hmα (r := fun i => r (X + i)) (by simp)
    (fun i => ⟨(hr.2 (X + i)).1, fun p hp => by
      obtain ⟨u, h1, h2, h3⟩ := (hr.2 (X + i)).2 p (enabled_iff.mpr (Or.inr (Or.inl (runEnabled_a_iff.mp hp))))
      refine ⟨u, h1, h2, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl ⟨h3, hnMI u (le_trans (hrmono (by omega)) h1) p⟩
      · exact Or.inr fun h'' => h3 (enabled_iff.mpr (Or.inr (Or.inl (runEnabled_a_iff.mp h''))))⟩)
  have ha : ∀ t, r (X + X) ≤ t → ∀ q, (e t q).a = (e (r (X + X)) q).a := fun t ht q =>
    Subtype.ext ((hA t (by simpa using ht) q).trans (hA (r (X + X)) le_rfl q).symm)
  have hnA : ∀ t, r (X + X) ≤ t → ∀ p, ¬ EnA G α (e t) p := by
    intro t ht p hen
    apply hen
    have hIA : IA G (e t) = IA G (e (r X)) := IA_congr (hmi t (le_trans (hrmono (by omega)) ht))
    have hK : (fun q => (aC α (e t) q).1) = target G (IA G (e (r X))) :=
      funext (hA t (by simpa using ht))
    show CMAI.next G α (IA G (e t)) (aC α (e t)) p = aC α (e t) p
    apply Subtype.ext
    show bestKey G α (IA G (e t)) (fun q => (aC α (e t) q).1) p = (aC α (e t) p).1
    rw [hK, hIA]; exact (bestKey_target hα p).trans (hA t (by simpa using ht) p).symm
  -- layer E
  have hIEc : ∀ t, r (X + X) ≤ t → IE fixed ι (e t) = IE fixed ι (e (r (X + X))) := fun t ht =>
    IE_congr (fun q => (hmi t (le_trans (hrmono (by omega)) ht) q).trans
      (hmi _ (hrmono (by omega)) q).symm) (ha t ht)
  have hE := (runE h).target_within (T := r (X + X)) hIEc
    (fun t _ p => (e t p).e.2) hm hmα (r := fun i => r (X + X + i)) (by simp)
    (fun i => ⟨(hr.2 (X + X + i)).1, fun p hp => by
      obtain ⟨u, h1, h2, h3⟩ := (hr.2 (X + X + i)).2 p (enabled_iff.mpr (Or.inr (Or.inr (runEnabled_e_iff.mp hp))))
      refine ⟨u, h1, h2, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl ⟨h3, hnMI u (le_trans (hrmono (by omega)) h1) p,
          hnA u (le_trans (hrmono (by omega)) h1) p⟩
      · exact Or.inr fun h'' => h3 (enabled_iff.mpr (Or.inr (Or.inr (runEnabled_e_iff.mp h''))))⟩)
  intro t ht p
  apply next_eq_of_not
  · exact hnMI t (le_trans (hrmono (by omega)) ht) p
  · exact hnA t (le_trans (hrmono (by omega)) ht) p
  · intro hen
    apply hen
    have hK : (fun q => (eC α (e t) q).1) = target G (IE fixed ι (e (r (X + X)))) :=
      funext (hE t (by rw [show X + X + (α + m + 2) = 3 * (α + m + 2) by omega]; exact ht))
    show CMAI.next G α (IE fixed ι (e t)) (eC α (e t)) p = eC α (e t) p
    apply Subtype.ext
    show bestKey G α (IE fixed ι (e t)) (fun q => (eC α (e t) q).1) p = (eC α (e t) p).1
    rw [hK, hIEc t (le_trans (hrmono (by omega)) ht)]
    exact (bestKey_target hα p).trans (congrFun hK p).symm

end PEL

end Papers.PODC2024.SSLeaderElectionDirected
