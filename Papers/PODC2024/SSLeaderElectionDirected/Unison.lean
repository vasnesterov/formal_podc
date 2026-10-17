import Papers.PODC2024.SSLeaderElectionDirected.Necessity
import Podc.Foundations.Data.Fin.Cyclic

/-!
# Synchronous unison (Section 5)

* `UAlg`, `SPSU`: algorithms with a clock output in `[0..K-1]` (here `K = k + 1`) and the
  synchronous-unison specification (all clocks equal, all clocks incremented modulo `K` at every
  synchronous step).
* `theorem4` (Theorem 4, proved in the paper only by reference to [ACDD23]): a self-stabilizing
  synchronous unison under the synchronous daemon requires at most one source component.
* `U.next` : Algorithm `U(K) = U-DAG(K) ∘ PEL` (Algorithm 2).
* **`paper_unison_not_selfStab`**: with the paper's `I_E(p) = (¬ p.A.M, p.MI.M)`, *every* process of
  the source component (and every process whose ancestors all have identifier `≥ mid`) gets
  `E.d = 0` in a terminal configuration of PEL, contrary to the claim `E.d = ‖ℓ, p‖` used in
  Lemmas 16 and 19. Such processes increment their clocks independently, so `U(K)` is **not**
  self-stabilizing as soon as the source component has two processes (e.g. on every strongly
  connected network with `n ≥ 2`). `twoCycle_paper_unison_fails` (`Examples.lean`) instantiates
  this on a 2-node network.
* With the fixed input `I_E(p) = (¬ p.A.M, p.Id)` the proof of the paper goes through:
  `theorem5` (self-stabilization) and `theorem5_time` (stabilization within `3α + 4·MAD + 6`
  synchronous steps), and `corollary5` (unique source component ⇔ unison solvable).
-/

set_option linter.unusedSectionVars false

open Cslib.SelfStabilization Relation

namespace Papers.PODC2024.SSLeaderElectionDirected

universe u

variable {V : Type*} [Fintype V] {G : Digraph V}

/-- Synchronous unison specification `SP_SU` with period `K = k + 1`. -/
def SPSU {Q : Type*} {k : ℕ} (clk : (V → Q) → V → Fin (k + 1)) (e : ℕ → V → Q) : Prop :=
  (∀ t p q, clk (e t) p = clk (e t) q) ∧ ∀ t p, clk (e (t + 1)) p = clk (e t) p + 1

/-- **Theorem 4** (necessary condition for synchronous unison; the paper refers to [ACDD23]).
If a deterministic local algorithm is self-stabilizing for the synchronous unison (period `K ≥ 2`)
under the synchronous daemon for some identifier assignment, then `G` has at most one source
component. -/
theorem theorem4 {ID Q : Type*} {k : ℕ} (hk : 1 ≤ k) (next : (V → ID) → (V → Q) → V → Q)
    (hloc : IsLocal G next) (clk : (V → Q) → V → Fin (k + 1))
    (hclk : ∀ γ γ' p, γ p = γ' p → clk γ p = clk γ' p) (ι : V → ID)
    (hss : SelfStab (IsSyncExec (next ι)) (SPSU clk)) {S₁ S₂ : Set V}
    (h₁ : G.IsSourceComponent S₁) (h₂ : G.IsSourceComponent S₂) : S₁ = S₂ := by
  classical
  by_contra hne
  have hdisj := h₁.disjoint h₂ hne
  obtain ⟨L, ⟨γ, hγ⟩, hconv, hcorr⟩ := hss
  let e : ℕ → V → Q := fun t => (next ι)^[t] γ
  have he : IsSyncExec (next ι) e := isSyncExec_iterate γ
  have hsp := hcorr e he hγ
  -- shift the configuration of `S₂` by one step
  let π : V → Q := fun p => if p ∈ S₂ then e 1 p else γ p
  let e' : ℕ → V → Q := fun t => (next ι)^[t] π
  have he' : IsSyncExec (next ι) e' := isSyncExec_iterate π
  have hag₁ := syncExec_agree hloc h₁.closed (fun _ _ => rfl) he he' fun p hp => by
    simp only [π, e', Function.iterate_zero, id, ite_eq_right (Set.disjoint_left.mp hdisj hp)]; rfl
  have hag₂ := syncExec_agree hloc h₂.closed (fun _ _ => rfl) (he.shift 1) he' fun p hp => by
    simp only [π, e', Function.iterate_zero, id, ite_eq_left hp]
  obtain ⟨t₀, ht₀⟩ := hconv e' he'
  have hsp' := hcorr (fun t => e' (t₀ + t)) (he'.shift t₀) ht₀
  obtain ⟨p₁, hp₁⟩ := h₁.nonempty
  obtain ⟨p₂, hp₂⟩ := h₂.nonempty
  have heq := hsp'.1 0 p₁ p₂
  simp only [Nat.add_zero] at heq
  rw [hclk _ _ p₁ (hag₁ t₀ p₁ hp₁).symm, hclk _ _ p₂ (hag₂ t₀ p₂ hp₂).symm] at heq
  have hstep : clk (e (1 + t₀)) p₂ = clk (e t₀) p₂ + 1 := by
    have h1t : 1 + t₀ = t₀ + 1 := Nat.add_comm 1 t₀
    simp only [h1t]; exact hsp.2 t₀ p₂
  rw [hstep, hsp.1 t₀ p₂ p₁] at heq
  exact Fin.add_one_ne_self (by omega) _ heq.symm

/-! ### Algorithm U(K) -/

/-- The local state of `U(K)`: the state of PEL and a clock in `[0..K-1]`, `K = k + 1`. -/
@[ext] structure UState (ID : Type*) (α k : ℕ) where
  /-- the variables of PEL -/
  pel : PState ID α
  /-- `p.Clock` -/
  clock : Fin (k + 1)

namespace U

variable (G) {ID : Type*} [LinearOrder ID] (α k : ℕ)

/-- The PEL part of a configuration of `U(K)`. -/
def pelC {α k : ℕ} (γ : V → UState ID α k) : V → PState ID α := fun q => (γ q).pel

/-- `p.E.d`. -/
def ed {α k : ℕ} (γ : V → UState ID α k) (p : V) : ℕ := (γ p).pel.e.1.d

variable {α k} in
open Classical in
/-- `Values(p) = {q.Clock | q ∈ Γ⁻(p) ∧ q.E.d < p.E.d} ∪ {K - 1}`. -/
noncomputable def values (γ : V → UState ID α k) (p : V) : Finset (Fin (k + 1)) :=
  insert (Fin.last k) ((Finset.univ.filter fun q => G.Adj q p ∧ ed γ q < ed γ p).image
    fun q => (γ q).clock)

variable {α k} in
/-- `NextValue(p)`. -/
noncomputable def nextValue (γ : V → UState ID α k) (p : V) : Fin (k + 1) :=
  if ed γ p = 0 then (γ p).clock + 1 else (values G γ p).min' (Finset.insert_nonempty _ _) + 1

open Classical in
/-- Algorithm `U(K) = U-DAG(K) ∘ PEL` (`fixed = false`: the paper's PEL; `fixed = true`: PEL with
the corrected input of `E`). -/
noncomputable def next (fixed : Bool) (ι : V → ID) (γ : V → UState ID α k) (p : V) :
    UState ID α k :=
  if Enabled (PEL.next G α fixed ι) (pelC γ) p then ⟨PEL.next G α fixed ι (pelC γ) p, (γ p).clock⟩
  else ⟨(γ p).pel, nextValue G γ p⟩

/-- The clock output. -/
def clk {α k : ℕ} (γ : V → UState ID α k) (p : V) : Fin (k + 1) := (γ p).clock

variable {G α k} {fixed : Bool} {ι : V → ID}

theorem next_pel (γ : V → UState ID α k) (p : V) :
    (next G α k fixed ι γ p).pel = PEL.next G α fixed ι (pelC γ) p := by
  unfold next
  split_ifs with h
  · rfl
  · simp only [Enabled, ne_eq, not_not] at h; exact h.symm

theorem next_clock_of_not {γ : V → UState ID α k} {p : V}
    (h : ¬ Enabled (PEL.next G α fixed ι) (pelC γ) p) :
    (next G α k fixed ι γ p).clock = nextValue G γ p := by
  unfold next; rw [ite_eq_right h]

/-- The PEL part of a synchronous execution of `U(K)` is a synchronous execution of PEL. -/
theorem isSyncExec_pel {e : ℕ → V → UState ID α k} (he : IsSyncExec (next G α k fixed ι) e) :
    IsSyncExec (PEL.next G α fixed ι) (fun t => pelC (e t)) := fun t => by
  funext p
  simp only [pelC]
  rw [he t, next_pel]

/-- One synchronous step from a configuration whose PEL part is terminal: the PEL part does not
change, and the clocks follow `NextValue`. -/
theorem step_of_terminal {γ : V → UState ID α k} (hγ : Terminal (PEL.next G α fixed ι) (pelC γ))
    (p : V) : (next G α k fixed ι γ p).pel = (γ p).pel ∧
      (next G α k fixed ι γ p).clock = nextValue G γ p := by
  have hn : ¬ Enabled (PEL.next G α fixed ι) (pelC γ) p := fun h => h (hγ p)
  exact ⟨by rw [next_pel]; exact hγ p, next_clock_of_not hn⟩

/-- `min Values(p) = c` when all clocks in `Values(p) \ {K-1}` equal `c` and there is one. -/
theorem min_values_eq {γ : V → UState ID α k} {p : V} {c : Fin (k + 1)}
    (hall : ∀ q, G.Adj q p → ed γ q < ed γ p → (γ q).clock = c)
    (hex : ∃ q, G.Adj q p ∧ ed γ q < ed γ p) :
    (values G γ p).min' (Finset.insert_nonempty _ _) = c := by
  classical
  obtain ⟨q, hq, hqd⟩ := hex
  apply le_antisymm
  · apply Finset.min'_le
    simp only [values, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact Or.inr ⟨q, ⟨hq, hqd⟩, hall q hq hqd⟩
  · apply Finset.le_min'
    intro v hv
    simp only [values, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv
    rcases hv with rfl | ⟨q', ⟨hq', hqd'⟩, rfl⟩
    · exact Fin.le_last c
    · exact (hall q' hq' hqd').ge

/-! ### The counterexample for the paper's `U(K)` -/

/-- Every ancestor of `x` has an identifier at least as large as some identifier of `SC`, i.e.
`≥ mid`. Holds for all processes of `SC`, and for *all* processes when the globally smallest
identifier lies in `SC`. -/
def LowAnc (G : Digraph V) (SC : Set V) (ι : V → ID) (x : V) : Prop :=
  ∀ q, G.Reachable q x → ∃ s ∈ SC, ι s ≤ ι q

theorem lowAnc_of_mem {SC : Set V} (hSC : G.IsSourceComponent SC) {x : V} (hx : x ∈ SC) :
    LowAnc G SC ι x := fun q hq =>
  ⟨q, Digraph.mem_of_reachable_of_closed hSC.closed hq hx, le_rfl⟩

theorem lowAnc_of_min {SC : Set V} {ℓ : V} (hℓ : ℓ ∈ SC) (hmin : ∀ q, ι ℓ ≤ ι q) (x : V) :
    LowAnc G SC ι x := fun q _ => ⟨ℓ, hℓ, hmin q⟩

section Counterexample

variable {SC : Set V} (hSC : G.IsSourceComponent SC)
  (huniq : ∀ S, G.IsSourceComponent S → S = SC) (hα : MADLe G α)
include hSC huniq hα

/-- In every terminal configuration of the paper's PEL, all processes of the source component have
`E.d = 0`. -/
theorem paper_ed_eq_zero {γ : V → PState ID α} (hγ : Terminal (PEL.next G α false ι) γ) {x : V}
    (hx : LowAnc G SC ι x) : (γ x).e.1.d = 0 := by
  obtain ⟨ℓ, hℓ, hℓmin⟩ := PEL.exists_mid (ι := ι) hSC
  have h1 : (γ x).mi.1.M = ι ℓ := by
    rw [(PEL.terminal_keys hα hγ).1 x]
    refine CMAI.minI_eq (fun q hq => ?_) ⟨ℓ, PEL.anc_mid hSC huniq hℓ x, rfl⟩
    obtain ⟨s, hs, hsq⟩ := hx q hq
    exact (hℓmin s hs).trans hsq
  rw [(PEL.terminal_keys hα hγ).2.2 x]
  simp only [CMAI.target]
  apply (CMAI.mind_eq_zero_iff (G := G)).mpr
  have h15 := PEL.lemma15 hSC huniq hℓ hℓmin hα hγ x
  rw [(PEL.terminal_keys hα hγ).2.2 x] at h15
  simp only [CMAI.target] at h15
  rw [h15]
  have h2 := (PEL.lemma14 hSC huniq hℓ hℓmin hα hγ x).mpr h1
  simp [PEL.IE, h1, h2]

/-- Every configuration has a terminal PEL successor (PEL is silent). -/
theorem exists_terminal_pel (fixed : Bool) (γ₀ : V → PState ID α) :
    ∃ γ, Terminal (PEL.next G α fixed ι) γ := by
  obtain ⟨t, ht⟩ := PEL.silent (isSyncExec_iterate (next := PEL.next G α fixed ι) γ₀).isUnfairRun
  exact ⟨_, ht⟩

/-- **The paper's `U(K)` is not self-stabilizing** (Theorem 5 fails) as soon as two distinct
processes `p₁, p₂` have only ancestors with identifiers `≥ mid` (`LowAnc`), for every period
`K ≥ 2` and every `α ≥ MAD`. This covers every network whose source component has two processes,
and every network with `n ≥ 2` in which the globally smallest identifier lies in the source
component (`paper_unison_not_selfStab_of_min`). -/
theorem paper_unison_not_selfStab_gen (hk : 1 ≤ k) {p₁ p₂ : V} (h₁ : LowAnc G SC ι p₁)
    (h₂ : LowAnc G SC ι p₂) (hne : p₁ ≠ p₂) :
    ¬ SelfStab (IsSyncExec (next G α k false ι)) (SPSU clk) := by
  classical
  rintro ⟨L, -, hconv, hcorr⟩
  -- a terminal configuration of PEL
  obtain ⟨γP, hγP⟩ := exists_terminal_pel hSC huniq hα (ι := ι) false
    (fun p => ⟨⟨⟨ι p, 0⟩, Nat.zero_le _⟩, ⟨⟨true, 0⟩, Nat.zero_le _⟩,
      ⟨⟨toLex (true, ι p), 0⟩, Nat.zero_le _⟩⟩)
  let γ₀ : V → UState ID α k := fun p => ⟨γP p, if p = p₂ then 1 else 0⟩
  let e : ℕ → V → UState ID α k := fun t => (next G α k false ι)^[t] γ₀
  have he : IsSyncExec (next G α k false ι) e := isSyncExec_iterate γ₀
  -- the PEL part stays `γP`
  have hpel : ∀ t, pelC (e t) = γP := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext p
      have := (step_of_terminal (ih ▸ hγP) p).1
      simp only [pelC] at this ⊢
      rw [he t, this]
      exact congrFun ih p
  -- processes with `E.d = 0` increment their own clock
  have hlow : ∀ x, x = p₁ ∨ x = p₂ → LowAnc G SC ι x := by
    rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  have hinc : ∀ t x, x = p₁ ∨ x = p₂ → (e (t + 1) x).clock = (e t x).clock + 1 := by
    intro t x hx
    rw [he t, (step_of_terminal ((hpel t).symm ▸ hγP) x).2]
    have hd : ed (e t) x = 0 := by
      have := paper_ed_eq_zero hSC huniq hα hγP (hlow x hx)
      simp only [ed]; rw [show (e t x).pel = γP x from congrFun (hpel t) x]; exact this
    simp [nextValue, hd]
  have hdiff : ∀ t, (e t p₂).clock = (e t p₁).clock + 1 := by
    intro t
    induction t with
    | zero => simp [e, γ₀, hne]
    | succ t ih => rw [hinc t p₂ (Or.inr rfl), hinc t p₁ (Or.inl rfl), ih]
  obtain ⟨t₀, ht₀⟩ := hconv e he
  have hsp := hcorr (fun t => e (t₀ + t)) (he.shift t₀) ht₀
  have := hsp.1 0 p₂ p₁
  simp only [clk, Nat.add_zero] at this
  rw [hdiff t₀] at this
  exact Fin.add_one_ne_self (by omega) _ this

/-- The paper's `U(K)` fails on every network whose source component has two distinct
processes. -/
theorem paper_unison_not_selfStab (hk : 1 ≤ k) {p₁ p₂ : V} (h₁ : p₁ ∈ SC) (h₂ : p₂ ∈ SC)
    (hne : p₁ ≠ p₂) :
    ¬ SelfStab (IsSyncExec (next G α k false ι)) (SPSU clk) :=
  paper_unison_not_selfStab_gen hSC huniq hα hk (lowAnc_of_mem hSC h₁) (lowAnc_of_mem hSC h₂) hne

/-- The paper's `U(K)` fails on every network with `n ≥ 2` in which the process with the globally
smallest identifier belongs to the source component (e.g. the dipath `0 → 1`). -/
theorem paper_unison_not_selfStab_of_min (hk : 1 ≤ k) {ℓ : V} (hℓ : ℓ ∈ SC)
    (hmin : ∀ q, ι ℓ ≤ ι q) {p₁ p₂ : V} (hne : p₁ ≠ p₂) :
    ¬ SelfStab (IsSyncExec (next G α k false ι)) (SPSU clk) :=
  paper_unison_not_selfStab_gen hSC huniq hα hk (lowAnc_of_min hℓ hmin p₁)
    (lowAnc_of_min hℓ hmin p₂) hne

end Counterexample

/-! ### The corrected `U(K)` (Theorem 5) -/

section Fixed

variable {SC : Set V} (hSC : G.IsSourceComponent SC)
  (huniq : ∀ S, G.IsSourceComponent S → S = SC) (hα : MADLe G α) (hι : Function.Injective ι)
  {ℓ : V} (hℓ : ℓ ∈ SC) (hℓmin : ∀ x ∈ SC, ι ℓ ≤ ι x)
include hSC huniq hα hι hℓ hℓmin

/-- With the corrected `I_E`, in a terminal configuration of PEL, `E.d` is the distance from the
leader `ℓ` (in the sense of `Mind`), and the leader is the only process with `E.d = 0`. -/
theorem fixed_ed {γ : V → PState ID α} (hγ : Terminal (PEL.next G α true ι) γ) :
    (∀ p, (γ p).e.1.d = 0 ↔ p = ℓ) ∧
      ∀ p m, (γ p).e.1.d = m + 1 → ∃ q, G.Adj q p ∧ (γ q).e.1.d = m := by
  obtain ⟨-, -, he⟩ := PEL.terminal_keys hα hγ
  have h15 : ∀ p, CMAI.minI G (PEL.IE true ι γ) p = toLex (false, ι ℓ) := fun p => by
    have := PEL.lemma15 hSC huniq hℓ hℓmin hα hγ p
    rw [he p] at this; exact this
  have hIEℓ : PEL.IE true ι γ ℓ = toLex (false, ι ℓ) := by
    have h1 := PEL.corollary4 hSC huniq hℓ hℓmin hα hγ hℓ
    have h2 := (PEL.lemma14 hSC huniq hℓ hℓmin hα hγ ℓ).mpr h1
    simp [PEL.IE, h2]
  refine ⟨fun p => ?_, fun p m hm => ?_⟩
  · rw [he p]
    simp only [CMAI.target]
    rw [CMAI.mind_eq_zero_iff, h15]
    constructor
    · intro h
      simp only [PEL.IE, ite_true, toLex_inj, Prod.mk.injEq] at h
      exact hι h.2
    · rintro rfl; exact hIEℓ
  · rw [he p] at hm
    simp only [CMAI.target] at hm
    obtain ⟨q, hq, -, hmq⟩ := CMAI.exists_pred_of_mind hm
    exact ⟨q, hq, by rw [he q]; exact hmq⟩

/-- `E.d ≤ MAD` in a terminal configuration. -/
theorem fixed_ed_le {γ : V → PState ID α} (hγ : Terminal (PEL.next G α fixed ι) γ) {m : ℕ}
    (hm : MADLe G m) (p : V) : (γ p).e.1.d ≤ m := by
  rw [(PEL.terminal_keys hα hγ).2.2 p]
  exact CMAI.mind_le_of_madLe hm p

/-- The inductive step of Lemma 19 (and of Lemma 16): from a configuration whose PEL part is
terminal and in which all processes with `E.d ≤ j` have clock `c`, one synchronous step leads to a
configuration with the same PEL part in which all processes with `E.d ≤ j + 1` have clock `c + 1`. -/
theorem fixed_step {γ : V → UState ID α k} (hγ : Terminal (PEL.next G α true ι) (pelC γ))
    {j : ℕ} {c : Fin (k + 1)} (hc : ∀ p, ed γ p ≤ j → (γ p).clock = c) :
    ∀ p, ed γ p ≤ j + 1 → (next G α k true ι γ p).clock = c + 1 := by
  obtain ⟨h0, hpred⟩ := fixed_ed hSC huniq hα hι hℓ hℓmin hγ
  intro p hp
  rw [(step_of_terminal hγ p).2]
  unfold nextValue
  split_ifs with hd
  · rw [hc p (by omega)]
  · congr 1
    obtain ⟨m, hm⟩ : ∃ m, ed γ p = m + 1 := ⟨ed γ p - 1, by omega⟩
    obtain ⟨q, hq, hqm⟩ := hpred p m hm
    exact min_values_eq (fun q' _ hq'd => hc q' (by omega)) ⟨q, hq, by simp only [ed, pelC] at hm hqm ⊢; omega⟩

/-- The legitimate configurations of the corrected `U(K)` (Definition 4). -/
def Legit (G : Digraph V) (α k : ℕ) (ι : V → ID) : Set (V → UState ID α k) :=
  {γ | Terminal (PEL.next G α true ι) (pelC γ) ∧ ∃ c, ∀ p, (γ p).clock = c}

omit hℓ hℓmin in
/-- **Lemma 16** (closure): from a legitimate configuration, a synchronous step increments all
clocks and leads to a legitimate configuration. -/
theorem legit_step {γ : V → UState ID α k} (hγ : γ ∈ Legit G α k ι) :
    next G α k true ι γ ∈ Legit G α k ι ∧
      ∀ p, (next G α k true ι γ p).clock = (γ p).clock + 1 := by
  obtain ⟨hT, c, hc⟩ := hγ
  obtain ⟨ℓ, hℓ, hℓmin⟩ := PEL.exists_mid (ι := ι) hSC
  have hst := fixed_step hSC huniq hα hι hℓ hℓmin hT (j := α) (fun p _ => hc p)
  have hle : ∀ p, ed γ p ≤ α + 1 := fun p => by
    have := fixed_ed_le hSC huniq hα hι hℓ hℓmin hT hα p; simp only [ed, pelC] at this ⊢; omega
  have hpel : pelC (next G α k true ι γ) = pelC γ := funext fun p => (step_of_terminal hT p).1
  refine ⟨⟨hpel ▸ hT, c + 1, fun p => hst p (hle p)⟩, fun p => by rw [hst p (hle p), hc p]⟩

omit hℓ hℓmin in
/-- **Lemmas 18, 19 and Corollary 6** (with the corrected PEL): every synchronous execution of
`U(K)` is legitimate after at most `3α + 4·MAD + 6` steps. -/
theorem theorem5_time {e : ℕ → V → UState ID α k} (he : IsSyncExec (next G α k true ι) e) :
    e (3 * α + 4 * mad G + 6) ∈ Legit G α k ι := by
  obtain ⟨ℓ, hℓ, hℓmin⟩ := PEL.exists_mid (ι := ι) hSC
  have hpe := isSyncExec_pel he
  -- Lemma 18: PEL is terminal after `3α + 3·MAD + 6` steps
  set i₀ := 3 * (α + mad G + 2)
  have hT : ∀ t, i₀ ≤ t → Terminal (PEL.next G α true ι) (pelC (e t)) := fun t ht =>
    PEL.terminal_within hpe.isUnfairRun madLe_mad (mad_le hα) hpe.roundBounds t ht
  have hpel : ∀ t, i₀ ≤ t → ∀ p, (e (t + 1) p).pel = (e t p).pel := fun t ht p => by
    rw [he t]; exact (step_of_terminal (hT t ht) p).1
  have hed : ∀ t, i₀ ≤ t → ∀ p, ed (e (t + 1)) p = ed (e t) p := fun t ht p => by
    simp only [ed, hpel t ht p]
  -- Lemma 19: `PseudoLeg(j)` after `j` more steps
  have hps : ∀ j, ∃ c, ∀ p, ed (e (i₀ + j)) p ≤ j → (e (i₀ + j) p).clock = c := by
    intro j
    induction j with
    | zero =>
      refine ⟨(e i₀ ℓ).clock, fun p hp => ?_⟩
      simp only [Nat.add_zero] at hp ⊢
      have := ((fixed_ed hSC huniq hα hι hℓ hℓmin (hT i₀ le_rfl)).1 p).mp (by
        simp only [ed, pelC] at hp ⊢; omega)
      rw [this]
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + 1, fun p hp => ?_⟩
      have hst := fixed_step hSC huniq hα hι hℓ hℓmin (hT (i₀ + j) (by omega)) hc p
        (by rw [← hed (i₀ + j) (by omega) p]; exact hp)
      rw [show i₀ + (j + 1) = i₀ + j + 1 by omega, he (i₀ + j)]
      exact hst
  obtain ⟨c, hc⟩ := hps (mad G)
  have heq : i₀ + mad G = 3 * α + 4 * mad G + 6 := by simp only [i₀]; ring
  rw [← heq]
  refine ⟨hT _ (by omega), c, fun p => hc p ?_⟩
  have := fixed_ed_le hSC huniq hα hι hℓ hℓmin (hT (i₀ + mad G) (by omega)) madLe_mad p
  simpa [ed, pelC] using this

omit hℓ hℓmin in
/-- **Theorem 5** (with the corrected PEL): `U(K)` is self-stabilizing for the synchronous unison
under the synchronous daemon in every network with a unique source component. -/
theorem theorem5 : SelfStab (IsSyncExec (next G α k true ι)) (SPSU clk) := by
  refine ⟨Legit G α k ι, ?_, fun e he => ?_, fun e he h0 => ?_⟩
  · -- nonempty: a terminal PEL configuration with all clocks `0`
    obtain ⟨γP, hγP⟩ := exists_terminal_pel hSC huniq hα (ι := ι) true
      (fun p => ⟨⟨⟨ι p, 0⟩, Nat.zero_le _⟩, ⟨⟨true, 0⟩, Nat.zero_le _⟩,
        ⟨⟨toLex (true, ι p), 0⟩, Nat.zero_le _⟩⟩)
    exact ⟨fun p => ⟨γP p, 0⟩, hγP, 0, fun _ => rfl⟩
  · -- convergence (see `theorem5_time` for the bound)
    exact ⟨_, theorem5_time hSC huniq hα hι he⟩
  · have hleg : ∀ t, e t ∈ Legit G α k ι := by
      intro t
      induction t with
      | zero => exact h0
      | succ t ih => rw [he t]; exact (legit_step hSC huniq hα hι ih).1
    refine ⟨fun t p q => ?_, fun t p => ?_⟩
    · obtain ⟨-, c, hc⟩ := hleg t
      simp only [clk, hc]
    · simp only [clk]; rw [he t]; exact (legit_step hSC huniq hα hι (hleg t)).2 p

end Fixed

variable (fixed) in
/-- `U(K)` is a local algorithm. -/
theorem isLocal : IsLocal G (fun ι : V → ID => next G α k fixed ι) := by
  intro ι ι' γ γ' p h
  have hp := h p (Or.inl rfl)
  have hq : ∀ q, G.Adj q p → ι q = ι' q ∧ γ q = γ' q := fun q hq => h q (Or.inr hq)
  have hpel : PEL.next G α fixed ι (pelC γ) p = PEL.next G α fixed ι' (pelC γ') p :=
    PEL.isLocal α fixed ι ι' (pelC γ) (pelC γ') p fun q hq' => by
      obtain ⟨h1, h2⟩ := h q hq'; exact ⟨h1, by simp [pelC, h2]⟩
  have hpp : pelC γ p = pelC γ' p := by simp [pelC, hp.2]
  have hen : Enabled (PEL.next G α fixed ι) (pelC γ) p ↔
      Enabled (PEL.next G α fixed ι') (pelC γ') p := by
    simp only [Enabled, hpel, hpp]
  have hval : values G γ p = values G γ' p := by
    classical
    have hed : ∀ q, G.Adj q p → (ed γ q < ed γ p ↔ ed γ' q < ed γ' p) := fun q hq' => by
      simp only [ed, (hq q hq').2, hp.2]
    ext v
    simp only [values, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h' | ⟨q, ⟨hq', hd⟩, rfl⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨q, ⟨hq', (hed q hq').mp hd⟩, by rw [(hq q hq').2]⟩
    · rintro (h' | ⟨q, ⟨hq', hd⟩, rfl⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨q, ⟨hq', (hed q hq').mpr hd⟩, by rw [(hq q hq').2]⟩
  have hnv : nextValue G γ p = nextValue G γ' p := by
    simp only [nextValue, ed, hval, hp.2]
    rfl
  show next G α k fixed ι γ p = next G α k fixed ι' γ' p
  unfold next
  by_cases h1 : Enabled (PEL.next G α fixed ι) (pelC γ) p
  · rw [ite_eq_left h1, ite_eq_left (hen.mp h1), hpel, hp.2]
  · rw [ite_eq_right h1, ite_eq_right (mt hen.mpr h1), hnv, hp.2]

end U

/-- A deterministic local algorithm with a clock output (synchronous unison, period `k + 1`). -/
structure UAlg (G : Digraph V) (ID Q : Type*) (k : ℕ) where
  /-- the next state of `p`, given the identifier assignment -/
  next : (V → ID) → (V → Q) → V → Q
  /-- the clock of `p` -/
  clk : (V → Q) → V → Fin (k + 1)
  local_next : IsLocal G next
  local_clk : ∀ γ γ' p, γ p = γ' p → clk γ p = clk γ' p

/-- **Corollary 5.** Assume `|IDSET| ≥ |V|`, `V` nonempty, `α ≥ MAD` and a period `K = k + 1 ≥ 2`.
A self-stabilizing synchronous unison algorithm under the synchronous daemon (for every assignment
of unique identifiers) exists iff `G` has exactly one source component. The algorithm for the "if"
direction is `U(K)` built on the *corrected* PEL. -/
theorem corollary5 {ID : Type u} [LinearOrder ID] [Nonempty V] (hcard : Nonempty (V ↪ ID))
    {α k : ℕ} (hα : MADLe G α) (hk : 1 ≤ k) :
    (∃ (Q : Type u) (A : UAlg G ID Q k), ∀ ι, Function.Injective ι →
      SelfStab (IsSyncExec (A.next ι)) (SPSU A.clk)) ↔ ∃! SC, G.IsSourceComponent SC := by
  constructor
  · rintro ⟨Q, A, hA⟩
    obtain ⟨f⟩ := hcard
    obtain ⟨SC, hSC⟩ := Digraph.exists_isSourceComponent (G := G)
    exact ⟨SC, hSC, fun S hS =>
      theorem4 hk A.next A.local_next A.clk A.local_clk f (hA f f.injective) hS hSC⟩
  · rintro ⟨SC, hSC, huniq⟩
    refine ⟨UState ID α k, ⟨fun ι => U.next G α k true ι, U.clk, U.isLocal true,
      fun γ γ' p h => by simp [U.clk, h]⟩, fun ι hι => ?_⟩
    exact U.theorem5 hSC huniq hα hι

end Papers.PODC2024.SSLeaderElectionDirected
