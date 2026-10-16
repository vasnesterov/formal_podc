import Papers.PODC2010.EdgeDominatingSets.Theorem4
import Papers.PODC2010.EdgeDominatingSets.Phase5

/-!
# The algorithm of Theorem 5 (§7.1) as a port-numbering algorithm

Local process with parameter `Δ` (the maximum degree) and `T5 Δ = 2 + Δ² + 2(Δ+1)Δ + 2Δ` rounds:

* rounds `0, 1`: as in Theorem 4 (remote ports, distinguishable port, `chosen`);
* `Δ²` rounds of phase I (`matchStep`), the matching `M` is stored in the field `inD`;
* `2(Δ+1)Δ` rounds of phase II, two rounds per pair `(i, q)`: white nodes accept (field `acc`),
  then both endpoints record the new matching edge;
* `2Δ` rounds of phase III, two rounds per port `q`: nodes accept a proposal (`pin`), then
  proposers learn about acceptance (`pout`).

The output selects the ports `r` with `inD r` (edges of `M`), `pin = some r` or `pout = some r`
(edges of `P`). We show that the run simulates the global processes of `Phase5.lean`
(`run5_phase1`, `run5_phase2`, `run5_phase3`).
-/

namespace Podc.EdgeDominatingSets

open Podc.PortNumbering Finset

/-- Local data of a node in the algorithm of Theorem 5; `inD` stores the matching `M`. -/
structure St5 extends St4 where
  /-- phase II: the port whose proposal was accepted in the current step -/
  acc : Option ℕ
  /-- phase III: the port at which a proposal was accepted -/
  pin : Option ℕ
  /-- phase III: the own port along which a proposal was accepted -/
  pout : Option ℕ

/-- Initial (meaningless) data. -/
def St5.init : St5 := ⟨St4.init, none, none, none⟩

/-- Phase II, receiving side: the neighbour behind this port is black for `i` and proposes along
its port `q`. -/
def proposesII (i q : ℕ) : Option (St5 × ℕ) → Bool
  | some (t, j) => decide (t.deg = i ∧ t.cov = false ∧ j = q)
  | none => false

/-- Phase III, receiving side: the neighbour behind this port proposes along its port `q`. -/
def proposesIII (q : ℕ) : Option (St5 × ℕ) → Bool
  | some (t, j) => decide (t.cov = false ∧ t.pout = none ∧ q < t.deg ∧ j = q)
  | none => false

/-- The local rule of the algorithm of Theorem 5. -/
def rule5 (Δ : ℕ) : ℕ → ℕ → St5 → (ℕ → Option (St5 × ℕ)) → St5
  | 0, d, _, m => ⟨⟨d, rpOf m, dnOf d (rpOf m), fun _ => false, fun _ => false⟩, none, none, none⟩
  | 1, _, s, m => { s with chosen := fun q => match m q with
      | some (t, j) => decide (t.dn = some j)
      | none => false }
  | r + 2, _, s, m =>
    if r < Δ * Δ then
      -- phase I, pair `(r / Δ, r % Δ)`
      { s with inD := fun q => s.inD q || (s.inM (r / Δ) (r % Δ) q && match m q with
          | some (t, _) => !s.cov && !t.cov
          | none => false) }
    else if r - Δ * Δ < 2 * ((Δ + 1) * Δ) then
      -- phase II, pair `(i, q) = (n / Δ, n % Δ)` with `n = (r - Δ²) / 2`
      if (r - Δ * Δ) % 2 = 0 then
        { s with acc := if s.deg < (r - Δ * Δ) / 2 / Δ ∧ s.cov = false then
            firstPort s.deg fun p => proposesII ((r - Δ * Δ) / 2 / Δ) ((r - Δ * Δ) / 2 % Δ) (m p)
          else none }
      else
        { s with
          inD := fun p => s.inD p || decide (s.acc = some p) || match m p with
            | some (t, j) => decide (t.acc = some j)
            | none => false
          acc := none }
    else if r - Δ * Δ - 2 * ((Δ + 1) * Δ) < 2 * Δ then
      -- phase III, port `q = (r - Δ² - 2(Δ+1)Δ) / 2`
      if (r - Δ * Δ - 2 * ((Δ + 1) * Δ)) % 2 = 0 then
        { s with pin := if s.pin = none ∧ s.cov = false then
            firstPort s.deg fun p => proposesIII ((r - Δ * Δ - 2 * ((Δ + 1) * Δ)) / 2) (m p)
          else s.pin }
      else
        { s with pout :=
            if s.pout = none ∧ (r - Δ * Δ - 2 * ((Δ + 1) * Δ)) / 2 < s.deg ∧
              (match m ((r - Δ * Δ - 2 * ((Δ + 1) * Δ)) / 2) with
                | some (t, j) => decide (t.pin = some j)
                | none => false) = true
            then some ((r - Δ * Δ - 2 * ((Δ + 1) * Δ)) / 2) else s.pout }
    else s

/-- The running time `2 + Δ² + 2(Δ+1)Δ + 2Δ = O(Δ²)`. -/
def T5 (Δ : ℕ) : ℕ := 2 + Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Δ

/-- **The algorithm of Theorem 5** with parameter `Δ`. -/
def alg5 (Δ : ℕ) : Algorithm Unit (Set ℕ) :=
  ((Algorithm.ofFun fun _ _ => St5.init).seq 0 (Algorithm.ofLocal (rule5 Δ))).seq (T5 Δ)
    (Algorithm.ofFun fun _ s =>
      {r | r < s.deg ∧ (s.inD r = true ∨ s.pin = some r ∨ s.pout = some r)})

variable {V : Type} [Fintype V] [DecidableEq V]

section Simulation

variable (G : PNGraph V) (Δ : ℕ)

/-- The run of the local process. -/
def run5 (r : ℕ) : V → St5 := Algorithm.localRun G (rule5 Δ) (fun _ => St5.init) r

omit [Fintype V] [DecidableEq V] in
theorem alg5_eval (v : V) :
    (alg5 Δ).eval G (T5 Δ) (fun _ => ()) v =
      {r | r < (run5 G Δ (T5 Δ) v).deg ∧ ((run5 G Δ (T5 Δ) v).inD r = true ∨
        (run5 G Δ (T5 Δ) v).pin = some r ∨ (run5 G Δ (T5 Δ) v).pout = some r)} := by
  have h1 := congrFun (Algorithm.eval_seq ((Algorithm.ofFun fun _ _ => St5.init).seq 0
    (Algorithm.ofLocal (rule5 Δ))) (T5 Δ)
    (Algorithm.ofFun fun _ (s : St5) =>
      {r | r < s.deg ∧ (s.inD r = true ∨ s.pin = some r ∨ s.pout = some r)}) G 0 (fun _ => ())) v
  have h2 := Algorithm.eval_seq (Algorithm.ofFun fun _ _ => St5.init) 0
    (Algorithm.ofLocal (rule5 Δ)) G (T5 Δ) (fun _ : V => ())
  rw [Nat.add_zero] at h1
  rw [zero_add] at h2
  rw [alg5, h1, Algorithm.eval_ofFun, h2, Algorithm.eval_ofLocal]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem run5_succ (r : ℕ) (v : V) :
    run5 G Δ (r + 1) v = rule5 Δ r (G.deg v) (run5 G Δ r v)
      (Algorithm.nbrInfo G (run5 G Δ r) v) := rfl

omit [Fintype V] [DecidableEq V] in
/-- The static data (degree, remote ports, distinguishable port) is correct after round `0`. -/
theorem run5_static (r : ℕ) (v : V) :
    (run5 G Δ (r + 1) v).deg = G.deg v ∧
      (∀ q < G.deg v, (run5 G Δ (r + 1) v).rp q = G.rport v q) ∧
      (run5 G Δ (r + 1) v).dn = G.dn v := by
  induction r generalizing v with
  | zero =>
    have hrp : ∀ q < G.deg v, rpOf (Algorithm.nbrInfo G (run5 G Δ 0) v) q = G.rport v q := by
      intro q hq; simp [rpOf, nbrInfo_of_lt G _ hq]
    exact ⟨rfl, hrp, dnOf_congr hrp⟩
  | succ r ih =>
    rw [run5_succ]
    rcases r with _ | r
    · exact ih v
    · simp only [rule5]
      split_ifs <;> exact ih v

omit [Fintype V] [DecidableEq V] in
theorem run5_stat (r : ℕ) : Stat G (fun v => (run5 G Δ (r + 2) v).toSt4) := by
  intro v
  obtain ⟨h1, h2, h3⟩ := run5_static G Δ (r + 1) v
  refine ⟨h1, h2, h3, ?_⟩
  induction r generalizing v with
  | zero =>
    intro q hq
    show (run5 G Δ (1 + 1) v).chosen q = _
    rw [run5_succ]
    simp only [rule5, nbrInfo_of_lt G _ hq]
    rw [(run5_static G Δ 0 _).2.2]
  | succ r ih =>
    intro q hq
    have := ih v (run5_static G Δ _ v).1 (run5_static G Δ _ v).2.1 (run5_static G Δ _ v).2.2 q hq
    show (run5 G Δ ((r + 2) + 1) v).chosen q = _
    rw [run5_succ]
    simp only [rule5]
    split_ifs <;> exact this

variable {Δ}

theorem rule5_ph1 {r : ℕ} (hr : r < Δ * Δ) (d : ℕ) (s : St5) (m : ℕ → Option (St5 × ℕ)) :
    rule5 Δ (r + 2) d s m =
      { s with inD := fun q => s.inD q || (s.inM (r / Δ) (r % Δ) q && match m q with
          | some (t, _) => !s.cov && !t.cov
          | none => false) } := by
  simp only [rule5, ite_eq_left hr]

theorem rule5_ph2a {n : ℕ} (hn : n < (Δ + 1) * Δ) (d : ℕ) (s : St5) (m : ℕ → Option (St5 × ℕ)) :
    rule5 Δ (Δ * Δ + 2 * n + 2) d s m =
      { s with acc := if s.deg < n / Δ ∧ s.cov = false then
          firstPort s.deg fun p => proposesII (n / Δ) (n % Δ) (m p)
        else none } := by
  have e : Δ * Δ + 2 * n - Δ * Δ = 2 * n := by omega
  simp only [rule5, ite_eq_right (show ¬ Δ * Δ + 2 * n < Δ * Δ by omega), e,
    ite_eq_left (show 2 * n < 2 * ((Δ + 1) * Δ) by omega), Nat.mul_mod_right, ite_true,
    Nat.mul_div_cancel_left n (show 0 < 2 by norm_num)]

theorem rule5_ph2b {n : ℕ} (hn : n < (Δ + 1) * Δ) (d : ℕ) (s : St5) (m : ℕ → Option (St5 × ℕ)) :
    rule5 Δ (Δ * Δ + 2 * n + 1 + 2) d s m =
      { s with
          inD := fun p => s.inD p || decide (s.acc = some p) || match m p with
            | some (t, j) => decide (t.acc = some j)
            | none => false
          acc := none } := by
  have e : Δ * Δ + 2 * n + 1 - Δ * Δ = 2 * n + 1 := by omega
  have e2 : (2 * n + 1) % 2 = 1 := by omega
  simp only [rule5, ite_eq_right (show ¬ Δ * Δ + 2 * n + 1 < Δ * Δ by omega), e,
    ite_eq_left (show 2 * n + 1 < 2 * ((Δ + 1) * Δ) by omega), e2, one_ne_zero, ite_false]

theorem rule5_ph3a {Q : ℕ} (hQ : Q < Δ) (d : ℕ) (s : St5) (m : ℕ → Option (St5 × ℕ)) :
    rule5 Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) d s m =
      { s with pin := if s.pin = none ∧ s.cov = false then
          firstPort s.deg fun p => proposesIII Q (m p)
        else s.pin } := by
  have e : Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q - Δ * Δ - 2 * ((Δ + 1) * Δ) = 2 * Q := by omega
  simp only [rule5, ite_eq_right (show ¬ Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q < Δ * Δ by omega),
    ite_eq_right (show ¬ Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q - Δ * Δ < 2 * ((Δ + 1) * Δ) by omega), e,
    ite_eq_left (show 2 * Q < 2 * Δ by omega), Nat.mul_mod_right, ite_true,
    Nat.mul_div_cancel_left Q (show 0 < 2 by norm_num)]

theorem rule5_ph3b {Q : ℕ} (hQ : Q < Δ) (d : ℕ) (s : St5) (m : ℕ → Option (St5 × ℕ)) :
    rule5 Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 1 + 2) d s m =
      { s with pout :=
          if s.pout = none ∧ Q < s.deg ∧
            (match m Q with
              | some (t, j) => decide (t.pin = some j)
              | none => false) = true
          then some Q else s.pout } := by
  have e : Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 1 - Δ * Δ - 2 * ((Δ + 1) * Δ) = 2 * Q + 1 := by
    omega
  have e2 : (2 * Q + 1) % 2 = 1 := by omega
  have e3 : (2 * Q + 1) / 2 = Q := by omega
  simp only [rule5, ite_eq_right (show ¬ Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 1 < Δ * Δ by omega),
    ite_eq_right (show ¬ Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 1 - Δ * Δ < 2 * ((Δ + 1) * Δ) by omega),
    e, ite_eq_left (show 2 * Q + 1 < 2 * Δ by omega), e2, e3, one_ne_zero, ite_false]

end Simulation

section Phases

variable {G : PNGraph V} (hG : G.IsSimple) (Δ : ℕ)
include hG

omit [Fintype V] [DecidableEq V] in
theorem edge_eq_edge_iff {u v : V} {p q : ℕ} (hp : p < G.deg u) (hq : q < G.deg v) :
    G.edge u p = G.edge v q ↔ (u = v ∧ p = q) ∨ (u = G.nbr v q ∧ p = G.rport v q) := by
  constructor
  · intro h
    have h' : s(u, G.nbr u p) = s(v, G.nbr v q) := h
    rcases Sym2.eq_iff.1 h' with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨rfl, hG.2 u p q hp hq h2⟩
    · refine Or.inr ⟨h1, ?_⟩
      subst h1
      exact hG.2 _ p _ hp (G.rport_lt hq) (h2.trans (G.nbr_nbr hq).symm)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact G.edge_nbr hq

theorem mphase1_sub (n : ℕ) : ∀ e ∈ mphase1 G Δ n, e ∈ G.toSimpleGraph.edgeSet := by
  intro e he
  obtain ⟨i, j, h⟩ := mem_M_of_mem_iterPairs (matchStep_cases G) Δ (by simp) n e he
  exact mem_edgeSet_of_mem_M hG h

theorem run5_phase1 {n : ℕ} (hn : n ≤ Δ * Δ) :
    Repr G (fun v => (run5 G Δ (n + 2) v).toSt4) (mphase1 G Δ n) ∧
      ∀ v, (run5 G Δ (n + 2) v).acc = none ∧ (run5 G Δ (n + 2) v).pin = none ∧
        (run5 G Δ (n + 2) v).pout = none := by
  classical
  induction n with
  | zero =>
    refine ⟨fun v q hq => ?_, fun v => ?_⟩ <;> simp [run5_succ, rule5, mphase1]
  | succ n ih =>
    have hn' : n < Δ * Δ := by omega
    obtain ⟨ih, ih'⟩ := ih (by omega)
    have hst := run5_stat G Δ n
    refine ⟨fun v q hq => ?_, fun v => ?_⟩
    · show (run5 G Δ ((n + 2) + 1) v).inD q = true ↔ _
      rw [run5_succ, rule5_ph1 hn']
      simp only [nbrInfo_of_lt G _ hq]
      rw [mphase1, iterPairs_succ, ← mphase1, matchStep, mem_union, mem_filter]
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      rw [← Bool.not_eq_true, ← Bool.not_eq_true, ih v q hq, inM_iff hG hst hq,
        forall_mem_edge]
      erw [cov_iff hst (mphase1_sub hG Δ n) ih, cov_iff hst (mphase1_sub hG Δ n) ih]
    · rw [show n + 1 + 2 = (n + 2) + 1 by ring, run5_succ, rule5_ph1 hn']
      exact ih' v

/-- The matching after phase I. -/
noncomputable abbrev M1 (G : PNGraph V) (Δ : ℕ) : Finset (Sym2 V) := mphase1 G Δ (Δ * Δ)

theorem mphase2_sub (n : ℕ) :
    ∀ e ∈ mphase2 G Δ (M1 G Δ) n, e ∈ G.toSimpleGraph.edgeSet := by
  induction n with
  | zero => exact mphase1_sub hG Δ _
  | succ n ih => exact propStep_sub hG ih

/-- The acceptance round of step `n` of phase II computes `accPort`. -/
theorem run5_acc {n : ℕ} (hn : n < (Δ + 1) * Δ)
    (hR : Repr G (fun v => (run5 G Δ (Δ * Δ + 2 * n + 2) v).toSt4) (mphase2 G Δ (M1 G Δ) n))
    (v : V) :
    (run5 G Δ (Δ * Δ + 2 * n + 2 + 1) v).acc = accPort G (mphase2 G Δ (M1 G Δ) n) (n / Δ) (n % Δ) v := by
  classical
  have hst : Stat G (fun v => (run5 G Δ (Δ * Δ + 2 * n + 2) v).toSt4) := run5_stat G Δ _
  have hcov := cov_iff hst (mphase2_sub hG Δ n) hR
  rw [run5_succ, rule5_ph2a hn]
  simp only [accPort]
  have hdeg : ∀ u, (run5 G Δ (Δ * Δ + 2 * n + 2) u).deg = G.deg u := fun u => (hst u).1
  by_cases hw : White G (mphase2 G Δ (M1 G Δ) n) (n / Δ) v
  · have hw' : (run5 G Δ (Δ * Δ + 2 * n + 2) v).deg < n / Δ ∧
        (run5 G Δ (Δ * Δ + 2 * n + 2) v).cov = false := by
      rw [hdeg, ← Bool.not_eq_true]; erw [hcov]; exact hw
    rw [ite_eq_left hw', ite_eq_left hw, hdeg]
    apply firstPort_congr
    intro p hp
    simp only [nbrInfo_of_lt G _ hp, proposesII, decide_eq_true_eq, hdeg, ← Bool.not_eq_true,
      Black, and_assoc]
    erw [hcov]
  · have hw' : ¬ ((run5 G Δ (Δ * Δ + 2 * n + 2) v).deg < n / Δ ∧
        (run5 G Δ (Δ * Δ + 2 * n + 2) v).cov = false) := by
      rw [hdeg, ← Bool.not_eq_true]; erw [hcov]; exact hw
    rw [ite_eq_right hw', ite_eq_right hw]

theorem run5_phase2 {n : ℕ} (hn : n ≤ (Δ + 1) * Δ) :
    Repr G (fun v => (run5 G Δ (Δ * Δ + 2 * n + 2) v).toSt4) (mphase2 G Δ (M1 G Δ) n) ∧
      ∀ v, (run5 G Δ (Δ * Δ + 2 * n + 2) v).acc = none ∧
        (run5 G Δ (Δ * Δ + 2 * n + 2) v).pin = none ∧
        (run5 G Δ (Δ * Δ + 2 * n + 2) v).pout = none := by
  classical
  induction n with
  | zero => simpa [mphase2] using run5_phase1 hG Δ (le_refl (Δ * Δ))
  | succ n ih =>
    have hn' : n < (Δ + 1) * Δ := by omega
    obtain ⟨ih, ih'⟩ := ih (by omega)
    have hacc := run5_acc hG Δ hn' ih
    have e : Δ * Δ + 2 * (n + 1) + 2 = (Δ * Δ + 2 * n + 1 + 2) + 1 := by ring
    have e' : Δ * Δ + 2 * n + 1 + 2 = Δ * Δ + 2 * n + 2 + 1 := by ring
    -- the acceptance round changes only `acc`
    have hmid : ∀ u, (run5 G Δ (Δ * Δ + 2 * n + 1 + 2) u).toSt4 =
        (run5 G Δ (Δ * Δ + 2 * n + 2) u).toSt4 ∧
        (run5 G Δ (Δ * Δ + 2 * n + 1 + 2) u).pin = none ∧
        (run5 G Δ (Δ * Δ + 2 * n + 1 + 2) u).pout = none := by
      intro u
      rw [e', run5_succ, rule5_ph2a hn']
      exact ⟨rfl, (ih' u).2.1, (ih' u).2.2⟩
    refine ⟨fun v q hq => ?_, fun v => ?_⟩
    · show (run5 G Δ (Δ * Δ + 2 * (n + 1) + 2) v).inD q = true ↔ _
      rw [e, run5_succ, rule5_ph2b hn']
      simp only [nbrInfo_of_lt G _ hq]
      rw [mphase2, iterPairs_succ, ← mphase2, mem_propStep]
      have h1 : (run5 G Δ (Δ * Δ + 2 * n + 1 + 2) v).inD q = true ↔
          G.edge v q ∈ mphase2 G Δ (M1 G Δ) n := by
        rw [show (run5 G Δ (Δ * Δ + 2 * n + 1 + 2) v).inD q =
          (run5 G Δ (Δ * Δ + 2 * n + 1 + 2) v).toSt4.inD q from rfl, (hmid v).1]
        exact ih v q hq
      simp only [Bool.or_eq_true, decide_eq_true_eq, h1]
      rw [e', hacc, hacc, or_assoc]
      apply or_congr_right
      constructor
      · rintro (h | h)
        · exact ⟨v, q, h, rfl⟩
        · exact ⟨_, _, h, G.edge_nbr hq⟩
      · rintro ⟨u, p, hp, he⟩
        rcases (edge_eq_edge_iff hG (accPort_spec hp).2.1 hq).1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl hp
        · exact Or.inr hp
    · rw [e, run5_succ, rule5_ph2b hn']
      exact ⟨rfl, (hmid v).2.1, (hmid v).2.2⟩

/-- The matching after phase II. -/
noncomputable abbrev Mfin (G : PNGraph V) (Δ : ℕ) : Finset (Sym2 V) :=
  mphase2 G Δ (M1 G Δ) ((Δ + 1) * Δ)

/-- The nodes of `H`: not covered by the final matching. -/
def Unm (G : PNGraph V) (Δ : ℕ) (v : V) : Prop := ¬ Covered (Mfin G Δ) v

theorem run5_phase3 {Q : ℕ} (hQ : Q ≤ Δ) :
    Repr G (fun v => (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) v).toSt4) (Mfin G Δ) ∧
      ∀ v, (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) v).pin =
          (phase3 G (Unm G Δ) Q).1 v ∧
        (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) v).pout =
          (phase3 G (Unm G Δ) Q).2 v := by
  classical
  induction Q with
  | zero =>
    obtain ⟨h1, h2⟩ := run5_phase2 hG Δ (le_refl ((Δ + 1) * Δ))
    exact ⟨h1, fun v => ⟨(h2 v).2.1, (h2 v).2.2⟩⟩
  | succ Q ih =>
    have hQ' : Q < Δ := by omega
    obtain ⟨hR3, ih'⟩ := ih (by omega)
    have hst : Stat G (fun v => (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) v).toSt4) := run5_stat G Δ _
    have hcov := cov_iff hst (mphase2_sub hG Δ _) hR3
    have hdeg : ∀ u, (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) u).deg = G.deg u := fun u => (hst u).1
    set pin := (phase3 G (Unm G Δ) Q).1
    set pout := (phase3 G (Unm G Δ) Q).2
    have e1 : Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 1 + 2 = Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2 + 1 := by omega
    have e2 : Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * (Q + 1) + 2 =
        (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 1 + 2) + 1 := by ring
    -- the acceptance round
    have hmid : ∀ u, (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2 + 1) u).toSt4 = (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) u).toSt4 ∧
        (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2 + 1) u).pout = pout u ∧
        (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2 + 1) u).pin = accept3 G (Unm G Δ) Q pin pout u := by
      intro u
      rw [run5_succ, rule5_ph3a hQ']
      refine ⟨rfl, (ih' u).2, ?_⟩
      simp only [accept3]
      have hU : (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) u).cov = false ↔ Unm G Δ u := by
        rw [← Bool.not_eq_true]; erw [hcov]; rfl
      by_cases hc : pin u = none ∧ Unm G Δ u
      · have hc' : (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) u).pin = none ∧ (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) u).cov = false := by
          rw [(ih' u).1, hU]; exact hc
        rw [ite_eq_left hc', ite_eq_left hc, hdeg]
        apply firstPort_congr
        intro p hp
        simp only [nbrInfo_of_lt G _ hp, proposesIII, decide_eq_true_eq, Eligible]
        rw [hdeg, (ih' _).2, show (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2)
          (G.nbr u p)).cov = false ↔ Unm G Δ (G.nbr u p) by
          rw [← Bool.not_eq_true]; erw [hcov]; rfl]
        constructor
        · rintro ⟨a, b, c, d⟩
          refine ⟨⟨a, b, c, ?_⟩, d⟩
          rw [← d, G.nbr_nbr hp]; exact hc.2
        · rintro ⟨⟨a, b, c, -⟩, d⟩
          exact ⟨a, b, c, d⟩
      · have hc' : ¬ ((run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) u).pin = none ∧ (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Q + 2) u).cov = false) := by
          rw [(ih' u).1, hU]; exact hc
        rw [ite_eq_right hc', ite_eq_right hc, (ih' u).1]
    refine ⟨fun v q hq => ?_, fun v => ⟨?_, ?_⟩⟩
    · show (run5 G Δ (Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * (Q + 1) + 2) v).toSt4.inD q = true ↔ _
      rw [e2, run5_succ, rule5_ph3b hQ', e1]
      exact (congrArg (fun s => s.inD q = true) (hmid v).1).to_iff.trans (hR3 v q hq)
    · rw [e2, run5_succ, rule5_ph3b hQ', e1]
      exact (hmid v).2.2
    · rw [e2, run5_succ, rule5_ph3b hQ', e1]
      show _ = commit3 G Q (accept3 G (Unm G Δ) Q pin pout) pout v
      simp only [commit3, (hmid v).2.1]
      erw [(congrArg St4.deg (hmid v).1)]
      rw [hdeg]
      by_cases hq : Q < G.deg v
      · simp only [nbrInfo_of_lt G _ hq, decide_eq_true_eq, (hmid _).2.2]
      · simp [hq]

end Phases

end Podc.EdgeDominatingSets
