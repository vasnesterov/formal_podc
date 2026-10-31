import Papers.PODC2015.RandomizedPLS.Acyclicity
import Papers.PODC2015.RandomizedPLS.TwoSided

/-!
# Acyclicity: lower bounds (proof of Theorem 5.1)

The path `P_n = (u_0, …, u_{n-1})` (port 0 = right neighbour, port 1 = left neighbour) contains the
`r = ⌊n/3⌋` pairwise independent port-preserving copies `H_k = {u_{3k}, u_{3k+1}}` of an edge. The
crossing of `H_a` and `H_b` (`a < b`) cuts out the cycle `C = (u_{3a+1}, …, u_{3b})`, a connected
component of the crossing, which lies in the family `F` of lines and cycles and is not acyclic
(`refuted_cross`). Hence (`thm_5_1_lower_det`, `thm_5_1_lower_oneSided`), for acyclicity on any
family `F` containing the lines and cycles with distinct identities (e.g. connected graphs with
distinct identities, the paper's `F_con`):
* deterministic PLS: `log₂ ⌊n/3⌋ ≤ 2(κ + 1)`, i.e. `κ = Ω(log n)`;
* one-sided RPLS: `log₂ ⌊n/3⌋ ≤ 2 · 2^(κ+1)`, i.e. `κ = Ω(log log n)`.
-/

namespace Podc.RandomizedPLS

open Classical SimpleGraph

/-- Lines and cycles: connected configurations of maximum degree `2` (the family `F` of the proof of
Theorem 5.1). -/
def LinesCycles {S : Type} (c : Config S) : Prop := c.Connected ∧ ∀ v, c.deg v ≤ 2

/-- A connected configuration in which every node has degree `2` is not acyclic. -/
lemma not_acyclic_of_deg_two {S : Type} (c : Config S) (hc : c.Connected)
    (h2 : ∀ v, (c.nbrs v).length = 2) : ¬ Acyclic c := by
  intro ha
  have ht : c.graph.IsTree := ⟨hc, ha⟩
  have h1 := ht.card_edgeFinset
  have h3 := c.graph.sum_degrees_eq_twice_card_edges
  simp only [c.degree_eq, h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h3
  omega

namespace PathLB

variable (n : ℕ)

/-- Neighbours on the path: right neighbour (port 0), then left neighbour. -/
def pn (t : Fin n) : List (Fin n) :=
  (if h : t.1 + 1 < n then [⟨t.1 + 1, h⟩] else []) ++ (if h : 0 < t.1 then [⟨t.1 - 1, by omega⟩] else [])

variable {n}

lemma mem_pn {t w : Fin n} : w ∈ pn n t ↔ w.1 = t.1 + 1 ∨ w.1 + 1 = t.1 := by
  unfold pn
  constructor
  · intro h
    simp only [List.mem_append] at h
    rcases h with h | h <;> split_ifs at h with hh <;> simp at h <;> subst h <;> simp <;> omega
  · rintro (h | h)
    · have : t.1 + 1 < n := h ▸ w.2
      simp only [List.mem_append, dite_eq_left this]
      left; simp [Fin.ext_iff, h]
    · have : 0 < t.1 := by omega
      simp only [List.mem_append, dite_eq_left this]
      right; simp [Fin.ext_iff]; omega

lemma length_pn {t : Fin n} (h0 : 0 < t.1) (h1 : t.1 + 1 < n) : (pn n t).length = 2 := by
  simp [pn, h0, h1]

lemma idxOf_pn_right {t w : Fin n} (h : w.1 = t.1 + 1) : (pn n t).idxOf w = 0 := by
  have h1 : t.1 + 1 < n := h ▸ w.2
  have e : w = ⟨t.1 + 1, h1⟩ := Fin.ext h
  subst e; simp [pn, h1]

lemma idxOf_pn_left {t w : Fin n} (h : w.1 + 1 = t.1) (h1 : t.1 + 1 < n) :
    (pn n t).idxOf w = 1 := by
  have : 0 < t.1 := by omega
  rw [pn, dite_eq_left h1, dite_eq_left this]
  have hne : (⟨t.1 + 1, h1⟩ : Fin n) ≠ w := by intro e; rw [← e] at h; simp only at h; omega
  rw [List.singleton_append, List.idxOf_cons_ne _ hne]
  have e : w = ⟨t.1 - 1, by omega⟩ := Fin.ext (by simp; omega)
  rw [e]; simp

/-- The path on `n` nodes, states = identities. -/
@[reducible] def path (n : ℕ) : Config ℕ where
  V := Fin n
  nbrs := pn n
  nodup t := by
    unfold pn; split_ifs <;> simp [Fin.ext_iff] <;> omega
  loopless t h := by rw [mem_pn] at h; omega
  symm t w h := by rw [mem_pn] at h ⊢; omega
  state t := t.1

/-- The copies `H_k = {u_{3k}, u_{3k+1}}`, `k < ⌊n/3⌋`. -/
@[reducible] def K (n : ℕ) : Copies (path n) (n / 3) where
  W := Bool
  H := ⊤
  emb k b := ⟨3 * k.1 + b.toNat, by have := k.2; have : b.toNat ≤ 1 := Bool.toNat_le b; omega⟩
  inj k a b h := by
    simp only [Fin.ext_iff] at h
    cases a <;> cases b <;> simp_all
  disj i j a b hij e := by
    simp only [Fin.ext_iff] at e
    have := Bool.toNat_le a; have := Bool.toNat_le b
    exact hij (Fin.ext (by omega))
  indep i j a b hij e := by
    change _ ∈ pn n _ at e
    rw [mem_pn] at e
    simp only at e
    have := Bool.toNat_le a; have := Bool.toNat_le b
    exact hij (Fin.ext (by omega))
  hom k a b hab := by
    change _ ∈ pn n _
    rw [mem_pn]
    cases a <;> cases b <;> simp_all
  port_eq i j a b hab := by
    have hi := i.2; have hj := j.2
    cases a <;> cases b
    · exact absurd hab (by simp)
    · change (pn n _).idxOf _ = (pn n _).idxOf _
      rw [idxOf_pn_right (by simp), idxOf_pn_right (by simp)]
    · change (pn n _).idxOf _ = (pn n _).idxOf _
      rw [idxOf_pn_left (by simp) (by simp; omega), idxOf_pn_left (by simp) (by simp; omega)]
    · exact absurd hab (by simp)

lemma K_s (n : ℕ) : (K n).s = 1 := by
  unfold Copies.s; rw [Finset.card_eq_one]
  exact ⟨s(false, true), by
    ext e; induction e using Sym2.ind with | _ x y => (cases x <;> cases y <;> simp)⟩

lemma emb_val (k : Fin (n / 3)) (b : Bool) : ((K n).emb k b).1 = 3 * k.1 + b.toNat := rfl

/-- The path is a line: connected, degrees `≤ 2`, acyclic. -/
lemma path_linesCycles (hn : 0 < n) : LinesCycles (path n) := by
  refine ⟨?_, fun t => ?_⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨fun u v => ?_⟩
    have toZero : ∀ t : Fin n, (path n).graph.Reachable t ⟨0, hn⟩ := by
      intro t
      obtain ⟨t, ht⟩ := t
      induction t with
      | zero => rfl
      | succ t ih =>
        exact (SimpleGraph.Adj.reachable (show (⟨t, by omega⟩ : Fin n) ∈ pn n ⟨t + 1, ht⟩ by
          rw [mem_pn]; simp)).trans (ih (by omega))
    exact (toZero u).trans (toZero v).symm
  · rw [(path n).deg_eq]
    change (pn n t).length ≤ 2
    unfold pn; split_ifs <;> simp

lemma path_acyclic : Acyclic (path n) := by
  refine isAcyclic_of_rank (fun t : Fin n => t.1) (fun u v h => ?_) (fun v u u' hu hu' h1 h2 => ?_)
  · change v ∈ pn n u at h; rw [mem_pn] at h; omega
  · change u ∈ pn n v at hu; change u' ∈ pn n v at hu'
    rw [mem_pn] at hu hu'
    exact Fin.ext (by omega)

/-- The cycle component of the crossing. -/
def U (a b : ℕ) : Set (Fin n) := {t | 3 * a + 1 ≤ t.1 ∧ t.1 ≤ 3 * b}

/-- Membership in a copy, by values. -/
lemma emb_eq_iff {k : Fin (n / 3)} {b : Bool} {x : Fin n} :
    (K n).emb k b = x ↔ x.1 = 3 * k.1 + b.toNat := by
  rw [Fin.ext_iff, emb_val]; omega

/-- The new neighbours of the crossing of copies `i` and `j`, by values. -/
lemma newNbr_val {i j : Fin (n / 3)} (hij : i ≠ j) (x w : Fin n) (_hw : w ∈ pn n x) :
    ((K n).newNbr i j x w).1 =
      if x.1 = 3 * i.1 ∧ w.1 = 3 * i.1 + 1 then 3 * j.1 + 1
      else if x.1 = 3 * i.1 + 1 ∧ w.1 = 3 * i.1 then 3 * j.1
      else if x.1 = 3 * j.1 ∧ w.1 = 3 * j.1 + 1 then 3 * i.1 + 1
      else if x.1 = 3 * j.1 + 1 ∧ w.1 = 3 * j.1 then 3 * i.1
      else w.1 := by
  have hi := i.2; have hj := j.2
  have hij' : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  by_cases harc : (K n).IsArc i j x w
  · obtain ⟨a, b, hab, H1⟩ := (K n).isArc_cases hij harc
    have hb : b = !a := by cases a <;> cases b <;> simp_all
    subst hb
    rcases H1 with ⟨hx, hw', hn⟩ | ⟨hx, hw', hn⟩ <;> rw [hn, emb_val] <;>
      rw [emb_eq_iff] at hx hw' <;> cases a <;> simp at hx hw' ⊢ <;> split_ifs <;> omega
  · rw [(K n).newNbr_of_not_isArc harc]
    have key : ∀ k, (k = i ∨ k = j) → ∀ a : Bool, x.1 = 3 * k.1 + a.toNat →
        w.1 = 3 * k.1 + (!a).toNat → False := by
      intro k hk a hx hw'
      exact harc ⟨k, hk, a, !a, by cases a <;> simp, (emb_eq_iff).2 hx, (emb_eq_iff).2 hw'⟩
    have k1 := key i (Or.inl rfl) false; have k2 := key i (Or.inl rfl) true
    have k3 := key j (Or.inr rfl) false; have k4 := key j (Or.inr rfl) true
    simp at k1 k2 k3 k4
    split_ifs <;> omega

/-- **The crossing is refuted**: the cycle `u_{3a+1} … u_{3b}` is a connected component of the
crossing; it is a cycle (in `F`), hence not acyclic. -/
lemma refuted_cross {i j : Fin (n / 3)} (hij : i ≠ j) :
    Refuted LinesCycles Acyclic ((K n).cross i j hij) := by
  have hi := i.2; have hj := j.2
  have hij' : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  set a := min i.1 j.1
  set b := max i.1 j.1
  have hab : a < b := by omega
  have hb : 3 * b + 3 ≤ n := by
    have : b < n / 3 := by omega
    omega
  -- `U a b` is closed in the crossing
  have hcl : ∀ v ∈ U (n := n) a b, ∀ w ∈ ((K n).cross i j hij).nbrs v, w ∈ U (n := n) a b := by
    intro v hv w hw
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.1 hw
    have hval := newNbr_val hij v w₀ hw₀
    rw [mem_pn] at hw₀
    simp only [U, Set.mem_ofPred_eq] at hv ⊢
    rw [hval]
    split_ifs <;> omega
  have hU0 : (⟨3 * a + 1, by omega⟩ : Fin n) ∈ U (n := n) a b := by simp [U]; omega
  have hconn : (((K n).cross i j hij).restrict _ hcl).Connected := by
    have : Nonempty (U (n := n) a b) := ⟨⟨_, hU0⟩⟩
    refine ⟨fun u v => ?_⟩
    have step : ∀ t (ht : 3 * a + 1 ≤ t) (ht' : t + 1 ≤ 3 * b),
        (((K n).cross i j hij).restrict _ hcl).graph.Adj
          ⟨⟨t + 1, by omega⟩, by simp [U]; omega⟩ ⟨⟨t, by omega⟩, by simp [U]; omega⟩ := by
      intro t ht ht'
      change _ ∈ List.pmap _ _ _
      rw [List.mem_pmap]
      refine ⟨⟨t, by omega⟩, ?_, rfl⟩
      refine List.mem_map.2 ⟨⟨t, by omega⟩, by rw [mem_pn]; simp, ?_⟩
      apply Fin.ext
      rw [newNbr_val hij _ _ (by rw [mem_pn]; simp)]
      simp only
      split_ifs <;> omega
    have toBase' : ∀ d (hd : 3 * a + 1 + d ≤ 3 * b),
        (((K n).cross i j hij).restrict _ hcl).graph.Reachable
          ⟨⟨3 * a + 1 + d, by omega⟩, by simp [U]; omega⟩ ⟨_, hU0⟩ := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        exact (step (3 * a + 1 + d) (by omega) (by omega)).reachable.trans (ih (by omega))
    have toBase : ∀ x : U (n := n) a b,
        (((K n).cross i j hij).restrict _ hcl).graph.Reachable x ⟨_, hU0⟩ := by
      rintro ⟨⟨t, htn⟩, ht⟩
      simp only [U, Set.mem_ofPred_eq] at ht
      obtain ⟨d, rfl⟩ : ∃ d, t = 3 * a + 1 + d := ⟨t - (3 * a + 1), by omega⟩
      exact toBase' d (by omega)
    exact (toBase u).trans (toBase v).symm
  refine Or.inr ⟨U a b, hcl, ⟨hconn, fun v => (path_linesCycles (by omega)).2 v.1⟩, ?_⟩
  -- every node of the component has degree two
  refine not_acyclic_of_deg_two _ hconn fun v => ?_
  obtain ⟨⟨t, htn⟩, ht⟩ := v
  simp only [U, Set.mem_ofPred_eq] at ht
  change (List.pmap _ ((pn n ⟨t, htn⟩).map _) _).length = 2
  rw [List.length_pmap, List.length_map]
  exact length_pn (by simp; omega) (by simp; omega)

lemma path_state_injective : Function.Injective (path n).state := fun _ _ h => Fin.ext h

end PathLB

open PathLB

/-- **Theorem 5.1 of [BFP15], deterministic lower bound for acyclicity** (`Ω(log n)`): every PLS for
acyclicity on a family `F` containing the lines and cycles with distinct identities needs, on the
`n`-node path, labels of `κ` bits with `log₂ ⌊n/3⌋ ≤ 2(κ + 1)`. -/
theorem thm_5_1_lower_det {F : Config ℕ → Prop}
    (hFF : ∀ c, LinesCycles c → Function.Injective c.state → F c)
    {ver : Verifier ℕ} {prover : ∀ c : Config ℕ, c.V → List Bool}
    (h : IsPLS ver prover F Acyclic) {κ : Config ℕ → ℕ}
    (hκ : LabelBound prover F Acyclic κ) (n : ℕ) (hn : 0 < n) :
    Real.logb 2 (n / 3 : ℕ) ≤ 2 * (κ (path n) + 1) := by
  have hF := hFF _ (path_linesCycles hn) path_state_injective
  have := thm_4_4_log h hF path_acyclic (K n) (κ (path n))
    (hκ _ hF path_acyclic) fun i j hij => (refuted_cross hij).mono hFF path_state_injective
  rwa [K_s, Nat.cast_one, mul_one] at this

/-- **Theorem 5.1 of [BFP15], one-sided randomized lower bound for acyclicity**
(`Ω(log log n)`, same families `F`): `log₂ ⌊n/3⌋ ≤ 2 · 2^(κ+1)` for certificates of `κ` bits on
the `n`-node path. -/
theorem thm_5_1_lower_oneSided {F : Config ℕ → Prop}
    (hFF : ∀ c, LinesCycles c → Function.Injective c.state → F c)
    {L : Type} {σ : RScheme ℕ L} {prover : ∀ c : Config ℕ, c.V → L}
    (h : IsOneSided σ prover F Acyclic) {κ : Config ℕ → ℕ}
    (hκ : CertBound σ prover F Acyclic κ) (n : ℕ) (hn : 0 < n) :
    Real.logb 2 (n / 3 : ℕ) ≤ 2 * 2 ^ (κ (path n) + 1) := by
  have hF := hFF _ (path_linesCycles hn) path_state_injective
  have := prop_4_8_log h hF path_acyclic (K n) (κ (path n))
    (hκ _ hF path_acyclic) fun i j hij => (refuted_cross hij).mono hFF path_state_injective
  rwa [K_s, Nat.cast_one, mul_one] at this

/-- **Theorem 5.1 of [BFP15], two-sided edge-independent randomized lower bound for acyclicity**
(`Ω(log log n)`, via Theorem 4.7, same families `F`): `log₂ log₂ ⌊n/3⌋ ≤ 2κ + 5` for certificates
of `κ` bits on the `n`-node path (`n ≥ 6`). -/
theorem thm_5_1_lower_twoSided {F : Config ℕ → Prop}
    (hFF : ∀ c, LinesCycles c → Function.Injective c.state → F c)
    {L : Type} {e : EIScheme ℕ L} {prover : ∀ c : Config ℕ, c.V → L}
    (h : IsTwoSided e.toRScheme prover F Acyclic) {κ : Config ℕ → ℕ}
    (hκ : CertBound e.toRScheme prover F Acyclic κ) (n : ℕ) (hn : 6 ≤ n) :
    Real.logb 2 (Real.logb 2 (n / 3 : ℕ)) ≤ 2 * κ (path n) + 5 := by
  have := thm_4_7_loglog h hκ (hFF _ (path_linesCycles (by omega)) path_state_injective)
    path_acyclic (by omega) (K n) fun i j hij => (refuted_cross hij).mono hFF path_state_injective
  rwa [K_s, Nat.cast_one, Real.logb_one, mul_zero, add_zero] at this

end Podc.RandomizedPLS
