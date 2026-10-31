import Papers.PODC2015.RandomizedPLS.LowerBound

/-!
# Theorem 4.4 (and Proposition 4.3) fail when `P(G) = FALSE`

Theorem 4.4 assumes `P(G_s) ≠ P(σ^{ij}₁(G)_s)` for all `i ≠ j`; the paper only proves (and only uses)
the case `P(G) = TRUE`. Proposition 4.3's proof also treats the case where `G` is rejected, but it
transfers *one* labelling of `G` to the crossing, whereas rejection of the crossing concerns *all*
labellings — and when `P(G) = FALSE` the crossings are legal and carry their own prover labels.

**Counterexample.** The windmill `G_r`: a hub adjacent to `L_k, R_k` (`k < r`), plus the edges
`L_k R_k`. The `r` edges `L_k R_k` are pairwise independent port-preserving copies of a single edge
(`s = 1`). States are identities. Let `F = {G} ∪ {crossings}` and `P` = "some node `(k, ·)` has a
neighbour `(k', ·)` with `k' ≠ k`": `P(G) = FALSE` and every crossing is legal. Yet `(F, P)` has a
PLS with `O(log log r)`-bit labels:
* a crossed `L_k` (its port-0 neighbour is `R_{k'}`, `k' ≠ k`) raises a flag `1`;
* every `R_m` carries a bit position `t` (in binary) and the bit `m_t`, and checks it (and that its
  own flag is `0`); a flagged `L_k` checks that its port-0 neighbour's bit differs from `k_t`
  (so that neighbour is not `R_k`); the prover picks a position where `k` and `k'` differ;
* the hub checks that some neighbour is flagged.
In `G` the flagged `L_k` would face `R_k`, whose bit equals `k_t` — rejected for every labelling.
Theorem 4.4 would demand `Ω(log r / s) = Ω(log r)` bits (`thm_4_4_false`), and Proposition 4.3's
conclusion fails for every pair (`prop_4_3_false`). All configurations are connected and the
identities are distinct, as in the paper's model.
-/

namespace Podc.RandomizedPLS.Windmill

open Classical

/-- A bit position where `m` and `k` differ (`0` if `m = k`). -/
noncomputable def diffBit (m k : ℕ) : ℕ :=
  if h : ∃ t, m.testBit t ≠ k.testBit t then Nat.find h else 0

lemma diffBit_spec {m k : ℕ} (h : m ≠ k) : m.testBit (diffBit m k) ≠ k.testBit (diffBit m k) := by
  have he : ∃ t, m.testBit t ≠ k.testBit t := by
    by_contra hc; push_neg at hc; exact h (Nat.eq_of_testBit_eq hc)
  rw [diffBit, dite_eq_left he]
  exact Nat.find_spec he

lemma diffBit_comm (m k : ℕ) : diffBit m k = diffBit k m := by
  have : (fun t => m.testBit t ≠ k.testBit t) = (fun t => k.testBit t ≠ m.testBit t) :=
    funext fun t => propext ne_comm
  simp only [diffBit, this]

lemma diffBit_le_log {m k r : ℕ} (h : m ≠ k) (hm : m < r) (hk : k < r) :
    diffBit m k ≤ Nat.log 2 r := by
  have hs := diffBit_spec h
  set t := diffBit m k
  have : 2 ^ t < r := by
    cases hmt : m.testBit t
    · have hkt : k.testBit t = true := by rw [hmt] at hs; cases hkt' : k.testBit t <;> simp_all
      exact lt_of_le_of_lt (Nat.ge_two_pow_of_testBit hkt) hk
    · exact lt_of_le_of_lt (Nat.ge_two_pow_of_testBit hmt) hm
  exact Nat.le_log_of_pow_le (by norm_num) this.le

/-! ### The windmill configuration -/

variable (r : ℕ)

/-- States: identities (`none` for the hub). -/
abbrev St := Option (ℕ × Bool)

/-- The neighbours in the windmill: the hub sees everybody, `(k, b)` sees `(k, !b)` at port 0 and
the hub at port 1. -/
noncomputable def wNbrs : Option (Fin r × Bool) → List (Option (Fin r × Bool))
  | none => (Finset.univ : Finset (Fin r × Bool)).toList.map some
  | some (k, b) => [some (k, !b), none]

/-- The windmill `G_r` (states = identities). -/
@[reducible] noncomputable def G : Config St where
  V := Option (Fin r × Bool)
  nbrs := wNbrs r
  nodup v := by
    rcases v with _ | ⟨k, b⟩
    · exact (Finset.nodup_toList _).map (Option.some_injective _)
    · simp [wNbrs]
  loopless v := by
    rcases v with _ | ⟨k, b⟩ <;> simp [wNbrs]
  symm v w h := by
    rcases v with _ | ⟨k, b⟩ <;> rcases w with _ | ⟨k', b'⟩ <;> simp_all [wNbrs]
  state v := v.map fun p => (p.1.val, p.2)

/-- The copies `L_k R_k` of a single edge. -/
@[reducible] noncomputable def K : Copies (G r) r where
  W := Bool
  H := ⊤
  emb k b := some (k, b)
  inj k a b h := by simpa using h
  disj i j a b h e := h (by simp at e; exact e.1)
  indep i j a b h e := by
    change some (j, b) ∈ wNbrs r (some (i, a)) at e
    simp [wNbrs] at e; exact h e.1.symm
  hom i a b h := by
    change some (i, b) ∈ wNbrs r (some (i, a))
    have : b = !a := by cases a <;> cases b <;> simp_all
    simp [wNbrs, this]
  port_eq i j a b h := by
    have : b = !a := by cases a <;> cases b <;> simp_all
    subst this
    simp [Config.port, wNbrs]

lemma K_s : (K r).s = 1 := by
  unfold Copies.s; rw [Finset.card_eq_one]
  exact ⟨s(false, true), by
    ext e; induction e using Sym2.ind with | _ x y => (cases x <;> cases y <;> simp)⟩

variable {r}

/-- The index swap of the crossing of copies `i` and `j`. -/
def τ (i j k : Fin r) : Fin r := if k = i then j else if k = j then i else k

lemma τ_τ {i j : Fin r} (k : Fin r) : τ i j (τ i j k) = k := by
  unfold τ; split_ifs <;> simp_all

lemma newNbr_hub (i j : Fin r) (x : Option (Fin r × Bool)) :
    (K r).newNbr i j x none = none := by
  apply (K r).newNbr_of_not_isArc
  rintro ⟨k, -, a, b, -, -, h⟩
  exact Option.some_ne_none _ h

lemma newNbr_none (i j : Fin r) (w : Option (Fin r × Bool)) : (K r).newNbr i j none w = w := by
  apply (K r).newNbr_of_not_isArc
  rintro ⟨k, -, a, b, -, h, -⟩
  exact Option.some_ne_none _ h

lemma newNbr_partner {i j : Fin r} (hij : i ≠ j) (k : Fin r) (b : Bool) :
    (K r).newNbr i j (some (k, b)) (some (k, !b)) = some (τ i j k, !b) := by
  have hadj : (⊤ : SimpleGraph Bool).Adj b (!b) := by cases b <;> simp
  by_cases hk : k = i
  · subst hk
    have : (K r).IsArc k j (some (k, b)) (some (k, !b)) := ⟨k, Or.inl rfl, b, !b, hadj, rfl, rfl⟩
    rw [Copies.newNbr, ite_eq_left this]
    exact ((K r).swap_emb_left k j (!b)).trans (by simp [τ, K])
  · by_cases hk' : k = j
    · subst hk'
      have : (K r).IsArc i k (some (k, b)) (some (k, !b)) :=
        ⟨k, Or.inr rfl, b, !b, hadj, rfl, rfl⟩
      rw [Copies.newNbr, ite_eq_left this]
      exact ((K r).swap_emb_right hij (!b)).trans (by simp [τ, K, hk])
    · rw [(K r).newNbr_of_not_isArc]
      · simp [τ, hk, hk']
      · rintro ⟨k', hk'', a, a', -, h, -⟩
        have : k' = k := by simp [K] at h; exact h.1
        subst this
        rcases hk'' with rfl | rfl <;> simp_all

lemma cross_nbrs_some {i j : Fin r} (hij : i ≠ j) (k : Fin r) (b : Bool) :
    ((K r).cross i j hij).nbrs (some (k, b)) = [some (τ i j k, !b), none] := by
  rw [Copies.cross_nbrs]
  change ([some (k, !b), none] : List _).map _ = _
  simp [newNbr_partner hij, newNbr_hub]

lemma cross_nbrs_none {i j : Fin r} (hij : i ≠ j) :
    ((K r).cross i j hij).nbrs none = (G r).nbrs none := by
  rw [Copies.cross_nbrs]
  conv_rhs => rw [← List.map_id ((G r).nbrs none)]
  exact List.map_congr_left fun w _ => newNbr_none i j w

/-! ### The family, the predicate and the scheme -/

/-- The family: the windmill and all its crossings. -/
def F (c : Config St) : Prop :=
  c = G r ∨ ∃ i j : Fin r, ∃ hij : i ≠ j, c = (K r).cross i j hij

/-- `P`: some node `(k, ·)` has a neighbour `(k', ·)` with `k' ≠ k`. -/
def P (c : Config St) : Prop :=
  ∃ v w, w ∈ c.nbrs v ∧ ∃ k b k' b', c.state v = some (k, b) ∧ c.state w = some (k', b') ∧ k ≠ k'

lemma not_P_G : ¬ P (G r) := by
  rintro ⟨v, w, hw, k, b, k', b', hv, hw', hne⟩
  rcases v with _ | ⟨k₀, b₀⟩
  · simp [G] at hv
  · change w ∈ wNbrs r (some (k₀, b₀)) at hw
    simp only [wNbrs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · simp [G] at hv hw'; exact hne (hv.1.symm.trans hw'.1)
    · simp [G] at hw'

lemma P_cross {i j : Fin r} (hij : i ≠ j) : P ((K r).cross i j hij) := by
  refine ⟨some (i, false), some (j, true), ?_, i, false, j, true, rfl, rfl,
    fun h => hij (Fin.ext h)⟩
  rw [cross_nbrs_some]; simp [τ]

/-- The flag of a label. -/
def flag (x : List Bool) : Bool := x.headD false

/-- The checked bit of a label. -/
def bitOf (x : List Bool) : Bool := x.getD 1 false

/-- The bit position of a label. -/
def posOf (x : List Bool) : ℕ := decN (x.drop 2)

/-- The verifier. -/
noncomputable def ver : Verifier St
  | none, _, ls => decide (∃ y ∈ ls, flag y = true)
  | some (m, true), x, _ => decide (flag x = false ∧ bitOf x = m.testBit (posOf x))
  | some (k, false), x, ls =>
      decide (flag x = true → bitOf (ls.headD []) ≠ k.testBit (posOf (ls.headD [])))

/-- The index of the port-0 neighbour (the node's own index if there is none). -/
noncomputable def partnerIdx (c : Config St) (v : c.V) (m : ℕ) : ℕ :=
  match (c.nbrs v).head? with
  | some w => match c.state w with
    | some (k, _) => k
    | none => m
  | none => m

/-- The prover (it only looks at states and ports). -/
noncomputable def prover (c : Config St) (v : c.V) : List Bool :=
  match c.state v with
  | none => []
  | some (k, false) => [decide (partnerIdx c v k ≠ k)]
  | some (m, true) =>
      false :: m.testBit (diffBit m (partnerIdx c v m)) :: encN (diffBit m (partnerIdx c v m))

lemma partnerIdx_cross {i j : Fin r} (hij : i ≠ j) (k : Fin r) (b : Bool) (m : ℕ) :
    partnerIdx ((K r).cross i j hij) (some (k, b)) m = (τ i j k).val := by
  unfold partnerIdx
  rw [cross_nbrs_some]
  rfl

lemma prover_cross_L {i j : Fin r} (hij : i ≠ j) (k : Fin r) :
    prover ((K r).cross i j hij) (some (k, false)) = [decide ((τ i j k : ℕ) ≠ k)] := by
  unfold prover
  rw [show ((K r).cross i j hij).state (some (k, false)) = some ((k : ℕ), false) from rfl]
  simp only [partnerIdx_cross]

lemma prover_cross_R {i j : Fin r} (hij : i ≠ j) (k : Fin r) :
    prover ((K r).cross i j hij) (some (k, true)) =
      false :: (k : ℕ).testBit (diffBit k (τ i j k)) :: encN (diffBit k (τ i j k)) := by
  unfold prover
  rw [show ((K r).cross i j hij).state (some (k, true)) = some ((k : ℕ), true) from rfl]
  simp only [partnerIdx_cross]

lemma prover_cross_hub {i j : Fin r} (hij : i ≠ j) :
    prover ((K r).cross i j hij) none = [] := rfl

/-- The scheme is complete on the crossings. -/
lemma accepts_cross {i j : Fin r} (hij : i ≠ j) :
    Accepts ver ((K r).cross i j hij) (prover ((K r).cross i j hij)) := by
  set c := (K r).cross i j hij
  intro v
  rcases v with _ | ⟨k, b⟩
  · -- the hub sees the flag of `L_i`
    change decide (∃ y ∈ (c.nbrs none).map (prover c), flag y = true) = true
    rw [decide_eq_true_iff, cross_nbrs_none]
    refine ⟨prover c (some (i, false)), List.mem_map.2 ⟨some (i, false), ?_, rfl⟩, ?_⟩
    · change _ ∈ (Finset.univ : Finset (Fin r × Bool)).toList.map some
      simp
    · rw [prover_cross_L]
      simp [flag, τ, Fin.val_ne_iff.2 (Ne.symm hij)]
  · cases b
    · -- `L_k`
      change decide (flag (prover c (some (k, false))) = true →
        bitOf ((c.nbrs (some (k, false))).map (prover c) |>.headD []) ≠
          (k : ℕ).testBit (posOf ((c.nbrs (some (k, false))).map (prover c) |>.headD []))) = true
      rw [decide_eq_true_iff, cross_nbrs_some, prover_cross_L]
      intro hflag
      have hR : prover c (some (τ i j k, true)) = _ := prover_cross_R hij (τ i j k)
      rw [τ_τ] at hR
      simp only [Bool.not_false, List.map_cons, List.headD_cons, hR, bitOf,
        posOf, List.getD_cons_succ, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero,
        decN_encN]
      have hk : (τ i j k : ℕ) ≠ k := by simpa [flag] using hflag
      exact diffBit_spec hk
    · -- `R_m`
      change decide (flag (prover c (some (k, true))) = false ∧
        bitOf (prover c (some (k, true))) = (k : ℕ).testBit (posOf (prover c (some (k, true))))) = true
      rw [prover_cross_R]
      simp [flag, bitOf, posOf, decN_encN]

/-- The scheme is sound: no labelling is accepted on the windmill. -/
lemma not_accepts_G (ℓ : (G r).V → List Bool) : ¬ Accepts ver (G r) ℓ := by
  intro h
  have hhub := h none
  change decide (∃ y ∈ ((G r).nbrs none).map ℓ, flag y = true) = true at hhub
  rw [decide_eq_true_iff] at hhub
  obtain ⟨y, hy, hfl⟩ := hhub
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
  rcases u with _ | ⟨k, b⟩
  · -- the hub is not its own neighbour
    exact absurd hu ((G r).loopless none)
  · cases b
    · have hL := h (some (k, false))
      have hR := h (some (k, true))
      change decide (flag (ℓ (some (k, false))) = true →
        bitOf ((wNbrs r (some (k, false))).map ℓ |>.headD []) ≠
          (k : ℕ).testBit (posOf ((wNbrs r (some (k, false))).map ℓ |>.headD []))) = true at hL
      change decide (flag (ℓ (some (k, true))) = false ∧
        bitOf (ℓ (some (k, true))) = (k : ℕ).testBit (posOf (ℓ (some (k, true))))) = true at hR
      simp only [decide_eq_true_iff, wNbrs, Bool.not_false, List.map_cons, List.headD_cons] at hL hR
      exact hL hfl hR.2
    · have hR := h (some (k, true))
      change decide (flag (ℓ (some (k, true))) = false ∧
        bitOf (ℓ (some (k, true))) = (k : ℕ).testBit (posOf (ℓ (some (k, true))))) = true at hR
      rw [decide_eq_true_iff] at hR
      rw [hR.1] at hfl; exact Bool.false_ne_true hfl

/-- `(ver, prover)` is a PLS for `(F, P)`. -/
theorem isPLS : IsPLS ver prover (F (r := r)) P := by
  refine ⟨?_, ?_⟩
  · rintro c (rfl | ⟨i, j, hij, rfl⟩) hP
    · exact absurd hP (not_P_G)
    · exact accepts_cross hij
  · rintro c (rfl | ⟨i, j, hij, rfl⟩) hP ℓ
    · exact not_accepts_G ℓ
    · exact absurd (P_cross hij) hP

/-- The labels have `O(log log r)` bits. -/
theorem labelBound : LabelBound prover (F (r := r)) P (fun _ => 3 + Nat.log 2 (Nat.log 2 r)) := by
  rintro c (rfl | ⟨i, j, hij, rfl⟩) hP v
  · exact absurd hP not_P_G
  · rcases v with _ | ⟨k, b⟩
    · rw [prover_cross_hub]; simp
    · cases b
      · rw [prover_cross_L]; simp only [List.length_cons, List.length_nil]; omega
      · rw [prover_cross_R]; simp only [List.length_cons]
        have h1 := length_encN (diffBit k (τ i j k))
        by_cases hk : (k : ℕ) = τ i j k
        · have : diffBit k (τ i j k) = 0 := by
            unfold diffBit; rw [dite_eq_right]; push_neg; intro t; rw [hk]
          rw [this] at h1 ⊢; simp at h1 ⊢; omega
        · have h2 := diffBit_le_log hk k.2 (τ i j k).2
          have h3 := Nat.log_mono_right (b := 2) h2
          omega

/-- The windmill and all its crossings are connected (the paper's networks are connected). -/
theorem connected_of_F {c : Config St} (hc : F (r := r) c) : c.Connected := by
  rcases hc with rfl | ⟨i, j, hij, rfl⟩
  · haveI : Nonempty (G r).V := ⟨none⟩
    refine ⟨fun u v => ?_⟩
    have toHub : ∀ u : (G r).V, (G r).graph.Reachable u none := by
      rintro (_ | ⟨k, b⟩)
      · rfl
      · exact SimpleGraph.Adj.reachable (by simp [Config.graph, wNbrs])
    exact (toHub u).trans (toHub v).symm
  · haveI : Nonempty ((K r).cross i j hij).V := ⟨none⟩
    refine ⟨fun u v => ?_⟩
    have toHub : ∀ u : ((K r).cross i j hij).V, ((K r).cross i j hij).graph.Reachable u none := by
      rintro (_ | ⟨k, b⟩)
      · rfl
      · exact SimpleGraph.Adj.reachable (by
          change none ∈ ((K r).cross i j hij).nbrs (some (k, b)); rw [cross_nbrs_some]; simp)
    exact (toHub u).trans (toHub v).symm

end Podc.RandomizedPLS.Windmill
