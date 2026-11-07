import Papers.PODC2013.SourceDetectionCongest.Main
import Podc.Computability.Distributed.Congest.Typed

/-!
# Algorithm 1 in the CONGEST model

* `est_lt_card`: every stored (hence every sent) distance is `< n = |V|`, whatever `h` and `σ`:
  the provenance of an entry `(e, s)` is a walk `s = w_0, …, w_e = v` along which node `w_i`
  stored `(i, s)` at increasing times, and since stored distances never increase, the `w_i` are
  distinct. So a message of Algorithm 1 is one pair in `Fin n × V`, i.e. `O(log n)` bits.
* `pbf`: Algorithm 1 as a typed CONGEST algorithm (`Cslib.Congest.TAlgorithm`) on a simple graph,
  with messages in `Option (Fin n × V)`, so `msgBits ≤ 2⌈log₂ n⌉ + 1`
  (`msgBits_pbf_le`); `pbf_run` says its runs are those of `run G.Adj S 1 cap`, and
  `theorem_1_2_congest` restates Theorem 1.2 for the CSLib CONGEST algorithm
  `(pbf …).toAlgorithm` (with `B = msgBits` bits per message). Node inputs: `v ∈ S` (a `Bool`).
* `theorem_1_2_graph`: Theorem 1.2 for an undirected graph with Mathlib's `SimpleGraph.edist`.
-/

namespace Podc.SourceDetectionCongest

open Finset Cslib.Congest

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {E : V → V → Prop} [DecidableRel E] {S : Finset V} {β : ℕ} {cap : ℕ∞}

/-- Provenance of a stored distance: `est = e` at `v` after `r` rounds is witnessed by nodes
`w 0, …, w e = v` and strictly increasing times `τ 0 < … < τ e ≤ r` with `est = i` at `w i` after
`τ i` rounds. -/
lemma est_chain : ∀ (r : ℕ) (v s : V) (e : ℕ), (run E S β cap r v).est s = e →
    ∃ (w : ℕ → V) (τ : ℕ → ℕ), w e = v ∧ τ e ≤ r ∧
      (∀ i ≤ e, (run E S β cap (τ i) (w i)).est s = i) ∧ ∀ i < e, τ i < τ (i + 1)
  | 0, v, s, e, h => by
      have h' := h
      simp only [run, init] at h'
      split_ifs at h' with hs
      · obtain ⟨rfl, -⟩ := hs
        have he : e = 0 := by exact_mod_cast h'.symm
        subst he
        refine ⟨fun _ => s, fun _ => 0, rfl, le_rfl, fun i hi => ?_, fun i hi => by omega⟩
        obtain rfl : i = 0 := by omega
        exact h
      · exact absurd h'.symm (ENat.natCast_ne_top e)
  | r + 1, v, s, e, h => by
      have h' := h
      rw [est_succ] at h'
      split_ifs at h' with hc
      · exact absurd h'.symm (ENat.natCast_ne_top e)
      rcases min_choice ((run E S β cap r v).est s) (recv (inboxAt E S β cap r v) s) with he | he
      · rw [he] at h'
        obtain ⟨w, τ, hw, hτ, hest, hmono⟩ := est_chain r v s e h'
        exact ⟨w, τ, hw, by omega, hest, hmono⟩
      · rw [he] at h'
        obtain ⟨u, x, hx, hs, heq⟩ := exists_of_recv_ne_top (by rw [h']; simp)
        simp only [inboxAt] at hx
        split_ifs at hx with huv
        · obtain ⟨⟨m, s'⟩, rfl⟩ := toLex.surjective x
          simp only [ofLex_toLex] at hs heq
          subst hs
          rw [h'] at heq
          have hem : e = m + 1 := by exact_mod_cast heq
          subst hem
          have hu := State.mem_entries.1 (msg_subset_entries hx)
          obtain ⟨w, τ, hw, hτ, hest, hmono⟩ := est_chain r u s' m hu
          refine ⟨Function.update w (m + 1) v, Function.update τ (m + 1) (r + 1), by simp,
            by simp, fun i hi => ?_, fun i hi => ?_⟩
          · rcases Nat.lt_or_ge i (m + 1) with hi' | hi'
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hest i (by omega)
            · obtain rfl : i = m + 1 := by omega
              simpa using h
          · rw [Function.update_of_ne (by omega)]
            rcases Nat.lt_or_ge (i + 1) (m + 1) with hi' | hi'
            · rw [Function.update_of_ne (by omega)]; exact hmono i (by omega)
            · obtain rfl : i = m := by omega
              simp only [Function.update_self]
              omega
        · simp at hx

/-- **Distances stay below `n`.** Every stored distance is `< |V|`; in particular every pair sent
by Algorithm 1 is in `Fin |V| × V`. -/
theorem est_lt_card {r : ℕ} {v s : V} {e : ℕ} (h : (run E S β cap r v).est s = e) :
    e < Fintype.card V := by
  obtain ⟨w, τ, -, -, hest, hmono⟩ := est_chain r v s e h
  have hτ : ∀ j ≤ e, ∀ i < j, τ i < τ j := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i j with hij | hij
      · exact (ih (by omega) i hij).trans (hmono j (by omega))
      · obtain rfl : i = j := by omega
        exact hmono i (by omega)
  have key : ∀ i j, j ≤ e → i < j → w i = w j → False := by
    intro i j hj hlt hij
    have h1 := est_anti (E := E) (S := S) (β := β) (cap := cap) (hτ j hj i hlt).le (w i) s
    rw [hij, hest j hj, ← hij, hest i (by omega)] at h1
    have : j ≤ i := by exact_mod_cast h1
    omega
  have hinj : Set.InjOn w (range (e + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact (key i j (by omega) hlt hij).elim
    · exact heq
    · exact (key j i (by omega) hlt hij.symm).elim
  have := card_le_card_of_injOn w (s := range (e + 1)) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _)) hinj
  simp at this
  omega

lemma msg_dist_lt {t : ℕ} {v : V} {x : ℕ ×ₗ V} (hx : x ∈ msg β (run E S β cap t v)) :
    (ofLex x).1 < Fintype.card V := by
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
  exact est_lt_card (State.mem_entries.1 (msg_subset_entries hx))

/-! ### Algorithm 1 as a typed CONGEST algorithm -/

/-- A message of Algorithm 1: no pair, or one pair `(distance, source)` with distance `< n`. -/
abbrev PbfMsg (V : Type*) [Fintype V] := Option (Fin (Fintype.card V) × V)

/-- Encode a set of pairs as a message: its smallest pair (with the distance clamped to `n - 1`;
the clamp is never active, by `msg_dist_lt`). -/
noncomputable def encodeMsg (X : Finset (ℕ ×ₗ V)) : PbfMsg V :=
  if hX : X.Nonempty then
    some (⟨min (ofLex (X.min' hX)).1 (Fintype.card V - 1), by
      have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨(ofLex (X.min' hX)).2⟩
      omega⟩, (ofLex (X.min' hX)).2)
  else none

/-- Decode a message into a set of pairs. -/
def decodeMsg : PbfMsg V → Finset (ℕ ×ₗ V)
  | none => ∅
  | some p => {toLex ((p.1 : ℕ), p.2)}

lemma decode_encode_msg {X : Finset (ℕ ×ₗ V)} (h1 : #X ≤ 1)
    (hX : ∀ x ∈ X, (ofLex x).1 < Fintype.card V) : decodeMsg (encodeMsg X) = X := by
  unfold encodeMsg
  split_ifs with hne
  · obtain ⟨a, rfl⟩ := card_le_one_iff_subsingleton_coe.1 h1 |> fun _ =>
      (card_eq_one.1 (le_antisymm h1 (card_pos.2 hne)))
    have ha := hX a (mem_singleton_self a)
    simp only [decodeMsg, min'_singleton]
    congr 1
    rw [min_eq_left (by omega)]
    rfl
  · simp only [decodeMsg]; exact (not_nonempty_iff_eq_empty.1 hne).symm

/-- Algorithm 1 (with Line 16 at `cap`) as a typed CONGEST algorithm on a simple graph: node
input `true` iff the node is a source. -/
noncomputable def pbf (V : Type*) [Fintype V] [LinearOrder V] (cap : ℕ∞) :
    TAlgorithm V Bool (State V) (PbfMsg V) where
  init v b := { est := fun s => if s = v ∧ b = true then 0 else ⊤, sent := fun _ => false }
  send _ st _ := encodeMsg (msg 1 st)
  step _ st m := step 1 cap st fun u => match m u with
    | some o => decodeMsg o
    | none => ∅

/-- The typed CONGEST algorithm has exactly the runs of Algorithm 1 on `G.Adj`. -/
theorem pbf_run (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (cap : ℕ∞) :
    ∀ t, (pbf V cap).run G (fun v => decide (v ∈ S)) t = run G.Adj S 1 cap t
  | 0 => by
      funext v
      simp [TAlgorithm.run, pbf, run, init]
  | t + 1 => by
      funext v
      rw [TAlgorithm.run_succ, pbf_run G S cap t]
      simp only [pbf]
      rw [run_succ]
      congr 1
      funext u
      simp only [inboxAt]
      split_ifs with huv
      · exact decode_encode_msg (card_msg_le 1 _) fun x hx => msg_dist_lt hx
      · rfl

omit [LinearOrder V] in
lemma msgBits_pbf_le :
    TAlgorithm.msgBits (PbfMsg V) ≤ 2 * Nat.clog 2 (Fintype.card V) + 1 := by
  unfold TAlgorithm.msgBits
  apply Nat.clog_le_of_le_pow
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card V)
  set c := Nat.clog 2 (Fintype.card V)
  have : Fintype.card V * Fintype.card V ≤ 2 ^ c * 2 ^ c := Nat.mul_le_mul h h
  have h1 : 1 ≤ 2 ^ c * 2 ^ c := Nat.one_le_iff_ne_zero.2 (by positivity)
  calc Fintype.card V * Fintype.card V + 1 ≤ 2 ^ c * 2 ^ c + 2 ^ c * 2 ^ c := by omega
    _ = 2 ^ (2 * c + 1) := by ring

/-- **Theorem 1.2 in the CONGEST model.** On a simple graph `G`, the CSLib CONGEST algorithm
`(pbf V ⊤).toAlgorithm out` sends messages of `msgBits ≤ 2⌈log₂ n⌉ + 1` bits, and after
`σ + h - 1` rounds every node's state yields `top_σ(L_v^{(h)})` (`hd` = `G.edist`). -/
theorem theorem_1_2_congest (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (out : V → State V → Bool) (h σ : ℕ) (v : V) :
    (output h σ (((pbf V ⊤).toAlgorithm out).run G (fun v => decide (v ∈ S)) (σ + h - 1) v)).sort
      (· ≤ ·) = ((Lspec G.Adj S h v).sort (· ≤ ·)).take σ := by
  rw [TAlgorithm.run_toAlgorithm, pbf_run]
  exact theorem_1_2 S h σ v

omit [Fintype V] in
/-- `L_v^{(h)}` for a simple graph, in terms of Mathlib's graph distance. -/
lemma mem_Lspec_graph (G : SimpleGraph V) {S : Finset V} {d m : ℕ} {s v : V} :
    toLex (m, s) ∈ Lspec G.Adj S d v ↔ s ∈ S ∧ G.edist v s = m ∧ m ≤ d := by
  rw [mem_Lspec, hd_adj_eq_edist, SimpleGraph.edist_comm]

/-- **Theorem 1.2** for an undirected graph `G`: after `σ + h - 1` rounds of Algorithm 1 every
node `v` outputs the first `σ` elements of the lexicographically sorted list of pairs
`(hd(v, s), s)`, `s ∈ S`, `hd(v, s) ≤ h` (`mem_Lspec_graph`). -/
theorem theorem_1_2_graph (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (h σ : ℕ)
    (v : V) :
    (output h σ (alg1 G.Adj S (σ + h - 1) v)).sort (· ≤ ·) =
      ((Lspec G.Adj S h v).sort (· ≤ ·)).take σ :=
  theorem_1_2 S h σ v

end Podc.SourceDetectionCongest
