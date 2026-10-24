import Papers.PODC2025.AmnesiacFloodingFaults.Theorem51
import Papers.PODC2025.AmnesiacFloodingFaults.OneMessage

/-!
# Fault sensitivity (Section 5.2.2, Appendix D): Theorems 5.6, 5.7, 5.8

Fault models (Section 5.2.2), with the natural indexing: faults may act from the very first
round on (see `differencies.md` for the paper's literal indexing).

* **Message dropping** — the fault-free single-source run `srcRun G s t = A_∅^t(A_{{s}}(∅))`
  loses the message `m` of round `k`; the run continues from `srcRun G s k \ {m}`.
* **Uni-directional link failure** — `uniRun G I X`: every round, the messages in the set `X`
  of failed directed links are lost.
* **Weak-Byzantine nodes** — `byzRun G I J k B`: until round `k` the nodes of `J` send the
  messages `B t` of the adversary's choice (along edges); the other nodes follow the protocol;
  from round `k` on everybody follows the protocol.

Main results:
* `theorem_5_6_nonterm` — dropping a message on a non-bridge, or on the path of a faux-even cycle,
  makes single-source amnesiac flooding non-terminating (Theorem 5.6, first part).
* `fails_of_failed_link` — if the link `a → b` fails but `b → a` works, flooding initiated at `a`
  fails to broadcast or fails to terminate. Corollaries: `theorem_5_7_singleton` (first claim of
  Theorem 5.7 for a single initiator; false for larger initiator sets, see
  `theorem_5_7_multi_false`) and `theorem_5_7_second` (second claim).
* `theorem_5_8_nonterm` — a weak-Byzantine set `J` can force non-termination iff some member of
  `J` lies on a cycle or on a path between two odd cycles (Theorem 5.8, second part).
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-! ### Single message drop (Theorem 5.6) -/

variable (G) in
/-- The fault-free run of single-source amnesiac flooding: `srcRun G s t` is the set of messages
sent in round `t + 1`. -/
def srcRun (s : V) (t : ℕ) : Config V := (af G)^[t] (step G {s} ∅)

lemma srcRun_reachable (s : V) (t : ℕ) : Reachable G (srcRun G s t) := by
  induction t with
  | zero => exact reachable_empty.step {s}
  | succ t ih =>
    rw [srcRun, Function.iterate_succ_apply']
    exact ih.step ∅

/-- **Theorem 5.6** (single message failure, non-termination). If single-source amnesiac
flooding loses the message `(u, v)` in some round, and `uv` is not a bridge or `uv` lies on a
path between two odd cycles (the path of a faux-even cycle), then flooding does not terminate. -/
theorem theorem_5_6_nonterm [Fintype V] {s u v : V} {k : ℕ} (hm : (u, v) ∈ srcRun G s k)
    (h : ¬ G.IsBridge s(u, v) ∨ ∃ F : FEC G, s(u, v) ∈ F.p.edges) :
    ¬ Terminates G (srcRun G s k \ {(u, v)}) := by
  intro ht
  have hS := (srcRun_reachable (G := G) s k).balancedAll
  have hadj : G.Adj u v := (srcRun_reachable (G := G) s k).isConfig u v hm
  exact not_balancedAll_sdiff hS hm hadj h ht.balancedAll

/-! ### Uni-directional link failures (Theorem 5.7) -/

variable (G) in
/-- Amnesiac flooding from the initiators `I` when the directed links in `X` have failed:
`uniRun G I X t` is the set of messages delivered in round `t + 1`. -/
def uniRun (I : Set V) (X : Set (V × V)) : ℕ → Config V
  | 0 => step G I ∅ \ X
  | t + 1 => af G (uniRun I X t) \ X

variable (G) in
/-- Flooding from `I` with failed links `X` fails to terminate or fails to broadcast (some
non-initiator never receives the message). -/
def UniFails (I : Set V) (X : Set (V × V)) : Prop :=
  (∀ t, uniRun G I X t ≠ ∅) ∨ ∃ v, v ∉ I ∧ ∀ t, ¬ Active (uniRun G I X t) v

lemma exists_walk_of_reflTransGen {X : Set (V × V)} {a b : V}
    (h : Relation.ReflTransGen (fun x y => G.Adj x y ∧ (x, y) ∉ X) a b) :
    ∃ p : G.Walk a b, ∀ d ∈ p.darts, d.toProd ∉ X := by
  induction h with
  | refl => exact ⟨Walk.nil, by simp⟩
  | tail _ hyz ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat hyz.1, fun d hd => ?_⟩
    rw [Walk.darts_concat, List.concat_eq_append, List.mem_append] at hd
    rcases hd with hd | hd
    · exact hp d hd
    · simp only [List.mem_singleton] at hd; subst hd; exact hyz.2

lemma getVert_pair_notMem {X : Set (V × V)} {x y : V} (p : G.Walk x y)
    (hp : ∀ d ∈ p.darts, d.toProd ∉ X) {i : ℕ} (hi : i < p.length) :
    (p.getVert i, p.getVert (i + 1)) ∉ X := by
  induction p generalizing i with
  | nil => simp at hi
  | cons h q ih =>
    cases i with
    | zero =>
      simpa [Walk.getVert_cons_succ] using hp _ (List.mem_cons_self ..)
    | succ i =>
      rw [Walk.getVert_cons_succ, Walk.getVert_cons_succ]
      exact ih (fun d hd => hp d (List.mem_cons_of_mem _ hd)) (by simp at hi; omega)

/-- Flow is non-decreasing under a round with link failures, along a closed walk all of whose
clockwise links work. -/
lemma flowSum_le_of_failures [NeZero L'] {w : ZMod L' → V} (hw : IsClosedWalk G w)
    (S : Config V) (X : Set (V × V)) (hX : ∀ k, (w k, w (k + 1)) ∉ X) :
    flowSum S w ≤ flowSum (af G S \ X) w := by
  rw [← sum_cw_sub_ccw, ← sum_cw_sub_ccw]
  have hshift : ∑ k, (ind (cw S w (k - 1)) - ind (ccw S w (k + 1))) =
      ∑ k, (ind (cw S w k) - ind (ccw S w k)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    congr 1
    · exact Equiv.sum_comp (Equiv.subRight (1 : ZMod L')) (fun k => ind (cw S w k))
    · exact Equiv.sum_comp (Equiv.addRight (1 : ZMod L')) (fun k => ind (ccw S w k))
  rw [← hshift]
  apply Finset.sum_le_sum
  intro k _
  rw [← ind_cw_step_sub hw ∅ S k]
  have h1 : ind (cw (af G S \ X) w k) = ind (cw (af G S) w k) :=
    ind_congr ⟨fun h => h.1, fun h => ⟨h, hX k⟩⟩
  have h2 : ind (ccw (af G S \ X) w k) ≤ ind (ccw (af G S) w k) := by
    by_cases h : ccw (af G S \ X) w k
    · rw [ind_of h, ind_of (show ccw (af G S) w k from h.1)]
    · rw [ind_of_not h]; exact ind_nonneg _
  rw [h1]; linarith

lemma walkFlow_gS_eq_zero_of_notMem {S : Config V} {a : V} (hS : ∀ e ∈ S, e.1 = a)
    {x y : V} (p : G.Walk x y) (hp : a ∉ p.support) : walkFlow (gS S) p = 0 := by
  induction p with
  | nil => rfl
  | @cons x' y' z' h p ih =>
    simp only [Walk.support_cons, List.mem_cons, not_or] at hp
    rw [walkFlow, ih hp.2]
    have h1 : (x', y') ∉ S := fun hm => hp.1 (hS _ hm).symm
    have h2 : (y', x') ∉ S := fun hm => hp.2 (by
      have := hS _ hm; simp only at this; subst this; exact p.start_mem_support)
    simp [gS, ind_of_not h1, ind_of_not h2]

/-- **Lemma D.3 / proof of Theorem 5.7.** If the directed link `a → b` has failed while `b → a`
works, amnesiac flooding initiated at `a` fails to broadcast or fails to terminate. Either `b` is
unreachable from `a` along working links (then `b` never receives the message), or there is a
cycle `a ⇝ b → a` all of whose links work in the cycle direction; initially exactly one message
travels in that direction around it, and the number of messages travelling with the cycle minus
those travelling against it never decreases. -/
theorem fails_of_failed_link [Fintype V] {X : Set (V × V)} {a b : V} (hab : G.Adj a b)
    (hX : (a, b) ∈ X) (hba : (b, a) ∉ X) : UniFails G {a} X := by
  classical
  set D : V → V → Prop := fun x y => G.Adj x y ∧ (x, y) ∉ X
  by_cases hR : Relation.ReflTransGen D a b
  · left
    obtain ⟨p₀, hp₀⟩ := exists_walk_of_reflTransGen hR
    set p := p₀.bypass
    have hpath : p.IsPath := p₀.bypass_isPath
    have hpd : ∀ d ∈ p.darts, d.toProd ∉ X := fun d hd =>
      hp₀ d (p₀.darts_bypass_subset_darts hd)
    -- the path is nonempty since `a ≠ b`
    cases hcase : p with
    | nil => exact absurd rfl hab.ne
    | @cons _ y _ hay q =>
      rw [hcase] at hpath hpd
      rw [Walk.cons_isPath_iff] at hpath
      have hay' : (a, y) ∉ X := hpd ⟨(a, y), hay⟩ (by simp)
      let c : G.Walk a a := (Walk.cons hay q).concat hab.symm
      have hclen : 0 < c.length := by simp [c]
      have : NeZero c.length := ⟨hclen.ne'⟩
      set w := toFun c
      have hw : IsClosedWalk G w := isClosedWalk_toFun c hclen
      -- all clockwise links of `c` work
      have hcd : ∀ d ∈ c.darts, d.toProd ∉ X := by
        intro d hd
        simp only [c, Walk.darts_concat, List.concat_eq_append, List.mem_append,
          List.mem_singleton] at hd
        rcases hd with hd | rfl
        · exact hpd d hd
        · exact hba
      have hXw : ∀ k, (w k, w (k + 1)) ∉ X := by
        intro k
        have hk := ZMod.val_lt k
        have e1 : w (k + 1) = c.getVert (k.val + 1) := by
          simp only [w, toFun]
          rw [← getVert_succ_toFun c hk, ZMod.natCast_zmod_val]
        rw [e1]
        exact getVert_pair_notMem c hcd hk
      -- initial flow is `1`
      have hU0 : ∀ e ∈ uniRun G {a} X 0, e.1 = a := by
        rintro ⟨x, z⟩ ⟨⟨-, -, hx⟩, -⟩
        simpa [Active] using hx
      have hflow0 : flowSum (uniRun G {a} X 0) w = 1 := by
        rw [flowSum_toFun, walkFlow_concat_aux, walkFlow,
          walkFlow_gS_eq_zero_of_notMem hU0 q hpath.2]
        have h1 : (a, y) ∈ uniRun G {a} X 0 := ⟨⟨hay, by simp, by simp⟩, hay'⟩
        have h2 : (y, a) ∉ uniRun G {a} X 0 := fun h => hay.ne (hU0 _ h).symm
        have h3 : (b, a) ∉ uniRun G {a} X 0 := fun h => hab.ne (hU0 _ h).symm
        have h4 : (a, b) ∉ uniRun G {a} X 0 := fun h => h.2 hX
        simp [gS, ind_of h1, ind_of_not h2, ind_of_not h3, ind_of_not h4]
      have hmono : ∀ t, 1 ≤ flowSum (uniRun G {a} X t) w := by
        intro t
        induction t with
        | zero => rw [hflow0]
        | succ t ih => exact ih.trans (flowSum_le_of_failures hw _ X hXw)
      intro t ht
      have := hmono t
      rw [ht] at this
      simp [flowSum, gS, ind_of_not] at this
  · right
    refine ⟨b, fun h => hab.ne (h.symm), fun t => ?_⟩
    have key : ∀ t, ∀ x z, (x, z) ∈ uniRun G {a} X t → Relation.ReflTransGen D a z := by
      intro t
      induction t with
      | zero =>
        rintro x z ⟨⟨hxz, -, hx⟩, hX'⟩
        have : x = a := by simpa [Active] using hx
        subst this
        exact Relation.ReflTransGen.single ⟨hxz, hX'⟩
      | succ t ih =>
        rintro x z ⟨⟨hxz, -, hx⟩, hX'⟩
        obtain ⟨y, hy⟩ := hx.resolve_left (Set.notMem_empty _)
        exact (ih y x hy).tail ⟨hxz, hX'⟩
    rintro ⟨x, hx⟩
    exact hR (key t x b hx)

/-- **Theorem 5.7, first claim, for a single initiator.** For every node `s` with a neighbour there
is a uni-directional link failure (of a link at `s`) making amnesiac flooding from `s` fail to
broadcast or fail to terminate. (The paper states this for every initiator set `I ⊊ V`; that is
false, see `theorem_5_7_multi_false`.) -/
theorem theorem_5_7_singleton [Fintype V] {s b : V} (hsb : G.Adj s b) :
    ∃ e : V × V, G.Adj e.1 e.2 ∧ UniFails G {s} {e} :=
  ⟨(s, b), hsb, fails_of_failed_link hsb rfl (fun h => hsb.ne (congrArg Prod.fst h).symm)⟩

/-- **Theorem 5.7, second claim.** For every non-empty set `X` of uni-directional link failures
(no link fails in both directions) there is a node `v` such that amnesiac flooding initiated at
`v` fails to broadcast or fails to terminate. -/
theorem theorem_5_7_second [Fintype V] {X : Set (V × V)} (hXE : ∀ e ∈ X, G.Adj e.1 e.2)
    (huni : ∀ u v, (u, v) ∈ X → (v, u) ∉ X) (hne : X.Nonempty) :
    ∃ v, UniFails G {v} X := by
  obtain ⟨⟨a, b⟩, hX⟩ := hne
  exact ⟨a, fails_of_failed_link (hXE _ hX) hX (huni a b hX)⟩

/-! ### Weak-Byzantine nodes (Theorem 5.8) -/

variable (G) in
/-- One round under a weak-Byzantine adversary controlling `J` until round `k`: the honest
messages of `X`, together with the messages `B` of the adversary sent from `J` along edges. -/
def byzMix (J : Set V) (k t : ℕ) (B : Config V) (X : Config V) : Config V :=
  if t < k then {e ∈ X | e.1 ∉ J} ∪ {e ∈ B | e.1 ∈ J ∧ G.Adj e.1 e.2} else X

variable (G) in
/-- Amnesiac flooding from `I` under a weak-Byzantine adversary controlling `J` until round `k`
and sending `B t` in round `t + 1`. -/
def byzRun (I J : Set V) (k : ℕ) (B : ℕ → Config V) : ℕ → Config V
  | 0 => byzMix G J k 0 (B 0) (step G I ∅)
  | t + 1 => byzMix G J k (t + 1) (B (t + 1)) (af G (byzRun I J k B t))

lemma byzRun_isConfig (I J : Set V) (k : ℕ) (B : ℕ → Config V) (t : ℕ) :
    IsConfig G (byzRun G I J k B t) := by
  have hmix : ∀ t' B' X, IsConfig G X → IsConfig G (byzMix G J k t' B' X) := by
    intro t' B' X hX u v h
    unfold byzMix at h
    split_ifs at h
    · rcases h with h | h
      · exact hX u v h.1
      · exact h.2.2
    · exact hX u v h
  cases t with
  | zero => exact hmix _ _ _ (isConfig_step _ _)
  | succ t => exact hmix _ _ _ (isConfig_step _ _)

lemma byzRun_add (I J : Set V) (k : ℕ) (B : ℕ → Config V) (t : ℕ) :
    byzRun G I J k B (k + t + 1) = af G (byzRun G I J k B (k + t)) := by
  rw [show k + t + 1 = (k + t) + 1 from rfl, byzRun, byzMix, ite_eq_right (by omega)]

lemma byzRun_eventually (I J : Set V) (k : ℕ) (B : ℕ → Config V) (t : ℕ) :
    byzRun G I J k B (k + t) = (af G)^[t] (byzRun G I J k B k) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [← add_assoc, byzRun_add, ih, Function.iterate_succ_apply']

/-- The adversary run eventually stops sending messages. -/
def EventuallyQuiet (R : ℕ → Config V) : Prop := ∃ T, ∀ t ≥ T, R t = ∅

lemma eventuallyQuiet_byzRun_iff (I J : Set V) (k : ℕ) (B : ℕ → Config V) :
    EventuallyQuiet (byzRun G I J k B) ↔ Terminates G (byzRun G I J k B k) := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    rw [← byzRun_eventually]; exact hT _ (by omega)
  · rintro ⟨m, hm⟩
    refine ⟨k + m, fun t ht => ?_⟩
    obtain ⟨r, rfl⟩ : ∃ r, t = k + m + r := ⟨t - (k + m), by omega⟩
    rw [add_assoc, byzRun_eventually, add_comm m r, Function.iterate_add_apply, hm,
      iterate_af_empty]

variable (G) in
/-- `j` lies on a cycle, or on a path between two odd cycles (the path of a faux-even cycle). -/
def OnCycleOrOddPath (j : V) : Prop :=
  (∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ j ∈ c.support) ∨ ∃ F : FEC G, j ∈ F.p.support

lemma mem_support_of_length_zero {x y j : V} (p : G.Walk x y) (h0 : p.length = 0)
    (hj : j ∈ p.support) : j = x := by
  cases p with
  | nil => simpa using hj
  | cons _ _ => simp at h0

lemma exists_edge_of_mem_support {x y j : V} (p : G.Walk x y) (hp : 0 < p.length)
    (hj : j ∈ p.support) : ∃ z, s(j, z) ∈ p.edges := by
  induction p with
  | nil => simp at hp
  | @cons a b c h q ih =>
    rw [Walk.support_cons, List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨b, by simp⟩
    · cases q with
      | nil =>
        simp only [Walk.support_nil, List.mem_singleton] at hj
        subst hj; exact ⟨a, by simp [Sym2.eq_swap]⟩
      | cons h' q' =>
        obtain ⟨z, hz⟩ := ih (by simp) hj
        exact ⟨z, by simp only [Walk.edges_cons, List.mem_cons] at hz ⊢; tauto⟩

/-- A node on a cycle or on the path of a faux-even cycle has an incident edge that is not a
bridge or lies on the path of a faux-even cycle. -/
lemma exists_bad_edge {j : V} (h : OnCycleOrOddPath G j) :
    ∃ z, G.Adj j z ∧ (¬ G.IsBridge s(j, z) ∨ ∃ F : FEC G, s(j, z) ∈ F.p.edges) := by
  classical
  have hcyc : ∀ (u : V) (c : G.Walk u u), c.IsCycle → j ∈ c.support →
      ∃ z, G.Adj j z ∧ ¬ G.IsBridge s(j, z) := by
    intro u c hc hj
    have hlen : 0 < c.length := by have := hc.three_le_length; omega
    obtain ⟨z, hz⟩ := exists_edge_of_mem_support c hlen hj
    have hadj := c.adj_of_mem_edges hz
    refine ⟨z, hadj, fun hb => ?_⟩
    exact hb.notMem_edges_of_isCycle hc hz
  rcases h with ⟨u, c, hc, hj⟩ | ⟨F, hF⟩
  · obtain ⟨z, hz, hb⟩ := hcyc u c hc hj
    exact ⟨z, hz, Or.inl hb⟩
  · rcases Nat.eq_zero_or_pos F.p.length with h0 | hpos
    · -- the path is trivial, so `j` is the junction vertex, on the first cycle
      have : j = F.u := mem_support_of_length_zero F.p h0 hF
      obtain ⟨z, hz, hb⟩ := hcyc _ F.c₁ F.isCycle₁ (this ▸ F.c₁.start_mem_support)
      exact ⟨z, hz, Or.inl hb⟩
    · obtain ⟨z, hz⟩ := exists_edge_of_mem_support F.p hpos hF
      exact ⟨z, F.p.adj_of_mem_edges hz, Or.inr ⟨F, hz⟩⟩

lemma balancedOn_congr {S S' : Config V} {L' : ℕ} {w : ZMod L' → V}
    (h : ∀ k, (w k, w (k + 1)) ∈ S ↔ (w k, w (k + 1)) ∈ S')
    (h' : ∀ k, (w k, w (k - 1)) ∈ S ↔ (w k, w (k - 1)) ∈ S') :
    BalancedOn S w ↔ BalancedOn S' w := by
  have : ∀ k₀, classSum S w k₀ = classSum S' w k₀ := by
    intro k₀; unfold classSum
    apply Finset.sum_congr rfl; intro i _
    exact congrArg₂ (· - ·) (ind_congr (h _)) (ind_congr (h' _))
  simp only [BalancedOn, this]

/-- Along a closed walk avoiding `J`, the adversary cannot change the balance. -/
lemma balancedOn_byzRun {I J : Set V} {k : ℕ} {B : ℕ → Config V} {L' : ℕ} [NeZero L']
    {w : ZMod L' → V} (hw : IsClosedWalk G w) (hJ : ∀ k, w k ∉ J) (t : ℕ) :
    BalancedOn (byzRun G I J k B t) w := by
  have hmix : ∀ t' B' X, BalancedOn (byzMix G J k t' B' X) w ↔ BalancedOn X w := by
    intro t' B' X
    unfold byzMix
    split_ifs
    · apply balancedOn_congr <;> intro i <;> simp [hJ i]
    · rfl
  induction t with
  | zero =>
    rw [byzRun, hmix, balancedOn_step_iff hw]; exact balancedOn_empty w
  | succ t ih => rw [byzRun, hmix, balancedOn_step_iff hw]; exact ih

/-- **Theorem 5.8** (weak-Byzantine failure, non-termination). Let the initiators `I` and the
weak-Byzantine set `J` be disjoint, and let the adversary control `J` until a round `k ≥ k₀` of its
choice (in the paper `k₀` is twice the diameter). The adversary can force non-termination iff
some member of `J` lies on a cycle or on a path between two odd cycles. -/
theorem theorem_5_8_nonterm [Fintype V] {I J : Set V} (hIJ : Disjoint I J) (k₀ : ℕ) :
    (∃ k ≥ k₀, ∃ B, ¬ EventuallyQuiet (byzRun G I J k B)) ↔ ∃ j ∈ J, OnCycleOrOddPath G j := by
  classical
  constructor
  · rintro ⟨k, -, B, hB⟩
    by_contra hno
    push Not at hno
    apply hB
    rw [eventuallyQuiet_byzRun_iff]
    apply (terminates_iff_balancedAll (byzRun_isConfig I J k B k)).2
    apply Balanced.balancedAll
    have avoid : ∀ (u : V) (p : G.Walk u u), (∀ x ∈ p.support, x ∉ J) → 0 < p.length →
        BalancedOn (byzRun G I J k B k) (toFun p) := by
      intro u p hp hpos
      have : NeZero p.length := ⟨hpos.ne'⟩
      exact balancedOn_byzRun (isClosedWalk_toFun p hpos)
        (fun i => hp _ (p.getVert_mem_support _)) k
    refine ⟨fun u c hc => avoid u c (fun x hx hxJ => hno x hxJ (Or.inl ⟨u, c, hc, hx⟩))
      (by have := hc.three_le_length; omega), fun F => avoid _ F.walk ?_ F.walk_length_pos⟩
    intro x hx hxJ
    simp only [FEC.walk, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hx
    rcases hx with hx | hx | hx | hx
    · exact hno x hxJ (Or.inl ⟨_, _, F.isCycle₁, hx⟩)
    · exact hno x hxJ (Or.inr ⟨F, hx⟩)
    · exact hno x hxJ (Or.inl ⟨_, _, F.isCycle₂, hx⟩)
    · exact hno x hxJ (Or.inr ⟨F, hx⟩)
  · rintro ⟨j, hjJ, hj⟩
    obtain ⟨z, hjz, hbad⟩ := exists_bad_edge hj
    set Z₀ : Config V := step G I ∅ ∪ {(j, z)}
    refine ⟨k₀ + 1, by omega, fun t => (af G)^[t] Z₀, ?_⟩
    have hjI : j ∉ I := fun h => Set.disjoint_left.1 hIJ h hjJ
    have hZ0J : ∀ e ∈ step G I ∅, e.1 ∉ J := by
      rintro ⟨x, y⟩ ⟨-, -, hx⟩ hxJ
      rcases hx with hx | ⟨w, hw⟩
      · exact Set.disjoint_left.1 hIJ hx hxJ
      · exact hw
    have hZc : IsConfig G Z₀ := by
      rintro x y (h | h)
      · exact isConfig_step _ _ x y h
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact hjz
    have mix_eq : ∀ t (X Y : Config V), t < k₀ + 1 → IsConfig G Y →
        (∀ e : V × V, e.1 ∉ J → (e ∈ X ↔ e ∈ Y)) → byzMix G J (k₀ + 1) t Y X = Y := by
      intro t X Y ht hY hXY
      unfold byzMix
      rw [ite_eq_left ht]
      ext e
      simp only [Set.mem_union, Set.mem_sep_iff]
      by_cases he : e.1 ∈ J
      · exact ⟨fun h => h.elim (fun h => absurd he h.2) (fun h => h.1),
          fun h => Or.inr ⟨h, he, hY _ _ h⟩⟩
      · exact ⟨fun h => h.elim (fun h => (hXY e he).1 h.1) (fun h => absurd h.2.1 he),
          fun h => Or.inl ⟨(hXY e he).2 h, he⟩⟩
    have hrun : ∀ t, byzRun G I J (k₀ + 1) (fun t => (af G)^[t] Z₀) t = (af G)^[t] Z₀ := by
      intro t
      induction t with
      | zero =>
        rw [byzRun]
        apply mix_eq 0 _ _ (by omega) hZc
        intro e he
        constructor
        · intro h; exact Or.inl h
        · rintro (h | h)
          · exact h
          · simp only [Set.mem_singleton_iff] at h; subst h; exact absurd hjJ he
      | succ t ih =>
        rw [byzRun, ih, ← Function.iterate_succ_apply' (af G)]
        by_cases ht : t + 1 < k₀ + 1
        · exact mix_eq _ _ _ ht (isConfig_iterate hZc _) (fun _ _ => Iff.rfl)
        · unfold byzMix; rw [ite_eq_right ht]
    rw [eventuallyQuiet_byzRun_iff, hrun, terminates_iterate_iff]
    have hZ : Reachable G (step G I ∅) := reachable_empty.step I
    have hnot : (j, z) ∉ step G I ∅ := fun h => hZ0J _ h hjJ
    exact fun ht => not_balancedAll_union hZ.balancedAll hnot hjz hbad ht.balancedAll

end AmnesiacFloodingFaults
