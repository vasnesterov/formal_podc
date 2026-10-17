import Mathlib
import Podc.DynamicNetworks.FullInfo
import Podc.Knowledge.Basic

/-!
# The dynamic-network model of Kuhn–Moses–Oshman (PODC 2011)

Synchronous rounds; round `r ≥ 1` takes place between time `r - 1` and time `r`. In every
round the adversary picks an undirected communication graph on the (fixed, finite) node set `V`
which must be connected (1-interval connectivity); every node broadcasts to its current
neighbours.

* Nodes are their UIDs: `V : Finset ℕ`. Different executions may have different node sets,
  which is needed for the "unknown `n`" results.
* `input : ℕ → α` is the input assignment (only its values on `V` matter), `N : ℕ` is the a-priori
  information given to every node (exact count, upper bound on the count, or a dummy `0` when
  nothing is known). Together these form the paper's *signature* `σ`.
* `adj r x y`: `{x, y} ∈ E(r)`.

Causality: `G.Reach v s u t` is the paper's `(v, s) ↝_G (u, t)` (reflexive-transitive closure of
`(u, t) → (v, t + 1)` iff `u = v` or `{u, v} ∈ E(t + 1)`), i.e. a journey
(`Cslib.DynNet.Journey`) in the dynamic network whose graph between times `k` and `k + 1` is
`adj (k + 1)`; `G.past u t s` is `past_{(G,u,t)}(s)`.

Views / indistinguishability: rather than building the view object of Definition 1, we define the
relation "same full-information view" `Indist G H u t` (the paper's `(G, t) ∼_u (H, t)`)
recursively: at time `0` a node sees its UID, input and `N`; at time `t + 1` it additionally sees
the identities of its round-`t+1` neighbours and their views at time `t`. This is the
full-information indistinguishability `Cslib.HeardOf.FIIndist` with the initial views above
(`Indist.zero_iff`, `Indist.succ_iff` restate the recursion).
`Protocol.state_eq_of_indist` shows that the local state of *every* deterministic protocol is a
function of this view, so lower bounds proved for view-local decision functions apply to all
protocols.
-/

namespace CoordCons

open Relation
open Cslib.DynNet (Journey)

/-- A dynamic graph together with its signature (node set = UIDs, inputs, a-priori info). -/
structure DGraph (α : Type*) where
  /-- The node set (= set of UIDs). -/
  V : Finset ℕ
  /-- The input assignment (only its values on `V` matter). -/
  input : ℕ → α
  /-- A-priori information known to all nodes (count / bound on the count / dummy). -/
  N : ℕ
  /-- `adj r x y` : `{x, y}` is an edge of the communication graph of round `r` (`r ≥ 1`). -/
  adj : ℕ → ℕ → ℕ → Prop

variable {α : Type*}

namespace DGraph

/-- Well-formed executions: undirected loopless graphs on `V`, connected in every round `r ≥ 1`. -/
structure Valid (G : DGraph α) : Prop where
  nonempty : G.V.Nonempty
  mem : ∀ r x y, G.adj r x y → x ∈ G.V ∧ y ∈ G.V
  symm : ∀ r x y, G.adj r x y → G.adj r y x
  irrefl : ∀ r x, ¬ G.adj r x x
  conn : ∀ r, 1 ≤ r → ∀ x ∈ G.V, ∀ y ∈ G.V, ReflTransGen (G.adj r) x y

/-! ### Causal order -/

/-- `G.Reach v s u t` : `(v, s) ↝_G (u, t)`: a journey from `v` at time `s` to `u` at time `t`,
where round `r` (between times `r - 1` and `r`) uses the edges `adj r`. -/
abbrev Reach (G : DGraph α) (v s u t : ℕ) : Prop :=
  Cslib.DynNet.Journey (fun k => G.adj (k + 1)) s v t u

variable {G H : DGraph α}

theorem Reach.mem_iff (hG : G.Valid) {v s u t : ℕ} (h : G.Reach v s u t) :
    v ∈ G.V ↔ u ∈ G.V := by
  induction h with
  | refl => rfl
  | step _ hs ih =>
    rcases hs with rfl | hs
    · exact ih
    · exact ih.trans (iff_of_true (hG.mem _ _ _ hs).1 (hG.mem _ _ _ hs).2)

theorem _root_.Relation.ReflTransGen.symm_of {β : Type*} {r : β → β → Prop}
    (hr : ∀ a b, r a b → r b a) {a b : β} (h : ReflTransGen r a b) : ReflTransGen r b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (hr _ _ hbc) ih

open Classical in
/-- `past_{(G,u,t)}(s) = {v ∈ V | (v, s) ↝ (u, t)}`. -/
noncomputable def past (G : DGraph α) (u t s : ℕ) : Finset ℕ :=
  G.V.filter fun v => G.Reach v s u t

theorem mem_past {u t s v : ℕ} : v ∈ G.past u t s ↔ v ∈ G.V ∧ G.Reach v s u t := by
  classical
  simp [past]

theorem past_subset (u t s : ℕ) : G.past u t s ⊆ G.V := fun _ hv => (mem_past.1 hv).1

theorem past_succ_subset (u t s : ℕ) : G.past u t (s + 1) ⊆ G.past u t s := by
  intro v hv
  rw [mem_past] at *
  exact ⟨hv.1, hv.2.mono_left (by omega)⟩

theorem past_mono_right {u t s s' : ℕ} (h : s ≤ s') : G.past u t s' ⊆ G.past u t s := by
  intro v hv
  rw [mem_past] at *
  exact ⟨hv.1, hv.2.mono_left h⟩

theorem past_mono_left {u t t' s : ℕ} (h : t ≤ t') : G.past u t s ⊆ G.past u t' s := by
  intro v hv
  rw [mem_past] at *
  exact ⟨hv.1, hv.2.trans (Journey.self h)⟩

/-! ### Flooding: connectivity forces the past to grow by one node per round -/

/-- If `past(u,t)(s+1) ≠ V`, then `past(u,t)(s)` is strictly larger (connectivity of round
`s + 1`). -/
theorem past_ssubset (hG : G.Valid) {u t s : ℕ} (hu : u ∈ G.V) (hst : s < t)
    (hne : G.past u t (s + 1) ≠ G.V) : G.past u t (s + 1) ⊂ G.past u t s := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨past_succ_subset u t s, fun heq => hne ?_⟩
  apply Finset.Subset.antisymm (past_subset _ _ _)
  intro y hy
  by_contra hyp
  have hu' : u ∈ G.past u t (s + 1) := mem_past.2 ⟨hu, Journey.self (by omega)⟩
  obtain ⟨z, x, hzx, hz, hx⟩ := Cslib.DynNet.exists_edge_cross
    (S := fun x => x ∈ G.past u t (s + 1)) (hG.conn (s + 1) (by omega) y hy u hu) hyp hu'
  apply hz
  rw [heq, mem_past]
  exact ⟨(hG.mem _ _ _ hzx).1, Journey.cons (Or.inr hzx) (mem_past.1 hx).2⟩

/-- **Flooding lemma**: `|past(u,t)(t-j)| ≥ min(n, j+1)`. -/
theorem min_card_le_card_past (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V) :
    ∀ j ≤ t, min G.V.card (j + 1) ≤ (G.past u t (t - j)).card := by
  intro j
  induction j with
  | zero =>
    intro _
    have : u ∈ G.past u t (t - 0) := mem_past.2 ⟨hu, Journey.self (by omega)⟩
    have := Finset.card_pos.2 ⟨u, this⟩
    omega
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have e : t - j = (t - (j + 1)) + 1 := by omega
    rw [e] at ih
    by_cases hV : G.past u t (t - (j + 1) + 1) = G.V
    · have := Finset.card_le_card (past_succ_subset (G := G) u t (t - (j + 1)))
      rw [hV] at this
      omega
    · have := Finset.card_lt_card (past_ssubset hG hu (by omega) hV)
      omega

/-- After `n - 1` rounds every node has heard from everyone: `past(u,t)(s) = V` for
`t ≥ s + n - 1`. -/
theorem past_eq_V (hG : G.Valid) {u t s : ℕ} (hu : u ∈ G.V) (h : s + G.V.card ≤ t + 1) :
    G.past u t s = G.V := by
  have hn := Finset.card_pos.2 hG.nonempty
  have := min_card_le_card_past hG hu (t := t) (t - s) (by omega)
  rw [show t - (t - s) = s by omega] at this
  exact Finset.eq_of_subset_of_card_le (past_subset _ _ _) (by omega)

/-- At time `n - s - 1` every node has heard all but at most `s` inputs (used in Lemma 6.2). -/
theorem card_sdiff_past_le (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V) :
    (G.V \ G.past u t 0).card ≤ G.V.card - (t + 1) := by
  have h1 := min_card_le_card_past hG hu t le_rfl
  rw [Nat.sub_self] at h1
  rw [Finset.card_sdiff_of_subset (past_subset _ _ _)]
  omega

/-! ### Indistinguishability (equal full-information views) -/

/-- The time-`0` view of node `u` is the same in `G` and `H`: `u` is a node of both, with the same
input, and the a-priori information is the same. -/
def InitIndist (G H : DGraph α) (u : ℕ) : Prop :=
  u ∈ G.V ∧ u ∈ H.V ∧ G.input u = H.input u ∧ G.N = H.N

/-- `Indist G H u t` : node `u` has the same view at time `t` in `G` and in `H`
(the paper's `(G, t) ∼_u (H, t)`): full-information indistinguishability with initial views
`InitIndist`, round `r` using the edges `adj r`. -/
abbrev Indist (G H : DGraph α) (u t : ℕ) : Prop :=
  Cslib.HeardOf.FIIndist (InitIndist G H) (fun k => G.adj (k + 1)) (fun k => H.adj (k + 1)) t u

namespace Indist

theorem zero_iff {u : ℕ} :
    Indist G H u 0 ↔ u ∈ G.V ∧ u ∈ H.V ∧ G.input u = H.input u ∧ G.N = H.N := Iff.rfl

theorem succ_iff {u t : ℕ} : Indist G H u (t + 1) ↔ Indist G H u t ∧
    (∀ w, G.adj (t + 1) w u ↔ H.adj (t + 1) w u) ∧ ∀ w, G.adj (t + 1) w u → Indist G H w t :=
  Iff.rfl

theorem mono {u t t' : ℕ} (h : Indist G H u t') (htt : t ≤ t') : Indist G H u t :=
  Cslib.HeardOf.FIIndist.mono h htt

theorem mem_left {u t : ℕ} (h : Indist G H u t) : u ∈ G.V := h.zero.1
theorem mem_right {u t : ℕ} (h : Indist G H u t) : u ∈ H.V := h.zero.2.1
theorem N_eq {u t : ℕ} (h : Indist G H u t) : G.N = H.N := h.zero.2.2.2

theorem refl (hG : G.Valid) {u : ℕ} (hu : u ∈ G.V) (t : ℕ) : Indist G G u t :=
  Cslib.HeardOf.FIIndist.refl_of (S := (G.V : Set ℕ)) (fun _ hu => ⟨hu, hu, rfl, rfl⟩)
    (fun _ _ _ _ hw => (hG.mem _ _ _ hw).1) t u hu

theorem symm {u t : ℕ} (h : Indist G H u t) : Indist H G u t :=
  Cslib.HeardOf.FIIndist.symm (fun _ h => ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩) h

theorem trans {K : DGraph α} {u t : ℕ} (h₁ : Indist G H u t) (h₂ : Indist H K u t) :
    Indist G K u t :=
  Cslib.HeardOf.FIIndist.trans
    (fun _ h₁ h₂ => ⟨h₁.1, h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩) h₁ h₂

/-- The view determines the causal past, and the views of all time-nodes in it. -/
theorem reach {u t v s : ℕ} (h : Indist G H u t) (hr : G.Reach v s u t) :
    H.Reach v s u t ∧ Indist G H v s :=
  Cslib.HeardOf.FIIndist.journey h hr

theorem reach_iff {u t v s : ℕ} (h : Indist G H u t) : G.Reach v s u t ↔ H.Reach v s u t :=
  ⟨fun hr => (h.reach hr).1, fun hr => (h.symm.reach hr).1⟩

theorem input_eq {u t v : ℕ} (h : Indist G H u t) (hr : G.Reach v 0 u t) :
    G.input v = H.input v :=
  (h.reach hr).2.zero.2.2.1

theorem adj_iff {u t w s : ℕ} (h : Indist G H u t) (hr : G.Reach w (s + 1) u t) (x : ℕ) :
    G.adj (s + 1) x w ↔ H.adj (s + 1) x w :=
  (h.reach hr).2.2.1 x

theorem past_eq {u t : ℕ} (h : Indist G H u t) (hG : G.Valid) (hH : H.Valid) (s : ℕ) :
    G.past u t s = H.past u t s := by
  ext v
  simp only [mem_past]
  constructor
  · rintro ⟨hv, hr⟩
    exact ⟨((h.reach_iff.1 hr).mem_iff hH).2 h.mem_right, h.reach_iff.1 hr⟩
  · rintro ⟨hv, hr⟩
    exact ⟨((h.reach_iff.2 hr).mem_iff hG).2 h.mem_left, h.reach_iff.2 hr⟩

end Indist

/-- **Locality**: if `H` agrees with `G` on everything `u` can have heard of by time `t` in `G`
(node membership and inputs of the time-0 nodes in the causal past, edges into the time-nodes
of the causal past, and `N`), then `u` cannot distinguish them. -/
theorem indist_of_agree (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V) (hN : G.N = H.N)
    (hV : ∀ w, G.Reach w 0 u t → w ∈ H.V ∧ G.input w = H.input w)
    (hE : ∀ w s, G.Reach w (s + 1) u t → ∀ x, G.adj (s + 1) x w ↔ H.adj (s + 1) x w) :
    Indist G H u t :=
  Cslib.HeardOf.FIIndist.of_agree
    (fun w hw => ⟨(Reach.mem_iff hG hw).2 hu, (hV w hw).1, (hV w hw).2, hN⟩) hE

end DGraph

/-! ### Protocols -/

/-- A deterministic protocol: initial state from UID, input and a-priori information; in round
`t + 1` every node broadcasts `send t (state)` and updates its state from the messages received
(indexed by sender; `none` = no message from that node). `out` is the irrevocable output. -/
structure Protocol (α σ M : Type*) where
  init : ℕ → α → ℕ → σ
  send : ℕ → σ → M
  trans : ℕ → σ → (ℕ → Option M) → σ
  out : σ → Option Bool

namespace Protocol

variable {σ M : Type*}

open Classical in
/-- The local state of node `u` at time `t` when the protocol runs on `G`. -/
noncomputable def state (P : Protocol α σ M) (G : DGraph α) : ℕ → ℕ → σ
  | u, 0 => P.init u (G.input u) G.N
  | u, t + 1 => P.trans t (P.state G u t)
      (fun w => if G.adj (t + 1) w u then some (P.send t (P.state G w t)) else none)

/-- The state of every protocol is a function of the full-information view. -/
theorem state_eq_of_indist (P : Protocol α σ M) {G H : DGraph α} {u t : ℕ}
    (h : DGraph.Indist G H u t) : P.state G u t = P.state H u t := by
  induction t generalizing u with
  | zero =>
    obtain ⟨-, -, h1, h2⟩ := h
    simp [state, h1, h2]
  | succ t ih =>
    obtain ⟨h0, hadj, hw⟩ := h
    simp only [state]
    rw [ih h0]
    congr 1
    funext w
    by_cases hg : G.adj (t + 1) w u
    · simp [hg, (hadj w).1 hg, ih (hw w hg)]
    · have hg' : ¬ H.adj (t + 1) w u := fun h => hg ((hadj w).2 h)
      simp [hg, hg']

end Protocol

/-! ### Decision rules, consensus and coordination -/

/-- A decision rule: `D G u t = some v` iff `u` has decided `v` at or before time `t`. -/
abbrev Decision (α : Type*) := DGraph α → ℕ → ℕ → Option Bool

/-- A decision rule is *local* if it depends only on the full-information view. Every protocol's
outputs are local (`Protocol.local_out`). -/
def Local (D : Decision α) : Prop :=
  ∀ G H u t, DGraph.Indist G H u t → D G u t = D H u t

theorem Protocol.local_out {σ M : Type*} (P : Protocol α σ M) :
    Local (fun G u t => P.out (P.state G u t)) :=
  fun _ _ _ _ h => by simp only [P.state_eq_of_indist h]

/-- Binary consensus (inputs and outputs in `Bool`) in the system `S` of admissible executions. -/
structure Consensus (S : DGraph Bool → Prop) (D : Decision Bool) : Prop where
  loc : Local D
  stable : ∀ G, S G → ∀ u ∈ G.V, ∀ t v, D G u t = some v → D G u (t + 1) = some v
  agreement : ∀ G, S G → ∀ u ∈ G.V, ∀ w ∈ G.V, ∀ t t' a b,
    D G u t = some a → D G w t' = some b → a = b
  validity : ∀ G, S G → ∀ u ∈ G.V, ∀ t v, D G u t = some v → ∃ w ∈ G.V, G.input w = v
  termination : ∀ G, S G → ∀ u ∈ G.V, ∃ t, (D G u t).isSome

/-- `Δ`-coordination (Definition 4): once some node has decided at time `t`, every node has
decided by time `t + Δ`. Simultaneous consensus is `0`-coordinated consensus. -/
def Coordinated (S : DGraph Bool → Prop) (Δ : ℕ) (D : Decision Bool) : Prop :=
  ∀ G, S G → ∀ u ∈ G.V, ∀ t, (D G u t).isSome → ∀ w ∈ G.V, (D G w (t + Δ)).isSome

theorem Consensus.stable_le {S : DGraph Bool → Prop} {D : Decision Bool} (hD : Consensus S D)
    {G : DGraph Bool} (hG : S G) {u : ℕ} (hu : u ∈ G.V) {t t' : ℕ} (htt : t ≤ t') {v : Bool}
    (h : D G u t = some v) : D G u t' = some v := by
  induction t' with
  | zero => obtain rfl : t = 0 := by omega
            exact h
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le htt with rfl | hlt
    · exact h
    · exact hD.stable G hG u hu t' v (ih (by omega))

/-! ### Systems, knowledge, similarity -/

/-- The system where the count `n` is known a priori (`N = n`). -/
def KnownN (n : ℕ) (G : DGraph α) : Prop := G.Valid ∧ G.V.card = n ∧ G.N = n

/-- The system where nothing is known about the count (the dummy `N = 0`). -/
def UnknownN (G : DGraph α) : Prop := G.Valid ∧ G.N = 0

/-- The system where `N` is an upper bound on the count. -/
def BoundN (G : DGraph α) : Prop := G.Valid ∧ G.V.card ≤ G.N

/-- The paper's knowledge operator in the system `S`: `(S, G, t) ⊨ K_u φ`. -/
def Knows (S : DGraph α → Prop) (G : DGraph α) (u t : ℕ) (φ : DGraph α → Prop) : Prop :=
  ∀ H, S H → DGraph.Indist G H u t → φ H

/-- An edge of the similarity graph at time `t` in system `S`. -/
def SimStep (S : DGraph α → Prop) (t : ℕ) (G H : DGraph α) : Prop :=
  S G ∧ S H ∧ ∃ u, DGraph.Indist G H u t

/-- `(G, t) ∼ (H, t)`: same connected component of the similarity graph. -/
def Sim (S : DGraph α → Prop) (t : ℕ) : DGraph α → DGraph α → Prop :=
  ReflTransGen (SimStep S t)

/-- Common knowledge (semantic definition of Section 2.1). -/
def CK (S : DGraph α → Prop) (G : DGraph α) (t : ℕ) (φ : DGraph α → Prop) : Prop :=
  ∀ H, Sim S t G H → φ H

theorem SimStep.symm {S : DGraph α → Prop} {t : ℕ} {G H : DGraph α} (h : SimStep S t G H) :
    SimStep S t H G :=
  ⟨h.2.1, h.1, h.2.2.imp fun _ hu => hu.symm⟩

theorem Sim.symm {S : DGraph α → Prop} {t : ℕ} {G H : DGraph α} (h : Sim S t G H) :
    Sim S t H G :=
  by
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hs ih => exact ReflTransGen.head hs.symm ih

theorem Sim.trans {S : DGraph α → Prop} {t : ℕ} {G H K : DGraph α} (h₁ : Sim S t G H)
    (h₂ : Sim S t H K) : Sim S t G K :=
  ReflTransGen.trans h₁ h₂

theorem Sim.single {S : DGraph α → Prop} {t : ℕ} {G H : DGraph α} (hG : S G) (hH : S H) {u : ℕ}
    (h : DGraph.Indist G H u t) : Sim S t G H :=
  ReflTransGen.single ⟨hG, hH, u, h⟩

theorem Sim.mono {S S' : DGraph α → Prop} (hS : ∀ G, S G → S' G) {t : ℕ} {G H : DGraph α}
    (h : Sim S t G H) : Sim S' t G H :=
  by
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hs ih => exact ih.tail ⟨hS _ hs.1, hS _ hs.2.1, hs.2.2⟩

/-! ### Knowledge and common knowledge as instances of `Podc.Knowledge.IndistSystem` -/

/-- The executions of a system `S` of valid dynamic graphs at time `t`, as an indistinguishability
system: node `u` cannot distinguish `G` from `H` iff it has the same view in both, or it is a node
of neither (a node outside `V` has the trivial view). -/
def indistSystem (S : DGraph α → Prop) (hS : ∀ G, S G → G.Valid) (t : ℕ) :
    Podc.Knowledge.IndistSystem ℕ {G // S G} where
  indist u G H := (u ∉ G.1.V ∧ u ∉ H.1.V) ∨ DGraph.Indist G.1 H.1 u t
  equiv u :=
    ⟨fun G => by
      by_cases hu : u ∈ G.1.V
      · exact Or.inr (DGraph.Indist.refl (hS _ G.2) hu t)
      · exact Or.inl ⟨hu, hu⟩,
    fun h => h.imp And.symm DGraph.Indist.symm,
    fun h₁ h₂ => by
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact Or.inl ⟨h₁.1, h₂.2⟩
      · exact absurd h₂.mem_left h₁.2
      · exact absurd h₁.mem_right h₂.1
      · exact Or.inr (h₁.trans h₂)⟩

/-- The nodes present in an execution, as a nonrigid set. -/
def nodes (S : DGraph α → Prop) (G : {G // S G}) : Set ℕ := (G.1.V : Set ℕ)

variable {S : DGraph α → Prop} {hS : ∀ G, S G → G.Valid} {t : ℕ}

/-- The paper's `K_u` is the knowledge modality of `indistSystem` (for nodes `u ∈ V`). -/
theorem knows_iff_K {G : DGraph α} (hG : S G) {u : ℕ} (hu : u ∈ G.V) {φ : DGraph α → Prop} :
    Knows S G u t φ ↔ (indistSystem S hS t).K u (fun H => φ H.1) ⟨G, hG⟩ := by
  constructor
  · rintro h ⟨H, hH⟩ (hi | hi)
    · exact absurd hu hi.1
    · exact h H hH hi
  · exact fun h H hH hi => h ⟨H, hH⟩ (Or.inr hi)

/-- An edge of the similarity graph is a step of the reachability relation of `indistSystem`
among the nodes present. -/
theorem simStep_iff_reach {G H : {G // S G}} :
    SimStep S t G.1 H.1 ↔ (indistSystem S hS t).Reach (nodes S) G H := by
  constructor
  · rintro ⟨-, -, u, hu⟩
    exact ⟨u, hu.mem_left, Or.inr hu⟩
  · rintro ⟨u, hu, hi | hi⟩
    · exact absurd hu hi.1
    · exact ⟨G.2, H.2, u, hi⟩

/-- **Common knowledge** (Section 2.1): the paper's `CK` is common knowledge among the nodes
present, in the sense of `Podc.Knowledge.IndistSystem.C`. -/
theorem CK_iff_C {G : DGraph α} (hG : S G) {φ : DGraph α → Prop} :
    CK S G t φ ↔ (indistSystem S hS t).C (nodes S) (fun H => φ H.1) ⟨G, hG⟩ := by
  rw [Podc.Knowledge.IndistSystem.C_iff_forall_reach]
  constructor
  · intro h H hr
    refine h H.1 ?_
    induction hr with
    | single hs => exact ReflTransGen.single (simStep_iff_reach.2 hs)
    | tail _ hs ih => exact ih.tail (simStep_iff_reach.2 hs)
  · intro h H hsim
    obtain ⟨u, hu⟩ := (hS G hG).nonempty
    have key : ∀ K, Sim S t G K → ∃ hK : S K,
        TransGen ((indistSystem S hS t).Reach (nodes S)) ⟨G, hG⟩ ⟨K, hK⟩ := by
      intro K hK
      induction hK with
      | refl => exact ⟨hG, .single ⟨u, hu, Or.inr (DGraph.Indist.refl (hS G hG) hu t)⟩⟩
      | tail _ hs ih =>
        obtain ⟨hK, hr⟩ := ih
        exact ⟨hs.2.1, hr.tail (simStep_iff_reach (G := ⟨_, hK⟩) (H := ⟨_, hs.2.1⟩) |>.1 hs)⟩
    obtain ⟨hH, hr⟩ := key H hsim
    exact h ⟨H, hH⟩ hr

/-- Walks of a given length in the similarity graph. -/
inductive Walk (S : DGraph α → Prop) (t : ℕ) : ℕ → DGraph α → DGraph α → Prop
  | nil (G : DGraph α) : Walk S t 0 G G
  | snoc {ℓ : ℕ} {G H K : DGraph α} : Walk S t ℓ G H → SimStep S t H K → Walk S t (ℓ + 1) G K

theorem Walk.append {S : DGraph α → Prop} {t ℓ₁ ℓ₂ : ℕ} {G H K : DGraph α}
    (h₁ : Walk S t ℓ₁ G H) (h₂ : Walk S t ℓ₂ H K) : Walk S t (ℓ₁ + ℓ₂) G K := by
  induction h₂ with
  | nil => exact h₁
  | snoc _ hs ih => exact .snoc (ih h₁) hs

theorem Walk.single {S : DGraph α → Prop} {t : ℕ} {G H : DGraph α} (h : SimStep S t G H) :
    Walk S t 1 G H :=
  .snoc (.nil G) h

theorem Walk.symm {S : DGraph α → Prop} {t ℓ : ℕ} {G H : DGraph α} (h : Walk S t ℓ G H) :
    Walk S t ℓ H G := by
  induction h with
  | nil => exact .nil _
  | snoc _ hs ih => simpa [Nat.add_comm] using (Walk.single hs.symm).append ih

theorem Walk.sim {S : DGraph α → Prop} {t ℓ : ℕ} {G H : DGraph α} (h : Walk S t ℓ G H) :
    Sim S t G H := by
  induction h with
  | nil => exact ReflTransGen.refl
  | snoc _ hs ih => exact ih.tail hs

theorem Sim.exists_walk {S : DGraph α → Prop} {t : ℕ} {G H : DGraph α} (h : Sim S t G H) :
    ∃ ℓ, Walk S t ℓ G H := by
  induction h with
  | refl => exact ⟨0, .nil _⟩
  | tail _ hs ih => obtain ⟨ℓ, hℓ⟩ := ih; exact ⟨ℓ + 1, .snoc hℓ hs⟩

end CoordCons
