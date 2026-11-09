import Papers.PODC2015.AnonymousDynamicCounting.Multigraph
import Cslib.Computability.Distributed.DynamicNetworks.Journey

/-!
# Anonymous dynamic networks with a leader, `G(PD)₂`, Lemma 1, Theorem 2 and Corollary 1

Di Luna, Baldoni, *Investigating the Cost of Anonymity on Dynamic Networks* (PODC 2015 brief
announcement; full version arXiv:1505.03509v1), Sections 3 and 4.

**Model (Section 3).** Synchronous rounds; a finite set `V` of nodes with a leader; in round `r`
the adversary chooses an undirected graph `E r` on `V`. Each node broadcasts one message (unbounded
size) per round and receives the *multiset* of its neighbours' messages of that round (anonymous
broadcast, no labels, the degree is not known before receiving). Deterministic algorithms
(`NAlgo`): the leader starts in its own initial state, all other nodes in a common one.

**The networks of the reduction.** `chainNet k L M` turns `M ∈ M(DBL_k)` into a dynamic network:
a static path `c_0 – c_1 – ⋯ – c_L` whose end `c_L` is the leader, `k` relay nodes `V₁` (pairwise
adjacent, all adjacent to `c_0`) and the nodes `W` of `M`; in round `r`, relay `j` and `w ∈ W` are
adjacent iff `j ∈ L r w`. For `L = 0` this is the graph `G` of Lemma 1 (leader, `V₁`, `V₂ = W`;
`chainNet_mem_PD`); for `L ≥ 1` it is the network of Corollary 1 (a chain of length `L` before the
`G(PD)₂` part; dynamic diameter `L + 2`, `chainNet_diam`).

**Results.**
* `lemma_1`: every network algorithm is simulated round by round by an `M(DBL_k)` algorithm
  (`simAlgo`), so counting lower bounds for `M(DBL_k)` transfer to `G(PD)₂`.
* `leader_agree`: the leader of `chainNet k L M` cannot tell `M` from `M'` for `L + 1` more rounds
  than the views of `M` and `M'` agree.
* `theorem_2`: every counting algorithm for `G(PD)₂` needs more than `log₃(2|V| - 5) + 1` rounds on
  some `|V|`-node network; `theorem_2_log`: more than `log₃ |V|` rounds (`|V| ≥ 5`).
* `corollary_1`: for every `D ≥ 3`, on networks of dynamic diameter at most `D` counting needs at
  least `D + log₃(2|V| - 2D - 1)` rounds.
-/

namespace Podc.AnonymousDynamicCounting

open Classical

/-- A dynamic network with a leader: the graph of round `r` is `E r`. -/
structure DynNet where
  V : Type
  [fintype : Fintype V]
  E : ℕ → SimpleGraph V
  leader : V

attribute [instance] DynNet.fintype

/-- A deterministic algorithm for anonymous dynamic networks with anonymous broadcast. -/
structure NAlgo (S Msg : Type*) where
  leaderInit : S
  init : S
  send : S → Msg
  /-- New state from the old one and the multiset of messages received from the neighbours. -/
  step : S → Multiset Msg → S
  output : S → Option ℕ

variable {S Msg : Type*}

/-- The execution: the state of every node after `t` rounds. -/
noncomputable def NAlgo.run (A : NAlgo S Msg) (G : DynNet) : ℕ → G.V → S
  | 0 => fun v => if v = G.leader then A.leaderInit else A.init
  | t + 1 => fun v => A.step (A.run G t v)
      (∑ u, if (G.E t).Adj v u then {A.send (A.run G t u)} else 0)

theorem NAlgo.run_succ (A : NAlgo S Msg) (G : DynNet) (t : ℕ) (v : G.V) :
    A.run G (t + 1) v = A.step (A.run G t v)
      (∑ u, if (G.E t).Adj v u then {A.send (A.run G t u)} else 0) := rfl

/-- `A` counts on `G` by round `T` (Definition 2): the leader's first output is `|V|`, by round `T`. -/
def NAlgo.CountsBy (A : NAlgo S Msg) (G : DynNet) (T : ℕ) : Prop :=
  ∃ T' ≤ T, FirstOutput (fun s => A.output (A.run G s G.leader)) T' (Fintype.card G.V)

/-- `A` counts on every network of the class `𝓕` with `|V| = N` by round `f N`. -/
def NAlgo.CountsWithin (A : NAlgo S Msg) (𝓕 : DynNet → Prop) (f : ℕ → ℕ) : Prop :=
  ∀ G, 𝓕 G → A.CountsBy G (f (Fintype.card G.V))

/-- `G(PD)_h` (Definitions 3, 4): every round is connected and every node has the same distance
`≤ h` from the leader in all rounds. -/
def InPD (h : ℕ) (G : DynNet) : Prop :=
  (∀ r, (G.E r).Connected) ∧ ∀ v, ∃ d ≤ h, ∀ r, (G.E r).dist v G.leader = d

/-- The dynamic diameter is at most `D`: a flood started by any node at any round `r` has reached
every node at the end of round `r + D - 1` (a journey from `(x, r)` to `(y, r + D)`). With this
convention the network of Figure 1 has `D = 4`. -/
def DiamLE (D : ℕ) (G : DynNet) : Prop :=
  ∀ r x y, Cslib.DynNet.Journey (fun r => (G.E r).Adj) r x (r + D) y

/-! ### The networks `chainNet k L M` -/

section Chain

variable {k L : ℕ}

/-- Adjacency among the static nodes: the path `c_0 – ⋯ – c_L`, `c_0` joined to every relay, and
the relays pairwise joined. -/
def sAdj : (Fin (L + 1) ⊕ Fin k) → (Fin (L + 1) ⊕ Fin k) → Prop
  | .inl i, .inl i' => i.val + 1 = i'.val ∨ i'.val + 1 = i.val
  | .inl i, .inr _ => i.val = 0
  | .inr _, .inl i => i.val = 0
  | .inr j, .inr j' => j ≠ j'

theorem sAdj_symm {x y : Fin (L + 1) ⊕ Fin k} (h : sAdj x y) : sAdj y x := by
  rcases x with i | j <;> rcases y with i' | j' <;> simp_all [sAdj] <;> omega

theorem sAdj_irrefl (x : Fin (L + 1) ⊕ Fin k) : ¬ sAdj x x := by
  rcases x with i | j <;> simp [sAdj]

/-- Adjacency between a static node and `w ∈ W` in round `r`: relay `j` and `w` iff `j ∈ L r w`. -/
def fAdj (M : DBL k) (r : ℕ) : (Fin (L + 1) ⊕ Fin k) → M.W → Prop
  | .inl _, _ => False
  | .inr j, w => j ∈ M.L r w

/-- The adjacency of `chainNet` in round `r`. -/
def cAdj (M : DBL k) (r : ℕ) : ((Fin (L + 1) ⊕ Fin k) ⊕ M.W) → ((Fin (L + 1) ⊕ Fin k) ⊕ M.W) → Prop
  | .inl x, .inl y => sAdj x y
  | .inl x, .inr w => fAdj M r x w
  | .inr w, .inl x => fAdj M r x w
  | .inr _, .inr _ => False

variable (k L) in
/-- The dynamic network built from `M ∈ M(DBL_k)`: a static chain of `L + 1` nodes ending in the
leader, `k` relays, and the nodes of `W`. -/
abbrev chainNet (M : DBL k) : DynNet where
  V := (Fin (L + 1) ⊕ Fin k) ⊕ M.W
  E r :=
    { Adj := cAdj (L := L) M r
      symm := ⟨fun x y h => by
        rcases x with x | w <;> rcases y with y | w' <;> simp_all [cAdj, sAdj_symm]⟩
      loopless := ⟨fun x h => by
        rcases x with x | w
        · exact sAdj_irrefl x h
        · exact h⟩ }
  leader := .inl (.inl (Fin.last L))

theorem card_chainNet (M : DBL k) :
    Fintype.card (chainNet k L M).V = M.size + L + 1 + k := by
  rw [Fintype.card_eq_nat_card]
  show Nat.card ((_ ⊕ _) ⊕ _) = _
  rw [Nat.card_sum, Nat.card_sum, DBL.size, Fintype.card_eq_nat_card]
  simp; ring


/-! ### Received messages in `chainNet` -/


theorem recv_static (M : DBL k) (t : ℕ) (x : Fin (L + 1) ⊕ Fin k) (st : (chainNet k L M).V → Msg) :
    (∑ u : (chainNet k L M).V, if ((chainNet k L M).E t).Adj (.inl x) u then
        ({st u} : Multiset Msg) else 0) =
      (∑ y, if sAdj x y then ({st (.inl y)} : Multiset Msg) else 0) +
        ∑ w, if fAdj M t x w then ({st (.inr w)} : Multiset Msg) else 0 := by
  erw [Fintype.sum_sum_type]; rfl

theorem recv_far (M : DBL k) (t : ℕ) (w : M.W) (st : (chainNet k L M).V → Msg) :
    (∑ u : (chainNet k L M).V, if ((chainNet k L M).E t).Adj (.inr w) u then
        ({st u} : Multiset Msg) else 0) =
      ∑ j, if j ∈ M.L t w then ({st (.inl (.inr j))} : Multiset Msg) else 0 := by
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero (s := (Finset.univ : Finset M.W)), zero_add, add_zero]
  · exact Finset.sum_congr rfl fun j _ => by
      split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  · intro w' _; exact ite_eq_right id
  · intro i _; exact ite_eq_right id

theorem fAdj_inl (M : DBL k) (t : ℕ) (i : Fin (L + 1)) (w : M.W) : ¬ fAdj M t (.inl i) w := id

theorem fAdj_inr (M : DBL k) (t : ℕ) (j : Fin k) (w : M.W) :
    fAdj (L := L) M t (.inr j) w ↔ j ∈ M.L t w := Iff.rfl

/-- The relays' share of a filtered `view`-shaped multiset. -/
theorem filter_map_sum {β γ : Type*} (M : DBL k) (T : ℕ) (j : Fin k) (h : M.W → β) (g : β → γ) :
    (((∑ w, (M.L T w).val.map fun j' => (j', h w)).filter (·.1 = j)).map fun p => g p.2) =
      ∑ w, if j ∈ M.L T w then {g (h w)} else 0 := by
  let F : Multiset (Fin k × β) →+ Multiset (Fin k × β) :=
    { toFun := Multiset.filter (·.1 = j)
      map_zero' := Multiset.filter_zero _
      map_add' := Multiset.filter_add _ }
  have e : (∑ w, (M.L T w).val.map fun j' => (j', h w)).filter (·.1 = j) =
      ∑ w, ((M.L T w).val.map fun j' => (j', h w)).filter (·.1 = j) :=
    map_sum F _ _
  rw [e, Multiset.map_finsetSum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Multiset.filter_map, Multiset.map_map]
  have : Multiset.filter ((fun p : Fin k × β => p.1 = j) ∘ fun j' => (j', h w)) (M.L T w).val =
      ((M.L T w).filter (· = j)).val := by
    rw [Finset.filter_val]; rfl
  rw [this, Finset.filter_eq']
  split_ifs <;> simp

/-! ### The delay argument -/

variable (A : NAlgo S Msg)

/-- The state of `w ∈ W` when the relays' states are `rel` and `w`'s label sets are `Lw`. -/
def farSt (rel : ℕ → Fin k → S) (Lw : ℕ → Finset (Fin k)) : ℕ → S
  | 0 => A.init
  | T + 1 => A.step (farSt rel Lw T) (∑ j, if j ∈ Lw T then {A.send (rel T j)} else 0)

theorem farSt_congr {rel rel' : ℕ → Fin k → S} {Lw Lw' : ℕ → Finset (Fin k)} {T : ℕ}
    (hr : ∀ s < T, rel s = rel' s) (hL : ∀ s < T, Lw s = Lw' s) :
    farSt A rel Lw T = farSt A rel' Lw' T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    simp only [farSt]
    rw [ih (fun s hs => hr s (by omega)) (fun s hs => hL s (by omega)), hr T (by omega),
      hL T (by omega)]

theorem run_far (M : DBL k) (T : ℕ) (w : M.W) :
    A.run (chainNet k L M) T (.inr w) =
      farSt A (fun s j => A.run (chainNet k L M) s (.inl (.inr j))) (fun s => M.L s w) T := by
  induction T with
  | zero => simp [NAlgo.run, farSt, chainNet]
  | succ T ih => rw [NAlgo.run_succ, recv_far, ih]; rfl

theorem run_zero_inl (M : DBL k) (x : Fin (L + 1) ⊕ Fin k) :
    A.run (chainNet k L M) 0 (.inl x) = if x = .inl (Fin.last L) then A.leaderInit else A.init := by
  simp [NAlgo.run, chainNet]

/-- The relays' messages from `W` in round `T` are determined by the view `C(v_l, T)`. -/
theorem recv_relay_far (M : DBL k) (T : ℕ) (j : Fin k) (rel : ℕ → Fin k → S) :
    (∑ w, if fAdj (L := L) M T (.inr j) w then
        {A.send (farSt A rel (fun s => M.L s w) T)} else 0) =
      ((view M T).filter (·.1 = j)).map fun p => A.send (farSt A rel (Podc.AnonymousDynamicCounting.DAlgo.decode p.2) T) := by
  rw [view, filter_map_sum M T j (hist M · T)
    (fun h => A.send (farSt A rel (DAlgo.decode h) T))]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [fAdj_inr]
  rw [farSt_congr A (rel' := rel) (Lw' := DAlgo.decode (hist M w T)) (fun _ _ => rfl)
    fun s hs => (DAlgo.decode_hist M w hs).symm]

/-- **The delay argument.** If the views of `M` and `M'` agree in rounds `< t`, then in
`chainNet k L M` and `chainNet k L M'` the relays agree up to round `t` and the chain node `c_i`
up to round `t + i + 1`; in particular the leader `c_L` agrees up to round `t + L + 1`. -/
theorem static_agree (M M' : DBL k) {t : ℕ} (hv : ∀ i < t, view M i = view M' i) (T : ℕ) :
    (T ≤ t → ∀ j, A.run (chainNet k L M) T (.inl (.inr j)) =
        A.run (chainNet k L M') T (.inl (.inr j))) ∧
    (∀ i : Fin (L + 1), T ≤ t + i + 1 → A.run (chainNet k L M) T (.inl (.inl i)) =
        A.run (chainNet k L M') T (.inl (.inl i))) := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  cases T with
  | zero =>
    refine ⟨fun _ j => by rw [run_zero_inl, run_zero_inl], fun i _ => by rw [run_zero_inl, run_zero_inl]⟩
  | succ T =>
  have ihT := ih T (by omega)
  -- relays agree below `T + 1 ≤ t`
  have hrel : T + 1 ≤ t → ∀ s < T + 1, (fun j => A.run (chainNet k L M) s (.inl (.inr j))) =
      fun j => A.run (chainNet k L M') s (.inl (.inr j)) := fun ht s hs =>
    funext ((ih s hs).1 (by omega))
  refine ⟨fun ht j => ?_, fun i hi => ?_⟩
  · rw [NAlgo.run_succ, NAlgo.run_succ, recv_static, recv_static, ihT.1 (by omega) j]
    congr 2
    · refine Finset.sum_congr rfl fun y _ => ?_
      rcases y with i | j'
      · rw [ihT.2 i (by omega)]
      · rw [ihT.1 (by omega) j']
    · simp only [run_far]
      rw [recv_relay_far, recv_relay_far, hv T (by omega)]
      refine Multiset.map_congr rfl fun p _ => ?_
      rw [farSt_congr A (rel' := fun s j => A.run (chainNet k L M') s (.inl (.inr j)))
        (Lw' := DAlgo.decode p.2) (fun s hs => hrel ht s (by omega)) fun _ _ => rfl]
  · rw [NAlgo.run_succ, NAlgo.run_succ, recv_static, recv_static, ihT.2 i (by omega)]
    congr 2
    · refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : sAdj (Sum.inl i) y
      · rw [ite_eq_left hy, ite_eq_left hy]
        rcases y with i' | j'
        · simp only [sAdj] at hy
          rw [ihT.2 i' (by omega)]
        · simp only [sAdj] at hy
          rw [ihT.1 (by omega) j']
      · rw [ite_eq_right hy, ite_eq_right hy]
    · simp [fAdj]

/-- The leader of `chainNet k L M` cannot distinguish `M` from `M'` up to round `t + L + 1` if
their views agree in rounds `< t`. -/
theorem leader_agree (M M' : DBL k) {t : ℕ} (hv : ∀ i < t, view M i = view M' i) :
    ∀ T ≤ t + L + 1, A.run (chainNet k L M) T (chainNet k L M).leader =
      A.run (chainNet k L M') T (chainNet k L M').leader := fun T hT =>
  (static_agree A M M' hv T).2 (Fin.last L) (by simpa using hT)


/-! ### Lemma 1: simulation of a network algorithm in `M(DBL_k)` -/

/-- The multiset of messages of the `W`-nodes received by the static node `x`, recovered by the
`M(DBL_k)`-leader from the labelled messages it received. -/
def farRecv : (Fin (L + 1) ⊕ Fin k) → Multiset (Fin k × ((Fin k → Msg) ⊕ Msg)) → Msg →
    Multiset Msg
  | .inl _, _, _ => 0
  | .inr j, R, d => (R.filter (·.1 = j)).map fun p => p.2.elim (fun _ => d) id

variable (k L) in
/-- The `M(DBL_k)` algorithm of Lemma 1: the leader simulates the leader, the chain and the relays
of `chainNet k L M` (it knows the relay of each message from its label), every `w ∈ W` simulates
itself (it receives the relays' messages, each on the edge with the relay's label). -/
noncomputable def simAlgo (A : NAlgo S Msg) :
    DAlgo k ((Fin (L + 1) ⊕ Fin k → S) ⊕ S) ((Fin k → Msg) ⊕ Msg) where
  leaderInit := .inl fun x => if x = .inl (Fin.last L) then A.leaderInit else A.init
  init := .inr A.init
  send
    | .inl f => .inl fun j => A.send (f (.inr j))
    | .inr s => .inr (A.send s)
  step
    | .inl f, R => .inl fun x => A.step (f x)
        ((∑ y, if sAdj x y then {A.send (f y)} else 0) + farRecv x R (A.send A.init))
    | .inr s, R => .inr (A.step s (R.map fun p => p.2.elim (fun g => g p.1) fun _ => A.send A.init))
  output
    | .inl f => (A.output (f (.inl (Fin.last L)))).map (· - (L + 1 + k))
    | .inr _ => none

theorem Finset.val_map_eq_sum_ite {α β : Type*} [Fintype α] [DecidableEq α] (s : Finset α)
    (g : α → β) : s.val.map g = ∑ j, if j ∈ s then ({g j} : Multiset β) else 0 := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_eq_multiset_sum]
  rw [show (s.val.map fun j => ({g j} : Multiset β)) = (s.val.map g).map (fun x => {x}) by
    rw [Multiset.map_map]; rfl, Multiset.sum_map_singleton]

theorem simAlgo_run (M : DBL k) (t : ℕ) :
    ((simAlgo k L A).run M t).1 = .inl (fun x => A.run (chainNet k L M) t (.inl x)) ∧
      ∀ w, ((simAlgo k L A).run M t).2 w = .inr (A.run (chainNet k L M) t (.inr w)) := by
  induction t with
  | zero =>
    refine ⟨?_, fun w => ?_⟩
    · simp only [DAlgo.run, simAlgo]
      congr 1; funext x; rw [run_zero_inl]
    · simp [DAlgo.run, simAlgo, NAlgo.run, chainNet]
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, fun w => ?_⟩
    · simp only [DAlgo.run, h1, h2]
      simp only [simAlgo]
      congr 1; funext x
      rw [NAlgo.run_succ, recv_static]
      congr 2
      rcases x with i | j
      · simp [farRecv, fAdj]
      · simp only [farRecv]
        rw [filter_map_sum M t j (fun w => (Sum.inr (A.send (A.run (chainNet k L M) t (.inr w))) :
          (Fin k → Msg) ⊕ Msg)) (fun m => m.elim (fun _ => A.send A.init) id)]
        refine Finset.sum_congr rfl fun w _ => ?_
        split_ifs with h h' h' <;> first | rfl | exact absurd h h' | exact absurd h' h
    · simp only [DAlgo.run, h1, h2]
      simp only [simAlgo]
      congr 1
      rw [NAlgo.run_succ, recv_far, Multiset.map_map]
      congr 1
      rw [Finset.val_map_eq_sum_ite]
      rfl

/-- The outputs of `simAlgo` are those of the simulated leader, minus the `L + 1 + k` static
nodes. -/
theorem simAlgo_output (M : DBL k) (t : ℕ) :
    (simAlgo k L A).output ((simAlgo k L A).leader M t) =
      (A.output (A.run (chainNet k L M) t (chainNet k L M).leader)).map (· - (L + 1 + k)) := by
  rw [DAlgo.leader, (simAlgo_run A M t).1]
  rfl

/-- **Lemma 1.** Counting on the networks `chainNet k L M` (for `L = 0`: the `G(PD)₂` networks of
the paper's proof, `chainNet_mem_PD`) is at least as hard as counting on `M(DBL_k)`: if a network
algorithm counts on all of them by round `f |V|`, then `simAlgo` counts on `M(DBL_k)` by round
`f (|W| + L + 1 + k)` — the same round. -/
theorem lemma_1 {f : ℕ → ℕ}
    (hA : ∀ M : DBL k, A.CountsBy (chainNet k L M) (f (Fintype.card (chainNet k L M).V))) :
    (simAlgo k L A).CountsWithin fun n => f (n + L + 1 + k) := by
  intro M
  obtain ⟨T, hT, hfo⟩ := hA M
  rw [card_chainNet] at hT hfo
  refine ⟨T, hT, ?_, fun s hs => ?_⟩ <;> dsimp only
  · rw [simAlgo_output, show A.output _ = _ from hfo.1]; simp; omega
  · rw [simAlgo_output, show A.output _ = _ from hfo.2 s hs]; rfl

/-! ### `chainNet` is connected, in `G(PD)₂` for `L = 0`, and of dynamic diameter `L + 2` -/

theorem adj_chain_relay (M : DBL k) (r : ℕ) (j : Fin k) :
    ((chainNet k L M).E r).Adj (.inl (.inl 0)) (.inl (.inr j)) := rfl

theorem adj_relay_far (M : DBL k) (r : ℕ) {j : Fin k} {w : M.W} (h : j ∈ M.L r w) :
    ((chainNet k L M).E r).Adj (.inl (.inr j)) (.inr w) := h

theorem adj_relay_relay (M : DBL k) (r : ℕ) {j j' : Fin k} (h : j ≠ j') :
    ((chainNet k L M).E r).Adj (.inl (.inr j)) (.inl (.inr j')) := h

theorem adj_chain_succ (M : DBL k) (r : ℕ) (i : ℕ) (hi : i + 1 < L + 1) :
    ((chainNet k L M).E r).Adj (.inl (.inl ⟨i, by omega⟩)) (.inl (.inl ⟨i + 1, hi⟩)) :=
  Or.inl rfl

theorem reach_chain (M : DBL k) (r : ℕ) (i : Fin (L + 1)) :
    ((chainNet k L M).E r).Reachable (.inl (.inl 0)) (.inl (.inl i)) := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    exact (ih (by omega)).trans (adj_chain_succ M r i hi).reachable

theorem chainNet_connected (M : DBL k) (r : ℕ) : ((chainNet k L M).E r).Connected := by
  have h : ∀ v, ((chainNet k L M).E r).Reachable (.inl (.inl 0)) v := by
    rintro ((i | j) | w)
    · exact reach_chain M r i
    · exact (adj_chain_relay M r j).reachable
    · obtain ⟨j, hj⟩ := M.nonempty r w
      exact (adj_chain_relay M r j).reachable.trans (adj_relay_far M r hj).reachable
  exact (SimpleGraph.connected_iff _).2 ⟨fun u v => (h u).symm.trans (h v), ⟨.inl (.inl 0)⟩⟩

/-- For `L = 0`, `chainNet k 0 M` is the network `G` of the proof of Lemma 1 and lies in
`G(PD)₂`: the relays `V₁` are at distance 1 and the nodes of `W = V₂` at distance 2 from the
leader in every round. -/
theorem chainNet_mem_PD (M : DBL k) : InPD 2 (chainNet k 0 M) := by
  refine ⟨chainNet_connected M, ?_⟩
  have hl : (chainNet k 0 M).leader = .inl (.inl 0) := rfl
  rintro ((i | j) | w)
  · refine ⟨0, by omega, fun r => ?_⟩
    rw [hl, show i = 0 from Fin.ext (by omega)]; simp
  · refine ⟨1, by omega, fun r => ?_⟩
    rw [hl, SimpleGraph.dist_eq_one_iff_adj]
    exact (adj_chain_relay M r j).symm
  · refine ⟨2, le_rfl, fun r => ?_⟩
    rw [hl]
    obtain ⟨j, hj⟩ := M.nonempty r w
    have hw : ((chainNet k 0 M).E r).Adj (.inr w) (.inl (.inr j)) := (adj_relay_far M r hj).symm
    have hj0 : ((chainNet k 0 M).E r).Adj (.inl (.inr j)) (.inl (.inl 0)) :=
      (adj_chain_relay M r j).symm
    have hle : ((chainNet k 0 M).E r).dist (.inr w) (.inl (.inl 0)) ≤ 2 :=
      (SimpleGraph.dist_le ((SimpleGraph.Walk.nil.cons hj0).cons hw)).trans (by simp)
    have h0 : ((chainNet k 0 M).E r).dist (.inr w) (.inl (.inl 0)) ≠ 0 := by
      rw [Ne, ((chainNet_connected M r).preconnected _ _).dist_eq_zero_iff]
      simp
    have h1 : ((chainNet k 0 M).E r).dist (.inr w) (.inl (.inl 0)) ≠ 1 := by
      rw [Ne, SimpleGraph.dist_eq_one_iff_adj]
      exact id
    omega

open Cslib.DynNet in
theorem journey_chain (M : DBL k) (s : ℕ) (i i' : Fin (L + 1)) (n : ℕ)
    (hn : i.val ≤ i'.val + n ∧ i'.val ≤ i.val + n) :
    Journey (fun r => ((chainNet k L M).E r).Adj) s (.inl (.inl i)) (s + n) (.inl (.inl i')) := by
  induction n generalizing s i with
  | zero =>
    have : i = i' := Fin.ext (by omega)
    subst this; exact .refl
  | succ n ih =>
    by_cases h : i = i'
    · subst h; exact Journey.self (by omega)
    · have hlt : i.val < i'.val ∨ i'.val < i.val := by
        rcases Nat.lt_or_gt_of_ne (fun e => h (Fin.ext e)) with h | h <;> simp [h]
      rcases hlt with hlt | hlt
      · have := ih (s + 1) ⟨i.val + 1, by omega⟩ (by simp; omega)
        rw [show s + (n + 1) = s + 1 + n by ring]
        exact Journey.cons (Or.inr (adj_chain_succ M s i.val (by omega))) this
      · have := ih (s + 1) ⟨i.val - 1, by omega⟩ (by simp; omega)
        rw [show s + (n + 1) = s + 1 + n by ring]
        refine Journey.cons (Or.inr ?_) this
        have := adj_chain_succ M s (L := L) (i.val - 1) (by omega)
        have e : (⟨i.val - 1 + 1, by omega⟩ : Fin (L + 1)) = i := Fin.ext (by simp; omega)
        rw [e] at this
        exact this.symm


section Diam

open Cslib.DynNet

variable (M : DBL k)

theorem journey_static_relay (s : ℕ) (x : Fin (L + 1) ⊕ Fin k) (j : Fin k) :
    Journey (fun r => ((chainNet k L M).E r).Adj) s (.inl x) (s + L + 1) (.inl (.inr j)) := by
  rcases x with i | j'
  · have h1 := journey_chain M s i 0 i.val (by simp)
    have h2 := Journey.single (E := fun r => ((chainNet k L M).E r).Adj)
      (adj_chain_relay M (s + i.val) j)
    exact (h1.trans h2).mono_right (by omega)
  · by_cases h : j' = j
    · subst h; exact Journey.self (by omega)
    · exact (Journey.single (adj_relay_relay M s h)).mono_right (by omega)

theorem journey_relay_static (s : ℕ) (j : Fin k) (y : Fin (L + 1) ⊕ Fin k) :
    Journey (fun r => ((chainNet k L M).E r).Adj) s (.inl (.inr j)) (s + L + 1) (.inl y) := by
  rcases y with i | j'
  · have h1 := journey_chain M (s + 1) 0 i i.val (by simp)
    have h2 := Journey.single (E := fun r => ((chainNet k L M).E r).Adj)
      (adj_chain_relay M s j).symm
    exact (h2.trans h1).mono_right (by omega)
  · by_cases h : j = j'
    · subst h; exact Journey.self (by omega)
    · exact (Journey.single (adj_relay_relay M s h)).mono_right (by omega)

/-- The network of Corollary 1 (a chain of `L ≥ 1` nodes before the `G(PD)₂` part) has dynamic
diameter at most `L + 2`. (It is exactly `L + 2`: the leader is at distance `L + 2` from `W`.) -/
theorem chainNet_diam (hL : 1 ≤ L) : DiamLE (L + 2) (chainNet k L M) := by
  intro r x y
  rcases x with x | w <;> rcases y with y | w'
  · -- static to static
    refine Journey.mono_right ?_ (show r + L + 1 ≤ r + (L + 2) by omega)
    rcases x with i | j
    · rcases y with i' | j'
      · exact (journey_chain M r i i' (L + 1) (by omega)).mono_right (by omega)
      · exact journey_static_relay M r (.inl i) j'
    · exact journey_relay_static M r j y
  · -- static to `W`
    obtain ⟨j, hj⟩ := M.nonempty (r + L + 1) w'
    rw [show r + (L + 2) = r + L + 1 + 1 by ring]
    exact .step (journey_static_relay M r x j) (Or.inr (adj_relay_far M _ hj))
  · -- `W` to static
    obtain ⟨j, hj⟩ := M.nonempty r w
    rw [show r + (L + 2) = r + 1 + L + 1 by ring]
    exact Journey.cons (Or.inr (adj_relay_far M r hj).symm) (journey_relay_static M (r + 1) j y)
  · -- `W` to `W`
    obtain ⟨j, hj⟩ := M.nonempty r w
    obtain ⟨j', hj'⟩ := M.nonempty (r + L + 1) w'
    have hjj : Journey (fun r => ((chainNet k L M).E r).Adj) (r + 1) (.inl (.inr j)) (r + L + 1)
        (.inl (.inr j')) := by
      by_cases h : j = j'
      · subst h; exact Journey.self (by omega)
      · exact (Journey.single (adj_relay_relay M (r + 1) h)).mono_right (by omega)
    rw [show r + (L + 2) = r + L + 1 + 1 by ring]
    exact Journey.cons (Or.inr (adj_relay_far M r hj).symm) (.step hjj (Or.inr (adj_relay_far M _ hj')))

end Diam

end Chain

/-! ### Theorem 2 and Corollary 1 -/

/-- The common lower bound: if a network algorithm counts on all networks `chainNet 2 L M` by round
`f |V|`, then `f (n + L + 3) > t + L + 1` whenever `3^t ≤ 2n + 1`. -/
theorem chain_lower_bound (A : NAlgo S Msg) (L : ℕ) {f : ℕ → ℕ}
    (hA : ∀ M : DBL 2, A.CountsBy (chainNet 2 L M) (f (Fintype.card (chainNet 2 L M).V)))
    {n t : ℕ} (ht : 3 ^ t ≤ 2 * n + 1) : t + L + 1 < f (n + L + 3) := by
  obtain ⟨M, M', hM, hM', -, -, hv, -⟩ := lemma_5 (S := S) (Msg := Msg) le_rfl ht
  rw [leaderView_eq_iff] at hv
  by_contra hlt
  obtain ⟨T, hT, hfo⟩ := hA M
  obtain ⟨T', -, hfo'⟩ := hA M'
  rw [card_chainNet, hM] at hT hfo
  rw [card_chainNet, hM'] at hfo'
  rw [show n + L + 1 + 2 = n + L + 3 by ring] at hT
  have hT' : T ≤ t + L + 1 := by omega
  have := hfo.of_agree (o' := fun s => A.output (A.run (chainNet 2 L M') s (chainNet 2 L M').leader))
    fun s hs => by simp only [leader_agree A M M' hv s (hs.trans hT')]
  have := (this.unique hfo').2
  omega

/-- **Theorem 2.** Every algorithm that counts on all networks of `G(PD)₂` (by round `f |V|` on
`|V|`-node networks) needs `f N ≥ ⌊log₃(2N - 5)⌋ + 2` for every `N ≥ 3`; so counting on `G(PD)₂`
takes `Ω(log |V|)` rounds. -/
theorem theorem_2 (A : NAlgo S Msg) {f : ℕ → ℕ} (hA : A.CountsWithin (InPD 2) f) {N : ℕ}
    (hN : 3 ≤ N) : Nat.log 3 (2 * N - 5) + 2 ≤ f N := by
  have h := chain_lower_bound A 0 (fun M => hA _ (chainNet_mem_PD M))
    (n := N - 3) (Nat.pow_log_le_self 3 (x := 2 * (N - 3) + 1) (by omega))
  rw [show N - 3 + 0 + 3 = N by omega, show 2 * (N - 3) + 1 = 2 * N - 5 by omega] at h
  omega

/-- Theorem 2, simplified: counting on `|V|`-node networks of `G(PD)₂` takes more than
`log₃ |V| + 1` rounds (`|V| ≥ 5`). -/
theorem theorem_2_log (A : NAlgo S Msg) {f : ℕ → ℕ} (hA : A.CountsWithin (InPD 2) f) {N : ℕ}
    (hN : 5 ≤ N) : Nat.log 3 N + 2 ≤ f N :=
  (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 2).trans (theorem_2 A hA (by omega))

/-- **Corollary 1.** For every `D ≥ 3`: every algorithm that counts on all (1-interval connected)
networks of dynamic diameter at most `D` needs `f N ≥ D + ⌊log₃(2(N - D - 1) + 1)⌋` rounds on
`N`-node networks (`N ≥ D + 1`), i.e. `D + Ω(log |V|)`. -/
theorem corollary_1 (A : NAlgo S Msg) {D : ℕ} (hD : 3 ≤ D) {f : ℕ → ℕ}
    (hA : A.CountsWithin (fun G => (∀ r, (G.E r).Connected) ∧ DiamLE D G) f) {N : ℕ}
    (hN : D + 1 ≤ N) : D + Nat.log 3 (2 * (N - D - 1) + 1) ≤ f N := by
  have h := chain_lower_bound A (D - 2)
    (fun M => hA _ ⟨chainNet_connected M, by
      have := chainNet_diam (L := D - 2) M (by omega)
      rwa [show D - 2 + 2 = D by omega] at this⟩)
    (n := N - D - 1) (Nat.pow_log_le_self 3 (x := 2 * (N - D - 1) + 1) (by omega))
  rw [show N - D - 1 + (D - 2) + 3 = N by omega] at h
  omega

/-- Corollary 1, simplified: `D + ⌊log₃ |V|⌋` rounds for `|V| ≥ 2D + 1`. -/
theorem corollary_1_log (A : NAlgo S Msg) {D : ℕ} (hD : 3 ≤ D) {f : ℕ → ℕ}
    (hA : A.CountsWithin (fun G => (∀ r, (G.E r).Connected) ∧ DiamLE D G) f) {N : ℕ}
    (hN : 2 * D + 1 ≤ N) : D + Nat.log 3 N ≤ f N :=
  (Nat.add_le_add_left (Nat.log_mono_right (by omega)) D).trans (corollary_1 A hD hA (by omega))

/-- Theorem 2 by the paper's route: Lemma 1 (`simAlgo`) and Theorem 1. This gives one round less
than `theorem_2`, because the leader of the `G(PD)₂` network hears from `V₂` only through `V₁`. -/
theorem theorem_2_via_lemma_1 (A : NAlgo S Msg) {f : ℕ → ℕ} (hA : A.CountsWithin (InPD 2) f)
    (n : ℕ) : Nat.log 3 (2 * n + 1) < f (n + 0 + 1 + 2) :=
  theorem_1_log le_rfl (simAlgo 2 0 A) (lemma_1 A fun M => hA _ (chainNet_mem_PD M)) n

end Podc.AnonymousDynamicCounting
