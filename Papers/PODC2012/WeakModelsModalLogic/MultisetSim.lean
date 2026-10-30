import Papers.PODC2012.WeakModelsModalLogic.Model

/-!
# `VV = MV` and `VB = MB` (Theorems 8, 9 and Corollary 10 of Hella et al., §5.2)

Given a machine `A : Machine Δ Y` and a linear order on its messages, we construct a `Multiset`
machine `A.sim` simulating `A`:

* an intermediate state of `A.sim` (`SimState`) stores the current state `cur` of `A`, the list
  `past` of the earlier states of `A` at this node, and the multiset `hist` of the full histories
  of `A`-messages received so far on the in-ports (one list of length `t` per in-port);
* the message sent to port `j` is `some h`, where `h` is the history of all `A`-messages sent so
  far to port `j`, including the current one (stopped nodes send `none`);
* on receiving the multiset `R` of histories, the node extends the stored histories of the
  *stopped* neighbours by `m0` (they send `none` in `A.sim`, but `m0` in `A`; the paper does not
  discuss this case), sorts the resulting multiset of histories lexicographically and feeds the
  last entries to `δ` of `A`.

The execution of `A.sim` on `(G, p₀)` reproduces, up to time `T`, the execution of `A` on the
port numbering `p*` obtained from `p₀` by permuting the in-ports of every node so that they are
sorted by the message history up to time `T` (`PortNumbering.permIn`, `simPort`). The paper
constructs `p*` by a round-by-round refinement `P₀ ⊇ P₁ ⊇ ⋯`; we construct it in one step from
the execution of `A.sim` itself (which does not depend on `p*`), using that truncation of lists
is monotone for the lexicographic order (`take_le_take`).
-/

namespace Podc.WeakModelsModalLogic

open Function

/-! ### Auxiliary lemmas on lists and multisets -/

-- CSLib candidate
/-- Truncation is monotone for the lexicographic order on lists. -/
theorem take_le_take {α : Type*} [LinearOrder α] :
    ∀ (n : ℕ) {l l' : List α}, l ≤ l' → l.take n ≤ l'.take n
  | 0, _, _, _ => le_rfl
  | n + 1, l, l', h => by
    rcases h.lt_or_eq with hlt | rfl
    · change List.Lex (· < ·) l l' at hlt
      clear h
      cases hlt with
      | nil => exact le_of_lt (List.Lex.nil : List.Lex (· < ·) [] _)
      | cons hh => exact List.cons_le_cons _ (take_le_take n (le_of_lt hh))
      | rel hh => exact le_of_lt (List.Lex.rel hh)
    · exact le_rfl

/-- Dropping the `none` entries of a vector whose entries beyond `d` are `none`. -/
theorem filterMap_univ_castLE {α : Type*} {Δ d : ℕ} (h : d ≤ Δ) (f : Fin Δ → Option α)
    (hf : ∀ i : Fin Δ, d ≤ (i : ℕ) → f i = none) :
    (Finset.univ.val.map f).filterMap id =
      (Finset.univ.val.map (fun i : Fin d => f (Fin.castLE h i))).filterMap id := by
  classical
  have hsplit := Multiset.filter_add_not (fun i : Fin Δ => (i : ℕ) < d) Finset.univ.val
  have h0 : (Multiset.filter (fun i : Fin Δ => ¬ (i : ℕ) < d) Finset.univ.val).filterMap
      (id ∘ f) = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    rw [Multiset.mem_filterMap] at ha
    obtain ⟨i, hi, hfi⟩ := ha
    rw [Multiset.mem_filter] at hi
    simp [hf i (not_lt.1 hi.2)] at hfi
  have h1 : Multiset.filter (fun i : Fin Δ => (i : ℕ) < d) Finset.univ.val =
      Finset.univ.val.map (Fin.castLE h) := by
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ Finset.univ.nodup)
      (Finset.univ.nodup.map (Fin.castLE_injective h))).2 ?_
    intro i
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, Multiset.mem_map]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, -, rfl⟩; exact j.2
  rw [Multiset.filterMap_map, Multiset.filterMap_map, ← hsplit, Multiset.filterMap_add, h0,
    add_zero, h1, Multiset.filterMap_map]
  rfl

/-- The update of the stored histories. -/
theorem newHist_aux {ι M : Type*} [DecidableEq M] (m0 : M) (s : Multiset ι) (F : ι → Option (List M))
    (f : ι → List M) (c : ι → M)
    (hF : ∀ i, F i = some (f i ++ [c i]) ∨ (F i = none ∧ c i = m0)) :
    (s.filterMap F) + (s.map f - (s.filterMap F).map List.dropLast).map (· ++ [m0]) =
      s.map (fun i => f i ++ [c i]) := by
  classical
  let p : ι → Prop := fun i => (F i).isSome
  have hR : s.filterMap F = (s.filter p).map (fun i => f i ++ [c i]) := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rcases hF a with h | ⟨h, -⟩
      · rw [Multiset.filterMap_cons_some _ _ _ h, Multiset.filter_cons_of_pos _ (by simp [p, h]),
          Multiset.map_cons, ih]
      · rw [Multiset.filterMap_cons_none _ _ h, Multiset.filter_cons_of_neg _ (by simp [p, h]),
          ih]
  have hdrop : ((s.filter p).map (fun i => f i ++ [c i])).map List.dropLast =
      (s.filter p).map f := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => by simp
  have hrest : ((s.filter fun i => ¬ p i).map f).map (· ++ [m0]) =
      (s.filter fun i => ¬ p i).map (fun i => f i ++ [c i]) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i hi => ?_
    rw [Multiset.mem_filter] at hi
    rcases hF i with h | ⟨-, h⟩
    · exact absurd (by simp [p, h]) hi.2
    · simp [h]
  have hs : s.map f = (s.filter p).map f + (s.filter fun i => ¬ p i).map f := by
    rw [← Multiset.map_add, Multiset.filter_add_not]
  rw [hR, hdrop, hs, add_tsub_cancel_left, hrest, ← Multiset.map_add, Multiset.filter_add_not]

-- CSLib candidate
/-- A list with the same multiset as `H` which is sorted is `H.sort`. -/
theorem sort_map_univ {α : Type*} [LinearOrder α] {n : ℕ} (g : Fin n → α) (σ : Equiv.Perm (Fin n))
    (hσ : Monotone (g ∘ σ)) :
    (Finset.univ.val.map g).sort (· ≤ ·) = List.ofFn (g ∘ σ) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Multiset.pairwise_sort _ _)
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact hσ hij.le
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, ← Fin.univ_val_map, ← Multiset.map_map,
      Multiset.map_univ_val_equiv]

/-! ### Permuting in-ports -/

namespace PortNumbering

variable {V : Type*} {G : SimpleGraph V}

/-- The port numbering obtained from `P` by renumbering the in-ports of every node `v` by a
permutation `σ v`: in-port `i` of `v` in the new numbering is in-port `σ v i` in `P`.
Out-ports are unchanged. -/
def permIn (P : PortNumbering G) (σ : ∀ v, Equiv.Perm (Fin (deg G v))) : PortNumbering G where
  p := P.p.trans (Equiv.sigmaCongrRight fun v => (σ v).symm)
  adj x := by simpa using P.adj x
  cover u v h := by
    obtain ⟨x, hx, hy⟩ := P.cover u v h
    exact ⟨x, hx, by simpa using hy⟩

theorem permIn_symm (P : PortNumbering G) (σ : ∀ v, Equiv.Perm (Fin (deg G v))) (v : V)
    (i : Fin (deg G v)) : (P.permIn σ).p.symm ⟨v, i⟩ = P.p.symm ⟨v, σ v i⟩ := by
  simp [permIn]

end PortNumbering

/-! ### The simulating machine -/

namespace Machine

variable {Δ : ℕ} {Y : Type} (A : Machine Δ Y)

/-- Intermediate state of the simulating machine `A.sim`. -/
structure SimState where
  /-- The current state of `A`. -/
  cur : A.Z
  /-- The earlier states of `A` (oldest first). -/
  past : List A.Z
  /-- The multiset of the histories of `A`-messages received on the in-ports so far. -/
  hist : Multiset (List A.M)

variable [LinearOrder A.M]

/-- The vector fed to `δ` of `A`: the last messages of the histories, sorted
lexicographically (padded with `m0`). -/
noncomputable def simVec (H : Multiset (List A.M)) : Fin Δ → A.M := fun i =>
  ((H.sort (· ≤ ·)).getD i []).getLastD A.m0

/-- The new multiset of histories: received histories `R`, plus the stored histories of the
stopped neighbours (those not extended by `R`), extended by `m0`. -/
def simNewHist (H R : Multiset (List A.M)) : Multiset (List A.M) :=
  R + (H - R.map List.dropLast).map (· ++ [A.m0])

/-- The multiset of the `some` entries of a vector of received messages. -/
def received (w : Fin Δ → Option (List A.M)) : Multiset (List A.M) :=
  (Finset.univ.val.map w).filterMap id

/-- The transition of `A.sim`, as a function of the multiset `R` of received histories. -/
noncomputable def simδ (s : SimState A) (R : Multiset (List A.M)) : Y ⊕ SimState A :=
  (A.δ s.cur (A.simVec (A.simNewHist s.hist R))).map id
    fun z => ⟨z, s.past ++ [s.cur], A.simNewHist s.hist R⟩

/-- The `Multiset` machine simulating `A` (proof of Theorem 8). -/
noncomputable abbrev sim : Machine Δ Y where
  Z := SimState A
  M := Option (List A.M)
  m0 := none
  z0 d := (A.z0 d).map id fun z => ⟨z, [], Multiset.replicate d []⟩
  μ s j := some ((s.past ++ [s.cur]).map (A.μ · j))
  δ s w := A.simδ s (A.received w)

theorem sim_isMultiset : A.sim.IsMultiset := by
  intro s a b h
  exact congrArg (fun m : Multiset (Option (List A.M)) => A.simδ s (m.filterMap id)) h

theorem sim_isBroadcast (hA : A.IsBroadcast) : A.sim.IsBroadcast := by
  intro s i j hi hj
  change some _ = some _
  congr 1
  exact List.map_congr_left fun z _ => hA z i j hi hj

/-! ### The simulation -/

variable {V : Type*} (G : SimpleGraph V) (P : PortNumbering G)

/-- The state of `A` carried by `A.sim` at time `t`. -/
noncomputable def simOut (t : ℕ) (v : V) : Y ⊕ A.Z :=
  Sum.map id SimState.cur (A.sim.state G P t v)

/-- The history `[x₀, …, x_{n-1}]` of the messages sent by `w` to port `j` in the simulated
execution. -/
noncomputable def simHist (n : ℕ) (w : V) (j : ℕ) : List A.M :=
  (List.range n).map fun s => A.send (A.simOut G P s w) j

/-- The history of in-port `i` of `v` (w.r.t. the port numbering `P` of the simulation). -/
noncomputable def inHist (n : ℕ) (v : V) (i : Fin (deg G v)) : List A.M :=
  A.simHist G P n (P.p.symm ⟨v, i⟩).1 (P.p.symm ⟨v, i⟩).2

theorem simHist_succ (n : ℕ) (w : V) (j : ℕ) :
    A.simHist G P (n + 1) w j = A.simHist G P n w j ++ [A.send (A.simOut G P n w) j] := by
  simp [simHist, List.range_succ]

theorem simHist_take {n T : ℕ} (h : n ≤ T) (w : V) (j : ℕ) :
    (A.simHist G P T w j).take n = A.simHist G P n w j := by
  rw [simHist, simHist, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- The permutations of in-ports sorting them by the history up to time `T`. -/
noncomputable def simPerm (T : ℕ) (v : V) : Equiv.Perm (Fin (deg G v)) :=
  Tuple.sort (A.inHist G P T v)

/-- The port numbering `p*` whose execution `A.sim` reproduces up to time `T`. -/
noncomputable def simPort (T : ℕ) : PortNumbering G := P.permIn (A.simPerm G P T)

variable {G}

/-- The multiset of received histories, in terms of the in-ports of `v`. -/
theorem sim_recv_filterMap (hG : MaxDegLE G Δ) (x : V → Y ⊕ A.sim.Z) (v : V) :
    A.received (A.sim.recv G P x v) =
      (Finset.univ.val.map fun i : Fin (deg G v) =>
        A.sim.send (x (P.p.symm ⟨v, i⟩).1) (P.p.symm ⟨v, i⟩).2).filterMap id := by
  refine (filterMap_univ_castLE (hG v) (A.sim.recv G P x v) ?_).trans ?_
  · intro i hi
    simp [recv, not_lt.2 hi]
  · congr 2
    funext i
    simp [recv]

@[simp] theorem sim_send_inl (y : Y) (j : ℕ) : A.sim.send (.inl y) j = none := rfl

@[simp] theorem sim_send_inr (s : SimState A) (j : ℕ) :
    A.sim.send (.inr s) j = some ((s.past ++ [s.cur]).map (A.μ · j)) := rfl

theorem sim_update_inr (s : SimState A) (w : Fin Δ → Option (List A.M)) :
    A.sim.update (.inr s) w = A.simδ s (A.received w) := rfl

theorem proj_simδ (s : SimState A) (R : Multiset (List A.M)) :
    Sum.map id SimState.cur (A.simδ s R) = A.δ s.cur (A.simVec (A.simNewHist s.hist R)) := by
  unfold simδ
  cases A.δ s.cur (A.simVec (A.simNewHist s.hist R)) <;> rfl

/-- The stored histories are updated correctly, given that the senders' messages are their
histories. -/
theorem sim_newHist (hG : MaxDegLE G Δ) (t : ℕ)
    (hI : ∀ w (s : SimState A), A.sim.state G P t w = .inr s →
      ∀ j, (s.past ++ [s.cur]).map (A.μ · j) = A.simHist G P (t + 1) w j) (v : V) :
    A.simNewHist (Finset.univ.val.map (A.inHist G P t v))
        (A.received (A.sim.recv G P (A.sim.state G P t) v)) =
      Finset.univ.val.map (A.inHist G P (t + 1) v) := by
  rw [sim_recv_filterMap A P hG, simNewHist, Multiset.filterMap_map]
  have := newHist_aux A.m0 Finset.univ.val
    (id ∘ fun i : Fin (deg G v) => A.sim.send (A.sim.state G P t (P.p.symm ⟨v, i⟩).1)
      (P.p.symm ⟨v, i⟩).2) (A.inHist G P t v)
    (fun i => A.send (A.simOut G P t (P.p.symm ⟨v, i⟩).1) (P.p.symm ⟨v, i⟩).2) ?_
  · refine this.trans (Multiset.map_congr rfl fun i _ => ?_)
    simp only [inHist, simHist_succ]
  · intro i
    simp only [comp_apply, id_eq]
    rcases hx : A.sim.state G P t (P.p.symm ⟨v, i⟩).1 with y | s
    · right
      simp [simOut, hx]
      rfl
    · left
      rw [sim_send_inr, hI _ s hx, simHist_succ]
      rfl

/-- Invariant of the execution of `A.sim`: messages are the histories of sent messages, and
the stored multiset is the multiset of the histories of the in-ports. -/
theorem sim_inv (hG : MaxDegLE G Δ) (t : ℕ) :
    ∀ v (s : SimState A), A.sim.state G P t v = .inr s →
      (∀ j, (s.past ++ [s.cur]).map (A.μ · j) = A.simHist G P (t + 1) v j) ∧
      s.hist = Finset.univ.val.map (A.inHist G P t v) := by
  induction t with
  | zero =>
    intro v s hs
    have h0 : A.sim.state G P 0 v = (A.z0 (deg G v)).map id
        fun z => (⟨z, [], Multiset.replicate (deg G v) []⟩ : SimState A) := rfl
    rw [h0] at hs
    rcases hz : A.z0 (deg G v) with y | z
    · rw [hz] at hs; cases hs
    · rw [hz] at hs
      cases hs
      have ho : A.simOut G P 0 v = .inr z := by
        simp only [simOut, h0, hz]; rfl
      refine ⟨fun j => ?_, ?_⟩
      · simp [simHist, ho]
      · have : A.inHist G P 0 v = fun _ => [] := by funext i; simp [inHist, simHist]
        rw [this, Multiset.map_const', Finset.card_val, Finset.card_univ, Fintype.card_fin]
  | succ t ih =>
    intro v s' hs'
    rw [state_succ] at hs'
    change A.sim.update (A.sim.state G P t v) (A.sim.recv G P (A.sim.state G P t) v) = _ at hs'
    rcases hx : A.sim.state G P t v with y | s
    · rw [hx] at hs'; cases hs'
    · rw [hx, sim_update_inr] at hs'
      obtain ⟨h1, h2⟩ := ih v s hx
      have hH := A.sim_newHist P hG t (fun w s hs => (ih w s hs).1) v
      rw [← h2] at hH
      unfold simδ at hs'
      rcases hz : A.δ s.cur (A.simVec (A.simNewHist s.hist
        (A.received (A.sim.recv G P (A.sim.state G P t) v)))) with y | z
      · rw [hz] at hs'; cases hs'
      · rw [hz] at hs'
        cases hs'
        have ho : A.simOut G P (t + 1) v = .inr z := by
          simp only [simOut, state_succ]
          change Sum.map id SimState.cur
            (A.sim.update (A.sim.state G P t v) (A.sim.recv G P (A.sim.state G P t) v)) = _
          rw [hx, sim_update_inr, proj_simδ, hz]
        refine ⟨fun j => ?_, hH⟩
        rw [A.simHist_succ G P (t + 1) v j, ← h1, ho]
        simp

/-- The vector fed to `δ` of `A` by `A.sim` is the vector received in `(G, p*)`. -/
theorem sim_vec {T t : ℕ} (ht : t + 1 ≤ T) (v : V) :
    A.simVec (Finset.univ.val.map (A.inHist G P (t + 1) v)) =
      A.recv G (A.simPort G P T) (A.simOut G P t) v := by
  have hmono : Monotone (A.inHist G P (t + 1) v ∘ A.simPerm G P T v) := by
    intro i j hij
    have := Tuple.monotone_sort (A.inHist G P T v) hij
    simp only [comp_apply, inHist] at this ⊢
    rw [← simHist_take A G P ht, ← simHist_take A G P ht]
    exact take_le_take _ this
  unfold simVec
  rw [sort_map_univ _ _ hmono]
  funext i
  by_cases hi : (i : ℕ) < deg G v
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    simp only [comp_apply, inHist, simHist_succ, recv, hi, dite_true, simPort]
    rw [PortNumbering.permIn_symm]
    simp [simPerm]
  · rw [List.getD_eq_default _ _ (by simpa using hi), recv_eq_m0' A G _ _ hi]
    rfl
  where
    recv_eq_m0' {Δ' : ℕ} (B : Machine Δ' Y) (G : SimpleGraph V) (P : PortNumbering G) (x) {u}
        {i : Fin Δ'} (hi : ¬ (i : ℕ) < deg G u) : B.recv G P x u i = B.m0 := by
      simp [recv, hi]

/-- The simulation: up to time `T`, `A.sim` on `(G, p)` carries the states of `A` on
`(G, p*)`. -/
theorem sim_simulates (hG : MaxDegLE G Δ) (T : ℕ) :
    ∀ t ≤ T, A.state G (A.simPort G P T) t = A.simOut G P t := by
  intro t
  induction t with
  | zero =>
    intro _
    funext v
    simp only [state_zero, init, simOut]
    rw [Sum.map_map]
    cases A.z0 (deg G v) <;> rfl
  | succ t ih =>
    intro ht
    funext v
    rw [state_succ, ih (by omega)]
    simp only [step, simOut, state_succ]
    rcases hx : A.sim.state G P t v with y | s
    · rfl
    · rw [Sum.map_inr, update_inr, sim_update_inr, proj_simδ]
      obtain ⟨-, h2⟩ := A.sim_inv P hG t v s hx
      rw [h2, A.sim_newHist P hG t (fun w s hs => (A.sim_inv P hG t w s hs).1) v,
        A.sim_vec P ht v]

/-- If `A` stops in time `T` on `(G, p*)` with output `S`, then `A.sim` stops in time `T` on
`(G, p)` with output `S`. -/
theorem sim_stopsWith (hG : MaxDegLE G Δ) {T : ℕ} {S : V → Y}
    (h : A.StopsWith G (A.simPort G P T) T S) : A.sim.StopsWith G P T S := by
  intro u
  have := congrFun (A.sim_simulates P hG T T le_rfl) u
  rw [h u] at this
  unfold simOut at this
  rcases hB : A.sim.state G P T u with y | s
  · rw [hB] at this
    simpa using this.symm
  · rw [hB] at this
    simp at this

end Machine

/-! ### Theorems 8, 9 and Corollary 10 -/

variable {Y : Type}

/-- The simulating algorithm: `sim` applied to every `A Δ`, with an arbitrary (well-)order on
its messages. -/
noncomputable def Algorithm.sim (A : Algorithm Y) : Algorithm Y := fun Δ =>
  @Machine.sim Δ Y (A Δ) (IsWellOrder.linearOrder WellOrderingRel)

theorem Algorithm.sim_solvesIn {Pr : GraphProblem Y} {T : ℕ → ℕ → ℕ} {A : Algorithm Y}
    (hA : A.SolvesIn Pr T) : A.sim.SolvesIn Pr T := by
  intro Δ V _ G hG P
  let : LinearOrder (A Δ).M := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨S, hS, hSP⟩ := hA Δ V G hG ((A Δ).simPort G P (T Δ (Nat.card V)))
  exact ⟨S, (A Δ).sim_stopsWith P hG hS, hSP⟩

/-- Theorem 8 of [Hella et al.]: every problem solvable in time `T` by a `Vector` algorithm is
solvable in time `T` by a `Multiset` algorithm. -/
theorem theorem8 {Pr : GraphProblem Y} {T : ℕ → ℕ → ℕ} {A : Algorithm Y}
    (hA : A.SolvesIn Pr T) : ∃ B : Algorithm Y, (∀ Δ, (B Δ).IsMultiset) ∧ B.SolvesIn Pr T :=
  ⟨A.sim, fun Δ => @Machine.sim_isMultiset Δ Y (A Δ) (IsWellOrder.linearOrder WellOrderingRel),
    Algorithm.sim_solvesIn hA⟩

/-- Theorem 9 of [Hella et al.]: every problem solvable in time `T` by a `Broadcast` algorithm
is solvable in time `T` by a `Multiset ∩ Broadcast` algorithm. -/
theorem theorem9 {Pr : GraphProblem Y} {T : ℕ → ℕ → ℕ} {A : Algorithm Y}
    (hb : ∀ Δ, (A Δ).IsBroadcast) (hA : A.SolvesIn Pr T) :
    ∃ B : Algorithm Y, (∀ Δ, (B Δ).IsMultiset ∧ (B Δ).IsBroadcast) ∧ B.SolvesIn Pr T :=
  ⟨A.sim, fun Δ => ⟨@Machine.sim_isMultiset Δ Y (A Δ) (IsWellOrder.linearOrder WellOrderingRel),
    @Machine.sim_isBroadcast Δ Y (A Δ) (IsWellOrder.linearOrder WellOrderingRel) (hb Δ)⟩,
    Algorithm.sim_solvesIn hA⟩

variable (Y) in
/-- Corollary 10 of [Hella et al.]: `VB = MB`, `VB(1) = MB(1)`, `VV = MV`, `VV(1) = MV(1)`. -/
theorem cor10 : VB Y = MB Y ∧ VB1 Y = MB1 Y ∧ VV Y = MV Y ∧ VV1 Y = MV1 Y := by
  refine ⟨(Set.Subset.antisymm ?_ MB_subset_VB), (Set.Subset.antisymm ?_ MB1_subset_VB1),
    (Set.Subset.antisymm ?_ MV_subset_VV), (Set.Subset.antisymm ?_ MV1_subset_VV1)⟩
  · rintro Pr ⟨A, T, hb, hA⟩
    obtain ⟨B, hB, hBs⟩ := theorem9 hb hA
    exact ⟨B, T, hB, hBs⟩
  · rintro Pr ⟨A, T, hb, hA⟩
    obtain ⟨B, hB, hBs⟩ := theorem9 hb hA
    exact ⟨B, T, hB, hBs⟩
  · rintro Pr ⟨A, T, -, hA⟩
    obtain ⟨B, hB, hBs⟩ := theorem8 hA
    exact ⟨B, T, hB, hBs⟩
  · rintro Pr ⟨A, T, -, hA⟩
    obtain ⟨B, hB, hBs⟩ := theorem8 hA
    exact ⟨B, T, hB, hBs⟩

end Podc.WeakModelsModalLogic
