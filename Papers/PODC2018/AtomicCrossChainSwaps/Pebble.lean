import Papers.PODC2018.AtomicCrossChainSwaps.Basic

/-!
# §4.4 pebble games, Theorem 4.12 (core) and Lemma 4.13

* The lazy pebble game by rounds (`Fired`): leaders fire in round `0`; a vertex fires in round
  `k + 1` if all its in-neighbours fired by round `k`. Firing = placing pebbles (contracts) on all
  leaving arcs. Lemma 4.1: everybody fires iff `L` is a feedback vertex set; Lemma 4.3: in a
  strongly connected digraph everybody fires by round `diam D - 1`.
* The eager game from `z` is reachability (`ReachIn`): Lemma 4.2/4.3.
* Theorem 4.12 (core, "waits-for" argument): if followers publish on a leaving arc only after all
  their entering arcs carry contracts, no arc on a cycle of followers ever gets a contract.
* Lemma 4.13 (single leader): with simple paths, `D(v, v̂) ≥ D(w, v̂) + 1` for every arc `(v, w)`
  leaving a follower `v`; with the paper's literal (lax) paths it fails.
-/

namespace AtomicSwap

variable {V : Type*}

/-- Lazy pebble game: `Fired D L k v` iff `v` has fired by round `k`. -/
def Fired (D : Digraph V) (L : Set V) : ℕ → V → Prop
  | 0, v => v ∈ L
  | k + 1, v => Fired D L k v ∨ ∀ u, D.Adj u v → Fired D L k u

/-- `ReachIn D k v w`: `w` is reachable from `v` by a walk of length at most `k`. -/
def ReachIn (D : Digraph V) : ℕ → V → V → Prop
  | 0, v, w => v = w
  | k + 1, v, w => v = w ∨ ∃ x, D.Adj v x ∧ ReachIn D k x w

/-! ### Generic facts on chains and acyclic relations -/

section Chains

variable {α : Type*} {R : α → α → Prop}

/-- In an `R`-chain, the head is `TransGen R`-related to every later element. -/
lemma transGen_of_isChain {a b : α} {l : List α} (h : (a :: l).IsChain R) (hb : b ∈ l) :
    Relation.TransGen R a b := by
  have h' : (a :: l).IsChain (Relation.TransGen R) := h.imp fun _ _ => Relation.TransGen.single
  exact (List.pairwise_cons.1 (List.isChain_iff_pairwise.1 h')).1 b hb

/-- A chain of an acyclic relation has no repeated vertices. -/
lemma nodup_of_isChain (hR : ∀ v, ¬ Relation.TransGen R v v) {l : List α} (h : l.IsChain R) :
    l.Nodup := by
  have h' := List.isChain_iff_pairwise.1 (h.imp fun _ _ => Relation.TransGen.single (r := R))
  exact h'.imp fun {a _} hab heq => by subst heq; exact hR a hab

end Chains

variable {D : Digraph V} {L : Set V}

/-- An `Adj`-chain all of whose vertices are followers is a `FollowerAdj`-chain. -/
lemma isChain_followerAdj {l : List V} (h : l.IsChain D.Adj) (hl : ∀ x ∈ l, x ∉ L) :
    l.IsChain (FollowerAdj D L) := by
  induction h with
  | nil => exact .nil
  | singleton a => exact .singleton a
  | cons_cons hab _ ih =>
    exact .cons_cons ⟨hab, hl _ (by simp), hl _ (by simp)⟩
      (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))

/-- Every vertex of a strongly connected digraph on `≥ 2` vertices has an in-neighbour. -/
lemma exists_adj_to [Nontrivial V] (hD : StronglyConnected D) (v : V) : ∃ u, D.Adj u v := by
  obtain ⟨w, hw⟩ := exists_ne v
  rcases Relation.ReflTransGen.cases_tail (hD w v) with h | ⟨b, -, hb⟩
  · exact absurd h.symm hw
  · exact ⟨b, hb⟩

/-- Every vertex of a strongly connected digraph on `≥ 2` vertices has an out-neighbour. -/
lemma exists_adj_from [Nontrivial V] (hD : StronglyConnected D) (v : V) : ∃ u, D.Adj v u := by
  obtain ⟨w, hw⟩ := exists_ne v
  rcases Relation.ReflTransGen.cases_head (hD v w) with h | ⟨b, hb, -⟩
  · exact absurd h.symm hw
  · exact ⟨b, hb⟩

/-! ### The lazy pebble game -/

lemma Fired.succ {k : ℕ} {v : V} (h : Fired D L k v) : Fired D L (k + 1) v := Or.inl h

/-- Fired vertices stay fired. -/
lemma Fired.mono {k k' : ℕ} {v : V} (hk : k ≤ k') (h : Fired D L k v) : Fired D L k' v := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- Leaders fire in round `0`. -/
lemma Fired.of_mem {k : ℕ} {v : V} (hv : v ∈ L) : Fired D L k v :=
  Fired.mono (Nat.zero_le k) hv

lemma not_mem_of_not_fired {k : ℕ} {v : V} (h : ¬ Fired D L k v) : v ∉ L :=
  fun hv => h (Fired.of_mem hv)

/-- If `v` has not fired by round `k`, there is a chain of `k + 1` followers ending at `v`. -/
lemma exists_chain_of_not_fired : ∀ {k : ℕ} {v : V}, ¬ Fired D L k v →
    ∃ c : List V, c.IsChain (FollowerAdj D L) ∧ (∀ x ∈ c, x ∉ L) ∧ c.getLast? = some v ∧
      c.length = k + 1
  | 0, v, h => ⟨[v], .singleton _, fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact h, rfl, rfl⟩
  | k + 1, v, h => by
    have h' : ¬ Fired D L k v ∧ ∃ u, D.Adj u v ∧ ¬ Fired D L k u := by
      simpa only [Fired, not_or, not_forall, exists_prop] using h
    obtain ⟨h1, u, huv, hu⟩ := h'
    obtain ⟨c, hc, hcL, hcl, hlen⟩ := exists_chain_of_not_fired hu
    refine ⟨c ++ [v], hc.append (.singleton v) ?_, ?_, by simp, by simp [hlen]⟩
    · simp only [hcl, Option.mem_def, Option.some.injEq, List.head?_cons, forall_eq']
      exact ⟨huv, not_mem_of_not_fired hu, not_mem_of_not_fired h1⟩
    · simpa [or_imp, forall_and] using ⟨hcL, not_mem_of_not_fired h1⟩

/-- **Lemma 4.1** (one direction) of [Herlihy, PODC 2018]: if `L` is a feedback vertex set, every
vertex fires in the lazy pebble game, by round `|V|`. -/
theorem fired_card [Fintype V] (h : IsFVS D L) (v : V) : Fired D L (Fintype.card V) v := by
  by_contra hv
  obtain ⟨c, hc, -, -, hlen⟩ := exists_chain_of_not_fired hv
  have := (nodup_of_isChain h hc).length_le_card
  omega

/-- A vertex on a cycle of followers never fires. -/
lemma not_fired_of_cycle : ∀ (k : ℕ) {x : V}, Relation.TransGen (FollowerAdj D L) x x →
    ¬ Fired D L k x
  | 0, x, hx, hf => by
    obtain ⟨y, hxy, -⟩ := Relation.TransGen.head'_iff.1 hx
    exact hxy.2.1 hf
  | k + 1, x, hx, hf => by
    rcases hf with hf | hf
    · exact not_fired_of_cycle k hx hf
    · obtain ⟨b, hxb, hbx⟩ := Relation.TransGen.tail'_iff.1 hx
      exact not_fired_of_cycle k (Relation.TransGen.head' hbx hxb) (hf b hbx.1)

/-- **Lemma 4.1** (other direction) of [Herlihy, PODC 2018]: if every vertex fires, `L` is a
feedback vertex set. -/
theorem isFVS_of_fired {k : ℕ} (h : ∀ v, Fired D L k v) : IsFVS D L :=
  fun v hv => not_fired_of_cycle k hv (h v)

/-- **Lemma 4.1** of [Herlihy, PODC 2018]: the lazy pebble game started at `L` terminates with
every vertex fired iff `L` is a feedback vertex set. -/
theorem exists_fired_iff [Fintype V] : (∃ k, ∀ v, Fired D L k v) ↔ IsFVS D L :=
  ⟨fun ⟨_, h⟩ => isFVS_of_fired h, fun h => ⟨_, fired_card h⟩⟩

/-- A follower chain in a strongly connected digraph with a feedback vertex set `L` extends, by a
leader in-neighbour before and a leader out-neighbour after, to a path two arcs longer. -/
lemma exists_path_of_chain [Fintype V] [Nontrivial V] (hD : StronglyConnected D)
    (hL : IsFVS D L) (c : List V) (hne : c ≠ []) (hc : c.IsChain (FollowerAdj D L))
    (hcL : ∀ x ∈ c, x ∉ L) : ∃ p, IsPath D p ∧ c.length + 2 ≤ p.length := by
  induction hm : Fintype.card V - c.length using Nat.strong_induction_on generalizing c with
  | _ m ih =>
  have hnd := nodup_of_isChain hL hc
  obtain ⟨u, hu⟩ := exists_adj_to hD (c.head hne)
  obtain ⟨x, hx⟩ := exists_adj_from hD (c.getLast hne)
  by_cases huL : u ∈ L
  swap
  · have hc' : (u :: c).IsChain (FollowerAdj D L) :=
      hc.cons_of_ne_nil hne ⟨hu, huL, hcL _ (List.head_mem hne)⟩
    have h' := (nodup_of_isChain hL hc').length_le_card
    obtain ⟨p, hp, hlen⟩ := ih _ (by simp at h' ⊢; omega) (u :: c) (by simp) hc'
      (by simpa [huL] using hcL) rfl
    exact ⟨p, hp, by simp at hlen; omega⟩
  by_cases hxL : x ∈ L
  swap
  · have hc' : (c ++ [x]).IsChain (FollowerAdj D L) := hc.append (.singleton x) (by
      simpa [List.getLast?_eq_some_getLast hne] using ⟨hx, hcL _ (List.getLast_mem hne), hxL⟩)
    have h' := (nodup_of_isChain hL hc').length_le_card
    obtain ⟨p, hp, hlen⟩ := ih _ (by simp at h' ⊢; omega) (c ++ [x]) (by simp) hc'
      (by simpa [or_imp, forall_and, hxL] using hcL) rfl
    exact ⟨p, hp, by simp at hlen; omega⟩
  have hA : c.IsChain D.Adj := hc.imp fun _ _ h => h.1
  refine ⟨(u :: c) ++ [x], ⟨by simp, ?_, ?_⟩, by simp⟩
  · refine (hA.cons_of_ne_nil hne hu).append (.singleton x) ?_
    intro y hy z hz
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hne] at hy
    simp only [Option.getD_some, Option.mem_def, Option.some.injEq, List.head?_cons] at hy hz
    subst hy hz
    exact hx
  · rw [List.dropLast_concat]
    exact List.nodup_cons.2 ⟨fun h => hcL u h huL, hnd⟩

/-- **Lemma 4.3** (lazy game) of [Herlihy, PODC 2018]: in a strongly connected digraph with
feedback vertex set `L`, every vertex fires by round `diam D - 1`. -/
theorem fired_diam [Fintype V] [Nontrivial V] (hD : StronglyConnected D) (hL : IsFVS D L)
    (v : V) : Fired D L (diam D - 1) v := by
  by_contra hv
  obtain ⟨c, hc, hcL, -, hlen⟩ := exists_chain_of_not_fired hv
  obtain ⟨p, hp, hplen⟩ :=
    exists_path_of_chain hD hL c (by rintro rfl; simp at hlen) hc hcL
  have := le_diam hp
  omega

/-! ### The eager pebble game (distances) -/

lemma ReachIn.refl {k : ℕ} {v : V} : ReachIn D k v v := by
  cases k with
  | zero => rfl
  | succ k => exact Or.inl rfl

lemma ReachIn.succ : ∀ {k : ℕ} {v w : V}, ReachIn D k v w → ReachIn D (k + 1) v w
  | 0, _, _, h => Or.inl h
  | k + 1, _, _, h => by
    rcases h with h | ⟨x, hx, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, h.succ⟩

/-- `ReachIn` is monotone in the bound. -/
lemma ReachIn.mono {k k' : ℕ} {v w : V} (hk : k ≤ k') (h : ReachIn D k v w) :
    ReachIn D k' v w := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

lemma ReachIn.reach : ∀ {k : ℕ} {v w : V}, ReachIn D k v w → Reach D v w
  | 0, _, _, h => h ▸ Relation.ReflTransGen.refl
  | k + 1, _, _, h => by
    rcases h with h | ⟨x, hx, h⟩
    · exact h ▸ Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hx h.reach

lemma Reach.exists_reachIn {v w : V} (h : Reach D v w) : ∃ k, ReachIn D k v w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, Or.inr ⟨_, hab, hk⟩⟩

/-- A walk realising the distance is a simple path. -/
lemma ReachIn.exists_nodup : ∀ {n : ℕ} {v w : V}, ReachIn D n v w →
    (∀ m < n, ¬ ReachIn D m v w) →
    ∃ p : List V, p.Nodup ∧ p.IsChain D.Adj ∧ p.head? = some v ∧ p.getLast? = some w ∧
      p.length = n + 1 ∧ ∀ x ∈ p, ReachIn D n x w
  | 0, v, w, h, _ => ⟨[v], by simp, .singleton _, rfl, by simp [show v = w from h], rfl,
      by simpa using h⟩
  | n + 1, v, w, h, hmin => by
    rcases h with h | ⟨x, hx, h⟩
    · exact absurd (h ▸ ReachIn.refl) (hmin 0 (Nat.succ_pos n))
    have hmin' : ∀ m < n, ¬ ReachIn D m x w := fun m hm hm' =>
      hmin (m + 1) (by omega) (Or.inr ⟨x, hx, hm'⟩)
    obtain ⟨p, hnd, hch, hh, hl, hlen, hall⟩ := ReachIn.exists_nodup h hmin'
    have hne : p ≠ [] := by rintro rfl; simp at hlen
    refine ⟨v :: p, List.nodup_cons.2 ⟨fun hv => hmin n (by omega) (hall v hv), hnd⟩,
      hch.cons (by simpa [hh] using hx), rfl, ?_, by simp [hlen], ?_⟩
    · rw [List.getLast?_cons, hl]; rfl
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨Or.inr ⟨x, hx, h⟩, fun y hy => (hall y hy).succ⟩

/-- Reachability is witnessed by a simple path (as a list without repetitions). -/
lemma Reach.exists_nodup {v w : V} (h : Reach D v w) :
    ∃ p : List V, p.Nodup ∧ p.IsChain D.Adj ∧ p.head? = some v ∧ p.getLast? = some w := by
  classical
  have hex := h.exists_reachIn
  obtain ⟨p, hnd, hch, hh, hl, -⟩ :=
    (Nat.find_spec hex).exists_nodup fun m hm => Nat.find_min hex hm
  exact ⟨p, hnd, hch, hh, hl⟩

/-- **Lemma 4.3** (eager game) of [Herlihy, PODC 2018]: in a strongly connected digraph every
vertex is at distance at most `diam D - 1` from every other. -/
theorem reachIn_diam [Fintype V] (hD : StronglyConnected D) (v w : V) :
    ReachIn D (diam D - 1) v w := by
  classical
  have hex := (hD v w).exists_reachIn
  have hn := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ ReachIn D m v w := fun m hm => Nat.find_min hex hm
  refine hn.mono ?_
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · omega
  obtain ⟨p, hnd, hch, -, hl, hlen, -⟩ := hn.exists_nodup hmin
  have hvw : v ≠ w := by rintro rfl; exact hmin 0 hpos ReachIn.refl
  obtain ⟨x, hwx, -⟩ := (Relation.ReflTransGen.cases_head (hD w v)).resolve_left (Ne.symm hvw)
  have hP : IsPath D (p ++ [x]) :=
    ⟨by simp, hch.append (.singleton x) (by simpa [hl] using hwx), by simpa using hnd⟩
  have := le_diam hP
  simp only [List.length_append, List.length_singleton] at this
  omega

/-! ### Theorem 4.12 (core): the waits-for argument -/

/-- **Theorem 4.12** (core) of [Herlihy, PODC 2018]. Let `c u w = some t` mean that the contract on
arc `(u, w)` is published at time `t`. If a follower publishes on a leaving arc only after all of
its entering arcs carry contracts published strictly earlier, then no arc on a cycle of followers
ever carries a contract. -/
theorem no_contract_on_follower_cycle (c : V → V → Option ℕ)
    (hc : ∀ u w t, u ∉ L → c u w = some t → ∀ x, D.Adj x u → ∃ t' < t, c x u = some t') :
    ∀ u w, FollowerAdj D L u w → Relation.TransGen (FollowerAdj D L) w u → c u w = none := by
  have key : ∀ t u w, FollowerAdj D L u w → Relation.TransGen (FollowerAdj D L) w u →
      c u w ≠ some t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
    intro u w huw hwu hcu
    obtain ⟨b, hwb, hbu⟩ := Relation.TransGen.tail'_iff.1 hwu
    obtain ⟨t', ht', hb⟩ := hc u w t huw.2.1 hcu b hbu.1
    exact ih t' ht' b u hbu (Relation.TransGen.head' huw hwb) hb
  intro u w huw hwu
  exact Option.eq_none_iff_forall_ne_some.2 fun t => key t u w huw hwu

end AtomicSwap
