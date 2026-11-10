import Papers.PODC2010.KShotRadioBroadcast.Model


-- CSLib candidate: chain lemma for radio lower bounds
/-!
# Networks that start with a chain

A network *starts with the chain* `c 0 = s, c 1, …, c (ℓ-1)` if consecutive chain nodes are linked
and every chain node except the last one transmits only to chain nodes (its successor or earlier
nodes). In such a network the message travels along the chain exactly along the greedy first
occurrence of the sequence `c 0, …, c (ℓ-1)` in the schedule (`chainTime`), and no node outside
the chain is informed before the last chain node first transmits (`chain_outside_none`), at which
step all its outside out-neighbours are informed (`chain_last_informs`).

The `k`-shot limit plays no role along a chain: each chain node forwards the message at its first
transmission.
-/

namespace Podc.KShotRadioBroadcast

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `chainTime σ c i`: the step at which the chain node `c i` receives the message, when the
message travels along the chain `c 0, c 1, …` (`c 0` is the source, informed at step `0`); it is
the step of the first occurrence of `c 0, …, c (i-1)`. `chainTime σ c ℓ` is the step at which
`c (ℓ-1)` first transmits. -/
noncomputable def chainTime (σ : Schedule V) (c : ℕ → V) : ℕ → Option ℕ
  | 0 => some 0
  | i + 1 => (chainTime σ c i).bind (nextApp σ (c i))

section chainTime

variable {σ : Schedule V} {c : ℕ → V}

theorem chainTime_succ (i : ℕ) :
    chainTime σ c (i + 1) = (chainTime σ c i).bind (nextApp σ (c i)) := rfl

theorem chainTime_succ_some {i a : ℕ} (h : chainTime σ c (i + 1) = some a) :
    ∃ b, chainTime σ c i = some b ∧ nextApp σ (c i) b = some a := by
  rw [chainTime_succ] at h
  cases h' : chainTime σ c i with
  | none => simp [h'] at h
  | some b => exact ⟨b, rfl, by simpa [h'] using h⟩

theorem chainTime_lt_of_lt {i j a : ℕ} (hij : j < i) (h : chainTime σ c i = some a) :
    ∃ b, chainTime σ c j = some b ∧ b < a := by
  induction i generalizing a with
  | zero => omega
  | succ i ih =>
    obtain ⟨b, hb, hn⟩ := chainTime_succ_some h
    have hba := (nextApp_spec hn).1
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hj | rfl
    · obtain ⟨b', hb', hlt⟩ := ih hj hb
      exact ⟨b', hb', hlt.trans hba⟩
    · exact ⟨b, hb, hba⟩

theorem chainTime_pos {i a : ℕ} (hi : 0 < i) (h : chainTime σ c i = some a) : 0 < a := by
  obtain ⟨b, -, hb⟩ := chainTime_lt_of_lt hi h
  omega

/-- Extending a chain by a list `R`: the new end time is the first occurrence of `R` after the old
end time. -/
theorem chainTime_add_length {ℓ : ℕ} (R : List V) (hc : ∀ j (hj : j < R.length), c (ℓ + j) = R[j]) :
    chainTime σ c (ℓ + R.length) = (chainTime σ c ℓ).bind (occ σ R) := by
  induction R generalizing ℓ with
  | nil => cases chainTime σ c ℓ <;> simp [occ]
  | cons v R ih =>
    have h1 : ℓ + (v :: R).length = (ℓ + 1) + R.length := by simp; omega
    rw [h1, ih (fun j hj => by
      have := hc (j + 1) (by simp; omega)
      rw [show ℓ + 1 + j = ℓ + (j + 1) by omega, this]; simp)]
    have hocc : occ σ (v :: R) = fun T => (nextApp σ v T).bind (occ σ R) :=
      funext fun T => occ_cons v R T
    have hv : c ℓ = v := by have := hc 0 (by simp); simpa using this
    rw [chainTime_succ, hocc, hv]
    cases chainTime σ c ℓ <;> simp

/-- `chainTime` only depends on the chain nodes before the index. -/
theorem chainTime_congr {c c' : ℕ → V} {ℓ : ℕ} (h : ∀ j < ℓ, c j = c' j) :
    chainTime σ c ℓ = chainTime σ c' ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [chainTime_succ, chainTime_succ, ih (fun j hj => h j (by omega)), h ℓ (by omega)]

end chainTime

/-- A network `E` *starts with the chain* `c 0, …, c (ℓ-1)` (with `c 0` the source): chain nodes
are distinct, consecutive chain nodes are linked, and every chain node but the last one transmits
only to chain nodes that are its successor or not later than itself. -/
structure StartsWithChain (E : V → V → Prop) (s : V) (c : ℕ → V) (ℓ : ℕ) : Prop where
  pos : 1 ≤ ℓ
  head : c 0 = s
  inj : ∀ i j, i < ℓ → j < ℓ → c i = c j → i = j
  link : ∀ i, i + 1 < ℓ → E (c i) (c (i + 1))
  out : ∀ i, i + 1 < ℓ → ∀ u, E (c i) u → u = c (i + 1) ∨ ∃ j ≤ i, u = c j

section chain

variable {σ : Schedule V} {k : ℕ} {E : V → V → Prop} {s : V} {c : ℕ → V} {ℓ : ℕ}

/-- The invariant of a chain execution before the last chain node transmits. -/
private def ChainInv (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (c : ℕ → V) (ℓ t : ℕ) :
    Prop :=
  (∀ i < ℓ, ∀ r, recvTime σ k E s t (c i) = some r ↔ chainTime σ c i = some r ∧ r ≤ t) ∧
  (∀ u, (∀ i < ℓ, c i ≠ u) → recvTime σ k E s t u = none)

/-- Under the invariant, transmitters are chain nodes. -/
private theorem transmits_chain (t : ℕ) (hJ : ChainInv σ k E s c ℓ t) {u : V}
    (hu : Transmits σ k E s t u) :
    ∃ j < ℓ, c j = u ∧ ∃ r, chainTime σ c j = some r ∧ r ≤ t ∧ TransmitsAt σ k r u (t + 1) := by
  obtain ⟨r, hr, htx⟩ := hu
  by_cases hin : ∃ i < ℓ, c i = u
  · obtain ⟨j, hj, rfl⟩ := hin
    exact ⟨j, hj, rfl, r, ((hJ.1 j hj r).1 hr).1, ((hJ.1 j hj r).1 hr).2, htx⟩
  · push Not at hin
    rw [hJ.2 u hin] at hr; cases hr

/-- A node informed at `r` whose next appearance after `r` is `a` transmits at `a`. -/
theorem transmitsAt_of_nextApp (hk : 1 ≤ k) {v : V} {r a : ℕ} (h : nextApp σ v r = some a) :
    TransmitsAt σ k r v a := by
  obtain ⟨h1, h2, h3⟩ := nextApp_spec h
  refine ⟨h1, h2, ?_⟩
  have : count σ v r a = 0 := by
    simp only [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_Ioo]
    exact fun t ht => h3 t ht.1 ht.2
  omega

private theorem chainInv_zero (hC : StartsWithChain E s c ℓ) : ChainInv σ k E s c ℓ 0 := by
  constructor
  · intro i hi r
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [hC.head, chainTime]; omega
    · have hne : c i ≠ s := by
        intro h
        have := hC.inj i 0 hi hC.pos (h.trans hC.head.symm)
        omega
      simp only [recvTime_zero, hne, ite_false, reduceCtorEq, false_iff, not_and]
      intro h; have := chainTime_pos hpos h; omega
  · intro u hu
    have : u ≠ s := fun h => hu 0 hC.pos (hC.head.trans h.symm)
    simp [this]

private theorem chainInv_succ (hk : 1 ≤ k) (hC : StartsWithChain E s c ℓ) {t : ℕ}
    (hJ : ChainInv σ k E s c ℓ t) (hbefore : ∀ T, chainTime σ c ℓ = some T → t + 1 < T) :
    ChainInv σ k E s c ℓ (t + 1) := by
  -- transmitters at step `t+1` are non-last chain nodes
  have htx : ∀ u, Transmits σ k E s t u →
      ∃ j, j + 1 < ℓ ∧ c j = u ∧ ∃ r, chainTime σ c j = some r ∧ r ≤ t ∧
        TransmitsAt σ k r u (t + 1) := by
    intro u hu
    obtain ⟨j, hj, rfl, r, hr, hrt, htr⟩ := transmits_chain t hJ hu
    refine ⟨j, ?_, rfl, r, hr, hrt, htr⟩
    by_contra hlast
    have hjl : j + 1 = ℓ := by omega
    obtain ⟨a, ha, hat⟩ := nextApp_isSome htr.1 htr.2.1
    have : chainTime σ c ℓ = some a := by rw [← hjl, chainTime_succ, hr]; simpa using ha
    have := hbefore a this
    omega
  constructor
  · intro i hi r
    cases h0 : recvTime σ k E s t (c i) with
    | some r0 =>
      rw [recvTime_succ_of_some h0]
      obtain ⟨hc0, hr0⟩ := (hJ.1 i hi r0).1 h0
      constructor
      · intro h; cases h; exact ⟨hc0, by omega⟩
      · rintro ⟨hc, -⟩; rw [hc0] at hc; exact hc
    | none =>
      have hun : ∀ r, chainTime σ c i = some r → t < r := by
        intro r hr; by_contra hle; push Not at hle
        rw [(hJ.1 i hi r).2 ⟨hr, hle⟩] at h0; cases h0
      rw [recvTime_succ_of_none h0]
      -- the only possible transmitting in-neighbour is `c (i-1)`
      have key : (∃! u, E u (c i) ∧ Transmits σ k E s t u) ↔ chainTime σ c i = some (t + 1) := by
        constructor
        · rintro ⟨u, ⟨hEu, hu⟩, -⟩
          obtain ⟨j, hj, rfl, r', hr', hr't, htr⟩ := htx u hu
          rcases hC.out j hj (c i) hEu with heq | ⟨j', hj', heq⟩
          · have hij := hC.inj i (j + 1) hi hj heq
            subst hij
            obtain ⟨a, ha, hat⟩ := nextApp_isSome htr.1 htr.2.1
            have hci : chainTime σ c (j + 1) = some a := by rw [chainTime_succ, hr']; simpa using ha
            have := hun a hci
            rw [hci]; congr 1; omega
          · have hij := hC.inj i j' hi (by omega) heq
            subst hij
            rcases Nat.lt_or_ge i j with hlt | hge
            · obtain ⟨b, hb, hbr⟩ := chainTime_lt_of_lt hlt hr'
              have := hun b hb; omega
            · have : i = j := by omega
              subst this; have := hun r' hr'; omega
        · intro hci
          have hi0 : 0 < i := by
            rcases Nat.eq_zero_or_pos i with rfl | h
            · simp [chainTime] at hci
            · exact h
          obtain ⟨b, hb, hn⟩ := chainTime_succ_some (i := i - 1) (by
            rw [Nat.sub_add_cancel hi0]; exact hci)
          have hbt : b ≤ t := by have := (nextApp_spec hn).1; omega
          refine ⟨c (i - 1), ⟨?_, ?_⟩, ?_⟩
          · have := hC.link (i - 1) (by omega); rwa [Nat.sub_add_cancel hi0] at this
          · exact ⟨b, (hJ.1 (i - 1) (by omega) b).2 ⟨hb, hbt⟩, transmitsAt_of_nextApp hk hn⟩
          · rintro u ⟨hEu, hu⟩
            obtain ⟨j, hj, rfl, r', hr', hr't, htr⟩ := htx u hu
            rcases hC.out j hj (c i) hEu with heq | ⟨j', hj', heq⟩
            · have := hC.inj i (j + 1) hi hj heq
              subst this; simp
            · have hij := hC.inj i j' hi (by omega) heq
              subst hij
              rcases Nat.lt_or_ge i j with hlt | hge
              · obtain ⟨b', hb', hbr⟩ := chainTime_lt_of_lt hlt hr'
                have := hun b' hb'; omega
              · have : i = j := by omega
                subst this; have := hun r' hr'; omega
      by_cases hc : ∃! u, E u (c i) ∧ Transmits σ k E s t u
      · simp only [hc, ↓reduceIte, key.1 hc]
        constructor
        · intro h; cases h; exact ⟨rfl, le_rfl⟩
        · rintro ⟨h, -⟩; cases h; rfl
      · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        intro hr hle
        rcases Nat.lt_or_ge r (t + 1) with hlt | hge
        · have := hun r hr; omega
        · have : r = t + 1 := by omega
          subst this; exact hc (key.2 hr)
  · intro u hu
    cases h0 : recvTime σ k E s t u with
    | some r => rw [hJ.2 u hu] at h0; cases h0
    | none =>
      rw [recvTime_succ_of_none h0]
      split_ifs with hcw
      swap; · rfl
      exfalso
      obtain ⟨w, ⟨hEw, hw⟩, -⟩ := hcw
      obtain ⟨j, hj, rfl, -⟩ := htx w hw
      rcases hC.out j hj u hEw with heq | ⟨j', hj', heq⟩
      · exact hu (j + 1) hj heq.symm
      · exact hu j' (by omega) heq.symm

private theorem chainInv_of_before (hk : 1 ≤ k) (hC : StartsWithChain E s c ℓ) :
    ∀ t, (∀ T, chainTime σ c ℓ = some T → t < T) → ChainInv σ k E s c ℓ t := by
  intro t
  induction t with
  | zero => intro _; exact chainInv_zero hC
  | succ t ih =>
    intro hb
    exact chainInv_succ hk hC (ih fun T hT => by have := hb T hT; omega) hb

/-- **Chain lemma (a).** In a network that starts with a chain, no node outside the chain is
informed before the last chain node first transmits (at step `chainTime σ c ℓ`, if ever). -/
theorem chain_outside_none (hk : 1 ≤ k) (hC : StartsWithChain E s c ℓ) {t : ℕ}
    (ht : ∀ T, chainTime σ c ℓ = some T → t < T) {u : V} (hu : ∀ i < ℓ, c i ≠ u) :
    recvTime σ k E s t u = none :=
  (chainInv_of_before hk hC t ht).2 u hu

/-- **Chain lemma (b).** In a network that starts with a chain, every node outside the chain to
which the last chain node transmits is informed exactly at the step `T = chainTime σ c ℓ` at which
the last chain node first transmits. -/
theorem chain_last_informs (hk : 1 ≤ k) (hC : StartsWithChain E s c ℓ) {T : ℕ}
    (hT : chainTime σ c ℓ = some T) {u : V} (hu : ∀ i < ℓ, c i ≠ u) (hE : E (c (ℓ - 1)) u) :
    recvTime σ k E s T u = some T := by
  have hl : ℓ - 1 + 1 = ℓ := Nat.sub_add_cancel hC.pos
  obtain ⟨b, hb, hn⟩ := chainTime_succ_some (i := ℓ - 1) (by rw [hl]; exact hT)
  have hbT := (nextApp_spec hn).1
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have hJ := chainInv_of_before hk hC t (fun T' hT' => by rw [hT] at hT'; cases hT'; omega)
  have h0 := hJ.2 u hu
  rw [recvTime_succ_of_none h0]
  split_ifs with hcon
  · rfl
  exfalso; apply hcon
  refine ⟨c (ℓ - 1), ⟨hE, b, (hJ.1 (ℓ - 1) (by omega) b).2 ⟨hb, by omega⟩,
    transmitsAt_of_nextApp hk hn⟩, ?_⟩
  rintro w ⟨hEw, hw⟩
  obtain ⟨j, hj, rfl, -⟩ := transmits_chain t hJ hw
  by_contra hne
  have hj' : j + 1 < ℓ := by
    by_contra h; exact hne (by congr 1; omega)
  rcases hC.out j hj' u hEw with heq | ⟨j', hj'', heq⟩
  · exact hu (j + 1) hj' heq.symm
  · exact hu j' (by omega) heq.symm

end chain

/-! ## Undirected networks that start with a chain -/

/-- The edges `c i — c (i+1)` of the chain `c 0, …, c (ℓ-1)`. -/
def ChainRel (c : ℕ → V) (ℓ : ℕ) (u v : V) : Prop :=
  ∃ i, i + 1 < ℓ ∧ u = c i ∧ v = c (i + 1)

/-- The undirected network consisting of the chain `c 0, …, c (ℓ-1)` and the extra edges `X`. -/
def chainGraph (c : ℕ → V) (ℓ : ℕ) (X : V → V → Prop) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => ChainRel c ℓ u v ∨ X u v)

section chainGraph

variable {c : ℕ → V} {ℓ : ℕ} {X : V → V → Prop} {s : V}

theorem chainGraph_adj {u v : V} :
    (chainGraph c ℓ X).Adj u v ↔
      u ≠ v ∧ ((ChainRel c ℓ u v ∨ X u v) ∨ (ChainRel c ℓ v u ∨ X v u)) := by
  simp [chainGraph, SimpleGraph.fromRel_adj]

theorem chainGraph_adj_of_X {u v : V} (hne : u ≠ v) (h : X u v) : (chainGraph c ℓ X).Adj u v :=
  chainGraph_adj.2 ⟨hne, Or.inl (Or.inr h)⟩

/-- If the extra edges avoid all chain nodes but the last, the chain graph starts with the
chain. -/
theorem startsWithChain_chainGraph (hpos : 1 ≤ ℓ) (hhead : c 0 = s)
    (hinj : ∀ i j, i < ℓ → j < ℓ → c i = c j → i = j)
    (hX : ∀ u v, X u v → ∀ i, i + 1 < ℓ → u ≠ c i ∧ v ≠ c i) :
    StartsWithChain (chainGraph c ℓ X).Adj s c ℓ where
  pos := hpos
  head := hhead
  inj := hinj
  link i hi := chainGraph_adj.2 ⟨fun h => by have := hinj i (i + 1) (by omega) hi h; omega,
    Or.inl (Or.inl ⟨i, hi, rfl, rfl⟩)⟩
  out i hi u hu := by
    obtain ⟨-, h⟩ := chainGraph_adj.1 hu
    rcases h with (⟨j, hj, h1, rfl⟩ | h) | (⟨j, hj, rfl, h2⟩ | h)
    · have := hinj i j (by omega) (by omega) h1; subst this; exact Or.inl rfl
    · exact absurd rfl (hX _ _ h i hi).1
    · have := hinj i (j + 1) (by omega) hj h2; subst this
      exact Or.inr ⟨j, by omega, rfl⟩
    · exact absurd rfl (hX _ _ h i hi).2

theorem reachable_chainGraph (hhead : c 0 = s)
    (hinj : ∀ i j, i < ℓ → j < ℓ → c i = c j → i = j) :
    ∀ i < ℓ, (chainGraph c ℓ X).Reachable s (c i) := by
  intro i
  induction i with
  | zero => intro _; rw [hhead]
  | succ i ih =>
    intro hi
    refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
    exact chainGraph_adj.2 ⟨fun h => by have := hinj i (i + 1) (by omega) hi h; omega,
      Or.inl (Or.inl ⟨i, hi, rfl, rfl⟩)⟩

theorem connected_of_reachable {G : SimpleGraph V} (s : V) (h : ∀ v, G.Reachable s v) :
    G.Connected :=
  { preconnected := fun u v => (h u).symm.trans (h v), nonempty := ⟨s⟩ }

end chainGraph

end Podc.KShotRadioBroadcast
