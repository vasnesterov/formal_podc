import Mathlib

-- CSLib candidate

/-!
# The synchronous KT0 clique with port numbers

Model of Section 2 / 3.1 of Kutten, Robinson, Tan, Zhu, *Improved Tradeoffs for Leader Election*
(PODC 2023).

* There are `n = m + 1` nodes. Every node has `m` ports `Fin m`. A node is identified with its ID
  (a natural number); the ID assignment is a finset `I : Finset ℕ` with `I.card = m + 1`.
* A **(partial) port map** `p : PortMap m` says that port `j` of node `u` leads to node `v` when
  `p u j = some v`. A port map for the ID assignment `I` (`IsPortMap p I`) is total on `I`,
  injective at every node and has no self-loops; since `I.card = m + 1`, port `j ↦ p u j` is then
  a bijection from `Fin m` onto `I \ {u}` (`IsPortMap.surj`). This is exactly the paper's
  port mapping (KT0: a node knows nothing about the IDs behind its ports).
* A deterministic synchronous algorithm (`Algorithm m`) has an initial state computed from the
  node's own ID, sends in every round at most one message per port (computed from the current
  state), and then updates its state from the vector of messages received on its ports (LOCAL:
  messages are unbounded). All nodes wake up simultaneously (round 0, 0-indexed).
* `run A p r u` is the state of node `u` after `r` rounds when the ports are wired by `p`.
  Messages sent by `v` in round `r` (0-indexed) are computed from `run A p r v`.
  The definition makes sense for *partial* port maps too: messages are only delivered along
  defined links. A partial port map `p` is *valid through round `r` on `S`* (`Valid A p r S`) if
  during rounds `< r` no node of `S` sends a message over an undefined port. Such partial
  executions are the paper's "execution prefixes with a partial port mapping" and "restricted
  execution prefixes" `Exec_r(X)` (Definition 3.4); `run_eq_of_extends` says that every port map
  compatible with `p` (the paper's "compatible" port mapping) produces the same execution prefix.
-/

open Classical Finset

namespace LeaderTradeoffs

/-- A deterministic algorithm for the synchronous clique with `m + 1` nodes (ports `Fin m`). -/
structure Algorithm (m : ℕ) where
  /-- Local states. -/
  State : Type
  /-- Messages (unbounded: LOCAL model). -/
  Msg : Type
  /-- Initial state, computed from the node's own ID (KT0). -/
  init : ℕ → State
  /-- The message (if any) sent on each port in the current round. -/
  send : State → Fin m → Option Msg
  /-- State update from the vector of received messages (indexed by the receiving port). -/
  step : State → (Fin m → Option Msg) → State
  /-- Output: `none` = undecided, `some true` = leader, `some false` = non-leader. -/
  output : State → Option Bool

/-- A partial port map: `p u j = some v` means that port `j` of node `u` leads to node `v`. -/
abbrev PortMap (m : ℕ) := ℕ → Fin m → Option ℕ

variable {m : ℕ}

/-- The port of `v` leading to `u`, if any. -/
noncomputable def backPort (p : PortMap m) (v u : ℕ) : Option (Fin m) :=
  if h : ∃ i, p v i = some u then some (Classical.choose h) else none

/-- The message received by `u` on port `j`, when the states before the round are `st`. -/
noncomputable def inbox (A : Algorithm m) (p : PortMap m) (st : ℕ → A.State) (u : ℕ)
    (j : Fin m) : Option A.Msg :=
  (p u j).bind fun v => (backPort p v u).bind fun i => A.send (st v) i

/-- `run A p r u`: the state of node `u` after `r` synchronous rounds. -/
noncomputable def run (A : Algorithm m) (p : PortMap m) : ℕ → ℕ → A.State
  | 0, u => A.init u
  | r + 1, u => A.step (run A p r u) (inbox A p (run A p r) u)

/-- Well-formedness of a partial port map on a node set `S`: links of `S` stay in `S`, no
self-loops, injective at every node, and links are bidirectional. -/
structure WF (p : PortMap m) (S : Finset ℕ) : Prop where
  mem : ∀ u ∈ S, ∀ j v, p u j = some v → v ∈ S
  ne : ∀ u ∈ S, ∀ j, p u j ≠ some u
  inj : ∀ u ∈ S, ∀ i j v, p u i = some v → p u j = some v → i = j
  symm : ∀ u ∈ S, ∀ j v, p u j = some v → ∃ i, p v i = some u

/-- A (total) port map for the ID assignment `I`. -/
def IsPortMap (p : PortMap m) (I : Finset ℕ) : Prop :=
  WF p I ∧ ∀ u ∈ I, ∀ j, (p u j).isSome

/-- `p` is valid through round `r` on `S`: in rounds `< r` no node of `S` sends a message
over a port that `p` leaves undefined. -/
def Valid (A : Algorithm m) (p : PortMap m) (r : ℕ) (S : Finset ℕ) : Prop :=
  ∀ r' < r, ∀ u ∈ S, ∀ j, p u j = none → A.send (run A p r' u) j = none

/-- Number of messages sent in state `s`. -/
noncomputable def sendCount (A : Algorithm m) (s : A.State) : ℕ :=
  (univ.filter fun j => (A.send s j).isSome).card

/-- Number of messages sent by the nodes of `S` in round `r`. -/
noncomputable def roundMsgs (A : Algorithm m) (p : PortMap m) (r : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ u ∈ S, sendCount A (run A p r u)

/-- Number of messages sent by the nodes of `S` in rounds `< T`. -/
noncomputable def msgs (A : Algorithm m) (p : PortMap m) (T : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ r ∈ range T, roundMsgs A p r S

/-- The nodes of `I` that output "leader" after `T` rounds. -/
noncomputable def leaders (A : Algorithm m) (p : PortMap m) (T : ℕ) (I : Finset ℕ) :
    Finset ℕ :=
  I.filter fun u => A.output (run A p T u) = some true

/-- `A` elects a leader by round `T` for every ID assignment from the ID universe `U` and every
port map: after `T` rounds exactly one node outputs "leader" (implicit leader election). This is
weaker than the paper's requirement (all nodes terminate with irrevocable outputs), so lower bounds
assuming only `ElectsBy` are stronger. -/
def ElectsBy (A : Algorithm m) (U : Finset ℕ) (T : ℕ) : Prop :=
  ∀ I ⊆ U, I.card = m + 1 → ∀ p : PortMap m, IsPortMap p I → (leaders A p T I).card = 1

/-- Termination by round `T` (used for upper bounds): in every execution, after `T` rounds every
node has an output, never changes it again and never sends another message. -/
def TerminatesBy (A : Algorithm m) (U : Finset ℕ) (T : ℕ) : Prop :=
  ∀ I ⊆ U, I.card = m + 1 → ∀ p : PortMap m, IsPortMap p I → ∀ u ∈ I,
    (A.output (run A p T u)).isSome ∧
      ∀ r ≥ T, A.output (run A p r u) = A.output (run A p T u) ∧ sendCount A (run A p r u) = 0

/-- Every execution with IDs from `U` sends at most `M` messages in rounds `< T`. -/
def MsgBound (A : Algorithm m) (U : Finset ℕ) (T : ℕ) (M : ℝ) : Prop :=
  ∀ I ⊆ U, I.card = m + 1 → ∀ p : PortMap m, IsPortMap p I → (msgs A p T I : ℝ) ≤ M

/-! ### Basic lemmas -/

theorem backPort_eq {p : PortMap m} {S : Finset ℕ} (hp : WF p S) {v u : ℕ} (hv : v ∈ S)
    {i : Fin m} (h : p v i = some u) : backPort p v u = some i := by
  have hex : ∃ i, p v i = some u := ⟨i, h⟩
  simp only [backPort, hex, dite_true]
  congr 1
  exact hp.inj v hv _ _ _ (Classical.choose_spec hex) h

theorem backPort_eq_none {p : PortMap m} {v u : ℕ} (h : ∀ i, p v i ≠ some u) :
    backPort p v u = none := by
  have hex : ¬ ∃ i, p v i = some u := fun ⟨i, hi⟩ => h i hi
  simp [backPort, hex]

/-- Locality: the execution of a set `X` that is closed under `p` only depends on `p` restricted
to `X`. -/
theorem run_congr {A : Algorithm m} {p q : PortMap m} {X : Finset ℕ}
    (hpq : ∀ u ∈ X, p u = q u) (hX : ∀ u ∈ X, ∀ j v, p u j = some v → v ∈ X) :
    ∀ r, ∀ u ∈ X, run A p r u = run A q r u := by
  intro r
  induction r with
  | zero => intro u _; rfl
  | succ r ih =>
    intro u hu
    simp only [run]
    rw [ih u hu]
    congr 1
    funext j
    simp only [inbox]
    rw [← hpq u hu]
    rcases hj : p u j with _ | v
    · rfl
    · have hv : v ∈ X := hX u hu j v hj
      simp only [Option.bind_some]
      have hb : backPort p v u = backPort q v u := by
        simp only [backPort, hpq v hv]
      rw [hb]
      rcases backPort q v u with _ | i
      · rfl
      · simp only [Option.bind_some]
        rw [ih v hv]

/-- An extension `p'` of a partial port map `p` that is valid through round `r` produces the same
execution prefix. -/
theorem run_eq_of_extends {A : Algorithm m} {p p' : PortMap m} {S : Finset ℕ} {r : ℕ}
    (hp : WF p S) (hp' : WF p' S) (hext : ∀ u ∈ S, ∀ j v, p u j = some v → p' u j = some v)
    (hv : Valid A p r S) : ∀ r' ≤ r, ∀ u ∈ S, run A p' r' u = run A p r' u := by
  intro r'
  induction r' with
  | zero => intro _ u _; rfl
  | succ r' ih =>
    intro hr u hu
    have ih' := ih (by omega)
    simp only [run]
    rw [ih' u hu]
    congr 1
    funext j
    simp only [inbox]
    rcases hj : p u j with _ | v
    · rcases hj' : p' u j with _ | v
      · rfl
      · -- a new link: nothing is sent over it
        have hvS : v ∈ S := hp'.mem u hu j v hj'
        obtain ⟨i, hi⟩ := hp'.symm u hu j v hj'
        simp only [Option.bind_some, Option.bind_none]
        rw [backPort_eq hp' hvS hi]
        simp only [Option.bind_some]
        have hpi : p v i = none := by
          rcases hpi : p v i with _ | w
          · rfl
          · exfalso
            have hw := hext v hvS i w hpi
            rw [hi] at hw
            cases hw
            obtain ⟨j', hj''⟩ := hp.symm v hvS i u hpi
            have := hext u hu j' v hj''
            have hjj := hp'.inj u hu _ _ _ this hj'
            subst hjj
            rw [hj] at hj''
            cases hj''
        rw [ih' v hvS]
        exact hv r' (by omega) v hvS i hpi
    · have hj' := hext u hu j v hj
      rw [hj']
      have hvS : v ∈ S := hp.mem u hu j v hj
      obtain ⟨i, hi⟩ := hp.symm u hu j v hj
      simp only [Option.bind_some]
      rw [backPort_eq hp hvS hi, backPort_eq hp' hvS (hext v hvS i u hi)]
      simp only [Option.bind_some]
      rw [ih' v hvS]

theorem valid_of_extends {A : Algorithm m} {p p' : PortMap m} {S : Finset ℕ} {r : ℕ}
    (hp : WF p S) (hp' : WF p' S) (hext : ∀ u ∈ S, ∀ j v, p u j = some v → p' u j = some v)
    (hv : Valid A p r S) : Valid A p' r S := by
  intro r' hr u hu j hj
  rw [run_eq_of_extends hp hp' hext hv r' hr.le u hu]
  apply hv r' hr u hu j
  rcases h : p u j with _ | v
  · rfl
  · rw [hext u hu j v h] at hj; cases hj

theorem valid_mono {A : Algorithm m} {p : PortMap m} {S : Finset ℕ} {r r' : ℕ}
    (hv : Valid A p r S) (h : r' ≤ r) : Valid A p r' S :=
  fun r'' hr'' => hv r'' (by omega)

theorem roundMsgs_congr {A : Algorithm m} {p q : PortMap m} {r : ℕ} {S : Finset ℕ}
    (h : ∀ u ∈ S, run A p r u = run A q r u) : roundMsgs A p r S = roundMsgs A q r S :=
  Finset.sum_congr rfl fun u hu => by rw [h u hu]

theorem msgs_congr {A : Algorithm m} {p q : PortMap m} {T : ℕ} {S : Finset ℕ}
    (h : ∀ r < T, ∀ u ∈ S, run A p r u = run A q r u) : msgs A p T S = msgs A q T S :=
  Finset.sum_congr rfl fun r hr => roundMsgs_congr (h r (Finset.mem_range.1 hr))

theorem msgs_union {A : Algorithm m} {p : PortMap m} {T : ℕ} {S S' : Finset ℕ}
    (h : Disjoint S S') : msgs A p T (S ∪ S') = msgs A p T S + msgs A p T S' := by
  simp only [msgs, roundMsgs, Finset.sum_union h, Finset.sum_add_distrib]

theorem roundMsgs_le_msgs {A : Algorithm m} {p : PortMap m} {T r : ℕ} {S : Finset ℕ}
    (hr : r < T) : roundMsgs A p r S ≤ msgs A p T S :=
  Finset.single_le_sum (f := fun r => roundMsgs A p r S) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hr)

theorem msgs_succ {A : Algorithm m} {p : PortMap m} {T : ℕ} {S : Finset ℕ} :
    msgs A p (T + 1) S = msgs A p T S + roundMsgs A p T S := by
  simp [msgs, Finset.sum_range_succ]

theorem msgs_mono {A : Algorithm m} {p : PortMap m} {T T' : ℕ} {S : Finset ℕ} (h : T ≤ T') :
    msgs A p T S ≤ msgs A p T' S :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

/-! ### Port maps on `m + 1` nodes are bijective -/

/-- The neighbours of `u` under `p`. -/
noncomputable def nbrs (p : PortMap m) (u : ℕ) : Finset ℕ :=
  (univ.filter fun j => (p u j).isSome).image fun j => (p u j).getD 0

/-- The undefined ports of `u`. -/
noncomputable def freePorts (p : PortMap m) (u : ℕ) : Finset (Fin m) :=
  univ.filter fun j => p u j = none

theorem mem_nbrs {p : PortMap m} {u v : ℕ} : v ∈ nbrs p u ↔ ∃ j, p u j = some v := by
  simp only [nbrs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j, ?_⟩
    rcases h : p u j with _ | w
    · rw [h] at hj; cases hj
    · rfl
  · rintro ⟨j, hj⟩
    exact ⟨j, by simp [hj], by simp [hj]⟩

theorem card_nbrs {p : PortMap m} {S : Finset ℕ} (hp : WF p S) {u : ℕ} (hu : u ∈ S) :
    (nbrs p u).card + (freePorts p u).card = m := by
  have h1 : (nbrs p u).card = (univ.filter fun j => (p u j).isSome).card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    rcases hpi : p u i with _ | v
    · rw [hpi] at hi; cases hi
    rcases hpj : p u j with _ | w
    · rw [hpj] at hj; cases hj
    simp only [hpi, hpj, Option.getD_some] at hij
    subst hij
    exact hp.inj u hu i j v hpi hpj
  rw [h1, freePorts]
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (fun j => (p u j).isSome)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  convert this using 3
  ext j
  simp

theorem nbrs_subset {p : PortMap m} {S : Finset ℕ} (hp : WF p S) {u : ℕ} (hu : u ∈ S) :
    nbrs p u ⊆ S.erase u := by
  intro v hv
  obtain ⟨j, hj⟩ := mem_nbrs.1 hv
  refine Finset.mem_erase.2 ⟨?_, hp.mem u hu j v hj⟩
  intro h
  rw [h] at hj
  exact hp.ne u hu j hj

theorem IsPortMap.surj {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I) (hI : I.card = m + 1)
    {u v : ℕ} (hu : u ∈ I) (hv : v ∈ I) (hne : v ≠ u) : ∃ j, p u j = some v := by
  have hfree : (freePorts p u).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro j hj
    simp only [freePorts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have := hp.2 u hu j
    rw [hj] at this; cases this
  have hc := card_nbrs hp.1 hu
  rw [hfree, add_zero] at hc
  have heq : nbrs p u = I.erase u := by
    apply Finset.eq_of_subset_of_card_le (nbrs_subset hp.1 hu)
    rw [Finset.card_erase_of_mem hu, hI, hc]; simp
  have : v ∈ nbrs p u := by rw [heq]; exact Finset.mem_erase.2 ⟨hne, hv⟩
  exact mem_nbrs.1 this

end LeaderTradeoffs
