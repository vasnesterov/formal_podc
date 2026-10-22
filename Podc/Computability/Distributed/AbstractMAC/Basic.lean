import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/AbstractMAC/Basic.lean

/-!
# The abstract MAC layer model

An event-based model of the *abstract MAC layer* (Kuhn, Lynch, Newport, DISC 2009): nodes of a
graph `G` communicate by *acknowledged local broadcast*.

* A node broadcasts one message at a time (`Node.cur`). The message is delivered to every
  neighbour, one `Event.recv` at a time, in an order chosen by the scheduler; when every neighbour
  has received it, the scheduler may deliver the acknowledgment (`Event.ack`). Messages that a node
  would broadcast while another broadcast is pending are discarded: the algorithm's `bcast` is only
  consulted when the node is idle (initially, after an ack, or after a receive while idle).
* Deterministic algorithms (`Algorithm`): initial state from an identity and a binary input,
  transitions on receive and on ack, an optional message to broadcast, an irrevocable decision
  (the first `some` value of `out` is recorded in `Node.dec`).
* Crash failures (`Event.crash`): a crashed node takes no further steps and its message is no
  longer delivered. Deliveries *to* a crashed node are kept as bookkeeping events that do not change
  its state, and acks wait for them; this is a sub-model of the paper's model (where acks need not
  wait for crashed neighbours), which only strengthens impossibility results.
* Executions are sequences of *blocks* of events (`run`); a disabled event is a no-op.
  Single-event blocks give the usual interleaving semantics, blocks of a synchronous round give
  lock-step executions.
* `Fair`: every broadcast of a node is eventually acknowledged unless the node crashes.
  `Timely T F`: block `j` happens at time `T (j+1)`, and every broadcast is acknowledged (or its
  node crashes) within time `F` of its start (the bound `F_ack` of the paper).
* `SolvesConsensus A G id f`: agreement, validity and termination in every timely execution with
  diverging time and at most `f` crashes.
* `Fair.exists_timely`: every fair execution is timely for `F = 2` with diverging time.
-/

namespace Cslib.AbstractMAC

open Filter

/-- A deterministic algorithm in the abstract MAC layer model. `I`: identity information of a node
(`Unit` for anonymous algorithms), `M`: messages, `S`: local states. -/
structure Algorithm (I M S : Type*) where
  /-- Initial state from the identity and the binary input. -/
  init : I → Bool → S
  /-- Receiving a message. -/
  recv : S → M → S
  /-- Receiving the acknowledgment of the current broadcast. -/
  ack : S → S
  /-- The message the node wants to broadcast (consulted only when it is idle). -/
  bcast : S → Option M
  /-- The decision of the node (only the first `some` value counts). -/
  out : S → Option Bool

/-- The local data of a node: algorithm state, recorded decision, current broadcast. -/
@[ext] structure Node (M S : Type*) where
  /-- Algorithm state. -/
  st : S
  /-- The (irrevocable) decision, if any. -/
  dec : Option Bool
  /-- The message currently being broadcast (`none`: idle). -/
  cur : Option M

variable {I M S V : Type*}

namespace Algorithm

variable (A : Algorithm I M S)

/-- Initial local data. -/
def initNode (i : I) (b : Bool) : Node M S :=
  ⟨A.init i b, A.out (A.init i b), A.bcast (A.init i b)⟩

/-- Local effect of receiving `m`. -/
def recvNode (x : Node M S) (m : M) : Node M S :=
  ⟨A.recv x.st m, x.dec.or (A.out (A.recv x.st m)), x.cur.or (A.bcast (A.recv x.st m))⟩

/-- Local effect of an acknowledgment. -/
def ackNode (x : Node M S) : Node M S :=
  ⟨A.ack x.st, x.dec.or (A.out (A.ack x.st)), A.bcast (A.ack x.st)⟩

@[simp] lemma recvNode_cur_of_isSome {x : Node M S} (h : x.cur.isSome) (m : M) :
    (A.recvNode x m).cur = x.cur := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
  simp [recvNode, hy]

lemma recvNode_dec {x : Node M S} {b : Bool} (h : x.dec = some b) (m : M) :
    (A.recvNode x m).dec = some b := by
  simp [recvNode, h]

lemma ackNode_dec {x : Node M S} {b : Bool} (h : x.dec = some b) :
    (A.ackNode x).dec = some b := by
  simp [ackNode, h]

end Algorithm

/-- A global configuration. -/
@[ext] structure Config (V M S : Type*) where
  /-- Local data of every node. -/
  loc : V → Node M S
  /-- `got u`: the neighbours that already received the current message of `u`. -/
  got : V → Set V
  /-- Crashed nodes. -/
  down : Set V
  /-- Number of acknowledgments received so far by each node. -/
  acks : V → ℕ

/-- Events. -/
inductive Event (V : Type*)
  /-- `v` receives the current message of `u`. -/
  | recv (u v : V)
  /-- `u` receives the acknowledgment of its current message. -/
  | ack (u : V)
  /-- `u` crashes. -/
  | crash (u : V)
  /-- No-op. -/
  | skip

/-- `u` is broadcasting. -/
def Config.Live (c : Config V M S) (u : V) : Prop := (c.loc u).cur.isSome

/-- The initial configuration. -/
def Config.init (A : Algorithm I M S) (id : V → I) (inp : V → Bool) : Config V M S :=
  ⟨fun v => A.initNode (id v) (inp v), fun _ => ∅, ∅, fun _ => 0⟩

section Step

variable [DecidableEq V] (A : Algorithm I M S) (G : SimpleGraph V)

open Classical in
/-- The effect of an event; disabled events are no-ops. -/
noncomputable def step (c : Config V M S) : Event V → Config V M S
  | .recv u v =>
    match (c.loc u).cur with
    | some m =>
      if u ∉ c.down ∧ G.Adj u v ∧ v ∉ c.got u then
        { c with
          loc := if v ∈ c.down then c.loc else Function.update c.loc v (A.recvNode (c.loc v) m)
          got := Function.update c.got u (insert v (c.got u)) }
      else c
    | none => c
  | .ack u =>
    if (c.loc u).cur.isSome ∧ u ∉ c.down ∧ ∀ v, G.Adj u v → v ∈ c.got u then
      { c with
        loc := Function.update c.loc u (A.ackNode (c.loc u))
        got := Function.update c.got u ∅
        acks := Function.update c.acks u (c.acks u + 1) }
    else c
  | .crash u => { c with down := insert u c.down }
  | .skip => c

/-- Configurations along an execution given by blocks of events `σ`. -/
noncomputable def run (c₀ : Config V M S) (σ : ℕ → List (Event V)) : ℕ → Config V M S
  | 0 => c₀
  | j + 1 => (σ j).foldl (step A G) (run c₀ σ j)

@[simp] lemma run_zero (c₀ : Config V M S) (σ) : run A G c₀ σ 0 = c₀ := rfl

lemma run_succ (c₀ : Config V M S) (σ) (j : ℕ) :
    run A G c₀ σ (j + 1) = (σ j).foldl (step A G) (run A G c₀ σ j) := rfl

/-- Configurations of the execution produced by a scheduling strategy `π` (block `j` is chosen
from the current configuration). -/
noncomputable def stratCfg (π : ℕ → Config V M S → List (Event V)) (c₀ : Config V M S) :
    ℕ → Config V M S
  | 0 => c₀
  | j + 1 => (π j (stratCfg π c₀ j)).foldl (step A G) (stratCfg π c₀ j)

/-- The blocks produced by a scheduling strategy. -/
noncomputable def stratSched (π : ℕ → Config V M S → List (Event V)) (c₀ : Config V M S) :
    ℕ → List (Event V) :=
  fun j => π j (stratCfg A G π c₀ j)

lemma run_stratSched (π : ℕ → Config V M S → List (Event V)) (c₀ : Config V M S) :
    run A G c₀ (stratSched A G π c₀) = stratCfg A G π c₀ := by
  funext j
  induction j with
  | zero => rfl
  | succ j ih => simp only [run_succ, ih, stratSched, stratCfg]

/-! ### Monotonicity along executions -/

/-- What a node `u` can rely on between two configurations of an execution: its ack counter and
the crashed set only grow, its decision is kept, and its broadcast stays the same until the
next ack. -/
structure Mono (u : V) (c c' : Config V M S) : Prop where
  acks_le : c.acks u ≤ c'.acks u
  down_sub : c.down ⊆ c'.down
  dec_eq : ∀ b, (c.loc u).dec = some b → (c'.loc u).dec = some b
  cur_eq : c.Live u → c'.acks u = c.acks u → (c'.loc u).cur = (c.loc u).cur

omit [DecidableEq V] in
lemma Mono.refl (u : V) (c : Config V M S) : Mono u c c :=
  ⟨le_rfl, subset_rfl, fun _ h => h, fun _ _ => rfl⟩

omit [DecidableEq V] in
lemma Mono.trans {u : V} {c c' c'' : Config V M S} (h₁ : Mono u c c') (h₂ : Mono u c' c'') :
    Mono u c c'' where
  acks_le := h₁.acks_le.trans h₂.acks_le
  down_sub := h₁.down_sub.trans h₂.down_sub
  dec_eq b h := h₂.dec_eq b (h₁.dec_eq b h)
  cur_eq hl he := by
    have e1 : c'.acks u = c.acks u := le_antisymm (he ▸ h₂.acks_le) h₁.acks_le
    have e2 : c''.acks u = c'.acks u := e1 ▸ he
    have hc := h₁.cur_eq hl e1
    rw [h₂.cur_eq (by unfold Config.Live; rw [hc]; exact hl) e2, hc]

lemma mono_step (u : V) (c : Config V M S) (e : Event V) : Mono u c (step A G c e) := by
  cases e with
  | recv x y =>
    cases hx : (c.loc x).cur with
    | none => simpa [step, hx] using Mono.refl u c
    | some m =>
      by_cases hc : x ∉ c.down ∧ G.Adj x y ∧ y ∉ c.got x
      · simp only [step, hx, hc, not_false_eq_true, and_self, ite_true]
        refine ⟨le_rfl, subset_rfl, fun b hb => ?_, fun hl _ => ?_⟩
        · split_ifs
          · exact hb
          · by_cases huy : u = y
            · subst huy; simp [A.recvNode_dec hb]
            · simp [Function.update_of_ne huy, hb]
        · split_ifs
          · rfl
          · by_cases huy : u = y
            · subst huy; simp [A.recvNode_cur_of_isSome hl]
            · simp [Function.update_of_ne huy]
      · simpa [step, hx, hc] using Mono.refl u c
  | ack x =>
    by_cases hc : (c.loc x).cur.isSome ∧ x ∉ c.down ∧ ∀ v, G.Adj x v → v ∈ c.got x
    · simp only [step]; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      by_cases hux : u = x
      · subst hux
        refine ⟨by simp, subset_rfl, fun b hb => by simp [A.ackNode_dec hb], fun _ he => ?_⟩
        simp at he
      · refine ⟨by simp [Function.update_of_ne hux], subset_rfl,
          fun b hb => by simp [Function.update_of_ne hux, hb], fun _ _ => ?_⟩
        simp [Function.update_of_ne hux]
    · simpa [step, hc] using Mono.refl u c
  | crash x => exact ⟨le_rfl, Set.subset_insert _ _, fun _ h => h, fun _ _ => rfl⟩
  | skip => exact Mono.refl u c

lemma mono_foldl (u : V) (l : List (Event V)) (c : Config V M S) :
    Mono u c (l.foldl (step A G) c) := by
  induction l generalizing c with
  | nil => exact Mono.refl u c
  | cons e l ih => exact (mono_step A G u c e).trans (ih _)

lemma mono_run (u : V) (c₀ : Config V M S) (σ) {i j : ℕ} (h : i ≤ j) :
    Mono u (run A G c₀ σ i) (run A G c₀ σ j) := by
  induction h with
  | refl => exact Mono.refl u _
  | step _ ih => exact ih.trans (mono_foldl A G u _ _)

end Step

/-! ### Fairness, timeliness, consensus -/

section Spec

variable [DecidableEq V] (A : Algorithm I M S) (G : SimpleGraph V)

/-- Progress of the broadcast of `u` between configurations `i` and `j`: `u` received an ack or
crashed. -/
def Prog (c₀ : Config V M S) (σ : ℕ → List (Event V)) (u : V) (i j : ℕ) : Prop :=
  (run A G c₀ σ i).acks u < (run A G c₀ σ j).acks u ∨ u ∈ (run A G c₀ σ j).down

/-- Fairness: every broadcast is eventually acknowledged, unless its node crashes. -/
def Fair (c₀ : Config V M S) (σ : ℕ → List (Event V)) : Prop :=
  ∀ u i, (run A G c₀ σ i).Live u → ∃ j ≥ i, Prog A G c₀ σ u i j

/-- The broadcast of `u` in configuration `i` started in the block leading to `i` (or
initially). -/
def Fresh (c₀ : Config V M S) (σ : ℕ → List (Event V)) (u : V) : ℕ → Prop
  | 0 => (run A G c₀ σ 0).Live u
  | i + 1 => (run A G c₀ σ (i + 1)).Live u ∧
      ¬ ((run A G c₀ σ i).Live u ∧ (run A G c₀ σ i).acks u = (run A G c₀ σ (i + 1)).acks u)

/-- Timed executions with acknowledgment bound `F` (`F_ack`): configuration `i` exists at time
`T i` (block `j` happens at time `T (j + 1)`), and every broadcast is acknowledged (or its node
crashes) at most `F` time units after it started. -/
def Timely (c₀ : Config V M S) (σ : ℕ → List (Event V)) (T : ℕ → ℝ) (F : ℝ) : Prop :=
  Monotone T ∧ T 0 = 0 ∧
    ∀ u i, Fresh A G c₀ σ u i → ∃ j ≥ i, T j ≤ T i + F ∧ Prog A G c₀ σ u i j

/-- Agreement: no two decisions differ. -/
def Agreement (c₀ : Config V M S) (σ : ℕ → List (Event V)) : Prop :=
  ∀ i j u v b b', ((run A G c₀ σ i).loc u).dec = some b → ((run A G c₀ σ j).loc v).dec = some b' →
    b = b'

/-- Validity: every decision is the input of some node. -/
def Validity (inp : V → Bool) (c₀ : Config V M S) (σ : ℕ → List (Event V)) : Prop :=
  ∀ i u b, ((run A G c₀ σ i).loc u).dec = some b → ∃ w, inp w = b

/-- Termination: every node that never crashes decides. -/
def Termination (c₀ : Config V M S) (σ : ℕ → List (Event V)) : Prop :=
  ∀ u, (∀ i, u ∉ (run A G c₀ σ i).down) → ∃ i, ((run A G c₀ σ i).loc u).dec.isSome

/-- `A` solves binary consensus on the network `G` with identities `id`, tolerating `f` crashes:
in every timely execution (for some bound `F_ack`) with diverging time and at most `f` crashes,
agreement, validity and termination hold. -/
def SolvesConsensus (id : V → I) (f : ℕ) : Prop :=
  ∀ (inp : V → Bool) (σ : ℕ → List (Event V)) (T : ℕ → ℝ) (F : ℝ),
    Timely A G (Config.init A id inp) σ T F → Tendsto T atTop atTop →
    (∀ i, (run A G (Config.init A id inp) σ i).down.encard ≤ f) →
    Agreement A G (Config.init A id inp) σ ∧ Validity A G inp (Config.init A id inp) σ ∧
      Termination A G (Config.init A id inp) σ

variable {A G}

lemma Prog.mono {c₀ : Config V M S} {σ} {u : V} {i j k : ℕ} (h : Prog A G c₀ σ u i j)
    (hjk : j ≤ k) : Prog A G c₀ σ u i k := by
  have hm := mono_run A G u c₀ σ hjk
  rcases h with h | h
  · exact Or.inl (h.trans_le hm.acks_le)
  · exact Or.inr (hm.down_sub h)

lemma Fresh.live {c₀ : Config V M S} {σ} {u : V} {i : ℕ} (h : Fresh A G c₀ σ u i) :
    (run A G c₀ σ i).Live u := by
  cases i with
  | zero => exact h
  | succ i => exact h.1

/-- The broadcast pending at `i` is still pending at `j ≥ i` if there was no progress. -/
lemma live_of_not_prog {c₀ : Config V M S} {σ} {u : V} {i j : ℕ} (hij : i ≤ j)
    (hl : (run A G c₀ σ i).Live u) (hp : ¬ Prog A G c₀ σ u i j) :
    (run A G c₀ σ j).Live u ∧ (run A G c₀ σ j).acks u = (run A G c₀ σ i).acks u := by
  have hm := mono_run A G u c₀ σ hij
  have he : (run A G c₀ σ j).acks u = (run A G c₀ σ i).acks u :=
    le_antisymm (not_lt.1 fun h => hp (Or.inl h)) hm.acks_le
  refine ⟨?_, he⟩
  unfold Config.Live; rw [hm.cur_eq hl he]; exact hl

/-- Cut points of a fair execution: after `i`, a point by which every broadcast pending at `i`
made progress. -/
lemma Fair.exists_cut [Finite V] {c₀ : Config V M S} {σ} (hf : Fair A G c₀ σ) (i : ℕ) :
    ∃ k, i < k ∧ ∀ u, (run A G c₀ σ i).Live u → Prog A G c₀ σ u i k := by
  classical
  have := Fintype.ofFinite V
  have hu : ∀ u, ∃ j, (run A G c₀ σ i).Live u → j ≥ i ∧ Prog A G c₀ σ u i j := by
    intro u
    by_cases hl : (run A G c₀ σ i).Live u
    · obtain ⟨j, hj, hp⟩ := hf u i hl
      exact ⟨j, fun _ => ⟨hj, hp⟩⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose J hJ using hu
  refine ⟨Finset.univ.sup J + i + 1, by omega, fun u hl => ?_⟩
  exact (hJ u hl).2.mono (by have := Finset.le_sup (f := J) (Finset.mem_univ u); omega)

/-- Every fair execution is timely, for the bound `F = 2`, with diverging time. -/
theorem Fair.exists_timely [Finite V] {c₀ : Config V M S} {σ} (hf : Fair A G c₀ σ) :
    ∃ T : ℕ → ℝ, Timely A G c₀ σ T 2 ∧ Tendsto T atTop atTop := by
  classical
  choose nx hnx using hf.exists_cut
  let cut : ℕ → ℕ := fun m => nx^[m] 0
  have cut_succ : ∀ m, cut (m + 1) = nx (cut m) := fun m => Function.iterate_succ_apply' _ _ _
  have cut_lt : ∀ m, cut m < cut (m + 1) := fun m => by rw [cut_succ]; exact (hnx _).1
  have cut_mono : StrictMono cut := strictMono_nat_of_lt_succ cut_lt
  have cut_ge : ∀ m, m ≤ cut m := fun m => cut_mono.id_le m
  have hex : ∀ i, ∃ m, i < cut (m + 1) := fun i => ⟨i, (cut_ge (i + 1)).trans_lt' (by omega)⟩
  let Tn : ℕ → ℕ := fun i => Nat.find (hex i)
  have Tn_spec : ∀ i, cut (Tn i) ≤ i ∧ i < cut (Tn i + 1) := by
    intro i
    refine ⟨?_, Nat.find_spec (hex i)⟩
    rcases h : Tn i with _ | m
    · show nx^[0] 0 ≤ i; simp
    · have := Nat.find_min (hex i) (m := m) (by simp only [Tn] at h; omega)
      omega
  have Tn_cut : ∀ m, Tn (cut m) = m := by
    intro m
    obtain ⟨h1, h2⟩ := Tn_spec (cut m)
    have a := cut_mono.le_iff_le.1 h1
    have b := cut_mono.lt_iff_lt.1 h2
    omega
  have Tn_mono : Monotone Tn := by
    intro i j hij
    exact Nat.find_mono (fun m hm => lt_of_le_of_lt hij hm)
  refine ⟨fun i => (Tn i : ℝ), ⟨fun i j hij => by simp only; exact_mod_cast Tn_mono hij, ?_, ?_⟩,
    ?_⟩
  · simp only [Nat.cast_eq_zero]
    have := Tn_spec 0
    have h0 : cut 0 = 0 := rfl
    by_contra hne
    have := cut_mono (Nat.pos_of_ne_zero hne)
    omega
  · intro u i hfr
    have hl := hfr.live
    set m := Tn i
    obtain ⟨hm1, hm2⟩ := Tn_spec i
    by_cases hp : Prog A G c₀ σ u i (cut (m + 1))
    · refine ⟨cut (m + 1), hm2.le, ?_, hp⟩
      simp only [Tn_cut]; push_cast; linarith
    · obtain ⟨hl', he⟩ := live_of_not_prog hm2.le hl hp
      have hp2 := (hnx (cut (m + 1))).2 u hl'
      rw [← cut_succ] at hp2
      refine ⟨cut (m + 2), (hm2.trans (cut_lt _)).le, ?_, ?_⟩
      · simp only [Tn_cut]; push_cast; linarith
      · rcases hp2 with h | h
        · exact Or.inl (he ▸ h)
        · exact Or.inr h
  · refine tendsto_atTop_atTop.2 fun b => ⟨cut ⌈b⌉₊, fun a ha => ?_⟩
    have := Tn_mono ha
    rw [Tn_cut] at this
    exact (Nat.le_ceil b).trans (by exact_mod_cast this)

/-- In a timely execution with diverging time every broadcast eventually makes progress. -/
lemma Timely.fair {c₀ : Config V M S} {σ} {T : ℕ → ℝ} {F : ℝ} (h : Timely A G c₀ σ T F) :
    Fair A G c₀ σ := by
  intro u i hl
  -- the broadcast pending at `i` started at the last fresh point `≤ i`
  induction i with
  | zero =>
    obtain ⟨j, hj, -, hp⟩ := h.2.2 u 0 hl
    exact ⟨j, hj, hp⟩
  | succ i ih =>
    by_cases hfr : Fresh A G c₀ σ u (i + 1)
    · obtain ⟨j, hj, -, hp⟩ := h.2.2 u _ hfr
      exact ⟨j, hj, hp⟩
    · have h' : (run A G c₀ σ i).Live u ∧
          (run A G c₀ σ i).acks u = (run A G c₀ σ (i + 1)).acks u := by
        by_contra hc; exact hfr ⟨hl, hc⟩
      obtain ⟨j, hj, hp⟩ := ih h'.1
      by_cases hji : j ≤ i
      · -- progress happened before `i + 1`: impossible for acks, possible for crashes
        refine ⟨i + 1, le_rfl, ?_⟩
        rcases hp.mono (Nat.le_succ_of_le hji) with h1 | h1
        · exact absurd (h'.2 ▸ h1) (lt_irrefl _)
        · exact Or.inr h1
      · refine ⟨j, by omega, ?_⟩
        rcases hp with h1 | h1
        · exact Or.inl (h'.2 ▸ h1)
        · exact Or.inr h1

end Spec

end Cslib.AbstractMAC
