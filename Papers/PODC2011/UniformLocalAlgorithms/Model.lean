import Mathlib
import Cslib.Computability.Distributed.Local.Locality

-- CSLib candidate: `Alg`, `res`, `Stage`, `Pruning` and the alternating-algorithm machinery
-- (target e.g. `Cslib/Computability/Distributed/Local/Terminating.lean`).

/-!
# The model of Korman–Sereni–Viennot, PODC 2011 (Section 2 and Section 3.2–3.3)

A. Korman, J.-S. Sereni, L. Viennot, *Toward More Localized Local Algorithms: Removing
Assumptions Concerning Global Knowledge*, PODC 2011 / Distributed Computing (arXiv:1512.03306).

We work in the LOCAL model with unique identifiers, in the extensional style of
`Cslib.Computability.Distributed.Local.Locality`: the identifiers are the elements of a fixed type
`V`; an *instance* is a pair `(G, x)` of a graph `G : SimpleGraph V` and an input labelling
`x : V → Option α`, whose node set is `supp x = {v | x v ≠ none}` and whose graph is
`res G x` (the subgraph of `G` induced by `supp x`). This lets us speak about the induced subgraphs
produced by pruning without changing the vertex type.

* `Problem V α β`: a problem `Pb` (a predicate on triples `(G, x, y)`) which only looks at the
  induced instance `res G x` and at the outputs of nodes of the instance, and which contains the
  empty instance.
* `Family V α`: a collection `F` of instances (we require `res G x = G` for its members).
* `Alg V α β`: a (uniform, deterministic) local algorithm with termination: `A.out t G x v` is the
  output of node `v` after `t` rounds (`none` = not terminated yet); it is a `t`-local function of
  the instance, and outputs are final. `Alg.SolvesWithin A Pb G x T`: after `T` rounds all nodes
  of the instance have terminated, and their outputs form a solution.
* `Stage V α β`: an algorithm that runs for a fixed number `rad` of rounds and produces an output at
  every node (e.g. `Alg.restrict`, "algorithm `A` restricted to `t` rounds").
* `Pruning Pb F`: a pruning algorithm (Section 3.2): a constant-time uniform algorithm which, given
  a tentative output `ŷ`, prunes a set of nodes and possibly changes the inputs of the others; it
  satisfies *solution detection* and *gluing*. `Pruning.Monotone P p`: `P` does not increase the
  parameter `p`.
* `Pruning.alg P phases`: the alternating algorithm (Section 3.3) for a sequence of stages, given
  as a sequence of finite *phases* (lists of stages); nodes output at the end of the phase in which
  they are pruned.

## Main results

* `Pruning.solvesWithin_of_runList_empty` (Observation 3.4 + running time): if all nodes are pruned
  after the first `s` phases, the alternating algorithm solves the instance within
  `max s (duration of the first s phases)` rounds.
* `Pruning.act_runList_eq_none_of_mem`: progress — if a stage of a list solves every instance
  reachable during the run, all nodes are pruned at the end of the list.
-/

open Cslib.Local SimpleGraph

namespace Podc.UniformLocalAlgorithms

variable {V α β γ : Type*}

/-! ### Instances -/

/-- The node set of an instance with input labelling `x`. -/
def supp (x : V → Option α) : Set V := {v | (x v).isSome}

/-- The subgraph of `G` induced by the nodes of the instance `x`. -/
def res (G : SimpleGraph V) (x : V → Option α) : SimpleGraph V where
  Adj u w := G.Adj u w ∧ (x u).isSome ∧ (x w).isSome
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

@[simp] lemma res_adj {G : SimpleGraph V} {x : V → Option α} {u w : V} :
    (res G x).Adj u w ↔ G.Adj u w ∧ (x u).isSome ∧ (x w).isSome := Iff.rfl

lemma res_le (G : SimpleGraph V) (x : V → Option α) : res G x ≤ G := fun _ _ h => h.1

lemma res_res {G : SimpleGraph V} {x : V → Option α} {x' : V → Option γ}
    (h : ∀ v, (x' v).isSome → (x v).isSome) : res (res G x) x' = res G x' := by
  ext u w
  simp only [res_adj]
  constructor
  · rintro ⟨⟨h1, -, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h _ h2, h _ h3⟩, h2, h3⟩

lemma res_none (G : SimpleGraph V) : res G (fun _ : V => (none : Option α)) = ⊥ := by
  ext u w; simp

/-- The induced subgraph depends only on the node set. -/
lemma res_congr {G : SimpleGraph V} {x : V → Option α} {x' : V → Option γ}
    (h : ∀ v, (x v).isSome ↔ (x' v).isSome) : res G x = res G x' := by
  ext u w; simp [h]

/-- Restricting the graph to the instance does not change the radius-`R` views. This is the
locality of "run the algorithm on the induced subgraph". -/
lemma viewEq_res {R : ℕ} {G G' : SimpleGraph V} {x x' : V → Option α} {v : V}
    (h : ViewEq R G x G' x' v) : ViewEq R (res G x) x (res G' x') x' v := by
  have hd : ∀ w, (res G x).edist v w ≤ R → G.edist v w ≤ R := fun w hw =>
    (edist_anti (res_le G x)).trans hw
  refine ⟨fun w hw z => ?_, fun w hw => h.2 w (hd w hw)⟩
  have hwG : G.edist v w < R := lt_of_le_of_lt (edist_anti (res_le G x)) hw
  have hadj := h.1 hwG z
  have hw' : x w = x' w := h.2 w hwG.le
  simp only [res_adj, hw']
  have hz : ∀ {z}, G.Adj w z → G.edist v z ≤ R := fun {z} hwz => by
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hwG)
    have hjR : j < R := by rw [← hj] at hwG; exact_mod_cast hwG
    have h1 : G.edist w z ≤ (1 : ℕ) := by simp [edist_eq_one_iff_adj.2 hwz]
    have h0 : G.edist v w ≤ (j : ℕ) := hj ▸ le_refl _
    exact (edist_le_natCast_add (G := G) h0 h1).trans (by exact_mod_cast hjR)
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hadj.1 h1, h2, (h.2 _ (hz h1)) ▸ h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h1' := hadj.2 h1
    exact ⟨h1', h2, (h.2 _ (hz h1')).symm ▸ h3⟩

/-- If `f` is `R`-local, then so is "run `f` on the induced instance". -/
lemma isLocal_res {R : ℕ} {f : SimpleGraph V → (V → Option α) → V → β} (hf : IsLocal R f) :
    IsLocal R (fun G x => f (res G x) x) :=
  fun _ _ _ _ _ h => hf _ _ _ _ _ (viewEq_res h)

/-- Locality is preserved under relabelling the inputs pointwise. -/
lemma isLocal_comp_label {R : ℕ} {f : SimpleGraph V → (V → α) → V → β} (hf : IsLocal R f)
    (e : γ → α) : IsLocal R (fun G (x : V → γ) => f G (e ∘ x)) :=
  fun _ _ _ _ _ h => hf _ _ _ _ _ ⟨h.1, fun u hu => by simp [h.2 u hu]⟩

/-- Pairing two `R`-local functions. -/
lemma isLocal_pair {R : ℕ} {f : SimpleGraph V → (V → α) → V → β}
    {g : SimpleGraph V → (V → α) → V → γ} (hf : IsLocal R f) (hg : IsLocal R g) :
    IsLocal R (fun G x v => (f G x v, g G x v)) :=
  fun _ _ _ _ _ h => by simp [hf _ _ _ _ _ h, hg _ _ _ _ _ h]

/-- A function of the own label is `R`-local for every `R`. -/
lemma isLocal_label (R : ℕ) (e : α → β) : IsLocal (V := V) R (fun _ x v => e (x v)) :=
  fun _ _ _ _ v h => by simp [h.2 v (by simp)]

/-! ### Problems, families, parameters -/

/-- A problem: a set of triples `(G, x, y)` of an instance and an output vector. It only depends
on the induced instance `res G x` (`res_congr`) and on the outputs of the nodes of the instance
(`congr`), and the empty output is a solution of the empty instance (`empty`). -/
structure Problem (V α β : Type*) where
  /-- `sol G x y`: `y` is a solution of the instance `(G, x)`. -/
  sol : SimpleGraph V → (V → Option α) → (V → β) → Prop
  /-- Only the outputs of the nodes of the instance matter. -/
  congr : ∀ {G x y y'}, (∀ v, (x v).isSome → y v = y' v) → sol G x y → sol G x y'
  /-- The empty instance has a solution. -/
  empty : ∃ y, sol ⊥ (fun _ => none) y

/-- A family of instances. Its members are *normalized*: the graph is induced by the node set. -/
structure Family (V α : Type*) where
  /-- Membership. -/
  mem : SimpleGraph V → (V → Option α) → Prop
  /-- Members are normalized. -/
  res_eq : ∀ {G x}, mem G x → res G x = G

/-- A parameter: a natural number attached to each instance (e.g. `n`, `Δ`, the arboricity). -/
abbrev Param (V α : Type*) := SimpleGraph V → (V → Option α) → ℕ

/-! ### Algorithms -/

/-- A uniform deterministic LOCAL algorithm with termination: `out t G x v` is the output of `v`
after `t` rounds on the instance `(G, x)` (`none` if `v` has not terminated yet). It is computed
from the radius-`t` view of `v`, and outputs are final. -/
structure Alg (V α β : Type*) where
  /-- Output after `t` rounds. -/
  out : ℕ → SimpleGraph V → (V → Option α) → V → Option β
  /-- The output after `t` rounds depends only on the radius-`t` view. -/
  isLocal : ∀ t, IsLocal t (out t)
  /-- Outputs are final. -/
  stable : ∀ {t G x v b}, out t G x v = some b → out (t + 1) G x v = some b

namespace Alg

variable (A : Alg V α β)

lemma out_mono {t t' : ℕ} (h : t ≤ t') {G : SimpleGraph V} {x : V → Option α} {v : V} {b : β}
    (hb : A.out t G x v = some b) : A.out t' G x v = some b := by
  induction h with
  | refl => exact hb
  | step _ ih => exact A.stable ih

/-- `A` solves the instance `(G, x)` of `Pb` within `T` rounds: after `T` rounds every node of the
instance has terminated and the outputs form a solution. -/
def SolvesWithin (Pb : Problem V α β) (G : SimpleGraph V) (x : V → Option α) (T : ℕ) : Prop :=
  ∃ y, Pb.sol G x y ∧ ∀ v, (x v).isSome → A.out T G x v = some (y v)

lemma SolvesWithin.mono {Pb : Problem V α β} {G : SimpleGraph V} {x : V → Option α} {T T' : ℕ}
    (h : A.SolvesWithin Pb G x T) (hT : T ≤ T') : A.SolvesWithin Pb G x T' := by
  obtain ⟨y, hy, hout⟩ := h
  exact ⟨y, hy, fun v hv => A.out_mono hT (hout v hv)⟩

end Alg

/-- An algorithm that runs for exactly `rad` rounds and then outputs a value at every node. -/
structure Stage (V α β : Type*) where
  /-- The outputs. -/
  run : SimpleGraph V → (V → Option α) → V → β
  /-- The number of rounds. -/
  rad : ℕ
  /-- The outputs are computed in `rad` rounds. -/
  isLocal : IsLocal rad run

/-- The algorithm `A` restricted to `t` rounds (Section 2): a node that has not terminated after
`t` rounds outputs the default value `b₀`. -/
def Alg.restrict (A : Alg V α β) (t : ℕ) (b₀ : β) : Stage V α β where
  run G x v := (A.out t G x v).getD b₀
  rad := t
  isLocal := fun _ _ _ _ _ h => by simp only [A.isLocal t _ _ _ _ _ h]

lemma Alg.restrict_run_of_solvesWithin {A : Alg V α β} {Pb : Problem V α β} {G : SimpleGraph V}
    {x : V → Option α} {T t : ℕ} (b₀ : β) (h : A.SolvesWithin Pb G x T) (hT : T ≤ t) :
    Pb.sol G x ((A.restrict t b₀).run G x) := by
  obtain ⟨y, hy, hout⟩ := h.mono A hT
  exact Pb.congr (fun v hv => by simp [Alg.restrict, hout v hv]) hy

/-! ### Pruning algorithms (Section 3.2) -/

/-- A pruning algorithm for `Pb` and `F`: a uniform algorithm running in `rad` rounds which, given an
instance `(G, x)` and a tentative output `ŷ`, returns at each node either `none` (the node is
pruned) or its new input; the non-pruned nodes form the new instance
`(res G (prune G x ŷ), prune G x ŷ)` (an induced subgraph with possibly modified inputs). -/
structure Pruning (Pb : Problem V α β) (F : Family V α) where
  /-- The new input of each node, `none` for pruned nodes. -/
  prune : SimpleGraph V → (V → Option α) → (V → β) → V → Option α
  /-- The running time. -/
  rad : ℕ
  /-- Locality: `prune` is computed in `rad` rounds from the labels `(x v, ŷ v)`. -/
  isLocal : IsLocal rad (fun G (z : V → Option α × β) => prune G (fun v => (z v).1)
    (fun v => (z v).2))
  /-- The new instance is a sub-instance: nodes outside the instance stay outside. -/
  sub : ∀ G x ŷ v, (prune G x ŷ v).isSome → (x v).isSome
  /-- The new instance belongs to the family. -/
  mem : ∀ G x ŷ, F.mem G x → F.mem (res G (prune G x ŷ)) (prune G x ŷ)
  /-- Solution detection: if `ŷ` is a solution, all nodes are pruned. -/
  detect : ∀ G x ŷ, F.mem G x → Pb.sol G x ŷ → ∀ v, prune G x ŷ v = none
  /-- Gluing: a solution of the new instance combined with `ŷ` on the pruned nodes is a solution. -/
  glue : ∀ G x ŷ y', F.mem G x → Pb.sol (res G (prune G x ŷ)) (prune G x ŷ) y' →
    Pb.sol G x (fun v => if (prune G x ŷ v).isSome then y' v else ŷ v)

namespace Pruning

variable {Pb : Problem V α β} {F : Family V α} (P : Pruning Pb F)

/-- `P` is monotone with respect to the parameter `p`: pruning never increases `p`. -/
def Monotone (p : Param V α) : Prop :=
  ∀ G x ŷ, F.mem G x → p (res G (P.prune G x ŷ)) (P.prune G x ŷ) ≤ p G x

/-- The state of an alternating algorithm at a node: its current input (`none` once pruned, or for
nodes outside the instance) and its committed output (`some` once pruned). -/
abbrev State (V α β : Type*) := V → Option α × Option β

/-- The current instance encoded in a state. -/
def act (z : State V α β) : V → Option α := fun v => (z v).1

/-- One stage `B ; P` of an alternating algorithm, run on the instance induced in `G` by the
current inputs. -/
def step (B : Stage V α β) (G : SimpleGraph V) (z : State V α β) : State V α β :=
  let x := act z
  let H := res G x
  let ŷ := B.run H x
  let x' := P.prune H x ŷ
  fun v => (x' v, if (x v).isSome ∧ (x' v).isNone then some (ŷ v) else (z v).2)

/-- Run a list of stages. -/
def runList (L : List (Stage V α β)) (G : SimpleGraph V) (z : State V α β) : State V α β :=
  L.foldl (fun z B => P.step B G z) z

/-- The initial state. -/
def init (x : V → Option α) : State V α β := fun v => (x v, none)

/-- The number of rounds used by a list of stages (each followed by `P`). -/
def dur (L : List (Stage V α β)) : ℕ := (L.map fun B => B.rad + P.rad).sum

@[simp] lemma runList_nil (G : SimpleGraph V) (z : State V α β) : P.runList [] G z = z := rfl

@[simp] lemma runList_cons (B : Stage V α β) (L : List (Stage V α β)) (G : SimpleGraph V)
    (z : State V α β) : P.runList (B :: L) G z = P.runList L G (P.step B G z) := rfl

lemma runList_append (L L' : List (Stage V α β)) (G : SimpleGraph V) (z : State V α β) :
    P.runList (L ++ L') G z = P.runList L' G (P.runList L G z) := by
  simp [runList, List.foldl_append]

@[simp] lemma dur_nil : P.dur ([] : List (Stage V α β)) = 0 := rfl

@[simp] lemma dur_cons (B : Stage V α β) (L : List (Stage V α β)) :
    P.dur (B :: L) = B.rad + P.rad + P.dur L := by simp [dur]

lemma dur_append (L L' : List (Stage V α β)) : P.dur (L ++ L') = P.dur L + P.dur L' := by
  simp [dur]

/-! #### Locality of the alternating algorithm -/

lemma step_isLocal (B : Stage V α β) :
    IsLocal (P.rad + B.rad) (fun G z => P.step B G z) := by
  -- the tentative output, as a function of `(G, z)`
  have hŷ : IsLocal B.rad (fun G (z : State V α β) => B.run (res G (act z)) (act z)) :=
    isLocal_comp_label (isLocal_res B.isLocal) (fun p : Option α × Option β => p.1)
  -- the labels `(x v, ŷ v)` fed to the pruning algorithm, together with the old state
  have hpair : IsLocal B.rad (fun G (z : State V α β) v =>
      (((act z v, B.run (res G (act z)) (act z) v)), z v)) :=
    isLocal_pair (isLocal_pair (isLocal_label B.rad (fun p : Option α × Option β => p.1)) hŷ)
      (isLocal_label B.rad id)
  have hP : IsLocal P.rad (fun G (w : V → (Option α × β) × (Option α × Option β)) v =>
      (P.prune (res G (fun u => (w u).1.1)) (fun u => (w u).1.1) (fun u => (w u).1.2) v,
        (w v).1.2, w v)) := by
    have h1 : IsLocal P.rad (fun G (w : V → (Option α × β) × (Option α × Option β)) =>
        P.prune (res G (fun u => (w u).1.1)) (fun u => (w u).1.1) (fun u => (w u).1.2)) := by
      have := isLocal_comp_label P.isLocal (fun q : (Option α × β) × (Option α × Option β) => q.1)
      intro G w G' w' v h
      have hv := viewEq_res (x := fun u => (w u).1.1) (x' := fun u => (w' u).1.1)
        ⟨h.1, fun u hu => by simp [h.2 u hu]⟩
      have hv' : ViewEq P.rad (res G (fun u => (w u).1.1)) w
          (res G' (fun u => (w' u).1.1)) w' v := ⟨hv.1, fun u hu => by
            have := hv.2 u hu
            exact h.2 u ((edist_anti (res_le _ _)).trans hu)⟩
      exact this _ _ _ _ _ hv'
    exact isLocal_pair h1 (isLocal_pair (isLocal_label P.rad
      (fun q : (Option α × β) × (Option α × Option β) => q.1.2)) (isLocal_label P.rad id))
  have hc := hP.comp hpair
  intro G z G' z' v h
  have := hc G z G' z' v h
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2, h3⟩ := this
  have h1' : P.prune (res G (act z)) (act z) (B.run (res G (act z)) (act z)) v =
      P.prune (res G' (act z')) (act z') (B.run (res G' (act z')) (act z')) v := h1
  have h3' : z v = z' v := h3.2
  have h4 : act z v = act z' v := by simp [act, h3']
  simp only [step]
  rw [h1', h2, h3', h4]

lemma runList_isLocal (L : List (Stage V α β)) :
    IsLocal (P.dur L) (fun G z => P.runList L G z) := by
  induction L with
  | nil => exact fun _ _ _ _ v h => by simpa using h.2 v (by simp)
  | cons B L ih =>
    have := ih.comp (P.step_isLocal B)
    simp only [dur_cons]
    exact (this.mono (by omega))

/-! #### Basic facts about runs -/

lemma act_step_isSome {B : Stage V α β} {G : SimpleGraph V} {z : State V α β} {v : V}
    (h : (act (P.step B G z) v).isSome) : (act z v).isSome :=
  P.sub _ _ _ v h

lemma act_runList_isSome {L : List (Stage V α β)} {G : SimpleGraph V} {z : State V α β} {v : V}
    (h : (act (P.runList L G z) v).isSome) : (act z v).isSome := by
  induction L generalizing z with
  | nil => exact h
  | cons B L ih => exact P.act_step_isSome (ih h)

/-- Committed outputs never change. -/
lemma step_snd {B : Stage V α β} {G : SimpleGraph V} {z : State V α β} {v : V} {b : β}
    (h : (z v).2 = some b) (hv : (act z v).isNone) : (P.step B G z v).2 = some b := by
  simp only [step]
  split_ifs with hc
  · simp_all [act]
  · exact h

/-- Valid states: a node with a committed output is no longer active. -/
def Valid (z : State V α β) : Prop := ∀ v, (z v).2.isSome → act z v = none

lemma valid_init (x : V → Option α) : Valid (init x : State V α β) := by
  intro v h; simp [init] at h

lemma valid_step {B : Stage V α β} {G : SimpleGraph V} {z : State V α β} (hz : Valid z) :
    Valid (P.step B G z) := by
  intro v hv
  simp only [step] at hv ⊢
  split_ifs at hv with h
  · simpa [act] using h.2
  · have := hz v (by simpa using hv)
    have h2 : (P.prune (res G (act z)) (act z) (B.run (res G (act z)) (act z)) v).isSome = false := by
      by_contra hc
      have := P.sub _ _ _ v (Bool.not_eq_false _ ▸ hc)
      simp_all
    simpa [act] using h2

lemma valid_runList {L : List (Stage V α β)} {G : SimpleGraph V} {z : State V α β} (hz : Valid z) :
    Valid (P.runList L G z) := by
  induction L generalizing z with
  | nil => exact hz
  | cons B L ih => exact ih (P.valid_step hz)

/-- Committed outputs never change. -/
lemma runList_snd {L : List (Stage V α β)} {G : SimpleGraph V} {z : State V α β} (hz : Valid z)
    {v : V} {b : β} (h : (z v).2 = some b) : (P.runList L G z v).2 = some b := by
  induction L generalizing z with
  | nil => exact h
  | cons B L ih =>
    exact ih (P.valid_step hz) (P.step_snd h (by simp [hz v (by simp [h])]))

/-- Once all nodes are pruned, the stages do nothing. -/
lemma step_of_act_eq_none {B : Stage V α β} {G : SimpleGraph V} {z : State V α β}
    (h : ∀ v, act z v = none) : P.step B G z = z := by
  funext v
  have h1 : P.prune (res G (act z)) (act z) (B.run (res G (act z)) (act z)) v = none := by
    by_contra hc
    have := P.sub _ _ _ v (Option.isSome_iff_ne_none.2 hc)
    simp [h v] at this
  have h2 : (z v).1 = none := h v
  simp only [step, h1]
  ext <;> simp [h2, act]

lemma runList_of_act_eq_none {L : List (Stage V α β)} {G : SimpleGraph V} {z : State V α β}
    (h : ∀ v, act z v = none) : P.runList L G z = z := by
  induction L with
  | nil => rfl
  | cons B L ih => simp only [runList_cons, P.step_of_act_eq_none h, ih]

/-- An invariant of the current instances preserved by pruning is preserved by runs. -/
lemma act_runList_inv {Inv : (V → Option α) → Prop} {G : SimpleGraph V}
    (hInv : ∀ x ŷ, Inv x → Inv (P.prune (res G x) x ŷ)) {L : List (Stage V α β)}
    {z : State V α β} (hz : Inv (act z)) : Inv (act (P.runList L G z)) := by
  induction L generalizing z with
  | nil => exact hz
  | cons B L ih => exact ih (hInv _ _ hz)

/-- Progress: if a stage `B` of the list solves every instance satisfying an invariant preserved by
pruning (e.g. "belongs to `F` and has parameters at most those of the original instance"), then all
nodes are pruned at the end of the list. -/
lemma act_runList_eq_none_of_mem {Inv : (V → Option α) → Prop} {G : SimpleGraph V}
    (hInv : ∀ x ŷ, Inv x → Inv (P.prune (res G x) x ŷ)) (hF : ∀ x, Inv x → F.mem (res G x) x)
    {L : List (Stage V α β)} {B : Stage V α β} (hBL : B ∈ L)
    (hB : ∀ x, Inv x → Pb.sol (res G x) x (B.run (res G x) x))
    {z : State V α β} (hz : Inv (act z)) : ∀ v, act (P.runList L G z) v = none := by
  induction L generalizing z with
  | nil => simp at hBL
  | cons B' L ih =>
    rcases List.mem_cons.1 hBL with rfl | hBL
    · have hnone : ∀ v, act (P.step B G z) v = none :=
        P.detect _ _ _ (hF _ hz) (hB _ hz)
      simp only [runList_cons, P.runList_of_act_eq_none hnone]
      exact hnone
    · exact ih hBL (hInv _ _ hz)

/-- Observation 3.4 (for a finite list of stages): if all nodes are pruned at the end of the run,
the committed outputs form a solution. -/
lemma runList_correct {G : SimpleGraph V} {L : List (Stage V α β)} {z : State V α β}
    (hvz : Valid z) (hz : F.mem (res G (act z)) (act z)) (hend : ∀ v, act (P.runList L G z) v = none) :
    ∃ y, Pb.sol (res G (act z)) (act z) y ∧
      ∀ v, (act z v).isSome → (P.runList L G z v).2 = some (y v) := by
  induction L generalizing z with
  | nil =>
    have h0 : act z = fun _ => none := funext hend
    obtain ⟨y, hy⟩ := Pb.empty
    refine ⟨y, ?_, fun v hv => by simp [show act z v = none from hend v] at hv⟩
    rw [h0, res_none]; exact hy
  | cons B L ih =>
    set x := act z
    set H := res G x
    set ŷ := B.run H x
    set x' := P.prune H x ŷ with hx'
    have hact : act (P.step B G z) = x' := rfl
    have hres : res H x' = res G x' := res_res (P.sub H x ŷ)
    have hmem : F.mem (res G x') x' := hres ▸ P.mem H x ŷ hz
    obtain ⟨y', hy', hout⟩ := ih (z := P.step B G z) (P.valid_step hvz) (by rw [hact]; exact hmem)
      hend
    rw [hact] at hy' hout
    refine ⟨fun v => if (x' v).isSome then y' v else ŷ v, P.glue H x ŷ y' hz (hres ▸ hy'), ?_⟩
    intro v hv
    simp only [runList_cons]
    by_cases hv' : (x' v).isSome
    · simp only [hv', ite_true]; exact hout v hv'
    · simp only [hv']
      have hs : (P.step B G z v).2 = some (ŷ v) := by
        simp only [step]
        split_ifs with hc
        · rfl
        · exact absurd ⟨hv, by simpa using hv'⟩ hc
      exact P.runList_snd (P.valid_step hvz) hs

/-! #### The alternating algorithm of a sequence of phases -/

/-- The stages of the first `m` phases. -/
def pre (phases : ℕ → List (Stage V α β)) (m : ℕ) : List (Stage V α β) :=
  (List.range m).flatMap phases

@[simp] lemma pre_zero (phases : ℕ → List (Stage V α β)) : pre phases 0 = [] := rfl

lemma pre_succ (phases : ℕ → List (Stage V α β)) (m : ℕ) :
    pre phases (m + 1) = pre phases m ++ phases m := by
  simp [pre, List.range_succ, List.flatMap_append]

lemma pre_prefix (phases : ℕ → List (Stage V α β)) {m m' : ℕ} (h : m ≤ m') :
    ∃ L, pre phases m' = pre phases m ++ L := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step _ ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L ++ phases _, by rw [pre_succ, hL, List.append_assoc]⟩

/-- The number of complete phases that fit into `t` rounds (at most `t`). -/
def numPhases (phases : ℕ → List (Stage V α β)) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun m => P.dur (pre phases m) ≤ t) t

lemma dur_pre_numPhases_le (phases : ℕ → List (Stage V α β)) (t : ℕ) :
    P.dur (pre phases (P.numPhases phases t)) ≤ t := by
  exact Nat.findGreatest_spec (P := fun m => P.dur (pre phases m) ≤ t) (Nat.zero_le t) (by simp)

lemma numPhases_mono (phases : ℕ → List (Stage V α β)) {t t' : ℕ} (h : t ≤ t') :
    P.numPhases phases t ≤ P.numPhases phases t' := by
  unfold numPhases
  exact Nat.findGreatest_mono (fun m hm => le_trans hm h) h

lemma le_numPhases (phases : ℕ → List (Stage V α β)) {s t : ℕ} (hs : s ≤ t)
    (hd : P.dur (pre phases s) ≤ t) : s ≤ P.numPhases phases t :=
  Nat.le_findGreatest hs hd

/-- The alternating algorithm `π((A_i), P)` (Section 3.3) for the sequence of stages obtained by
concatenating the phases: after `t` rounds, a node outputs its committed output after the complete
phases that fit into `t` rounds. -/
def alg (phases : ℕ → List (Stage V α β)) : Alg V α β where
  out t G x v := (P.runList (pre phases (P.numPhases phases t)) G (init x) v).2
  isLocal t := by
    have h1 := P.runList_isLocal (pre phases (P.numPhases phases t))
    have h2 : IsLocal 0 (fun (_ : SimpleGraph V) (x : V → Option α) => (init x : State V α β)) :=
      isLocal_label 0 (fun a => ((a, none) : Option α × Option β))
    have h3 := (h1.comp h2).mono (by simpa using P.dur_pre_numPhases_le phases t)
    intro G x G' x' v h
    have : P.runList (pre phases (P.numPhases phases t)) G (init x) v =
        P.runList (pre phases (P.numPhases phases t)) G' (init x') v := h3 G x G' x' v h
    show (P.runList _ G (init x) v).2 = (P.runList _ G' (init x') v).2
    rw [this]
  stable {t G x v b} h := by
    obtain ⟨L, hL⟩ := pre_prefix phases (P.numPhases_mono phases (Nat.le_succ t))
    rw [hL, runList_append]
    exact P.runList_snd (P.valid_runList (valid_init x)) h

/-- Observation 3.4 together with the running time of the alternating algorithm: if all nodes of
an instance of `F` are pruned after the first `s` phases, the alternating algorithm solves the
instance within `max s (duration of the first s phases)` rounds. -/
theorem solvesWithin_of_runList_empty {phases : ℕ → List (Stage V α β)} {G : SimpleGraph V}
    {x : V → Option α} (hx : F.mem G x) {s : ℕ}
    (hs : ∀ v, act (P.runList (pre phases s) G (init x)) v = none) :
    (P.alg phases).SolvesWithin Pb G x (max s (P.dur (pre phases s))) := by
  have hres : res G x = G := F.res_eq hx
  have hai : act (init x : State V α β) = x := rfl
  obtain ⟨y, hy, hout⟩ := P.runList_correct (L := pre phases s) (valid_init x)
    (by rw [hai, hres]; exact hx) hs
  rw [hai, hres] at hy
  refine ⟨y, hy, fun v hv => ?_⟩
  have hle := P.le_numPhases phases (le_max_left s _) (le_max_right s _)
  obtain ⟨L, hL⟩ := pre_prefix phases hle
  show (P.runList _ G (init x) v).2 = _
  rw [hL, runList_append, P.runList_of_act_eq_none hs]
  exact hout v (by rw [hai]; exact hv)

end Pruning

end Podc.UniformLocalAlgorithms
