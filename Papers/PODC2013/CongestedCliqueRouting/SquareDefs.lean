import Papers.PODC2013.CongestedCliqueRouting.Primitives

/-!
# The routing algorithm on `s²` nodes (Algorithms 1 and 2 of the paper)

Node set `V ≃ Fin s × Fin s` (groups `W` of size `s = √n`). Every node `v` initially holds the
messages `inp d v` (at most `s²` of them), every node is the destination of at most `s²`
messages. The algorithm takes 15 rounds:

* **Phase A** (Step 2 of Algorithm 1 = Algorithm 2; rounds 0–5).
  Rounds 0–1: group announcement of the counts `c0 v j` (messages of `v` for group `j`)
  (Steps 1 and 3 of Algorithm 2, merged). Round 2: node `(a, j)` broadcasts the total `T a j`
  of messages of group `a` for group `j` (end of Step 1). Locally: König-split `T` into `s` parts
  `Tp x` with row/column sums `≤ s²` (Step 2: the `n` messages from `W` to `W''`), distribute the
  quota of each group among its members (`q`, the "deferred completion" of Step 2), split once
  more inside the group (`Ep`, Step 4). Rounds 3–4: Corollary 3.3 inside the groups (Step 5).
  Round 5: every node sends, for every target group, one message to each of its members (Step 6).
* **Phase B** (Step 3 of Algorithm 1 = Corollary 3.5; rounds 6–9): group announcement of the
  counts per destination group, König split, Corollary 3.3.
* **Phase C** (Step 4 of Algorithm 1; round 10): one message per edge to the destination group.
* **Phase D** (Step 5 of Algorithm 1 = Corollary 3.4; rounds 11–14): group announcement of the
  counts per destination, Corollary 3.3 delivering every message at its destination.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

/-- Parameters of the square algorithm: the grid structure, the destination function of
messages, and the inputs. -/
structure Setup (I V M : Type*) (s : ℕ) where
  e : V ≃ Fin s × Fin s
  dst : M → V
  inp : I → V → Finset M

/-- Number of elements of `H` in class `j`. -/
def cnt {M : Type*} {κ : Type*} [DecidableEq κ] (H : Finset M) (f : M → κ) (j : κ) : ℕ :=
  (H.filter fun m => f m = j).card

namespace Setup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] [Nonempty V] {s : ℕ}
  [NeZero s] (σ : Setup I V M s)

/-- Hypotheses on the instances: at most `s²` messages per node, at most `s²` per destination. -/
structure Good : Prop where
  card_le : ∀ d v, (σ.inp d v).card ≤ s * s
  load_le : ∀ d w, ∑ v, ((σ.inp d v).filter fun m => σ.dst m = w).card ≤ s * s

/-- Destination group of a message. -/
def dg (m : M) : Fin s := grp σ.e (σ.dst m)

/-! ### Phase A -/

/-- Messages of `v` for group `j`. -/
def c0 (d : I) (v : V) (j : Fin s) : ℕ := cnt (σ.inp d v) σ.dg j
/-- The count matrix of group `a`: member `b`, destination group `j`. -/
def C (d : I) (a b j : Fin s) : ℕ := σ.c0 d (node σ.e a b) j
/-- Messages of group `a` for group `j`. -/
def T (d : I) (a j : Fin s) : ℕ := ∑ b, σ.C d a b j
/-- `Tp d x a j`: messages of group `a` for group `j` sent to group `x` (Step 2, König). -/
noncomputable def Tp (d : I) : Fin s → Fin s → Fin s → ℕ := splitParts (Fin s) (σ.T d) (s * s)
/-- `q d a j b x`: messages of member `b` of group `a` for group `j` sent to group `x`. -/
noncomputable def q (d : I) (a j : Fin s) : Fin s → Fin s → ℕ :=
  transportOf (fun b => σ.C d a b j) (fun x => σ.Tp d x a j)
/-- Target group of each message of `v`. -/
noncomputable def xA (d : I) (v : V) : M → Fin s :=
  assign (σ.inp d v) σ.dg fun j x => σ.q d (grp σ.e v) j (mem σ.e v) x
/-- Messages of member `b` of group `a` for target group `x`. -/
noncomputable def E (d : I) (a : Fin s) (b x : Fin s) : ℕ := ∑ j, σ.q d a j b x
/-- `Ep d a y b x`: messages of member `b` with target group `x` moved to member `y` (Step 4). -/
noncomputable def Ep (d : I) (a : Fin s) : Fin s → Fin s → Fin s → ℕ :=
  splitParts (Fin s) (σ.E d a) s
/-- Member of the own group to which each message of `v` is moved. -/
noncomputable def yA (d : I) (v : V) : M → Fin s :=
  assign (σ.inp d v) (σ.xA d v) fun x y => σ.Ep d (grp σ.e v) y (mem σ.e v) x
/-- Messages moved from member `b` to member `y` inside group `a`. -/
noncomputable def R (d : I) (a : Fin s) (b y : Fin s) : ℕ := ∑ x, σ.Ep d a y b x
/-- König split of `R` into matchings, one per intermediate node (Corollary 3.3). -/
noncomputable def Rp (d : I) (a : Fin s) : V → Fin s → Fin s → ℕ := splitParts V (σ.R d a) 1
/-- What `v` sends to intermediate node `c` in round 3. -/
noncomputable def relA (d : I) (v : V) : V → Option (M × ℕ × ℕ) :=
  relayOf (σ.inp d v) (σ.yA d v) (fun m => (σ.xA d v m : ℕ))
    fun y c => σ.Rp d (grp σ.e v) c (mem σ.e v) y

def P0 (d : I) : V → V → Packet M 3 := ga1 σ.e (σ.c0 d)
def P1 (d : I) : V → V → Packet M 3 := ga2 σ.e (σ.P0 d)
def P2 (d : I) : V → V → Packet M 3 := bc σ.e (σ.T d)
noncomputable def P3 (d : I) : V → V → Packet M 3 := fun v c => c33a (σ.relA d v c)
noncomputable def P4 (d : I) : V → V → Packet M 3 := fun c w => c33b σ.e (fun u => σ.P3 d u c) w
/-- (message, target group) pairs held after round 4. -/
noncomputable def TA (d : I) (w : V) : Finset (M × ℕ) := tagged (σ.P4 d) w
noncomputable def P5 (d : I) : V → V → Packet M 3 :=
  fun w z => scatter σ.e (σ.TA d w) Prod.snd Prod.fst z

/-! ### Phase B -/

/-- Messages held after Phase A. -/
noncomputable def HB (d : I) (v : V) : Finset M := rcvd (σ.P5 d) v
noncomputable def c1 (d : I) (v : V) (j : Fin s) : ℕ := cnt (σ.HB d v) σ.dg j
noncomputable def P6 (d : I) : V → V → Packet M 3 := ga1 σ.e (σ.c1 d)
noncomputable def P7 (d : I) : V → V → Packet M 3 := ga2 σ.e (σ.P6 d)
noncomputable def F (d : I) (a b j : Fin s) : ℕ := σ.c1 d (node σ.e a b) j
/-- `Fp d a y b j`: messages for group `j` moved from member `b` to member `y` (Cor. 3.5). -/
noncomputable def Fp (d : I) (a : Fin s) : Fin s → Fin s → Fin s → ℕ :=
  splitParts (Fin s) (σ.F d a) s
noncomputable def yB (d : I) (v : V) : M → Fin s :=
  assign (σ.HB d v) σ.dg fun j y => σ.Fp d (grp σ.e v) y (mem σ.e v) j
noncomputable def R1 (d : I) (a : Fin s) (b y : Fin s) : ℕ := ∑ j, σ.Fp d a y b j
noncomputable def R1p (d : I) (a : Fin s) : V → Fin s → Fin s → ℕ := splitParts V (σ.R1 d a) 1
noncomputable def relB (d : I) (v : V) : V → Option (M × ℕ × ℕ) :=
  relayOf (σ.HB d v) (σ.yB d v) (fun _ => 0) fun y c => σ.R1p d (grp σ.e v) c (mem σ.e v) y
noncomputable def P8 (d : I) : V → V → Packet M 3 := fun v c => c33a (σ.relB d v c)
noncomputable def P9 (d : I) : V → V → Packet M 3 := fun c w => c33b σ.e (fun u => σ.P8 d u c) w

/-! ### Phase C -/

/-- Messages held after Phase B. -/
noncomputable def HC (d : I) (v : V) : Finset M := rcvd (σ.P9 d) v
noncomputable def P10 (d : I) : V → V → Packet M 3 :=
  fun w z => scatter σ.e (σ.HC d w) (fun m => (σ.dg m : ℕ)) id z

/-! ### Phase D -/

/-- Messages held after Phase C. -/
noncomputable def HD (d : I) (v : V) : Finset M := rcvd (σ.P10 d) v
/-- Destination member of a message. -/
def dm (m : M) : Fin s := mem σ.e (σ.dst m)
noncomputable def c3 (d : I) (v : V) (y : Fin s) : ℕ := cnt (σ.HD d v) σ.dm y
noncomputable def P11 (d : I) : V → V → Packet M 3 := ga1 σ.e (σ.c3 d)
noncomputable def P12 (d : I) : V → V → Packet M 3 := ga2 σ.e (σ.P11 d)
noncomputable def G3 (d : I) (a b y : Fin s) : ℕ := σ.c3 d (node σ.e a b) y
noncomputable def G3p (d : I) (a : Fin s) : V → Fin s → Fin s → ℕ := splitParts V (σ.G3 d a) 1
noncomputable def relD (d : I) (v : V) : V → Option (M × ℕ × ℕ) :=
  relayOf (σ.HD d v) σ.dm (fun _ => 0) fun y c => σ.G3p d (grp σ.e v) c (mem σ.e v) y
noncomputable def P13 (d : I) : V → V → Packet M 3 := fun v c => c33a (σ.relD d v c)
noncomputable def P14 (d : I) : V → V → Packet M 3 :=
  fun c w => c33b σ.e (fun u => σ.P13 d u c) w
/-- Messages held at the end. -/
noncomputable def HE (d : I) (v : V) : Finset M := rcvd (σ.P14 d) v

/-- The intended run of the 15-round algorithm. -/
noncomputable def run : Run I V M 3 := fun d t =>
  match t with
  | 0 => σ.P0 d
  | 1 => σ.P1 d
  | 2 => σ.P2 d
  | 3 => σ.P3 d
  | 4 => σ.P4 d
  | 5 => σ.P5 d
  | 6 => σ.P6 d
  | 7 => σ.P7 d
  | 8 => σ.P8 d
  | 9 => σ.P9 d
  | 10 => σ.P10 d
  | 11 => σ.P11 d
  | 12 => σ.P12 d
  | 13 => σ.P13 d
  | 14 => σ.P14 d
  | _ => fun _ _ => pkt0

end Setup

end CongestedCliqueRouting
