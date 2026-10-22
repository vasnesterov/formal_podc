import Mathlib

/-!
# The networks of Theorem 3.3 (Figure 1)

Newport, *Consensus with an abstract MAC layer*, PODC 2014, Section 3.2.

The lower bound of Theorem 3.3 (no consensus without knowledge of the network size, for every
diameter `D` and size) needs, for every even `D ≥ 4` and many sizes `n`, two connected networks
`A` and `B` of the same size `n` and the same diameter `D` such that `A` contains two copies of a
gadget joined through a bridge node `q`, and `B` *covers* each copy: the projection `p b` maps the
neighbours of each node of `B` bijectively onto the neighbours (other than `q`) of its image.

The paper's own network (Figure 1) does not have the claimed diameter (`claim_3_4_false_D4`
below), so we use a different gadget `Γ`:

* nodes `c, t, s, r, u`, pads `pad j` (`j ≤ m`) and path nodes `y 0, …, y (L-1)`;
* edges `c – t, s, r, u, pad j`; `t – s`; `u – r`; `r – s`; `pad j – u`; `t – y 0`; `y i – y (i+1)`.

`B` is the 3-fold voltage cover of `Γ` (voltage `1` on `u → r` and `r → s`), `A` is two copies of
`Γ` joined by `q` at `c`, plus a star of `|Γ| - 1` leaves at `q`. Both have diameter `2L + 4`.

* `Nets`: the structure the proof of Theorem 3.3 needs.
* `exists_nets`: such networks exist for every `D = 2d + 2 ≥ 4` and `n = 3 (m + d + 5)`.
* `claim_3_4_false_D4`: the paper's network `A` for `D = 4` (15 nodes) has diameter `6`.
-/

namespace Podc.AbstractMACConsensus

/-- The two networks of Theorem 3.3 (Figure 1): `A` contains two copies `p false`, `p true`
of a gadget joined through a bridge node `q`; `B` covers each copy (`cover`). -/
structure Nets (D n : ℕ) where
  VA : Type
  VB : Type
  [fA : Fintype VA] [dA : DecidableEq VA] [fB : Fintype VB] [dB : DecidableEq VB]
  GA : SimpleGraph VA
  GB : SimpleGraph VB
  [rA : DecidableRel GA.Adj] [rB : DecidableRel GB.Adj]
  cardA : Fintype.card VA = n
  cardB : Fintype.card VB = n
  connA : GA.Connected
  connB : GB.Connected
  diamA : GA.diam = D
  diamB : GB.diam = D
  q : VA
  p : Bool → VB → VA
  p_ne_q : ∀ b v, p b v ≠ q
  p_disj : ∀ v v', p false v ≠ p true v'
  cover : ∀ b v', (Finset.univ.filter fun u => GA.Adj u (p b v') ∧ u ≠ q).val =
    (Finset.univ.filter fun u' => GB.Adj u' v').val.map (p b)

namespace NetsConstr

open SimpleGraph

/-! ### Walk-length bounds and diameters -/

/-- `x` and `y` are joined by a walk of length at most `k`. -/
def WithinN {V : Type*} (G : SimpleGraph V) (k : ℕ) (x y : V) : Prop :=
  ∃ p : G.Walk x y, p.length ≤ k

namespace WithinN

variable {V : Type*} {G : SimpleGraph V} {k l : ℕ} {x y z : V}

lemma refl (x : V) (k : ℕ) : WithinN G k x x := ⟨.nil, Nat.zero_le _⟩

lemma adj (h : G.Adj x y) : WithinN G 1 x y := ⟨.cons h .nil, le_rfl⟩

lemma mono (h : WithinN G k x y) (hkl : k ≤ l) : WithinN G l x y :=
  let ⟨p, hp⟩ := h; ⟨p, hp.trans hkl⟩

lemma trans (h1 : WithinN G k x y) (h2 : WithinN G l y z) : WithinN G (k + l) x z := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  exact ⟨p.append q, by rw [Walk.length_append]; omega⟩

lemma symm (h : WithinN G k x y) : WithinN G k y x :=
  let ⟨p, hp⟩ := h; ⟨p.reverse, by simpa using hp⟩

end WithinN

/-- A path `t – f 0 – f 1 – ⋯` hanging below `t`. -/
lemma within_path {V : Type*} {G : SimpleGraph V} {L : ℕ} (t : V) (f : Fin L → V)
    (h0 : ∀ h : 0 < L, G.Adj t (f ⟨0, h⟩))
    (hs : ∀ n (h : n + 1 < L), G.Adj (f ⟨n, by omega⟩) (f ⟨n + 1, h⟩)) :
    ∀ i : Fin L, WithinN G (i.val + 1) t (f i) := by
  rintro ⟨n, hn⟩
  induction n with
  | zero => exact WithinN.adj (h0 hn)
  | succ n ih => exact (ih (by omega)).trans (WithinN.adj (hs n hn))

/-- A function that grows by at most one along edges grows by at most the length along walks. -/
lemma le_of_walk {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) {x y : V} (p : G.Walk x y) :
    f y ≤ f x + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := hf _ _ h
    simp only [Walk.length_cons]
    push_cast
    omega

/-- Diameter from an upper bound by walks and a lower bound by a `1`-Lipschitz function. -/
theorem diam_eq_of {V : Type*} (G : SimpleGraph V) (D : ℕ) (hup : ∀ x y, WithinN G D x y)
    (f : V → ℤ) (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) (x₀ y₀ : V) (h : f y₀ = f x₀ + D) :
    G.Connected ∧ G.diam = D := by
  have hconn : G.Connected := by
    have : Nonempty V := ⟨x₀⟩
    rw [connected_iff]
    exact ⟨fun x y => let ⟨p, _⟩ := hup x y; p.reachable, ⟨x₀⟩⟩
  refine ⟨hconn, ?_⟩
  have he : G.ediam = D := by
    apply le_antisymm
    · rw [ediam_le_iff]
      intro u v
      obtain ⟨p, hp⟩ := hup u v
      exact p.edist_le.trans (by exact_mod_cast hp)
    · obtain ⟨p, hp⟩ := (hconn x₀ y₀).exists_walk_length_eq_edist
      have := le_of_walk f hf p
      refine le_trans ?_ (hp ▸ edist_le_ediam)
      exact_mod_cast (by omega : D ≤ p.length)
  rw [diam, he]
  rfl

/-! ### The gadget `Γ` -/

/-- Nodes of the gadget `Γ`. -/
inductive GV (m L : ℕ)
  | c | t | s | r | u
  | pad (j : Fin (m + 1))
  | y (i : Fin L)
  deriving DecidableEq, Fintype

namespace GV

variable {m L : ℕ}

/-- Adjacency of `Γ`. -/
def adjB : GV m L → GV m L → Bool
  | c, t | c, s | c, r | c, u | c, pad _ => true
  | t, c | s, c | r, c | u, c | pad _, c => true
  | t, s | s, t | u, r | r, u | r, s | s, r => true
  | pad _, u | u, pad _ => true
  | t, y i | y i, t => i.val == 0
  | y i, y j => i.val + 1 == j.val || j.val + 1 == i.val
  | _, _ => false

/-- Voltages of the covering `B → Γ`. -/
def volt : GV m L → GV m L → ZMod 3
  | u, r => 1
  | r, u => 2
  | r, s => 1
  | s, r => 2
  | _, _ => 0

/-- Distance from `c` in `Γ`. -/
def depth : GV m L → ℕ
  | c => 0
  | y i => i.val + 2
  | _ => 1

/-- Path nodes. -/
def isPath : GV m L → Bool
  | y _ => true
  | _ => false

/-- The node of `Γ` farthest from `c` (depth `L + 1`). -/
def far : (L : ℕ) → GV m L
  | 0 => t
  | n + 1 => y (Fin.last n)

lemma adjB_symm (x x' : GV m L) : adjB x x' = adjB x' x := by
  cases x <;> cases x' <;> simp [adjB, Bool.or_comm]

lemma adjB_irrefl (x : GV m L) : adjB x x = false := by
  cases x <;> simp [adjB]

lemma volt_symm (x x' : GV m L) : volt x' x = - volt x x' := by
  cases x <;> cases x' <;> simp [volt] <;> decide

lemma depth_lip {x x' : GV m L} (h : adjB x x' = true) :
    (depth x' : ℤ) ≤ depth x + 1 ∧ (depth x : ℤ) ≤ depth x' + 1 := by
  cases x <;> cases x' <;> simp [adjB, depth] at h ⊢ <;> omega

lemma depth_le (x : GV m L) : depth x ≤ L + 1 := by
  cases x <;> simp [depth]

lemma depth_far : depth (far (m := m) L) = L + 1 := by
  cases L <;> simp [far, depth]

/-- `Γ` has `m + L + 6` nodes. -/
def equivSum : GV m L ≃ (Fin 5 ⊕ Fin (m + 1)) ⊕ Fin L where
  toFun
    | c => .inl (.inl 0)
    | t => .inl (.inl 1)
    | s => .inl (.inl 2)
    | r => .inl (.inl 3)
    | u => .inl (.inl 4)
    | pad j => .inl (.inr j)
    | y i => .inr i
  invFun
    | .inl (.inl k) => ![c, t, s, r, u] k
    | .inl (.inr j) => pad j
    | .inr i => y i
  left_inv x := by cases x <;> rfl
  right_inv := by
    rintro ((k | j) | i)
    · fin_cases k <;> rfl
    · rfl
    · rfl

lemma card : Fintype.card (GV m L) = m + L + 6 := by
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end GV

open GV

/-! ### Network `A` -/

/-- Nodes of `A`: two copies of `Γ`, the bridge `q = inr none` and the star leaves `inr (some k)`. -/
abbrev AV (m L : ℕ) := (Bool × GV m L) ⊕ Option (Fin (m + L + 5))

variable {m L : ℕ}

/-- Adjacency of `A`. -/
def adjA : AV m L → AV m L → Bool
  | .inl (b, x), .inl (b', x') => b == b' && adjB x x'
  | .inl (_, .c), .inr none => true
  | .inr none, .inl (_, .c) => true
  | .inr none, .inr (some _) => true
  | .inr (some _), .inr none => true
  | _, _ => false

lemma adjA_symm (x x' : AV m L) : adjA x x' = adjA x' x := by
  rcases x with ⟨b, x⟩ | _ | k <;> rcases x' with ⟨b', x'⟩ | _ | k' <;>
    (try cases x) <;> (try cases x') <;> simp [adjA, adjB_symm, Bool.beq_comm]

lemma adjA_irrefl (x : AV m L) : adjA x x = false := by
  rcases x with ⟨b, x⟩ | _ | k <;> simp [adjA, adjB_irrefl]

/-- The network `A`. -/
def GA (m L : ℕ) : SimpleGraph (AV m L) where
  Adj x x' := adjA x x' = true
  symm := ⟨fun x x' h => by rwa [adjA_symm]⟩
  loopless := ⟨fun x h => by simp [adjA_irrefl] at h⟩

instance : DecidableRel (GA m L).Adj := fun x x' =>
  inferInstanceAs (Decidable (adjA x x' = true))

/-- Depth in `A`, signed by the copy. -/
def fA : AV m L → ℤ
  | .inl (false, x) => -(depth x + 1)
  | .inl (true, x) => depth x + 1
  | .inr _ => 0

lemma fA_lip (x x' : AV m L) (h : (GA m L).Adj x x') : fA x' ≤ fA x + 1 := by
  change adjA x x' = true at h
  rcases x with ⟨b, x⟩ | _ | k <;> rcases x' with ⟨b', x'⟩ | _ | k'
  · simp only [adjA, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    have := depth_lip h
    cases b <;> simp [fA] <;> omega
  all_goals (try cases x) <;> (try cases x') <;> (try cases b) <;> (try cases b') <;>
    simp_all [adjA, fA, depth]

lemma within_q (x : AV m L) : WithinN (GA m L) (L + 2) (.inr none) x := by
  rcases x with ⟨b, x⟩ | _ | k
  · have h1 : WithinN (GA m L) 1 (.inr none) (.inl (b, .c)) := WithinN.adj rfl
    have h2 : WithinN (GA m L) (depth x) (.inl (b, .c)) (.inl (b, x)) := by
      cases x with
      | c => exact WithinN.refl _ _
      | y i =>
        have hp := within_path (G := GA m L) (.inl (b, .t)) (fun i => .inl (b, .y i))
          (fun _ => by simp [GA, adjA, adjB]) (fun n _ => by simp [GA, adjA, adjB]) i
        exact (WithinN.adj (by simp [GA, adjA, adjB])).trans hp |>.mono (by simp [depth]; omega)
      | _ => exact WithinN.adj (by simp [GA, adjA, adjB])
    exact (h1.trans h2).mono (by have := depth_le x; omega)
  · exact WithinN.refl _ _
  · exact (WithinN.adj rfl).mono (by omega)

lemma diam_A : (GA m L).Connected ∧ (GA m L).diam = 2 * (L + 1) + 2 := by
  refine diam_eq_of _ _ (fun x x' => ((within_q x).symm.trans (within_q x')).mono (by omega))
    fA fA_lip (.inl (false, far L)) (.inl (true, far L)) ?_
  simp only [fA, depth_far]
  push_cast
  ring

/-! ### Network `B` -/

/-- Nodes of `B`: three layers of `Γ`. -/
abbrev BV (m L : ℕ) := ZMod 3 × GV m L

/-- Adjacency of `B` (the voltage cover). -/
def adjBB (x x' : BV m L) : Bool := adjB x.2 x'.2 && decide (x'.1 = x.1 + volt x.2 x'.2)

lemma adjBB_symm (x x' : BV m L) : adjBB x x' = adjBB x' x := by
  unfold adjBB
  rw [adjB_symm, volt_symm x'.2 x.2]
  congr 2
  apply propext
  constructor <;> intro h <;> rw [h] <;> ring

/-- The network `B`. -/
def GB (m L : ℕ) : SimpleGraph (BV m L) where
  Adj x x' := adjBB x x' = true
  symm := ⟨fun x x' h => by rwa [adjBB_symm]⟩
  loopless := ⟨fun x h => by simp [adjBB, adjB_irrefl] at h⟩

instance : DecidableRel (GB m L).Adj := fun x x' =>
  inferInstanceAs (Decidable (adjBB x x' = true))

/-- A walk certificate: `x – l₀ – ⋯ – lₖ – x'` is a walk in `B`. -/
def chainB : BV m L → List (BV m L) → BV m L → Bool
  | x, [], x' => adjBB x x'
  | x, z :: l, x' => adjBB x z && chainB z l x'

lemma chainB_within : ∀ (x : BV m L) (l : List (BV m L)) (x' : BV m L),
    chainB x l x' = true → WithinN (GB m L) (l.length + 1) x x'
  | x, [], x', h => WithinN.adj h
  | x, z :: l, x', h => by
    simp only [chainB, Bool.and_eq_true] at h
    have := (WithinN.adj (G := GB m L) h.1).trans (chainB_within z l x' h.2)
    exact this.mono (by simp; omega)

/-- Short walks from layer `i` to layer `i + 1` between non-path nodes (found by BFS). -/
def cert (i : ZMod 3) (x x' : GV m L) : List (BV m L) :=
  (match x, x' with
    | c, c => [(0, r), (1, s)]
    | c, t => [(0, r), (1, s)]
    | c, s => [(0, r)]
    | c, r => [(0, u)]
    | c, u => [(0, s), (2, r)]
    | c, pad _ => [(0, r), (1, s), (1, c)]
    | t, c => [(0, c), (0, r), (1, s)]
    | t, t => [(0, c), (0, r), (1, s)]
    | t, s => [(0, c), (0, r)]
    | t, r => [(0, c), (0, u)]
    | t, u => [(0, s), (2, r)]
    | t, pad _ => [(0, s), (2, r), (1, u)]
    | s, c => [(2, r), (1, u)]
    | s, t => [(0, c), (0, r), (1, s)]
    | s, s => [(0, c), (0, r)]
    | s, r => [(0, c), (0, u)]
    | s, u => [(2, r)]
    | s, pad _ => [(2, r), (1, u)]
    | r, c => [(1, s)]
    | r, t => [(1, s)]
    | r, s => []
    | r, r => [(0, c), (0, u)]
    | r, u => [(1, s), (1, c)]
    | r, pad _ => [(1, s), (1, c)]
    | u, c => [(1, r)]
    | u, t => [(1, r), (1, c)]
    | u, s => [(0, c), (0, r)]
    | u, r => []
    | u, u => [(1, r), (1, c)]
    | u, pad _ => [(1, r), (1, c)]
    | pad _, c => [(0, u), (1, r)]
    | pad _, t => [(0, c), (0, r), (1, s)]
    | pad _, s => [(0, c), (0, r)]
    | pad _, r => [(0, u)]
    | pad _, u => [(0, c), (0, s), (2, r)]
    | pad _, pad _ => [(0, u), (1, r), (1, c)]
    | _, _ => [] : List (BV m L)).map fun z => (i + z.1, z.2)

lemma cert_length (i : ZMod 3) (x x' : GV m L) : (cert i x x').length ≤ 3 := by
  cases x <;> cases x' <;> simp [cert]

lemma cert_ok (i : ZMod 3) (x x' : GV m L) (hx : isPath x = false) (hx' : isPath x' = false) :
    chainB (i, x) (cert i x x') (i + 1, x') = true := by
  fin_cases i <;> cases x <;> cases x' <;> first | rfl | simp [isPath] at hx hx'

lemma within_next (i : ZMod 3) (x x' : GV m L) (hx : isPath x = false)
    (hx' : isPath x' = false) : WithinN (GB m L) 4 (i, x) (i + 1, x') :=
  (chainB_within _ _ _ (cert_ok i x x' hx hx')).mono (by have := cert_length i x x'; omega)

lemma within_c (i : ZMod 3) (x : GV m L) (hx : isPath x = false) :
    WithinN (GB m L) 1 (i, x) (i, c) := by
  cases x with
  | c => exact WithinN.refl _ _
  | y _ => simp [isPath] at hx
  | _ => exact WithinN.adj (by simp [GB, adjBB, adjB, volt])

lemma within_core (x x' : BV m L) (hx : isPath x.2 = false) (hx' : isPath x'.2 = false) :
    WithinN (GB m L) 4 x x' := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, x'⟩ := x'
  have hij : j = i ∨ j = i + 1 ∨ i = j + 1 := by
    have key : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ i = j + 1 := by decide
    exact key i j
  rcases hij with rfl | rfl | rfl
  · exact ((within_c j x hx).trans (within_c j x' hx').symm).mono (by omega)
  · exact within_next i x x' hx hx'
  · exact (within_next j x' x hx' hx).symm

/-- The non-path node above a node of `Γ`. -/
def toCore : GV m L → GV m L
  | y _ => t
  | x => x

/-- Depth below `t` of a path node. -/
def pdepth : GV m L → ℕ
  | y i => i.val + 1
  | _ => 0

lemma within_toCore (i : ZMod 3) (x : GV m L) :
    WithinN (GB m L) (pdepth x) (i, x) (i, toCore x) := by
  cases x with
  | y a =>
    exact (within_path (G := GB m L) (i, .t) (fun a => (i, .y a))
      (fun _ => by simp [GB, adjBB, adjB, volt]) (fun n _ => by simp [GB, adjBB, adjB, volt])
      a).symm
  | _ => exact WithinN.refl _ _

lemma isPath_toCore (x : GV m L) : isPath (toCore x) = false := by
  cases x <;> rfl

lemma pdepth_le (x : GV m L) : pdepth x ≤ L := by
  cases x <;> simp [pdepth]

/-- Core part of the lower-bound function: BFS distance from `(0, t)` in the core of `B`. -/
def hcore (i : ZMod 3) : GV m L → ℤ
  | c => ![1, 4, 3] (show Fin 3 from i)
  | t => ![0, 4, 4] (show Fin 3 from i)
  | s => ![1, 3, 4] (show Fin 3 from i)
  | r => ![2, 3, 2] (show Fin 3 from i)
  | u => ![2, 3, 3] (show Fin 3 from i)
  | pad _ => ![2, 4, 4] (show Fin 3 from i)
  | y _ => 0

/-- The lower-bound function on `B`. -/
def fB (x : BV m L) : ℤ :=
  match x.2 with
  | y a => if x.1 = 0 then -(a.val + 1 : ℤ) else 4 + (a.val + 1)
  | z => hcore x.1 z

lemma fB_y (i : ZMod 3) (a : Fin L) :
    fB (i, (y a : GV m L)) = if i = 0 then -(a.val + 1 : ℤ) else 4 + (a.val + 1) := rfl

lemma fB_lip (x x' : BV m L) (h : (GB m L).Adj x x') : fB x' ≤ fB x + 1 := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, x'⟩ := x'
  change adjBB _ _ = true at h
  simp only [adjBB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h, rfl⟩ := h
  have ht : fB (i, (t : GV m L)) = if i = 0 then 0 else 4 := by fin_cases i <;> rfl
  cases x <;> cases x' <;>
    first
    | (simp [adjB] at h; done)
    | (simp only [volt, add_zero, fB_y, ht]; simp [adjB] at h; split_ifs <;> omega)
    | (fin_cases i <;> exact of_decide_eq_true rfl)

lemma diam_B : (GB m L).Connected ∧ (GB m L).diam = 2 * (L + 1) + 2 := by
  refine diam_eq_of _ _ (fun x x' => ?_) fB fB_lip (0, far L) (1, far L) ?_
  · obtain ⟨i, x⟩ := x
    obtain ⟨j, x'⟩ := x'
    have h1 := within_toCore i x
    have h2 := within_toCore j x'
    have h3 := within_core (i, toCore x) (j, toCore x') (isPath_toCore x) (isPath_toCore x')
    exact ((h1.trans h3).trans h2.symm).mono
      (by have := pdepth_le x; have := pdepth_le x'; omega)
  · cases L <;> (simp [far, fB, hcore]; try omega)

/-! ### The covering -/

/-- The projection of `B` onto copy `b` of `A`. -/
def pr (b : Bool) (x : BV m L) : AV m L := .inl (b, x.2)

lemma cover (b : Bool) (x : BV m L) :
    (Finset.univ.filter fun w => (GA m L).Adj w (pr b x) ∧ w ≠ .inr none).val =
      (Finset.univ.filter fun w => (GB m L).Adj w x).val.map (pr b) := by
  obtain ⟨i, x⟩ := x
  refine (Multiset.Nodup.ext (Finset.nodup _) (Multiset.Nodup.map_on ?_ (Finset.nodup _))).2 ?_
  · rintro ⟨j, z⟩ hz ⟨j', z'⟩ hz' he
    simp only [pr, Sum.inl.injEq, Prod.mk.injEq, true_and] at he
    subst he
    simp [GB, adjBB] at hz hz'
    have : j = j' := by linear_combination hz'.2 - hz.2
    rw [this]
  · intro w
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_map]
    rcases w with ⟨b', z⟩ | _ | k
    · simp [GA, GB, pr, adjA, adjBB]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h2, i - z.volt x, by ring⟩, h1.symm⟩,
        fun ⟨⟨h2, _⟩, h1⟩ => ⟨h1.symm, h2⟩⟩
    · simp [pr]
    · simp [GA, pr, adjA]


/-! ### The paper's network for `D = 4` -/

/-- Nodes of the paper's network `A` for `D = 4` (`d = 1`, `k = 0`): two copies of the gadget
`c = 0, a₁ = 1, a₂⁺ = 2, a₃⁺ = 3, a₄⁺ = 4`, the bridge `q = inr none` and the clique `C`. -/
abbrev PV := (Bool × Fin 5) ⊕ Option (Fin 4)

/-- The gadget of Figure 1 for `d = 1`, `k = 0`: edges `c – a₁ – a₂⁺ – a₃⁺ – a₄⁺`, `c – a₃⁺`,
`c – a₄⁺`. -/
def paperGadget (x x' : Fin 5) : Bool :=
  decide ((x.val, x'.val) ∈ [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3),
    (0, 3), (3, 0), (0, 4), (4, 0)])

/-- Adjacency of the paper's network `A` for `D = 4`. -/
def paperAdj : PV → PV → Bool
  | .inl (b, x), .inl (b', x') => b == b' && paperGadget x x'
  | .inl (_, x), .inr none => x == 0
  | .inr none, .inl (_, x) => x == 0
  | .inr none, .inr (some _) => true
  | .inr (some _), .inr none => true
  | .inr (some k), .inr (some k') => k != k'
  | _, _ => false

/-- The paper's network `A` for `D = 4` (15 nodes). -/
def paperA : SimpleGraph PV where
  Adj x x' := paperAdj x x' = true
  symm := ⟨fun x x' h => by
    have key : ∀ x x' : PV, paperAdj x x' = paperAdj x' x := by decide
    rwa [key]⟩
  loopless := ⟨fun x h => by
    have key : ∀ x : PV, paperAdj x x = false := by decide
    simp [key] at h⟩

/-- Signed depth in the paper's network. -/
def fP : PV → ℤ
  | .inl (false, x) => -(![0, 1, 2, 1, 1] x + 1)
  | .inl (true, x) => ![0, 1, 2, 1, 1] x + 1
  | .inr _ => 0

lemma fP_lip : ∀ x x' : PV, paperA.Adj x x' → fP x' ≤ fP x + 1 := by
  have key : ∀ x x' : PV, paperAdj x x' = true → fP x' ≤ fP x + 1 := by decide
  exact key

lemma paperA_q (v : PV) : WithinN paperA 3 (.inr none) v := by
  have h0 : ∀ b, WithinN paperA 1 (.inr none) (.inl (b, 0)) := fun b =>
    WithinN.adj (by cases b <;> rfl)
  have h1 : ∀ b (x : Fin 5), paperGadget 0 x = true → WithinN paperA 2 (.inr none) (.inl (b, x)) :=
    fun b x hx => (h0 b).trans (WithinN.adj (by simp [paperA, paperAdj, hx]))
  rcases v with ⟨b, x⟩ | _ | k
  · fin_cases x
    · exact (h0 b).mono (by omega)
    · exact (h1 b 1 rfl).mono (by omega)
    · exact (h1 b 1 rfl).trans (WithinN.adj (by cases b <;> rfl))
    · exact (h1 b 3 rfl).mono (by omega)
    · exact (h1 b 4 rfl).mono (by omega)
  · exact WithinN.refl _ _
  · exact (WithinN.adj (by simp [paperA, paperAdj])).mono (by omega)

end NetsConstr

open NetsConstr in
/-- Claim 3.4 of the paper fails for `D = 4`: the paper's network `A` (Figure 1, `d = 1`,
`k = 0`, 15 nodes) is connected but has diameter `6`, not `4`. -/
theorem claim_3_4_false_D4 :
    Fintype.card PV = 15 ∧ paperA.Connected ∧ paperA.diam = 6 := by
  refine ⟨rfl, diam_eq_of paperA 6
    (fun x x' => ((paperA_q x).symm.trans (paperA_q x')).mono (by omega))
    fP fP_lip (.inl (false, 2)) (.inl (true, 2)) (by decide)⟩

open NetsConstr in
/-- The networks needed by Theorem 3.3 exist for every even diameter `D = 2d + 2 ≥ 4` and every
size `n = 3 (m + d + 5)`. -/
theorem exists_nets (d m : ℕ) (hd : 1 ≤ d) : Nonempty (Nets (2 * d + 2) (3 * (m + d + 5))) := by
  obtain ⟨L, rfl⟩ : ∃ L, d = L + 1 := ⟨d - 1, by omega⟩
  exact ⟨{
    VA := AV m L
    VB := BV m L
    GA := GA m L
    GB := GB m L
    cardA := by simp [GV.card]; ring
    cardB := by simp [GV.card]; ring
    connA := diam_A.1
    connB := diam_B.1
    diamA := diam_A.2
    diamB := diam_B.2
    q := .inr none
    p := pr
    p_ne_q := by simp [pr]
    p_disj := by simp [pr]
    cover := cover }⟩

end Podc.AbstractMACConsensus
