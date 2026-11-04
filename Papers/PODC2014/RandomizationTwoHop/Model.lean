import Papers.PODC2014.RandomizationTwoHop.ColorPorts

-- CSLib candidate (paper-local for now; see README)

/-!
# Randomized anonymous algorithms, problems, GRAN

§1.1 of the paper.

* `RAlg I O`: a randomized anonymous algorithm in the port-numbering model (CSLib's `PNGraph`,
  ports `0, …, deg - 1`, messages may depend on the port, the receiver learns the port at the
  sender's end). Initially a node knows its degree and its input; in round `t + 1` it sends a
  message to every port, receives one from every port, gets **one random bit** `β v t` and moves
  to a new state. `out : State → Option O`; outputs are **irrevocable**: the output of a node is
  the first `some` it produces (`decided`). `IsDeterministic`: `recv` ignores the random bit.
* `Problem In Out`: a set of input instances (labelled graphs) and, for each, the valid output
  labellings.
* `Solves A Π` (Las Vegas): on every instance and every simple port numbering of it,
  (termination) every finite prefix of random bits can be extended to an assignment under which
  all nodes output, and (validity) whenever all nodes have output, the output labelling is valid.
  See `Measure.lean` for the equivalence of validity with "every output labelling obtained with
  positive probability is valid" and the implication "termination with probability 1 ⇒
  termination as above".
* `decision Y`: the decision problem `Δ_Y`; `GRAN`; `colored Π`: the 2-hop coloured variant `Πᶜ`.

The *locality lemma* `decided_local`: with the colour-sorted port numbering, the state of a node
after `t` rounds is determined by its view of tree depth `t + 1` (i.e. `L_{t+2}`) labelled with
inputs, colours and the first `t` random bits. (One more level than rounds, because the port
number at the far end of an edge depends on the colours around the far end.) Coverings preserve
runs (`decided_of_localIso`).
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph Cslib.PortNumbering

/-- A randomized anonymous synchronous algorithm in the port-numbering model with one random bit
per round and irrevocable outputs. -/
structure RAlg (I O : Type) where
  /-- Local states. -/
  State : Type
  /-- Messages. -/
  Msg : Type
  /-- Initial state from the degree and the local input. -/
  init : ℕ → I → State
  /-- The message sent to port `i`. -/
  send : State → ℕ → Msg
  /-- Transition: current state, the random bit of this round, the received messages (indexed by
  own port numbers, `none` for non-existing ports). -/
  recv : State → Bool → (ℕ → Option Msg) → State
  /-- Output (`none`: no output yet). -/
  out : State → Option O

namespace RAlg

variable {I O : Type} {V : Type} (A : RAlg I O)

/-- The algorithm does not access its random bits. -/
def IsDeterministic : Prop := ∀ s b b' m, A.recv s b m = A.recv s b' m

/-- The messages received by `v` when the nodes are in states `s`. -/
def inbox (P : PNGraph V) (s : V → A.State) (v : V) : ℕ → Option A.Msg :=
  fun i => if i < P.deg v then some (A.send (s (P.nbr v i)) (P.rport v i)) else none

/-- States after `t` rounds on the port-numbered graph `P` with inputs `x` and random bits `β`
(`β v t` is the bit of node `v` in round `t + 1`). -/
def state (P : PNGraph V) (x : V → I) (β : V → ℕ → Bool) : ℕ → V → A.State
  | 0 => fun v => A.init (P.deg v) (x v)
  | t + 1 => fun v => A.recv (state P x β t v) (β v t) (A.inbox P (state P x β t) v)

/-- The irrevocable output of `v` within the first `t` rounds (the first output produced). -/
def decided (P : PNGraph V) (x : V → I) (β : V → ℕ → Bool) : ℕ → V → Option O
  | 0 => fun v => A.out (A.state P x β 0 v)
  | t + 1 => fun v => (decided P x β t v).or (A.out (A.state P x β (t + 1) v))

variable {A} {P : PNGraph V} {x : V → I} {β : V → ℕ → Bool}

theorem decided_succ_of_isSome {t : ℕ} {v : V} (h : (A.decided P x β t v).isSome) :
    A.decided P x β (t + 1) v = A.decided P x β t v := by
  simp only [decided]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
  rw [ho]; rfl

theorem decided_mono {t t' : ℕ} (htt : t ≤ t') {v : V} (h : (A.decided P x β t v).isSome) :
    A.decided P x β t' v = A.decided P x β t v := by
  induction htt with
  | refl => rfl
  | step _ ih =>
    rw [decided_succ_of_isSome (by rw [ih]; exact h), ih]

theorem decided_eq_some_mono {t t' : ℕ} (htt : t ≤ t') {v : V} {o : O}
    (h : A.decided P x β t v = some o) : A.decided P x β t' v = some o := by
  rw [decided_mono htt (by simp [h]), h]

/-- Causality: the first `t` rounds only use the first `t` random bits. -/
theorem state_congr_bits {β' : V → ℕ → Bool} {t : ℕ} (h : ∀ v k, k < t → β v k = β' v k) :
    A.state P x β t = A.state P x β' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih (fun v k hk => h v k (by omega))
    funext v
    simp only [state, ih, h v t (by omega)]

theorem decided_congr_bits {β' : V → ℕ → Bool} {t : ℕ} (h : ∀ v k, k < t → β v k = β' v k) :
    A.decided P x β t = A.decided P x β' t := by
  induction t with
  | zero => funext v; rfl
  | succ t ih =>
    have ih := ih (fun v k hk => h v k (by omega))
    funext v
    simp only [decided, ih, state_congr_bits h]

theorem decided_det (hA : A.IsDeterministic) (β' : V → ℕ → Bool) (t : ℕ) :
    A.decided P x β t = A.decided P x β' t := by
  have : ∀ t, A.state P x β t = A.state P x β' t := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => funext v; simp only [state, ih]; exact hA _ _ _ _
  induction t with
  | zero => funext v; simp only [decided, this]
  | succ t ih => funext v; simp only [decided, ih, this]

end RAlg

/-- Random bits from a finite bitstring (padded with `false`). -/
def bitsOf (l : List Bool) : ℕ → Bool := fun k => l.getD k false

/-! ### Locality of runs with colour-sorted ports -/

section Locality

variable {I O C : Type} [LinearOrder C] (A : RAlg I O)
variable {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
  {cG : V → C} {cH : W → C} {xG : V → I} {xH : W → I} {βG : V → ℕ → Bool} {βH : W → ℕ → Bool}

/-- The labels relevant for the first `t` rounds: input, colour, first `t` random bits. -/
def runLab (x : V → I) (c : V → C) (β : V → ℕ → Bool) (t : ℕ) (v : V) : I × C × List Bool :=
  (x v, c v, List.ofFn fun k : Fin t => β v k)

omit [LinearOrder C] [Finite V] [Finite W] in
theorem runLab_eq_of_le {s t : ℕ} (hst : s ≤ t) {u : V} {v : W}
    (h : runLab xG cG βG t u = runLab xH cH βH t v) :
    runLab xG cG βG s u = runLab xH cH βH s v := by
  simp only [runLab, Prod.mk.injEq] at h ⊢
  refine ⟨h.1, h.2.1, ?_⟩
  have h3 := List.ofFn_inj.1 h.2.2
  rw [List.ofFn_inj]; funext k
  exact congrFun h3 ⟨k, by omega⟩

omit [LinearOrder C] [Finite V] [Finite W] in
theorem bit_eq_of_runLab {t : ℕ} {u : V} {v : W}
    (h : runLab xG cG βG (t + 1) u = runLab xH cH βH (t + 1) v) : βG u t = βH v t := by
  simp only [runLab, Prod.mk.injEq] at h
  exact congrFun (List.ofFn_inj.1 h.2.2) ⟨t, by omega⟩

theorem teq_runLab_le {s t k : ℕ} (hst : s ≤ t) {u : V} {v : W}
    (h : TEq G (runLab xG cG βG t) H (runLab xH cH βH t) k u v) :
    TEq G (runLab xG cG βG s) H (runLab xH cH βH s) k u v :=
  h.map_lab fun _ _ => runLab_eq_of_le hst

/-- **Locality.** With colour-sorted ports, equal views of tree depth `t + 1` (labelled with
inputs, colours and the first `t` random bits) give equal states after `t` rounds. -/
theorem state_local (hG : NbhdInj G cG) (hH : NbhdInj H cH) (t : ℕ) (u : V) (v : W)
    (h : TEq G (runLab xG cG βG t) H (runLab xH cH βH t) (t + 1) u v) :
    A.state (colorPN G cG) xG βG t u = A.state (colorPN H cH) xH βH t v := by
  induction t generalizing u v with
  | zero =>
    obtain ⟨hl, e, -⟩ := h
    simp only [runLab, Prod.mk.injEq] at hl
    simp only [RAlg.state, colorPN_deg hG, colorPN_deg hH, cdeg_eq_of_equiv e, hl.1]
  | succ t ih =>
    have hlow : ∀ {a : V} {b : W} {k : ℕ},
        TEq G (runLab xG cG βG (t + 1)) H (runLab xH cH βH (t + 1)) k a b →
        TEq G (runLab xG cG βG t) H (runLab xH cH βH t) k a b := teq_runLab_le (by omega)
    obtain ⟨hl, e, he⟩ := h
    have hcol : ∀ w : G.neighborSet u, cH (e w) = cG w := fun w => by
      have := (he w).lab; simp only [runLab, Prod.mk.injEq] at this; exact this.2.1.symm
    have hdeg : cdeg H v = cdeg G u := cdeg_eq_of_equiv e
    simp only [RAlg.state]
    rw [ih u v (hlow (TEq.of_succ ⟨hl, e, he⟩)), bit_eq_of_runLab hl]
    congr 1
    funext i
    simp only [RAlg.inbox, colorPN_deg hG, colorPN_deg hH, hdeg]
    split_ifs with hi
    · have hp := pick_eq_of_equiv hG hH e hcol hi
      rw [colorPN_nbr hG, colorPN_nbr hH, colorPN_rport hG, colorPN_rport hH, hp]
      set w : G.neighborSet u := ⟨pick G cG u i, (pick_spec hG hi).1⟩
      have hw := he w
      rw [ih _ _ (hlow hw)]
      congr 2
      obtain ⟨-, e', he'⟩ := hw
      have hcol' : ∀ z : G.neighborSet w.1, cH (e' z) = cG z := fun z => by
        have := (he' z).lab; simp only [runLab, Prod.mk.injEq] at this; exact this.2.1.symm
      have hcu : cH v = cG u := by
        simp only [runLab, Prod.mk.injEq] at hl; exact hl.2.1.symm
      rw [hcu, rankC_eq_of_equiv e' hcol']
    · rfl

theorem decided_local (hG : NbhdInj G cG) (hH : NbhdInj H cH) (t : ℕ) (u : V) (v : W)
    (h : TEq G (runLab xG cG βG t) H (runLab xH cH βH t) (t + 1) u v) :
    A.decided (colorPN G cG) xG βG t u = A.decided (colorPN H cH) xH βH t v := by
  induction t with
  | zero => simp only [RAlg.decided, state_local A hG hH 0 u v h]
  | succ t ih =>
    have h' := teq_runLab_le (Nat.le_succ t) h.of_succ
    simp only [RAlg.decided, ih h', state_local A hG hH (t + 1) u v h]

end Locality

section Covering

variable {I O C L : Type} [LinearOrder C] (A : RAlg I O) (inp : L → I) (col : L → C)

/-- Runs with colour-sorted ports, inputs and colours read off the labels. -/
noncomputable def runC {X : LGraph L} (β : X.V → ℕ → Bool) : ℕ → X.V → Option O :=
  A.decided (colorPN X.G (col ∘ X.lab)) (inp ∘ X.lab) β

/-- Covering maps preserve runs: a node and its image under a label-preserving local isomorphism
make the same decisions when the random bits are pulled back. -/
theorem runC_localIso {X Y : LGraph L} (hX : NbhdInj X.G (col ∘ X.lab))
    (hY : NbhdInj Y.G (col ∘ Y.lab)) {f : X.V → Y.V}
    (hf : IsLocalIso X.G X.lab Y.G Y.lab f) (β : Y.V → ℕ → Bool) (t : ℕ) (v : X.V) :
    runC A inp col (X := X) (β ∘ f) t v = runC A inp col (X := Y) β t (f v) := by
  apply decided_local A hX hY
  have : IsLocalIso X.G (runLab (inp ∘ X.lab) (col ∘ X.lab) (β ∘ f) t) Y.G
      (runLab (inp ∘ Y.lab) (col ∘ Y.lab) β t) f :=
    ⟨fun w => by simp [runLab, hf.lab], hf.bij⟩
  exact this.teq _ v

end Covering

/-! ### Problems, solvability, GRAN -/

/-- A distributed problem (§1.1): input instances and valid output labellings. -/
structure Problem (In Out : Type) where
  /-- The input instances. -/
  inst : LGraph In → Prop
  /-- The valid output labellings of an instance. -/
  valid : (X : LGraph In) → (X.V → Out) → Prop

variable {In Out : Type}

/-- `A` solves `Π` (Las Vegas, §1.1): for every instance and every simple port numbering of it,
(1) every prefix of random bits extends to an assignment under which all nodes output within
finite time, and (2) every output labelling produced (all nodes have output) is valid. -/
def Solves (A : RAlg In Out) (Pb : Problem In Out) : Prop :=
  ∀ X : LGraph In, Pb.inst X → ∀ P : PNGraph X.V, P.IsSimple → P.toSimpleGraph = X.G →
    (∀ (β₀ : X.V → ℕ → Bool) (t₀ : ℕ), ∃ β : X.V → ℕ → Bool,
        (∀ v k, k < t₀ → β v k = β₀ v k) ∧ ∃ t, ∀ v, (A.decided P X.lab β t v).isSome) ∧
    (∀ (β : X.V → ℕ → Bool) (t : ℕ) (h : ∀ v, (A.decided P X.lab β t v).isSome),
        Pb.valid X (fun v => (A.decided P X.lab β t v).get (h v)))

/-- The distributed decision problem `Δ_Y` (§1.1): every labelled graph is an instance; all nodes
output `true` ("YES") if `X ∈ Y`, and some node outputs `false` ("NO") otherwise. -/
def decision (Y : LGraph In → Prop) : Problem In Bool where
  inst _ := True
  valid X o := (Y X → ∀ v, o v = true) ∧ (¬ Y X → ∃ v, o v = false)

/-- `Π ∈ GRAN` (§1.1): `Π` is solvable by a randomized anonymous algorithm, and so is the decision
problem of its input instances. -/
def GRAN (Pb : Problem In Out) : Prop :=
  (∃ A : RAlg In Out, Solves A Pb) ∧ ∃ B : RAlg In Bool, Solves B (decision Pb.inst)

/-- The 2-hop coloured variant `Πᶜ` (§1.1): instances `(V, E, i, c)` with `(V, E, i) ∈ Π` and `c`
a 2-hop colouring; same valid outputs. -/
def colored (C : Type) (Pb : Problem In Out) : Problem (In × C) Out where
  inst X := Pb.inst (X.map Prod.fst) ∧ IsTwoHopColoring X.G (Prod.snd ∘ X.lab)
  valid X o := Pb.valid (X.map Prod.fst) o

end Podc.RandomizationTwoHop
