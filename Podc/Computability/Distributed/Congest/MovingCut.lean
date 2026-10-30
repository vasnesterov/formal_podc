import Cslib.Computability.Distributed.Congest.Randomized

-- CSLib candidate: Cslib/Computability/Distributed/Congest/MovingCut.lean

/-!
# Moving-cut simulation (Das Sarma et al.)

`Cslib.Congest.LBFamily.simulation` simulates a CONGEST algorithm across a *fixed* cut, with
`|Ecut| · B` bits per round and direction. The lower bounds in the style of Das Sarma, Holzer,
Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer (*Distributed verification and hardness of
distributed approximation*, STOC'11 / SICOMP 2012, Simulation Theorem 3.1) instead let the sets
of nodes simulated by Alice and by Bob **shrink** by one "column" per round. This only needs the
messages that *enter* the shrinking sets, which is a small number (`O(log n)` per round for the
networks of paths plus a balanced shortcut tree), whereas every fixed cut of those networks is
large.

* `MovingCutFamily X Y V I`: graphs `G x y` with node inputs `inp x y`, and two *knowledge
  horizons* `ka kb : V → ℕ`: Alice can compute the state of `v` after `t` rounds iff
  `t < ka v`, Bob iff `t < kb v`. The axioms: nodes that Alice ever knows (`0 < ka v`) have
  input and neighbourhood independent of Bob's input `y` (symmetrically for Bob); and in round
  `t`, every message received by a node that Alice must know at time `t + 1` from a node that she
  does not know at time `t` travels along an arc of a fixed (input-independent) finset `toA t`
  whose senders Bob knows at time `t` (symmetrically `toB t`).
* `MovingCutFamily.simulation`: a `T`-round algorithm with `B`-bit messages yields a protocol
  that exchanges, in round `t`, the messages on `toA t` and `toB t`, and then one bit from each
  player: if `|toA t|, |toB t| ≤ D`, its cost is at most `T · 2 · D · B + 2`. It computes
  `gA x (states) && gB y (states)` for any `gA` reading only the states Alice knows at time `T`
  and any `gB` reading only those Bob knows.
* `MovingCutFamily.simulation_accepts`, `lowerBound`, `not_disj_lowerBound`: if every node is
  known to Alice or Bob at time `T`, the protocol computes "all nodes accept"; hence lower bounds
  from communication complexity (unconditional for set disjointness).
* Randomized algorithms (private random strings of the nodes, `Algorithm V (I × ρ) σ B`): a node
  may be simulated by both players, so they need the same random strings — the simulation gives
  a **public-coin** protocol (`Protocol.PubRandComputes`), `MovingCutFamily.rand_lowerBound`.
-/

namespace Cslib.CommunicationComplexity.Protocol

open Finset

variable {X Y R : Type*} [Fintype R]

/-- Number of public random strings on which a public-coin protocol (a family of deterministic
protocols indexed by the shared random string) errs on `(x, y)`. -/
noncomputable def pubErrCount (P : R → Protocol X Y Bool) (f : X → Y → Bool) (x : X) (y : Y) :
    ℕ := by
  classical
  exact (univ.filter fun r : R => (P r).eval x y ≠ f x y).card

/-- A public-coin randomized protocol (uniform shared random string `r : R`) computing `f` with
error at most `ε` on every input. -/
def PubRandComputes (P : R → Protocol X Y Bool) (f : X → Y → Bool) (ε : ℝ) : Prop :=
  ∀ x y, (pubErrCount P f x y : ℝ) ≤ ε * Fintype.card R

end Cslib.CommunicationComplexity.Protocol

namespace Cslib.Congest

open Cslib.CommunicationComplexity Protocol Finset

/-- A family of lower-bound graphs with a moving cut. Alice knows the state of `v` after `t`
rounds iff `t < ka v`, Bob iff `t < kb v`. Messages entering Alice's shrinking set in round `t`
from outside travel along arcs `(sender, receiver)` of `toA t` (sent by Bob), and symmetrically
for `toB t`. -/
structure MovingCutFamily (X Y V I : Type*) where
  /-- The graph for inputs `x`, `y`. -/
  G : X → Y → SimpleGraph V
  /-- Node inputs. -/
  inp : X → Y → V → I
  /-- Alice's knowledge horizon: she knows the state of `v` after `t` rounds iff `t < ka v`. -/
  ka : V → ℕ
  /-- Bob's knowledge horizon. -/
  kb : V → ℕ
  /-- The arcs whose round-`t` messages Bob sends to Alice. -/
  toA : ℕ → Finset (V × V)
  /-- The arcs whose round-`t` messages Alice sends to Bob. -/
  toB : ℕ → Finset (V × V)
  inp_alice : ∀ x y y' v, 0 < ka v → inp x y v = inp x y' v
  inp_bob : ∀ x x' y v, 0 < kb v → inp x y v = inp x' y v
  adj_alice : ∀ x y y' w v, 0 < ka v → ((G x y).Adj w v ↔ (G x y').Adj w v)
  adj_bob : ∀ x x' y w v, 0 < kb v → ((G x y).Adj w v ↔ (G x' y).Adj w v)
  /-- Bob knows the senders of the arcs of `toA t` at time `t`. -/
  toA_bob : ∀ t p, p ∈ toA t → t < kb p.1
  /-- Alice knows the senders of the arcs of `toB t` at time `t`. -/
  toB_alice : ∀ t p, p ∈ toB t → t < ka p.1
  /-- Messages entering Alice's set from outside use arcs of `toA t`. -/
  bdry_alice : ∀ x y t w v, t + 1 < ka v → (G x y).Adj w v → ka w ≤ t → (w, v) ∈ toA t
  /-- Messages entering Bob's set from outside use arcs of `toB t`. -/
  bdry_bob : ∀ x y t w v, t + 1 < kb v → (G x y).Adj w v → kb w ≤ t → (w, v) ∈ toB t

namespace MovingCutFamily

variable {X Y V I σ : Type*} {B : ℕ} (F : MovingCutFamily X Y V I)
  [∀ x y, DecidableRel (F.G x y).Adj]

/-- Alice's simulation (meaningful at nodes she knows), given her input, a dummy input `y₀` for
Bob and the history `hB t w v` of the messages from `w` to `v` sent to her by Bob. -/
def simA (A : Algorithm V I σ B) (x : X) (y₀ : Y) (hB : ℕ → V → V → Msg B) : ℕ → V → σ
  | 0 => fun v => A.init v (F.inp x y₀ v)
  | t + 1 => fun v => A.step v (simA A x y₀ hB t v)
      (fun w => if (F.G x y₀).Adj w v then
        some (if t < F.ka w then A.send w (simA A x y₀ hB t w) v else hB t w v) else none)

/-- Bob's simulation (meaningful at nodes he knows). -/
def simB (A : Algorithm V I σ B) (x₀ : X) (y : Y) (hA : ℕ → V → V → Msg B) : ℕ → V → σ
  | 0 => fun v => A.init v (F.inp x₀ y v)
  | t + 1 => fun v => A.step v (simB A x₀ y hA t v)
      (fun w => if (F.G x₀ y).Adj w v then
        some (if t < F.kb w then A.send w (simB A x₀ y hA t w) v else hA t w v) else none)

/-- Alice's simulation is exact on the nodes she knows, given correct messages on `toA`. -/
lemma simA_eq (A : Algorithm V I σ B) (x : X) (y y₀ : Y) (hB : ℕ → V → V → Msg B) :
    ∀ t, (∀ s < t, ∀ p ∈ F.toA s, hB s p.1 p.2 = A.send p.1 (A.run (F.G x y) (F.inp x y) s p.1) p.2) →
      ∀ v, t < F.ka v → F.simA A x y₀ hB t v = A.run (F.G x y) (F.inp x y) t v
  | 0, _, v, hv => by simp [simA, Algorithm.run, F.inp_alice x y₀ y v hv]
  | t + 1, h, v, hv => by
      have ih := simA_eq A x y y₀ hB t (fun s hs => h s (Nat.lt_succ_of_lt hs))
      simp only [simA, Algorithm.run]
      rw [ih v (by omega)]
      congr 1
      funext w
      have hadj : (F.G x y₀).Adj w v ↔ (F.G x y).Adj w v :=
        (F.adj_alice x y y₀ w v (by omega)).symm
      by_cases hwv : (F.G x y).Adj w v
      · simp only [hadj.2 hwv, hwv, ↓reduceIte, Option.some.injEq]
        by_cases hw : t < F.ka w
        · simp [hw, ih w hw]
        · simp only [hw, ↓reduceIte]
          exact h t (Nat.lt_succ_self t) (w, v) (F.bdry_alice x y t w v hv hwv (not_lt.1 hw))
      · have h0 : ¬(F.G x y₀).Adj w v := fun h' => hwv (hadj.1 h')
        simp only [h0, hwv, ↓reduceIte]

/-- Bob's simulation is exact on the nodes he knows, given correct messages on `toB`. -/
lemma simB_eq (A : Algorithm V I σ B) (x x₀ : X) (y : Y) (hA : ℕ → V → V → Msg B) :
    ∀ t, (∀ s < t, ∀ p ∈ F.toB s, hA s p.1 p.2 = A.send p.1 (A.run (F.G x y) (F.inp x y) s p.1) p.2) →
      ∀ v, t < F.kb v → F.simB A x₀ y hA t v = A.run (F.G x y) (F.inp x y) t v
  | 0, _, v, hv => by simp [simB, Algorithm.run, F.inp_bob x₀ x y v hv]
  | t + 1, h, v, hv => by
      have ih := simB_eq A x x₀ y hA t (fun s hs => h s (Nat.lt_succ_of_lt hs))
      simp only [simB, Algorithm.run]
      rw [ih v (by omega)]
      congr 1
      funext w
      have hadj : (F.G x₀ y).Adj w v ↔ (F.G x y).Adj w v :=
        (F.adj_bob x x₀ y w v (by omega)).symm
      by_cases hwv : (F.G x y).Adj w v
      · simp only [hadj.2 hwv, hwv, ↓reduceIte, Option.some.injEq]
        by_cases hw : t < F.kb w
        · simp [hw, ih w hw]
        · simp only [hw, ↓reduceIte]
          exact h t (Nat.lt_succ_self t) (w, v) (F.bdry_bob x y t w v hv hwv (not_lt.1 hw))
      · have h0 : ¬(F.G x₀ y).Adj w v := fun h' => hwv (hadj.1 h')
        simp only [h0, hwv, ↓reduceIte]

variable [DecidableEq V]

/-- Record the messages `m` of round `t` on the arcs of `S` in a message history. -/
def record (h : ℕ → V → V → Msg B) (t : ℕ) (S : Finset (V × V)) (m : S → Msg B) :
    ℕ → V → V → Msg B :=
  fun s w v => if s = t then (if hp : (w, v) ∈ S then m ⟨(w, v), hp⟩ else fun _ => false)
    else h s w v

/-- One round of messages on the arcs of `S` costs `|S| · B` bits. -/
lemma clog_card_msgs (S : Finset (V × V)) (B : ℕ) :
    Nat.clog 2 (Fintype.card (S → Msg B)) = S.card * B := by
  simp only [Fintype.card_fun, Msg, Fintype.card_bool, Fintype.card_fin, Fintype.card_coe]
  rw [← pow_mul, mul_comm B, Nat.clog_pow _ _ (by norm_num)]

/-- The protocol simulating the remaining `r` rounds from round `t`, given the message histories
`hA` (Alice → Bob) and `hB` (Bob → Alice). In round `t` Alice sends the messages on `toB t`, then
Bob those on `toA t`; at the end Alice sends the bit `gA`, Bob the bit `gB`. -/
noncomputable def simProt [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y)
    (gA : X → (V → σ) → Bool) (gB : Y → (V → σ) → Bool) :
    ℕ → ℕ → (ℕ → V → V → Msg B) → (ℕ → V → V → Msg B) → Protocol X Y Bool
  | 0, t, hA, hB =>
      .alice 2 (fun x => if gA x (F.simA A x y₀ hB t) then 1 else 0)
        fun i => .bob 2 (fun y => if gB y (F.simB A x₀ y hA t) then 1 else 0)
          fun j => .ret (decide (i = 1 ∧ j = 1))
  | r + 1, t, hA, hB =>
      .alice (Fintype.card (F.toB t → Msg B))
        (fun x => Fintype.equivFin _
          (fun p : F.toB t => A.send p.1.1 (F.simA A x y₀ hB t p.1.1) p.1.2))
        fun i => .bob (Fintype.card (F.toA t → Msg B))
          (fun y => Fintype.equivFin _
            (fun p : F.toA t => A.send p.1.1 (F.simB A x₀ y hA t p.1.1) p.1.2))
          fun j => simProt A x₀ y₀ gA gB r (t + 1)
            (record hA t (F.toB t) ((Fintype.equivFin _).symm i))
            (record hB t (F.toA t) ((Fintype.equivFin _).symm j))

/-- If at most `D` arcs carry messages per round and direction, the protocol for `r` rounds costs
at most `r · 2 · D · B + 2` bits. -/
lemma simProt_cost [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y)
    (gA : X → (V → σ) → Bool) (gB : Y → (V → σ) → Bool) {D : ℕ}
    (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D) :
    ∀ r t hA hB, (F.simProt A x₀ y₀ gA gB r t hA hB).CostLE (r * (2 * (D * B)) + 2)
  | 0, t, hA, hB => by
      have h2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by norm_num)
      simp only [simProt, CostLE, zero_mul, zero_add, h2]
      exact ⟨by norm_num, fun i => ⟨by norm_num, fun j => trivial⟩⟩
  | r + 1, t, hA, hB => by
      simp only [simProt, CostLE, clog_card_msgs]
      have hb := Nat.mul_le_mul_right B (hDB t)
      have ha := Nat.mul_le_mul_right B (hDA t)
      have e : (r + 1) * (2 * (D * B)) = r * (2 * (D * B)) + 2 * (D * B) := by ring
      refine ⟨by rw [e]; omega, fun i => ⟨by rw [e]; omega, fun j => ?_⟩⟩
      refine (simProt_cost A x₀ y₀ gA gB hDA hDB r (t + 1) _ _).mono ?_
      rw [e]; omega

/-- The simulating protocol computes `gA x (states) && gB y (states)` at time `t + r`, given
correct message histories, if `gA` only reads states known to Alice and `gB` only states known
to Bob at time `t + r`. -/
lemma simProt_eval [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y)
    (gA : X → (V → σ) → Bool) (gB : Y → (V → σ) → Bool) (x : X) (y : Y) :
    ∀ r t hA hB,
      (∀ x s s', (∀ v, t + r < F.ka v → s v = s' v) → gA x s = gA x s') →
      (∀ y s s', (∀ v, t + r < F.kb v → s v = s' v) → gB y s = gB y s') →
      (∀ s < t, ∀ p ∈ F.toB s, hA s p.1 p.2 = A.send p.1 (A.run (F.G x y) (F.inp x y) s p.1) p.2) →
      (∀ s < t, ∀ p ∈ F.toA s, hB s p.1 p.2 = A.send p.1 (A.run (F.G x y) (F.inp x y) s p.1) p.2) →
      (F.simProt A x₀ y₀ gA gB r t hA hB).eval x y =
        (gA x (A.run (F.G x y) (F.inp x y) (t + r)) && gB y (A.run (F.G x y) (F.inp x y) (t + r)))
  | 0, t, hA, hB, hgA, hgB, hhA, hhB => by
      have eA : gA x (F.simA A x y₀ hB t) = gA x (A.run (F.G x y) (F.inp x y) t) :=
        hgA x _ _ fun v hv => F.simA_eq A x y y₀ hB t hhB v (by simpa using hv)
      have eB : gB y (F.simB A x₀ y hA t) = gB y (A.run (F.G x y) (F.inp x y) t) :=
        hgB y _ _ fun v hv => F.simB_eq A x x₀ y hA t hhA v (by simpa using hv)
      simp only [simProt, eval, add_zero, ← eA, ← eB]
      by_cases h1 : gA x (F.simA A x y₀ hB t) = true <;>
        by_cases h2 : gB y (F.simB A x₀ y hA t) = true <;> simp [h1, h2]
  | r + 1, t, hA, hB, hgA, hgB, hhA, hhB => by
      simp only [simProt, eval, Equiv.symm_apply_apply]
      rw [simProt_eval A x₀ y₀ gA gB x y r (t + 1), show t + 1 + r = t + (r + 1) by omega]
      · intro x s s' h; exact hgA x s s' fun v hv => h v (by omega)
      · intro y s s' h; exact hgB y s s' fun v hv => h v (by omega)
      · intro s hs p hp
        by_cases hst : s = t
        · subst hst
          simp only [record, ↓reduceIte, Prod.mk.eta, hp, ↓reduceDIte]
          exact congrArg (fun st => A.send p.1 st p.2)
            (F.simA_eq A x y y₀ hB s hhB p.1 (F.toB_alice s p hp))
        · have hst' : s < t := by omega
          simp only [record, hst, ↓reduceIte]
          exact hhA s hst' p hp
      · intro s hs p hp
        by_cases hst : s = t
        · subst hst
          simp only [record, ↓reduceIte, Prod.mk.eta, hp, ↓reduceDIte]
          exact congrArg (fun st => A.send p.1 st p.2)
            (F.simB_eq A x x₀ y hA s hhA p.1 (F.toA_bob s p hp))
        · have hst' : s < t := by omega
          simp only [record, hst, ↓reduceIte]
          exact hhB s hst' p hp

omit [DecidableEq V] in
/-- **Moving-cut simulation** (Das Sarma et al., Simulation Theorem 3.1): a `T`-round CONGEST
algorithm with `B`-bit messages yields a two-party protocol with at most `T · 2 · D · B + 2` bits
(`D` bounds the number of arcs entering the shrinking sets per round) computing
`gA x (states) && gB y (states)` after `T` rounds, for any `gA` that only reads the states Alice
knows at time `T` and any `gB` that only reads the states Bob knows. -/
theorem simulation [Fintype V] [Nonempty X] [Nonempty Y] (A : Algorithm V I σ B) (T D : ℕ)
    (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D)
    (gA : X → (V → σ) → Bool) (gB : Y → (V → σ) → Bool)
    (hgA : ∀ x s s', (∀ v, T < F.ka v → s v = s' v) → gA x s = gA x s')
    (hgB : ∀ y s s', (∀ v, T < F.kb v → s v = s' v) → gB y s = gB y s') :
    ∃ P : Protocol X Y Bool, P.CostLE (T * (2 * (D * B)) + 2) ∧
      ∀ x y, P.eval x y =
        (gA x (A.run (F.G x y) (F.inp x y) T) && gB y (A.run (F.G x y) (F.inp x y) T)) := by
  classical
  refine ⟨F.simProt A (Classical.arbitrary X) (Classical.arbitrary Y) gA gB T 0
    (fun _ _ _ _ => false) (fun _ _ _ _ => false), F.simProt_cost A _ _ gA gB hDA hDB T 0 _ _,
    fun x y => ?_⟩
  rw [F.simProt_eval A _ _ gA gB x y T 0 _ _ (by simpa using hgA) (by simpa using hgB)
    (fun s hs => absurd hs (Nat.not_lt_zero s)) (fun s hs => absurd hs (Nat.not_lt_zero s)),
    zero_add]

omit [DecidableEq V] in
/-- If every node is known to Alice or to Bob at time `T`, the moving-cut simulation computes
"all nodes accept" with at most `T · 2 · D · B + 2` bits. -/
theorem simulation_accepts [Fintype V] [Nonempty X] [Nonempty Y] (A : Algorithm V I σ B)
    (T D : ℕ) (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D)
    (hcover : ∀ v, T < F.ka v ∨ T < F.kb v) :
    ∃ P : Protocol X Y Bool, P.CostLE (T * (2 * (D * B)) + 2) ∧
      P.Computes fun x y => decide (A.Accepts (F.G x y) (F.inp x y) T) := by
  classical
  obtain ⟨P, hc, hP⟩ := F.simulation A T D hDA hDB
    (fun _ s => decide (∀ v, T < F.ka v → A.out v (s v) = true))
    (fun _ s => decide (∀ v, T < F.kb v → A.out v (s v) = true))
    (fun x s s' h => by
      simp only [decide_eq_decide]
      exact forall_congr' fun v => imp_congr_right fun hv => by rw [h v hv])
    (fun y s s' h => by
      simp only [decide_eq_decide]
      exact forall_congr' fun v => imp_congr_right fun hv => by rw [h v hv])
  refine ⟨P, hc, fun x y => ?_⟩
  rw [hP, Bool.eq_iff_iff]
  simp only [Algorithm.Accepts, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩ v
    rcases hcover v with hv | hv
    · exact h1 v hv
    · exact h2 v hv
  · intro h
    exact ⟨fun v _ => h v, fun v _ => h v⟩

omit [DecidableEq V] in
/-- **Lower bound from communication complexity.** If every protocol for `f` needs `C` bits,
every node is known to Alice or Bob at time `T`, and a `T`-round algorithm accepts `G x y` iff
`f x y`, then `C ≤ T · 2 · D · B + 2`. -/
theorem lowerBound [Finite V] [Nonempty X] [Nonempty Y] (A : Algorithm V I σ B) (T D : ℕ)
    (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D)
    (hcover : ∀ v, T < F.ka v ∨ T < F.kb v) (f : X → Y → Bool)
    (hA : ∀ x y, A.Accepts (F.G x y) (F.inp x y) T ↔ f x y = true) (C : ℕ)
    (hC : ∀ (P : Protocol X Y Bool) c, P.Computes f → P.CostLE c → C ≤ c) :
    C ≤ T * (2 * (D * B)) + 2 := by
  have := Fintype.ofFinite V
  obtain ⟨P, hc, hP⟩ := F.simulation_accepts A T D hDA hDB hcover
  refine hC P _ (fun x y => ?_) hc
  rw [hP x y]
  cases h : f x y <;> simp [hA, h]

omit [DecidableEq V] in
/-- Lower bound for the complement of set disjointness (unconditional): if a `T`-round algorithm
accepts `G x y` iff the inputs intersect, then `K ≤ T · 2 · D · B + 2`. -/
theorem not_disj_lowerBound {ι : Type*} [Fintype ι] [Finite V]
    (F : MovingCutFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V I σ B) (T D : ℕ)
    (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D)
    (hcover : ∀ v, T < F.ka v ∨ T < F.kb v)
    (hA : ∀ x y, A.Accepts (F.G x y) (F.inp x y) T ↔ disj x y = false) :
    Fintype.card ι ≤ T * (2 * (D * B)) + 2 :=
  F.lowerBound A T D hDA hDB hcover (fun x y => !disj x y) (fun x y => by simpa using hA x y) _
    fun _ _ hP hc => Protocol.not_disj_lowerBound hP hc

/-! ### Randomized algorithms -/

variable {ρ : Type*}

/-- The family with the (fixed) random strings `r v` added to the node inputs. -/
def withCoins (r : V → ρ) : MovingCutFamily X Y V (I × ρ) where
  G := F.G
  inp x y v := (F.inp x y v, r v)
  ka := F.ka
  kb := F.kb
  toA := F.toA
  toB := F.toB
  inp_alice x y y' v hv := by rw [F.inp_alice x y y' v hv]
  inp_bob x x' y v hv := by rw [F.inp_bob x x' y v hv]
  adj_alice := F.adj_alice
  adj_bob := F.adj_bob
  toA_bob := F.toA_bob
  toB_alice := F.toB_alice
  bdry_alice := F.bdry_alice
  bdry_bob := F.bdry_bob

instance (r : V → ρ) (x : X) (y : Y) : DecidableRel ((F.withCoins r).G x y).Adj :=
  inferInstanceAs (DecidableRel (F.G x y).Adj)

omit [DecidableEq V] in
/-- **Randomized moving-cut simulation.** For a randomized algorithm (node `v` receives its random
string `r v` with its input), every fixed `r` gives a protocol of cost `T · 2 · D · B + 2`; the
family of these protocols is a public-coin protocol whose bad coins on `(x, y)` are exactly the
random strings on which the algorithm's acceptance differs from `f x y`. -/
theorem rand_simulation [Fintype V] [Nonempty X] [Nonempty Y] (A : Algorithm V (I × ρ) σ B)
    (T D : ℕ) (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D)
    (hcover : ∀ v, T < F.ka v ∨ T < F.kb v) :
    ∃ P : (V → ρ) → Protocol X Y Bool, (∀ r, (P r).CostLE (T * (2 * (D * B)) + 2)) ∧
      ∀ r x y, (P r).eval x y =
        decide (A.Accepts (F.G x y) (fun v => (F.inp x y v, r v)) T) := by
  have h := fun r : V → ρ => (F.withCoins r).simulation_accepts A T D hDA hDB hcover
  choose P hc hP using h
  exact ⟨P, hc, fun r x y => hP r x y⟩

/-- **Lower bound for randomized algorithms.** If every public-coin protocol computing `f` with
error `≤ ε` needs `C` bits, every node is known to Alice or Bob at time `T`, and a randomized
`T`-round algorithm decides `f` on the family with error `≤ ε` (over uniform random strings
`r : V → ρ`), then `C ≤ T · 2 · D · B + 2`. -/
theorem rand_lowerBound [Fintype V] [Fintype ρ] [Nonempty X] [Nonempty Y]
    (A : Algorithm V (I × ρ) σ B) (T D : ℕ) (hDA : ∀ t, (F.toA t).card ≤ D)
    (hDB : ∀ t, (F.toB t).card ≤ D) (hcover : ∀ v, T < F.ka v ∨ T < F.kb v)
    (f : X → Y → Bool) (ε : ℝ)
    (hA : ∀ x y, ((univ.filter fun r : V → ρ =>
      decide (A.Accepts (F.G x y) (fun v => (F.inp x y v, r v)) T) ≠ f x y).card : ℝ) ≤
        ε * Fintype.card (V → ρ))
    (C : ℕ) (hC : ∀ (P : (V → ρ) → Protocol X Y Bool) (c : ℕ),
      (∀ r, (P r).CostLE c) → PubRandComputes P f ε → C ≤ c) :
    C ≤ T * (2 * (D * B)) + 2 := by
  classical
  obtain ⟨P, hc, hP⟩ := F.rand_simulation A T D hDA hDB hcover
  refine hC P _ hc fun x y => le_trans (le_of_eq ?_) (hA x y)
  simp only [pubErrCount, hP]

end MovingCutFamily

end Cslib.Congest
