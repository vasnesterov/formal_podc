import Papers.PODC2020.AsyncApproxBCDirected.Graph
import Papers.PODC2020.AsyncApproxBCDirected.FilterAverage

/-!
# One asynchronous round of Algorithm BW: model

We model one asynchronous round `r` of Algorithm BW (Algorithm 1) at the level of the information
received by the correct nodes over (global, unobservable) time `t : ℕ`.

**Communication layer (hypotheses).** The two flooding primitives of the paper are not
implemented message by message; instead `RoundExec` records what every correct node has received
by time `t` and assumes exactly the guarantees that RedundantFlood (Appendix E) and FIFO-Flood /
FIFO-Receive (Appendix F) provide on reliable asynchronous links against Byzantine nodes:
* `M v t` — the value messages `(x, p)` received by `v` by time `t` (the path `p` ends at `v`);
  `acc p` is the value that the terminal node of `p` accepted (received first) on path `p`.
  A correct relay forwards its accepted value on every redundant extension (`M_live`,
  `acc_snoc`), only after accepting it (`M_src`); a message whose last hop is correct carries the
  accepted value (`M_honest`); a node knows its own value (`acc_self`, `M_live_self`).
  Byzantine nodes may send anything, any number of times.
* `CR v t` — the `COMPLETE` messages `(c, p, M^c, F')` FIFO-received by `v` through the path `p`
  from the initiator `c`, by time `t`. Along a path of correct nodes they are genuine
  (`CR_honest`), arrive in the sending order of `c` (per-path FIFO, `CR_fifo`; `idx` is the FIFO
  counter of `c`) and eventually arrive (`CR_live`).

**Protocol logic (definitions).** Everything the algorithm *decides* is defined from these data:
Maximal-Consistency (line 10, `MCAt`, `mcTime`, `mcMsg`), the `COMPLETE` messages sent (`Sent`),
the FIFO-Receive-All condition (line 12, `FIFORecAll`), `Completeness` (Algorithm 2), `Verify`
(lines 20–26), the first verified thread (`Executes`, lines 14–18) and the new value
(`Output`, Algorithm 3).
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Message sets (Definitions 7–9) -/

/-- Definition 7: the exclusion `M|_A` (messages whose path avoids `A`). -/
noncomputable def excl (M : Finset (Msg V)) (A : Finset V) : Finset (Msg V) := by
  classical exact M.filter fun m => Avoids m.2 A

theorem mem_excl {M : Finset (Msg V)} {A : Finset V} {m : Msg V} :
    m ∈ excl M A ↔ m ∈ M ∧ Avoids m.2 A := by
  classical simp [excl]

/-- Definition 8: consistent message set (same initial node ⇒ same value). -/
def Consistent (M : Finset (Msg V)) : Prop :=
  ∀ m ∈ M, ∀ m' ∈ M, m.2.head? = m'.2.head? → m.1 = m'.1

/-- Definition 9: `M` is full for `(A, v)`: it contains a message for every redundant path of
`G − A` ending at `v`. -/
def Full (G : Digraph V) (M : Finset (Msg V)) (A : Finset V) (v : V) : Prop :=
  ∀ p, IsRedundant G p → Avoids p A → p.getLast? = some v → ∃ y, (y, p) ∈ M

/-- The value reported for `q` in `Mc` (meaningful for consistent `Mc`). -/
noncomputable def valueOf (Mc : Finset (Msg V)) (q : V) : ℝ := by
  classical exact if h : ∃ m ∈ Mc, m.2.head? = some q then (Classical.choose h).1 else 0

theorem Consistent.eq_valueOf {Mc : Finset (Msg V)} (h : Consistent Mc) {m : Msg V}
    (hm : m ∈ Mc) {q : V} (hq : m.2.head? = some q) : m.1 = valueOf Mc q := by
  classical
  have hex : ∃ m ∈ Mc, m.2.head? = some q := ⟨m, hm, hq⟩
  simp only [valueOf, hex, dite_true]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  exact h m hm _ h1 (hq.trans h2.symm)

/-! ## Maximal consistency and `COMPLETE` messages -/

section Protocol

variable (G : Digraph V) (f : ℕ)

/-- Maximal-Consistency condition (line 10) of thread `F'` at node `c` at time `t`. -/
def MCAt (M : V → ℕ → Finset (Msg V)) (c : V) (F' : Finset V) (t : ℕ) : Prop :=
  Consistent (excl (M c t) F') ∧ Full G (excl (M c t) F') F' c

/-- Node `c` sends `COMPLETE(F')` (line 11): `F'` is one of its threads and Maximal-Consistency
eventually holds for it. -/
def Sent (M : V → ℕ → Finset (Msg V)) (c : V) (F' : Finset V) : Prop :=
  c ∉ F' ∧ F'.card ≤ f ∧ ∃ t, MCAt G M c F' t

/-- The time at which Maximal-Consistency holds for the first time. -/
noncomputable def mcTime (M : V → ℕ → Finset (Msg V)) (c : V) (F' : Finset V) : ℕ := by
  classical exact if h : ∃ t, MCAt G M c F' t then Nat.find h else 0

/-- The content `M_c|_{F'}` of `COMPLETE(F')` (the message set at the first time
Maximal-Consistency holds). -/
noncomputable def mcMsg (M : V → ℕ → Finset (Msg V)) (c : V) (F' : Finset V) :
    Finset (Msg V) :=
  excl (M c (mcTime G M c F')) F'

theorem Sent.mcAt {M : V → ℕ → Finset (Msg V)} {c : V} {F' : Finset V} (h : Sent G f M c F') :
    MCAt G M c F' (mcTime G M c F') := by
  classical
  have hex := h.2.2
  simp only [mcTime, hex, dite_true]
  exact Nat.find_spec hex

theorem Sent.consistent {M : V → ℕ → Finset (Msg V)} {c : V} {F' : Finset V}
    (h : Sent G f M c F') : Consistent (mcMsg G M c F') := (h.mcAt G f).1

theorem Sent.full {M : V → ℕ → Finset (Msg V)} {c : V} {F' : Finset V}
    (h : Sent G f M c F') : Full G (mcMsg G M c F') F' c := (h.mcAt G f).2

end Protocol

/-- One asynchronous round of Algorithm BW, as seen by the correct nodes (see the module
docstring). `F` is the actual set of Byzantine nodes and `x` the state values of the correct
nodes at the beginning of the round. -/
structure RoundExec (G : Digraph V) (f : ℕ) where
  /-- The Byzantine nodes. -/
  F : Finset V
  card_F : F.card ≤ f
  /-- State values (inputs of the round) of the correct nodes. -/
  x : V → ℝ
  /-- Value messages received by time `t`. -/
  M : V → ℕ → Finset (Msg V)
  /-- The value accepted (received first) on a path by its terminal node. -/
  acc : List V → ℝ
  /-- `COMPLETE` messages `(initiator, path, content, thread set)` FIFO-received by time `t`. -/
  CR : V → ℕ → Finset (V × List V × Finset (Msg V) × Finset V)
  /-- FIFO counter of the `COMPLETE` messages of a node. -/
  idx : V → Finset V → ℕ
  M_mono : ∀ v, Monotone (M v)
  M_last : ∀ v ∉ F, ∀ t, ∀ m ∈ M v t, m.2.getLast? = some v
  M_first : ∀ v ∉ F, ∀ t y p, (y, p) ∈ M v t → (acc p, p) ∈ M v t
  M_honest : ∀ v ∉ F, ∀ t y p, (y, p ++ [v]) ∈ M v t → (∀ q ∈ p.getLast?, q ∉ F) →
    y = acc (p ++ [v])
  acc_self : ∀ s ∉ F, acc [s] = x s
  acc_snoc : ∀ p q w, p.getLast? = some q → q ∉ F → acc (p ++ [w]) = acc p
  M_src : ∀ v ∉ F, ∀ t y p q, (y, p ++ [v]) ∈ M v t → p.getLast? = some q → q ∉ F →
    ∃ t', (acc p, p) ∈ M q t'
  M_live_self : ∀ s ∉ F, ∃ t, (x s, [s]) ∈ M s t
  M_live : ∀ v ∉ F, ∀ p q, p.getLast? = some q → q ∉ F → G.Adj q v → q ≠ v →
    IsRedundant G (p ++ [v]) → (∃ t, (acc p, p) ∈ M q t) → ∃ t, (acc p, p ++ [v]) ∈ M v t
  CR_mono : ∀ v, Monotone (CR v)
  CR_honest : ∀ v ∉ F, ∀ t c p Mc F', (c, p, Mc, F') ∈ CR v t → Avoids p F →
    p.head? = some c ∧ Sent G f M c F' ∧ Mc = mcMsg G M c F' ∧ mcTime G M c F' ≤ t
  CR_fifo : ∀ v ∉ F, ∀ t c p Mc F' F'', (c, p, Mc, F') ∈ CR v t → Avoids p F →
    Sent G f M c F'' → idx c F'' < idx c F' → (c, p, mcMsg G M c F'', F'') ∈ CR v t
  CR_live : ∀ v ∉ F, ∀ c p F', Sent G f M c F' → IsSimplePath G p c v → Avoids p F →
    ∃ t, (c, p, mcMsg G M c F', F') ∈ CR v t
  idx_inj : ∀ c ∉ F, ∀ F₁ F₂, Sent G f M c F₁ → Sent G f M c F₂ → idx c F₁ = idx c F₂ → F₁ = F₂

namespace RoundExec

variable {G : Digraph V} {f : ℕ} (E : RoundExec G f)

/-- Line 12: FIFO-Receive-All for thread `Fv` at `v` by time `t`: from every `c`, the same
`COMPLETE(Fv)` message was FIFO-received along every simple `(c, v)`-path inside
`reach_v(Fv)`. -/
def FIFORecAll (v : V) (Fv : Finset V) (t : ℕ) : Prop :=
  ∀ c, ∃ Mc, ∀ p, IsSimplePath G p c v → (∀ y ∈ p, Reaches G Fv y v) → (c, p, Mc, Fv) ∈ E.CR v t

end RoundExec

/-- **Algorithm 2** (`Completeness(Mv, Mc, Fu)` at node `v`), with covers not containing `v`:
for every `Fw ≠ Fu` with `|Fw| ≤ f` and every `q ∈ S_{Fu,Fw}`, the messages of `Mv` from `q`
carrying the value reported for `q` in `Mc` admit no `f`-cover inside `V \ S_{Fu,Fw}`. -/
def Completeness (G : Digraph V) (f : ℕ) (v : V) (Mv Mc : Finset (Msg V)) (Fu : Finset V) :
    Prop :=
  ∀ Fw : Finset V, Fw.card ≤ f → Fw ≠ Fu → ∀ q ∈ srcComp G Fu Fw,
    ∃ m ∈ Mc, m.2.head? = some q ∧
      ¬ ∃ H : Finset V, H.card ≤ f ∧ v ∉ H ∧ (∀ h ∈ H, h ∉ srcComp G Fu Fw) ∧
        ∀ m' ∈ Mv, m'.2.head? = some q → m'.1 = m.1 → ¬ Avoids m'.2 H

namespace RoundExec

variable {G : Digraph V} {f : ℕ} (E : RoundExec G f)

/-- Function `Verify` (lines 20–26) for thread `Fv` at time `t`. -/
def Verify (v : V) (Fv : Finset V) (t : ℕ) : Prop :=
  (∃ t' ≤ t, E.FIFORecAll v Fv t') ∧
  ∀ c p Mc Fu, (c, p, Mc, Fu) ∈ E.CR v t → (∀ y ∈ p, Reaches G Fv y v) → Consistent Mc →
    Completeness G f v (E.M v t) Mc Fu

/-- Lines 14–18: `v` executes Filter-and-Average at time `t` in thread `Fv`: the first time at
which the `Verify` condition of some thread holds. -/
def Executes (v : V) (Fv : Finset V) (t : ℕ) : Prop :=
  v ∉ Fv ∧ Fv.card ≤ f ∧ E.Verify v Fv t ∧
    ∀ t' < t, ∀ F' : Finset V, v ∉ F' → F'.card ≤ f → ¬ E.Verify v F' t'

/-- The new state value `y` of `v` at the end of the round (Algorithm 3 applied to `M_v`). -/
def Output (v : V) (y : ℝ) : Prop := ∃ Fv t, E.Executes v Fv t ∧ IsFA f v (E.M v t) y

end RoundExec

end AsyncApproxBCDirected
