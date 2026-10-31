import Podc.Computability.Distributed.Byzantine.AsyncBroadcast

/-!
# The algorithm of Mostéfaoui, Moumen, Raynal (PODC 2014) as an asynchronous broadcast protocol

A. Mostéfaoui, H. Moumen, M. Raynal, *Signature-Free Asynchronous Byzantine Consensus with
`t < n/3` and `O(n²)` Messages*, PODC 2014 (full version: IRISA PI-2016, hal-00944019).

We model Figure 1 (BV-broadcast) and Figure 2 (binary consensus with a common coin) in the
interleaving model `Cslib.Byzantine.AsyncBroadcast` (asynchronous reliable authenticated
channels, at most `t` Byzantine processes, chosen adaptively).

* Messages: `bval r v tag` is `B_VAL[r](v)` and `aux r v` is `AUX[r](v)`. Receivers ignore
  `tag`. It is `none` for an echo (Figure 1, line 03) and `some d` for the broadcast of the
  own estimate (Figure 1, line 01, called by Figure 2, line 02). The bit `d` records whether the
  set `values` of the previous round was a singleton. It makes the local variables of the
  process (`est`, the current round, whether line 08 applies) readable from its broadcasts.
* `binVal t ib r v` is `v ∈ bin_values[r]` (Figure 1, line 05): `B_VAL[r](v)` received from
  `2t + 1` processes.
* `AuxQuorum t ib r V` is the predicate of Figure 2, line 05 with `values = V`.
* `nextEst V s` is lines 06–11: the new estimate and whether `values` was a singleton.
* The common coin is a fixed sequence `coin : ℕ → Bool` (`coin r` = the `r`-th bit
  `random()` returns, the same at every process).
* Decision (line 08) is the `decide` guard: the process has started round `r + 1` with
  estimate `v` after a singleton `values = {v}` in round `r`, and `coin r = v`.

The guards are liberal (a "wait until" may be passed later, with any set of messages that
satisfies it). This is a superset of the behaviours of the code, so safety transfers.
-/

namespace Podc.SignatureFreeBA

open Cslib.Byzantine.AsyncBroadcast

/-- Messages of Figures 1–2. `bval r v tag` = `B_VAL[r](v)` (with a local tag ignored by the
receivers), `aux r v` = `AUX[r](v)`. -/
inductive Msg
  | bval (r : ℕ) (v : Bool) (tag : Option Bool)
  | aux (r : ℕ) (v : Bool)
  deriving DecidableEq

instance : Countable Msg := by
  have : Function.Injective (fun m : Msg => match m with
      | .bval r v d => (Sum.inl (r, v, d) : (ℕ × Bool × Option Bool) ⊕ (ℕ × Bool))
      | .aux r v => Sum.inr (r, v)) := by
    intro a b h
    cases a <;> cases b <;> simp_all
  exact this.countable

/-- `m` is a `B_VAL[r](v)` message (any tag). -/
def IsBval (r : ℕ) (v : Bool) (m : Msg) : Prop := ∃ d, m = .bval r v d

/-- `m` is an `AUX[r](·)` message. -/
def IsAux (r : ℕ) (m : Msg) : Prop := ∃ w, m = .aux r w

/-- `m` is the broadcast of an own estimate for round `r`. -/
def IsEst (r : ℕ) (m : Msg) : Prop := ∃ v d, m = .bval r v (some d)

variable {P : Type*} [Fintype P]

/-- The number of processes from which `B_VAL[r](v)` was received. -/
noncomputable def bvCnt (ib : P → Set Msg) (r : ℕ) (v : Bool) : ℕ := cntP ib (IsBval r v)

/-- `v ∈ bin_values[r]` (Figure 1, line 05). -/
def BinVal (t : ℕ) (ib : P → Set Msg) (r : ℕ) (v : Bool) : Prop := 2 * t + 1 ≤ bvCnt ib r v

/-- The predicate of Figure 2, line 05, with `values = V`: there are `n − t` distinct senders
`S` and, for each of them, a received message `AUX[r](f s)` with `f s ∈ bin_values[r]`, and
`V` is the set of the values `f s`. -/
def AuxQuorum (t : ℕ) (ib : P → Set Msg) (r : ℕ) (V : Finset Bool) : Prop :=
  ∃ (S : Finset P) (f : P → Bool), S.card = Fintype.card P - t ∧
    (∀ s ∈ S, Msg.aux r (f s) ∈ ib s ∧ BinVal t ib r (f s)) ∧ S.image f = V

/-- Lines 06–11 of Figure 2: from `values = V` and the coin `s`, the new estimate and whether
`values` was a singleton (line 07). -/
def nextEst (V : Finset Bool) (s : Bool) : Bool × Bool :=
  if true ∈ V ∧ false ∈ V then (s, false) else if true ∈ V then (true, true) else (false, true)

/-- Broadcast guards of Figures 1–2 (input `x`, coin sequence `coin`). -/
def sendG (t : ℕ) (coin : ℕ → Bool) (x : Bool) (ib : P → Set Msg) (out : Set Msg) :
    Msg → Prop
  -- Figure 1, lines 02–03: echo `B_VAL[r](v)` once received from `t + 1` processes, if not yet
  -- broadcast.
  | .bval r v none => t + 1 ≤ bvCnt ib r v ∧ ∀ d, Msg.bval r v d ∉ out
  -- Figure 2, lines 01–02 of round 1: `BV_broadcast EST[1](x)`.
  | .bval 0 _ (some _) => False
  | .bval 1 v (some d) => v = x ∧ d = false ∧ ∀ m ∈ out, ¬ IsEst 1 m
  -- Figure 2, lines 05–11 of round `r + 1` and lines 01–02 of round `r + 2`.
  | .bval (r + 2) v (some d) => (∃ w, Msg.aux (r + 1) w ∈ out) ∧ (∀ m ∈ out, ¬ IsEst (r + 2) m) ∧
      ∃ V, AuxQuorum t ib (r + 1) V ∧ nextEst V (coin (r + 1)) = (v, d)
  -- Figure 2, lines 03–04.
  | .aux r w => (∃ v d, Msg.bval r v (some d) ∈ out) ∧ BinVal t ib r w ∧ ∀ m ∈ out, ¬ IsAux r m

/-- Decision guard (Figure 2, line 08). -/
def decideG (coin : ℕ → Bool) (out : Set Msg) (o : Bool) : Prop :=
  ∃ r, Msg.bval (r + 1) o (some true) ∈ out ∧ coin r = o

/-- The algorithm of Figure 2 (on top of Figure 1) with resilience parameter `t` and common coin
`coin`, as a broadcast protocol with binary inputs and outputs. -/
def mmr (t : ℕ) (coin : ℕ → Bool) : Protocol P Msg Bool Bool where
  send _ x ib out m := sendG t coin x ib out m
  decide _ _ _ out o := decideG coin out o

/-! ### Basic facts -/

theorem nextEst_false {V : Finset Bool} {s v : Bool} (h : nextEst V s = (v, false)) : v = s := by
  unfold nextEst at h
  split_ifs at h <;> simp_all

theorem nextEst_true {V : Finset Bool} {s v : Bool} (h : nextEst V s = (v, true)) :
    ∀ w ∈ V, w = v := by
  unfold nextEst at h
  split_ifs at h with h1 h2
  · simp at h
  · simp only [Prod.mk.injEq, and_true] at h
    subst h
    intro w hw
    cases w
    · exact absurd ⟨h2, hw⟩ h1
    · rfl
  · simp only [Prod.mk.injEq, and_true] at h
    subst h
    intro w hw
    cases w
    · rfl
    · exact absurd hw h2

theorem nextEst_of_subset {V : Finset Bool} {s v : Bool} (hV : V.Nonempty) (h : ∀ w ∈ V, w = v) :
    nextEst V s = (v, true) := by
  obtain ⟨w, hw⟩ := hV
  have hwv := h w hw
  subst hwv
  unfold nextEst
  cases w
  · have : true ∉ V := fun h' => absurd (h _ h') (by decide)
    simp [this]
  · have : false ∉ V := fun h' => absurd (h _ h') (by decide)
    simp [this, hw]

omit [Fintype P] in
theorem BinVal.mono [Finite P] {t : ℕ} {ib ib' : P → Set Msg} (h : ∀ s, ib s ⊆ ib' s) {r : ℕ}
    {v : Bool} (hv : BinVal t ib r v) : BinVal t ib' r v :=
  le_trans hv (cntP_mono h _)

theorem AuxQuorum.mono {t : ℕ} {ib ib' : P → Set Msg} (h : ∀ s, ib s ⊆ ib' s) {r : ℕ}
    {V : Finset Bool} (hV : AuxQuorum t ib r V) : AuxQuorum t ib' r V := by
  obtain ⟨S, f, hS, hf, rfl⟩ := hV
  exact ⟨S, f, hS, fun s hs => ⟨h s (hf s hs).1, (hf s hs).2.mono h⟩, rfl⟩

theorem AuxQuorum.nonempty {t : ℕ} (ht : t < Fintype.card P) {ib : P → Set Msg} {r : ℕ}
    {V : Finset Bool} (hV : AuxQuorum t ib r V) : V.Nonempty := by
  obtain ⟨S, f, hS, -, rfl⟩ := hV
  rw [Finset.image_nonempty, ← Finset.card_pos]
  omega

end Podc.SignatureFreeBA
