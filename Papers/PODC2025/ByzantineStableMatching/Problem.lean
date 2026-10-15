import Mathlib
import Cslib.Computability.Distributed.Byzantine.LockStep.Auth
import Cslib.Algorithms.Lean.StableMatching.GaleShapley

/-!
# Byzantine stable matching: problem definitions

Constantinescu, Dufay, Ghinea, Wattenhofer, *Byzantine Stable Matching*, PODC 2025 (arXiv 2502.05889).

Parties are `Party k = Fin k ⊕ Fin k`: `inl i` is the `i`-th party of `L`, `inr j` the `j`-th party
of `R`. Outputs are `Option (Fin k)`: `some j` means "match with the `j`-th party of the other side",
`none` means "match with nobody".

* `bSM`: inputs are preference lists `π : Equiv.Perm (Fin k)` (`π 0` is the favourite);
* `sSM`: inputs are favourites `Fin k`;
* networks: `fully`, `oneSided` (all pairs except inside `L`), `bipartite` (only `L × R` pairs);
* adversary structure `thresholds k tL tR`: at most `tL` Byzantine parties in `L`, `tR` in `R`.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

/-- The parties: `L = range inl`, `R = range inr`. -/
abbrev Party (k : ℕ) := Fin k ⊕ Fin k

variable {k : ℕ}

/-! ## Networks -/

/-- Fully-connected network. -/
def fully (k : ℕ) : SimpleGraph (Party k) := ⊤

/-- One-sided network: all pairs except pairs inside `L` are connected. -/
def oneSided (k : ℕ) : SimpleGraph (Party k) where
  Adj p q := p ≠ q ∧ (p.isRight ∨ q.isRight)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Bipartite network: only pairs `L × R` are connected. -/
def bipartite (k : ℕ) : SimpleGraph (Party k) where
  Adj p q := p.isLeft ≠ q.isLeft
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

/-- One-sided network with the roles of the sides swapped (`R` disconnected). -/
def oneSidedR (k : ℕ) : SimpleGraph (Party k) where
  Adj p q := p ≠ q ∧ (p.isLeft ∨ q.isLeft)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] lemma fully_adj (p q : Party k) : (fully k).Adj p q ↔ p ≠ q := Iff.rfl
@[simp] lemma oneSided_adj (p q : Party k) :
    (oneSided k).Adj p q ↔ p ≠ q ∧ (p.isRight ∨ q.isRight) := Iff.rfl
@[simp] lemma oneSidedR_adj (p q : Party k) :
    (oneSidedR k).Adj p q ↔ p ≠ q ∧ (p.isLeft ∨ q.isLeft) := Iff.rfl
@[simp] lemma bipartite_adj (p q : Party k) : (bipartite k).Adj p q ↔ p.isLeft ≠ q.isLeft := Iff.rfl

lemma bipartite_le_oneSided : bipartite k ≤ oneSided k := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q <;> simp_all

lemma bipartite_le_oneSidedR : bipartite k ≤ oneSidedR k := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q <;> simp_all

lemma oneSided_le_fully : oneSided k ≤ fully k := fun _ _ h => h.1

/-! ## Adversary -/

/-- At most `tL` Byzantine parties in `L` and at most `tR` in `R`. -/
def thresholds (k tL tR : ℕ) : AdvStructure (Party k) :=
  {B | (inl ⁻¹' B).ncard ≤ tL ∧ (inr ⁻¹' B).ncard ≤ tR}

/-! ## Specifications -/

/-- The output index `j` of party `p` denotes this party (on the other side). -/
def partner : Party k → Fin k → Party k
  | inl _, j => inr j
  | inr _, j => inl j

/-- Termination, symmetry and non-competition (common to `bSM` and `sSM`). -/
structure CommonProps (H : Set (Party k)) (dec : Party k → Option (Fin k) → Prop) : Prop where
  /-- Every honest party outputs a party of the other side or nobody. -/
  termination : ∀ p ∈ H, ∃ o, dec p o
  /-- Honest `u` decides to match honest `v` iff `v` decides to match `u`. -/
  symmetry : ∀ i j, inl i ∈ H → inr j ∈ H → (dec (inl i) (some j) ↔ dec (inr j) (some i))
  /-- Two distinct honest parties never output the same party. -/
  nonCompetition : ∀ p q, p ∈ H → q ∈ H → p ≠ q → ∀ z z',
    dec p (some z) → dec q (some z') → partner p z ≠ partner q z'

/-- `a` is preferred to the current match `o` according to the list `π` (anybody beats nobody). -/
def Prefers (π : Equiv.Perm (Fin k)) (a : Fin k) : Option (Fin k) → Prop
  | none => True
  | some b => π.symm a < π.symm b

/-- **Definition 1** (Byzantine stable matching). -/
def bSM (k : ℕ) : Spec (Party k) (Equiv.Perm (Fin k)) (Option (Fin k)) := fun x H dec =>
  CommonProps H dec ∧
  -- Stability: no blocking pair of honest parties.
  ∀ i j oi oj, inl i ∈ H → inr j ∈ H → dec (inl i) oi → dec (inr j) oj →
    ¬ (Prefers (x (inl i)) j oi ∧ Prefers (x (inr j)) i oj)

/-- **Simplified stable matching** (Section 3): inputs are favourites. -/
def sSM (k : ℕ) : Spec (Party k) (Fin k) (Option (Fin k)) := fun x H dec =>
  CommonProps H dec ∧
  -- Simplified stability: honest mutual favourites output each other.
  ∀ i j, inl i ∈ H → inr j ∈ H → x (inl i) = j → x (inr j) = i →
    dec (inl i) (some j) ∧ dec (inr j) (some i)

/-! ## Lemma 2: sSM reduces to bSM -/

/-- A preference list ranking `f` first. -/
def favList [NeZero k] (f : Fin k) : Equiv.Perm (Fin k) := Equiv.swap 0 f

lemma favList_symm_self [NeZero k] (f : Fin k) : (favList f).symm f = 0 := by
  simp [favList, Equiv.swap_apply_right]

lemma favList_symm_pos [NeZero k] {f a : Fin k} (h : a ≠ f) : (0 : Fin k) < (favList f).symm a := by
  rw [Fin.pos_iff_ne_zero]
  intro h0
  apply h
  have : favList f 0 = a := by rw [← h0]; simp
  simpa [favList] using this.symm

/-- Every algorithm solving bSM, run on the favourite-first lists, solves sSM. -/
lemma sSM_of_bSM [NeZero k] (x : Party k → Fin k) (H : Set (Party k))
    (dec : Party k → Option (Fin k) → Prop)
    (h : bSM k (fun p => favList (x p)) H dec) : sSM k x H dec := by
  obtain ⟨hc, hst⟩ := h
  refine ⟨hc, fun i j hi hj hxi hxj => ?_⟩
  obtain ⟨oi, hoi⟩ := hc.termination _ hi
  obtain ⟨oj, hoj⟩ := hc.termination _ hj
  have hnb := hst i j oi oj hi hj hoi hoj
  -- one of them is matched to the other, otherwise they block
  have : oi = some j ∨ oj = some i := by
    by_contra hcon
    push Not at hcon
    apply hnb
    constructor
    · cases oi with
      | none => trivial
      | some b =>
        have hb : b ≠ j := fun e => hcon.1 (by rw [e])
        show (favList (x (inl i))).symm j < (favList (x (inl i))).symm b
        rw [hxi, favList_symm_self]; exact favList_symm_pos hb
    · cases oj with
      | none => trivial
      | some b =>
        have hb : b ≠ i := fun e => hcon.2 (by rw [e])
        show (favList (x (inr j))).symm i < (favList (x (inr j))).symm b
        rw [hxj, favList_symm_self]; exact favList_symm_pos hb
  rcases this with rfl | rfl
  · exact ⟨hoi, (hc.symmetry i j hi hj).mp hoi⟩
  · exact ⟨(hc.symmetry i j hi hj).mpr hoj, hoj⟩

/-- **Lemma 2** (unauthenticated): if bSM is solvable then sSM is solvable (on the same network,
against the same adversary structure). -/
theorem lemma2 [NeZero k] {G : SimpleGraph (Party k)} {Z : AdvStructure (Party k)}
    (h : Solvable G Z (bSM k)) : Solvable G Z (sSM k) := by
  obtain ⟨M, alg, halg⟩ := h
  refine ⟨M, alg.comapInput favList, fun s hZ hrel => ?_⟩
  have := halg (s.mapInput favList) hZ hrel
  have e : Decides G (alg.comapInput favList) s = Decides G alg (s.mapInput favList) := by
    funext p o; exact propext (decides_comapInput G alg favList s p o)
  exact sSM_of_bSM s.input s.honest _ (by rw [e]; exact this)

/-- **Lemma 2** (authenticated). -/
theorem lemma2_auth [NeZero k] {G : SimpleGraph (Party k)} {Z : AdvStructure (Party k)}
    (h : SolvableAuth G Z (bSM k)) : SolvableAuth G Z (sSM k) := by
  obtain ⟨M, S, A, alg, hU, halg⟩ := h
  refine ⟨M, S, A, alg.comapInput favList, hU.comapInput favList, fun s hZ hrel hV => ?_⟩
  have := halg (s.mapInput favList) hZ hrel ((Scenario.authValid_comapInput favList s).mp hV)
  have e : Decides G (alg.comapInput favList) s = Decides G alg (s.mapInput favList) := by
    funext p o; exact propext (decides_comapInput G alg favList s p o)
  exact sSM_of_bSM s.input s.honest _ (by rw [e]; exact this)

end Papers.PODC2025.ByzantineStableMatching
