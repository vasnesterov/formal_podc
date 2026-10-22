import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Model

/-!
# Generalized quorum systems (Naser-Pastoriza, Chockler, Gotsman, Ryabinin, PODC 2025, §3)

* `Available f Q` (*f-availability*): all members of `Q` are correct and mutually reachable in the
  residual graph `G \ f` (paths may leave `Q`; see `differencies.md`).
* `ReachableFrom f W R` (*f-reachability*): members of `W` and `R` are correct and every member of
  `R` reaches every member of `W` in `G \ f`.
* `IsGQS F R W` (Definition 2) and the classical `IsQS F R W` (Definition 1); they coincide when
  `F` has no channel failures (`isGQS_iff_isQS`).
* `U R W f` (the union of the write quorums validating Availability for `f`) and `Uf R W f` (its
  strongly connected component in `G \ f`); Proposition 1 (`proposition_1`).
-/

namespace Podc.GeneralizedQuorums

open Cslib.ChannelFailures

variable {P : Type}

/-- `Q` is `f`-available: its members are correct and strongly connected in `G \ f`. -/
def Available (f : FailurePattern P) (Q : Set P) : Prop := ∀ u ∈ Q, ∀ v ∈ Q, f.Reach u v

/-- `W` is `f`-reachable from `R`. -/
def ReachableFrom (f : FailurePattern P) (W R : Set P) : Prop :=
  (∀ w ∈ W, w ∉ f.procs) ∧ (∀ r ∈ R, r ∉ f.procs) ∧ ∀ r ∈ R, ∀ w ∈ W, f.Reach r w

/-- **Definition 2.** A generalized quorum system `(F, R, W)`. -/
structure IsGQS (F : Set (FailurePattern P)) (R W : Set (Set P)) : Prop where
  /-- Every read quorum intersects every write quorum. -/
  consistency : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty
  /-- For every failure pattern some write quorum is available and reachable from some read
  quorum. -/
  availability : ∀ f ∈ F, ∃ w ∈ W, ∃ r ∈ R, Available f w ∧ ReachableFrom f w r

/-- **Definition 1.** A classical quorum system (for fail-prone systems without channel failures
between correct processes). -/
structure IsQS (F : Set (FailurePattern P)) (R W : Set (Set P)) : Prop where
  /-- Every read quorum intersects every write quorum. -/
  consistency : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty
  /-- For every failure pattern some read and some write quorum consist of correct processes. -/
  availability : ∀ f ∈ F, ∃ r ∈ R, ∃ w ∈ W, ∀ p ∈ r ∪ w, p ∉ f.procs

/-- The union `U` of the write quorums that validate Availability for `f` (§3). -/
def U (R W : Set (Set P)) (f : FailurePattern P) : Set P :=
  ⋃₀ {w | w ∈ W ∧ Available f w ∧ ∃ r ∈ R, ReachableFrom f w r}

/-- `U_f`: the strongly connected component of `G \ f` containing `U` (§3). -/
def Uf (R W : Set (Set P)) (f : FailurePattern P) : Set P :=
  {p | ∃ u ∈ U R W f, f.Reach u p ∧ f.Reach p u}

lemma reach_trans {f : FailurePattern P} {a b c : P} (h₁ : f.Reach a b) (h₂ : f.Reach b c) :
    f.Reach a c := Digraph.ReachableAvoiding.trans h₁ h₂

lemma reach_refl {f : FailurePattern P} {a : P} (h : a ∉ f.procs) : f.Reach a a :=
  Digraph.ReachableAvoiding.refl h

lemma Reach.left_notMem {f : FailurePattern P} {a b : P} (h : f.Reach a b) : a ∉ f.procs :=
  Digraph.ReachableAvoiding.notMem_left h

lemma Reach.right_notMem {f : FailurePattern P} {a b : P} (h : f.Reach a b) : b ∉ f.procs :=
  Digraph.ReachableAvoiding.notMem_right h

/-- A correct process reaches its successors along edges of `G \ f`. -/
lemma reach_of_edge {f : FailurePattern P} {a b : P} (h : f.Edge a b) : f.Reach a b :=
  Digraph.ReachableAvoiding.tail (reach_refl h.1) h.2.2 h.2.1

lemma Reach.head {f : FailurePattern P} {a b c : P} (h : f.Edge a b) (h' : f.Reach b c) :
    f.Reach a c := reach_trans (reach_of_edge h) h'

lemma Reach.tail {f : FailurePattern P} {a b c : P} (h' : f.Reach a b) (h : f.Edge b c) :
    f.Reach a c := reach_trans h' (reach_of_edge h)

/-- **Proposition 1.** The union `U` of the write quorums validating Availability for `f` is
strongly connected in `G \ f` (only Consistency is needed). -/
theorem proposition_1 {F : Set (FailurePattern P)} {R W : Set (Set P)} (hQ : IsGQS F R W)
    (f : FailurePattern P) : ∀ p₁ ∈ U R W f, ∀ p₂ ∈ U R W f, f.Reach p₁ p₂ := by
  rintro p₁ ⟨W₁, ⟨hW₁, hav₁, R₁, hR₁, hr₁⟩, hp₁⟩ p₂ ⟨W₂, ⟨hW₂, hav₂, R₂, hR₂, hr₂⟩, hp₂⟩
  obtain ⟨q, hqR, hqW⟩ := hQ.consistency R₂ hR₂ W₁ hW₁
  exact reach_trans (hav₁ p₁ hp₁ q hqW) (hr₂.2.2 q hqR p₂ hp₂)

lemma subset_Uf (R W : Set (Set P)) (f : FailurePattern P) : U R W f ⊆ Uf R W f := by
  rintro p ⟨w, hw, hp⟩
  exact ⟨p, ⟨w, hw, hp⟩, hw.2.1 p hp p hp, hw.2.1 p hp p hp⟩

/-- `U_f` is strongly connected in `G \ f`. -/
theorem Uf_stronglyConnected {F : Set (FailurePattern P)} {R W : Set (Set P)} (hQ : IsGQS F R W)
    (f : FailurePattern P) : ∀ p₁ ∈ Uf R W f, ∀ p₂ ∈ Uf R W f, f.Reach p₁ p₂ := by
  rintro p₁ ⟨u₁, hu₁, -, h₁⟩ p₂ ⟨u₂, hu₂, h₂, -⟩
  exact reach_trans h₁ (reach_trans (proposition_1 hQ f u₁ hu₁ u₂ hu₂) h₂)

/-- `U_f` is non-empty for `f ∈ F`. -/
theorem Uf_nonempty {F : Set (FailurePattern P)} {R W : Set (Set P)} (hQ : IsGQS F R W)
    {f : FailurePattern P} (hf : f ∈ F) : (Uf R W f).Nonempty := by
  obtain ⟨w, hw, r, hr, hav, hre⟩ := hQ.availability f hf
  obtain ⟨p, -, hp⟩ := hQ.consistency r hr w hw
  exact ⟨p, subset_Uf R W f ⟨w, ⟨hw, hav, r, hr, hre⟩, hp⟩⟩

/-- `U_f` is maximal: whatever is strongly connected to it lies in it. -/
theorem mem_Uf_of_reach {R W : Set (Set P)} {f : FailurePattern P} {p q : P}
    (hq : q ∈ Uf R W f) (h₁ : f.Reach p q) (h₂ : f.Reach q p) : p ∈ Uf R W f := by
  obtain ⟨u, hu, hu₁, hu₂⟩ := hq
  exact ⟨u, hu, reach_trans hu₁ h₂, reach_trans h₁ hu₂⟩

/-- Without channel failures, any two correct processes are adjacent in `G \ f`. -/
lemma reach_of_chans_empty {f : FailurePattern P} (hf : f.chans = ∅) {a b : P}
    (ha : a ∉ f.procs) (hb : b ∉ f.procs) : f.Reach a b :=
  reach_of_edge ⟨ha, hb, by simp [hf]⟩

/-- **§3, after Definition 2.** If `F` has no channel failures, Definition 2 is equivalent to
Definition 1. -/
theorem isGQS_iff_isQS {F : Set (FailurePattern P)} (hF : ∀ f ∈ F, f.chans = ∅)
    {R W : Set (Set P)} : IsGQS F R W ↔ IsQS F R W := by
  constructor
  · intro h
    refine ⟨h.consistency, fun f hf => ?_⟩
    obtain ⟨w, hw, r, hr, -, hw', hr', -⟩ := h.availability f hf
    exact ⟨r, hr, w, hw, fun p hp => hp.elim (hr' p) (hw' p)⟩
  · intro h
    refine ⟨h.consistency, fun f hf => ?_⟩
    obtain ⟨r, hr, w, hw, hc⟩ := h.availability f hf
    have hw' : ∀ p ∈ w, p ∉ f.procs := fun p hp => hc p (Or.inr hp)
    have hr' : ∀ p ∈ r, p ∉ f.procs := fun p hp => hc p (Or.inl hp)
    exact ⟨w, hw, r, hr, fun u hu v hv => reach_of_chans_empty (hF f hf) (hw' u hu) (hw' v hv),
      hw', hr', fun a ha b hb => reach_of_chans_empty (hF f hf) (hr' a ha) (hw' b hb)⟩

end Podc.GeneralizedQuorums
