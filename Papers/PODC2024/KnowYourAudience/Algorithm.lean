import Papers.PODC2024.KnowYourAudience.Decode

/-!
# The view-based algorithm

Each agent stores its view: after round `t` its state is `⟨t, (input, R)⟩` where `R` is the multiset
of the depth-`(t-1)` views received from its in-neighbours. In round `t + 1` it sends its depth-`t`
view, tagged with `dd (outdegree)` (`dd = id`: outdegree awareness; `dd = 0`: simple broadcast /
symmetric communications). From round `t + 2 ≥ 2` on, it decodes (`decodeQ`) its view at depth
`s + 1 = ⌊t/2⌋ + 1` with lookahead `K = t - ⌊t/2⌋` (`classes`, `solve`), and its output is any
function `G` of its state and of the decoded multiset.

* `run_viewAlg`: the state of agent `i` after round `t` (the algorithm builds views).
* `viewAlg_decode`: eventually every agent decodes a nonempty multiset `u` with
  `n • u = |u| • ⟦x⟧`, i.e. `u` has the frequencies of the input vector (the core of the
  positive results of Section 4).
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset Filter

open scoped Classical

universe u v

variable {I : Type u} {X : Type v}

/-- The state after `t` rounds. -/
def St (I : Type u) : ℕ → Type u
  | 0 => I
  | t + 1 => I × Multiset (Msg I t)

/-- The input stored in a state. -/
def St.input : (t : ℕ) → St I t → I
  | 0, a => a
  | _ + 1, s => s.1

/-- The view sent by an agent in state `s` with tag `d`. -/
def St.toMsg (d : ℕ) : (t : ℕ) → St I t → Msg I t
  | 0, a => (d, a)
  | _ + 1, s => (d, s.1, s.2)

/-- Keep the received views of the expected depth. -/
def sel (t : ℕ) (m : Σ t', Msg I t') : Option (Msg I t) :=
  if h : m.1 = t then some (h ▸ m.2) else none

lemma sel_self (t : ℕ) (m : Msg I t) : sel t ⟨t, m⟩ = some m := by
  simp [sel]

/-- Transport a multiset of views along an equality of depths. -/
def castMsgs {t t' : ℕ} (h : t = t') (R : Multiset (Msg I t)) : Multiset (Msg I t') := h ▸ R

/-- The decoding of a state (`none` before round 2). -/
noncomputable def decodeQ (b : ∀ s, Msg I (s + 1) → ℕ) : (Σ t, St I t) → Option (Multiset I)
  | ⟨t + 2, s⟩ =>
    solve (t / 2) (b (t / 2)) (classes (t / 2) (t - t / 2) (castMsgs (by omega) s.2))
  | _ => none

/-- The view-based algorithm with tag function `dd` and output map `G`. -/
noncomputable def viewAlg (dd : ℕ → ℕ) (b : ∀ s, Msg I (s + 1) → ℕ)
    (G : (Σ t, St I t) → Option (Multiset I) → X) : Algorithm I X where
  Q := Σ t, St I t
  M := Σ t, Msg I t
  init a := ⟨0, a⟩
  send q d _ := ⟨q.1, St.toMsg (dd d) q.1 q.2⟩
  trans q R := ⟨q.1 + 1, (St.input q.1 q.2, R.filterMap (sel q.1))⟩
  out q := G q (decodeQ b q)

lemma viewAlg_out (dd : ℕ → ℕ) (b : ∀ s, Msg I (s + 1) → ℕ)
    (G : (Σ t, St I t) → Option (Multiset I) → X) (q : (viewAlg dd b G).Q) :
    (viewAlg dd b G).out q = G q (decodeQ b q) := rfl

lemma viewAlg_allowed_outdegree (b : ∀ s, Msg I (s + 1) → ℕ)
    (G : (Σ t, St I t) → Option (Multiset I) → X) :
    CommModel.outdegree.Allowed (viewAlg id b G) := fun _ _ _ _ => rfl

lemma viewAlg_allowed_outPort (dd : ℕ → ℕ) (b : ∀ s, Msg I (s + 1) → ℕ)
    (G : (Σ t, St I t) → Option (Multiset I) → X) :
    CommModel.outPort.Allowed (viewAlg dd b G) := trivial

lemma viewAlg_allowed_symmetric (b : ∀ s, Msg I (s + 1) → ℕ)
    (G : (Σ t, St I t) → Option (Multiset I) → X) :
    CommModel.symmetric.Allowed (viewAlg (fun _ => 0) b G) := fun _ _ _ _ _ => rfl

variable {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) (x : V → I) (dd : ℕ → ℕ)

/-- The state of agent `i` after round `t`. -/
def stOf : (t : ℕ) → V → St I t
  | 0, i => x i
  | t + 1, i => (x i, (N.inN i).val.map (msg N x dd t))

lemma toMsg_stOf (t : ℕ) (i : V) :
    St.toMsg (dd (N.outdeg i)) t (stOf N x dd t i) = msg N x dd t i := by
  cases t <;> rfl

lemma input_stOf (t : ℕ) (i : V) : St.input t (stOf N x dd t i) = x i := by
  cases t <;> rfl

theorem run_viewAlg (b : ∀ s, Msg I (s + 1) → ℕ) (G : (Σ t, St I t) → Option (Multiset I) → X)
    (t : ℕ) (i : V) : N.run (viewAlg dd b G) x t i = ⟨t, stOf N x dd t i⟩ := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [Network.run, Network.runFrom_succ, ← Network.run]
    simp only [Network.step, Network.recv, ih]
    simp only [viewAlg, input_stOf, toMsg_stOf]
    congr 1
    show (x i, _) = (x i, _)
    congr 1
    rw [Multiset.filterMap_map]
    simp only [Function.comp_def, sel_self]
    rw [← Multiset.filterMap_eq_map]; rfl

lemma castMsgs_map {t t' : ℕ} (h : t = t') (s : Finset V) :
    castMsgs h (s.val.map (msg N x dd t)) = s.val.map (msg N x dd t') := by
  subst h; rfl

omit [DecidableEq V] in
lemma nsmul_eq_of_count {u : Multiset I}
    (h : ∀ a, u.count a * Fintype.card V = (univ.filter fun j => x j = a).card * Multiset.card u) :
    Fintype.card V • u = Multiset.card u • (univ.val.map x) := by
  ext a
  rw [Multiset.count_nsmul, Multiset.count_nsmul, Multiset.count_map, mul_comm, h a, mul_comm]
  congr 2
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro j _; exact eq_comm

/-- **The view-based algorithm computes the input frequencies.** In a strongly connected network,
if `b` reads off the outdegree of an agent from its view, then eventually every agent decodes a
nonempty multiset `u` with `n • u = |u| • ⟦x⟧`. -/
theorem viewAlg_decode [Nonempty V] (hsc : N.StronglyConnected) (b : ∀ s, Msg I (s + 1) → ℕ)
    (hb : ∀ s j, b s (msg N x dd (s + 1) j) = N.outdeg j)
    (G : (Σ t, St I t) → Option (Multiset I) → X) :
    ∀ᶠ t in atTop, ∀ i, ∃ u, decodeQ b (N.run (viewAlg dd b G) x t i) = some u ∧ u ≠ 0 ∧
      Fintype.card V • u = Multiset.card u • (univ.val.map x) := by
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 (eventually_stable N x dd)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (eventually_reachLE N hsc)
  rw [eventually_atTop]
  refine ⟨2 * (s₀ + K₀) + 2, fun t ht i => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
  rw [run_viewAlg]
  set s := t / 2
  set K := t - t / 2
  have hs : s₀ ≤ s := by omega
  have hK : K₀ ≤ K := by omega
  have hdec : decodeQ b ⟨t + 2, stOf N x dd (t + 2) i⟩ =
      solve s (b s) (classes s K ((N.inN i).val.map (msg N x dd (s + 1 + K)))) := by
    show solve s (b s) (classes s K (castMsgs _ ((N.inN i).val.map (msg N x dd (t + 1))))) = _
    rw [castMsgs_map]
  rw [hdec, classes_eq N x dd s K (hK₀ K hK) i]
  obtain ⟨u, hu, hu0, hcount⟩ := solve_correct N x dd hsc s (b s) (hb s) (hs₀ s hs)
  exact ⟨u, hu, hu0, nsmul_eq_of_count x hcount⟩

end Podc.KnowYourAudience
