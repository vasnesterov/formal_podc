import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Auxiliary lemmas for the max-array linearizability criterion

* `invPos α x` / `retPos α x`: the length of the shortest prefix of `α` in which `x` is invoked /
  has returned (`α.length + 1` if never); real-time order is `retPos a < invPos b`
  (`precedes_iff_retPos_lt_invPos`).
* `exists_isLinearization_of_key`: a history is linearizable if there is a set `X` of invoked
  instances containing all completed ones and a key `κ` into a linear order that is monotone along
  real-time order on `X` and for which the legality condition holds when the instances of `X` are
  executed in key order.
-/

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {A : ObjSpec}

section Positions

open Classical in
/-- The length of the shortest prefix of `α` in which `x` is invoked (`α.length + 1` if `x` is
never invoked). -/ -- CSLib candidate
noncomputable def invPos (α : List (Label P A)) (x : OpId P) : ℕ :=
  Nat.find (p := fun n => Invoked (α.take n) x ∨ α.length < n)
    ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩

open Classical in
/-- The length of the shortest prefix of `α` in which `x` has returned (`α.length + 1` if `x`
never returns). -/ -- CSLib candidate
noncomputable def retPos (α : List (Label P A)) (x : OpId P) : ℕ :=
  Nat.find (p := fun n => Completed (α.take n) x ∨ α.length < n)
    ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩

lemma invoked_take_mono {α : List (Label P A)} {x : OpId P} {m n : ℕ} (hmn : m ≤ n)
    (h : Invoked (α.take m) x) : Invoked (α.take n) x := by
  obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := α) hmn
  rw [← ht]; exact h.mono

lemma completed_take_mono {α : List (Label P A)} {x : OpId P} {m n : ℕ} (hmn : m ≤ n)
    (h : Completed (α.take m) x) : Completed (α.take n) x := by
  obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := α) hmn
  rw [← ht]; exact h.mono

lemma invoked_take_of_invPos_le {α : List (Label P A)} {x : OpId P} {n : ℕ}
    (h : invPos α x ≤ n) (hn : n ≤ α.length) : Invoked (α.take n) x := by
  classical
  have hs := Nat.find_spec (p := fun n => Invoked (α.take n) x ∨ α.length < n)
    ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩
  rcases hs with hs | hs
  · exact invoked_take_mono (by convert h using 1; unfold invPos; congr) hs
  · exfalso
    have : invPos α x = Nat.find (p := fun n => Invoked (α.take n) x ∨ α.length < n)
      ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩ := by unfold invPos; congr
    omega

lemma completed_take_retPos {α : List (Label P A)} {x : OpId P} (h : Completed α x) :
    Completed (α.take (retPos α x)) x ∧ retPos α x ≤ α.length := by
  classical
  have e : retPos α x = Nat.find (p := fun n => Completed (α.take n) x ∨ α.length < n)
      ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩ := by unfold retPos; congr
  have hle : retPos α x ≤ α.length := by
    rw [e]; exact Nat.find_min' _ (Or.inl (by simpa using h))
  have hs := Nat.find_spec (p := fun n => Completed (α.take n) x ∨ α.length < n)
    ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩
  rw [← e] at hs
  exact ⟨hs.resolve_right (by omega), hle⟩

lemma retPos_le_of_completed_take {α : List (Label P A)} {x : OpId P} {n : ℕ}
    (h : Completed (α.take n) x) : retPos α x ≤ n := by
  classical
  have e : retPos α x = Nat.find (p := fun n => Completed (α.take n) x ∨ α.length < n)
      ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩ := by unfold retPos; congr
  rw [e]; exact Nat.find_min' _ (Or.inl h)

lemma invPos_le_of_invoked_take {α : List (Label P A)} {x : OpId P} {n : ℕ}
    (h : Invoked (α.take n) x) : invPos α x ≤ n := by
  classical
  have e : invPos α x = Nat.find (p := fun n => Invoked (α.take n) x ∨ α.length < n)
      ⟨α.length + 1, Or.inr (Nat.lt_succ_self _)⟩ := by unfold invPos; congr
  rw [e]; exact Nat.find_min' _ (Or.inl h)

/-- Real-time order in terms of positions. -/ -- CSLib candidate
lemma precedes_iff_retPos_lt_invPos {α : List (Label P A)} {a b : OpId P} :
    Precedes α a b ↔ Completed α a ∧ retPos α a < invPos α b := by
  constructor
  · intro h
    refine ⟨h.completed, ?_⟩
    obtain ⟨β, γ, rfl, ha, hb⟩ := h
    have hβ : (β ++ γ).take β.length = β := by simp
    have h1 : retPos (β ++ γ) a ≤ β.length := retPos_le_of_completed_take (by rwa [hβ])
    by_contra hc
    have : Invoked ((β ++ γ).take β.length) b :=
      invoked_take_of_invPos_le (by omega) (by simp)
    rw [hβ] at this
    exact hb this
  · rintro ⟨hc, hlt⟩
    obtain ⟨h1, h2⟩ := completed_take_retPos hc
    refine ⟨α.take (retPos α a), α.drop (retPos α a), (List.take_append_drop _ _).symm, h1, ?_⟩
    intro hi
    have := invPos_le_of_invoked_take hi
    omega

/-- An instance returns after it is invoked (well-formed histories). -/
lemma invPos_le_retPos {α : List (Label P A)} (hwf : WellFormed α) {x : OpId P}
    (h : Completed α x) : invPos α x ≤ retPos α x := by
  obtain ⟨h1, -⟩ := completed_take_retPos h
  have hwf' : WellFormed (α.take (retPos α x)) := by
    have := List.take_append_drop (retPos α x) α
    rw [← this] at hwf
    exact hwf.of_append
  exact invPos_le_of_invoked_take (hwf'.invoked_of_completed h1)

end Positions

section Bridge

/-- Legality from a description of every prefix ending in a completed instance. -/
lemma seqOK_of_split {α : List (Label P A)} {q : A.State} {L : List (OpId P × A.Op)}
    (h : ∀ L₁ x o L₂, L = L₁ ++ (x, o) :: L₂ → ∀ r, respOf α x = some r →
      (A.δ (A.runOps q (L₁.map Prod.snd)) o).2 = r) :
    SeqOK α q L := by
  induction L generalizing q with
  | nil => trivial
  | cons y L ih =>
    obtain ⟨x, o⟩ := y
    refine ⟨fun r hr => by simpa using h [] x o L (by simp) r hr, ih fun L₁ x' o' L₂ e r hr => ?_⟩
    simpa using h ((x, o) :: L₁) x' o' L₂ (by simp [e]) r hr

lemma map_fst_filterMap_opOf {α : List (Label P A)} {l : List (OpId P)}
    (h : ∀ x ∈ l, Invoked α x) :
    (l.filterMap (fun x => (opOf α x).map (x, ·))).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x (by simp)
    have : opOf α x = some ((opsOf α x.1)[x.2]'hx) := by
      simp [opOf, List.getElem?_eq_getElem hx]
    simp [this, ih fun y hy => h y (by simp [hy])]

/-- **Linearization by keys.** Let `X` be a set of invoked instances containing every completed
one, and `κ` a key into a linear order that is monotone along the real-time order on `X`. If
every completed instance `x ∈ X` gets its actual response when executed after any sequence `L₁`
of instances of `X` with key `≤ κ x` that contains all instances of `X` with key `< κ x`
(sorted by key), then the history is linearizable (sort `X` by key, ties broken by invocation
order). -/ -- CSLib candidate
theorem exists_isLinearization_of_key {K : Type} [LinearOrder K]
    (α : List (Label P A)) (hwf : WellFormed α) (X : OpId P → Prop) (κ : OpId P → K)
    (hX : ∀ x, X x → Invoked α x) (hC : ∀ x, Completed α x → X x)
    (hrt : ∀ a b, Precedes α a b → X b → κ a ≤ κ b)
    (hseq : ∀ (L₁ : List (OpId P × A.Op)) x o r, X x → opOf α x = some o →
      respOf α x = some r →
      (∀ y ∈ L₁, opOf α y.1 = some y.2 ∧ X y.1 ∧ κ y.1 ≤ κ x) →
      (∀ y, X y → κ y < κ x → y ∈ L₁.map Prod.fst) →
      (L₁.map Prod.fst).Pairwise (fun a b => κ a ≤ κ b) →
      (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).2 = r) :
    ∃ L, IsLinearization α L := by
  classical
  set le : OpId P → OpId P → Bool := fun a b => decide (κ a ≤ κ b) with hle
  have htrans : ∀ a b c, le a b → le b c → le a c := by
    intro a b c h1 h2; simp only [hle, decide_eq_true_eq] at *; exact h1.trans h2
  have htot : ∀ a b, (le a b || le b a) = true := by
    intro a b; simp only [hle, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _
  set l₀ := (invIds α).filter (fun x => decide (X x)) with hl₀
  set l := l₀.mergeSort le with hl
  have hmem : ∀ x, x ∈ l ↔ X x := by
    intro x
    simp only [hl, List.mem_mergeSort, hl₀, List.mem_filter, mem_invIds, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hX x h, h⟩⟩
  have hnd : l.Nodup := (List.mergeSort_perm l₀ le).nodup_iff.2
    ((nodup_invIds α).filter _)
  have hsort : l.Pairwise (fun a b => κ a ≤ κ b) := by
    have := List.pairwise_mergeSort htrans htot l₀
    exact this.imp fun h => by simpa [hle] using h
  set L := l.filterMap (fun x => (opOf α x).map (x, ·)) with hL
  have hLf : L.map Prod.fst = l := map_fst_filterMap_opOf fun x hx => hX x ((hmem x).1 hx)
  have hLop : ∀ y ∈ L, opOf α y.1 = some y.2 := by
    intro y hy
    simp only [hL, List.mem_filterMap, Option.map_eq_some_iff] at hy
    obtain ⟨x, -, o, ho, rfl⟩ := hy
    exact ho
  refine ⟨L, ⟨by rw [hLf]; exact hnd, hLop, fun a ha => by rw [hLf, hmem]; exact hC a ha,
    fun a b hab hb => ?_, ?_⟩⟩
  · rw [hLf] at hb ⊢
    have hXb := (hmem b).1 hb
    have hXa := hC a hab.completed
    have h1 : [a, b].Sublist (invIds α) := hab.sublist_invIds (hX b hXb) hwf
    have h2 : [a, b].Sublist l₀ := by
      have := h1.filter (fun x => decide (X x))
      simpa [List.filter_cons, hXa, hXb] using this
    exact List.pair_sublist_mergeSort htrans htot (by simpa [hle] using hrt a b hab hXb) h2
  · apply seqOK_of_split
    intro L₁ x o L₂ e r hr
    have hl' : l = L₁.map Prod.fst ++ x :: L₂.map Prod.fst := by
      rw [← hLf, e]; simp
    have hxl : x ∈ l := by rw [hl']; simp
    have hxo : opOf α x = some o := hLop (x, o) (by rw [e]; simp)
    rw [hl'] at hsort
    rw [List.pairwise_append] at hsort
    obtain ⟨hs1, hs2, hs3⟩ := hsort
    apply hseq L₁ x o r ((hmem x).1 hxl) hxo hr
    · intro y hy
      refine ⟨hLop y (by rw [e]; simp [hy]), (hmem _).1 ?_, hs3 _ (by simp; exact ⟨_, hy⟩) _
        (by simp)⟩
      rw [hl']; simp; exact Or.inl ⟨_, hy⟩
    · intro y hy hlt
      have hyl := (hmem y).2 hy
      rw [hl'] at hyl
      simp only [List.mem_append, List.mem_cons] at hyl
      rcases hyl with h | rfl | h
      · exact h
      · exact absurd hlt (lt_irrefl _)
      · rw [List.pairwise_cons] at hs2
        exact absurd (hs2.1 y h) (not_le.2 hlt)
    · exact hs1

end Bridge

end Podc.LimitedUseSnapshots
