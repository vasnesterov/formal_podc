import Podc.Foundations.Combinatorics.DiophantineDecomposition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

-- CSLib candidate (generic Petri-net / labelled-multigraph infrastructure)
/-!
# Petri nets with control-states (Section 7 of Leroux)

A Petri net with control-states `(S, T, E)` is abstracted as a finite set `E` of labelled edges
`(s, t, s')` between control-states `s, s' : V`, with labels `t : L`, and a displacement
`δ : L → ℤ^P` of labels. The control-states are a finite set `S` containing all edge endpoints.

Paths are lists of edges (`IsPath E s π s'`), cycles are closed paths, a multicycle is a multiset
of cycles; its Parikh image `parikh Θ` is the multiset of all its edges, its displacement
`mdisp δ Θ` the sum of the displacements of its edges and its length `mlength Θ` the total number
of edges.

## Main statements

* `exists_decomp`: the Parikh image of a path is the Parikh image of a short path plus a
  multicycle of short cycles (length `≤ |S|`).
* `lemma_7_1` (Euler lemma): a total multicycle of a strongly connected net is the Parikh image
  of one cycle, through any given control-state.
* `lemma_7_2`: a total cycle of length `≤ |E||S|` exists.
* `lemma_7_3`: small multicycles with prescribed sign pattern (with the constant
  `|S| (2|S|M)^(2^d − 1)` coming from the weak Pottier bound
  `Cslib.exists_small_decomposition` instead of Pottier's `(1 + 2|S|‖T‖)^(d(d+1))`).
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

variable {V L : Type*} [DecidableEq V] [DecidableEq L]

/-- An edge `(s, t, s')` of a Petri net with control-states. -/
abbrev Edge (V L : Type*) := V × L × V

/-- `π` is a path in `E` from `s` to `s'`. -/
def IsPath (E : Finset (Edge V L)) : V → List (Edge V L) → V → Prop
  | s, [], s' => s = s'
  | s, e :: π, s' => e ∈ E ∧ e.1 = s ∧ IsPath E e.2.2 π s'

/-- `θ` is a cycle (closed path) of `E`. -/
def IsCycle (E : Finset (Edge V L)) (θ : List (Edge V L)) : Prop := ∃ s, IsPath E s θ s

/-- The Parikh image of a multicycle: the multiset of all its edges. -/
def parikh (Θ : Multiset (List (Edge V L))) : Multiset (Edge V L) :=
  (Θ.map fun θ : List (Edge V L) => (θ : Multiset (Edge V L))).sum

/-- The length `|Θ|` of a multicycle. -/
def mlength (Θ : Multiset (List (Edge V L))) : ℕ := (Θ.map List.length).sum

variable {P : Type*} [Fintype P]

/-- The displacement `Δ(π)` of a path. -/
def disp (δ : L → P → ℤ) (π : List (Edge V L)) : P → ℤ := fun p => (π.map fun e => δ e.2.1 p).sum

/-- The displacement `Δ(Θ)` of a multicycle. -/
def mdisp (δ : L → P → ℤ) (Θ : Multiset (List (Edge V L))) : P → ℤ :=
  fun p => (Θ.map fun θ => disp δ θ p).sum

/-- `(S, E)` is strongly connected. -/
def StronglyConnected (E : Finset (Edge V L)) (S : Finset V) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, ∃ π, IsPath E s π s'

/-! ### Paths -/

/-- The control-states visited by the path `π` started at `s`. -/
def verts (s : V) (π : List (Edge V L)) : List V := s :: π.map (fun e => e.2.2)

theorem verts_append (s : V) (α β : List (Edge V L)) :
    verts s (α ++ β) = verts s α ++ β.map (fun e => e.2.2) := by
  simp [verts]

theorem isPath_append {E : Finset (Edge V L)} {u w : V} {α β : List (Edge V L)} :
    IsPath E u (α ++ β) w ↔ ∃ v, IsPath E u α v ∧ IsPath E v β w := by
  induction α generalizing u with
  | nil => simp [IsPath]
  | cons e α ih =>
    simp only [List.cons_append, IsPath, ih]
    constructor
    · rintro ⟨h1, h2, v, h3, h4⟩; exact ⟨v, ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨v, ⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, v, h3, h4⟩

theorem IsPath.mem_E {E : Finset (Edge V L)} {u w : V} {π : List (Edge V L)}
    (h : IsPath E u π w) : ∀ e ∈ π, e ∈ E := by
  induction π generalizing u with
  | nil => simp
  | cons f π ih =>
    obtain ⟨h1, -, h3⟩ := h
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact ih h3 e he

theorem IsPath.verts_mem {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) {u w : V} {π : List (Edge V L)} (hu : u ∈ S)
    (h : IsPath E u π w) : ∀ v ∈ verts u π, v ∈ S := by
  intro v hv
  rcases List.mem_cons.1 hv with rfl | hv
  · exact hu
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
    exact (hE e (h.mem_E e he)).2

theorem IsPath.end_mem_verts {E : Finset (Edge V L)} {u w : V} {π : List (Edge V L)}
    (h : IsPath E u π w) : w ∈ verts u π := by
  induction π generalizing u with
  | nil => exact List.mem_singleton.2 h.symm
  | cons f π ih =>
    obtain ⟨-, -, h3⟩ := h
    exact List.mem_cons_of_mem _ (ih h3)

theorem IsPath.split {E : Finset (Edge V L)} {u v w : V} {π : List (Edge V L)}
    (h : IsPath E u π w) (hv : v ∈ verts u π) :
    ∃ α β, π = α ++ β ∧ IsPath E u α v ∧ IsPath E v β w := by
  induction π generalizing u with
  | nil =>
    have : v = u := List.mem_singleton.1 hv
    exact ⟨[], [], rfl, this.symm, this ▸ h⟩
  | cons f π ih =>
    by_cases hvu : v = u
    · subst hvu; exact ⟨[], f :: π, rfl, rfl, h⟩
    · obtain ⟨h1, h2, h3⟩ := h
      have hv' : v ∈ verts f.2.2 π := by
        rcases List.mem_cons.1 hv with h' | h'
        · exact absurd h' hvu
        · exact h'
      obtain ⟨α, β, rfl, hα, hβ⟩ := ih h3 hv'
      exact ⟨f :: α, β, rfl, ⟨h1, h2, hα⟩, hβ⟩

theorem length_verts (s : V) (π : List (Edge V L)) : (verts s π).length = π.length + 1 := by
  simp [verts]

theorem length_le_card_of_nodup {S : Finset V} {l : List V} (hl : l.Nodup)
    (hS : ∀ v ∈ l, v ∈ S) : l.length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup hl]
  exact Finset.card_le_card fun v hv => hS v (List.mem_toFinset.1 hv)

theorem parikh_zero : parikh (0 : Multiset (List (Edge V L))) = 0 := by simp [parikh]

theorem parikh_cons (θ : List (Edge V L)) (Θ : Multiset (List (Edge V L))) :
    parikh (θ ::ₘ Θ) = (θ : Multiset (Edge V L)) + parikh Θ := by simp [parikh]

theorem parikh_add (Θ Θ' : Multiset (List (Edge V L))) :
    parikh (Θ + Θ') = parikh Θ + parikh Θ' := by simp [parikh]

theorem mem_parikh {e : Edge V L} {Θ : Multiset (List (Edge V L))} :
    e ∈ parikh Θ ↔ ∃ θ ∈ Θ, e ∈ θ := by
  induction Θ using Multiset.induction_on with
  | empty => simp [parikh_zero]
  | cons θ Θ ih => simp [parikh_cons, ih]

/-- Decomposition of a path into a path visiting pairwise distinct control-states and short
cycles. -/
theorem exists_decomp_nodup {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) {s' : V} (π : List (Edge V L)) :
    ∀ s, s ∈ S → IsPath E s π s' →
    ∃ π₀ : List (Edge V L), ∃ Θ : Multiset (List (Edge V L)),
      IsPath E s π₀ s' ∧ (verts s π₀).Nodup ∧ (∀ θ ∈ Θ, IsCycle E θ ∧ θ.length ≤ S.card) ∧
      (π : Multiset (Edge V L)) = (π₀ : Multiset (Edge V L)) + parikh Θ := by
  induction π with
  | nil =>
    intro s _ h
    exact ⟨[], 0, h, by simp [verts], by simp, by simp [parikh_zero]⟩
  | cons e π ih =>
    intro s hs h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨π₀, Θ, hp, hnd, hΘ, heq⟩ := ih e.2.2 (hE e h1).2 h3
    by_cases hsv : s ∈ verts e.2.2 π₀
    · obtain ⟨α, β, rfl, hα, hβ⟩ := hp.split hsv
      rw [verts_append] at hnd
      have hsα : s ∈ verts e.2.2 α := hα.end_mem_verts
      refine ⟨β, (e :: α) ::ₘ Θ, hβ, ?_, ?_, ?_⟩
      · refine List.nodup_cons.2 ⟨fun hs' => ?_, (List.nodup_append.1 hnd).2.1⟩
        exact (List.nodup_append.1 hnd).2.2 s hsα s hs' rfl
      · intro θ hθ
        rcases Multiset.mem_cons.1 hθ with rfl | hθ
        · refine ⟨⟨s, h1, h2, hα⟩, ?_⟩
          have := length_le_card_of_nodup (List.nodup_append.1 hnd).1
            (hα.verts_mem hE (hE e h1).2)
          simpa [length_verts] using this
        · exact hΘ θ hθ
      · rw [parikh_cons, ← Multiset.cons_coe, heq, ← Multiset.coe_add]
        simp only [← Multiset.cons_coe]
        rw [← Multiset.singleton_add, ← Multiset.singleton_add]
        abel
    · refine ⟨e :: π₀, Θ, ⟨h1, h2, hp⟩, ?_, hΘ, ?_⟩
      · have : verts s (e :: π₀) = s :: verts e.2.2 π₀ := by simp [verts]
        rw [this]
        exact List.nodup_cons.2 ⟨hsv, hnd⟩
      · rw [← Multiset.cons_coe, heq, ← Multiset.cons_coe, Multiset.cons_add]

/-- Decomposition of a path into a short path and short cycles. -/
theorem exists_decomp {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) {s s' : V} (hs : s ∈ S) {π : List (Edge V L)}
    (h : IsPath E s π s') :
    ∃ π₀ : List (Edge V L), ∃ Θ : Multiset (List (Edge V L)),
      IsPath E s π₀ s' ∧ π₀.length < S.card ∧ (∀ θ ∈ Θ, IsCycle E θ ∧ θ.length ≤ S.card) ∧
      (π : Multiset (Edge V L)) = (π₀ : Multiset (Edge V L)) + parikh Θ := by
  obtain ⟨π₀, Θ, hp, hnd, hΘ, heq⟩ := exists_decomp_nodup hE π s hs h
  refine ⟨π₀, Θ, hp, ?_, hΘ, heq⟩
  have := length_le_card_of_nodup hnd (hp.verts_mem hE hs)
  rw [length_verts] at this
  omega

/-! ### Euler lemma -/

theorem mem_verts_of_mem {s : V} {π : List (Edge V L)} {e : Edge V L} (he : e ∈ π) :
    e.2.2 ∈ verts s π :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem he)

theorem IsPath.src_mem_verts {E : Finset (Edge V L)} {u w : V} {π : List (Edge V L)}
    (h : IsPath E u π w) {e : Edge V L} (he : e ∈ π) : e.1 ∈ verts u π := by
  induction π generalizing u with
  | nil => simp at he
  | cons f π ih =>
    obtain ⟨-, h2, h3⟩ := h
    rcases List.mem_cons.1 he with rfl | he
    · exact h2 ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h3 he)

/-- A path from inside `W` to outside `W` has an edge leaving `W`. -/
theorem IsPath.exists_leave {E : Finset (Edge V L)} {u x : V} {π : List (Edge V L)}
    (h : IsPath E u π x) (W : V → Prop) (hu : W u) (hx : ¬ W x) :
    ∃ e ∈ π, W e.1 ∧ ¬ W e.2.2 := by
  induction π generalizing u with
  | nil => exact absurd (show W x from (show u = x from h) ▸ hu) hx
  | cons f π ih =>
    obtain ⟨-, h2, h3⟩ := h
    by_cases hf : W f.2.2
    · obtain ⟨e, he, h⟩ := ih h3 hf
      exact ⟨e, List.mem_cons_of_mem _ he, h⟩
    · exact ⟨f, List.mem_cons_self, h2 ▸ hu, hf⟩

/-- A cycle through an edge `f` can be rotated to start at `f`'s source. -/
theorem IsCycle.rotate {E : Finset (Edge V L)} {c : List (Edge V L)} (hc : IsCycle E c)
    {f : Edge V L} (hf : f ∈ c) :
    ∃ c', IsPath E f.1 c' f.1 ∧ (c' : Multiset (Edge V L)) = c := by
  obtain ⟨y, hy⟩ := hc
  obtain ⟨c₁, c₂, rfl⟩ := List.append_of_mem hf
  obtain ⟨v, h₁, h₂⟩ := isPath_append.1 hy
  have hv : f.1 = v := h₂.2.1
  refine ⟨(f :: c₂) ++ c₁, isPath_append.2 ⟨y, hv ▸ h₂, hv ▸ h₁⟩, ?_⟩
  exact Multiset.coe_eq_coe.2 List.perm_append_comm

theorem parikh_eq_zero {Θ : Multiset (List (Edge V L))} (h : ∀ θ ∈ Θ, θ = []) :
    parikh Θ = 0 :=
  Multiset.eq_zero_of_forall_notMem fun e he => by
    obtain ⟨θ, hθ, he⟩ := mem_parikh.1 he
    simp [h θ hθ] at he

theorem euler_aux {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) (hSC : StronglyConnected E S) {s₀ : V} (hs₀ : s₀ ∈ S)
    (n : ℕ) : ∀ (w : List (Edge V L)) (R : Multiset (List (Edge V L))), R.card = n →
      IsPath E s₀ w s₀ → (∀ c ∈ R, IsCycle E c) → (∀ e ∈ E, e ∈ w ∨ e ∈ parikh R) →
      ∃ θ, IsPath E s₀ θ s₀ ∧ (θ : Multiset (Edge V L)) = w + parikh R := by
  induction n with
  | zero =>
    intro w R hR hw _ _
    rw [Multiset.card_eq_zero.1 hR]
    exact ⟨w, hw, by simp [parikh_zero]⟩
  | succ n ih =>
    intro w R hR hw hRc htot
    by_cases hnil : ∀ c ∈ R, c = []
    · exact ⟨w, hw, by simp [parikh_eq_zero hnil]⟩
    push Not at hnil
    obtain ⟨c₀, hc₀, hc₀ne⟩ := hnil
    have hex : ∃ c ∈ R, ∃ f ∈ c, f.1 ∈ verts s₀ w := by
      by_contra hno
      push Not at hno
      obtain ⟨g, c', rfl⟩ := List.exists_cons_of_ne_nil hc₀ne
      obtain ⟨y, hy⟩ := hRc _ hc₀
      have hgE : g ∈ E := hy.mem_E g List.mem_cons_self
      obtain ⟨π, hπ⟩ := hSC s₀ hs₀ g.1 (hE g hgE).1
      obtain ⟨e, he, heW, heW'⟩ := hπ.exists_leave (· ∈ verts s₀ w) List.mem_cons_self
        (hno _ hc₀ g List.mem_cons_self)
      rcases htot e (hπ.mem_E e he) with hew | heR
      · exact heW' (mem_verts_of_mem hew)
      · obtain ⟨c, hc, hec⟩ := mem_parikh.1 heR
        exact hno c hc e hec heW
    obtain ⟨c, hc, f, hfc, hfw⟩ := hex
    obtain ⟨c', hc', hc'eq⟩ := (hRc c hc).rotate hfc
    obtain ⟨α, β, rfl, hα, hβ⟩ := hw.split hfw
    have hR' : R = c ::ₘ R.erase c := (Multiset.cons_erase hc).symm
    have key : ((α ++ (c' ++ β) : List (Edge V L)) : Multiset (Edge V L)) + parikh (R.erase c) =
        ((α ++ β : List (Edge V L)) : Multiset (Edge V L)) + parikh R := by
      rw [hR', parikh_cons, Multiset.erase_cons_head]
      simp only [← Multiset.coe_add, hc'eq]
      abel
    obtain ⟨θ, hθ, hθeq⟩ := ih (α ++ (c' ++ β)) (R.erase c)
      (by rw [Multiset.card_erase_of_mem hc, hR]; rfl)
      (isPath_append.2 ⟨f.1, hα, isPath_append.2 ⟨f.1, hc', hβ⟩⟩)
      (fun c'' hc'' => hRc c'' (Multiset.mem_of_mem_erase hc''))
      (fun e he => by
        have : e ∈ ((α ++ β : List (Edge V L)) : Multiset (Edge V L)) + parikh R := by
          rcases htot e he with h | h
          · exact Multiset.mem_add.2 (Or.inl (Multiset.mem_coe.2 h))
          · exact Multiset.mem_add.2 (Or.inr h)
        rw [← key] at this
        rcases Multiset.mem_add.1 this with h | h
        · exact Or.inl (Multiset.mem_coe.1 h)
        · exact Or.inr h)
    exact ⟨θ, hθ, hθeq.trans key⟩

/-- **Lemma 7.1 (Euler lemma).** In a strongly connected Petri net with control-states, every
total multicycle `Θ` has the Parikh image of a single cycle, which can be chosen through any
control-state `s₀`. -/
theorem lemma_7_1 {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) (hSC : StronglyConnected E S) {s₀ : V} (hs₀ : s₀ ∈ S)
    {Θ : Multiset (List (Edge V L))} (hΘ : ∀ θ ∈ Θ, IsCycle E θ)
    (htot : ∀ e ∈ E, e ∈ parikh Θ) :
    ∃ θ, IsPath E s₀ θ s₀ ∧ (θ : Multiset (Edge V L)) = parikh Θ := by
  obtain ⟨θ, hθ, heq⟩ := euler_aux hE hSC hs₀ Θ.card [] Θ rfl rfl hΘ
    (fun e he => Or.inr (htot e he))
  exact ⟨θ, hθ, by simpa using heq⟩

theorem card_parikh (Θ : Multiset (List (Edge V L))) :
    Multiset.card (parikh Θ) = mlength Θ := by
  induction Θ using Multiset.induction_on with
  | empty => simp [parikh_zero, mlength]
  | cons θ Θ ih => simp [parikh_cons, mlength, ih] at *

theorem mlength_le {Θ : Multiset (List (Edge V L))} {n : ℕ} (h : ∀ θ ∈ Θ, θ.length ≤ n) :
    mlength Θ ≤ Multiset.card Θ * n := by
  have := Multiset.sum_le_card_nsmul (Θ.map List.length) n (by simpa using h)
  simpa [mlength] using this

/-- **Lemma 7.2.** A strongly connected Petri net with control-states has a total cycle through
any control-state `s₀`, of length at most `|E||S|`. -/
theorem lemma_7_2 {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) (hSC : StronglyConnected E S) {s₀ : V} (hs₀ : s₀ ∈ S) :
    ∃ θ, IsPath E s₀ θ s₀ ∧ (∀ e ∈ E, e ∈ θ) ∧ θ.length ≤ E.card * S.card := by
  have hc : ∀ e ∈ E, ∃ c : List (Edge V L), IsPath E e.1 c e.1 ∧ e ∈ c ∧ c.length ≤ S.card := by
    intro e he
    obtain ⟨π, hπ⟩ := hSC e.2.2 (hE e he).2 e.1 (hE e he).1
    obtain ⟨π₀, -, hπ₀, hlen, -⟩ := exists_decomp hE (hE e he).2 hπ
    exact ⟨e :: π₀, ⟨he, rfl, hπ₀⟩, List.mem_cons_self, by simp; omega⟩
  choose c hc using hc
  set Θ : Multiset (List (Edge V L)) := E.attach.val.map (fun e => c e.1 e.2) with hΘdef
  have hmem : ∀ θ ∈ Θ, ∃ e : E, θ = c e.1 e.2 := by
    intro θ hθ
    obtain ⟨e, -, rfl⟩ := Multiset.mem_map.1 hθ
    exact ⟨e, rfl⟩
  have htot : ∀ e ∈ E, e ∈ parikh Θ := fun e he =>
    mem_parikh.2 ⟨c e he, Multiset.mem_map.2 ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩,
      (hc e he).2.1⟩
  obtain ⟨θ, hθ, hθeq⟩ := lemma_7_1 hE hSC hs₀ (Θ := Θ)
    (fun θ hθ => by obtain ⟨e, rfl⟩ := hmem θ hθ; exact ⟨_, (hc e.1 e.2).1⟩) htot
  refine ⟨θ, hθ, fun e he => Multiset.mem_coe.1 (hθeq ▸ htot e he), ?_⟩
  have h1 : θ.length = mlength Θ := by
    rw [← card_parikh, ← hθeq, Multiset.coe_card]
  have h2 := mlength_le (Θ := Θ) (n := S.card)
    (fun θ hθ => by obtain ⟨e, rfl⟩ := hmem θ hθ; exact (hc e.1 e.2).2.2)
  have h3 : Multiset.card Θ = E.card := by
    rw [hΘdef, Multiset.card_map]; exact E.card_attach
  rw [h1, ← h3]; exact h2

/-! ### Lemma 7.3 -/

theorem mem_multiset_sum {α : Type*} {a : α} {m : Multiset (Multiset α)} :
    a ∈ m.sum ↔ ∃ x ∈ m, a ∈ x := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih => simp [ih]

/-- `mdisp δ · p` as an additive monoid homomorphism. -/
def mdispHom (δ : L → P → ℤ) (p : P) : Multiset (List (Edge V L)) →+ ℤ where
  toFun Θ := mdisp δ Θ p
  map_zero' := by simp [mdisp]
  map_add' Θ Θ' := by simp [mdisp]

/-- `parikh` as an additive monoid homomorphism. -/
def parikhHom : Multiset (List (Edge V L)) →+ Multiset (Edge V L) where
  toFun := parikh
  map_zero' := parikh_zero
  map_add' := parikh_add

/-- `mlength` as an additive monoid homomorphism. -/
def mlengthHom : Multiset (List (Edge V L)) →+ ℕ where
  toFun := mlength
  map_zero' := by simp [mlength]
  map_add' Θ Θ' := by simp [mlength]

@[simp] theorem mdispHom_apply (δ : L → P → ℤ) (p : P) (Θ : Multiset (List (Edge V L))) :
    mdispHom δ p Θ = mdisp δ Θ p := rfl

@[simp] theorem parikhHom_apply (Θ : Multiset (List (Edge V L))) : parikhHom Θ = parikh Θ := rfl

@[simp] theorem mlengthHom_apply (Θ : Multiset (List (Edge V L))) : mlengthHom Θ = mlength Θ :=
  rfl

theorem mdisp_singleton (δ : L → P → ℤ) (θ : List (Edge V L)) (p : P) :
    mdisp δ {θ} p = disp δ θ p := by simp [mdisp]

theorem mdisp_zero (δ : L → P → ℤ) (p : P) :
    mdisp δ (0 : Multiset (List (Edge V L))) p = 0 := by simp [mdisp]

/-- The displacement of a multicycle only depends on its Parikh image. -/
theorem mdisp_eq_parikh (δ : L → P → ℤ) (Θ : Multiset (List (Edge V L))) (p : P) :
    mdisp δ Θ p = ((parikh Θ).map fun e => δ e.2.1 p).sum := by
  induction Θ using Multiset.induction_on with
  | empty => simp [mdisp, parikh_zero]
  | cons θ Θ ih =>
    rw [parikh_cons, Multiset.map_add, Multiset.sum_add, ← ih]
    simp [mdisp, disp]

theorem abs_disp_le {E : Finset (Edge V L)} (δ : L → P → ℤ) {M : ℕ}
    (hδ : ∀ e ∈ E, ∀ p, |δ e.2.1 p| ≤ M) {θ : List (Edge V L)} (hθ : ∀ e ∈ θ, e ∈ E) (p : P) :
    |disp δ θ p| ≤ θ.length * M := by
  induction θ with
  | nil => simp [disp]
  | cons e θ ih =>
    have h1 := hδ e (hθ e List.mem_cons_self) p
    have h2 := ih (fun f hf => hθ f (List.mem_cons_of_mem _ hf))
    have : disp δ (e :: θ) p = δ e.2.1 p + disp δ θ p := by simp [disp]
    rw [this]
    calc _ ≤ |δ e.2.1 p| + |disp δ θ p| := abs_add_le _ _
      _ ≤ _ := by simp only [List.length_cons]; push_cast; linarith

/-- A cycle is the Parikh image of a multicycle of cycles of length `≤ |S|`. -/
theorem IsCycle.exists_short {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) {θ : List (Edge V L)} (hθ : IsCycle E θ) :
    ∃ Γ : Multiset (List (Edge V L)), (∀ γ ∈ Γ, IsCycle E γ ∧ γ.length ≤ S.card) ∧
      parikh Γ = θ := by
  obtain ⟨s, hs⟩ := hθ
  cases θ with
  | nil => exact ⟨0, by simp, by simp [parikh_zero]⟩
  | cons e θ =>
    have hsS : s ∈ S := hs.2.1 ▸ (hE e hs.1).1
    obtain ⟨π₀, Θ₀, hp, hlen, hΘ₀, heq⟩ := exists_decomp hE hsS hs
    refine ⟨π₀ ::ₘ Θ₀, fun γ hγ => ?_, by rw [parikh_cons, heq]⟩
    rcases Multiset.mem_cons.1 hγ with rfl | hγ
    · exact ⟨⟨s, hp⟩, hlen.le⟩
    · exact hΘ₀ γ hγ

/-- A multicycle has the Parikh image of a multicycle of cycles of length `≤ |S|`. -/
theorem exists_short_multicycle {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) {Θ : Multiset (List (Edge V L))}
    (hΘ : ∀ θ ∈ Θ, IsCycle E θ) :
    ∃ Θs : Multiset (List (Edge V L)), (∀ θ ∈ Θs, IsCycle E θ ∧ θ.length ≤ S.card) ∧
      parikh Θs = parikh Θ := by
  induction Θ using Multiset.induction_on with
  | empty => exact ⟨0, by simp, rfl⟩
  | cons θ Θ ih =>
    obtain ⟨Γ, hΓ, hΓeq⟩ := (hΘ θ (Multiset.mem_cons.2 (Or.inl rfl))).exists_short hE
    obtain ⟨Θs, hs, hseq⟩ := ih (fun θ' h => hΘ θ' (Multiset.mem_cons_of_mem h))
    refine ⟨Γ + Θs, fun γ hγ => ?_, by rw [parikh_add, parikh_cons, hΓeq, hseq]⟩
    rcases Multiset.mem_add.1 hγ with h | h
    exacts [hΓ γ h, hs γ h]

theorem msum_nonpos {m : Multiset ℤ} (h : ∀ z ∈ m, z ≤ 0) : m.sum ≤ 0 := by
  simpa using Multiset.sum_le_card_nsmul m 0 h

theorem abs_eq_sig {σ x : ℤ} (hσ : σ = 1 ∨ σ = -1) (h : 0 ≤ σ * x) : |x| = σ * x := by
  rcases hσ with rfl | rfl
  · rw [one_mul] at *; exact abs_of_nonneg h
  · rw [abs_of_nonpos (by linarith)]; ring

theorem abs_sum_conformal {β : Type*} (s : Multiset β) (f : β → ℤ) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (h : ∀ y ∈ s, 0 ≤ σ * f y) :
    |(s.map f).sum| = (s.map fun y => |f y|).sum := by
  have h1 : (s.map fun y => |f y|).sum = (s.map fun y => σ * f y).sum :=
    congrArg Multiset.sum (Multiset.map_congr rfl fun y hy => abs_eq_sig hσ (h y hy))
  rw [h1, Multiset.sum_map_mul_left]
  refine abs_eq_sig hσ ?_
  rw [← Multiset.sum_map_mul_left]
  exact Multiset.sum_nonneg fun z hz => by
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact h y hy

theorem sum_map_finset_comm {β : Type*} (s : Multiset β) (Q : Finset P) (f : β → P → ℤ) :
    ∑ q ∈ Q, (s.map fun y => f y q).sum = (s.map fun y => ∑ q ∈ Q, f y q).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih => simp [Finset.sum_add_distrib, ih]

theorem sum_filter_le {β : Type*} (s : Multiset β) (r : β → Prop) [DecidablePred r] (g : β → ℤ)
    (hg : ∀ y ∈ s, 0 ≤ g y) : ((s.filter r).map g).sum ≤ (s.map g).sum := by
  conv_rhs => rw [← Multiset.filter_add_not r s, Multiset.map_add, Multiset.sum_add]
  have : 0 ≤ ((s.filter fun y => ¬ r y).map g).sum := Multiset.sum_nonneg fun z hz => by
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact hg y (Multiset.mem_of_mem_filter hy)
  linarith

/-- If the parts violating `Fr` are few and each contributes at most `B`, but the total exceeds
`N B`, then some part satisfying `Fr` contributes. -/
theorem exists_pos_of_sum {β : Type*} (s : Multiset β) (Fr : β → Prop) [DecidablePred Fr]
    (g : β → ℤ) (B N : ℤ) (hB : 0 ≤ B) (hgB : ∀ y ∈ s, ¬ Fr y → g y ≤ B)
    (hN : ((s.filter fun y => ¬ Fr y).card : ℤ) ≤ N) (hlt : N * B < (s.map g).sum) :
    ∃ y ∈ s, Fr y ∧ 0 < g y := by
  by_contra hno
  push Not at hno
  have h1 : ((s.filter Fr).map g).sum ≤ 0 :=
    msum_nonpos fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
      exact hno y (Multiset.mem_of_mem_filter hy) (Multiset.of_mem_filter hy)
  have h2 : ((s.filter fun y => ¬ Fr y).map g).sum ≤
      Multiset.card ((s.filter fun y => ¬ Fr y).map g) • B :=
    Multiset.sum_le_card_nsmul _ _ fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
      exact hgB y (Multiset.mem_of_mem_filter hy) (Multiset.mem_filter.1 hy).2
  rw [← Multiset.filter_add_not Fr s, Multiset.map_add, Multiset.sum_add] at hlt
  rw [Multiset.card_map, nsmul_eq_mul] at h2
  have h3 := mul_le_mul_of_nonneg_right hN hB
  linarith

theorem sum_neg_of_mem {m : Multiset ℤ} (h : ∀ z ∈ m, z ≤ 0) {a : ℤ} (ha : a ∈ m) (ha' : a < 0) :
    m.sum < 0 := by
  rw [← Multiset.cons_erase ha, Multiset.sum_cons]
  have : (m.erase a).sum ≤ 0 := msum_nonpos fun z hz => h z (Multiset.mem_of_mem_erase hz)
  linarith

theorem sum_pos_of_mem {m : Multiset ℤ} (h : ∀ z ∈ m, 0 ≤ z) {a : ℤ} (ha : a ∈ m) (ha' : 0 < a) :
    0 < m.sum := by
  rw [← Multiset.cons_erase ha, Multiset.sum_cons]
  have : 0 ≤ (m.erase a).sum := Multiset.sum_nonneg fun z hz => h z (Multiset.mem_of_mem_erase hz)
  linarith

/-- The multicycle with multiplicity `y c` for each cycle `c ∈ C`. -/
def gam (C : Finset (List (Edge V L))) : (C → ℕ) →+ Multiset (List (Edge V L)) where
  toFun y := ∑ c : C, y c • ({c.1} : Multiset (List (Edge V L)))
  map_zero' := by simp
  map_add' y z := by simp [add_nsmul, Finset.sum_add_distrib]

theorem mem_gam {C : Finset (List (Edge V L))} {y : C → ℕ} {θ : List (Edge V L)}
    (h : θ ∈ gam C y) : θ ∈ C := by
  obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 h
  rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hc
  exact hc.2 ▸ c.2

theorem mdisp_gam (δ : L → P → ℤ) (C : Finset (List (Edge V L))) (y : C → ℕ) (p : P) :
    mdisp δ (gam C y) p = ∑ c : C, (y c : ℤ) * disp δ c.1 p := by
  change mdispHom δ p (∑ c : C, y c • ({c.1} : Multiset (List (Edge V L)))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_nsmul]
  simp [mdisp_singleton]

theorem mlength_gam (C : Finset (List (Edge V L))) (y : C → ℕ) :
    mlength (gam C y) = ∑ c : C, y c * c.1.length := by
  change mlengthHom (∑ c : C, y c • ({c.1} : Multiset (List (Edge V L)))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_nsmul]
  simp [mlength]

theorem gam_count (Θ : Multiset (List (Edge V L))) :
    gam Θ.toFinset (fun c => Θ.count c.1) = Θ := by
  change ∑ c : Θ.toFinset, Θ.count c.1 • ({c.1} : Multiset (List (Edge V L))) = Θ
  rw [Finset.sum_coe_sort Θ.toFinset (fun c => Θ.count c • ({c} : Multiset (List (Edge V L))))]
  exact Multiset.toFinset_sum_count_nsmul_eq Θ

/-- Lemma 7.3 for a multicycle of cycles of length `≤ |S|`. -/
theorem lemma_7_3_short {E : Finset (Edge V L)} {S : Finset V} (δ : L → P → ℤ) {M : ℕ}
    (hM : 1 ≤ M) (hδ : ∀ e ∈ E, ∀ p, |δ e.2.1 p| ≤ M)
    {Θ : Multiset (List (Edge V L))} (hΘ : ∀ θ ∈ Θ, IsCycle E θ ∧ θ.length ≤ S.card)
    (Q : Finset P) (k : ℕ)
    (hk : (∑ q ∈ Q, |mdisp δ Θ q|) * S.card * M * (2 * S.card * M) ^ (2 ^ Fintype.card P - 1)
      < k) :
    ∃ Θ' : Multiset (List (Edge V L)), (∀ θ ∈ Θ', IsCycle E θ) ∧
      (∀ p, (mdisp δ Θ p ≤ 0 → mdisp δ Θ' p ≤ 0) ∧ (mdisp δ Θ p ≤ -k → mdisp δ Θ' p < 0) ∧
        (0 ≤ mdisp δ Θ p → 0 ≤ mdisp δ Θ' p) ∧ ((k : ℤ) ≤ mdisp δ Θ p → 0 < mdisp δ Θ' p)) ∧
      (∀ q ∈ Q, mdisp δ Θ' q = 0) ∧
      (∀ e, k ≤ (parikh Θ).count e → e ∈ parikh Θ') ∧
      mlength Θ' ≤ (E.card + Fintype.card P) * S.card *
        (2 * S.card * M) ^ (2 ^ Fintype.card P - 1) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K, K = (2 * S.card * M) ^ (2 ^ Fintype.card P - 1) := ⟨_, rfl⟩
  have hk' : (∑ q ∈ Q, |mdisp δ Θ q|) * S.card * M * (K : ℤ) < k := by
    rw [hK]; push_cast; exact hk
  clear hk
  rw [← hK]
  obtain ⟨N, hNdef⟩ : ∃ N, N = ∑ q ∈ Q, |mdisp δ Θ q| := ⟨_, rfl⟩
  rw [← hNdef] at hk'
  have hk := hk'
  clear hk'
  have hN0 : 0 ≤ N := hNdef ▸ Finset.sum_nonneg fun q _ => abs_nonneg _
  have hk1 : 1 ≤ k := by
    have : (0 : ℤ) ≤ N * S.card * M * K := by positivity
    omega
  have hΘE : ∀ θ ∈ Θ, ∀ e ∈ θ, e ∈ E := fun θ hθ => by
    obtain ⟨s, hs⟩ := (hΘ θ hθ).1
    exact hs.mem_E
  by_cases hS : S.card = 0
  · have hnil : ∀ θ ∈ Θ, θ = [] := fun θ hθ =>
      List.eq_nil_of_length_eq_zero (by have := (hΘ θ hθ).2; omega)
    have hp0 := parikh_eq_zero hnil
    have hm0 : ∀ p, mdisp δ Θ p = 0 := fun p => by rw [mdisp_eq_parikh, hp0]; simp
    refine ⟨0, by simp, fun p => ?_, fun q _ => mdisp_zero δ q, fun e he => ?_, by simp [mlength]⟩
    · rw [hm0 p, mdisp_zero]
      exact ⟨fun _ => le_rfl, fun h => by omega, fun _ => le_rfl, fun h => by omega⟩
    · rw [hp0] at he; simp at he; omega
  obtain ⟨C, hC⟩ : ∃ C, C = Θ.toFinset := ⟨_, rfl⟩
  have hCc : ∀ c : C, IsCycle E c.1 ∧ c.1.length ≤ S.card := fun c =>
    hΘ c.1 (Multiset.mem_toFinset.1 (hC ▸ c.2))
  have hCE : ∀ c : C, ∀ e ∈ c.1, e ∈ E := fun c =>
    hΘE c.1 (Multiset.mem_toFinset.1 (hC ▸ c.2))
  have hgx : gam C (fun c => Θ.count c.1) = Θ := by subst hC; exact gam_count Θ
  set σ : P → ℤ := fun p => if 0 ≤ mdisp δ Θ p then 1 else -1 with hσdef
  have hσ : ∀ p, σ p = 1 ∨ σ p = -1 := fun p => by
    by_cases h : 0 ≤ mdisp δ Θ p <;> simp [σ, h]
  have hσabs : ∀ p, σ p * mdisp δ Θ p = |mdisp δ Θ p| := fun p => by
    by_cases h : 0 ≤ mdisp δ Θ p
    · simp [σ, h, abs_of_nonneg h]
    · simp [σ, h, abs_of_neg (lt_of_not_ge h)]
  set A : P → C → ℤ := fun p c => σ p * disp δ c.1 p with hAdef
  set D : (C → ℕ) → P → ℤ := fun y p => mdisp δ (gam C y) p with hDdef
  have hDy : ∀ y p, σ p * D y p = ∑ c, A p c * (y c : ℤ) := fun y p => by
    simp only [D, A, mdisp_gam, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hdisp : ∀ c : C, ∀ p, |disp δ c.1 p| ≤ ((S.card * M : ℕ) : ℤ) := fun c p => by
    calc |disp δ c.1 p| ≤ c.1.length * M := abs_disp_le δ hδ (hCE c) p
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hCc c).2) (by positivity)
  have hA : ∀ p c, |A p c| ≤ ((S.card * M : ℕ) : ℤ) := fun p c => by
    simp only [A]
    rw [abs_mul]
    have hs : |σ p| = 1 := by rcases hσ p with h | h <;> simp [h]
    rw [hs, one_mul]
    exact hdisp c p
  have hM' : 1 ≤ S.card * M := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨s, hs, hsy⟩ := Cslib.exists_small_decomposition (S.card * M) hM' A hA
    (fun c => Θ.count c.1)
    (fun p => by
      rw [← hDy]
      show 0 ≤ σ p * mdisp δ (gam C (fun c => Θ.count c.1)) p
      rw [hgx, hσabs]; exact abs_nonneg _)
  have hK' : (2 * (S.card * M)) ^ (2 ^ Fintype.card P - 1) = K := by rw [hK, mul_assoc]
  have hnorm : ∀ y ∈ s, ∑ c, y c ≤ K := fun y hy => hK' ▸ (hsy y hy).2
  have hconf : ∀ y ∈ s, ∀ p, 0 ≤ σ p * D y p := fun y hy p => by
    rw [hDy]; exact (hsy y hy).1 p
  have hΘs : Θ = gam C s.sum := by rw [hs, hgx]
  have hsum : ∀ p, (s.map (D · p)).sum = mdisp δ Θ p := by
    intro p
    have : mdisp δ (gam C s.sum) p = (s.map (D · p)).sum := by
      change mdispHom δ p (gam C s.sum) = _
      rw [map_multiset_sum, map_multiset_sum, Multiset.map_map]
      rfl
    rw [this.symm, ← hΘs]
  have habs_sum : ∀ p, |mdisp δ Θ p| = (s.map fun y => |D y p|).sum := fun p => by
    rw [← hsum p]
    exact abs_sum_conformal s (D · p) (hσ p) (fun y hy => hconf y hy p)
  have hzero : ∀ p, mdisp δ Θ p = 0 → ∀ y ∈ s, D y p = 0 := by
    intro p h y hy
    have h1 := habs_sum p
    rw [h, abs_zero] at h1
    have h2 := Multiset.single_le_sum (fun z hz => by
      obtain ⟨y', _, rfl⟩ := Multiset.mem_map.1 hz; exact abs_nonneg _) _
      (Multiset.mem_map_of_mem (fun y => |D y p|) hy)
    rw [← h1] at h2
    exact abs_nonpos_iff.1 h2
  have hDbound : ∀ y : C → ℕ, ∀ p, |D y p| ≤ (S.card * M : ℕ) * ((∑ c, y c : ℕ) : ℤ) := by
    intro y p
    simp only [D, mdisp_gam]
    calc |∑ c : C, (y c : ℤ) * disp δ c.1 p| ≤ ∑ c : C, |(y c : ℤ) * disp δ c.1 p| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c : C, (y c : ℤ) * ((S.card * M : ℕ) : ℤ) := Finset.sum_le_sum fun c _ => by
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left (hdisp c p) (by positivity)
      _ = _ := by push_cast; rw [← Finset.sum_mul, mul_comm]
  have hlenbound : ∀ y : C → ℕ, mlength (gam C y) ≤ S.card * ∑ c, y c := by
    intro y
    rw [mlength_gam, Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hCc c).2
  -- `Q`-free parts
  set Fr : (C → ℕ) → Prop := fun y => ∀ q ∈ Q, D y q = 0 with hFr
  have hN : ((s.filter fun y => ¬ Fr y).card : ℤ) ≤ N := by
    have h1 : N = (s.map fun y => ∑ q ∈ Q, |D y q|).sum := by
      rw [hNdef, ← sum_map_finset_comm]
      exact Finset.sum_congr rfl fun q _ => habs_sum q
    rw [h1]
    refine le_trans ?_ (sum_filter_le s (fun y => ¬ Fr y) _
      (fun y _ => Finset.sum_nonneg fun q _ => abs_nonneg _))
    have := Multiset.card_nsmul_le_sum (s := (s.filter fun y => ¬ Fr y).map
      fun y => ∑ q ∈ Q, |D y q|) (a := 1) (fun z hz => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        have hy' := (Multiset.mem_filter.1 hy).2
        simp only [Fr, not_forall] at hy'
        obtain ⟨q, hq, hne⟩ := hy'
        calc (1 : ℤ) ≤ |D y q| := Int.one_le_abs hne
          _ ≤ _ := Finset.single_le_sum (f := fun q => |D y q|)
              (fun q _ => abs_nonneg _) hq)
    simpa using this
  have hkN : N * ((S.card * M : ℕ) * K : ℤ) < k := by
    push_cast; linarith [show N * (S.card * M * K : ℤ) = N * S.card * M * K by ring]
  have hP : ∀ p, (k : ℤ) ≤ |mdisp δ Θ p| → ∃ y ∈ s, Fr y ∧ 0 < |D y p| := fun p hp =>
    exists_pos_of_sum s Fr (fun y => |D y p|) ((S.card * M : ℕ) * K) N
      (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      (fun y hy _ => (hDbound y p).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hnorm y hy) (Int.natCast_nonneg _))) hN
      (by rw [← habs_sum]; linarith)
  have hcount : ∀ e, ((s.map fun y => ((parikh (gam C y)).count e : ℤ))).sum =
      (parikh Θ).count e := by
    intro e
    have : (parikh (gam C s.sum)).count e = (s.map fun y => (parikh (gam C y)).count e).sum := by
      change (((Multiset.countAddMonoidHom e).comp parikhHom).comp (gam C)) s.sum = _
      rw [map_multiset_sum]
      rfl
    rw [hΘs, this, Nat.cast_multiset_sum, Multiset.map_map]
    rfl
  have hEd : ∀ e, k ≤ (parikh Θ).count e →
      ∃ y ∈ s, Fr y ∧ 0 < ((parikh (gam C y)).count e : ℤ) := fun e he =>
    exists_pos_of_sum s Fr (fun y => ((parikh (gam C y)).count e : ℤ)) ((S.card * K : ℕ)) N
      (Int.natCast_nonneg _)
      (fun y hy _ => by
        have h1 : (parikh (gam C y)).count e ≤ S.card * K :=
          calc _ ≤ Multiset.card (parikh (gam C y)) := Multiset.count_le_card _ _
            _ = mlength (gam C y) := card_parikh _
            _ ≤ S.card * ∑ c, y c := hlenbound y
            _ ≤ S.card * K := Nat.mul_le_mul_left _ (hnorm y hy)
        exact_mod_cast h1) hN
      (by
        rw [hcount]
        have h1 : N * ((S.card * K : ℕ) : ℤ) ≤ N * ((S.card * M : ℕ) * K : ℤ) := by
          apply mul_le_mul_of_nonneg_left _ hN0
          push_cast
          have : (S.card : ℤ) * K * 1 ≤ S.card * K * M :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hM)
              (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
          linarith
        have h2 : (k : ℤ) ≤ (parikh Θ).count e := by exact_mod_cast he
        linarith)
  -- good parts
  set Good : (C → ℕ) → Prop := fun y => (∀ p, 0 ≤ σ p * D y p) ∧
    (∀ p, mdisp δ Θ p = 0 → D y p = 0) ∧ Fr y ∧ ∑ c, y c ≤ K with hGood
  have hD0 : ∀ p, D 0 p = 0 := fun p => by simp [D, mdisp_zero]
  have hgood0 : Good 0 := ⟨fun p => by simp [hD0], fun p _ => hD0 p, fun q _ => hD0 q, by simp⟩
  have hgoods : ∀ y ∈ s, Fr y → Good y := fun y hy hf =>
    ⟨hconf y hy, fun p hp => hzero p hp y hy, hf, hnorm y hy⟩
  let yP : P → C → ℕ := fun p =>
    if h : (k : ℤ) ≤ |mdisp δ Θ p| then (hP p h).choose else 0
  have hyP : ∀ p, Good (yP p) ∧ ((k : ℤ) ≤ |mdisp δ Θ p| → 0 < |D (yP p) p|) := by
    intro p
    by_cases h : (k : ℤ) ≤ |mdisp δ Θ p|
    · simp only [yP, h, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := (hP p h).choose_spec
      exact ⟨hgoods _ h1 h2, fun _ => h3⟩
    · simp only [yP, h, ↓reduceDIte]
      exact ⟨hgood0, fun h' => h'.elim⟩
  let yE : Edge V L → C → ℕ := fun e =>
    if h : k ≤ (parikh Θ).count e then (hEd e h).choose else 0
  have hyE : ∀ e, Good (yE e) ∧ (k ≤ (parikh Θ).count e → e ∈ parikh (gam C (yE e))) := by
    intro e
    by_cases h : k ≤ (parikh Θ).count e
    · simp only [yE, h, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := (hEd e h).choose_spec
      exact ⟨hgoods _ h1 h2, fun _ => Multiset.count_pos.1 (by exact_mod_cast h3)⟩
    · simp only [yE, h, ↓reduceDIte]
      exact ⟨hgood0, fun h' => h'.elim⟩
  set T : Multiset (C → ℕ) := (Finset.univ : Finset P).val.map yP + E.val.map yE with hT
  have hTgood : ∀ y ∈ T, Good y := by
    intro y hy
    rcases Multiset.mem_add.1 hy with h | h
    · obtain ⟨p, -, rfl⟩ := Multiset.mem_map.1 h; exact (hyP p).1
    · obtain ⟨e, -, rfl⟩ := Multiset.mem_map.1 h; exact (hyE e).1
  have hD' : ∀ p, mdisp δ (T.map (gam C)).sum p = (T.map (D · p)).sum := fun p => by
    change mdispHom δ p _ = _
    rw [map_multiset_sum, Multiset.map_map]
    rfl
  refine ⟨(T.map (gam C)).sum, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨m, hm, hθm⟩ := mem_multiset_sum.1 hθ
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hm
    have := mem_gam hθm
    exact (hΘ θ (Multiset.mem_toFinset.1 (hC ▸ this))).1
  · intro p
    have hle : mdisp δ Θ p ≤ 0 → ∀ z ∈ T.map (D · p), z ≤ 0 := by
      intro hp z hz
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
      have hg := hTgood y hy
      by_cases h0 : mdisp δ Θ p = 0
      · exact (hg.2.1 p h0).le
      · have h1 := hg.1 p
        have : ¬ 0 ≤ mdisp δ Θ p := fun h => h0 (le_antisymm hp h)
        simp only [σ, this, ite_false] at h1
        linarith
    have hge : 0 ≤ mdisp δ Θ p → ∀ z ∈ T.map (D · p), 0 ≤ z := by
      intro hp z hz
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
      have h1 := (hTgood y hy).1 p
      simp only [σ, hp, ite_true, one_mul] at h1
      exact h1
    have hmemP : yP p ∈ T :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ (Finset.mem_univ_val p)))
    rw [hD']
    refine ⟨fun hp => msum_nonpos (hle hp), fun hp => ?_, fun hp => Multiset.sum_nonneg (hge hp),
      fun hp => ?_⟩
    · have hp0 : mdisp δ Θ p ≤ 0 := by linarith
      have hkp : (k : ℤ) ≤ |mdisp δ Θ p| := by rw [abs_of_nonpos hp0]; linarith
      have hz := (hyP p).2 hkp
      have hmem := Multiset.mem_map_of_mem (D · p) hmemP
      have hz0 := hle hp0 _ hmem
      exact sum_neg_of_mem (hle hp0) hmem (lt_of_le_of_ne hz0 fun h => by simp [h] at hz)
    · have hp0 : 0 ≤ mdisp δ Θ p := by linarith
      have hkp : (k : ℤ) ≤ |mdisp δ Θ p| := by rw [abs_of_nonneg hp0]; linarith
      have hz := (hyP p).2 hkp
      have hmem := Multiset.mem_map_of_mem (D · p) hmemP
      have hz0 := hge hp0 _ hmem
      exact sum_pos_of_mem (hge hp0) hmem (lt_of_le_of_ne hz0 fun h => by simp [← h] at hz)
  · intro q hq
    rw [hD']
    exact Multiset.sum_eq_zero fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
      exact (hTgood y hy).2.2.1 q hq
  · intro e he
    have hepos : e ∈ parikh Θ := Multiset.count_pos.1 (by omega)
    obtain ⟨θ, hθ, heθ⟩ := mem_parikh.1 hepos
    have heE : e ∈ E := hΘE θ hθ e heθ
    have hmemE : yE e ∈ T :=
      Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ (show e ∈ E.val from heE)))
    have : parikh (T.map (gam C)).sum = (T.map fun y => parikh (gam C y)).sum := by
      change parikhHom _ = _
      rw [map_multiset_sum, Multiset.map_map]
      rfl
    rw [this, mem_multiset_sum]
    exact ⟨_, Multiset.mem_map_of_mem _ hmemE, (hyE e).2 he⟩
  · have : mlength (T.map (gam C)).sum = (T.map fun y => mlength (gam C y)).sum := by
      change mlengthHom _ = _
      rw [map_multiset_sum, Multiset.map_map]
      rfl
    rw [this]
    have h1 := Multiset.sum_le_card_nsmul (T.map fun y => mlength (gam C y)) (S.card * K)
      (fun z hz => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        exact (hlenbound y).trans (Nat.mul_le_mul_left _ (hTgood y hy).2.2.2))
    have h2 : Multiset.card T = Fintype.card P + E.card := by
      simp [hT, Finset.card_univ]
    rw [Multiset.card_map, h2, smul_eq_mul] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring

/-- **Lemma 7.3** (with the constant of the weak Pottier bound). Let `Θ` be a multicycle, `Q` a
set of places, `M ≥ 1` a bound on the displacements of the labels, `d = |P|`,
`K = (2|S|M)^(2^d − 1)` and `k > ‖Δ(Θ)|_Q‖₁ · |S| · M · K`. There is a multicycle `Θ'` with:
the sign pattern of `Δ(Θ)` (strict where `|Δ(Θ)(p)| ≥ k`), `Δ(Θ')(q) = 0` for `q ∈ Q`, every edge
used at least `k` times by `Θ` is used by `Θ'`, and `|Θ'| ≤ (|E| + d) |S| K`. -/
theorem lemma_7_3 {E : Finset (Edge V L)} {S : Finset V}
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.2 ∈ S) (δ : L → P → ℤ) {M : ℕ} (hM : 1 ≤ M)
    (hδ : ∀ e ∈ E, ∀ p, |δ e.2.1 p| ≤ M)
    {Θ : Multiset (List (Edge V L))} (hΘ : ∀ θ ∈ Θ, IsCycle E θ) (Q : Finset P) (k : ℕ)
    (hk : (∑ q ∈ Q, |mdisp δ Θ q|) * S.card * M * (2 * S.card * M) ^ (2 ^ Fintype.card P - 1)
      < k) :
    ∃ Θ' : Multiset (List (Edge V L)), (∀ θ ∈ Θ', IsCycle E θ) ∧
      (∀ p, (mdisp δ Θ p ≤ 0 → mdisp δ Θ' p ≤ 0) ∧ (mdisp δ Θ p ≤ -k → mdisp δ Θ' p < 0) ∧
        (0 ≤ mdisp δ Θ p → 0 ≤ mdisp δ Θ' p) ∧ ((k : ℤ) ≤ mdisp δ Θ p → 0 < mdisp δ Θ' p)) ∧
      (∀ q ∈ Q, mdisp δ Θ' q = 0) ∧
      (∀ e, k ≤ (parikh Θ).count e → e ∈ parikh Θ') ∧
      mlength Θ' ≤ (E.card + Fintype.card P) * S.card *
        (2 * S.card * M) ^ (2 ^ Fintype.card P - 1) := by
  obtain ⟨Θs, hΘs, hpar⟩ := exists_short_multicycle hE hΘ
  have hm : mdisp δ Θ = mdisp δ Θs :=
    funext fun p => by rw [mdisp_eq_parikh, mdisp_eq_parikh, hpar]
  rw [hm] at hk ⊢
  rw [← hpar]
  exact lemma_7_3_short δ hM hδ hΘs Q k hk

end Podc.PPLeadersStateComplexity
