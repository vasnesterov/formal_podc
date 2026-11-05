import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/NIS/Subdivision.lean
-- (staged by Papers/PODC2020/WhyExtensionBased)
/-!
# Distances do not shrink under subdivision (abstract form)

Alistarh, Aspnes, Ellen, Gelashvili, Zhu, *Why extension-based proofs fail*, Lemmas 4.11 and 4.13,
in an abstract "carrier" form.

We have two graphs `G` (level `r`) and `G'` (level `r + 1`) on the same vertex type, a *carrier* map
`car : V → Set V` (the carrier of a vertex of `G'` is a set of vertices of `G`), a choice `anc x ∈ car x`
(the vertex of the same process one level down), and a predicate `act` (non-terminated vertices of `G`).
The two structural hypotheses are
* `hcar`: the carriers of two adjacent vertices of `G'` lie in a common clique of `G`
  (any two of their elements are equal or adjacent);
* `hnest`: if two adjacent vertices of `G'` have active `anc`s, their carriers are nested.

Then distances between "carrier-closed" sets do not decrease (`Far.subdiv`), and they strictly
increase if every walk between the old sets uses an edge between two active vertices
(`Far.subdiv_succ`). Walks are lists of vertices, distances are expressed by `Far G A B d`:
every walk from `A` to `B` has at least `d` edges.
-/

namespace Cslib.NIS.Subdiv

variable {V : Type*}

/-- A walk: a nonempty list of vertices in which consecutive vertices are adjacent. -/
def IsWalk (G : V → V → Prop) (l : List V) : Prop := l ≠ [] ∧ List.IsChain G l

/-- `Far G A B d`: every walk from a vertex of `A` to a vertex of `B` has at least `d` edges
(the distance between `A` and `B` is at least `d`; vacuous if there is no such walk). -/
def Far (G : V → V → Prop) (A B : Set V) (d : ℕ) : Prop :=
  ∀ l : List V, IsWalk G l → ∀ a ∈ l.head?, a ∈ A → ∀ b ∈ l.getLast?, b ∈ B → d + 1 ≤ l.length

/-- Every walk from `A` to `B` contains an edge between two vertices satisfying `act`. -/
def ActCut (G : V → V → Prop) (act : V → Prop) (A B : Set V) : Prop :=
  ∀ l : List V, IsWalk G l → ∀ a ∈ l.head?, a ∈ A → ∀ b ∈ l.getLast?, b ∈ B →
    ∃ u v, [u, v] <:+: l ∧ act u ∧ act v

variable {G G' : V → V → Prop}

lemma far_zero (A B : Set V) : Far G A B 0 := by
  intro l hl _ _ _ _ _ _
  have := List.length_pos_of_ne_nil hl.1
  omega

lemma Far.mono {A B A' B' : Set V} {d d' : ℕ} (h : Far G A B d) (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hd : d' ≤ d) : Far G A' B' d' := by
  intro l hl a ha haA b hb hbB
  have := h l hl a ha (hA haA) b hb (hB hbB)
  omega

lemma Far.disjoint {A B : Set V} {d : ℕ} (h : Far G A B (d + 1)) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro a haA haB
  have := h [a] ⟨by simp, List.isChain_singleton a⟩ a rfl haA a rfl haB
  simp at this

lemma far_union_left {A A' B : Set V} {d : ℕ} (h : Far G A B d) (h' : Far G A' B d) :
    Far G (A ∪ A') B d := by
  intro l hl a ha haA b hb hbB
  rcases haA with haA | haA
  · exact h l hl a ha haA b hb hbB
  · exact h' l hl a ha haA b hb hbB

lemma far_union_right {A B B' : Set V} {d : ℕ} (h : Far G A B d) (h' : Far G A B' d) :
    Far G A (B ∪ B') d := by
  intro l hl a ha haA b hb hbB
  rcases hbB with hbB | hbB
  · exact h l hl a ha haA b hb hbB
  · exact h' l hl a ha haA b hb hbB

/-- Symmetry of `Far` for a symmetric adjacency. -/
lemma Far.symm (hG : ∀ u v, G u v → G v u) {A B : Set V} {d : ℕ} (h : Far G A B d) :
    Far G B A d := by
  intro l hl a ha haA b hb hbB
  have := h l.reverse ⟨by simpa using hl.1, List.isChain_reverse.2 (hl.2.imp fun x y h => hG x y h)⟩
    b (by simpa using hb) hbB a (by simpa using ha) haA
  simpa using this

/-- A vertex all of whose neighbours are at distance `≥ d` from `B` (and which is not in `B`)
is at distance `≥ d + 1` from `B`. -/
lemma far_of_neighbors {s : V} {B : Set V} {d : ℕ} (hs : s ∉ B)
    (h : ∀ z, G s z → Far G {z} B d) : Far G {s} B (d + 1) := by
  intro l hl a ha haA b hb hbB
  obtain ⟨hne, hch⟩ := hl
  rcases l with _ | ⟨x, t⟩
  · simp at hne
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
  subst ha
  rw [Set.mem_singleton_iff] at haA
  subst haA
  rcases t with _ | ⟨z, t⟩
  · simp at hb
    subst hb
    exact absurd hbB hs
  rw [List.isChain_cons_cons] at hch
  have := h z hch.1 (z :: t) ⟨by simp, hch.2⟩ z rfl rfl b (by simpa using hb) hbB
  simp only [List.length_cons] at this ⊢
  omega

/-- Triangle inequality: if `z` is joined to `A` by a walk with `e` edges, and `A` is at distance
`≥ d + e` from `B`, then `z` is at distance `≥ d` from `B`. -/
lemma Far.of_walk (hG : ∀ u v, G u v → G v u) {A B : Set V} {d e : ℕ} (h : Far G A B (d + e))
    {l : List V} (hl : IsWalk G l) {z a : V} (hz : z ∈ l.head?) (ha : a ∈ l.getLast?) (haA : a ∈ A)
    (hlen : l.length ≤ e + 1) : Far G {z} B d := by
  intro m hm z' hz' hzz b hb hbB
  rw [Set.mem_singleton_iff] at hzz
  subst hzz
  obtain ⟨hne, hch⟩ := hm
  rcases m with _ | ⟨y, m⟩
  · simp at hne
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz'
  subst hz'
  have hlne : l ≠ [] := by rintro rfl; simp at hz
  have hrev : List.IsChain G l.reverse :=
    List.isChain_reverse.2 (hl.2.imp fun x y h => hG x y h)
  have hw : IsWalk G (l.reverse ++ m) := by
    refine ⟨by simp [hlne], hrev.append hch.tail ?_⟩
    intro x hx y hy
    rw [List.getLast?_reverse] at hx
    rw [Option.mem_unique hx hz]
    exact (List.isChain_cons.1 hch).1 y hy
  have hhead : a ∈ (l.reverse ++ m).head? := by
    rw [List.head?_append, List.head?_reverse, ha]; rfl
  have hlast : b ∈ (l.reverse ++ m).getLast? := by
    rw [List.getLast?_append, List.getLast?_reverse, hz]
    rcases m with _ | ⟨y, m⟩
    · simpa using hb
    · rw [List.getLast?_cons_cons] at hb
      rw [hb]; rfl
  have := h _ hw a hhead haA b hlast hbB
  simp only [List.length_append, List.length_reverse, List.length_cons] at this ⊢
  omega

/-- Same, for a neighbour. -/
lemma Far.of_adj (hG : ∀ u v, G u v → G v u) {A B : Set V} {d : ℕ} (h : Far G A B (d + 1))
    {a z : V} (haA : a ∈ A) (hz : G a z) : Far G {z} B d :=
  Far.of_walk (e := 1) hG h (l := [z, a]) ⟨by simp, by simp [hG a z hz]⟩ rfl rfl haA (by simp)

/-- `Far` can be checked vertex by vertex. -/
lemma far_of_forall_singleton {A B : Set V} {d : ℕ} (h : ∀ a ∈ A, Far G {a} B d) : Far G A B d := by
  intro l hl a ha haA b hb hbB
  exact h a haA l hl a ha rfl b hb hbB

/-- A *lazy walk* (consecutive vertices equal or adjacent) can be shortened to a walk with the same
endpoints; the walk is strictly shorter if two consecutive vertices of the lazy walk are equal. -/
lemma exists_walk_of_lazy {c : List V} (hne : c ≠ [])
    (hc : List.IsChain (fun a b => a = b ∨ G a b) c) :
    ∃ l, IsWalk G l ∧ l.head? = c.head? ∧ l.getLast? = c.getLast? ∧ l.length ≤ c.length ∧
      ((∃ z, [z, z] <:+: c) → l.length < c.length) := by
  induction c with
  | nil => exact absurd rfl hne
  | cons x t ih =>
    rcases t with _ | ⟨y, t⟩
    · refine ⟨[x], ⟨by simp, List.isChain_singleton x⟩, rfl, rfl, le_rfl, ?_⟩
      rintro ⟨z, hz⟩
      have := hz.length_le; simp at this
    rw [List.isChain_cons_cons] at hc
    obtain ⟨l, hl, hh, hlast, hlen, hdup⟩ := ih (by simp) hc.2
    simp only [List.length_cons] at hlen hdup ⊢
    by_cases hxy : x = y
    · subst hxy
      exact ⟨l, hl, by simpa using hh, by simpa [List.getLast?_cons_cons] using hlast, by omega,
        fun _ => by omega⟩
    · have hG : G x y := hc.1.resolve_left hxy
      rcases l with _ | ⟨w, l⟩
      · exact absurd rfl hl.1
      refine ⟨x :: w :: l, ⟨by simp, List.isChain_cons_cons.2 ⟨?_, hl.2⟩⟩, rfl, ?_, ?_, ?_⟩
      · simp only [List.head?_cons, Option.some.injEq] at hh
        rw [hh]; exact hG
      · rw [List.getLast?_cons_cons, List.getLast?_cons_cons, hlast]
      · simp only [List.length_cons] at hlen ⊢; omega
      · rintro ⟨z, hz⟩
        rw [List.infix_cons_iff] at hz
        rcases hz with hz | hz
        · simp [List.prefix_cons_iff] at hz
          exact absurd (hz.1.symm.trans hz.2) hxy
        · have := hdup ⟨z, hz⟩
          simp only [List.length_cons] at this ⊢; omega

/-- A lazy walk without repeated consecutive vertices is a walk. -/
lemma isChain_of_lazy {c : List V} (hc : List.IsChain (fun a b => a = b ∨ G a b) c)
    (hnd : ∀ z, ¬ [z, z] <:+: c) : List.IsChain G c := by
  induction c with
  | nil => exact List.isChain_nil
  | cons x t ih =>
    rcases t with _ | ⟨y, t⟩
    · exact List.isChain_singleton x
    rw [List.isChain_cons_cons] at hc ⊢
    refine ⟨hc.1.resolve_left ?_, ih hc.2 fun z hz => hnd z (List.infix_cons hz)⟩
    rintro rfl
    exact hnd x ⟨[], t, rfl⟩

/-- A pair of consecutive elements of `x.map f` comes from a pair of consecutive elements of `x`. -/
lemma exists_infix_of_infix_map (f : V → V) {u v : V} {x : List V} (h : [u, v] <:+: x.map f) :
    ∃ p q, [p, q] <:+: x ∧ f p = u ∧ f q = v := by
  induction x with
  | nil => have := h.length_le; simp at this
  | cons a t ih =>
    rw [List.map_cons, List.infix_cons_iff] at h
    rcases h with h | h
    · rcases t with _ | ⟨b, t⟩
      · have := h.length_le; simp at this
      simp [List.prefix_cons_iff] at h
      exact ⟨a, b, ⟨[], t, rfl⟩, h.1.symm, h.2.symm⟩
    · obtain ⟨p, q, hpq, rfl, rfl⟩ := ih h
      exact ⟨p, q, List.infix_cons hpq, rfl, rfl⟩

variable (car : V → Set V) (anc : V → V) (act : V → Prop)

/-- Core of Lemmas 4.11/4.13: pushing a walk of `G'` down to `G` along any choice `f x ∈ car x`
gives a lazy walk; hence the walk has `≥ d` edges, and `≥ d + 1` edges if the image has two equal
consecutive vertices. -/
lemma Far.lift (hcar : ∀ x y, G' x y → ∀ c ∈ car x, ∀ d ∈ car y, c = d ∨ G c d)
    {A B A' B' : Set V} (hA : ∀ x ∈ A', car x ⊆ A) (hB : ∀ x ∈ B', car x ⊆ B) {d : ℕ}
    (h : Far G A B d) (f : V → V) (hf : ∀ x, f x ∈ car x) {x : List V} (hx : IsWalk G' x)
    {a : V} (ha : a ∈ x.head?) (haA : a ∈ A') {b : V} (hb : b ∈ x.getLast?) (hbB : b ∈ B') :
    d + 1 ≤ x.length ∧ ((∃ z, [z, z] <:+: x.map f) → d + 1 + 1 ≤ x.length) := by
  have hc : List.IsChain (fun a b => a = b ∨ G a b) (x.map f) :=
    (List.isChain_map f).2 (hx.2.imp fun p q hpq => hcar p q hpq _ (hf p) _ (hf q))
  obtain ⟨l, hl, hh, hlast, hlen, hdup⟩ := exists_walk_of_lazy (by simpa using hx.1) hc
  have hfar := h l hl (f a) (by rw [hh, List.head?_map, ha]; rfl) (hA a haA (hf a))
    (f b) (by rw [hlast, List.getLast?_map, hb]; rfl) (hB b hbB (hf b))
  simp only [List.length_map] at hlen hdup
  exact ⟨by omega, fun hz => by have := hdup hz; omega⟩

/-- **Lemma 4.11** (carrier form): subdivision does not decrease distances. -/
theorem Far.subdiv (hanc : ∀ x, anc x ∈ car x)
    (hcar : ∀ x y, G' x y → ∀ c ∈ car x, ∀ d ∈ car y, c = d ∨ G c d)
    {A B A' B' : Set V} (hA : ∀ x ∈ A', car x ⊆ A) (hB : ∀ x ∈ B', car x ⊆ B) {d : ℕ}
    (h : Far G A B d) : Far G' A' B' d := by
  intro x hx a ha haA b hb hbB
  exact (Far.lift car hcar hA hB h anc hanc hx ha haA hb hbB).1

/-- **Lemma 4.13** (carrier form): if every walk between `A` and `B` uses an edge between two
active vertices, subdivision strictly increases the distance. -/
theorem Far.subdiv_succ (hanc : ∀ x, anc x ∈ car x)
    (hcar : ∀ x y, G' x y → ∀ c ∈ car x, ∀ d ∈ car y, c = d ∨ G c d)
    (hnest : ∀ x y, G' x y → act (anc x) → act (anc y) → car x ⊆ car y ∨ car y ⊆ car x)
    {A B A' B' : Set V} (hA : ∀ x ∈ A', car x ⊆ A) (hB : ∀ x ∈ B', car x ⊆ B) {d : ℕ}
    (h : Far G A B d) (hcut : ActCut G act A B) : Far G' A' B' (d + 1) := by
  classical
  intro x hx a ha haA b hb hbB
  have hl := Far.lift car hcar hA hB h
  by_cases hdup : ∃ z, [z, z] <:+: x.map anc
  · exact (hl anc hanc hx ha haA hb hbB).2 hdup
  push Not at hdup
  have hc : List.IsChain (fun a b => a = b ∨ G a b) (x.map anc) :=
    (List.isChain_map anc).2 (hx.2.imp fun p q hpq => hcar p q hpq _ (hanc p) _ (hanc q))
  have hG := isChain_of_lazy hc hdup
  obtain ⟨u, v, huv, hu, hv⟩ := hcut _ ⟨by simpa using hx.1, hG⟩ (anc a)
    (by rw [List.head?_map, ha]; rfl) (hA a haA (hanc a)) (anc b)
    (by rw [List.getLast?_map, hb]; rfl) (hB b hbB (hanc b))
  obtain ⟨p, q, hpq, rfl, rfl⟩ := exists_infix_of_infix_map anc huv
  have hG' : G' p q := by simpa using hx.2.infix hpq
  -- modify the choice at one end of the edge `p — q` so that both ends get the same image
  have key : ∀ f : V → V, (∀ y, f y ∈ car y) → f p = f q → d + 1 + 1 ≤ x.length := by
    intro f hf hfpq
    refine (hl f hf hx ha haA hb hbB).2 ⟨f p, ?_⟩
    have h2 := List.IsInfix.map f hpq
    rw [List.map_cons, List.map_cons, List.map_nil, ← hfpq] at h2
    exact h2
  rcases hnest p q hG' hu hv with hsub | hsub
  · refine key (Function.update anc q (anc p)) ?_ ?_
    · intro y
      by_cases hy : y = q
      · subst hy; simpa using hsub (hanc p)
      · simp [hy, hanc]
    · by_cases hpq' : p = q
      · rw [hpq']
      · simp [hpq']
  · refine key (Function.update anc p (anc q)) ?_ ?_
    · intro y
      by_cases hy : y = p
      · subst hy; simpa using hsub (hanc q)
      · simp [hy, hanc]
    · by_cases hpq' : q = p
      · rw [hpq']
      · simp [hpq']

end Cslib.NIS.Subdiv
