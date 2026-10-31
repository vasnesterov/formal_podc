import Papers.PODC2016.AnalysingSI.CycleDefs

/-!
# Cycles in edge-labelled graphs

The dynamic criteria of Cerone–Gotsman (Theorems 16, 19, 22) talk about *cycles* of dependency
graphs and chopping graphs and the labels of their edges ("two adjacent anti-dependency edges",
"conflict, predecessor, conflict", …). We represent an edge-labelled multigraph on `α` by a family
of relations `E : L → α → α → Prop` (`E l a b`: an `l`-labelled edge from `a` to `b`).

* `Walk E a w b`: `w = [(l₁, v₁), …, (lₖ, vₖ)]` describes the walk `a —l₁→ v₁ —l₂→ ⋯ —lₖ→ vₖ = b`.
* `IsCycle E w`: `w` is a nonempty closed walk (cycles may repeat vertices, as in §A.5 of the
  paper); its vertices are `w.map Prod.snd`, its labels `w.map Prod.fst`; it is *simple*
  (`IsSimple`) if no vertex repeats.
* `CycAdj P ls`: two cyclically consecutive labels of the cyclic sequence `ls` satisfy `P`.

Main facts: rotation invariance, Lemma 24 (a cycle without adjacent `P`-pairs contains a simple
one), and the translation between cycles and the relations `(B ; A?)⁺`, `B⁺ ; A?`.
-/

-- CSLib candidate: generic relation/walk lemmas (Cslib/Foundations/Data/Relation or Combinatorics)
namespace Podc.AnalysingSI

open Relation

variable {α L : Type*}

theorem Walk.append {E : L → α → α → Prop} {a b c : α} {w w' : List (L × α)}
    (h : Walk E a w b) (h' : Walk E b w' c) : Walk E a (w ++ w') c := by
  induction h with
  | nil => exact h'
  | cons he _ ih => exact Walk.cons he (ih h')

theorem Walk.append_iff {E : L → α → α → Prop} {a c : α} {w w' : List (L × α)} :
    Walk E a (w ++ w') c ↔ ∃ b, Walk E a w b ∧ Walk E b w' c := by
  constructor
  · intro h
    induction w generalizing a with
    | nil => exact ⟨a, Walk.nil a, h⟩
    | cons x w ih =>
      cases h with
      | cons he hw =>
        obtain ⟨b, h1, h2⟩ := ih hw
        exact ⟨b, Walk.cons he h1, h2⟩
  · rintro ⟨b, h1, h2⟩
    exact h1.append h2

theorem IsCycle.rotate {E : L → α → α → Prop} {w : List (L × α)} (h : IsCycle E w) (k : ℕ) :
    IsCycle E (w.rotate k) := by
  obtain ⟨hne, a, ha⟩ := h
  refine ⟨fun h' => hne (List.rotate_eq_nil_iff.mp h'), ?_⟩
  rw [List.rotate_eq_drop_append_take_mod]
  rw [← List.take_append_drop (k % w.length) w, Walk.append_iff] at ha
  obtain ⟨b, h1, h2⟩ := ha
  exact ⟨b, h2.append h1⟩

theorem IsSimple.rotate {w : List (L × α)} (h : IsSimple w) (k : ℕ) : IsSimple (w.rotate k) := by
  unfold IsSimple at *
  rw [List.map_rotate]
  exact List.nodup_rotate.mpr h

theorem labels_rotate (w : List (L × α)) (k : ℕ) : labels (w.rotate k) = (labels w).rotate k := by
  unfold labels
  rw [List.map_rotate]

theorem cycAdj_rotate_one {P : L → L → Prop} {ls : List L} (h : CycAdj P ls) :
    CycAdj P (ls.rotate 1) := by
  rcases ls with _ | ⟨x, t⟩
  · simpa using h
  simp only [List.rotate_cons_succ, List.rotate_zero]
  rcases h with ⟨pre, a, b, suf, he, hab⟩ | ⟨a, mid, b, he, hba⟩
  · rcases pre with _ | ⟨y, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨h1, h2⟩ := he
      subst h2
      exact Or.inr ⟨b, suf, x, by simp, h1 ▸ hab⟩
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨h1, h2⟩ := he
      subst h2
      exact Or.inl ⟨pre, a, b, suf ++ [x], by simp, hab⟩
  · simp only [List.cons.injEq] at he
    obtain ⟨h1, h2⟩ := he
    subst h2
    exact Or.inl ⟨mid, b, x, [], by simp, h1 ▸ hba⟩

theorem cycAdj_rotate {P : L → L → Prop} {ls : List L} (h : CycAdj P ls) (k : ℕ) :
    CycAdj P (ls.rotate k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := cycAdj_rotate_one ih
    rwa [List.rotate_rotate] at this

theorem cycAdj_rotate_iff {P : L → L → Prop} {ls : List L} (k : ℕ) :
    CycAdj P (ls.rotate k) ↔ CycAdj P ls := by
  refine ⟨fun h => ?_, fun h => cycAdj_rotate h k⟩
  rcases Nat.eq_zero_or_pos ls.length with hl | hl
  · rw [List.length_eq_zero_iff] at hl
    subst hl
    simpa using h
  have h' := cycAdj_rotate h (ls.length * (k + 1) - k)
  rw [List.rotate_rotate, Nat.add_sub_cancel' (by nlinarith), List.rotate_length_mul] at h'
  exact h'

/-- Filtering a rotated list gives a rotation of the filtered list. -/
theorem exists_filter_rotate (p : L → Bool) (ls : List L) (k : ℕ) :
    ∃ k', (ls.rotate k).filter p = (ls.filter p).rotate k' := by
  refine ⟨((ls.take (k % ls.length)).filter p).length, ?_⟩
  have hls : ls.filter p = (ls.take (k % ls.length)).filter p ++
      (ls.drop (k % ls.length)).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [hls, List.rotate_append_length_eq, List.rotate_eq_drop_append_take_mod, List.filter_append]

/-- Adjacent pairs survive filtering, provided both members pass the filter. -/
theorem CycAdj.filter {P : L → L → Prop} {p : L → Bool} (hP : ∀ a b, P a b → p a ∧ p b)
    {ls : List L} (h : CycAdj P ls) : CycAdj P (ls.filter p) := by
  rcases h with ⟨pre, a, b, suf, rfl, hab⟩ | ⟨a, mid, b, rfl, hba⟩
  · obtain ⟨ha, hb⟩ := hP a b hab
    exact Or.inl ⟨pre.filter p, a, b, suf.filter p, by simp [List.filter_append, ha, hb], hab⟩
  · obtain ⟨hb, ha⟩ := hP b a hba
    exact Or.inr ⟨a, mid.filter p, b, by simp [List.filter_append, ha, hb], hba⟩

/-- The edges of a walk are edges of the graph. -/
theorem Walk.mono {E E' : L → α → α → Prop} {a b : α} {w : List (L × α)}
    (hE : ∀ l ∈ labels w, ∀ x y, E l x y → E' l x y) (h : Walk E a w b) : Walk E' a w b := by
  induction h with
  | nil => exact Walk.nil _
  | cons he _ ih =>
    simp only [labels, List.map_cons, List.mem_cons] at hE
    exact Walk.cons (hE _ (Or.inl rfl) _ _ he) (ih fun l hl => hE l (Or.inr hl))

/-- Relabelling a walk. -/
theorem Walk.map {L' : Type*} {E : L → α → α → Prop} {E' : L' → α → α → Prop} (f : L → L')
    {a b : α} {w : List (L × α)}
    (hE : ∀ l ∈ labels w, ∀ x y, E l x y → E' (f l) x y) (h : Walk E a w b) :
    Walk E' a (w.map (Prod.map f id)) b := by
  induction h with
  | nil => exact Walk.nil _
  | cons he _ ih =>
    simp only [labels, List.map_cons, List.mem_cons] at hE
    exact Walk.cons (hE _ (Or.inl rfl) _ _ he) (ih fun l hl => hE l (Or.inr hl))

/-- Linear adjacency: two consecutive elements `a, b` of `ls` satisfy `P a b`. -/
def LinAdj (P : L → L → Prop) : List L → Prop
  | a :: b :: t => P a b ∨ LinAdj P (b :: t)
  | _ => False

theorem linAdj_iff {P : L → L → Prop} : ∀ {ls : List L},
    LinAdj P ls ↔ ∃ pre a b suf, ls = pre ++ a :: b :: suf ∧ P a b
  | [] => by simp [LinAdj]
  | [x] => by
      simp only [LinAdj, false_iff, not_exists, not_and]
      intro pre a b suf h
      have := congrArg List.length h
      simp at this
      omega
  | a :: b :: t => by
      simp only [LinAdj]
      rw [linAdj_iff]
      constructor
      · rintro (h | ⟨pre, c, d, suf, he, hcd⟩)
        · exact ⟨[], a, b, t, rfl, h⟩
        · exact ⟨a :: pre, c, d, suf, by simp [he], hcd⟩
      · rintro ⟨pre, c, d, suf, he, hcd⟩
        rcases pre with _ | ⟨y, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact Or.inl hcd
        · simp only [List.cons_append, List.cons.injEq] at he
          exact Or.inr ⟨pre, c, d, suf, he.2, hcd⟩

theorem cycAdj_iff_linAdj {P : L → L → Prop} {ls : List L} :
    CycAdj P ls ↔ LinAdj P ls ∨ ∃ a mid b, ls = a :: (mid ++ [b]) ∧ P b a := by
  rw [CycAdj, linAdj_iff]

/-- A nonempty walk whose labels satisfy `Q` yields a `TransGen` path of `Q`-labelled edges. -/
theorem Walk.transGen {E : L → α → α → Prop} {Q : L → Prop} {a b : α} {w : List (L × α)}
    (h : Walk E a w b) (hw : w ≠ []) (hQ : ∀ l ∈ labels w, Q l) :
    TransGen (fun x y => ∃ l, Q l ∧ E l x y) a b := by
  induction h with
  | nil => exact absurd rfl hw
  | @cons a b c l w he hw' ih =>
    simp only [labels, List.map_cons, List.mem_cons] at hQ
    rcases w with _ | ⟨x, w⟩
    · cases hw'
      exact TransGen.single ⟨l, hQ l (Or.inl rfl), he⟩
    · exact TransGen.head ⟨l, hQ l (Or.inl rfl), he⟩
        (ih (List.cons_ne_nil _ _) fun l' hl' => hQ l' (Or.inr hl'))

/-- A `TransGen` path of `Q`-labelled edges yields a nonempty walk with labels in `Q`. -/
theorem exists_walk_of_transGen {E : L → α → α → Prop} {Q : L → Prop} {a b : α}
    (h : TransGen (fun x y => ∃ l, Q l ∧ E l x y) a b) :
    ∃ w, w ≠ [] ∧ (∀ l ∈ labels w, Q l) ∧ Walk E a w b := by
  induction h with
  | single h =>
    obtain ⟨l, hl, he⟩ := h
    exact ⟨[(l, _)], by simp, by simp [labels, hl], Walk.cons he (Walk.nil _)⟩
  | tail _ h ih =>
    obtain ⟨l, hl, he⟩ := h
    obtain ⟨w, hne, hQ, hw⟩ := ih
    refine ⟨w ++ [(l, _)], by simp, ?_, hw.append (Walk.cons he (Walk.nil _))⟩
    intro l' hl'
    simp only [labels, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hl'
    rcases hl' with hl' | rfl
    · exact hQ l' hl'
    · exact hl

/-- A list of vertices with a repetition splits around two equal vertices. -/
theorem exists_dup_split {w : List (L × α)} (h : ¬ (w.map Prod.snd).Nodup) :
    ∃ A x B y C, w = A ++ x :: (B ++ y :: C) ∧ x.2 = y.2 := by
  induction w with
  | nil => simp at h
  | cons z w ih =>
    rw [List.map_cons, List.nodup_cons, not_and_or, not_not] at h
    rcases h with h | h
    · obtain ⟨y, hy, hyz⟩ := List.mem_map.mp h
      obtain ⟨B, C, rfl⟩ := List.append_of_mem hy
      exact ⟨[], z, B, y, C, rfl, hyz.symm⟩
    · obtain ⟨A, x, B, y, C, rfl, hxy⟩ := ih h
      exact ⟨z :: A, x, B, y, C, rfl, hxy⟩

/-- For a "rectangular" `P` (`P a b → P c d → P a d`), cyclic adjacency in both halves gives
cyclic adjacency in the concatenation. -/
theorem cycAdj_append {P : L → L → Prop} (hP : ∀ a b c d, P a b → P c d → P a d)
    {l₁ l₂ : List L} (h₁ : CycAdj P l₁) (h₂ : CycAdj P l₂) : CycAdj P (l₁ ++ l₂) := by
  rcases h₁ with ⟨pre, a, b, suf, rfl, hab⟩ | ⟨a, mid, b, rfl, hba⟩
  · exact Or.inl ⟨pre, a, b, suf ++ l₂, by simp, hab⟩
  rcases h₂ with ⟨pre, c, d, suf, rfl, hcd⟩ | ⟨c, mid', d, rfl, hdc⟩
  · exact Or.inl ⟨a :: mid ++ [b] ++ pre, c, d, suf, by simp, hcd⟩
  · exact Or.inl ⟨a :: mid, b, c, mid' ++ [d], by simp, hP b a d c hba hdc⟩

/-- **Lemma 24** of Cerone–Gotsman (generalised to any "rectangular" adjacency predicate `P`,
i.e. `P a b → P c d → P a d`, e.g. `P a b ↔ a = r ∧ b = r`): if a graph has a cycle with no two
adjacent `P`-related labels, it has a simple such cycle. (For an arbitrary `P` the statement is
false.) -/
theorem lemma24 {E : L → α → α → Prop} {P : L → L → Prop}
    (hP' : ∀ a b c d, P a b → P c d → P a d) {w : List (L × α)}
    (hw : IsCycle E w) (hP : ¬ CycAdj P (labels w)) :
    ∃ w', IsCycle E w' ∧ IsSimple w' ∧ ¬ CycAdj P (labels w') := by
  suffices H : ∀ n, ∀ w : List (L × α), w.length = n → IsCycle E w → ¬ CycAdj P (labels w) →
      ∃ w', IsCycle E w' ∧ IsSimple w' ∧ ¬ CycAdj P (labels w') from H _ w rfl hw hP
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn hw hP
  by_cases hs : IsSimple w
  · exact ⟨w, hw, hs, hP⟩
  obtain ⟨A, ⟨lx, u⟩, B, ⟨ly, u'⟩, C, rfl, hxy⟩ := exists_dup_split hs
  simp only at hxy
  subst hxy
  obtain ⟨-, a, ha⟩ := hw
  rw [Walk.append_iff] at ha
  obtain ⟨b, hA, hxBC⟩ := ha
  cases hxBC with
  | cons hex hBC =>
  rw [Walk.append_iff] at hBC
  obtain ⟨c, hB, hyC⟩ := hBC
  cases hyC with
  | cons hey hC =>
  have hq : Walk E u (B ++ [(ly, u)]) u := hB.append (Walk.cons hey (Walk.nil _))
  have hr : Walk E u (C ++ A ++ [(lx, u)]) u := (hC.append hA).append (Walk.cons hex (Walk.nil _))
  have hrot : (A ++ (lx, u) :: (B ++ (ly, u) :: C)).rotate (A ++ [(lx, u)]).length =
      (B ++ [(ly, u)]) ++ (C ++ A ++ [(lx, u)]) := by
    have : A ++ (lx, u) :: (B ++ (ly, u) :: C) = (A ++ [(lx, u)]) ++ (B ++ (ly, u) :: C) := by
      simp
    rw [this, List.rotate_append_length_eq]
    simp
  have hP2 : ¬ CycAdj P (labels (B ++ [(ly, u)]) ++ labels (C ++ A ++ [(lx, u)])) := by
    intro h
    apply hP
    rw [← cycAdj_rotate_iff (A ++ [(lx, u)]).length, ← labels_rotate, hrot, labels,
      List.map_append]
    exact h
  have hlen : (A ++ (lx, u) :: (B ++ (ly, u) :: C)).length =
      A.length + B.length + C.length + 2 := by simp; omega
  by_cases hq' : CycAdj P (labels (B ++ [(ly, u)]))
  · have hr' : ¬ CycAdj P (labels (C ++ A ++ [(lx, u)])) := fun h =>
      hP2 (cycAdj_append hP' hq' h)
    exact ih _ (by rw [← hn, hlen]; simp; omega) _ rfl ⟨by simp, u, hr⟩ hr'
  · exact ih _ (by rw [← hn, hlen]; simp; omega) _ rfl ⟨by simp, u, hq⟩ hq'

/-- A graph has a cycle iff the union of its edge relations is cyclic. -/
theorem exists_cycle_iff {E : L → α → α → Prop} :
    (∃ w, IsCycle E w) ↔ ∃ a, TransGen (fun x y => ∃ l, E l x y) a a := by
  constructor
  · rintro ⟨w, hne, a, ha⟩
    exact ⟨a, TransGen.mono (fun x y ⟨l, _, h⟩ => ⟨l, h⟩) _ _
      (ha.transGen (Q := fun _ => True) hne fun _ _ => trivial)⟩
  · rintro ⟨a, ha⟩
    obtain ⟨w, hne, -, hw⟩ := exists_walk_of_transGen (Q := fun _ => True) (E := E)
      (TransGen.mono (fun x y ⟨l, h⟩ => ⟨l, trivial, h⟩) _ _ ha)
    exact ⟨w, hne, a, hw⟩

/-- A path of `(B ; A?)⁺` yields a walk whose first label is not `r` and without two consecutive
`r`-labels. -/
theorem exists_walk_of_transGen_comp {E : L → α → α → Prop} {r : L} {a b : α}
    (h : TransGen (Comp (fun x y => ∃ l, l ≠ r ∧ E l x y) (ReflGen (E r))) a b) :
    ∃ x w, Walk E a (x :: w) b ∧ x.1 ≠ r ∧
      ¬ LinAdj (fun x y => x = r ∧ y = r) (labels (x :: w)) := by
  induction h using TransGen.head_induction_on with
  | single h =>
    obtain ⟨m, ⟨l, hl, he⟩, hA⟩ := h
    cases hA with
    | refl => exact ⟨(l, _), [], Walk.cons he (Walk.nil _), hl, by simp [LinAdj, labels]⟩
    | single h' =>
      exact ⟨(l, _), [(r, _)], Walk.cons he (Walk.cons h' (Walk.nil _)), hl,
        by simp [LinAdj, labels, hl]⟩
  | head h _ ih =>
    obtain ⟨y, w, hw, hy, hlin⟩ := ih
    obtain ⟨m, ⟨l, hl, he⟩, hA⟩ := h
    simp only [labels, List.map_cons] at hlin
    cases hA with
    | refl =>
      refine ⟨(l, _), y :: w, Walk.cons he hw, hl, ?_⟩
      simp only [labels, List.map_cons]
      simp [LinAdj, hl, hlin]
    | single h' =>
      refine ⟨(l, _), (r, _) :: y :: w, Walk.cons he (Walk.cons h' hw), hl, ?_⟩
      simp only [labels, List.map_cons]
      simp [LinAdj, hl, hy, hlin]

/-- A walk whose first label is not `r` and without two consecutive `r`-labels yields a path of
`(B ; A?)⁺`. -/
theorem transGen_comp_of_walk {E : L → α → α → Prop} {r : L} :
    ∀ {a b : α} {l : L} {v : α} {w : List (L × α)}, l ≠ r → Walk E a ((l, v) :: w) b →
      ¬ LinAdj (fun x y => x = r ∧ y = r) (labels ((l, v) :: w)) →
      TransGen (Comp (fun x y => ∃ l, l ≠ r ∧ E l x y) (ReflGen (E r))) a b
  | a, b, l, v, [], hl, h, _ => by
      cases h with
      | cons he hw =>
        cases hw
        exact TransGen.single ⟨_, ⟨l, hl, he⟩, ReflGen.refl⟩
  | a, b, l, v, (l2, v2) :: w, hl, h, hlin => by
      cases h with
      | cons he hw =>
      by_cases hl2 : l2 = r
      · cases hw with
        | cons he2 hw2 =>
        rcases w with _ | ⟨⟨l3, v3⟩, w⟩
        · cases hw2
          exact TransGen.single ⟨v, ⟨l, hl, he⟩, ReflGen.single (hl2 ▸ he2)⟩
        · have hl3 : l3 ≠ r := by
            intro h
            apply hlin
            simp [labels, LinAdj, hl2, h]
          refine TransGen.head ⟨v, ⟨l, hl, he⟩, ReflGen.single (hl2 ▸ he2)⟩
            (transGen_comp_of_walk hl3 hw2 fun h => hlin ?_)
          simp only [labels, List.map_cons] at h ⊢
          exact Or.inr (Or.inr h)
      · refine TransGen.head ⟨v, ⟨l, hl, he⟩, ReflGen.refl⟩
          (transGen_comp_of_walk hl2 hw fun h => hlin ?_)
        simp only [labels, List.map_cons] at h ⊢
        exact Or.inr h

/-- With `B` the union of the edges labelled other than `r` and `A` the `r`-edges (assumed
irreflexive), `(B ; A?)⁺` is cyclic iff there is a cycle without two adjacent `r`-labels. -/
theorem exists_transGen_comp_iff {E : L → α → α → Prop} (r : L) (hirr : ∀ a, ¬ E r a a) :
    (∃ a, TransGen (Comp (fun x y => ∃ l, l ≠ r ∧ E l x y) (ReflGen (E r))) a a) ↔
      ∃ w, IsCycle E w ∧ ¬ CycAdj (fun x y => x = r ∧ y = r) (labels w) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x, w, hw, hx, hlin⟩ := exists_walk_of_transGen_comp ha
    refine ⟨x :: w, ⟨List.cons_ne_nil _ _, a, hw⟩, ?_⟩
    rw [cycAdj_iff_linAdj]
    rintro (h | ⟨a', mid, b', he, -, ha'⟩)
    · exact hlin h
    · simp only [labels, List.map_cons, List.cons.injEq] at he
      exact hx (he.1 ▸ ha')
  · rintro ⟨w, hw, hP⟩
    have hex : ∃ x ∈ w, x.1 ≠ r := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      obtain ⟨hne, a, ha⟩ := hw
      rcases w with _ | ⟨x, _ | ⟨y, w⟩⟩
      · exact hne rfl
      · cases ha with
        | cons he hw' =>
          cases hw'
          have h := hall _ (List.mem_singleton_self _)
          simp only at h
          exact hirr _ (h ▸ he)
      · apply hP
        exact Or.inl ⟨[], x.1, y.1, labels w, rfl, hall x (by simp), hall y (by simp)⟩
    obtain ⟨⟨lx, vx⟩, hxw, hxr⟩ := hex
    obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hxw
    have hc := hw.rotate pre.length
    rw [List.rotate_append_length_eq] at hc
    obtain ⟨-, c, hc⟩ := hc
    have hP' := hP
    rw [← cycAdj_rotate_iff pre.length, ← labels_rotate, List.rotate_append_length_eq,
      cycAdj_iff_linAdj, not_or] at hP'
    exact ⟨c, transGen_comp_of_walk hxr hc hP'.1⟩

/-- With `B`, `A` as above, `B⁺ ; A?` is reflexive somewhere iff there is a cycle with at most one
`r`-label. -/
theorem exists_comp_transGen_iff [DecidableEq L] {E : L → α → α → Prop} (r : L)
    (hirr : ∀ a, ¬ E r a a) :
    (∃ a, Comp (TransGen (fun x y => ∃ l, l ≠ r ∧ E l x y)) (ReflGen (E r)) a a) ↔
      ∃ w, IsCycle E w ∧ (labels w).count r ≤ 1 := by
  constructor
  · rintro ⟨a, m, hT, hA⟩
    obtain ⟨w, hne, hQ, hw⟩ := exists_walk_of_transGen (Q := fun l => l ≠ r) hT
    have h0 : (labels w).count r = 0 := List.count_eq_zero.mpr fun h => hQ r h rfl
    cases hA with
    | refl => exact ⟨w, ⟨hne, a, hw⟩, by omega⟩
    | single h =>
      refine ⟨w ++ [(r, a)], ⟨by simp, a, hw.append (Walk.cons h (Walk.nil _))⟩, ?_⟩
      have : labels (w ++ [(r, a)]) = labels w ++ [r] := by simp [labels]
      rw [this, List.count_append]
      simp [h0]
  · rintro ⟨w, ⟨hne, a, ha⟩, hc⟩
    by_cases hr : r ∈ labels w
    · obtain ⟨⟨l, u⟩, hx, hl⟩ := List.mem_map.mp hr
      simp only at hl
      subst hl
      obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hx
      have hlab : labels (pre ++ (l, u) :: suf) = labels pre ++ l :: labels suf := by
        simp [labels]
      rw [hlab, List.count_append, List.count_cons_self] at hc
      have hpre : l ∉ labels pre := List.count_eq_zero.mp (by omega)
      have hsuf : l ∉ labels suf := List.count_eq_zero.mp (by omega)
      rw [Walk.append_iff] at ha
      obtain ⟨b, hpre', hsuf'⟩ := ha
      cases hsuf' with
      | cons he hs =>
      have hw' := hs.append hpre'
      by_cases h0 : suf ++ pre = []
      · rw [h0] at hw'
        cases hw'
        exact absurd he (hirr _)
      refine ⟨u, b, hw'.transGen (Q := fun l' => l' ≠ l) h0 ?_, ReflGen.single he⟩
      intro l' hl' h
      subst h
      simp only [labels, List.map_append, List.mem_append] at hl'
      rcases hl' with h | h
      · exact hsuf h
      · exact hpre h
    · refine ⟨a, a, ha.transGen (Q := fun l => l ≠ r) hne ?_, ReflGen.refl⟩
      intro l hl h
      exact hr (h ▸ hl)

end Podc.AnalysingSI
