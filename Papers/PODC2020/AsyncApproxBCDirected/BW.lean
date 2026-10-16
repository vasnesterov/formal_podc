import Papers.PODC2020.AsyncApproxBCDirected.RoundModel

/-!
# Properties of Algorithm BW (Lemmas 6–8, Theorem 9)

* Flooding facts: values along paths of correct nodes (`acc_append`, `value_of_avoids`), relaying
  (`mem_of_accepted`), and the converse (`accepted_of_mem`).
* `sent_actual` — **Lemma 6**: every correct node eventually satisfies Maximal-Consistency in its
  thread for the actual fault set `F`, hence sends `COMPLETE(F)`.
* `lemma7` — **Lemma 7**: two correct nodes that pass Maximal-Consistency on the same set `F'`
  report the same value for every node of every source component `S_{F',F''}`.
* `completeness_eventually` — **Lemma 8**: a correct node eventually satisfies
  `Completeness(Mv, M^c, Fu)` for every genuine `COMPLETE(Fu)` message of a correct `c`.
* `exists_executes` — **Theorem 9**: every correct node eventually executes Filter-and-Average.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-! ## Lists and paths -/

theorem getLast?_append_of {a b : List V} {z : V} (ha : a.getLast? = some z) :
    (a ++ b).getLast? = (z :: b).getLast? := by
  rw [List.getLast?_append, ha, List.getLast?_cons]
  cases b.getLast? <;> rfl

theorem avoids_append {a b : List V} {X : Finset V} (ha : Avoids a X) (hb : Avoids b X) :
    Avoids (a ++ b) X := fun y hy => by
  rcases List.mem_append.mp hy with h | h
  · exact ha y h
  · exact hb y h

theorem Avoids.mono {p : List V} {X Y : Finset V} (h : Avoids p Y) (hXY : X ⊆ Y) : Avoids p X :=
  fun y hy hx => h y hy (hXY hx)

theorem avoids_union {p : List V} {X Y : Finset V} : Avoids p (X ∪ Y) ↔ Avoids p X ∧ Avoids p Y :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun h y hy hxy => (mem_union.mp hxy).elim (h.1 y hy) (h.2 y hy)⟩

theorem IsSimplePath.eq_cons {p : List V} {a b : V} (h : IsSimplePath G p a b) : p = a :: p.tail := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp h.1.1
  simp [hys]

theorem IsSimplePath.redundant_append {a b : List V} {q z w : V} (ha : IsSimplePath G a q z)
    (hb : IsSimplePath G b z w) : IsRedundant G (a ++ b.tail) := ⟨a, b, q, z, w, ha, hb, rfl⟩

theorem IsSimplePath.getLast_append {a b : List V} {q z w : V} (ha : IsSimplePath G a q z)
    (hb : IsSimplePath G b z w) : (a ++ b.tail).getLast? = some w := by
  rw [getLast?_append_of ha.1.2.1, ← hb.eq_cons]; exact hb.1.2.1

theorem IsSimplePath.head_append {a : List V} {q z : V} (ha : IsSimplePath G a q z) (b : List V) :
    (a ++ b).head? = some q := by
  rw [ha.eq_cons]; simp

/-- Every node of a path to `b` avoiding `X` reaches `b` while avoiding `X`. -/
theorem IsPathFT.reaches_of_mem {p : List V} {a b : V} (h : IsPathFT G p a b) {X : Finset V}
    (hX : Avoids p X) : ∀ y ∈ p, Reaches G X y b := by
  induction p generalizing a with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hh, hl, hc⟩ := h
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    intro y hy
    rcases l with _ | ⟨x', l'⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at hl
      simp only [List.mem_singleton] at hy
      subst hl hy; exact Reaches.refl (hX _ (by simp))
    · have hc' : (x' :: l').IsChain G.Adj := hc.tail
      have ih' := ih (a := x') ⟨rfl, by simpa using hl, hc'⟩ (fun z hz => hX z (by simp [hz]))
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (ih' x' (by simp)).head (List.isChain_cons_cons.mp hc).1 (hX _ (by simp))
      · exact ih' y hy

/-- The prefix `z :: b` of a simple path `z :: b ++ [w]`. -/
theorem IsSimplePath.of_snoc {b : List V} {z w : V} (h : IsSimplePath G (z :: (b ++ [w])) z w) :
    ∃ q, IsSimplePath G (z :: b) z q ∧ G.Adj q w ∧ q ≠ w ∧ (z :: b).getLast? = some q := by
  obtain ⟨⟨-, -, hc⟩, hn⟩ := h
  have hc' : List.IsChain G.Adj ((z :: b) ++ [w]) := hc
  have hn' : ((z :: b) ++ [w]).Nodup := hn
  set q := (z :: b).getLast (List.cons_ne_nil _ _)
  have hq : (z :: b).getLast? = some q := List.getLast?_eq_some_getLast _
  rw [List.isChain_append] at hc'
  rw [List.nodup_append] at hn'
  refine ⟨q, ⟨⟨rfl, hq, hc'.1⟩, hn'.1⟩, hc'.2.2 q hq w (by simp), ?_, hq⟩
  exact hn'.2.2 q (List.getLast_mem _) w (by simp)

/-! ## Choosing a common time -/

theorem exists_time {ι : Type*} {s : Set ι} (hs : s.Finite) {P : ι → ℕ → Prop}
    (hmono : ∀ i t t', t ≤ t' → P i t → P i t') (h : ∀ i ∈ s, ∃ t, P i t) :
    ∃ T, ∀ i ∈ s, P i T := by
  classical
  let g : ι → ℕ := fun i => if hi : i ∈ s then Classical.choose (h i hi) else 0
  refine ⟨hs.toFinset.sup g, fun i hi => hmono i (g i) _ ?_ ?_⟩
  · exact Finset.le_sup (f := g) (hs.mem_toFinset.mpr hi)
  · simp only [g, hi, dite_true]; exact Classical.choose_spec (h i hi)

theorem finite_simplePaths (P : List V → Prop) (hP : ∀ p, P p → p.Nodup) : {p | P p}.Finite :=
  (List.finite_length_le V (Fintype.card V)).subset fun p hp => (hP p hp).length_le_card

theorem IsRedundant.length_le {p : List V} (h : IsRedundant G p) :
    p.length ≤ 2 * Fintype.card V := by
  obtain ⟨p₁, p₂, _, _, _, h₁, h₂, rfl⟩ := h
  have := h₁.2.length_le_card
  have := h₂.2.length_le_card
  simp only [List.length_append, List.length_tail]
  omega

namespace RoundExec

variable (E : RoundExec G f)

/-! ## Flooding -/

/-- Values do not change along correct relays. -/
theorem acc_append (b : List V) : ∀ (a : List V) (z : V), a.getLast? = some z →
    Avoids (z :: b) E.F → E.acc (a ++ b) = E.acc a := by
  induction b with
  | nil => intros; simp
  | cons w b ih =>
    intro a z ha hb
    have h1 := ih (a ++ [w]) w (by simp) (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    rw [List.append_assoc] at h1
    simp only [List.singleton_append] at h1
    rw [h1, E.acc_snoc a z w ha (hb z (by simp))]

/-- A message received along a path of correct nodes carries the input of its initial node. -/
theorem value_of_avoids {v : V} (hv : v ∉ E.F) {t : ℕ} {y : ℝ} {p : List V}
    (hm : (y, p) ∈ E.M v t) (hp : Avoids p E.F) {s : V} (hs : p.head? = some s) : y = E.x s := by
  obtain ⟨p₀, rfl⟩ := List.getLast?_eq_some_iff.mp (E.M_last v hv t _ hm)
  have hy := E.M_honest v hv t y p₀ hm (fun q hq => hp q (List.mem_append_left _
    (List.mem_of_getLast? hq)))
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hs
  rw [hy, hys]
  have hsF : s ∉ E.F := hp s (by rw [hys]; simp)
  have := E.acc_append ys [s] s (by simp) (by rw [← hys]; exact hp)
  simp only [List.singleton_append] at this
  rw [this, E.acc_self s hsF]

/-- A correct relay at the end of `a` forwards its accepted value along every simple path of
correct nodes. -/
theorem mem_of_accepted {a : List V} {s z : V} (ha : IsSimplePath G a s z)
    (hacc : ∃ t, (E.acc a, a) ∈ E.M z t) (b : List V) :
    ∀ w, IsSimplePath G (z :: b) z w → Avoids (z :: b) E.F → ∃ t, (E.acc a, a ++ b) ∈ E.M w t := by
  induction b using List.reverseRecOn with
  | nil =>
    intro w hw _
    have : w = z := by simpa using hw.1.2.1.symm
    subst this; simpa using hacc
  | append_singleton b w ih =>
    intro w' hw hF
    have hww' : w' = w := by
      have := hw.1.2.1
      rw [← List.cons_append, List.getLast?_append] at this; simpa using this.symm
    subst hww'
    obtain ⟨q, hq, hadj, hne, hql⟩ := IsSimplePath.of_snoc hw
    have hF' : Avoids (z :: b) E.F := fun y hy => hF y (by
      rw [← List.cons_append]; exact List.mem_append_left _ hy)
    obtain ⟨t, ht⟩ := ih q hq hF'
    have hlast : (a ++ b).getLast? = some q := by rw [getLast?_append_of ha.1.2.1, hql]
    have hqF : q ∉ E.F := hF' q (List.mem_of_getLast? hql)
    have hwF : w' ∉ E.F := hF w' (by simp)
    have hacc' : E.acc (a ++ b) = E.acc a := E.acc_append b a z ha.1.2.1 hF'
    have hred : IsRedundant G (a ++ b ++ [w']) := by
      have := ha.redundant_append hw
      simpa [List.append_assoc] using this
    obtain ⟨t', ht'⟩ := E.M_live w' hwF (a ++ b) q hlast hqF hadj hne hred
      ⟨t, by rw [hacc']; exact ht⟩
    exact ⟨t', by rw [hacc'] at ht'; simpa [List.append_assoc] using ht'⟩

/-- Conversely, if `w` received a message along `a ++ b` where `z :: b` consists of correct
nodes, then `z` accepted `a`. -/
theorem accepted_of_mem {a : List V} {z : V} (ha : a.getLast? = some z) (b : List V) :
    ∀ w, (z :: b).getLast? = some w → Avoids (z :: b) E.F → ∀ t y, (y, a ++ b) ∈ E.M w t →
      ∃ t', (E.acc a, a) ∈ E.M z t' := by
  induction b using List.reverseRecOn with
  | nil =>
    intro w hw hF t y hm
    have : w = z := by simpa using hw.symm
    subst this
    exact ⟨t, by simpa using E.M_first w (hF w (by simp)) t y a (by simpa using hm)⟩
  | append_singleton b w ih =>
    intro w' hw hF t y hm
    have hww' : w' = w := by
      rw [← List.cons_append, List.getLast?_append] at hw; simpa using hw.symm
    subst hww'
    have hF' : Avoids (z :: b) E.F := fun y hy => hF y (by
      rw [← List.cons_append]; exact List.mem_append_left _ hy)
    set q := (z :: b).getLast (List.cons_ne_nil _ _)
    have hql : (z :: b).getLast? = some q := List.getLast?_eq_some_getLast _
    have hlast : (a ++ b).getLast? = some q := by rw [getLast?_append_of ha, hql]
    obtain ⟨t', ht'⟩ := E.M_src w' (hF w' (by simp)) t y (a ++ b) q
      (by simpa [List.append_assoc] using hm) hlast (hF' q (List.mem_of_getLast? hql))
    exact ih q hql hF' t' _ ht'

/-! ## Lemma 6 -/

/-- **Lemma 6**: every correct node eventually satisfies Maximal-Consistency in the thread of the
actual fault set `F`, hence sends `COMPLETE(F)`. -/
theorem sent_actual {c : V} (hc : c ∉ E.F) : Sent G f E.M c E.F := by
  classical
  refine ⟨hc, E.card_F, ?_⟩
  set P : Set (List V) := {p | IsRedundant G p ∧ Avoids p E.F ∧ p.getLast? = some c}
  have hPfin : P.Finite :=
    (List.finite_length_le V (2 * Fintype.card V)).subset fun p hp => hp.1.length_le
  obtain ⟨T, hT⟩ := exists_time hPfin (P := fun p t => ∃ y, (y, p) ∈ E.M c t)
    (fun p t t' htt' ⟨y, hy⟩ => ⟨y, E.M_mono c htt' hy⟩) (by
      rintro p ⟨⟨p₁, p₂, s, q, w, h₁, h₂, rfl⟩, hF, hl⟩
      have hw : w = c := Option.some.inj ((h₁.getLast_append h₂).symm.trans hl)
      subst hw
      have hF₁ : Avoids p₁ E.F := fun y hy => hF y (List.mem_append_left _ hy)
      have hF₂ : Avoids p₂ E.F := by
        rw [h₂.eq_cons]
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hF₁ y (List.mem_of_getLast? h₁.1.2.1)
        · exact hF y (List.mem_append_right _ hy)
      have hsF : s ∉ E.F := hF₁ s (List.mem_of_head? h₁.1.1)
      obtain ⟨t₀, ht₀⟩ := E.M_live_self s hsF
      have h0 : ∃ t, (E.acc [s], [s]) ∈ E.M s t := ⟨t₀, by rw [E.acc_self s hsF]; exact ht₀⟩
      obtain ⟨t₁, ht₁⟩ := E.mem_of_accepted isSimplePath_singleton h0 p₁.tail q
        (by rw [← h₁.eq_cons]; exact h₁) (by rw [← h₁.eq_cons]; exact hF₁)
      have e1 : [s] ++ p₁.tail = p₁ := by rw [List.singleton_append, ← h₁.eq_cons]
      rw [e1] at ht₁
      have hacc : E.acc p₁ = E.acc [s] := by
        conv_lhs => rw [← e1]
        exact E.acc_append p₁.tail [s] s (by simp) (by rw [← h₁.eq_cons]; exact hF₁)
      obtain ⟨t₂, ht₂⟩ := E.mem_of_accepted h₁ ⟨t₁, by rw [hacc]; exact ht₁⟩ p₂.tail w
        (by rw [← h₂.eq_cons]; exact h₂) (by rw [← h₂.eq_cons]; exact hF₂)
      exact ⟨t₂, _, ht₂⟩)
  refine ⟨T, fun m hm m' hm' hh => ?_, fun p hp hpF hpl => ?_⟩
  · rw [mem_excl] at hm hm'
    obtain ⟨s, hs⟩ : ∃ s, m.2.head? = some s := by
      have := E.M_last c hc T m hm.1
      cases h : m.2 with
      | nil => rw [h] at this; simp at this
      | cons s _ => exact ⟨s, rfl⟩
    rw [E.value_of_avoids hc hm.1 hm.2 hs, E.value_of_avoids hc hm'.1 hm'.2 (hh ▸ hs)]
  · obtain ⟨y, hy⟩ := hT p ⟨hp, hpF, hpl⟩
    exact ⟨y, mem_excl.mpr ⟨hy, hpF⟩⟩

/-! ## A full `COMPLETE` content contains the relayed values -/

/-- If `c` is correct and sent `COMPLETE(F')`, then for every simple path `a` from `q` to `z`
avoiding `F'` and every simple path `b` of correct nodes from `z` to `c` avoiding `F'`, the content
`M^c` contains a message along `a ++ b.tail`, whose value is both the value reported for `q` in
`M^c` and the value accepted by `z` on `a`. -/
theorem full_value {c : V} (hc : c ∉ E.F) {F' : Finset V} (hs : Sent G f E.M c F')
    {a : List V} {q z : V} (ha : IsSimplePath G a q z) (haF' : Avoids a F')
    {b : List V} (hb : IsSimplePath G b z c) (hbF : Avoids b E.F) (hbF' : Avoids b F') :
    ∃ y, (y, a ++ b.tail) ∈ mcMsg G E.M c F' ∧ y = valueOf (mcMsg G E.M c F') q ∧
      y = E.acc a := by
  have hbt : Avoids b.tail F' := fun y hy => hbF' y (List.mem_of_mem_tail hy)
  obtain ⟨y, hy⟩ := (hs.full G f) (a ++ b.tail) (ha.redundant_append hb)
    (avoids_append haF' hbt) (ha.getLast_append hb)
  refine ⟨y, hy, (hs.consistent G f).eq_valueOf hy (ha.head_append _), ?_⟩
  have hy' := mem_excl.mp hy
  have hfirst : (E.acc (a ++ b.tail), a ++ b.tail) ∈ mcMsg G E.M c F' :=
    mem_excl.mpr ⟨E.M_first c hc _ y _ hy'.1, hy'.2⟩
  have h1 := (hs.consistent G f) _ hy _ hfirst rfl
  simp only at h1
  rw [h1]
  exact E.acc_append b.tail a z ha.1.2.1 (by rw [← hb.eq_cons]; exact hbF)

/-! ## Lemma 7 -/

/-- **Lemma 7**: if correct nodes `c` and `u` pass Maximal-Consistency on the same set `F'`, then
for every `F''` with `|F''| ≤ f`, their contents report the same value for every node of
`S_{F',F''}` (and both report one). -/
theorem lemma7 (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {c u : V} (hc : c ∉ E.F)
    (hu : u ∉ E.F) {F' : Finset V} (hsc : Sent G f E.M c F') (hsu : Sent G f E.M u F')
    {W : Finset V} (hW : W.card ≤ f) {q : V} (hq : q ∈ srcComp G F' W) :
    valueOf (mcMsg G E.M c F') q = valueOf (mcMsg G E.M u F') q ∧
      (∃ m ∈ mcMsg G E.M c F', m.2.head? = some q) ∧
      (∃ m ∈ mcMsg G E.M u F', m.2.head? = some q) := by
  have hcF' : c ∉ F' := hsc.1
  have huF' : u ∉ F' := hsu.1
  obtain ⟨z, hzu, hzc⟩ := hG E.F F' F' c u E.card_F hsc.2.1 hsc.2.1
    (by simp [hc, hcF']) (by simp [hu, huF'])
  obtain ⟨s, hsS, hsz⟩ := hG.theorem5 hn hsc.2.1 hW hsc.2.1 (b := z)
    (by have := hzc.1; simp only [mem_union, not_or] at this ⊢; exact ⟨this.2, this.2⟩)
  have hS : ∀ x ∈ F' ∪ F', x ∉ srcComp G F' W := fun x hx hxS =>
    notMem_of_mem_srcComp hn hxS (mem_union_left _ (by simpa using hx))
  have hqz : Reaches G (F' ∪ F') q z := (srcComp_reaches hq hsS hS).trans hsz
  obtain ⟨a, ha, haF⟩ := hqz.exists_simplePath
  have haF' : Avoids a F' := fun y hy h => haF y hy (mem_union_left _ h)
  obtain ⟨bc, hbc, hbcF⟩ := hzc.exists_simplePath
  obtain ⟨bu, hbu, hbuF⟩ := hzu.exists_simplePath
  obtain ⟨yc, hyc, hyc1, hyc2⟩ := E.full_value hc hsc ha haF' hbc
    (avoids_union.mp hbcF).1 (avoids_union.mp hbcF).2
  obtain ⟨yu, hyu, hyu1, hyu2⟩ := E.full_value hu hsu ha haF' hbu
    (avoids_union.mp hbuF).1 (avoids_union.mp hbuF).2
  exact ⟨by rw [← hyc1, ← hyu1, hyc2, hyu2], ⟨_, hyc, ha.head_append _⟩,
    ⟨_, hyu, ha.head_append _⟩⟩

/-! ## Lemma 8 -/

theorem completeness_mono {v : V} {Mv Mv' Mc : Finset (Msg V)} {Fu : Finset V} (h : Mv ⊆ Mv')
    (hc : Completeness G f v Mv Mc Fu) : Completeness G f v Mv' Mc Fu := by
  intro Fw hFw hne q hq
  obtain ⟨m, hm, hmq, hno⟩ := hc Fw hFw hne q hq
  exact ⟨m, hm, hmq, fun ⟨H, h1, h2, h3, h4⟩ => hno ⟨H, h1, h2, h3, fun m' hm' => h4 m' (h hm')⟩⟩

omit E in
/-- A node of `S_{Fu,Fw}` reaches every `b ∉ Fu ∪ H` in `G − (Fu ∪ H)` when `H` avoids the source
component (Theorem 5 + strong connectivity of the source component). -/
theorem reaches_from_srcComp (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V)
    {Fu Fw H : Finset V} (hFu : Fu.card ≤ f) (hFw : Fw.card ≤ f) (hH : H.card ≤ f) {q : V}
    (hq : q ∈ srcComp G Fu Fw) (hHS : ∀ h ∈ H, h ∉ srcComp G Fu Fw) {b : V}
    (hb : b ∉ Fu ∪ H) : Reaches G (Fu ∪ H) q b := by
  obtain ⟨s, hs, hsb⟩ := hG.theorem5 hn hFu hFw hH hb
  refine (srcComp_reaches hq hs fun x hx hxS => ?_).trans hsb
  rcases mem_union.mp hx with h | h
  · exact notMem_of_mem_srcComp hn hxS (mem_union_left _ h)
  · exact hHS x h hxS

/-- **Lemma 8**: if `c` is correct and sent `COMPLETE(Fu)` (content `M^c`), every correct node
`v` eventually satisfies `Completeness(M_v, M^c, Fu)`. (The paper's additional hypotheses — that
`v` received the message along a correct path before its FIFO-Receive-All condition — are not
needed.) -/
theorem completeness_eventually (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {v c : V}
    (hv : v ∉ E.F) (hc : c ∉ E.F) {Fu : Finset V} (hs : Sent G f E.M c Fu) :
    ∃ t, Completeness G f v (E.M v t) (mcMsg G E.M c Fu) Fu := by
  classical
  set Mc := mcMsg G E.M c Fu
  have hcFu : c ∉ Fu := hs.1
  let C : (Finset V × V × Finset V) → Prop := fun i =>
    i.1.card ≤ f ∧ i.1 ≠ Fu ∧ i.2.1 ∈ srcComp G Fu i.1 ∧ i.2.2.card ≤ f ∧ v ∉ i.2.2 ∧
      (∀ h ∈ i.2.2, h ∉ srcComp G Fu i.1)
  let P : (Finset V × V × Finset V) → ℕ → Prop := fun i t => C i →
      ∃ m' ∈ E.M v t, m'.2.head? = some i.2.1 ∧ m'.1 = valueOf Mc i.2.1 ∧ Avoids m'.2 i.2.2
  obtain ⟨T, hT⟩ := exists_time (s := Set.univ) Set.finite_univ (P := P)
    (fun i t t' htt' h hC => by
      obtain ⟨m', hm', h1, h2, h3⟩ := h hC
      exact ⟨m', E.M_mono v htt' hm', h1, h2, h3⟩) (by
      rintro ⟨Fw, q, H⟩ -
      by_cases hC : C (Fw, q, H)
      swap
      · exact ⟨0, fun h => absurd h hC⟩
      obtain ⟨hFw, hne, hq, hH, hvH, hHS⟩ := hC
      obtain ⟨z, hzv, hzc⟩ := hG E.F Fu H c v E.card_F hs.2.1 hH (by simp [hc, hcFu])
        (by simp [hv, hvH])
      have hz : z ∉ Fu ∪ H := by
        have h1 := hzv.1; have h2 := hzc.1
        simp only [mem_union, not_or] at h1 h2 ⊢; exact ⟨h2.2, h1.2⟩
      obtain ⟨a, ha, haF⟩ := (reaches_from_srcComp hG hn hs.2.1 hFw hH hq hHS hz).exists_simplePath
      obtain ⟨bc, hbc, hbcF⟩ := hzc.exists_simplePath
      obtain ⟨bv, hbv, hbvF⟩ := hzv.exists_simplePath
      obtain ⟨y, hy, hyq, hya⟩ := E.full_value hc hs ha (avoids_union.mp haF).1 hbc
        (avoids_union.mp hbcF).1 (avoids_union.mp hbcF).2
      have hbc' : bc = z :: bc.tail := hbc.eq_cons
      obtain ⟨t', ht'⟩ := E.accepted_of_mem ha.1.2.1 bc.tail c (by rw [← hbc']; exact hbc.1.2.1)
        (by rw [← hbc']; exact (avoids_union.mp hbcF).1) _ y (mem_excl.mp hy).1
      have hbv' : bv = z :: bv.tail := hbv.eq_cons
      obtain ⟨t'', ht''⟩ := E.mem_of_accepted ha ⟨t', ht'⟩ bv.tail v (by rw [← hbv']; exact hbv)
        (by rw [← hbv']; exact (avoids_union.mp hbvF).1)
      refine ⟨t'', fun _ => ⟨_, ht'', ha.head_append _, by rw [← hya, hyq], ?_⟩⟩
      exact avoids_append (avoids_union.mp haF).2
        (fun y hy => (avoids_union.mp hbvF).2 y (List.mem_of_mem_tail hy)))
  refine ⟨T, fun Fw hFw hne q hq => ?_⟩
  have hcb : c ∉ Fu ∪ Fu := by simpa using hcFu
  obtain ⟨p, hp, hpF⟩ := (reaches_from_srcComp hG hn hs.2.1 hFw hs.2.1 hq
    (fun h hh hhS => notMem_of_mem_srcComp hn hhS (mem_union_left _ hh)) hcb).exists_simplePath
  have hpF' : Avoids p Fu := fun y hy h => hpF y hy (mem_union_left _ h)
  obtain ⟨y, hy⟩ := (hs.full G f) p hp.isRedundant hpF' hp.1.2.1
  have hhead : (y, p).2.head? = some q := hp.1.1
  refine ⟨(y, p), hy, hhead, fun ⟨H, hH, hvH, hHS, hcov⟩ => ?_⟩
  obtain ⟨m', hm', hm'q, hm'v, hm'H⟩ := hT (Fw, q, H) trivial ⟨hFw, hne, hq, hH, hvH, hHS⟩
  exact hcov m' hm' hm'q (by rw [hm'v]; exact ((hs.consistent G f).eq_valueOf hy hhead).symm) hm'H

/-! ## Theorem 9 -/

/-- **Theorem 9**: every correct node eventually executes Filter-and-Average (in the first thread
whose `Verify` condition holds; at the latest in the thread of the actual fault set `F`). -/
theorem exists_executes (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {v : V}
    (hv : v ∉ E.F) : ∃ Fv t, E.Executes v Fv t := by
  classical
  -- FIFO-Receive-All in the thread of the actual fault set
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, E.FIFORecAll v E.F T₁ := by
    let s : Set (V × List V) :=
      {cp | IsSimplePath G cp.2 cp.1 v ∧ ∀ y ∈ cp.2, Reaches G E.F y v}
    have hs : s.Finite := (Set.finite_univ.prod (finite_simplePaths (fun p : List V => p.Nodup)
      fun _ h => h)).subset fun cp hcp => ⟨trivial, hcp.1.2⟩
    obtain ⟨T, hT⟩ := exists_time hs
      (P := fun cp t => (cp.1, cp.2, mcMsg G E.M cp.1 E.F, E.F) ∈ E.CR v t)
      (fun _ _ _ h hm => E.CR_mono v h hm) (by
        rintro ⟨c, p⟩ ⟨hp, hpr⟩
        have hpF : Avoids p E.F := fun y hy => (hpr y hy).1
        exact E.CR_live v hv c p E.F (E.sent_actual (hpF c (List.mem_of_head? hp.1.1))) hp hpF)
    exact ⟨T, fun c => ⟨mcMsg G E.M c E.F, fun p hp hpr => hT (c, p) ⟨hp, hpr⟩⟩⟩
  -- Completeness for all genuine `COMPLETE` messages
  obtain ⟨T₂, hT₂⟩ := exists_time (s := Set.univ) Set.finite_univ
    (P := fun (cF : V × Finset V) t => cF.1 ∉ E.F → Sent G f E.M cF.1 cF.2 →
      Completeness G f v (E.M v t) (mcMsg G E.M cF.1 cF.2) cF.2)
    (fun _ t t' htt' h a1 a2 => completeness_mono (E.M_mono v htt') (h a1 a2)) (by
      rintro ⟨c, Fu⟩ -
      by_cases h : c ∉ E.F ∧ Sent G f E.M c Fu
      · obtain ⟨t, ht⟩ := E.completeness_eventually hG hn hv h.1 h.2
        exact ⟨t, fun _ _ => ht⟩
      · exact ⟨0, fun a1 a2 => absurd ⟨a1, a2⟩ h⟩)
  have hver : E.Verify v E.F (max T₁ T₂) := by
    refine ⟨⟨T₁, le_max_left _ _, hT₁⟩, fun c p Mc Fu hm hpr _ => ?_⟩
    have hpF : Avoids p E.F := fun y hy => (hpr y hy).1
    obtain ⟨hph, hsent, rfl, -⟩ := E.CR_honest v hv _ c p Mc Fu hm hpF
    exact completeness_mono (E.M_mono v (le_max_right _ _))
      (hT₂ (c, Fu) trivial (hpF c (List.mem_of_head? hph)) hsent)
  have hex : ∃ t, ∃ F' : Finset V, v ∉ F' ∧ F'.card ≤ f ∧ E.Verify v F' t :=
    ⟨_, E.F, hv, E.card_F, hver⟩
  obtain ⟨F₀, h0⟩ := Nat.find_spec hex
  exact ⟨F₀, Nat.find hex, h0.1, h0.2.1, h0.2.2,
    fun t' ht' F' h1 h2 h3 => Nat.find_min hex ht' ⟨F', h1, h2, h3⟩⟩

end RoundExec

end AsyncApproxBCDirected
