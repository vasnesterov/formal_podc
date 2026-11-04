-- CSLib candidate: Cslib/Computability/Distributed/Homonyms/Cover.lean
import Papers.PODC2011.HomonymsBA.Basic

/-!
# Covering systems for homonymous systems

A *covering system* is a run of an algorithm on a set `Q` of processes with an arbitrary
communication relation `adj` (`adj c' c`: `c` hears `c'`) and no Byzantine process
(`coverRun`). Given an `n`-process system `P`, a set of correct processes mapped into the cover by
`e`, such that (1) the correct processes hear each other in the cover, and (2) every other cover
node a correct process hears carries the identifier of a Byzantine process, the Byzantine processes
can deliver to each correct `p` exactly what `e p` hears from outside the image of `e`
(`scenario`). Then every correct `p` has the state of `e p` (`st_scenario`).

The delivered multiset may be post-processed by `g`: `g = id` for numerate algorithms
(unrestricted Byzantine processes) and `g = dedup` for innumerate algorithms; in the latter case
the Byzantine processes are *restricted* as soon as the cover nodes outside the image that a correct
process hears with a common identifier are in the same state (`restricted_scenario_dedup`).
This is the general form of the scenario arguments of Fischer, Lynch and Merritt used in
Proposition 1 and Theorem 19 of the paper.
-/

namespace Podc.HomonymsBA

open Finset

variable {ℓ : ℕ} {V M S : Type*} (A : Algorithm ℓ V M S)
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A covering system: no Byzantine process, `c` hears `c'` iff `adj c' c`. -/
def coverRun (idQ : Q → Fin ℓ) (inpQ : Q → V) (adj : Q → Q → Prop) : Run Q ℓ V M where
  id := idQ
  byz := ∅
  inp := inpQ
  gst := 0
  drop _ c' c := ¬ adj c' c
  adv _ _ := 0

variable {P : Type*} [Fintype P] [DecidableEq P]

section

variable (idQ : Q → Fin ℓ) (inpQ : Q → V) (adj : Q → Q → Prop)
  (id : P → Fin ℓ) (byz : Finset P) (inp : P → V) (e : P → Q)

open Classical in
/-- What `e p` hears in round `r` of the cover from nodes outside the image of the correct
processes. -/
noncomputable def outside (r : ℕ) (p : P) : Multiset (Fin ℓ × M) :=
  ∑ c ∈ univ.filter (fun c => adj c (e p) ∧ ∀ q ∉ byz, e q ≠ c),
    (coverRun idQ inpQ adj : Run Q ℓ V M).msgFrom A
      ((coverRun idQ inpQ adj : Run Q ℓ V M).st A r c) c (e p)

/-- The scenario: Byzantine processes deliver to correct `p` (post-processed by `g`) what `e p`
hears from outside the image in the cover. Synchronous, no loss. -/
noncomputable def scenario (g : Multiset (Fin ℓ × M) → Multiset (Fin ℓ × M)) : Run P ℓ V M where
  id := id
  byz := byz
  inp := inp
  gst := 0
  drop _ _ _ := False
  adv r p := if p ∈ byz then 0 else g (outside A idQ inpQ adj byz e r p)

variable {idQ inpQ adj id byz inp e}

/-- The scenario is indistinguishable from the cover for the correct processes. -/
theorem st_scenario {g : Multiset (Fin ℓ × M) → Multiset (Fin ℓ × M)}
    (hg : ∀ s m m', A.step s (m + g m') = A.step s (m + m'))
    (hid : ∀ p ∉ byz, idQ (e p) = id p) (hinp : ∀ p ∉ byz, inpQ (e p) = inp p)
    (hinj : ∀ p ∉ byz, ∀ q ∉ byz, e p = e q → p = q)
    (hcl : ∀ p ∉ byz, ∀ q ∉ byz, adj (e q) (e p)) :
    ∀ r, ∀ p ∉ byz, (scenario A idQ inpQ adj id byz inp e g).st A r p =
      (coverRun idQ inpQ adj : Run Q ℓ V M).st A r (e p) := by
  classical
  set Rs := scenario A idQ inpQ adj id byz inp e g
  set Rc : Run Q ℓ V M := coverRun idQ inpQ adj
  intro r
  induction r with
  | zero => intro p hp; simp [Rs, Rc, scenario, coverRun, hid p hp, hinp p hp]
  | succ r ih =>
    intro p hp
    rw [Run.st_succ, Run.st_succ, ih p hp, Run.inbox_eq, Run.inbox_eq]
    have hadv : Rs.adv r p = g (outside A idQ inpQ adj byz e r p) := by
      simp [Rs, scenario, hp]
    rw [hadv, hg]
    congr 1
    -- the cover inbox splits into the image of the correct processes and the outside
    have hc : Rc.adv r (e p) = 0 := rfl
    rw [hc, add_zero]
    have hsplit : univ.filter (fun c => c ∉ Rc.byz ∧ ¬ Rc.drop r c (e p)) =
        (univ.filter (fun q => q ∉ byz)).image e ∪
          univ.filter (fun c => adj c (e p) ∧ ∀ q ∉ byz, e q ≠ c) := by
      ext c
      simp only [Rc, coverRun, Finset.notMem_empty, not_false_eq_true, not_not, true_and,
        Finset.mem_filter, Finset.mem_univ, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hc
        by_cases h : ∃ q, q ∉ byz ∧ e q = c
        · exact Or.inl h
        · exact Or.inr ⟨hc, fun q hq e' => h ⟨q, hq, e'⟩⟩
      · rintro (⟨q, hq, rfl⟩ | ⟨hc, -⟩)
        · exact hcl p hp q hq
        · exact hc
    erw [hsplit]
    rw [Finset.sum_union, Finset.sum_image (fun q hq q' hq' h =>
      hinj q (by simpa using hq) q' (by simpa using hq') h)]
    · congr 1
      · refine Finset.sum_congr (by ext q; simp [Rs, scenario]) fun q hq => ?_
        have hq' : q ∉ byz := by simpa using hq
        simp only [Run.msgFrom, ih q hq']
        simp [Rs, Rc, scenario, coverRun, hid p hp, hid q hq']
    · rw [Finset.disjoint_left]
      intro c h1 h2
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      obtain ⟨q, hq, rfl⟩ := h1
      exact h2.2 q hq rfl

lemma decides_scenario {g : Multiset (Fin ℓ × M) → Multiset (Fin ℓ × M)}
    (hg : ∀ s m m', A.step s (m + g m') = A.step s (m + m'))
    (hid : ∀ p ∉ byz, idQ (e p) = id p) (hinp : ∀ p ∉ byz, inpQ (e p) = inp p)
    (hinj : ∀ p ∉ byz, ∀ q ∉ byz, e p = e q → p = q)
    (hcl : ∀ p ∉ byz, ∀ q ∉ byz, adj (e q) (e p)) {p : P} (hp : p ∉ byz) {v : V} :
    (scenario A idQ inpQ adj id byz inp e g).Decides A p v ↔
      (coverRun idQ inpQ adj : Run Q ℓ V M).Decides A (e p) v :=
  Run.decides_of_st A _ fun r => st_scenario A hg hid hinp hinj hcl r p hp

lemma mem_outside {r : ℕ} {p : P} {x : Fin ℓ × M} (hx : x ∈ outside A idQ inpQ adj byz e r p) :
    ∃ c, adj c (e p) ∧ (∀ q ∉ byz, e q ≠ c) ∧ x.1 = idQ c ∧
      A.send ((coverRun idQ inpQ adj : Run Q ℓ V M).st A r c) (idQ (e p)) = some x.2 := by
  classical
  unfold outside at hx
  rw [Multiset.mem_sum] at hx
  obtain ⟨c, hc, hx⟩ := hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rw [Run.mem_msgFrom] at hx
  exact ⟨c, hc.1, hc.2, hx.1, hx.2⟩

/-- The scenario is a valid synchronous run if the identifiers are surjective, there are at most
`t` Byzantine processes and every outside cover node heard by a correct process carries a
Byzantine identifier. -/
theorem valid_scenario {g : Multiset (Fin ℓ × M) → Multiset (Fin ℓ × M)}
    (hgm : ∀ m x, x ∈ g m → x ∈ m) {t : ℕ} (hsurj : Function.Surjective id) (hbyz : byz.card ≤ t)
    (hout : ∀ p ∉ byz, ∀ c, adj c (e p) → (∀ q ∉ byz, e q ≠ c) → ∃ b ∈ byz, id b = idQ c) :
    (scenario A idQ inpQ adj id byz inp e g).Valid t := by
  refine ⟨hsurj, hbyz, ?_, fun _ _ _ _ _ _ h => h⟩
  intro r p x hx
  simp only [scenario] at hx
  split_ifs at hx with hp
  · simp at hx
  · obtain ⟨c, hc, hc', hx1, -⟩ := mem_outside A (hgm _ _ hx)
    obtain ⟨b, hb, e'⟩ := hout p hp c hc hc'
    exact ⟨b, hb, by simp [scenario, e', hx1]⟩

lemma card_dedup_filter_le_one {α : Type*} [DecidableEq α] (m : Multiset α) (f : α → Prop)
    [DecidablePred f] (h : ∀ x ∈ m, ∀ y ∈ m, f x → f y → x = y) :
    (m.dedup.filter f).card ≤ 1 := by
  have hnd : (m.dedup.filter f).Nodup := (Multiset.nodup_dedup m).filter f
  have : (m.dedup.filter f) = (⟨_, hnd⟩ : Finset α).val := rfl
  rw [this, ← Finset.card_def, Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_mk, Multiset.mem_filter, Multiset.mem_dedup] at hx hy
  exact h x hx.1 y hy.1 hx.2 hy.2

/-- With `g = dedup`, the Byzantine processes of the scenario are restricted provided outside
cover nodes heard by a correct process with a common identifier are in the same state. -/
theorem restricted_scenario_dedup [DecidableEq M]
    (hout : ∀ p ∉ byz, ∀ c, adj c (e p) → (∀ q ∉ byz, e q ≠ c) → ∃ b ∈ byz, id b = idQ c)
    (hclone : ∀ r, ∀ p ∉ byz, ∀ c c', adj c (e p) → (∀ q ∉ byz, e q ≠ c) → adj c' (e p) →
      (∀ q ∉ byz, e q ≠ c') → idQ c = idQ c' →
      (coverRun idQ inpQ adj : Run Q ℓ V M).st A r c =
        (coverRun idQ inpQ adj : Run Q ℓ V M).st A r c') :
    (scenario A idQ inpQ adj id byz inp e Multiset.dedup).Restricted := by
  classical
  intro r p j
  simp only [scenario]
  split_ifs with hp
  · simp
  · by_cases hj : ∃ x ∈ outside A idQ inpQ adj byz e r p, x.1 = j
    · obtain ⟨x, hx, rfl⟩ := hj
      obtain ⟨c, hc, hc', hx1, -⟩ := mem_outside A hx
      obtain ⟨b, hb, e'⟩ := hout p hp c hc hc'
      have h1 : 1 ≤ (byz.filter (id · = x.1)).card :=
        Finset.card_pos.2 ⟨b, by simp [hb, e', hx1]⟩
      refine le_trans ?_ h1
      convert card_dedup_filter_le_one (outside A idQ inpQ adj byz e r p) (·.1 = x.1) ?_
      intro y hy z hz hy1 hz1
      obtain ⟨c1, h1a, h1b, h1c, h1d⟩ := mem_outside A hy
      obtain ⟨c2, h2a, h2b, h2c, h2d⟩ := mem_outside A hz
      have hid : idQ c1 = idQ c2 := by rw [← h1c, ← h2c, hy1, hz1]
      have hs := hclone r p hp c1 c2 h1a h1b h2a h2b hid
      rw [hs, h2d] at h1d
      exact Prod.ext (by rw [hy1, hz1]) (Option.some_injective _ h1d).symm
    · push Not at hj
      have : ((outside A idQ inpQ adj byz e r p).dedup.filter (·.1 = j)) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro x hx; exact hj x (Multiset.mem_dedup.1 hx)
      simp [this]

end

end Podc.HomonymsBA
