import Papers.PODC2013.ConstantBarriersMutex.InvFlush

/-!
# Preservation of the invariant by local steps (memory unchanged)

A local step of `g` changes only `g`'s program counter and appends writes to `g`'s store buffer.
`inv_local` reduces the preservation of `Inv` by such a step to facts about `g` alone.
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- `g` appends `ws` to its buffer and moves to `c'`. -/
def Cfg.loc (s : Cfg h) (g : Proc h) (ws : List (W h)) (c' : PC h) : Cfg h :=
  { s with buf := Function.update s.buf g (s.buf g ++ ws), pc := Function.update s.pc g c' }

lemma goto_eq_loc (s : Cfg h) (g : Proc h) (c : PC h) : s.goto g c = s.loc g [] c := by
  simp [Cfg.goto, Cfg.loc]

lemma issue_eq_loc (s : Cfg h) (g : Proc h) (w : W h) (c : PC h) :
    s.issue g w c = s.loc g [w] c := rfl

section
variable (s : Cfg h) (g : Proc h) (ws : List (W h)) (c' : PC h)
@[simp] lemma loc_mem : (s.loc g ws c').mem = s.mem := rfl
@[simp] lemma loc_ent : (s.loc g ws c').ent = s.ent := rfl
@[simp] lemma loc_buf_self : (s.loc g ws c').buf g = s.buf g ++ ws := by simp [Cfg.loc]
@[simp] lemma loc_pc_self : (s.loc g ws c').pc g = c' := by simp [Cfg.loc]
lemma loc_buf_ne {q : Proc h} (hq : q ≠ g) : (s.loc g ws c').buf q = s.buf q := by
  simp [Cfg.loc, Function.update_of_ne hq]
lemma loc_pc_ne {q : Proc h} (hq : q ≠ g) : (s.loc g ws c').pc q = s.pc q := by
  simp [Cfg.loc, Function.update_of_ne hq]
end

/-- Generic preservation lemma for local steps. -/
theorem inv_local {s : Cfg h} (hI : Inv s) {g : Proc h} {ws : List (W h)} {c' : PC h}
    (hLI : LI (s.loc g ws c') g) (hHC : HC (s.loc g ws c') g)
    (hE : (s.pc g).Entry → c'.Entry)
    (hE' : c'.Entry → (s.pc g).Entry ∨ s.mem.apply g = false)
    (hNH : ¬ Holds s g → ∀ w ∈ ws, NHW g w)
    (hHolds : Holds (s.loc g ws c') g ↔ Holds s g)
    (hHands : ∀ nx, Hands (s.loc g ws c') g nx ↔ Hands s g nx)
    (hX : (s.loc g ws c').InCSX g ↔ s.InCSX g)
    (hlv : (lv (s.loc g ws c')).promQ = (lv s).promQ ∧
      ∀ r, (lv (s.loc g ws c')).inPromQ r = (lv s).inPromQ r)
    (hx38 : ∀ l q rest, c' = .x38 l q rest ↔ s.pc g = .x38 l q rest)
    (hx46 : ∀ q, c' = .x46 q ↔ s.pc g = .x46 q)
    (hex1 : c' = .cs ∨ c' = .x31 ∨ c' = .x32 → s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32)
    (hex2 : ∀ v, .exits v ∈ ws → v = s.mem.exits + 1 ∧ s.ent = v)
    (hex3 : (c' ≠ .cs ∧ c' ≠ .x31 ∧ c' ≠ .x32 ∧ ∀ v, .exits v ∉ s.buf g ++ ws) →
      (s.pc g ≠ .cs ∧ s.pc g ≠ .x31 ∧ s.pc g ≠ .x32 ∧ ∀ v, .exits v ∉ s.buf g))
    (hex4 : (s.buf g ++ ws).countP (fun w => w.isExits) ≤ 1) :
    Inv (s.loc g ws c') := by
  set s' := s.loc g ws c' with hs'
  have hpq : ∀ q, q ≠ g → s'.pc q = s.pc q := fun q hq => loc_pc_ne s g ws c' hq
  have hbq : ∀ q, q ≠ g → s'.buf q = s.buf q := fun q hq => loc_buf_ne s g ws c' hq
  have hholds : ∀ q, Holds s' q ↔ Holds s q := by
    intro q; by_cases hq : q = g
    · subst hq; exact hHolds
    · unfold Holds; rw [hpq q hq, hbq q hq]
  have hhands : ∀ q nx, Hands s' q nx ↔ Hands s q nx := by
    intro q nx; by_cases hq : q = g
    · subst hq; exact hHands nx
    · unfold Hands; rw [hpq q hq, hbq q hq]
  have hincsx : ∀ q, s'.InCSX q ↔ s.InCSX q := by
    intro q; by_cases hq : q = g
    · subst hq; exact hX
    · unfold Cfg.InCSX; rw [hpq q hq, hbq q hq]
  have hEc : ∀ c, (s.pc c).Entry → (s'.pc c).Entry := by
    intro c hc; by_cases hcg : c = g
    · subst hcg; rw [loc_pc_self]; exact hE hc
    · rw [hpq c hcg]; exact hc
  refine
    { loc := ?_, hc := ?_, lockRole := ?_, uniq := ?_, sig := ?_, nodup := ?_, pq := ?_,
      inpq := ?_, q4 := hI.q4, ex1 := ?_, ex2 := ?_, ex3 := ?_, ex4 := ?_ }
  · intro q
    by_cases hq : q = g
    · subst hq; exact hLI
    · exact (LI_congr (s' := s') (s := s) rfl (hbq q hq) (hpq q hq)).2 (hI.loc q)
  · intro q
    by_cases hq : q = g
    · subst hq; exact hHC
    · exact HC_mono (hpq q hq) hEc (fun c hc => hc) hlv.1 hlv.2
        (fun hne => by rwa [hbq q hq] at hne) (hI.hc q)
  · intro g' hg'
    rcases hI.lockRole g' hg' with h1 | ⟨h1, h2, h3⟩
    · exact Or.inl ((hholds g').2 h1)
    · right
      refine ⟨hEc g' h1, h2, ?_⟩
      rcases h3 with h3 | ⟨g'', h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨g'', (hhands g'' g').2 h3⟩
  · intro g₁ g₂ h₁ h₂; exact hI.uniq _ _ ((hincsx _).1 h₁) ((hincsx _).1 h₂)
  · intro q hs hE2 ha
    have hEq : (s.pc q).Entry := by
      by_cases hq : q = g
      · subst hq
        rw [loc_pc_self] at hE2
        rcases hE' hE2 with h1 | h1
        · exact h1
        · have ha' : s.mem.apply q = true := ha
          rw [h1] at ha'; exact absurd ha' (by simp)
      · rwa [hpq q hq] at hE2
    obtain ⟨h1, h2⟩ := hI.sig q hs hEq ha
    exact ⟨h1, fun g' hh => h2 g' ((hhands g' q).1 hh)⟩
  · rw [hlv.1]; exact hI.nodup
  · intro q hq
    rw [hlv.1] at hq
    obtain ⟨h1, h2, h3⟩ := hI.pq q hq
    exact ⟨hEc q h1, h2, h3⟩
  · intro q
    rw [hlv.1, hlv.2, hI.inpq q]
    have h38 : ∀ g'' l rest, s'.pc g'' = .x38 l q rest ↔ s.pc g'' = .x38 l q rest := by
      intro g'' l rest; by_cases hq : g'' = g
      · subst hq; rw [loc_pc_self]; exact hx38 l q rest
      · rw [hpq g'' hq]
    have h46 : ∀ g'', s'.pc g'' = .x46 q ↔ s.pc g'' = .x46 q := by
      intro g''; by_cases hq : g'' = g
      · subst hq; rw [loc_pc_self]; exact hx46 q
      · rw [hpq g'' hq]
    simp only [ne_eq, h38, h46]
  · intro g' hg'
    by_cases hq : g' = g
    · subst hq; rw [loc_pc_self] at hg'; exact hI.ex1 g' (hex1 hg')
    · rw [hpq g' hq] at hg'; exact hI.ex1 g' hg'
  · intro g' v hv
    by_cases hq : g' = g
    · subst hq
      rw [loc_buf_self, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hI.ex2 g' v hv
      · exact hex2 v hv
    · rw [hbq g' hq] at hv; exact hI.ex2 g' v hv
  · intro hpre
    apply hI.ex3
    intro g'
    by_cases hq : g' = g
    · subst hq
      have := hpre g'
      rw [loc_pc_self, loc_buf_self] at this
      exact hex3 this
    · have := hpre g'
      rwa [hpq g' hq, hbq g' hq] at this
  · intro g'
    by_cases hq : g' = g
    · subst hq; rw [loc_buf_self]; exact hex4
    · rw [hbq g' hq]; exact hI.ex4 g'

lemma lv_loc_nh {s : Cfg h} {g : Proc h} {ws : List (W h)} {c' : PC h}
    (hws : ∀ w ∈ ws, NHW g w) :
    (lv (s.loc g ws c')).promQ = (lv s).promQ ∧
      ∀ r, (lv (s.loc g ws c')).inPromQ r = (lv s).inPromQ r := by
  unfold lv
  simp only [loc_mem]
  rcases s.mem.lock with _ | g'
  · exact ⟨rfl, fun _ => rfl⟩
  · simp only
    by_cases hg : g' = g
    · subst hg
      rw [loc_buf_self, Mem.view_append]
      exact ⟨view_promQ_of (fun w hw => (hws w hw).promQ),
        fun r => view_inPromQ_of (fun w hw => (hws w hw).inPromQ)⟩
    · rw [loc_buf_ne s g ws c' hg]; exact ⟨rfl, fun _ => rfl⟩

lemma countP_exits_nh {s : Cfg h} (hI : Inv s) {g : Proc h} (hng : ¬ Holds s g) :
    ∀ w ∈ s.buf g, w.isExits = false := fun w hw => (hI.nonholder_buf hng w hw).exits

/-- Local steps of a process outside the critical and exit sections. -/
theorem inv_local_nh {s : Cfg h} (hI : Inv s) {g : Proc h} {ws : List (W h)} {c' : PC h}
    (hLI : LI (s.loc g ws c') g)
    (hE : (s.pc g).Entry → c'.Entry)
    (hE' : c'.Entry → (s.pc g).Entry ∨ s.mem.apply g = false)
    (hng : ¬ Holds s g) (hng' : ¬ Holds (s.loc g ws c') g)
    (hnd : ∀ nx, ¬ Hands s g nx) (hnd' : ∀ nx, ¬ Hands (s.loc g ws c') g nx)
    (hXs : ¬ s.InCSX g) (hXs' : ¬ (s.loc g ws c').InCSX g)
    (hws : ∀ w ∈ ws, NHW g w)
    (hc' : ¬ c'.Exit ∧ c' ≠ .cs ∧ ∀ o, c' ≠ .x50 o)
    (hpg : s.pc g ≠ .cs ∧ ¬ (s.pc g).Exit) :
    Inv (s.loc g ws c') := by
  have hbx : ∀ w ∈ s.buf g ++ ws, w.isExits = false := by
    intro w hw; rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact countP_exits_nh hI hng w hw
    · exact (hws w hw).exits
  apply inv_local hI hLI ?_ hE hE' (fun _ => hws) ⟨fun h => absurd h hng', fun h => absurd h hng⟩
    (fun nx => ⟨fun h => absurd h (hnd' nx), fun h => absurd h (hnd nx)⟩)
    ⟨fun h => absurd h hXs', fun h => absurd h hXs⟩ (lv_loc_nh hws)
  · intro l q rest
    constructor
    · rintro rfl; exact absurd (by simp [PC.Exit]) hc'.1
    · intro h; rw [h] at hpg; exact absurd (by simp [PC.Exit]) hpg.2
  · intro q
    constructor
    · rintro rfl; exact absurd (by simp [PC.Exit]) hc'.1
    · intro h; rw [h] at hpg; exact absurd (by simp [PC.Exit]) hpg.2
  · rintro (h | h | h)
    · exact absurd h hc'.2.1
    · subst h; exact absurd (by simp [PC.Exit]) hc'.1
    · subst h; exact absurd (by simp [PC.Exit]) hc'.1
  · intro v hv; have := (hws _ hv).exits; simp [W.isExits] at this
  · intro _
    refine ⟨hpg.1, fun h => hpg.2 (by rw [h]; simp [PC.Exit]),
      fun h => hpg.2 (by rw [h]; simp [PC.Exit]), fun v hv => ?_⟩
    have := countP_exits_nh hI hng _ hv; simp [W.isExits] at this
  · rw [List.countP_eq_zero.2 (fun w hw => by simp [hbx w hw])]; omega
  · unfold HC; rw [loc_pc_self]
    revert hc'; cases c' <;> simp [PC.Exit]

end Podc.ConstantBarriersMutex
