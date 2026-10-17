import Papers.PODC2021.TimeOptimalSSLE.OptimalSilent

/-!
# Correctness of `Optimal-Silent-SSR` with the fixed recruitment guard (reachability)

With the recruitment guard `2 · rank + children ≤ n` (`p.fixed = true`), from every valid
configuration (the paper's finite state space, `Valid`) a correctly ranked configuration is
reachable (`fixed_reachable_ranked`); since ranked configurations are silent
(`Ranked.reachable`), this is self-stabilization in the reachability ("probability 1") sense
(`fixed_selfStabilizes`). Hypotheses: `n ≥ 2`, `Rmax ≥ 2`, `Dmax ≥ 2` (the paper's
`Rmax = 60 ln n`, `Dmax = Θ(n)` satisfy them); no assumption on `Emax`.

## Proof (an explicit schedule)

* *Phase 0* (`phase0`): two Resetting agents interacting repeatedly drain their `resetcount`s and
  then their delay timers until both are computing or both are triggered (`preach_RR`, by a
  lexicographic measure); a lone Resetting agent first brings a computing agent in
  (`preach_R_any`). Hence a configuration with two triggered agents or without Resetting agents
  is reachable.
* *Phase 1* (`phase1`): without Resetting agents, two `Unsettled` agents, or an `Unsettled` agent
  and a settled agent that cannot recruit it, count down to a trigger; otherwise recruitment makes
  all agents settled, and then either the ranks are distinct (ranked) or two equal ranks collide.
* *Sweep* (`treach_process`, `sweep`): two triggered agents `x, y` become dormant leaders with
  fresh timers (`treach_trig`); using only `x, y` and one target agent, every non-clean agent is
  turned into a dormant follower while `x, y` return to the same state (re-triggering `x, y` by a
  rank-`1` collision when needed). Clean agents are `Unsettled` agents and dormant followers.
* *Endgame*: `x, y` produce ranks `1, 2` (`preach_LL`), and breadth-first recruitment of the clean
  agents (`BFS.step`: rank `m + 1` is recruited by rank `⌊(m+1)/2⌋`) completes the ranking.
-/

open Cslib.PopulationProtocol

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TimeOptimalSSLE.OptimalSilent

open St

/-- Validity of states (the paper's finite state space). -/
def Valid (p : Params) : St → Prop
  | .settled r c => 1 ≤ r ∧ r ≤ p.n ∧ c ≤ 2
  | .unsettled e => e ≤ p.Emax
  | .resetting _ r d => r ≤ p.Rmax ∧ d ≤ p.Dmax

variable (p : Params)

/-! ### Validity is preserved -/

lemma valid_trig : Valid p (trig p) := by simp [trig, Valid]

lemma valid_reset (hn : 1 ≤ p.n) {s : St} (hs : Valid p s) : Valid p (reset p s) := by
  cases s with
  | resetting l r d => cases l <;> simp [reset, Valid, hn]
  | settled r c => exact hs
  | unsettled e => exact hs

lemma valid_dormantStep (hn : 1 ≤ p.n) (w o : Bool) {s : St} (hs : Valid p s) :
    Valid p (dormantStep p w o s) := by
  cases s with
  | resetting l r d =>
    cases r with
    | zero =>
      simp only [dormantStep]
      split_ifs <;> first
        | exact valid_reset p hn (by simp only [Valid] at hs ⊢; omega)
        | (simp only [Valid] at hs ⊢; omega)
    | succ r => exact hs
  | settled r c => exact hs
  | unsettled e => exact hs

lemma valid_propagateReset (hn : 1 ≤ p.n) {a b : St} (ha : Valid p a) (hb : Valid p b) :
    Valid p (propagateReset p a b).1 ∧ Valid p (propagateReset p a b).2 := by
  cases a with
  | resetting la rca dta =>
    have key : ∀ x : St × St, Valid p x.1 → Valid p x.2 →
        Valid p (dormantStep p (decide (0 < rca)) (!x.2.isResetting) x.1) ∧
        Valid p (dormantStep p (b.isResetting && decide (0 < b.rc))
          (!(dormantStep p (decide (0 < rca)) (!x.2.isResetting) x.1).isResetting) x.2) :=
      fun x h1 h2 => ⟨valid_dormantStep p hn _ _ h1, valid_dormantStep p hn _ _ h2⟩
    refine key _ ?_ ?_
    · by_cases h : 0 < rca ∧ b.isResetting = false
      · have ha' : rca ≤ p.Rmax ∧ dta ≤ p.Dmax := ha
        simp only [h, and_self, ite_true]; simp only [Valid]; omega
      · simp only [h, ite_false]
        split
        · simp only [Valid] at *; omega
        · exact ha
    · by_cases h : 0 < rca ∧ b.isResetting = false
      · have ha' : rca ≤ p.Rmax ∧ dta ≤ p.Dmax := ha
        simp only [h, and_self, ite_true]; simp only [Valid]; omega
      · simp only [h, ite_false]
        split
        · simp only [Valid] at *; omega
        · exact hb
  | settled r c => exact ⟨ha, hb⟩
  | unsettled e => exact ⟨ha, hb⟩

lemma valid_leaderElect {x : St × St} (h1 : Valid p x.1) (h2 : Valid p x.2) :
    Valid p (leaderElect x).1 ∧ Valid p (leaderElect x).2 := by
  rcases x with ⟨a, b⟩
  cases a with
  | resetting la ra da =>
    cases b with
    | resetting lb rb db =>
      cases la <;> cases lb <;> simp only [leaderElect] <;> exact ⟨h1, h2⟩
    | _ => simp only [leaderElect]; exact ⟨h1, h2⟩
  | _ => simp only [leaderElect]; exact ⟨h1, h2⟩

lemma valid_collide {x : St × St} (h1 : Valid p x.1) (h2 : Valid p x.2) :
    Valid p (collide p x).1 ∧ Valid p (collide p x).2 := by
  rcases x with ⟨a, b⟩
  cases a with
  | settled ra ca =>
    cases b with
    | settled rb cb =>
      simp only [collide]
      split_ifs
      · exact ⟨valid_trig p, valid_trig p⟩
      · exact ⟨h1, h2⟩
    | _ => exact ⟨h1, h2⟩
  | _ => exact ⟨h1, h2⟩

lemma guard_le {r c : ℕ} (h : guard p r c) : 2 * r + c ≤ p.n := by
  unfold guard at h; split_ifs at h <;> omega

lemma valid_recruit {i j : St} (h1 : Valid p i) (h2 : Valid p j) :
    Valid p (recruit p i j).1 ∧ Valid p (recruit p i j).2 := by
  cases i with
  | settled r c =>
    cases j with
    | unsettled e =>
      simp only [recruit]
      split_ifs with h
      · have := guard_le p h.2
        simp only [Valid] at h1 ⊢; omega
      · exact ⟨h1, h2⟩
    | _ => exact ⟨h1, h2⟩
  | _ => exact ⟨h1, h2⟩

lemma valid_dec {s : St} (h : Valid p s) : Valid p (dec s) := by
  cases s with
  | unsettled e => simp only [dec, Valid] at h ⊢; omega
  | _ => exact h

lemma valid_countdown {x : St × St} (h1 : Valid p x.1) (h2 : Valid p x.2) :
    Valid p (countdown p x).1 ∧ Valid p (countdown p x).2 := by
  simp only [countdown]
  split_ifs
  · exact ⟨valid_trig p, valid_trig p⟩
  · exact ⟨valid_trig p, valid_trig p⟩
  · exact ⟨valid_dec p h1, valid_dec p h2⟩

/-- Validity of states is preserved by interactions (both variants of the guard). -/
theorem valid_step (hn : 1 ≤ p.n) {a b : St} (ha : Valid p a) (hb : Valid p b) :
    Valid p (δ p a b).1 ∧ Valid p (δ p a b).2 := by
  have h1 : Valid p (if a.isResetting then propagateReset p a b
      else if b.isResetting then (propagateReset p b a).swap else (a, b)).1 ∧
      Valid p (if a.isResetting then propagateReset p a b
      else if b.isResetting then (propagateReset p b a).swap else (a, b)).2 := by
    split_ifs
    · exact valid_propagateReset p hn ha hb
    · exact (valid_propagateReset p hn hb ha).symm
    · exact ⟨ha, hb⟩
  obtain ⟨h2, h2'⟩ := valid_leaderElect p h1.1 h1.2
  obtain ⟨h3, h3'⟩ := valid_collide p h2 h2'
  obtain ⟨h4, h4'⟩ := valid_recruit p h3 h3'
  obtain ⟨h5, h5'⟩ := valid_recruit p h4' h4
  exact valid_countdown p h5' h5

variable {A : Type*} [DecidableEq A]

/-- Valid configurations stay valid. -/
theorem valid_reachable (hn : 1 ≤ p.n) {C D : Config A St} (hC : ∀ a, Valid p (C a))
    (h : (protocol p).Reachable C D) : ∀ a, Valid p (D a) := by
  induction h with
  | refl => exact hC
  | tail _ hst ih =>
    obtain ⟨a, b, hab, rfl⟩ := hst
    have := valid_step p hn (ih a) (ih b)
    intro x
    by_cases hxa : x = a
    · subst hxa; rw [Protocol.interact_self_left]; exact this.1
    · by_cases hxb : x = b
      · subst hxb; rw [Protocol.interact_self_right _ _ hab]; exact this.2
      · rw [Protocol.interact_other _ _ hxa hxb]; exact ih x


/-! ### Reachability inside a pair or a triple of agents -/

section Generic

variable {Q : Type*}

-- CSLib candidate
/-- Reachability of pairs of states under repeated interactions of one ordered pair of agents. -/
def PairReach (P : Protocol Q) : Q × Q → Q × Q → Prop :=
  Relation.ReflTransGen fun u v => v = P.δ u.1 u.2

-- CSLib candidate
/-- Interactions inside a triple of agents (all six ordered pairs). -/
inductive TripleStep (P : Protocol Q) : Q × Q × Q → Q × Q × Q → Prop
  | xy (a b c : Q) : TripleStep P (a, b, c) ((P.δ a b).1, (P.δ a b).2, c)
  | yx (a b c : Q) : TripleStep P (a, b, c) ((P.δ b a).2, (P.δ b a).1, c)
  | xz (a b c : Q) : TripleStep P (a, b, c) ((P.δ a c).1, b, (P.δ a c).2)
  | zx (a b c : Q) : TripleStep P (a, b, c) ((P.δ c a).2, b, (P.δ c a).1)
  | yz (a b c : Q) : TripleStep P (a, b, c) (a, (P.δ b c).1, (P.δ b c).2)
  | zy (a b c : Q) : TripleStep P (a, b, c) (a, (P.δ c b).2, (P.δ c b).1)

-- CSLib candidate
/-- Reachability inside a triple of agents. -/
def TripleReach (P : Protocol Q) : Q × Q × Q → Q × Q × Q → Prop :=
  Relation.ReflTransGen (TripleStep P)

-- CSLib candidate
lemma PairReach.map {R : Type*} {P : Protocol Q} {S : R → R → Prop} (f : Q × Q → R)
    (hf : ∀ u, S (f u) (f (P.δ u.1 u.2))) {u v : Q × Q} (h : PairReach P u v) :
    Relation.ReflTransGen S (f u) (f v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => subst hst; exact ih.tail (hf _)

lemma PairReach.xy {P : Protocol Q} {a b a' b' : Q} (c : Q) (h : PairReach P (a, b) (a', b')) :
    TripleReach P (a, b, c) (a', b', c) :=
  PairReach.map (S := TripleStep P) (fun u => (u.1, u.2, c)) (fun _ => TripleStep.xy _ _ _) h

lemma PairReach.yx {P : Protocol Q} {a b a' b' : Q} (c : Q) (h : PairReach P (b, a) (b', a')) :
    TripleReach P (a, b, c) (a', b', c) :=
  PairReach.map (S := TripleStep P) (fun u => (u.2, u.1, c)) (fun _ => TripleStep.yx _ _ _) h

lemma PairReach.xz {P : Protocol Q} {a c a' c' : Q} (b : Q) (h : PairReach P (a, c) (a', c')) :
    TripleReach P (a, b, c) (a', b, c') :=
  PairReach.map (S := TripleStep P) (fun u => (u.1, b, u.2)) (fun _ => TripleStep.xz _ _ _) h

lemma PairReach.zx {P : Protocol Q} {a c a' c' : Q} (b : Q) (h : PairReach P (c, a) (c', a')) :
    TripleReach P (a, b, c) (a', b, c') :=
  PairReach.map (S := TripleStep P) (fun u => (u.2, b, u.1)) (fun _ => TripleStep.zx _ _ _) h

lemma PairReach.yz {P : Protocol Q} {b c b' c' : Q} (a : Q) (h : PairReach P (b, c) (b', c')) :
    TripleReach P (a, b, c) (a, b', c') :=
  PairReach.map (S := TripleStep P) (fun u => (a, u.1, u.2)) (fun _ => TripleStep.yz _ _ _) h

lemma PairReach.zy {P : Protocol Q} {b c b' c' : Q} (a : Q) (h : PairReach P (c, b) (c', b')) :
    TripleReach P (a, b, c) (a, b', c') :=
  PairReach.map (S := TripleStep P) (fun u => (a, u.2, u.1)) (fun _ => TripleStep.zy _ _ _) h

-- CSLib candidate
/-- A run of two agents `a ≠ b` lifts to the whole population (other agents idle). -/
lemma PairReach.lift {P : Protocol Q} {C : Config A Q} {a b : A} (hab : a ≠ b) {u : Q × Q}
    (h : PairReach P (C a, C b) u) :
    ∃ D, P.Reachable C D ∧ D a = u.1 ∧ D b = u.2 ∧ ∀ z, z ≠ a → z ≠ b → D z = C z := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl, rfl, fun _ _ _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, hDa, hDb, hDz⟩ := ih
    subst hst
    refine ⟨P.interact D a b, hD.tail ⟨a, b, hab, rfl⟩, ?_, ?_, ?_⟩
    · rw [Protocol.interact_self_left, hDa, hDb]
    · rw [Protocol.interact_self_right _ _ hab, hDa, hDb]
    · intro z hza hzb; rw [Protocol.interact_other _ _ hza hzb, hDz z hza hzb]

-- CSLib candidate
/-- A run of three distinct agents lifts to the whole population (other agents idle). -/
lemma TripleReach.lift {P : Protocol Q} {C : Config A Q} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) {u : Q × Q × Q} (h : TripleReach P (C x, C y, C z) u) :
    ∃ D, P.Reachable C D ∧ D x = u.1 ∧ D y = u.2.1 ∧ D z = u.2.2 ∧
      ∀ w, w ≠ x → w ≠ y → w ≠ z → D w = C w := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, hDx, hDy, hDz, hDw⟩ := ih
    have hyx := hxy.symm
    have hzx := hxz.symm
    have hzy := hyz.symm
    cases hst with
    | xy a b c =>
      refine ⟨P.interact D x y, hD.tail ⟨x, y, hxy, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | yx a b c =>
      refine ⟨P.interact D y x, hD.tail ⟨y, x, hyx, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | xz a b c =>
      refine ⟨P.interact D x z, hD.tail ⟨x, z, hxz, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | zx a b c =>
      refine ⟨P.interact D z x, hD.tail ⟨z, x, hzx, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | yz a b c =>
      refine ⟨P.interact D y z, hD.tail ⟨y, z, hyz, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | zy a b c =>
      refine ⟨P.interact D z y, hD.tail ⟨z, y, hzy, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]

end Generic


/-! ### One-interaction computations -/

/-- Pair reachability for `Optimal-Silent-SSR`. -/
abbrev PReach : St × St → St × St → Prop := PairReach (protocol p)

/-- Triple reachability for `Optimal-Silent-SSR`. -/
abbrev TReach : St × St × St → St × St × St → Prop := TripleReach (protocol p)

variable {p}

lemma PReach.step {a b : St} {w v : St × St} (h : δ p a b = w) (h' : PReach p w v) :
    PReach p (a, b) v :=
  Relation.ReflTransGen.head h.symm h'

lemma PReach.one {a b : St} {w : St × St} (h : δ p a b = w) : PReach p (a, b) w :=
  PReach.step h Relation.ReflTransGen.refl

lemma δ_dL_S {d r c : ℕ} (hr : r ≠ 1) :
    δ p (resetting true 0 d) (settled r c) = (settled 1 0, settled r c) := by
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
    expired, St.isResetting, Ne.symm hr]

lemma δ_dL_S1 {d c : ℕ} : δ p (resetting true 0 d) (settled 1 c) = (trig p, trig p) := by
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
    expired, St.isResetting, trig]

lemma δ_trig_S (hR : 2 ≤ p.Rmax) {r c : ℕ} :
    δ p (trig p) (settled r c) =
      (resetting true (p.Rmax - 1) p.Dmax, resetting false (p.Rmax - 1) p.Dmax) := by
  obtain ⟨R, hR'⟩ : ∃ R, p.Rmax = R + 2 := ⟨p.Rmax - 2, by omega⟩
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
    expired, St.isResetting, trig, hR']

lemma δ_trig_U (hR : 2 ≤ p.Rmax) {e : ℕ} :
    δ p (trig p) (unsettled e) =
      (resetting true (p.Rmax - 1) p.Dmax, resetting false (p.Rmax - 1) p.Dmax) := by
  obtain ⟨R, hR'⟩ : ∃ R, p.Rmax = R + 2 := ⟨p.Rmax - 2, by omega⟩
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
    expired, St.isResetting, trig, hR']

lemma δ_trig_R (hR : 2 ≤ p.Rmax) {l : Bool} {r d : ℕ} (hr : r ≤ p.Rmax) :
    δ p (trig p) (resetting l r d) =
      (resetting true (p.Rmax - 1) p.Dmax, resetting false (p.Rmax - 1) d) := by
  obtain ⟨R, hR'⟩ : ∃ R, p.Rmax = R + 2 := ⟨p.Rmax - 2, by omega⟩
  have : max (R + 1) (r - 1) = R + 1 := by omega
  cases l <;> simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, trig, hR', this, St.rc]

lemma δ_drain {r d₁ d₂ : ℕ} :
    δ p (resetting true (r + 2) d₁) (resetting false (r + 2) d₂) =
      (resetting true (r + 1) d₁, resetting false (r + 1) d₂) := by
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
    expired, St.isResetting, St.rc]

lemma δ_drain1 (hD : 1 ≤ p.Dmax) {d₁ d₂ : ℕ} :
    δ p (resetting true 1 d₁) (resetting false 1 d₂) =
      (resetting true 0 p.Dmax, resetting false 0 p.Dmax) := by
  have : p.Dmax ≠ 0 := by omega
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
    expired, St.isResetting, St.rc, this]

lemma δ_dL_P {l : Bool} {r d d' : ℕ} :
    δ p (resetting true 0 d) (resetting l (r + 2) d') =
      (resetting true (r + 1) d, resetting false (r + 1) d') := by
  cases l <;> simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, St.rc]

lemma δ_dL_P1 (hD : 1 ≤ p.Dmax) {l : Bool} {d d' : ℕ} (hd : 2 ≤ d) :
    δ p (resetting true 0 d) (resetting l 1 d') =
      (resetting true 0 (d - 1), resetting false 0 p.Dmax) := by
  have : p.Dmax ≠ 0 := by omega
  have h2 : d - 1 ≠ 0 := by omega
  cases l <;> simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, St.rc, this, h2]

lemma δ_dd {l : Bool} {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    δ p (resetting true 0 a) (resetting l 0 b) =
      (resetting true 0 (a - 1), resetting false 0 (b - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  cases l <;> simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, St.rc]

lemma δ_dd' {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    δ p (resetting false 0 a) (resetting true 0 b) =
      (resetting false 0 (a - 1), resetting true 0 (b - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, St.rc]

lemma δ_wakeLF (hp : p.fixed = true) (hn : 2 ≤ p.n) {d : ℕ} :
    δ p (resetting true 0 1) (resetting false 0 d) = (settled 1 1, settled 2 0) := by
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, St.rc, guard, hn, hp]

lemma δ_wakeFL (hp : p.fixed = true) (hn : 2 ≤ p.n) {d : ℕ} :
    δ p (resetting false 0 1) (resetting true 0 d) = (settled 2 0, settled 1 1) := by
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, St.rc, guard, hn, hp]

lemma δ_dL_dL1 {d d' : ℕ} (hd : 2 ≤ d) (hd' : d' ≤ 1) :
    δ p (resetting true 0 d) (resetting true 0 d') = (resetting true 0 (d - 1), settled 1 0) := by
  have h2 : d - 1 ≠ 0 := by omega
  have h3 : d' - 1 = 0 := by omega
  simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit,
    countdown, dec, expired, St.isResetting, St.rc, h2, h3]


/-! ### Runs of two agents -/

/-- Two Resetting agents with equal positive `resetcount` (an `L` and an `F`) drain it together and
become dormant with fresh delay timers. -/
lemma preach_drain (hD : 1 ≤ p.Dmax) : ∀ r, 1 ≤ r → ∀ d₁ d₂,
    PReach p (resetting true r d₁, resetting false r d₂)
      (resetting true 0 p.Dmax, resetting false 0 p.Dmax)
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, _, _ => PReach.one (δ_drain1 hD)
  | r + 2, _, d₁, d₂ => PReach.step δ_drain (preach_drain hD (r + 1) (by omega) d₁ d₂)

/-- A dormant `L` (initiator) and a dormant `F` whose timer is not smaller wake up together:
the `L` becomes the root (rank `1`) and recruits the `F` as rank `2`. -/
lemma preach_wakeLF (hp : p.fixed = true) (hn : 2 ≤ p.n) : ∀ a, 1 ≤ a → ∀ b, a ≤ b →
    PReach p (resetting true 0 a, resetting false 0 b) (settled 1 1, settled 2 0)
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, _, _ => PReach.one (δ_wakeLF hp hn)
  | a + 2, _, b, hb => PReach.step (δ_dd (by omega) (by omega))
      (preach_wakeLF hp hn (a + 1) (by omega) (b - 1) (by omega))

/-- Same as `preach_wakeLF` with the `F` as initiator. -/
lemma preach_wakeFL (hp : p.fixed = true) (hn : 2 ≤ p.n) : ∀ a, 1 ≤ a → ∀ b, a ≤ b →
    PReach p (resetting false 0 a, resetting true 0 b) (settled 2 0, settled 1 1)
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, _, _ => PReach.one (δ_wakeFL hp hn)
  | a + 2, _, b, hb => PReach.step (δ_dd' (by omega) (by omega))
      (preach_wakeFL hp hn (a + 1) (by omega) (b - 1) (by omega))

/-- A triggered agent turns any valid agent into a follower; both then drain to dormancy. -/
lemma preach_trig (hR : 2 ≤ p.Rmax) (hD : 1 ≤ p.Dmax) {s : St} (hs : Valid p s) :
    PReach p (trig p, s) (resetting true 0 p.Dmax, resetting false 0 p.Dmax) := by
  cases s with
  | settled r c => exact PReach.step (δ_trig_S hR) (preach_drain hD _ (by omega) _ _)
  | unsettled e => exact PReach.step (δ_trig_U hR) (preach_drain hD _ (by omega) _ _)
  | resetting l r d =>
    exact PReach.step (δ_trig_R hR hs.1) (preach_drain hD _ (by omega) _ _)

/-- Endgame: two dormant leaders with fresh timers produce ranks `1` and `2`. -/
lemma preach_LL (hp : p.fixed = true) (hn : 2 ≤ p.n) (hD : 2 ≤ p.Dmax) :
    PReach p (resetting true 0 p.Dmax, resetting true 0 p.Dmax) (settled 1 1, settled 2 0) :=
  PReach.step (δ_dd hD hD) (preach_wakeLF hp hn _ (by omega) _ le_rfl)

/-- Two triggered agents produce ranks `1` and `2`. -/
lemma preach_trig_trig (hp : p.fixed = true) (hn : 2 ≤ p.n) (hR : 2 ≤ p.Rmax)
    (hD : 1 ≤ p.Dmax) : PReach p (trig p, trig p) (settled 1 1, settled 2 0) :=
  (preach_trig hR hD (valid_trig p)).trans (preach_wakeLF hp hn _ hD _ le_rfl)

/-! ### The sweep: runs of three agents -/

/-- Clean states: `Unsettled`, or dormant followers. They are recruited in one interaction by
any settled agent that may recruit. -/
def Clean : St → Prop
  | .unsettled _ => True
  | .resetting false 0 _ => True
  | _ => False

instance (s : St) : Decidable (Clean s) := by
  unfold Clean; split <;> infer_instance

/-- Two triggered agents `x, y` turn a third agent into a dormant follower and become dormant
leaders with fresh timers. -/
lemma treach_trig (hR : 2 ≤ p.Rmax) (hD : 1 ≤ p.Dmax) {s : St} (hs : Valid p s) :
    TReach p (trig p, trig p, s)
      (resetting true 0 p.Dmax, resetting true 0 p.Dmax, resetting false 0 p.Dmax) :=
  ((preach_trig hR hD hs).xz (trig p)).trans
    ((preach_trig hR hD (s := resetting false 0 p.Dmax) ⟨by omega, le_rfl⟩).yz _)

/-- **One sweep step.** Two dormant leaders `x, y` with fresh timers turn a third, non-clean
agent into a dormant follower and end up as dormant leaders with fresh timers again. -/
lemma treach_process (hp : p.fixed = true) (hn : 2 ≤ p.n) (hR : 2 ≤ p.Rmax) (hD : 2 ≤ p.Dmax)
    {s : St} (hs : Valid p s) (hc : ¬ Clean s) :
    TReach p (resetting true 0 p.Dmax, resetting true 0 p.Dmax, s)
      (resetting true 0 p.Dmax, resetting true 0 p.Dmax, resetting false 0 p.Dmax) := by
  have hD1 : 1 ≤ p.Dmax := by omega
  have v20 : Valid p (settled 2 0) := ⟨by omega, hn, by omega⟩
  -- from `x = settled 1 _` and `y` a dormant leader to two triggered agents
  have hyx : ∀ c s', TReach p (settled 1 c, resetting true 0 p.Dmax, s') (trig p, trig p, s') :=
    fun c s' => (PReach.one δ_dL_S1).yx s'
  have htr : ∀ s', Valid p s' → TReach p (trig p, trig p, s')
      (resetting true 0 p.Dmax, resetting true 0 p.Dmax, resetting false 0 p.Dmax) :=
    fun s' hs' => treach_trig hR hD1 hs'
  cases s with
  | settled r c =>
    by_cases hr : r = 1
    · subst hr
      have h1 : TReach p (resetting true 0 p.Dmax, resetting true 0 p.Dmax, settled 1 c)
          (trig p, resetting true 0 p.Dmax, trig p) := (PReach.one δ_dL_S1).xz _
      have h2 : TReach p (trig p, resetting true 0 p.Dmax, trig p)
          (resetting true 0 p.Dmax, resetting true 0 p.Dmax, resetting false 0 p.Dmax) :=
        (preach_trig hR hD1 (valid_trig p)).xz _
      exact h1.trans h2
    · have h1 : TReach p (resetting true 0 p.Dmax, resetting true 0 p.Dmax, settled r c)
          (settled 1 0, resetting true 0 p.Dmax, settled r c) := (PReach.one (δ_dL_S hr)).xz _
      exact h1.trans ((hyx 0 _).trans (htr _ hs))
  | unsettled e => exact absurd trivial hc
  | resetting l r d =>
    match r, l, hc, hs with
    | r + 2, l, _, _ =>
      exact (PReach.step δ_dL_P (preach_drain hD1 (r + 1) (by omega) _ _)).xz _
    | 1, l, _, _ =>
      have h1 : TReach p (resetting true 0 p.Dmax, resetting true 0 p.Dmax, resetting l 1 d)
          (settled 1 1, resetting true 0 p.Dmax, settled 2 0) :=
        (PReach.step (δ_dL_P1 hD1 hD) (preach_wakeLF hp hn _ (by omega) _ (by omega))).xz _
      exact h1.trans ((hyx 1 _).trans (htr _ v20))
    | 0, false, hc, _ => exact absurd trivial hc
    | 0, true, _, _ =>
      by_cases hd : d ≤ 1
      · exact (PReach.step (δ_dL_dL1 hD hd) (PReach.step δ_dL_S1
          (preach_trig hR hD1 (valid_trig p)))).xz _
      · have h1 : TReach p (resetting true 0 p.Dmax, resetting true 0 p.Dmax, resetting true 0 d)
            (resetting true 0 (p.Dmax - 1), resetting true 0 p.Dmax, resetting false 0 (d - 1)) :=
          (PReach.one (δ_dd hD (by omega))).xz _
        have h2 : TReach p
            (resetting true 0 (p.Dmax - 1), resetting true 0 p.Dmax, resetting false 0 (d - 1))
            (settled 1 1, resetting true 0 p.Dmax, settled 2 0) := by
          by_cases hle : p.Dmax - 1 ≤ d - 1
          · exact (preach_wakeLF hp hn _ (by omega) _ hle).xz _
          · exact (preach_wakeFL hp hn _ (by omega) _ (by omega)).zx _
        exact h1.trans (h2.trans ((hyx 1 _).trans (htr _ v20)))


/-! ### Two Resetting agents eventually wake up -/

variable (p) in
/-- Both agents computing, or both freshly triggered. -/
def PairDone (u : St × St) : Prop :=
  (u.1.isResetting = false ∧ u.2.isResetting = false) ∨ u = (trig p, trig p)

variable (p) in
/-- Lines 3–18 of Protocol 3 (everything after `Propagate-Reset`). -/
def post (x : St × St) : St × St :=
  let x3 := collide p (leaderElect x)
  let x4 := recruit p x3.1 x3.2
  let x5 := (recruit p x4.2 x4.1).swap
  countdown p x5

lemma δ_eq_post (a b : St) : δ p a b = post p (if a.isResetting then propagateReset p a b
    else if b.isResetting then (propagateReset p b a).swap else (a, b)) := rfl

lemma PairDone_recruit {u : St × St} (h : PairDone p u) : PairDone p (recruit p u.1 u.2) := by
  rcases h with ⟨h1, h2⟩ | rfl
  · rcases u with ⟨a, b⟩
    cases a with
    | settled r c =>
      cases b with
      | unsettled e =>
        simp only [recruit]; split_ifs
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
      | _ => exact Or.inl ⟨h1, h2⟩
    | _ => exact Or.inl ⟨h1, h2⟩
  · right; simp [recruit, trig]

lemma PairDone_swap {u : St × St} (h : PairDone p u) : PairDone p (u.2, u.1) := by
  rcases h with ⟨h1, h2⟩ | rfl
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr rfl

lemma isResetting_dec (s : St) : (dec s).isResetting = s.isResetting := by
  cases s <;> rfl

lemma PairDone_countdown {u : St × St} (h : PairDone p u) : PairDone p (countdown p u) := by
  unfold countdown
  split_ifs
  · exact Or.inr rfl
  · exact Or.inr rfl
  · rcases h with ⟨h1, h2⟩ | rfl
    · exact Or.inl ⟨by rw [isResetting_dec, h1], by rw [isResetting_dec, h2]⟩
    · exact Or.inr (by simp [dec, trig])

lemma post_CC {a b : St} (ha : a.isResetting = false) (hb : b.isResetting = false) :
    PairDone p (post p (a, b)) := by
  have hle : leaderElect (a, b) = (a, b) := by
    cases a <;> cases b <;> simp_all [leaderElect, St.isResetting]
  have hcol : PairDone p (collide p (a, b)) := by
    cases a with
    | settled ra ca =>
      cases b with
      | settled rb cb =>
        simp only [collide]; split_ifs
        · exact Or.inr rfl
        · exact Or.inl ⟨rfl, rfl⟩
      | unsettled e => exact Or.inl ⟨rfl, rfl⟩
      | resetting => simp [St.isResetting] at hb
    | unsettled e => exact Or.inl ⟨rfl, hb⟩
    | resetting => simp [St.isResetting] at ha
  unfold post
  simp only [hle]
  exact PairDone_countdown (PairDone_swap (PairDone_recruit (PairDone_swap (PairDone_recruit hcol))))

lemma post_RR {la lb : Bool} {ra rb da db : ℕ} :
    post p (resetting la ra da, resetting lb rb db) =
      (resetting la ra da, resetting (lb && !la) rb db) := by
  cases la <;> cases lb <;> simp [post, leaderElect, collide, recruit, countdown, dec, expired]

lemma post_RC {l : Bool} {r d : ℕ} {c : St} (hc : c.isResetting = false) :
    PairDone p (post p (resetting l r d, c)) ∨
      ∃ c', c'.isResetting = false ∧ post p (resetting l r d, c) = (resetting l r d, c') := by
  cases c with
  | settled r' c' =>
    right; refine ⟨settled r' c', rfl, ?_⟩
    cases l <;> simp [post, leaderElect, collide, recruit, countdown, dec, expired]
  | unsettled e =>
    by_cases he : e - 1 = 0
    · left; right
      cases l <;> simp [post, leaderElect, collide, recruit, countdown, dec, expired, he]
    · right; refine ⟨unsettled (e - 1), rfl, ?_⟩
      cases l <;> simp [post, leaderElect, collide, recruit, countdown, dec, expired, he]
  | resetting => simp [St.isResetting] at hc

lemma isResetting_reset {s : St} (h : s.isResetting = true) : (reset p s).isResetting = false := by
  cases s with
  | resetting l r d => cases l <;> rfl
  | _ => simp [St.isResetting] at h

lemma ds_zero_wake {w o : Bool} {l : Bool} {d : ℕ}
    (h : (if w = true then p.Dmax else d - 1) = 0 ∨ o = true) :
    (dormantStep p w o (resetting l 0 d)).isResetting = false := by
  simp only [dormantStep, h, ite_true]
  exact isResetting_reset rfl

lemma ds_zero_stay {w o : Bool} {l : Bool} {d : ℕ}
    (h : ¬ ((if w = true then p.Dmax else d - 1) = 0 ∨ o = true)) :
    dormantStep p w o (resetting l 0 d) =
      resetting l 0 (if w = true then p.Dmax else d - 1) := by
  simp only [dormantStep, h, ite_false]

lemma δ_RR {la lb : Bool} {ra rb da db : ℕ} :
    δ p (resetting la ra da) (resetting lb rb db) = post p
      (dormantStep p (decide (0 < ra)) false (resetting la (max (ra - 1) (rb - 1)) da),
       dormantStep p (decide (0 < rb))
        (!(dormantStep p (decide (0 < ra)) false
          (resetting la (max (ra - 1) (rb - 1)) da)).isResetting)
        (resetting lb (max (ra - 1) (rb - 1)) db)) := by
  have e : ∀ l r d, (resetting l r d).isResetting = true := fun _ _ _ => rfl
  rw [δ_eq_post]
  simp [propagateReset, e, St.rc]
  rfl

/-- One interaction of two Resetting agents: both computing or triggered, or only the
initiator is (dormant and) Resetting, or both still Resetting with a smaller measure. -/
lemma step_RR (la lb : Bool) (ra rb da db : ℕ) :
    PairDone p (δ p (resetting la ra da) (resetting lb rb db)) ∨
    (∃ l d c, c.isResetting = false ∧
      δ p (resetting la ra da) (resetting lb rb db) = (resetting l 0 d, c)) ∨
    (∃ la' lb' r da' db', δ p (resetting la ra da) (resetting lb rb db) =
      (resetting la' r da', resetting lb' r db') ∧
      (r < max ra rb ∨ (ra = 0 ∧ rb = 0 ∧ r = 0 ∧ da' < da))) := by
  rw [δ_RR]
  generalize hm : max (ra - 1) (rb - 1) = m
  cases m with
  | succ m' =>
    have e1 : ∀ w o l d, dormantStep p w o (resetting l (m' + 1) d) = resetting l (m' + 1) d :=
      fun _ _ _ _ => rfl
    simp only [e1, post_RR]
    exact Or.inr (Or.inr ⟨_, _, _, _, _, rfl, Or.inl (by omega)⟩)
  | zero =>
    by_cases hA : (if decide (0 < ra) = true then p.Dmax else da - 1) = 0 ∨ false = true
    · have ha3 := ds_zero_wake (p := p) (l := la) hA
      generalize dormantStep p (decide (0 < ra)) false (resetting la 0 da) = a3 at *
      rw [ha3]
      have hb3 := ds_zero_wake (p := p) (w := decide (0 < rb)) (l := lb) (d := db)
        (o := !false) (Or.inr rfl)
      generalize dormantStep p (decide (0 < rb)) (!false) (resetting lb 0 db) = b3 at *
      exact Or.inl (post_CC ha3 hb3)
    · rw [ds_zero_stay hA]
      generalize hdA : (if decide (0 < ra) = true then p.Dmax else da - 1) = dA at *
      simp only [St.isResetting, Bool.not_true]
      by_cases hB : (if decide (0 < rb) = true then p.Dmax else db - 1) = 0 ∨ false = true
      · have hb3 := ds_zero_wake (p := p) (l := lb) hB
        generalize dormantStep p (decide (0 < rb)) false (resetting lb 0 db) = b3 at *
        rcases post_RC (p := p) (l := la) (r := 0) (d := dA) hb3 with h | ⟨c', hc', h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨_, _, _, hc', h⟩)
      · rw [ds_zero_stay hB, post_RR]
        refine Or.inr (Or.inr ⟨_, _, _, _, _, rfl, ?_⟩)
        by_cases hr : 0 < max ra rb
        · exact Or.inl hr
        · right
          have hra : ra = 0 := by omega
          have hrb : rb = 0 := by omega
          subst hra hrb
          simp only [lt_self_iff_false, decide_false, Bool.false_eq_true, ite_false] at hdA
          omega

lemma δ_dorm_comp {l : Bool} {d : ℕ} {c : St} (hc : c.isResetting = false) :
    PairDone p (δ p (resetting l 0 d) c) := by
  rw [δ_eq_post]
  have hw : (reset p (resetting l 0 (d - 1))).isResetting = false := isResetting_reset rfl
  cases c with
  | settled r c' =>
    simp only [propagateReset, St.isResetting, ite_true, lt_self_iff_false, false_and,
      ite_false, decide_false, dormantStep, Bool.not_false, or_true, St.rc, Bool.and_false]
    exact post_CC hw rfl
  | unsettled e =>
    simp only [propagateReset, St.isResetting, ite_true, lt_self_iff_false, false_and,
      ite_false, decide_false, dormantStep, Bool.not_false, or_true, St.rc, Bool.and_false]
    exact post_CC hw rfl
  | resetting => simp [St.isResetting] at hc

/-- Repeated interactions of two Resetting agents lead to both computing or both triggered. -/
lemma preach_RR0 : ∀ (da : ℕ) (la lb : Bool) (db : ℕ),
    ∃ u, PReach p (resetting la 0 da, resetting lb 0 db) u ∧ PairDone p u := by
  intro da
  induction da using Nat.strong_induction_on with
  | _ da ih =>
    intro la lb db
    rcases step_RR (p := p) la lb 0 0 da db with h | ⟨l, d, c, hc, h⟩ | ⟨la', lb', r, da', db', h, hr⟩
    · exact ⟨_, PReach.one rfl, h⟩
    · exact ⟨_, PReach.step h (PReach.one rfl), δ_dorm_comp hc⟩
    · rcases hr with hr | ⟨-, -, rfl, hd⟩
      · simp at hr
      · obtain ⟨u, hu, hG⟩ := ih da' hd la' lb' db'
        exact ⟨u, PReach.step h hu, hG⟩

lemma preach_RR : ∀ (N : ℕ) (la lb : Bool) (ra rb da db : ℕ), max ra rb = N →
    ∃ u, PReach p (resetting la ra da, resetting lb rb db) u ∧ PairDone p u := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro la lb ra rb da db hN
    by_cases h0 : N = 0
    · have hra : ra = 0 := by omega
      have hrb : rb = 0 := by omega
      subst hra hrb
      exact preach_RR0 da la lb db
    rcases step_RR (p := p) la lb ra rb da db with h | ⟨l, d, c, hc, h⟩ |
        ⟨la', lb', r, da', db', h, hr⟩
    · exact ⟨_, PReach.one rfl, h⟩
    · exact ⟨_, PReach.step h (PReach.one rfl), δ_dorm_comp hc⟩
    · rcases hr with hr | ⟨hra, hrb, -, -⟩
      · obtain ⟨u, hu, hG⟩ := ih r (by omega) la' lb' r r da' db' (max_self r)
        exact ⟨u, PReach.step h hu, hG⟩
      · omega

lemma δ_prop_comp (hD : 2 ≤ p.Dmax) {l : Bool} {r d : ℕ} {c : St} (hc : c.isResetting = false) :
    ∃ la ra da lb rb db, δ p (resetting l (r + 1) d) c = (resetting la ra da, resetting lb rb db) := by
  have h1 : p.Dmax ≠ 0 := by omega
  have h2 : p.Dmax - 1 ≠ 0 := by omega
  cases c with
  | settled r' c' =>
    cases r <;> cases l <;> simp [δ, propagateReset, dormantStep, reset, leaderElect, collide,
      recruit, countdown, dec, expired, St.isResetting, St.rc, h1, h2]
  | unsettled e =>
    cases r <;> cases l <;> simp [δ, propagateReset, dormantStep, reset, leaderElect, collide,
      recruit, countdown, dec, expired, St.isResetting, St.rc, h1, h2]
  | resetting => simp [St.isResetting] at hc

/-- A Resetting agent and any other agent: repeated interactions lead to both computing or both
triggered. -/
lemma preach_R_any (hD : 2 ≤ p.Dmax) {s c : St} (hs : s.isResetting = true) :
    ∃ u, PReach p (s, c) u ∧ PairDone p u := by
  cases s with
  | resetting l r d =>
    cases hcr : c.isResetting with
    | false =>
      cases r with
      | zero => exact ⟨_, PReach.one rfl, δ_dorm_comp hcr⟩
      | succ r =>
        obtain ⟨la, ra, da, lb, rb, db, h⟩ := δ_prop_comp (p := p) (l := l) (r := r) (d := d) hD hcr
        obtain ⟨u, hu, hG⟩ := preach_RR (p := p) _ la lb ra rb da db rfl
        exact ⟨u, PReach.step h hu, hG⟩
    | true =>
      cases c with
      | resetting lb rb db => exact preach_RR _ l lb r rb d db rfl
      | _ => simp [St.isResetting] at hcr
  | _ => simp [St.isResetting] at hs

/-! ### The sweep on configurations -/

section Config

variable [Fintype A]

/-- **The sweep.** Starting from two dormant leaders `x, y` with fresh timers, a configuration is
reachable in which `x, y` are still such leaders and every other agent is clean. -/
lemma sweep (hp : p.fixed = true) (hn : 2 ≤ p.n) (hR : 2 ≤ p.Rmax) (hD : 2 ≤ p.Dmax)
    {x y : A} (hxy : x ≠ y) : ∀ (k : ℕ) (C : Config A St),
    (Finset.univ.filter fun z => z ≠ x ∧ z ≠ y ∧ ¬ Clean (C z)).card = k →
    (∀ z, Valid p (C z)) → C x = resetting true 0 p.Dmax → C y = resetting true 0 p.Dmax →
    ∃ D, (protocol p).Reachable C D ∧ D x = resetting true 0 p.Dmax ∧
      D y = resetting true 0 p.Dmax ∧ ∀ z, z ≠ x → z ≠ y → Clean (D z) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hC hx hy
    by_cases hd : ∃ t, t ≠ x ∧ t ≠ y ∧ ¬ Clean (C t)
    · obtain ⟨t, htx, hty, htc⟩ := hd
      have h3 : TReach p (C x, C y, C t) (resetting true 0 p.Dmax, resetting true 0 p.Dmax,
          resetting false 0 p.Dmax) := by
        rw [hx, hy]; exact treach_process hp hn hR hD (hC t) htc
      obtain ⟨D, hCD, hDx, hDy, hDt, hDo⟩ := TripleReach.lift hxy htx.symm hty.symm h3
      have hDv : ∀ z, Valid p (D z) := valid_reachable p (by omega) hC hCD
      have hlt : (Finset.univ.filter fun z => z ≠ x ∧ z ≠ y ∧ ¬ Clean (D z)).card < k := by
        rw [← hk]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨t, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          refine ⟨hz.1, hz.2.1, ?_⟩
          by_cases hzt : z = t
          · subst hzt; exact absurd (by rw [hDt]; trivial) hz.2.2
          · rw [← hDo z hz.1 hz.2.1 hzt]; exact hz.2.2
        · simp [htx, hty, htc]
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
          intro _ _; rw [hDt]; trivial
      obtain ⟨E, hDE, hE⟩ := ih _ hlt D rfl hDv hDx hDy
      exact ⟨E, hCD.trans hDE, hE⟩
    · push Not at hd
      exact ⟨C, Relation.ReflTransGen.refl, hx, hy, hd⟩

/-! ### Breadth-first recruitment -/

/-- Number of children of rank `r` once ranks `1, …, m` have been assigned. -/
def ch (m r : ℕ) : ℕ := (if 2 * r ≤ m then 1 else 0) + (if 2 * r + 1 ≤ m then 1 else 0)

/-- Ranks `1, …, m` are held by settled agents (with the right number of children), all other
agents are clean. -/
structure BFS (m : ℕ) (C : Config A St) : Prop where
  state : ∀ a, Clean (C a) ∨ ∃ r, 1 ≤ r ∧ r ≤ m ∧ C a = settled r (ch m r)
  surj : ∀ r, 1 ≤ r → r ≤ m → ∃ a, (C a).rankOut = r
  inj : ∀ a b, 1 ≤ (C a).rankOut → (C a).rankOut = (C b).rankOut → a = b

lemma Clean.rankOut {s : St} (h : Clean s) : s.rankOut = 0 := by
  cases s with
  | settled r c => exact absurd h id
  | unsettled e => rfl
  | resetting l r d => rfl

lemma BFS.settled_of_rank {m : ℕ} {C : Config A St} (hC : BFS m C) {a : A}
    (ha : 1 ≤ (C a).rankOut) : C a = settled (C a).rankOut (ch m (C a).rankOut) ∧
      (C a).rankOut ≤ m := by
  rcases hC.state a with h | ⟨r, hr1, hrm, h⟩
  · rw [h.rankOut] at ha; omega
  · rw [h]; exact ⟨rfl, hrm⟩

lemma BFS.card_le {m : ℕ} {C : Config A St} (hC : BFS m C) (h : ∀ a, ¬ Clean (C a)) :
    Fintype.card A ≤ m := by
  have hr : ∀ a, 1 ≤ (C a).rankOut ∧ (C a).rankOut ≤ m := by
    intro a
    rcases hC.state a with h' | ⟨r, hr1, hrm, h'⟩
    · exact absurd h' (h a)
    · rw [h']; exact ⟨hr1, hrm⟩
  have := Finset.card_le_card_of_injOn (fun a => (C a).rankOut) (s := Finset.univ)
    (t := Finset.Icc 1 m) (fun a _ => by simpa using hr a)
    (fun a _ b _ hab => hC.inj a b (hr a).1 hab)
  simpa using this

lemma BFS.lt_card {m : ℕ} {C : Config A St} (hC : BFS m C) {z : A} (hz : Clean (C z)) :
    m < Fintype.card A := by
  classical
  have hsub : Finset.Icc 1 m ⊆ (Finset.univ.erase z).image fun a => (C a).rankOut := by
    intro r hr
    simp only [Finset.mem_Icc] at hr
    obtain ⟨a, ha⟩ := hC.surj r hr.1 hr.2
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨a, ?_, ha⟩
    rintro rfl
    rw [hz.rankOut] at ha; omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := Finset.univ.erase z) (f := fun a => (C a).rankOut)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h2
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h1
  have : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨z⟩
  omega

lemma BFS.ranked {C : Config A St} (hA : Fintype.card A = p.n) (hC : BFS p.n C) : Ranked p C := by
  have hnc : ∀ a, ¬ Clean (C a) := fun a ha => by have := hC.lt_card ha; omega
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rcases hC.state a with h | ⟨r, hr1, hrm, h⟩
    · exact absurd h (hnc a)
    · rw [h]; exact ⟨hr1, hrm⟩
  · rcases hC.state a with h | ⟨r, hr1, hrm, h⟩
    · exact absurd h (hnc a)
    · exact hC.inj a b (by rw [h]; exact hr1) hab

lemma δ_recruit_clean (hp : p.fixed = true) {r c : ℕ} {s : St} (hs : Clean s) (hc : c < 2)
    (hg : 2 * r + c ≤ p.n) : δ p (settled r c) s = (settled r (c + 1), settled (2 * r + c) 0) := by
  match s, hs with
  | unsettled e, _ =>
    simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
      expired, St.isResetting, guard, hp, hc, hg]
  | resetting false 0 d, _ =>
    simp [δ, propagateReset, dormantStep, reset, leaderElect, collide, recruit, countdown, dec,
      expired, St.isResetting, guard, hp, hc, hg, St.rc]

lemma BFS.step (hp : p.fixed = true) (hA : Fintype.card A = p.n) {m : ℕ} (hm : 1 ≤ m)
    (hmn : m < p.n) {C : Config A St} (hC : BFS m C) :
    ∃ D, (protocol p).Reachable C D ∧ BFS (m + 1) D := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, Clean (C z) := by
    by_contra h
    push Not at h
    have := hC.card_le h; omega
  set r₀ := (m + 1) / 2 with hr₀
  obtain ⟨s, hs⟩ := hC.surj r₀ (by omega) (by omega)
  obtain ⟨hCs, -⟩ := hC.settled_of_rank (a := s) (by omega)
  rw [hs] at hCs
  have hsz : s ≠ z := by rintro rfl; rw [hz.rankOut] at hs; omega
  have hδ := δ_recruit_clean (p := p) hp hz (r := r₀) (c := ch m r₀)
    (by unfold ch; split_ifs <;> omega) (by unfold ch; split_ifs <;> omega)
  rw [← hCs] at hδ
  obtain ⟨D, hCD, hDs, hDz, hDo⟩ := PairReach.lift (P := protocol p) hsz (PReach.one hδ)
  simp only at hDs hDz
  have h2 : 2 * r₀ + ch m r₀ = m + 1 := by unfold ch; split_ifs <;> omega
  rw [h2] at hDz
  refine ⟨D, hCD, ⟨fun a => ?_, fun r hr1 hr2 => ?_, fun a b ha hab => ?_⟩⟩
  · by_cases has : a = s
    · subst has; right; refine ⟨r₀, by omega, by omega, ?_⟩
      rw [hDs]; congr 1; unfold ch; split_ifs <;> omega
    · by_cases haz : a = z
      · subst haz; right; refine ⟨m + 1, by omega, le_rfl, ?_⟩
        rw [hDz]; congr 1; unfold ch; split_ifs <;> omega
      · rw [hDo a has haz]
        rcases hC.state a with h | ⟨r, hr1, hrm, h⟩
        · exact Or.inl h
        · right
          have hr : r ≠ r₀ := by
            rintro rfl
            exact has (hC.inj a s (by rw [h]; simpa [St.rankOut] using hr1)
              (by rw [h, hs]; rfl))
          refine ⟨r, hr1, by omega, ?_⟩
          rw [h]; congr 1; unfold ch; split_ifs <;> omega
  · by_cases hrm : r = m + 1
    · exact ⟨z, by rw [hDz, hrm]; rfl⟩
    · by_cases hr : r = r₀
      · exact ⟨s, by rw [hDs, hr]; rfl⟩
      · obtain ⟨a, ha⟩ := hC.surj r hr1 (by omega)
        have has : a ≠ s := by rintro rfl; exact hr (ha.symm.trans hs)
        have haz : a ≠ z := by rintro rfl; rw [hz.rankOut] at ha; omega
        exact ⟨a, by rw [hDo a has haz, ha]⟩
  · -- ranks in `D`
    have hrk : ∀ w, (D w).rankOut =
        if w = s then r₀ else if w = z then m + 1 else (C w).rankOut := by
      intro w
      by_cases hws : w = s
      · subst hws; rw [hDs]; simp [St.rankOut]
      · by_cases hwz : w = z
        · subst hwz; rw [hDz]; simp [St.rankOut, hws]
        · rw [hDo w hws hwz]; simp [hws, hwz]
    have hold : ∀ w, w ≠ s → 1 ≤ (C w).rankOut → (C w).rankOut ≤ m ∧ (C w).rankOut ≠ r₀ := by
      intro w hws hw
      refine ⟨(hC.settled_of_rank hw).2, fun h => hws (hC.inj w s hw (h.trans hs.symm))⟩
    have hval : ∀ w, (w = s ∧ (D w).rankOut = r₀) ∨ (w = z ∧ (D w).rankOut = m + 1) ∨
        (w ≠ s ∧ (D w).rankOut = (C w).rankOut ∧
          ((C w).rankOut = 0 ∨ ((C w).rankOut ≤ m ∧ (C w).rankOut ≠ r₀))) := by
      intro w
      rw [hrk w]
      by_cases hws : w = s
      · simp [hws]
      · by_cases hwz : w = z
        · simp [hwz, hsz.symm]
        · simp only [hws, hwz, ite_false, false_and, false_or, ne_eq, not_false_eq_true,
            true_and]
          by_cases h0 : (C w).rankOut = 0
          · exact Or.inl h0
          · exact Or.inr (hold w hws (by omega))
    have hm2 : r₀ < m + 1 := by omega
    rcases hval a with ⟨rfl, ha'⟩ | ⟨rfl, ha'⟩ | ⟨has, ha', ha''⟩ <;>
    rcases hval b with ⟨rfl, hb'⟩ | ⟨rfl, hb'⟩ | ⟨hbs, hb', hb''⟩ <;>
    first
      | rfl
      | omega
      | exact hC.inj a b (by omega) (by omega)

/-- BFS recruitment completes the ranking. -/
lemma BFS.reach_ranked (hp : p.fixed = true) (hA : Fintype.card A = p.n) :
    ∀ j m (C : Config A St), m + j = p.n → 1 ≤ m → BFS m C →
      ∃ D, (protocol p).Reachable C D ∧ Ranked p D
  | 0, m, C, hj, _, hC => ⟨C, Relation.ReflTransGen.refl, by simp at hj; subst hj; exact hC.ranked hA⟩
  | j + 1, m, C, hj, hm, hC => by
    obtain ⟨D, hCD, hD⟩ := hC.step hp hA hm (by omega)
    obtain ⟨E, hDE, hE⟩ := BFS.reach_ranked hp hA j (m + 1) D (by omega) (by omega) hD
    exact ⟨E, hCD.trans hDE, hE⟩

/-- From ranks `1, 2` at `x, y` and all other agents clean, the ranking completes. -/
lemma reach_ranked_of_12 (hp : p.fixed = true) (hA : Fintype.card A = p.n) (hn : 2 ≤ p.n)
    {C : Config A St} {x y : A} (hxy : x ≠ y) (hx : C x = settled 1 1) (hy : C y = settled 2 0)
    (ho : ∀ z, z ≠ x → z ≠ y → Clean (C z)) : ∃ D, (protocol p).Reachable C D ∧ Ranked p D := by
  have hrk : ∀ w, (C w).rankOut = if w = x then 1 else if w = y then 2 else 0 := by
    intro w
    by_cases hwx : w = x
    · subst hwx; simp [hx, St.rankOut]
    · by_cases hwy : w = y
      · subst hwy; simp [hy, St.rankOut, hwx]
      · simp [hwx, hwy, (ho w hwx hwy).rankOut]
  have hB : BFS 2 C := by
    refine ⟨fun a => ?_, fun r hr1 hr2 => ?_, fun a b ha hab => ?_⟩
    · by_cases hax : a = x
      · subst hax; exact Or.inr ⟨1, le_rfl, by omega, by rw [hx]; rfl⟩
      · by_cases hay : a = y
        · subst hay; exact Or.inr ⟨2, by omega, le_rfl, by rw [hy]; rfl⟩
        · exact Or.inl (ho a hax hay)
    · by_cases hr : r = 1
      · exact ⟨x, by rw [hrk]; simp [hr]⟩
      · exact ⟨y, by rw [hrk]; simp [hxy.symm]; omega⟩
    · have hval : ∀ w, (w = x ∧ (C w).rankOut = 1) ∨ (w = y ∧ (C w).rankOut = 2) ∨
          (C w).rankOut = 0 := by
        intro w
        rw [hrk w]
        by_cases hwx : w = x
        · simp [hwx]
        · by_cases hwy : w = y
          · simp [hwy, hxy.symm]
          · simp [hwx, hwy]
      rcases hval a with ⟨rfl, ha'⟩ | ⟨rfl, ha'⟩ | ha' <;>
      rcases hval b with ⟨rfl, hb'⟩ | ⟨rfl, hb'⟩ | hb' <;>
      first | rfl | omega
  exact BFS.reach_ranked hp hA (p.n - 2) 2 C (by omega) (by omega) hB

/-! ### Phase 0: no Resetting agents (or two triggered agents) -/

/-- From any configuration, a configuration is reachable that either contains two triggered agents
or has no Resetting agent. -/
lemma phase0 (hD : 2 ≤ p.Dmax) (hA2 : 1 < Fintype.card A) : ∀ (k : ℕ) (C : Config A St),
    (Finset.univ.filter fun z => (C z).isResetting = true).card = k →
    ∃ D, (protocol p).Reachable C D ∧
      ((∃ x y, x ≠ y ∧ D x = trig p ∧ D y = trig p) ∨ ∀ z, (D z).isResetting = false) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk
    by_cases h0 : ∀ z, (C z).isResetting = false
    · exact ⟨C, Relation.ReflTransGen.refl, Or.inr h0⟩
    push Not at h0
    obtain ⟨w, hw⟩ := h0
    have hw' : (C w).isResetting = true := by simpa using hw
    obtain ⟨c, hcw⟩ := Fintype.exists_ne_of_one_lt_card hA2 w
    obtain ⟨u, hu, hG⟩ := preach_R_any (p := p) (c := C c) hD hw'
    obtain ⟨D, hCD, hDw, hDc, hDo⟩ := PairReach.lift (P := protocol p) hcw.symm hu
    rcases hG with ⟨h1, h2⟩ | htr
    · have hlt : (Finset.univ.filter fun z => (D z).isResetting = true).card < k := by
        rw [← hk]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨w, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          by_cases hzw : z = w
          · subst hzw; rw [hDw, h1] at hz; exact absurd hz (by simp)
          · by_cases hzc : z = c
            · subst hzc; rw [hDc, h2] at hz; exact absurd hz (by simp)
            · rwa [← hDo z hzw hzc]
        · simp [hw']
        · simp [hDw, h1]
      obtain ⟨E, hDE, hE⟩ := ih _ hlt D rfl
      exact ⟨E, hCD.trans hDE, hE⟩
    · exact ⟨D, hCD, Or.inl ⟨w, c, hcw.symm, by rw [hDw, htr], by rw [hDc, htr]⟩⟩

/-! ### Phase 1: only computing agents -/

lemma δ_UU {a b : ℕ} : δ p (unsettled a) (unsettled b) =
    if a - 1 = 0 ∨ b - 1 = 0 then (trig p, trig p) else (unsettled (a - 1), unsettled (b - 1)) := by
  by_cases ha : a - 1 = 0
  · simp [δ, leaderElect, collide, recruit, countdown, dec, expired, St.isResetting, ha]
  · by_cases hb : b - 1 = 0
    · simp [δ, leaderElect, collide, recruit, countdown, dec, expired, St.isResetting, ha, hb]
    · simp [δ, leaderElect, collide, recruit, countdown, dec, expired, St.isResetting, ha, hb]

lemma preach_UU : ∀ a b : ℕ, PReach p (unsettled a, unsettled b) (trig p, trig p) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b
    by_cases h : a - 1 = 0 ∨ b - 1 = 0
    · exact PReach.one (by simp only [δ_UU, h, ite_true, true_or, or_true])
    · exact PReach.step (by simp only [δ_UU, h, ite_false]) (ih (a - 1) (by omega) (b - 1))

lemma δ_SU_stuck (hp : p.fixed = true) {r c e : ℕ} (h : ¬ (c < 2 ∧ 2 * r + c ≤ p.n)) :
    δ p (settled r c) (unsettled e) =
      if e - 1 = 0 then (trig p, trig p) else (settled r c, unsettled (e - 1)) := by
  have hg : ¬ (c < 2 ∧ guard p r c) := by simpa [guard, hp] using h
  by_cases he : e - 1 = 0
  · simp [δ, leaderElect, collide, recruit, countdown, dec, expired, St.isResetting, he, hg]
  · simp [δ, leaderElect, collide, recruit, countdown, dec, expired, St.isResetting, he, hg]

lemma preach_SU (hp : p.fixed = true) {r c : ℕ} (h : ¬ (c < 2 ∧ 2 * r + c ≤ p.n)) :
    ∀ e : ℕ, PReach p (settled r c, unsettled e) (trig p, trig p) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    by_cases he : e - 1 = 0
    · exact PReach.one (by simp only [δ_SU_stuck hp h, he, ite_true])
    · exact PReach.step (by simp only [δ_SU_stuck hp h, he, ite_false]) (ih (e - 1) (by omega))

lemma δ_SS {r c c' : ℕ} : δ p (settled r c) (settled r c') = (trig p, trig p) := by
  simp [δ, leaderElect, collide, recruit, countdown, dec, expired, St.isResetting, trig]

lemma computing_cases {s : St} (h : s.isResetting = false) :
    (∃ r c, s = settled r c) ∨ ∃ e, s = unsettled e := by
  cases s with
  | settled r c => exact Or.inl ⟨r, c, rfl⟩
  | unsettled e => exact Or.inr ⟨e, rfl⟩
  | resetting => simp [St.isResetting] at h

lemma reach_of_allSettled {C : Config A St} (hC : ∀ a, Valid p (C a))
    (hs : ∀ a, ∃ r c, C a = settled r c) :
    ∃ D, (protocol p).Reachable C D ∧
      (Ranked p D ∨ ∃ x y, x ≠ y ∧ D x = trig p ∧ D y = trig p) := by
  by_cases hinj : Function.Injective fun a => (C a).rankOut
  · refine ⟨C, Relation.ReflTransGen.refl, Or.inl ⟨fun a => ?_, hinj⟩⟩
    obtain ⟨r, c, h⟩ := hs a
    have := hC a
    rw [h] at this ⊢
    exact ⟨this.1, this.2.1⟩
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨a, b, hab, hne⟩ := hinj
    obtain ⟨r, c, ha⟩ := hs a
    obtain ⟨r', c', hb⟩ := hs b
    rw [ha, hb] at hab
    simp only [St.rankOut] at hab
    subst hab
    have h1 : PReach p (C a, C b) (trig p, trig p) := by rw [ha, hb]; exact PReach.one δ_SS
    obtain ⟨D, hCD, hDa, hDb, -⟩ := PairReach.lift (P := protocol p) hne h1
    exact ⟨D, hCD, Or.inr ⟨a, b, hne, hDa, hDb⟩⟩

/-- From a valid configuration without Resetting agents, a ranked configuration or a
configuration with two triggered agents is reachable. -/
lemma phase1 (hp : p.fixed = true) (hn : 2 ≤ p.n) (hA2 : 1 < Fintype.card A) {C : Config A St}
    (hC : ∀ a, Valid p (C a)) (hcomp : ∀ a, (C a).isResetting = false) :
    ∃ D, (protocol p).Reachable C D ∧
      (Ranked p D ∨ ∃ x y, x ≠ y ∧ D x = trig p ∧ D y = trig p) := by
  classical
  by_cases hU2 : ∃ u v, u ≠ v ∧ (∃ e, C u = unsettled e) ∧ ∃ e, C v = unsettled e
  · obtain ⟨u, v, huv, ⟨e, he⟩, ⟨e', he'⟩⟩ := hU2
    have h1 : PReach p (C u, C v) (trig p, trig p) := by rw [he, he']; exact preach_UU e e'
    obtain ⟨D, hCD, hDu, hDv, -⟩ := PairReach.lift (P := protocol p) huv h1
    exact ⟨D, hCD, Or.inr ⟨u, v, huv, hDu, hDv⟩⟩
  push Not at hU2
  by_cases hU1 : ∃ u e, C u = unsettled e
  · obtain ⟨u, e, hu⟩ := hU1
    by_cases hst : ∃ s r c, C s = settled r c ∧ ¬ (c < 2 ∧ 2 * r + c ≤ p.n)
    · obtain ⟨s, r, c, hs, hg⟩ := hst
      have hsu : s ≠ u := by rintro rfl; rw [hs] at hu; cases hu
      have h1 : PReach p (C s, C u) (trig p, trig p) := by
        rw [hs, hu]; exact preach_SU hp hg e
      obtain ⟨D, hCD, hDs, hDu, -⟩ := PairReach.lift (P := protocol p) hsu h1
      exact ⟨D, hCD, Or.inr ⟨s, u, hsu, hDs, hDu⟩⟩
    · push Not at hst
      obtain ⟨s, hsu⟩ := Fintype.exists_ne_of_one_lt_card hA2 u
      have hset : ∀ z, z ≠ u → ∃ r c, C z = settled r c := by
        intro z hz
        rcases computing_cases (hcomp z) with h | ⟨e', h⟩
        · exact h
        · exact absurd hu (hU2 z u hz ⟨e', h⟩ e)
      obtain ⟨r, c, hs⟩ := hset s hsu
      obtain ⟨hc2, hg⟩ := hst s r c hs
      have h1 : PReach p (C s, C u) (settled r (c + 1), settled (2 * r + c) 0) := by
        rw [hs, hu]; exact PReach.one (δ_recruit_clean hp trivial (hc2) (hg))
      obtain ⟨D, hCD, hDs, hDu, hDo⟩ := PairReach.lift (P := protocol p) hsu h1
      have hDv := valid_reachable p (by omega) hC hCD
      obtain ⟨E, hDE, hE⟩ := reach_of_allSettled hDv (fun z => by
        by_cases hzs : z = s
        · subst hzs; exact ⟨_, _, hDs⟩
        · by_cases hzu : z = u
          · subst hzu; exact ⟨_, _, hDu⟩
          · rw [hDo z hzs hzu]; exact hset z hzu)
      exact ⟨E, hCD.trans hDE, hE⟩
  · push Not at hU1
    exact reach_of_allSettled hC fun z => by
      rcases computing_cases (hcomp z) with h | ⟨e', h⟩
      · exact h
      · exact absurd h (hU1 z e')

/-! ### From two triggered agents to a ranked configuration -/

lemma reach_ranked_of_trig (hp : p.fixed = true) (hA : Fintype.card A = p.n) (hn : 2 ≤ p.n)
    (hR : 2 ≤ p.Rmax) (hD : 2 ≤ p.Dmax) {C : Config A St} (hC : ∀ a, Valid p (C a)) {x y : A}
    (hxy : x ≠ y) (hx : C x = trig p) (hy : C y = trig p) :
    ∃ D, (protocol p).Reachable C D ∧ Ranked p D := by
  classical
  have hD1 : 1 ≤ p.Dmax := by omega
  by_cases hd : ∃ t, t ≠ x ∧ t ≠ y ∧ ¬ Clean (C t)
  · obtain ⟨t, htx, hty, -⟩ := hd
    have h3 : TReach p (C x, C y, C t) (resetting true 0 p.Dmax, resetting true 0 p.Dmax,
        resetting false 0 p.Dmax) := by
      rw [hx, hy]; exact treach_trig hR hD1 (hC t)
    obtain ⟨D₁, hCD₁, hD₁x, hD₁y, -, -⟩ := TripleReach.lift hxy htx.symm hty.symm h3
    have hD₁v := valid_reachable p (by omega) hC hCD₁
    obtain ⟨D₂, hD₁D₂, hD₂x, hD₂y, hD₂o⟩ :=
      sweep hp hn hR hD hxy _ D₁ rfl hD₁v hD₁x hD₁y
    have h2 : PReach p (D₂ x, D₂ y) (settled 1 1, settled 2 0) := by
      rw [hD₂x, hD₂y]; exact preach_LL hp hn hD
    obtain ⟨D₃, hD₂D₃, hD₃x, hD₃y, hD₃o⟩ := PairReach.lift (P := protocol p) hxy h2
    obtain ⟨E, hD₃E, hE⟩ := reach_ranked_of_12 hp hA hn hxy hD₃x hD₃y
      (fun z hzx hzy => by rw [hD₃o z hzx hzy]; exact hD₂o z hzx hzy)
    exact ⟨E, hCD₁.trans (hD₁D₂.trans (hD₂D₃.trans hD₃E)), hE⟩
  · push Not at hd
    have h2 : PReach p (C x, C y) (settled 1 1, settled 2 0) := by
      rw [hx, hy]; exact preach_trig_trig hp hn hR hD1
    obtain ⟨D₁, hCD₁, hD₁x, hD₁y, hD₁o⟩ := PairReach.lift (P := protocol p) hxy h2
    obtain ⟨E, hD₁E, hE⟩ := reach_ranked_of_12 hp hA hn hxy hD₁x hD₁y
      (fun z hzx hzy => by rw [hD₁o z hzx hzy]; exact hd z hzx hzy)
    exact ⟨E, hCD₁.trans hD₁E, hE⟩

/-- **Correctness of `Optimal-Silent-SSR` with the fixed guard (Theorem 4.3, reachability
part).** For `n ≥ 2` agents, `Rmax ≥ 2` and `Dmax ≥ 2` (the paper's `Rmax = Θ(log n)` and
`Dmax = Θ(n)` satisfy this) and any `Emax`, from every valid configuration a correctly ranked
configuration is reachable. -/
theorem fixed_reachable_ranked (hA : Fintype.card A = p.n) (hn : 2 ≤ p.n)
    (hp : p.fixed = true) (hR : 2 ≤ p.Rmax) (hD : 2 ≤ p.Dmax)
    (C : Config A St) (hC : ∀ a, Valid p (C a)) :
    ∃ D, (protocol p).Reachable C D ∧ Ranked p D := by
  have hA2 : 1 < Fintype.card A := by omega
  obtain ⟨D₁, hCD₁, hD₁⟩ := phase0 hD hA2 _ C rfl
  have hD₁v := valid_reachable p (by omega) hC hCD₁
  rcases hD₁ with ⟨x, y, hxy, hx, hy⟩ | hcomp
  · obtain ⟨E, hD₁E, hE⟩ := reach_ranked_of_trig hp hA hn hR hD hD₁v hxy hx hy
    exact ⟨E, hCD₁.trans hD₁E, hE⟩
  · obtain ⟨D₂, hD₁D₂, hD₂⟩ := phase1 hp hn hA2 hD₁v hcomp
    rcases hD₂ with hR' | ⟨x, y, hxy, hx, hy⟩
    · exact ⟨D₂, hCD₁.trans hD₁D₂, hR'⟩
    · have hD₂v := valid_reachable p (by omega) hD₁v hD₁D₂
      obtain ⟨E, hD₂E, hE⟩ := reach_ranked_of_trig hp hA hn hR hD hD₂v hxy hx hy
      exact ⟨E, hCD₁.trans (hD₁D₂.trans hD₂E), hE⟩

/-- **Self-stabilization (reachability / "probability 1" sense).** From every valid
configuration, a configuration is reachable that is correctly ranked and silent: every
configuration reachable from it equals it (so it is stably ranked). -/
theorem fixed_selfStabilizes (hA : Fintype.card A = p.n) (hn : 2 ≤ p.n)
    (hp : p.fixed = true) (hR : 2 ≤ p.Rmax) (hD : 2 ≤ p.Dmax)
    (C : Config A St) (hC : ∀ a, Valid p (C a)) :
    ∃ D, (protocol p).Reachable C D ∧ Ranked p D ∧
      ∀ D', (protocol p).Reachable D D' → D' = D ∧ Ranked p D' := by
  obtain ⟨D, hCD, hD'⟩ := fixed_reachable_ranked hA hn hp hR hD C hC
  refine ⟨D, hCD, hD', fun D' h => ?_⟩
  have := hD'.reachable p h
  exact ⟨this, this ▸ hD'⟩

end Config

end TimeOptimalSSLE.OptimalSilent
