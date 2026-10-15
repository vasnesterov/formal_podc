import Papers.PODC2026.CanonicalRoundByzantine.Cover

/-!
# Theorems 1 and 7, Corollaries 6 and 8 of [AFW26]

For `3f < n ≤ 5f` (in fact for all `2f ≤ n ≤ 5f`, `f ≥ 1`):

* `theorem1`: every (randomized) canonical-round algorithm that safely solves a nontrivial
  convergence problem has, for every `K`, an admissible adversary and inputs with expected round
  complexity `> K`; in fact the round complexity exceeds `K` for **every** tape (`thm1_core`).
* `corollary6`: the deterministic version (worst-case round complexity unbounded).
* `theorem7`: for communication-closed algorithms there is one admissible adversary under which,
  for every tape, some correct process never decides (so the probability of termination is `0`).
* `corollary8`: no communication-closed canonical-round algorithm solves a nontrivial convergence
  problem (with termination in all admissible executions).

The adversary of `α₂` is a clean schedule (`schedule`) whose Byzantine processes (`E`) compute their
messages from the current configuration: they read the random numbers drawn so far by the correct
processes from their histories (`tapeOf`) and simulate the cover (`bm₂`). The executions `α₀`, `α₁`
are clean schedules with adversaries depending on the tape of `α₂` (this is allowed: safety must hold
for every adversary and every tape).
-/

namespace Podc2026.CanonicalRound

open Cslib.Byzantine.CanonicalRounds Finset

variable {n : ℕ} {V R M O : Type*}

/-! ### Reading the tape from a configuration -/

open Classical in
/-- The random numbers drawn so far, read from the histories (`r₀` if not drawn yet). -/
noncomputable def tapeOf (r₀ : R) (c : Config n R M) : Tape n R := fun X j =>
  if h : ∃ x, ∃ h : Log n R M, h ++ [Entry.draw x] <+: c.log X ∧ rnd h + 1 = j then h.choose
  else r₀

theorem tapeOf_eq {r₀ : R} {c : Config n R M} {ρ : Tape n R} {X : Fin n}
    (hX : CanonAlg.DrawsOK (ρ X) (c.log X)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ rnd (c.log X)) :
    tapeOf r₀ c X j = ρ X j := by
  have hex : ∃ x, ∃ h : Log n R M, h ++ [Entry.draw x] <+: c.log X ∧ rnd h + 1 = j := by
    obtain ⟨h, x, hh, hr⟩ := exists_draw_prefix (l := c.log X) (j := j - 1) (by omega)
    exact ⟨x, h, hh, by omega⟩
  simp only [tapeOf, hex, dif_pos]
  obtain ⟨h, hh, hr⟩ := hex.choose_spec
  rw [hX h _ hh, hr]

/-! ### Decisions -/

namespace Decisions

variable (alg : CanonAlg n V R M O)

theorem decision_mono {p : Fin n} {v : V} {l l' : Log n R M} (h : l <+: l') {o : O}
    (ho : alg.decision p v l = some o) : alg.decision p v l' = some o := by
  obtain ⟨t, rfl⟩ := h
  unfold CanonAlg.decision at *
  rw [List.inits_append, List.findSome?_append, ho]; rfl

/-- If `p` decides in a round `≤ K` along some history comparable with `L` and `L` already has
round `K + 1`, then the decision is visible in `L`. -/
theorem decision_isSome_of_decidesBy {p : Fin n} {v : V} {K : ℕ} {l L l' : Log n R M}
    (hd : alg.DecidesBy p v K l) (hl : l <+: l') (hL : L <+: l') (hr : K + 1 ≤ rnd L) :
    (alg.decision p v L).isSome := by
  obtain ⟨h, hh, hrh, hs⟩ := hd
  rw [List.mem_inits] at hh
  have hhL : h <+: L := by
    rcases List.prefix_of_prefix_length_le (hh.trans hl) hL (le_total _ _ |>.elim id fun h' => by
      exfalso
      have := List.prefix_of_prefix_length_le hL (hh.trans hl) h'
      have := rnd_mono this; omega) with h1
    exact h1
  exact List.findSome?_isSome_iff.2 ⟨h, List.mem_inits _ _ |>.2 hhL, hs⟩

theorem ccView_idem (l : Log n R M) : ccView (ccView l) = ccView l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [ccView_append_singleton]
    cases e with
    | draw x => simp only [ccStep]; rw [ccView_append_singleton, ih]; rfl
    | recv q r m =>
      simp only [ccStep]
      split_ifs with h
      · rw [ccView_append_singleton, ih]; simp only [ccStep]; rw [if_pos h]
      · exact ih

theorem inits_concat {α : Type*} (l : List α) (e : α) : (l ++ [e]).inits = l.inits ++ [l ++ [e]] := by
  simp [List.inits_append]

theorem findSome_inits_ccView {β : Type*} (g : Log n R M → Option β) (l : Log n R M) :
    l.inits.findSome? (fun h => g (ccView h)) = (ccView l).inits.findSome? g := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [inits_concat, List.findSome?_append, ih, ccView_append_singleton]
    simp only [List.findSome?_cons, List.findSome?_nil, ccView_append_singleton]
    cases e with
    | draw x =>
      simp only [ccStep, inits_concat, List.findSome?_append, List.findSome?_cons,
        List.findSome?_nil]
    | recv q r m =>
      simp only [ccStep]
      split_ifs with h
      · simp only [inits_concat, List.findSome?_append, List.findSome?_cons, List.findSome?_nil]
      · rcases hf : (ccView l).inits.findSome? g with _ | y
        · have hg : g (ccView l) = none := by
            rw [List.findSome?_eq_none_iff] at hf
            exact hf _ (List.mem_inits _ _ |>.2 (List.prefix_refl _))
          simp [hg]
        · rfl

/-- For a communication-closed algorithm, the decision only depends on the communication-closed
view of the history. -/
theorem decision_ccView (hcc : alg.CommClosed) (p : Fin n) (v : V) (l : Log n R M) :
    alg.decision p v l = alg.decision p v (ccView l) := by
  unfold CanonAlg.decision
  rw [← findSome_inits_ccView]
  congr 1; funext h
  exact (hcc p v h (ccView h) (ccView_idem h).symm).2

end Decisions

/-! ### The three adversaries -/

section Adversaries

variable (alg : CanonAlg n V R M O) {f : ℕ} (G : Groups n f) (x₀ x₁ : V) (r₀ : R)

/-- Byzantine messages of `α₂` computed from the configuration (full-information adversary). -/
noncomputable def bm₂ (s : ℕ) (c : Config n R M) (q p : Fin n) : M :=
  byz₂ alg G x₀ x₁ r₀ (tapeOf r₀ c) s q p

theorem bmOK₂ (ρ : Tape n R) :
    BmOK (G.set 4) (fun p => G.hb (G.side p)) (byz₂ alg G x₀ x₁ r₀ ρ) ρ (bm₂ alg G x₀ x₁ r₀) := by
  intro s c hs1 hc q _ p _ _
  simp only [bm₂, byz₂]
  rw [cov_congr alg G x₀ x₁ r₀ (s - 1) (fun X hX j h1 h2 => by
    have := hc X (by simpa using hX)
    exact tapeOf_eq this.2 h1 (by omega))]

/-- The adversary of `α₂`: Byzantine `E`, late messages from stage `lateFrom` on. -/
noncomputable def adv₂ (lateFrom : ℕ) : Adversary n R M :=
  schedule (G.set 4) (fun p => G.hb (G.side p)) (bm₂ alg G x₀ x₁ r₀) lateFrom

/-- The adversary of `α₀` (for the tape `ρ` of `α₂`): Byzantine `A` replaying `α₂`. -/
noncomputable def adv₀ (ρ : Tape n R) (lateFrom : ℕ) : Adversary n R M :=
  schedule (G.set 0) (fun _ => G.hb false) (fun s _ => byz₀ alg G x₀ x₁ r₀ ρ s) lateFrom

/-- The adversary of `α₁`: Byzantine `C` replaying `α₂`. -/
noncomputable def adv₁ (ρ : Tape n R) (lateFrom : ℕ) : Adversary n R M :=
  schedule (G.set 2) (fun _ => G.hb true) (fun s _ => byz₁ alg G x₀ x₁ r₀ ρ s) lateFrom

variable {alg G x₀ x₁ r₀}

theorem admissible₂ (hf : f < n) {lateFrom : ℕ} (hl : 1 ≤ lateFrom) (I : Fin n → V) :
    alg.Admissible f I (adv₂ alg G x₀ x₁ r₀ lateFrom) :=
  schedule_admissible alg f I _ _ _ lateFrom hf hl G.cardE (fun p _ => G.card_hb _)
    (byz₂ alg G x₀ x₁ r₀) (bmOK₂ alg G x₀ x₁ r₀)

theorem admissible₀ (hf : f < n) {lateFrom : ℕ} (hl : 1 ≤ lateFrom) (I : Fin n → V)
    (ρ : Tape n R) : alg.Admissible f I (adv₀ alg G x₀ x₁ r₀ ρ lateFrom) :=
  schedule_admissible alg f I _ _ _ lateFrom hf hl G.cardA (fun p _ => G.card_hb _)
    (fun _ => byz₀ alg G x₀ x₁ r₀ ρ) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

theorem admissible₁ (hf : f < n) {lateFrom : ℕ} (hl : 1 ≤ lateFrom) (I : Fin n → V)
    (ρ : Tape n R) : alg.Admissible f I (adv₁ alg G x₀ x₁ r₀ ρ lateFrom) :=
  schedule_admissible alg f I _ _ _ lateFrom hf hl G.cardC (fun p _ => G.card_hb _)
    (fun _ => byz₁ alg G x₀ x₁ r₀ ρ) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/-! ### Histories at the end of stage `K` -/

variable {vw : Log n R M → Log n R M}

theorem log₂ (hf : f < n) {lateFrom : ℕ} (hl : 1 ≤ lateFrom) (hv : ViewOK alg vw) (K : ℕ)
    (hdrop : lateFrom ≤ K → ∀ l q r' m, r' < rnd l → vw (l ++ [.recv q r' m]) = vw l)
    (ρ : Tape n R) (p : Fin n) (hp : G.grp p ≠ 4) :
    vw ((alg.exec f (I₂ G x₀ x₁) ρ (adv₂ alg G x₀ x₁ r₀ lateFrom) ((K + 1) * stageLen n)).log p)
      = cov alg G x₀ x₁ r₀ ρ K (G.side p) p ∧
    rnd ((alg.exec f (I₂ G x₀ x₁) ρ (adv₂ alg G x₀ x₁ r₀ lateFrom) ((K + 1) * stageLen n)).log p)
      = K + 1 := by
  have := stageInv_exec alg f (I₂ G x₀ x₁) (G.set 4) (fun p => G.hb (G.side p)) (byz₂ alg G x₀ x₁ r₀ ρ) ρ lateFrom
    (bm₂ alg G x₀ x₁ r₀) hf hl hv (fun p _ => G.card_hb _) (bmOK₂ alg G x₀ x₁ r₀ ρ) K hdrop K le_rfl
  have hp' : p ∉ G.set 4 := by simpa using hp
  exact ⟨(this.view p hp').trans (clean₂_eq alg G x₀ x₁ r₀ ρ K p hp), this.round p hp'⟩

theorem log₀ (hf : f < n) {lateFrom : ℕ} (hl : 1 ≤ lateFrom) (hv : ViewOK alg vw) (K : ℕ)
    (hdrop : lateFrom ≤ K → ∀ l q r' m, r' < rnd l → vw (l ++ [.recv q r' m]) = vw l)
    (ρ : Tape n R) (p : Fin n) (hp : G.grp p = 1 ∨ G.grp p = 2 ∨ G.grp p = 4) :
    vw ((alg.exec f (fun _ => x₀) (ρE G r₀ ρ) (adv₀ alg G x₀ x₁ r₀ ρ lateFrom)
      ((K + 1) * stageLen n)).log p) = cov alg G x₀ x₁ r₀ ρ K false p := by
  have := stageInv_exec alg f (fun _ => x₀) (G.set 0) (fun _ => G.hb false) (byz₀ alg G x₀ x₁ r₀ ρ) (ρE G r₀ ρ)
    lateFrom (fun s _ => byz₀ alg G x₀ x₁ r₀ ρ s) hf hl hv (fun p _ => G.card_hb _)
    (fun _ _ _ _ _ _ _ _ _ => rfl) K hdrop K le_rfl
  have hp' : p ∉ G.set 0 := by simp; omega
  exact (this.view p hp').trans (clean₀_eq alg G x₀ x₁ r₀ ρ K p hp)

theorem log₁ (hf : f < n) {lateFrom : ℕ} (hl : 1 ≤ lateFrom) (hv : ViewOK alg vw) (K : ℕ)
    (hdrop : lateFrom ≤ K → ∀ l q r' m, r' < rnd l → vw (l ++ [.recv q r' m]) = vw l)
    (ρ : Tape n R) (p : Fin n) (hp : G.grp p = 0 ∨ G.grp p = 3 ∨ G.grp p = 4) :
    vw ((alg.exec f (fun _ => x₁) (ρE G r₀ ρ) (adv₁ alg G x₀ x₁ r₀ ρ lateFrom)
      ((K + 1) * stageLen n)).log p) = cov alg G x₀ x₁ r₀ ρ K true p := by
  have := stageInv_exec alg f (fun _ => x₁) (G.set 2) (fun _ => G.hb true) (byz₁ alg G x₀ x₁ r₀ ρ) (ρE G r₀ ρ)
    lateFrom (fun s _ => byz₁ alg G x₀ x₁ r₀ ρ s) hf hl hv (fun p _ => G.card_hb _)
    (fun _ _ _ _ _ _ _ _ _ => rfl) K hdrop K le_rfl
  have hp' : p ∉ G.set 2 := by simp; omega
  exact (this.view p hp').trans (clean₁_eq alg G x₀ x₁ r₀ ρ K p hp)

end Adversaries

/-! ### The indistinguishability argument -/

section Main

variable (alg : CanonAlg n V R M O) {f : ℕ}

/-- The heart of Theorems 1 and 7: if in `α₂` (at the end of stage `K`) a process of `B` and a
process of `D` have decided, then safety is violated: by indistinguishability the `B`-process
decides as in `α₀`, where validity forces `d₀`; the `D`-process decides as in `α₁`, where validity
forces `d₁`; this violates agreement in `α₂`. -/
theorem key_contra {vw : Log n R M → Log n R M} (G : Groups n f) (r₀ : R) {x₀ x₁ : V} {d₀ d₁ : O}
    (hsafe : alg.Safe f (ncSpec x₀ x₁ d₀ d₁)) (hf : f < n) {lateFrom : ℕ} (hl : 1 ≤ lateFrom)
    (hv : ViewOK alg vw) (hdec : ∀ p v l, alg.decision p v l = alg.decision p v (vw l)) (K : ℕ)
    (hdrop : lateFrom ≤ K → ∀ l q r' m, r' < rnd l → vw (l ++ [.recv q r' m]) = vw l)
    (ρ : Tape n R) {b d : Fin n} (hb : G.grp b = 1) (hd : G.grp d = 3)
    (hsb : (alg.decision b (I₂ G x₀ x₁ b) ((alg.exec f (I₂ G x₀ x₁) ρ
      (adv₂ alg G x₀ x₁ r₀ lateFrom) ((K + 1) * stageLen n)).log b)).isSome)
    (hsd : (alg.decision d (I₂ G x₀ x₁ d) ((alg.exec f (I₂ G x₀ x₁) ρ
      (adv₂ alg G x₀ x₁ r₀ lateFrom) ((K + 1) * stageLen n)).log d)).isSome) : False := by
  have hsideb : G.side b = false := by simp [Groups.side, hb]
  have hsided : G.side d = true := by simp [Groups.side, hd]
  obtain ⟨ob, hob⟩ := Option.isSome_iff_exists.1 hsb
  obtain ⟨od, hod⟩ := Option.isSome_iff_exists.1 hsd
  have hb2 := (log₂ (x₀ := x₀) (x₁ := x₁) (r₀ := r₀) (alg := alg) (G := G) hf hl hv K hdrop ρ b
    (by rw [hb]; decide)).1
  have hd2 := (log₂ (x₀ := x₀) (x₁ := x₁) (r₀ := r₀) (alg := alg) (G := G) hf hl hv K hdrop ρ d
    (by rw [hd]; decide)).1
  rw [hsideb] at hb2; rw [hsided] at hd2
  -- `b` in `α₀`
  have hb0 := log₀ (x₀ := x₀) (x₁ := x₁) (alg := alg) (G := G) (r₀ := r₀) hf hl hv K hdrop ρ b (Or.inl hb)
  have hob0 : alg.decision b x₀ ((alg.exec f (fun _ => x₀) (ρE G r₀ ρ)
      (adv₀ alg G x₀ x₁ r₀ ρ lateFrom) ((K + 1) * stageLen n)).log b) = some ob := by
    rw [hdec, hb0, ← hb2, ← hdec, ← hob]; simp [I₂, xs, hsideb]
  have v0 := (hsafe (fun _ => x₀) (adv₀ alg G x₀ x₁ r₀ ρ lateFrom) (admissible₀ hf hl _ ρ) (ρE G r₀ ρ)
    ((K + 1) * stageLen n)).2.1 b
    (by simp [adv₀, schedule, hb]) (by beta_reduce; rw [hob0]; simp) (fun _ _ => rfl)
  beta_reduce at v0; rw [hob0] at v0
  -- `d` in `α₁`
  have hd1 := log₁ (x₀ := x₀) (x₁ := x₁) (alg := alg) (G := G) (r₀ := r₀) hf hl hv K hdrop ρ d
    (Or.inr (Or.inl hd))
  have hod1 : alg.decision d x₁ ((alg.exec f (fun _ => x₁) (ρE G r₀ ρ)
      (adv₁ alg G x₀ x₁ r₀ ρ lateFrom) ((K + 1) * stageLen n)).log d) = some od := by
    rw [hdec, hd1, ← hd2, ← hdec, ← hod]; simp [I₂, xs, hsided]
  have v1 := (hsafe (fun _ => x₁) (adv₁ alg G x₀ x₁ r₀ ρ lateFrom) (admissible₁ hf hl _ ρ) (ρE G r₀ ρ)
    ((K + 1) * stageLen n)).2.2 d
    (by simp [adv₁, schedule, hd]) (by beta_reduce; rw [hod1]; simp) (fun _ _ => rfl)
  beta_reduce at v1; rw [hod1] at v1
  -- agreement in `α₂`
  have ag := (hsafe (I₂ G x₀ x₁) (adv₂ alg G x₀ x₁ r₀ lateFrom) (admissible₂ hf hl _) ρ
    ((K + 1) * stageLen n)).1 b (by simp [adv₂, schedule, hb])
    d (by simp [adv₂, schedule, hd])
  exact ag (by beta_reduce; rw [hob, v0]) (by beta_reduce; rw [hod, v1])

theorem exists_B_D (G : Groups n f) (hf0 : 0 < f) : ∃ b d, G.grp b = 1 ∧ G.grp d = 3 := by
  obtain ⟨b, hb⟩ : (G.set 1).Nonempty := by
    rw [← Finset.card_pos]; unfold Groups.set; rw [G.cardB]; exact hf0
  obtain ⟨d, hd⟩ : (G.set 3).Nonempty := by
    rw [← Finset.card_pos]; unfold Groups.set; rw [G.cardD]; exact hf0
  exact ⟨b, d, (G.mem_set).1 hb, (G.mem_set).1 hd⟩

theorem decidesBy_mono {p : Fin n} {v : V} {r r' : ℕ} {l : Log n R M} (h : r ≤ r')
    (hd : alg.DecidesBy p v r l) : alg.DecidesBy p v r' l := by
  obtain ⟨h', hh, hr, hs⟩ := hd; exact ⟨h', hh, by omega, hs⟩

/-- **Theorem 1 / Corollary 6 of [AFW26], core statement.** For `2f ≤ n ≤ 5f`, `f ≥ 1`: if a
canonical-round algorithm satisfies the safety properties of a nontrivial convergence problem, then
for every `K` there are inputs and an admissible adversary under which, **for every tape**, some
correct process does not decide in or before its round `K`. -/
theorem thm1_core [Nonempty R] (hf0 : 0 < f) (h2f : 2 * f ≤ n) (h5f : n ≤ 5 * f) {x₀ x₁ : V}
    {d₀ d₁ : O} (hsafe : alg.Safe f (ncSpec x₀ x₁ d₀ d₁)) (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, ¬ alg.AllDecideBy f I ρ A K := by
  obtain ⟨G⟩ := Groups.exists f h2f h5f
  have hf : f < n := by omega
  let r₀ : R := Classical.arbitrary R
  refine ⟨I₂ G x₀ x₁, adv₂ alg G x₀ x₁ r₀ (K + 1), admissible₂ hf (by omega) _, fun ρ hall => ?_⟩
  obtain ⟨b, d, hb, hd⟩ := exists_B_D G hf0
  have hdrop : K + 1 ≤ K → ∀ (l : Log n R M) q r' m, r' < rnd l → id (l ++ [.recv q r' m]) = id l :=
    fun h => absurd h (by omega)
  have hs : ∀ p, G.grp p ≠ 4 → (alg.decision p (I₂ G x₀ x₁ p) ((alg.exec f (I₂ G x₀ x₁) ρ
      (adv₂ alg G x₀ x₁ r₀ (K + 1)) ((K + 1) * stageLen n)).log p)).isSome := by
    intro p hp
    obtain ⟨k, hk⟩ := hall p (by simpa [adv₂, schedule] using hp)
    have hle := fun k' (h : k' ≤ max k ((K + 1) * stageLen n)) =>
      (alg.le_exec f (I₂ G x₀ x₁) ρ (adv₂ alg G x₀ x₁ r₀ (K + 1)) h).log p
    exact Decisions.decision_isSome_of_decidesBy alg hk (hle k (le_max_left _ _))
      (hle _ (le_max_right _ _))
      (by rw [(log₂ hf (by omega) (viewOK_id alg) K hdrop ρ p hp).2])
  exact key_contra alg G r₀ hsafe hf (by omega) (viewOK_id alg) (fun _ _ _ => rfl) K hdrop ρ hb hd
    (hs b (by rw [hb]; decide)) (hs d (by rw [hd]; decide))

/-- **Theorem 7 / Corollary 8 of [AFW26], core statement.** For `2f ≤ n ≤ 5f`, `f ≥ 1`: if a
communication-closed canonical-round algorithm satisfies the safety properties of a nontrivial
convergence problem, there are inputs and an admissible adversary under which, **for every
tape**, some correct process never decides. -/
theorem thm7_core [Nonempty R] (hcc : alg.CommClosed) (hf0 : 0 < f) (h2f : 2 * f ≤ n)
    (h5f : n ≤ 5 * f) {x₀ x₁ : V} {d₀ d₁ : O} (hsafe : alg.Safe f (ncSpec x₀ x₁ d₀ d₁)) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, ¬ alg.AllDecide f I ρ A := by
  obtain ⟨G⟩ := Groups.exists f h2f h5f
  have hf : f < n := by omega
  let r₀ : R := Classical.arbitrary R
  refine ⟨I₂ G x₀ x₁, adv₂ alg G x₀ x₁ r₀ 1, admissible₂ hf le_rfl _, fun ρ hall => ?_⟩
  obtain ⟨b, d, hb, hd⟩ := exists_B_D G hf0
  obtain ⟨kb, hkb⟩ := hall b (by simp [adv₂, schedule, hb])
  obtain ⟨kd, hkd⟩ := hall d (by simp [adv₂, schedule, hd])
  set K := kb + kd
  have hS : 1 ≤ stageLen n := by unfold stageLen; nlinarith
  have hT : kb + kd ≤ (K + 1) * stageLen n :=
    le_trans (by omega : kb + kd ≤ K + 1) (Nat.le_mul_of_pos_right _ hS)
  have hpers : ∀ p k, k ≤ (K + 1) * stageLen n →
      (alg.decision p (I₂ G x₀ x₁ p) ((alg.exec f (I₂ G x₀ x₁) ρ
        (adv₂ alg G x₀ x₁ r₀ 1) k).log p)).isSome →
      (alg.decision p (I₂ G x₀ x₁ p) ((alg.exec f (I₂ G x₀ x₁) ρ
        (adv₂ alg G x₀ x₁ r₀ 1) ((K + 1) * stageLen n)).log p)).isSome := by
    intro p k hk hs
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hs
    rw [Decisions.decision_mono alg
      ((alg.le_exec f (I₂ G x₀ x₁) ρ (adv₂ alg G x₀ x₁ r₀ 1) hk).log p) ho]; rfl
  exact key_contra alg G r₀ hsafe hf le_rfl (viewOK_cc alg hcc)
    (Decisions.decision_ccView alg hcc) K (fun _ => ccView_drop) ρ hb hd
    (hpers b kb (by omega) hkb) (hpers d kd (by omega) hkd)

end Main

end Podc2026.CanonicalRound
