import Papers.PODC2021.FastByzantineConsensus.Protocol

/-!
# Reachable-state invariants of the fast Byzantine consensus protocol

Invariants of the transition system of `Protocol.lean` (Kuznetsov–Tonkikh–Zhang, PODC 2021)
about the tokens signed by correct processes. They formalize the facts that the paper uses
implicitly ("a correct process acknowledges at most one proposal per view", "the vote of a correct
process reports its latest acknowledged proposal", ...).
-/

namespace FastByzantineConsensus.Protocol

open Finset Classical

variable {P V : Type*} [Fintype P] [DecidableEq P]

section Mono

variable {E E' : Set (Tok P V)}

omit [DecidableEq P] in
theorem ackers_mono (h : E ⊆ E') (x : V) (v : ℕ) : ackers E x v ⊆ ackers E' x v := by
  intro p hp
  simp only [ackers, mem_filter, mem_univ, true_and] at hp ⊢
  exact h hp

omit [DecidableEq P] in
theorem committers_mono (h : E ⊆ E') (x : V) (v : ℕ) :
    committers E x v ⊆ committers E' x v := by
  intro p hp
  simp only [committers, mem_filter, mem_univ, true_and] at hp ⊢
  exact h hp

variable (pr : Params P)

omit [DecidableEq P] in
theorem Certified.mono (h : E ⊆ E') {x : V} {v : ℕ} (hc : Certified pr E x v) :
    Certified pr E' x v :=
  Cslib.Byzantine.Certified.mono hc (fun _ hp => h hp) le_rfl

omit [DecidableEq P] in
theorem HasCC.mono (h : E ⊆ E') {x : V} {v : ℕ} (hc : HasCC pr E x v) : HasCC pr E' x v :=
  Cslib.Byzantine.Certified.mono hc (fun _ hp => h hp) le_rfl

omit [DecidableEq P] in
theorem ValidBallot.mono (h : E ⊆ E') {v : ℕ} {b : Option (V × ℕ)}
    (hb : ValidBallot pr E v b) : ValidBallot pr E' v b := by
  rcases b with _ | ⟨x, u⟩
  · trivial
  · obtain ⟨h1, h2, h3⟩ := hb
    exact ⟨h1, h h2, h3.imp id (Certified.mono pr h)⟩

omit [DecidableEq P] in
theorem ValidCC.mono (h : E ⊆ E') {v : ℕ} {c : Option (V × ℕ)}
    (hc : ValidCC pr E v c) : ValidCC pr E' v c := by
  rcases c with _ | ⟨x, u⟩
  · trivial
  · exact ⟨hc.1, HasCC.mono pr h hc.2⟩

omit [DecidableEq P] in
theorem ValidVotes.mono (h : E ⊆ E') {v : ℕ} {S : Finset P} {bal cc : P → Option (V × ℕ)}
    (hS : ValidVotes pr E v S bal cc) : ValidVotes pr E' v S bal cc :=
  ⟨hS.1, fun s hs => ⟨h (hS.2 s hs).1, ValidBallot.mono pr h (hS.2 s hs).2.1,
    ValidCC.mono pr h (hS.2 s hs).2.2⟩⟩

end Mono

variable (pr : Params P) (B : Finset P)

/-- Invariants about the tokens in `E` signed by correct processes (no reference to local
states). These are all that the safety proof uses. -/
structure TokInv (E : Set (Tok P V)) : Prop where
  /-- The proposal part of a correct vote is a proposal the voter acknowledged. -/
  vote_bal : ∀ q ∉ B, ∀ v b c x u, Tok.vote q v b c ∈ E → b = some (x, u) → Tok.ack q x u ∈ E
  /-- The proposal part of a correct vote for view `v` is at least as recent as every
  acknowledgement of the voter in a view `< v`. -/
  vote_ack : ∀ q ∉ B, ∀ v b c x u, Tok.vote q v b c ∈ E → Tok.ack q x u ∈ E → u < v →
    ∃ x' u', b = some (x', u') ∧ u ≤ u' ∧ (u' = u → x' = x)
  /-- The commit-certificate part of a correct vote for view `v` is a valid certificate at
  least as recent as every `Commit` of the voter in a view `< v`. -/
  vote_commit : ∀ q ∉ B, ∀ v b c x u, Tok.vote q v b c ∈ E → Tok.commit q x u ∈ E → u < v →
    ∃ x' u', c = some (x', u') ∧ u ≤ u' ∧ HasCC pr E x' u'
  /-- A correct process acknowledges at most one value per view. -/
  ack_uniq : ∀ q ∉ B, ∀ x y u, Tok.ack q x u ∈ E → Tok.ack q y u ∈ E → x = y
  /-- A correct leader proposes at most one value per view. -/
  propose_uniq : ∀ q ∉ B, ∀ x y u, Tok.propose q x u ∈ E → Tok.propose q y u ∈ E → x = y
  /-- A correct process acknowledges only valid proposals. -/
  ack_valid : ∀ q ∉ B, ∀ x u, Tok.ack q x u ∈ E →
    Tok.propose (pr.leader u) x u ∈ E ∧ (u = 0 ∨ Certified pr E x u)
  /-- A correct process signs `CertAck(x, v)` only after verifying a valid vote set on which the
  selection algorithm may output `x`. -/
  certAck_valid : ∀ q ∉ B, ∀ x v, Tok.certAck q x v ∈ E →
    ∃ S bal cc, ValidVotes pr E v S bal cc ∧ Selects pr v S bal cc x
  /-- A correct process sends `Commit(x, u)` only with a commit certificate for `(x, u)`. -/
  commit_valid : ∀ q ∉ B, ∀ x u, Tok.commit q x u ∈ E → HasCC pr E x u

/-- The inductive invariant: `TokInv` plus the relation between the local states of correct
processes and their tokens. -/
structure Inv (s : State P V) : Prop extends TokInv pr B s.E where
  ack_loc : ∀ q ∉ B, ∀ x u, Tok.ack q x u ∈ s.E → u ≤ (s.loc q).view ∧
    ∃ x' u', (s.loc q).ballot = some (x', u') ∧ u ≤ u' ∧ (u' = u → x' = x)
  ballot_loc : ∀ q ∉ B, ∀ x u, (s.loc q).ballot = some (x, u) →
    Tok.ack q x u ∈ s.E ∧ u ≤ (s.loc q).view
  cc_loc : ∀ q ∉ B, ∀ x u, (s.loc q).cc = some (x, u) → HasCC pr s.E x u ∧ u ≤ (s.loc q).view
  commit_loc : ∀ q ∉ B, ∀ x u, Tok.commit q x u ∈ s.E → u ≤ (s.loc q).view ∧
    ∃ x' u', (s.loc q).cc = some (x', u') ∧ u ≤ u'
  vote_view : ∀ q ∉ B, ∀ v b c, Tok.vote q v b c ∈ s.E → v ≤ (s.loc q).view

theorem Inv.init : Inv pr B (init : State P V) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Protocol.init]

variable {pr B}

theorem mem_of_mem_insert_ne {α : Type*} {a m : α} {E : Set α} (h : a ∈ insert m E) (hne : a ≠ m) :
    a ∈ E :=
  (Set.mem_insert_iff.1 h).resolve_left hne

/-- Steps that emit a token which is not an `ack`, `commit` or `vote` of a correct process and
do not change local states (`propose`, `certAck`, Byzantine steps) preserve `Inv`. -/
theorem Inv.insert_of {s : State P V} (hI : Inv pr B s) (m : Tok P V)
    (hack : ∀ r ∉ B, ∀ x u, Tok.ack r x u ≠ m) (hcom : ∀ r ∉ B, ∀ x u, Tok.commit r x u ≠ m)
    (hvote : ∀ r ∉ B, ∀ v b c, Tok.vote r v b c ≠ m)
    (hprop : ∀ r ∉ B, ∀ x u, Tok.propose r x u = m → ∀ y, Tok.propose r y u ∉ s.E)
    (hcert : ∀ r ∉ B, ∀ x v, Tok.certAck r x v = m →
      ∃ S bal cc, ValidVotes pr s.E v S bal cc ∧ Selects pr v S bal cc x) :
    Inv pr B ⟨insert m s.E, s.loc⟩ := by
  have hsub : s.E ⊆ insert m s.E := Set.subset_insert _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro r hr v b c x u hv hbx
    exact hsub (hI.vote_bal r hr v b c x u (mem_of_mem_insert_ne hv (hvote r hr v b c)) hbx)
  · intro r hr v b c x u hv hax hu
    exact hI.vote_ack r hr v b c x u (mem_of_mem_insert_ne hv (hvote r hr v b c))
      (mem_of_mem_insert_ne hax (hack r hr x u)) hu
  · intro r hr v b c x u hv hcx hu
    obtain ⟨x', u', h1, h2, h3⟩ := hI.vote_commit r hr v b c x u
      (mem_of_mem_insert_ne hv (hvote r hr v b c)) (mem_of_mem_insert_ne hcx (hcom r hr x u)) hu
    exact ⟨x', u', h1, h2, HasCC.mono pr hsub h3⟩
  · intro r hr x y u h1 h2
    exact hI.ack_uniq r hr x y u (mem_of_mem_insert_ne h1 (hack r hr x u))
      (mem_of_mem_insert_ne h2 (hack r hr y u))
  · intro r hr x y u h1 h2
    rcases Set.mem_insert_iff.1 h1 with h1 | h1 <;> rcases Set.mem_insert_iff.1 h2 with h2 | h2
    · rw [← h2] at h1; simpa using h1
    · exact absurd h2 (hprop r hr x u h1 y)
    · exact absurd h1 (hprop r hr y u h2 x)
    · exact hI.propose_uniq r hr x y u h1 h2
  · intro r hr x u h
    obtain ⟨h1, h2⟩ := hI.ack_valid r hr x u (mem_of_mem_insert_ne h (hack r hr x u))
    exact ⟨hsub h1, h2.imp id (Certified.mono pr hsub)⟩
  · intro r hr x v h
    rcases Set.mem_insert_iff.1 h with h | h
    · obtain ⟨S, bal, cc, h1, h2⟩ := hcert r hr x v h
      exact ⟨S, bal, cc, ValidVotes.mono pr hsub h1, h2⟩
    · obtain ⟨S, bal, cc, h1, h2⟩ := hI.certAck_valid r hr x v h
      exact ⟨S, bal, cc, ValidVotes.mono pr hsub h1, h2⟩
  · intro r hr x u h
    exact HasCC.mono pr hsub (hI.commit_valid r hr x u (mem_of_mem_insert_ne h (hcom r hr x u)))
  · intro r hr x u h
    exact hI.ack_loc r hr x u (mem_of_mem_insert_ne h (hack r hr x u))
  · intro r hr x u h
    obtain ⟨h1, h2⟩ := hI.ballot_loc r hr x u h
    exact ⟨hsub h1, h2⟩
  · intro r hr x u h
    obtain ⟨h1, h2⟩ := hI.cc_loc r hr x u h
    exact ⟨HasCC.mono pr hsub h1, h2⟩
  · intro r hr x u h
    exact hI.commit_loc r hr x u (mem_of_mem_insert_ne h (hcom r hr x u))
  · intro r hr v b c h
    exact hI.vote_view r hr v b c (mem_of_mem_insert_ne h (hvote r hr v b c))

theorem Inv.enterView {s : State P V} (hI : Inv pr B s) (q : P) (v : ℕ) (hv : (s.loc q).view < v) :
    Inv pr B ⟨insert (Tok.vote q v (s.loc q).ballot (s.loc q).cc) s.E,
        Function.update s.loc q { s.loc q with view := v }⟩ := by
  have hsub : s.E ⊆ insert (Tok.vote q v (s.loc q).ballot (s.loc q).cc) s.E :=
    Set.subset_insert _ _
  have hb : ∀ r, (Function.update s.loc q { s.loc q with view := v } r).ballot =
      (s.loc r).ballot := by
    intro r; by_cases hr : r = q
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  have hc : ∀ r, (Function.update s.loc q { s.loc q with view := v } r).cc = (s.loc r).cc := by
    intro r; by_cases hr : r = q
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  have hvw : ∀ r, (s.loc r).view ≤ (Function.update s.loc q { s.loc q with view := v } r).view := by
    intro r; by_cases hr : r = q
    · subst hr; simp; omega
    · simp [Function.update_of_ne hr]
  have hack : ∀ r x₀ u, Tok.ack r x₀ u ∈ insert (Tok.vote q v (s.loc q).ballot (s.loc q).cc) s.E ↔
      Tok.ack r x₀ u ∈ s.E := by simp
  have hcom : ∀ r x₀ u,
      Tok.commit r x₀ u ∈ insert (Tok.vote q v (s.loc q).ballot (s.loc q).cc) s.E ↔
      Tok.commit r x₀ u ∈ s.E := by simp
  have hprop : ∀ r x₀ u,
      Tok.propose r x₀ u ∈ insert (Tok.vote q v (s.loc q).ballot (s.loc q).cc) s.E ↔
      Tok.propose r x₀ u ∈ s.E := by simp
  have hcert : ∀ r x₀ u,
      Tok.certAck r x₀ u ∈ insert (Tok.vote q v (s.loc q).ballot (s.loc q).cc) s.E ↔
      Tok.certAck r x₀ u ∈ s.E := by simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro r hr v' b c x u hv' hbx
    rw [hack]
    rcases Set.mem_insert_iff.1 hv' with h | h
    · simp only [Tok.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact (hI.ballot_loc r hr x u hbx).1
    · exact hI.vote_bal r hr v' b c x u h hbx
  · intro r hr v' b c x u hv' hax hu
    rw [hack] at hax
    rcases Set.mem_insert_iff.1 hv' with h | h
    · simp only [Tok.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact (hI.ack_loc r hr x u hax).2
    · exact hI.vote_ack r hr v' b c x u h hax hu
  · intro r hr v' b c x u hv' hcx hu
    rw [hcom] at hcx
    rcases Set.mem_insert_iff.1 hv' with h | h
    · simp only [Tok.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨-, x', u', h1, h2⟩ := hI.commit_loc r hr x u hcx
      exact ⟨x', u', h1, h2, HasCC.mono pr hsub (hI.cc_loc r hr x' u' h1).1⟩
    · obtain ⟨x', u', h1, h2, h3⟩ := hI.vote_commit r hr v' b c x u h hcx hu
      exact ⟨x', u', h1, h2, HasCC.mono pr hsub h3⟩
  · intro r hr x y u h1 h2; rw [hack] at h1 h2; exact hI.ack_uniq r hr x y u h1 h2
  · intro r hr x y u h1 h2; rw [hprop] at h1 h2; exact hI.propose_uniq r hr x y u h1 h2
  · intro r hr x u h; rw [hack] at h; rw [hprop]
    obtain ⟨h1, h2⟩ := hI.ack_valid r hr x u h
    exact ⟨h1, h2.imp id (Certified.mono pr hsub)⟩
  · intro r hr x v' h; rw [hcert] at h
    obtain ⟨S, bal, cc, h1, h2⟩ := hI.certAck_valid r hr x v' h
    exact ⟨S, bal, cc, ValidVotes.mono pr hsub h1, h2⟩
  · intro r hr x u h; rw [hcom] at h; exact HasCC.mono pr hsub (hI.commit_valid r hr x u h)
  · intro r hr x u h; rw [hack] at h; rw [hb]
    obtain ⟨h1, h2⟩ := hI.ack_loc r hr x u h
    exact ⟨h1.trans (hvw r), h2⟩
  · intro r hr x u h; rw [hb] at h; rw [hack]
    obtain ⟨h1, h2⟩ := hI.ballot_loc r hr x u h
    exact ⟨h1, h2.trans (hvw r)⟩
  · intro r hr x u h; rw [hc] at h
    obtain ⟨h1, h2⟩ := hI.cc_loc r hr x u h
    exact ⟨HasCC.mono pr hsub h1, h2.trans (hvw r)⟩
  · intro r hr x u h; rw [hcom] at h; rw [hc]
    obtain ⟨h1, h2⟩ := hI.commit_loc r hr x u h
    exact ⟨h1.trans (hvw r), h2⟩
  · intro r hr v' b c h
    rcases Set.mem_insert_iff.1 h with h | h
    · simp only [Tok.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp
    · exact (hI.vote_view r hr v' b c h).trans (hvw r)

theorem Inv.ack {s : State P V} (hI : Inv pr B s) (q : P) (x : V) (hq : q ∉ B)
    (hp : Tok.propose (pr.leader (s.loc q).view) x (s.loc q).view ∈ s.E)
    (hc : (s.loc q).view = 0 ∨ Certified pr s.E x (s.loc q).view)
    (hfirst : ∀ y, Tok.ack q y (s.loc q).view ∉ s.E) :
    Inv pr B ⟨insert (Tok.ack q x (s.loc q).view) s.E,
        Function.update s.loc q { s.loc q with ballot := some (x, (s.loc q).view) }⟩ := by
  have hsub : s.E ⊆ insert (Tok.ack q x (s.loc q).view) s.E := Set.subset_insert _ _
  have hcc : ∀ r, (Function.update s.loc q
      { s.loc q with ballot := some (x, (s.loc q).view) } r).cc = (s.loc r).cc := by
    intro r; by_cases hr : r = q
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  have hvw : ∀ r, (Function.update s.loc q
      { s.loc q with ballot := some (x, (s.loc q).view) } r).view = (s.loc r).view := by
    intro r; by_cases hr : r = q
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  have hvote : ∀ r v b c, Tok.vote r v b c ∈ insert (Tok.ack q x (s.loc q).view) s.E ↔
      Tok.vote r v b c ∈ s.E := by simp
  have hcom : ∀ r x₀ u, Tok.commit r x₀ u ∈ insert (Tok.ack q x (s.loc q).view) s.E ↔
      Tok.commit r x₀ u ∈ s.E := by simp
  have hprop : ∀ r x₀ u, Tok.propose r x₀ u ∈ insert (Tok.ack q x (s.loc q).view) s.E ↔
      Tok.propose r x₀ u ∈ s.E := by simp
  have hcert : ∀ r x₀ u, Tok.certAck r x₀ u ∈ insert (Tok.ack q x (s.loc q).view) s.E ↔
      Tok.certAck r x₀ u ∈ s.E := by simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro r hr v b c x' u hv hbx
    rw [hvote] at hv
    exact hsub (hI.vote_bal r hr v b c x' u hv hbx)
  · intro r hr v b c x' u hv hax hu
    rw [hvote] at hv
    rcases Set.mem_insert_iff.1 hax with h | h
    · simp only [Tok.ack.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      have := hI.vote_view r hr v b c hv
      omega
    · exact hI.vote_ack r hr v b c x' u hv h hu
  · intro r hr v b c x' u hv hcx hu
    rw [hvote] at hv; rw [hcom] at hcx
    obtain ⟨x'', u', h1, h2, h3⟩ := hI.vote_commit r hr v b c x' u hv hcx hu
    exact ⟨x'', u', h1, h2, HasCC.mono pr hsub h3⟩
  · intro r hr x₁ x₂ u h1 h2
    rcases Set.mem_insert_iff.1 h1 with e1 | e1 <;> rcases Set.mem_insert_iff.1 h2 with e2 | e2
    · simp only [Tok.ack.injEq] at e1 e2; rw [e1.2.1, e2.2.1]
    · simp only [Tok.ack.injEq] at e1; obtain ⟨rfl, rfl, rfl⟩ := e1
      exact absurd e2 (hfirst x₂)
    · simp only [Tok.ack.injEq] at e2; obtain ⟨rfl, rfl, rfl⟩ := e2
      exact absurd e1 (hfirst x₁)
    · exact hI.ack_uniq r hr x₁ x₂ u e1 e2
  · intro r hr x₁ x₂ u h1 h2; rw [hprop] at h1 h2; exact hI.propose_uniq r hr x₁ x₂ u h1 h2
  · intro r hr x' u h; rw [hprop]
    rcases Set.mem_insert_iff.1 h with h | h
    · simp only [Tok.ack.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hp, hc.imp id (Certified.mono pr hsub)⟩
    · obtain ⟨h1, h2⟩ := hI.ack_valid r hr x' u h
      exact ⟨h1, h2.imp id (Certified.mono pr hsub)⟩
  · intro r hr x' v' h; rw [hcert] at h
    obtain ⟨S, bal, cc, h1, h2⟩ := hI.certAck_valid r hr x' v' h
    exact ⟨S, bal, cc, ValidVotes.mono pr hsub h1, h2⟩
  · intro r hr x' u h; rw [hcom] at h; exact HasCC.mono pr hsub (hI.commit_valid r hr x' u h)
  · intro r hr x' u h; rw [hvw]
    by_cases hrq : r = q
    · subst hrq
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq]
      rcases Set.mem_insert_iff.1 h with h | h
      · simp only [Tok.ack.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h
        simp
      · obtain ⟨h1, -⟩ := hI.ack_loc r hr x' u h
        refine ⟨h1, x, _, ⟨rfl, rfl⟩, h1, fun he => ?_⟩
        rw [← he] at h
        exact absurd h (hfirst x')
    · rw [Function.update_of_ne hrq]
      rcases Set.mem_insert_iff.1 h with h | h
      · simp only [Tok.ack.injEq] at h; exact absurd h.1 hrq
      · exact hI.ack_loc r hr x' u h
  · intro r hr x' u h; rw [hvw]
    by_cases hrq : r = q
    · subst hrq
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Set.mem_insert _ _, le_rfl⟩
    · rw [Function.update_of_ne hrq] at h
      obtain ⟨h1, h2⟩ := hI.ballot_loc r hr x' u h
      exact ⟨hsub h1, h2⟩
  · intro r hr x' u h; rw [hcc] at h; rw [hvw]
    obtain ⟨h1, h2⟩ := hI.cc_loc r hr x' u h
    exact ⟨HasCC.mono pr hsub h1, h2⟩
  · intro r hr x' u h; rw [hcom] at h; rw [hcc, hvw]
    exact hI.commit_loc r hr x' u h
  · intro r hr v b c h; rw [hvote] at h; rw [hvw]
    exact hI.vote_view r hr v b c h

theorem Inv.commit {s : State P V} (hI : Inv pr B s) (q : P) (x : V)
    (hcc : HasCC pr s.E x (s.loc q).view) :
    Inv pr B ⟨insert (Tok.commit q x (s.loc q).view) s.E,
        Function.update s.loc q { s.loc q with cc := some (x, (s.loc q).view) }⟩ := by
  have hsub : s.E ⊆ insert (Tok.commit q x (s.loc q).view) s.E := Set.subset_insert _ _
  have hb : ∀ r, (Function.update s.loc q
      { s.loc q with cc := some (x, (s.loc q).view) } r).ballot = (s.loc r).ballot := by
    intro r; by_cases hr : r = q
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  have hvw : ∀ r, (Function.update s.loc q
      { s.loc q with cc := some (x, (s.loc q).view) } r).view = (s.loc r).view := by
    intro r; by_cases hr : r = q
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  have hvote : ∀ r v b c, Tok.vote r v b c ∈ insert (Tok.commit q x (s.loc q).view) s.E ↔
      Tok.vote r v b c ∈ s.E := by simp
  have hack : ∀ r x₀ u, Tok.ack r x₀ u ∈ insert (Tok.commit q x (s.loc q).view) s.E ↔
      Tok.ack r x₀ u ∈ s.E := by simp
  have hprop : ∀ r x₀ u, Tok.propose r x₀ u ∈ insert (Tok.commit q x (s.loc q).view) s.E ↔
      Tok.propose r x₀ u ∈ s.E := by simp
  have hcert : ∀ r x₀ u, Tok.certAck r x₀ u ∈ insert (Tok.commit q x (s.loc q).view) s.E ↔
      Tok.certAck r x₀ u ∈ s.E := by simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro r hr v b c x' u hv hbx
    rw [hvote] at hv; rw [hack]
    exact hI.vote_bal r hr v b c x' u hv hbx
  · intro r hr v b c x' u hv hax hu
    rw [hvote] at hv; rw [hack] at hax
    exact hI.vote_ack r hr v b c x' u hv hax hu
  · intro r hr v b c x' u hv hcx hu
    rw [hvote] at hv
    rcases Set.mem_insert_iff.1 hcx with h | h
    · simp only [Tok.commit.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      have := hI.vote_view r hr v b c hv
      omega
    · obtain ⟨x'', u', h1, h2, h3⟩ := hI.vote_commit r hr v b c x' u hv h hu
      exact ⟨x'', u', h1, h2, HasCC.mono pr hsub h3⟩
  · intro r hr x₁ x₂ u h1 h2; rw [hack] at h1 h2; exact hI.ack_uniq r hr x₁ x₂ u h1 h2
  · intro r hr x₁ x₂ u h1 h2; rw [hprop] at h1 h2; exact hI.propose_uniq r hr x₁ x₂ u h1 h2
  · intro r hr x' u h; rw [hack] at h; rw [hprop]
    obtain ⟨h1, h2⟩ := hI.ack_valid r hr x' u h
    exact ⟨h1, h2.imp id (Certified.mono pr hsub)⟩
  · intro r hr x' v' h; rw [hcert] at h
    obtain ⟨S, bal, cc, h1, h2⟩ := hI.certAck_valid r hr x' v' h
    exact ⟨S, bal, cc, ValidVotes.mono pr hsub h1, h2⟩
  · intro r hr x' u h
    rcases Set.mem_insert_iff.1 h with h | h
    · simp only [Tok.commit.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact HasCC.mono pr hsub hcc
    · exact HasCC.mono pr hsub (hI.commit_valid r hr x' u h)
  · intro r hr x' u h; rw [hack] at h; rw [hb, hvw]
    exact hI.ack_loc r hr x' u h
  · intro r hr x' u h; rw [hb] at h; rw [hack, hvw]
    exact hI.ballot_loc r hr x' u h
  · intro r hr x' u h; rw [hvw]
    by_cases hrq : r = q
    · subst hrq
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨HasCC.mono pr hsub hcc, le_rfl⟩
    · rw [Function.update_of_ne hrq] at h
      obtain ⟨h1, h2⟩ := hI.cc_loc r hr x' u h
      exact ⟨HasCC.mono pr hsub h1, h2⟩
  · intro r hr x' u h; rw [hvw]
    by_cases hrq : r = q
    · subst hrq
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq]
      rcases Set.mem_insert_iff.1 h with h | h
      · simp only [Tok.commit.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h
        simp
      · obtain ⟨h1, -⟩ := hI.commit_loc r hr x' u h
        simpa using h1
    · rw [Function.update_of_ne hrq]
      rcases Set.mem_insert_iff.1 h with h | h
      · simp only [Tok.commit.injEq] at h; exact absurd h.1 hrq
      · exact hI.commit_loc r hr x' u h
  · intro r hr v b c h; rw [hvote] at h; rw [hvw]
    exact hI.vote_view r hr v b c h

variable {inp : P → V}

theorem Inv.step {s s' : State P V} (hI : Inv pr B s) (h : Step pr B inp s s') : Inv pr B s' := by
  cases h with
  | enterView q v hq hv => exact hI.enterView q v hv
  | propose q x hq hl hfirst hx =>
    refine hI.insert_of _ (by simp) (by simp) (by simp) ?_ (by simp)
    intro r hr x' u he y
    simp only [Tok.propose.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hfirst y
  | ack q x hq hp hc hfirst => exact hI.ack q x hq hp hc hfirst
  | certAck q x v hq S bal cc hS hsel =>
    refine hI.insert_of _ (by simp) (by simp) (by simp) (by simp) ?_
    intro r hr x' v' he
    simp only [Tok.certAck.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨S, bal, cc, hS, hsel⟩
  | commit q x hq hcc => exact hI.commit q x hcc
  | byz m hm =>
    refine hI.insert_of _ ?_ ?_ ?_ ?_ ?_
    · rintro r hr x u rfl; exact hr hm
    · rintro r hr x u rfl; exact hr hm
    · rintro r hr v b c rfl; exact hr hm
    · rintro r hr x u rfl; exact absurd hm hr
    · rintro r hr x v rfl; exact absurd hm hr

/-- Every reachable state satisfies the inductive invariant. -/
theorem Inv.of_reachable {s : State P V} (hs : Reachable pr B inp s) : Inv pr B s := by
  induction hs with
  | refl => exact Inv.init pr B
  | tail _ hst ih => exact ih.step hst

end FastByzantineConsensus.Protocol
