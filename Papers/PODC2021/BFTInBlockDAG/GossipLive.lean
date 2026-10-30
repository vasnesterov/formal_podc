import Papers.PODC2021.BFTInBlockDAG.Shim

/-!
# Liveness of gossip (Lemmas 3.6, 3.7, A.8, 4.3 (1), A.17)

Runs of the asynchronous system of `Gossip.lean` and the fairness assumptions under which the
liveness lemmas of the paper hold.

A **run** is an infinite sequence of states `st 0 = Sys.init, st 1, …` and events `ev t` with
`Step Byz (st t) (ev t) (st (t+1))`. A run is **fair** (`Run.Fair`) if

* (Assumption 1, reliable delivery) every message sent from a correct server to a correct server
  is received at least once (`deliver`). This is weaker than the paper's assumption, which is per
  send event;
* (weak fairness of lines 6–9 and 10–11 of Algorithm 1) if `validate s B` (resp. `askFwd s B' B`)
  is continuously enabled from some time on, it eventually happens (`validate`, `askFwd`). The
  timeout `Δ_B'` of line 10 is abstracted away: lines 10–11 may fire at any time while the guard
  holds;
* (Algorithm 3, lines 10–11) every correct server calls `disseminate()` infinitely often
  (`disseminate`, the weak fairness of the always-enabled event `disseminate s`).

The user's requests and the Byzantine servers are not constrained.

Main results (for a fair run `ρ` and correct servers):
* Lemma A.8 (`lemma_A_8`): every block of `G_s` is eventually referenced by an own block of `s`;
* Lemma 3.6 (1) (`lemma_3_6_1`): a block of `G_s` is eventually received by every correct server;
* Lemma 3.6 (2) (`lemma_3_6_2`): a block of `G_s` is eventually in `G_{s'}` of every correct `s'`;
* Lemma 3.7 (`lemma_3_7`): eventually `G_s ∪ G_{s'} ⊆ G'_s` (and `G'_s` is a block DAG with
  `toGraph (G_s ∪ G_{s'}) ≤ toGraph G'_s`);
* Lemma 4.3 (1) (`lemma_4_3_1`): reliable delivery of the link implemented by the interpretation;
* Lemma A.17 (`lemma_A_17`): a request to a correct server `s` eventually appears in a block of
  `s` in the block DAG of every correct server.

Non-vacuity: `FairExample.run_fair` (a fair run with one correct server).

The only invariant needed beyond `Inv` is `Live.FwdOK`: a forwarding request `FWD B` between
correct servers is only sent to a server that has `B` in its block DAG; so a single delivery of
`FWD B` suffices, whenever it happens.
-/

set_option linter.unusedSectionVars false

namespace Podc.BFTInBlockDAG

open Block

variable {S L R : Type} [DecidableEq S] [DecidableEq L] [DecidableEq R] {Byz : Set S}

namespace Live

/-! ### One-step facts about `apply` -/

omit [DecidableEq L] [DecidableEq R] in
theorem loc_upd (σ : Sys S L R) (s s' : S) (l : Local S L R) :
    (σ.upd s l).loc s' = if s' = s then l else σ.loc s' := Function.update_apply ..

/-- `G` only grows. -/
theorem log_sub_apply (σ : Sys S L R) (e : Ev S L R) (s : S) :
    (σ.loc s).log ⊆ ((apply σ e).loc s).log := by
  intro B hB
  cases e with
  | request s₀ ℓ r => simp only [apply, loc_upd]; split_ifs with h <;> [subst h; skip] <;> simpa
  | recv s₀ src p =>
    cases p with
    | blk C =>
      simp only [apply]; split_ifs
      · exact hB
      · simp only [loc_upd]; split_ifs with h <;> [subst h; skip] <;> simpa
    | fwd C => simp only [apply]; split_ifs <;> exact hB
  | validate s₀ C =>
    simp only [apply, loc_upd]; split_ifs with h <;> [subst h; skip] <;> simp [hB]
  | askFwd => exact hB
  | disseminate s₀ =>
    simp only [apply, Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> simp [hB]
  | byz => exact hB

/-- The sent messages only grow. -/
theorem sent_sub_apply (σ : Sys S L R) (e : Ev S L R) : σ.sent ⊆ (apply σ e).sent := by
  intro x hx
  cases e with
  | request => exact hx
  | recv s₀ src p =>
    cases p with
    | blk C => simp only [apply]; split_ifs <;> exact hx
    | fwd C => simp only [apply]; split_ifs <;> simp [hx]
  | validate => exact hx
  | askFwd => exact Set.mem_insert_of_mem _ hx
  | disseminate => exact Or.inl hx
  | byz => exact Set.mem_insert_of_mem _ hx

/-- The own blocks only grow. -/
theorem own_sub_apply (σ : Sys S L R) (e : Ev S L R) (s : S) :
    (σ.loc s).own ⊆ ((apply σ e).loc s).own := by
  intro B hB
  cases e with
  | request s₀ ℓ r => simp only [apply, loc_upd]; split_ifs with h <;> [subst h; skip] <;> simpa
  | recv s₀ src p =>
    cases p with
    | blk C =>
      simp only [apply]; split_ifs
      · exact hB
      · simp only [loc_upd]; split_ifs with h <;> [subst h; skip] <;> simpa
    | fwd C => simp only [apply]; split_ifs <;> exact hB
  | validate s₀ C =>
    simp only [apply, loc_upd]; split_ifs with h <;> [subst h; skip] <;> simpa
  | askFwd => exact hB
  | disseminate s₀ =>
    simp only [apply, Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> simp [hB]
  | byz => exact hB

/-- The requests received from the user only grow. -/
theorem reqs_sub_apply (σ : Sys S L R) (e : Ev S L R) (s : S) :
    (σ.loc s).reqs ⊆ ((apply σ e).loc s).reqs := by
  intro B hB
  cases e with
  | request s₀ ℓ r =>
    simp only [apply, loc_upd]; split_ifs with h <;> [subst h; skip] <;> simp [hB]
  | recv s₀ src p =>
    cases p with
    | blk C =>
      simp only [apply]; split_ifs
      · exact hB
      · simp only [loc_upd]; split_ifs with h <;> [subst h; skip] <;> simpa
    | fwd C => simp only [apply]; split_ifs <;> exact hB
  | validate s₀ C =>
    simp only [apply, loc_upd]; split_ifs with h <;> [subst h; skip] <;> simpa
  | askFwd => exact hB
  | disseminate s₀ =>
    simp only [apply, Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> simpa
  | byz => exact hB

/-- `s` has received `B`: `B ∈ G ∪ blks`. -/
def Received (σ : Sys S L R) (s : S) (B : Block S L R) : Prop :=
  B ∈ (σ.loc s).log ∨ B ∈ (σ.loc s).blks

/-- A received block stays received. -/
theorem received_apply {σ : Sys S L R} {s : S} {B : Block S L R} (h : Received σ s B)
    (e : Ev S L R) : Received (apply σ e) s B := by
  rcases h with h | h
  · exact Or.inl (log_sub_apply σ e s h)
  cases e with
  | request s₀ ℓ r =>
    right; simp only [apply, loc_upd]; split_ifs with h' <;> [subst h'; skip] <;> simpa
  | recv s₀ src p =>
    cases p with
    | blk C =>
      simp only [apply]; split_ifs
      · exact Or.inr h
      · right; simp only [loc_upd]; split_ifs with h' <;> [subst h'; skip] <;> simp [h]
    | fwd C => simp only [apply]; split_ifs <;> exact Or.inr h
  | validate s₀ C =>
    unfold Received; simp only [apply, loc_upd]
    split_ifs with h'
    · subst h'
      by_cases hBC : B = C
      · subst hBC; simp
      · simp [h, hBC]
    · exact Or.inr h
  | askFwd => exact Or.inr h
  | disseminate s₀ =>
    right; simp only [apply, Function.update_apply]; split_ifs with h' <;> [subst h'; skip] <;>
      simpa
  | byz => exact Or.inr h

/-- Messages `fwd B` in `sent` after a step: old ones, or sent by `askFwd`, or by a `byz` event. -/
theorem mem_sent_apply_fwd {σ : Sys S L R} {e : Ev S L R} {a b : S} {B : Block S L R}
    (h : (a, b, Payload.fwd B) ∈ (apply σ e).sent) :
    (a, b, Payload.fwd B) ∈ σ.sent ∨ (∃ B', e = .askFwd a B' B ∧ B'.n = b) ∨
      e = .byz a b (.fwd B) := by
  cases e with
  | request => exact Or.inl h
  | recv s₀ src p =>
    cases p with
    | blk C => left; simp only [apply] at h; split_ifs at h <;> exact h
    | fwd C =>
      left; simp only [apply] at h; split_ifs at h
      · simpa using h
      · exact h
  | validate => exact Or.inl h
  | askFwd s₀ B' C =>
    rcases Set.mem_insert_iff.1 h with h | h
    · simp only [Prod.mk.injEq, Payload.fwd.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inl ⟨B', rfl, rfl⟩)
    · exact Or.inl h
  | disseminate s₀ =>
    rcases h with h | ⟨s', hs'⟩
    · exact Or.inl h
    · simp at hs'
  | byz b₀ dst p =>
    rcases Set.mem_insert_iff.1 h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr rfl)
    · exact Or.inl h

/-- Effect of `recv s src (blk B)`: afterwards `s` has received `B`. -/
theorem received_recv_blk (σ : Sys S L R) (s src : S) (B : Block S L R) :
    Received (apply σ (.recv s src (.blk B))) s B := by
  unfold Received; simp only [apply]
  split_ifs with h
  · exact Or.inl h
  · simp [loc_upd]

/-- Effect of `recv s src (fwd B)` when `B ∈ G_s`: `s` sends `B` to `src`. -/
theorem sent_recv_fwd {σ : Sys S L R} {s src : S} {B : Block S L R} (h : B ∈ (σ.loc s).log) :
    (s, src, Payload.blk B) ∈ (apply σ (.recv s src (.fwd B))).sent := by
  simp [apply, h]

/-- Effect of `askFwd s B' B`: `s` sends `FWD B` to `B'.n`. -/
theorem sent_askFwd (σ : Sys S L R) (s : S) (B' B : Block S L R) :
    (s, B'.n, Payload.fwd B) ∈ (apply σ (.askFwd s B' B)).sent := by
  simp [apply]

/-- Effect of `validate s B`: `B ∈ G_s`. -/
theorem mem_log_validate (σ : Sys S L R) (s : S) (B : Block S L R) :
    B ∈ ((apply σ (.validate s B)).loc s).log := by
  simp [apply, loc_upd]

/-- Effect of `disseminate s` on the local state of `s`. -/
theorem loc_disseminate (σ : Sys S L R) (s : S) :
    (apply σ (.disseminate s)).loc s =
      { σ.loc s with log := (σ.loc s).log ++ [newBlock s (σ.loc s)], k := (σ.loc s).k + 1,
                     preds := [newBlock s (σ.loc s)], rqsts := [],
                     own := (σ.loc s).own ++ [newBlock s (σ.loc s)] } := by
  simp [apply]

/-! ### Correct forwarding requests -/

/-- A forwarding request `FWD B` from a correct server to a correct server `b` is only sent for a
block `B ∈ G_b` (it is a predecessor of a block of `b`, and correct servers insert the
predecessors of their blocks before disseminating them). -/
def FwdOK (Byz : Set S) (σ : Sys S L R) : Prop :=
  ∀ a b B, a ∉ Byz → b ∉ Byz → (a, b, Payload.fwd B) ∈ σ.sent → B ∈ (σ.loc b).log

theorem FwdOK.step {σ σ' : Sys S L R} {e : Ev S L R} (hI : Inv Byz σ) (hF : FwdOK Byz σ)
    (h : Step Byz σ e σ') : FwdOK Byz σ' := by
  obtain ⟨hen, rfl⟩ := h
  intro a b B ha hb hB
  apply log_sub_apply
  rcases mem_sent_apply_fwd hB with hB | ⟨B', rfl, hn⟩ | rfl
  · exact hF a b B ha hb hB
  · obtain ⟨-, hB'b, hBB', -, -⟩ := hen
    have hB'own := hI.mem_own hb ((hI.loc a ha).auth B' (Or.inr hB'b)) hn
    exact (hI.loc b hb).dag.2 B' ((hI.loc b hb).own_sub B' hB'own) B hBB'
  · exact absurd hen.1 ha

theorem reachable_fwdOK {σ : Sys S L R} (h : Reachable Byz σ) : FwdOK Byz σ := by
  induction h with
  | refl => intro a b B _ _ h; simp [Sys.init] at h
  | tail h₁ h₂ ih => obtain ⟨e, he⟩ := h₂; exact ih.step (reachable_inv h₁) he

/-! ### Eventualities -/

/-- A property that is preserved by every time step holds from then on. -/
theorem stable {p : ℕ → Prop} (h : ∀ t, p t → p (t + 1)) {t t' : ℕ} (hp : p t) (htt' : t ≤ t') :
    p t' := by
  induction htt' with
  | refl => exact hp
  | step _ ih => exact h _ ih

/-- Finitely many stable eventualities hold simultaneously (and arbitrarily late). -/
theorem exists_forall_mem {α : Type*} {p : α → ℕ → Prop}
    (hp : ∀ a t t', t ≤ t' → p a t → p a t') (l : List α) (h : ∀ a ∈ l, ∃ t, p a t) (t₀ : ℕ) :
    ∃ T ≥ t₀, ∀ a ∈ l, p a T := by
  induction l with
  | nil => exact ⟨t₀, le_rfl, by simp⟩
  | cons a l ih =>
    obtain ⟨T, hT, hl⟩ := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    obtain ⟨ta, ha⟩ := h a List.mem_cons_self
    refine ⟨max T ta, le_trans hT (le_max_left _ _), ?_⟩
    rintro b (_ | ⟨_, hb⟩)
    · exact hp _ _ _ (le_max_right _ _) ha
    · exact hp _ _ _ (le_max_left _ _) (hl b hb)

end Live

/-! ### Runs and fairness -/

/-- A run of the system: an infinite execution from the initial state. -/
structure Run (Byz : Set S) where
  /-- The state at time `t`. -/
  st : ℕ → Sys S L R
  /-- The event taken at time `t`. -/
  ev : ℕ → Ev S L R
  init : st 0 = Sys.init
  step : ∀ t, Step Byz (st t) (ev t) (st (t + 1))

/-- Weak fairness of an event: if it is continuously enabled from some time on, it eventually
happens. -/
def Run.WeakFair (ρ : Run (S := S) (L := L) (R := R) Byz) (e : Ev S L R) : Prop :=
  ∀ t, (∀ t' ≥ t, Enabled Byz (ρ.st t') e) → ∃ t' ≥ t, ρ.ev t' = e

/-- Fair runs. -/
structure Run.Fair (ρ : Run (S := S) (L := L) (R := R) Byz) : Prop where
  /-- Assumption 1 (reliable delivery) between correct servers: a message sent from a correct
  server to a correct server is received (at least once). -/
  deliver : ∀ t a b p, a ∉ Byz → b ∉ Byz → (a, b, p) ∈ (ρ.st t).sent →
    ∃ t', ρ.ev t' = .recv b a p
  /-- Weak fairness of lines 6–9 of Algorithm 1. -/
  validate : ∀ s B, ρ.WeakFair (.validate s B)
  /-- Weak fairness of lines 10–11 of Algorithm 1 (the timeout `Δ_B'` is abstracted away). -/
  askFwd : ∀ s B' B, ρ.WeakFair (.askFwd s B' B)
  /-- Algorithm 3, lines 10–11: correct servers call `disseminate()` infinitely often. -/
  disseminate : ∀ s, ρ.WeakFair (.disseminate s)

namespace Run

open Live

variable (ρ : Run (S := S) (L := L) (R := R) Byz)

theorem st_succ (t : ℕ) : ρ.st (t + 1) = apply (ρ.st t) (ρ.ev t) := (ρ.step t).2

theorem enabled (t : ℕ) : Enabled Byz (ρ.st t) (ρ.ev t) := (ρ.step t).1

/-- Every state of a run is reachable. -/
theorem reachable (t : ℕ) : Reachable Byz (ρ.st t) := by
  induction t with
  | zero => rw [ρ.init]; exact Relation.ReflTransGen.refl
  | succ t ih => exact ih.tail ⟨ρ.ev t, ρ.step t⟩

theorem inv (t : ℕ) : Inv Byz (ρ.st t) := reachable_inv (ρ.reachable t)

theorem linv (t : ℕ) {s : S} (hs : s ∉ Byz) : LInv Byz (ρ.st t) s := (ρ.inv t).loc s hs

variable {ρ}

theorem log_mono {s : S} {t t' : ℕ} (h : t ≤ t') :
    ((ρ.st t).loc s).log ⊆ ((ρ.st t').loc s).log := fun B hB =>
  stable (p := fun t => B ∈ ((ρ.st t).loc s).log)
    (fun t h => by rw [ρ.st_succ]; exact log_sub_apply _ _ _ h) hB h

theorem sent_mono {t t' : ℕ} (h : t ≤ t') : (ρ.st t).sent ⊆ (ρ.st t').sent := fun x hx =>
  stable (p := fun t => x ∈ (ρ.st t).sent)
    (fun t h => by rw [ρ.st_succ]; exact sent_sub_apply _ _ h) hx h

theorem own_mono {s : S} {t t' : ℕ} (h : t ≤ t') :
    ((ρ.st t).loc s).own ⊆ ((ρ.st t').loc s).own := fun B hB =>
  stable (p := fun t => B ∈ ((ρ.st t).loc s).own)
    (fun t h => by rw [ρ.st_succ]; exact own_sub_apply _ _ _ h) hB h

theorem reqs_mono {s : S} {t t' : ℕ} (h : t ≤ t') :
    ((ρ.st t).loc s).reqs ⊆ ((ρ.st t').loc s).reqs := fun B hB =>
  stable (p := fun t => B ∈ ((ρ.st t).loc s).reqs)
    (fun t h => by rw [ρ.st_succ]; exact reqs_sub_apply _ _ _ h) hB h

theorem received_mono {s : S} {B : Block S L R} {t t' : ℕ} (h : t ≤ t')
    (hB : Received (ρ.st t) s B) : Received (ρ.st t') s B :=
  stable (p := fun t => Received (ρ.st t) s B)
    (fun t h => by rw [ρ.st_succ]; exact received_apply h _) hB h

/-- A correct server disseminates after any given time. -/
theorem Fair.exists_disseminate (hF : ρ.Fair) {s : S} (hs : s ∉ Byz) (t : ℕ) :
    ∃ t' ≥ t, ρ.ev t' = .disseminate s :=
  hF.disseminate s t fun _ _ => hs

/-- Lines 6–9: once `validate s B` is enabled, `B` is eventually inserted into `G_s`. -/
theorem Fair.validate_eventually (hF : ρ.Fair) {s : S} {B : Block S L R} {t : ℕ}
    (h : Enabled Byz (ρ.st t) (.validate s B)) : ∃ t' ≥ t, B ∈ ((ρ.st t').loc s).log := by
  by_contra hne
  push Not at hne
  have hen : ∀ t' ≥ t, Enabled Byz (ρ.st t') (.validate s B) := by
    intro t' ht'
    obtain ⟨hs, hb, hv, hp⟩ := h
    refine ⟨hs, ?_, hv, fun C hC => log_mono ht' (hp C hC)⟩
    rcases received_mono ht' (Or.inr hb : Received (ρ.st t) s B) with h' | h'
    · exact absurd h' (hne t' ht')
    · exact h'
  obtain ⟨t', ht', he⟩ := hF.validate s B t hen
  apply hne (t' + 1) (by omega)
  rw [ρ.st_succ, he]
  exact mem_log_validate _ _ _

end Run

/-! ### The liveness lemmas -/

open Live

variable {ρ : Run (S := S) (L := L) (R := R) Byz}

/-- Lemma A.8 of the paper: if `B ∈ G_s` for a correct server `s`, then eventually `G_s`
contains a block `D` built by `s` with `B ⇀ D` (`D` is one of the blocks `s` disseminated). -/
theorem lemma_A_8 (hF : ρ.Fair) {s : S} (hs : s ∉ Byz) {B : Block S L R} {t : ℕ}
    (hB : B ∈ ((ρ.st t).loc s).log) :
    ∃ t' ≥ t, ∃ D ∈ ((ρ.st t').loc s).own, B ∈ D.preds ∧ D.n = s ∧
      D ∈ ((ρ.st t').loc s).log := by
  obtain ⟨t₁, ht₁, he⟩ := hF.exists_disseminate hs t
  have hI := ρ.linv (t₁ + 1) hs
  have hB' : B ∈ ((ρ.st (t₁ + 1)).loc s).log := Run.log_mono (by omega) hB
  rcases hI.ref B hB' with h | ⟨D, hD, hBD⟩
  · exfalso
    rw [ρ.st_succ, he, loc_disseminate, List.mem_singleton] at h
    apply (ρ.inv t₁).newBlock_notMem hs
    rw [← h]
    exact Run.log_mono ht₁ hB
  · exact ⟨t₁ + 1, by omega, D, hD, hBD, hI.own_n D hD, hI.own_sub D hD⟩

/-- Lemma 3.6 (1) of the paper: a block in the block DAG of a correct server `s` is eventually
received (inserted into `blks` or `G`) by every correct server `s'`. -/
theorem lemma_3_6_1 (hF : ρ.Fair) {s s' : S} (hs : s ∉ Byz) (hs' : s' ∉ Byz)
    {B : Block S L R} {t : ℕ} (hB : B ∈ ((ρ.st t).loc s).log) :
    ∃ t' ≥ t, B ∈ ((ρ.st t').loc s').log ∨ B ∈ ((ρ.st t').loc s').blks := by
  -- `s` disseminates a block `D` with `B ∈ D.preds` and sends it to `s'`, which receives it
  obtain ⟨t₁, -, D, hD, hBD, hDn, -⟩ := lemma_A_8 hF hs hB
  obtain ⟨t₂, he₂⟩ := hF.deliver t₁ s s' (.blk D) hs hs' ((ρ.linv t₁ hs).sent_own D hD s')
  have hD₂ : Received (ρ.st (t₂ + 1)) s' D := by
    rw [ρ.st_succ, he₂]; exact received_recv_blk _ _ _ _
  by_contra hne
  push Not at hne
  -- while `B` is missing, `s'` keeps `D` in `blks`, so lines 10–11 stay enabled
  have hen : ∀ t' ≥ max t (t₂ + 1), Enabled Byz (ρ.st t') (.askFwd s' D B) := by
    intro t' ht'
    obtain ⟨h1, h2⟩ := hne t' (le_trans (le_max_left _ _) ht')
    rcases Run.received_mono (le_trans (le_max_right _ _) ht') hD₂ with h | h
    · exact absurd ((ρ.linv t' hs').dag.2 D h B hBD) h1
    · exact ⟨hs', h, hBD, h2, h1⟩
  -- `s'` sends `FWD B` to `D.n = s`
  obtain ⟨t₃, -, he₃⟩ := hF.askFwd s' D B _ hen
  have h₃ : (s', s, Payload.fwd B) ∈ (ρ.st (t₃ + 1)).sent := by
    rw [ρ.st_succ, he₃, ← hDn]; exact sent_askFwd _ _ _ _
  -- `s` receives it and answers with `B`
  obtain ⟨t₄, he₄⟩ := hF.deliver _ s' s _ hs' hs h₃
  have hB₄ : B ∈ ((ρ.st t₄).loc s).log := by
    have := ρ.enabled t₄
    rw [he₄] at this
    exact reachable_fwdOK (ρ.reachable t₄) s' s B hs' hs this.2
  have h₄ : (s, s', Payload.blk B) ∈ (ρ.st (t₄ + 1)).sent := by
    rw [ρ.st_succ, he₄]; exact sent_recv_fwd hB₄
  -- `s'` receives `B`
  obtain ⟨t₅, he₅⟩ := hF.deliver _ s s' _ hs hs' h₄
  have h₅ : Received (ρ.st (t₅ + 1)) s' B := by
    rw [ρ.st_succ, he₅]; exact received_recv_blk _ _ _ _
  obtain ⟨h1, h2⟩ := hne (max t (t₅ + 1)) (le_max_left _ _)
  rcases Run.received_mono (le_max_right _ _) h₅ with h | h
  · exact h1 h
  · exact h2 h

/-- Lemma 3.6 (2) of the paper: a block in the block DAG of a correct server `s` is eventually in
the block DAG of every correct server `s'` (i.e. `s'` eventually considers it valid and inserts
it). -/
theorem lemma_3_6_2 (hF : ρ.Fair) {s s' : S} (hs : s ∉ Byz) (hs' : s' ∉ Byz)
    {B : Block S L R} {t : ℕ} (hB : B ∈ ((ρ.st t).loc s).log) :
    ∃ t' ≥ t, B ∈ ((ρ.st t').loc s').log := by
  induction B using Block.wellFounded_edge.induction generalizing t with
  | _ B ih =>
  have hdag := (ρ.linv t hs).dag
  -- all predecessors are eventually in `G_{s'}` (induction hypothesis)
  obtain ⟨T, -, hT⟩ := exists_forall_mem (p := fun C t => C ∈ ((ρ.st t).loc s').log)
    (fun C t t' h hC => Run.log_mono h hC) B.preds
    (fun C hC => (ih C hC (hdag.2 B hB C hC)).imp fun _ h => h.2) t
  -- `B` is eventually received (Lemma 3.6 (1))
  obtain ⟨t₁, ht₁, h₁⟩ := lemma_3_6_1 hF hs hs' hB
  rcases Run.received_mono (le_max_left t₁ T) h₁ with h | h
  · exact ⟨_, le_trans ht₁ (le_max_left _ _), h⟩
  · -- then lines 6–9 are enabled for `B`
    obtain ⟨t', ht', h'⟩ := hF.validate_eventually (t := max t₁ T)
      ⟨hs', h, (hdag.1 B hB).locallyValid, fun C hC => Run.log_mono (le_max_right _ _) (hT C hC)⟩
    exact ⟨t', by omega, h'⟩

/-- Lemma 3.7 of the paper: for correct servers `s`, `s'`, eventually the block DAG of `s`
contains `G_s ∪ G_{s'}`; it is a block DAG `G'_s ⩾ G_s ∪ G_{s'}`. -/
theorem lemma_3_7 (hF : ρ.Fair) {s s' : S} (hs : s ∉ Byz) (hs' : s' ∉ Byz) (t : ℕ) :
    ∃ t' ≥ t, ((ρ.st t).loc s).G ∪ ((ρ.st t).loc s').G ⊆ ((ρ.st t').loc s).G ∧
      IsBlockDAG ((ρ.st t').loc s).G ∧
      toGraph (((ρ.st t).loc s).G ∪ ((ρ.st t).loc s').G) ≤ toGraph ((ρ.st t').loc s).G := by
  obtain ⟨T, hT, hT'⟩ := exists_forall_mem (p := fun C t => C ∈ ((ρ.st t).loc s).log)
    (fun C t t' h hC => Run.log_mono h hC) ((ρ.st t).loc s').log
    (fun C hC => (lemma_3_6_2 hF hs' hs hC).imp fun _ h => h.2) t
  have hsub : ((ρ.st t).loc s).G ∪ ((ρ.st t).loc s').G ⊆ ((ρ.st T).loc s).G := by
    rintro C (hC | hC)
    · exact Run.log_mono hT hC
    · exact hT' C hC
  exact ⟨T, hT, hsub, (ρ.linv T hs).dag, (toGraph_le_toGraph_iff
    (isBlockDAG_union (ρ.linv t hs).dag (ρ.linv t hs').dag).1.2).2 hsub⟩

/-- Lemma 4.3 (1) of the paper (reliable delivery): if, in the interpretation of the block DAG of
a correct server `s`, some server `s₁` (not necessarily correct) sends `m` for instance `ℓ` to a
correct server `s₂`, then eventually, in the interpretation of the block DAG of every correct
server `s'`, `s₂` receives `m`. -/
theorem lemma_4_3_1 {M I Q : Type} [LinearOrder M] (P : Protocol S L R M I Q) (hF : ρ.Fair)
    {ℓ : L} {s s₁ s₂ s' : S} (hs : s ∉ Byz) (hs₂ : s₂ ∉ Byz) (hs' : s' ∉ Byz) {m : M} {t : ℕ}
    (hm : Sends P ((ρ.st t).loc s).G ℓ s₁ m) (hr : P.receiver m = s₂) :
    ∃ t' ≥ t, Receives P ((ρ.st t').loc s').G ℓ s₂ m := by
  obtain ⟨B₁, hB₁, -, hmo⟩ := hm
  obtain ⟨t₁, ht₁, h₁⟩ := lemma_3_6_2 hF hs hs₂ hB₁
  obtain ⟨t₂, ht₂, D, -, hB₁D, hDn, hD⟩ := lemma_A_8 hF hs₂ h₁
  obtain ⟨t₃, ht₃, h₃⟩ := lemma_3_6_2 hF hs₂ hs' hD
  obtain ⟨B', hB', r, hr'⟩ := out_origin P hmo
  exact ⟨t₃, by omega, D, h₃, hDn, (mem_inn P).2
    ⟨seen_iff.2 ⟨B', Relation.TransGen.tail' hB' hB₁D, r, hr'⟩, hr.trans hDn.symm, B₁, hB₁D, hmo⟩⟩

/-- Lemma A.17 of the paper: a request `(ℓ, r)` to a correct server `s` (Algorithm 3, lines 6–7)
is eventually inscribed in a block `B` built by `s` that is in the block DAG of every correct
server `s'`; interpreting `B`, line 6 of Algorithm 2 then passes `r` to `B.PIs[ℓ]`. -/
theorem lemma_A_17 (hF : ρ.Fair) {s s' : S} (hs : s ∉ Byz) (hs' : s' ∉ Byz) {ℓ : L} {r : R}
    {t : ℕ} (h : (ℓ, r) ∈ ((ρ.st t).loc s).reqs) :
    ∃ t' ≥ t, ∃ B ∈ ((ρ.st t').loc s').log, B.n = s ∧ (ℓ, r) ∈ B.rs := by
  obtain ⟨t₁, ht₁, he⟩ := hF.exists_disseminate hs t
  have hI := ρ.linv (t₁ + 1) hs
  have h₁ : (ℓ, r) ∈ ((ρ.st (t₁ + 1)).loc s).reqs := Run.reqs_mono (by omega) h
  have hrq : ((ρ.st (t₁ + 1)).loc s).rqsts = [] := by rw [ρ.st_succ, he, loc_disseminate]
  rw [← hI.reqs, hrq, List.append_nil, List.mem_flatMap] at h₁
  obtain ⟨D, hD, hDr⟩ := h₁
  obtain ⟨t₂, ht₂, h₂⟩ := lemma_3_6_2 hF hs hs' (hI.own_sub D hD)
  exact ⟨t₂, by omega, D, h₂, hI.own_n D hD, hDr⟩

/-! ### Non-vacuity: a fair run

One correct server (`S = Unit`, `Byz = ∅`) that alternately disseminates (even times) and receives
the block it has just sent to itself (odd times). -/

namespace FairExample

variable {L R : Type} [DecidableEq L] [DecidableEq R]

/-- The last block disseminated by the server. -/
def lastOwn (σ : Sys Unit L R) : Block Unit L R := ((σ.loc ()).own.getLast?).getD (.mk () 0 [] [])

/-- The scheduler. -/
def ev (t : ℕ) (σ : Sys Unit L R) : Ev Unit L R :=
  if t % 2 = 0 then .disseminate () else .recv () () (.blk (lastOwn σ))

/-- The states. -/
def st : ℕ → Sys Unit L R
  | 0 => Sys.init
  | t + 1 => apply (st t) (ev t (st t))

omit [DecidableEq L] [DecidableEq R] in
theorem lastOwn_mem {σ : Sys Unit L R} (h : (σ.loc ()).own ≠ []) : lastOwn σ ∈ (σ.loc ()).own := by
  unfold lastOwn
  cases h' : (σ.loc ()).own.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 h') h
  | some D => exact List.mem_of_getLast? h'

theorem own_disseminate (σ : Sys Unit L R) :
    ((apply σ (.disseminate ())).loc ()).own = (σ.loc ()).own ++ [newBlock () (σ.loc ())] := by
  rw [Live.loc_disseminate]

theorem reachable_st (t : ℕ) :
    Reachable (∅ : Set Unit) (st (L := L) (R := R) t) ∧
      Step (∅ : Set Unit) (st (L := L) (R := R) t) (ev t (st t)) (st (t + 1)) := by
  induction t with
  | zero => exact ⟨Relation.ReflTransGen.refl, ⟨by simp [ev, Enabled], rfl⟩⟩
  | succ t ih =>
    have hR : Reachable (∅ : Set Unit) (st (L := L) (R := R) (t + 1)) := ih.1.tail ⟨_, ih.2⟩
    refine ⟨hR, ?_, rfl⟩
    unfold ev
    split_ifs with h
    · simp [Enabled]
    · have ht : t % 2 = 0 := by omega
      have hown : ((st (L := L) (R := R) (t + 1)).loc ()).own ≠ [] := by
        show ((apply (st t) (ev t (st t))).loc ()).own ≠ []
        simp only [ev, ht, ite_true, own_disseminate]
        simp
      exact ⟨by simp, ((reachable_inv hR).loc () (by simp)).sent_own _ (lastOwn_mem hown) ()⟩

/-- The run. -/
def run : Run (S := Unit) (L := L) (R := R) ∅ :=
  ⟨st, fun t => ev t (st t), rfl, fun t => (reachable_st t).2⟩

theorem own_ne_nil_odd (k : ℕ) : ((st (L := L) (R := R) (2 * k + 1)).loc ()).own ≠ [] := by
  show ((apply (st (2 * k)) (ev (2 * k) (st (2 * k)))).loc ()).own ≠ []
  simp [ev, own_disseminate]

theorem st_odd (k : ℕ) : st (L := L) (R := R) (2 * k + 2) = st (2 * k + 1) := by
  show apply (st (2 * k + 1)) (ev (2 * k + 1) (st (2 * k + 1))) = st (2 * k + 1)
  have hI := (reachable_inv (reachable_st (L := L) (R := R) (2 * k + 1)).1).loc () (by simp)
  have hmem := hI.own_sub _ (lastOwn_mem (own_ne_nil_odd k))
  have h2 : (2 * k + 1) % 2 ≠ 0 := by omega
  simp only [ev, h2, ite_false, apply, hmem, ite_true]

/-- In this run, `blks` stays empty and every sent message is an own block sent to itself. -/
theorem blks_sent (t : ℕ) : ((st (L := L) (R := R) t).loc ()).blks = [] ∧
    ∀ x ∈ (st (L := L) (R := R) t).sent, ∃ D ∈ ((st t).loc ()).own, x = ((), (), .blk D) := by
  induction t with
  | zero => simp [st, Sys.init]
  | succ t ih =>
    by_cases h : t % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k := ⟨t / 2, by omega⟩
      show ((apply (st (2 * k)) (ev (2 * k) (st (2 * k)))).loc ()).blks = [] ∧
        ∀ x ∈ (apply (st (2 * k)) (ev (2 * k) (st (2 * k)))).sent,
          ∃ D ∈ ((apply (st (2 * k)) (ev (2 * k) (st (2 * k)))).loc ()).own, x = ((), (), .blk D)
      simp only [ev, h, ite_true, Live.loc_disseminate]
      refine ⟨ih.1, ?_⟩
      rintro x (hx | ⟨s', rfl⟩)
      · obtain ⟨D, hD, rfl⟩ := ih.2 x hx
        exact ⟨D, List.mem_append_left _ hD, rfl⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 1 := ⟨t / 2, by omega⟩
      rw [st_odd]
      exact ih

theorem lastOwn_odd (k : ℕ) :
    ((st (L := L) (R := R) (2 * k + 1)).loc ()).own =
      ((st (L := L) (R := R) (2 * k)).loc ()).own ++ [lastOwn (st (2 * k + 1))] := by
  have h : ((st (L := L) (R := R) (2 * k + 1)).loc ()).own =
      ((st (L := L) (R := R) (2 * k)).loc ()).own ++ [newBlock () ((st (2 * k)).loc ())] := by
    show ((apply (st (2 * k)) (ev (2 * k) (st (2 * k)))).loc ()).own = _
    simp only [ev, show 2 * k % 2 = 0 by omega, ite_true, own_disseminate]
  rw [h]
  simp [lastOwn, h]

theorem own_received (k : ℕ) : ∀ D ∈ ((st (L := L) (R := R) (2 * k)).loc ()).own,
    ∃ j, lastOwn (st (L := L) (R := R) (2 * j + 1)) = D := by
  induction k with
  | zero => simp [st, Sys.init]
  | succ k ih =>
    intro D hD
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, st_odd, lastOwn_odd] at hD
    rcases List.mem_append.1 hD with hD | hD
    · exact ih D hD
    · exact ⟨k, (List.mem_singleton.1 hD).symm⟩

/-- Non-vacuity of `Run.Fair`: the run above is fair. -/
theorem run_fair : (run (L := L) (R := R)).Fair := by
  refine ⟨fun t a b p _ _ hx => ?_, fun s B t hen => ?_, fun s B' B t hen => ?_,
    fun s t _ => ⟨2 * t, by omega, ?_⟩⟩
  · obtain ⟨D, hD, hx⟩ := (blks_sent t).2 _ hx
    obtain rfl : p = .blk D := congrArg (fun x => x.2.2) hx
    obtain ⟨j, hj⟩ := own_received t D (Run.own_mono (ρ := run) (by omega) hD)
    refine ⟨2 * j + 1, ?_⟩
    show ev (2 * j + 1) (st (2 * j + 1)) = _
    simp [ev, hj]
  · have := (hen t le_rfl).2.1
    simp [run, (blks_sent t).1] at this
  · have := (hen t le_rfl).2.1
    simp [run, (blks_sent t).1] at this
  · show ev (2 * t) (st (2 * t)) = _
    simp [ev]

end FairExample

end Podc.BFTInBlockDAG
