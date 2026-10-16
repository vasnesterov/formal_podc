import Papers.PODC2026.TreeAA.Lemmas

/-!
# Protocol `TreeAA` in the lock-step model (Theorem 5)

`TreeAA = PathsFinder ; TreeAAFromPaths` (Section 4.6), built from black-box gradecast protocols
`gc s` (one per sender `s`, run in parallel) and a black-box real-valued AA protocol `realAA`:

* `pathsFinder`: every party gradecasts its root path `P(v_start, v_in)`
  (`Protocol.parallel` of the `gc s`, input translated by `rpath`);
* `pathsOf`: the local computation of `P` and `Q` (Definition 5, lines 2–3 of `PathsFinder`);
* `fromPaths`: `TreeAAFromPaths` — run `realAA` on the index of `proj_P(v_in)` and output
  `Q[[j]]`;
* `treeAA`: the sequential composition; phase 2 starts at round `R_GC` for everybody.

`treeAA_solves` (**Theorem 5**): if `t < n/2`, the gradecasts satisfy Definition 4 within `R_GC`
rounds and `realAA` satisfies Definition 1 with `ε = 1` within `R_RealAA` rounds whenever the
honest inputs are `D(T)`-close, then `treeAA` achieves AA on the tree `T` (Definition 2) within
`R_GC + R_RealAA` rounds. Works in the authenticated setting (signature tokens) and, with
`Auth.none`, in the unauthenticated one.
-/

namespace TreeAA

open Cslib.Byzantine.LockStep SimpleGraph

variable {P V : Type} [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
  {T : SimpleGraph V} (hT : T.IsTree) (r : V) {M₁ S₁ M₂ S₂ : Type}

/-- `PathsFinder`, communication part: `n` parallel gradecasts of the parties' root paths. -/
noncomputable def pathsFinder (gc : P → Protocol P (List V) M₁ (List V × Fin 3)) :
    Protocol P V (P → Option M₁) (P → List V × Fin 3) :=
  (Protocol.parallel (M := fun _ => M₁) gc).comapInput (rpath hT r)

/-- `PathsFinder`, local part: `P` and `Q` from the gradecast outputs (lines 2–3). The second
phase gets `(v_in, P, Q)`. -/
noncomputable def pathsOf (t : ℕ) (_ : P) (x : V) (o : Option (P → List V × Fin 3)) :
    V × List V × List V :=
  (x, lsp (Fintype.card P - t) (o.getD fun _ => ([], 0)) 2,
    lsp (Fintype.card P - t) (o.getD fun _ => ([], 0)) 1)

/-- `TreeAAFromPaths`: join `realAA` with the index `i` of `proj_P(v_in)` in `P`, output the
vertex `v_[j]` of `Q`. -/
noncomputable def fromPaths (realAA : Protocol P ℝ M₂ ℝ) : Protocol P (V × List V × List V) M₂ V :=
  realAA.wrap (fun _ i => (projIdx T i.2.1 i.1 : ℝ)) (fun _ i j => i.2.2.getD (rnd j).toNat i.1)

/-- **`TreeAA`** (Section 4.6). -/
noncomputable def treeAA (t Rgc : ℕ) (gc : P → Protocol P (List V) M₁ (List V × Fin 3))
    (realAA : Protocol P ℝ M₂ ℝ) : Protocol P V ((P → Option M₁) ⊕ M₂) V :=
  (pathsFinder hT r gc).seq Rgc (pathsOf t) (fromPaths (T := T) realAA)

/-- Signature structure of `treeAA`. -/
def treeAuth (A₁ : Auth P M₁ S₁) (A₂ : Auth P M₂ S₂) :
    Auth P ((P → Option M₁) ⊕ M₂) ((Σ _ : P, S₁) ⊕ S₂) :=
  Auth.seq (Auth.parallel (M := fun _ => M₁) fun _ : P => A₁) A₂

section Aux

variable {I M O : Type*} (G : SimpleGraph P) (alg : Protocol P I M O)

lemma status_comapInput {I' : Type*} (f : I' → I) (s : Scenario P I' M) (k : ℕ) (p : P) :
    status G (alg.comapInput f) s k p = status G alg (s.mapInput f) k p := by
  simp only [status, hist_comapInput]; rfl

end Aux

/-- Phase 1 of `treeAA`: in an admissible run, the honest parties' gradecast outputs `d p s`
satisfy integrity and consistency, and `PathsFinder` terminates within `R_GC` rounds. -/
lemma phase1 {t Rgc : ℕ} (A₁ : Auth P M₁ S₁) (gc : P → Protocol P (List V) M₁ (List V × Fin 3))
    (hgc : ∀ s, SolvesAuthWithin ⊤ (gc s) A₁ (atMost t) noPre
      (Gradecast s) Rgc)
    (s : Scenario P V (P → Option M₁)) (hZ : s.byz ∈ atMost t) (hrel : s.Reliable)
    (hV : s.AuthValid ⊤ (pathsFinder hT r gc) (Auth.parallel (M := fun _ => M₁) fun _ => A₁)) :
    ∃ d : P → P → List V × Fin 3,
      (∀ p ∈ s.honest, Decides ⊤ (pathsFinder hT r gc) s p (d p)) ∧
      (∀ q ∈ s.honest, ∀ p ∈ s.honest, d p q = (rpath hT r (s.input q), 2)) ∧
      (∀ p ∈ s.honest, ∀ q ∈ s.honest, ∀ i, (d p i).2 = 2 →
        (d q i).1 = (d p i).1 ∧ 1 ≤ (d q i).2) ∧
      TerminatesBy ⊤ (pathsFinder hT r gc) s Rgc := by
  classical
  set s' := s.mapInput (rpath hT r)
  have hV' : s'.AuthValid ⊤ (Protocol.parallel (M := fun _ => M₁) gc)
      (Auth.parallel (M := fun _ => M₁) fun _ => A₁) :=
    (Scenario.authValid_comapInput _ _).1 hV
  have hsol : ∀ i, Gradecast i (s'.proj i).input (s'.proj i).honest
      (Decides ⊤ (gc i) (s'.proj i)) ∧ TerminatesBy ⊤ (gc i) (s'.proj i) Rgc :=
    fun i => hgc i (s'.proj i) hZ hrel (hV'.proj i) trivial
  have hdec : ∀ p d, Decides ⊤ (pathsFinder hT r gc) s p d ↔
      ∀ i, Decides ⊤ (gc i) (s'.proj i) p (d i) := by
    intro p d
    rw [pathsFinder, decides_comapInput]
    exact decides_parallel_iff (M := fun _ => M₁) ⊤ gc s' p d
  have hex : ∀ p, ∃ d : P → List V × Fin 3, p ∈ s.honest → ∀ i, Decides ⊤ (gc i) (s'.proj i) p (d i) := by
    intro p
    by_cases hp : p ∈ s.honest
    · have : ∀ i, ∃ o, Decides ⊤ (gc i) (s'.proj i) p o := fun i => (hsol i).1.1 p hp
      choose d hd using this
      exact ⟨d, fun _ => hd⟩
    · exact ⟨fun _ => ([], 0), fun h => absurd h hp⟩
  choose d hd using hex
  refine ⟨d, fun p hp => (hdec p (d p)).2 (hd p hp), ?_, ?_, ?_⟩
  · intro q hq p hp
    have h1 := (hsol q).1.2.1 hq p hp
    exact Decides.unique _ _ (hd p hp q) h1
  · intro p hp q hq i h2
    have := (hsol i).1.2.2 p hp q hq _ _ _ _ (hd p hp i) (hd q hq i)
    rw [h2] at this
    have hg : 1 ≤ (d q i).2 := by
      have h := this.1
      have e : ((2 : Fin 3) : ℕ) = 2 := rfl
      rw [e] at h
      rw [Fin.le_iff_val_le_val, show ((1 : Fin 3) : ℕ) = 1 from rfl]
      omega
    exact ⟨(this.2 (by decide) (lt_of_lt_of_le (by decide) hg)).symm, hg⟩
  · intro p hp
    obtain ⟨k, hk, o, ho⟩ := terminatesBy_parallel (Mi := fun _ => M₁) ⊤ gc s' Rgc
      (fun i => (hsol i).2) p hp
    exact ⟨k, hk, o, by rw [pathsFinder, status_comapInput]; exact ho⟩

/-- **Theorem 5.** Let `t < n/2`. Given gradecast protocols (Definition 4, one per sender,
terminating within `R_GC` rounds) and a RealAA protocol (Definition 1 with `ε = 1`, terminating
within `R_RealAA` rounds when the honest inputs are `D(T)`-close), `TreeAA` achieves AA on the
tree `T` (Definition 2) within `R_GC + R_RealAA` rounds, against at most `t` Byzantine parties.
(Authenticated setting with any signature structures `A₁`, `A₂`; take `Auth.none` for the
unauthenticated one.) -/
theorem treeAA_solves {t Rgc Rreal : ℕ} (ht : 2 * t < Fintype.card P)
    (A₁ : Auth P M₁ S₁) (gc : P → Protocol P (List V) M₁ (List V × Fin 3))
    (hgcU : ∀ s, (gc s).Unforging A₁)
    (hgc : ∀ s, SolvesAuthWithin ⊤ (gc s) A₁ (atMost t) noPre (Gradecast s) Rgc)
    (A₂ : Auth P M₂ S₂) (realAA : Protocol P ℝ M₂ ℝ) (hrU : realAA.Unforging A₂)
    (hreal : SolvesAuthWithin ⊤ realAA A₂ (atMost t) (Close (T.diam : ℝ)) (RealAA 1) Rreal) :
    (treeAA hT r t Rgc gc realAA).Unforging (treeAuth A₁ A₂) ∧
    SolvesAuthWithin ⊤ (treeAA hT r t Rgc gc realAA) (treeAuth A₁ A₂) (atMost t) noPre
      (GraphAA T) (Rgc + Rreal) := by
  classical
  refine ⟨Protocol.Unforging.seq
    (Protocol.Unforging.comapInput (Protocol.Unforging.parallel (M := fun _ => M₁) hgcU) _)
    (Protocol.Unforging.wrap _ _ _ hrU), ?_⟩
  intro s hZ hrel hV _
  -- phase 1: `PathsFinder`
  have hV1 := Scenario.AuthValid.seqFst ⊤ (pathsFinder hT r gc) Rgc (pathsOf t)
    (fromPaths (T := T) realAA) hV
  obtain ⟨d, hdec, hint, hcons, hterm⟩ :=
    phase1 hT r A₁ gc hgc (s.seqFst Rgc) hZ (hrel.seqFst Rgc) hV1
  set x₂ := seqInputs ⊤ (pathsFinder hT r gc) Rgc (pathsOf (P := P) t) s with hx₂def
  have hx₂ : ∀ p ∈ s.honest, x₂ p = pathsOf t p (s.input p) (some (d p)) := fun p hp =>
    seqInputs_eq ⊤ _ Rgc (pathsOf t) s p (d p) (hdec p hp) (hterm p hp)
  have hH : s.honestᶜ.ncard ≤ t := by rw [Scenario.honest, compl_compl]; exact hZ
  -- Lemma 10
  obtain ⟨hP, hPQ⟩ := pathsFinder_spec hT r ht hH s.input d hint hcons
  set k := Fintype.card P - t with hk
  -- phase 2: `TreeAAFromPaths`
  have hV2 : ((s.seqSnd Rgc x₂).wrapIn (fun _ i => (projIdx T i.2.1 i.1 : ℝ))).AuthValid
      ⊤ realAA A₂ :=
    (Scenario.authValid_wrap _ _ _ _ _ _).1
      (Scenario.AuthValid.seqSnd ⊤ (pathsFinder hT r gc) Rgc (pathsOf t)
        (fromPaths (T := T) realAA) hV)
  set s₂ := (s.seqSnd Rgc x₂).wrapIn (fun _ (i : V × List V × List V) => (projIdx T i.2.1 i.1 : ℝ))
    with hs₂
  have hin₂ : ∀ p ∈ s.honest, s₂.input p = (projIdx T (lsp k (d p) 2) (s.input p) : ℝ) := by
    intro p hp
    simp only [s₂, Scenario.wrapIn_input, Scenario.seqSnd_input]
    rw [hx₂ p hp]
    rfl
  have hpre : Close (T.diam : ℝ) s₂.input s₂.honest := by
    have := close_projIdx hT r (H := s.honest) s.input (fun p => lsp k (d p) 2)
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
    intro p hp q hq
    rw [hin₂ p hp, hin₂ q hq]
    exact this p hp q hq
  obtain ⟨⟨hrT, hrV, hrA⟩, hrTerm⟩ :=
    hreal s₂ hZ ((hrel.seqSnd Rgc x₂).wrapIn _) hV2 hpre
  have hex : ∀ p, ∃ j : ℝ, p ∈ s.honest → Decides ⊤ realAA s₂ p j := by
    intro p
    by_cases hp : p ∈ s.honest
    · obtain ⟨j, hj⟩ := hrT p hp; exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose j hj using hex
  -- decisions of `treeAA`
  have hdecT : ∀ p ∈ s.honest, ∀ o, Decides ⊤ (treeAA hT r t Rgc gc realAA) s p o ↔
      o = (lsp k (d p) 1).getD (rnd (j p)).toNat (s.input p) := by
    intro p hp o
    have hx₂' : seqInputs ⊤ (pathsFinder hT r gc) Rgc (pathsOf t) s p =
        pathsOf t p (s.input p) (some (d p)) := hx₂ p hp
    rw [treeAA, decides_seq_iff, fromPaths, decides_wrap_iff]
    simp only [Scenario.seqSnd_input, hx₂']
    constructor
    · rintro ⟨j', hj', rfl⟩
      rw [Decides.unique _ _ hj' (hj p hp)]
      rfl
    · rintro rfl
      exact ⟨j p, hj p hp, rfl⟩
  -- Lemmas 6–9
  have hval : ∀ p ∈ s.honest, ∃ a ∈ s.honest, ∃ b ∈ s.honest,
      (projIdx T (lsp k (d a) 2) (s.input a) : ℝ) ≤ j p ∧
        j p ≤ projIdx T (lsp k (d b) 2) (s.input b) := by
    intro p hp
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hrV p hp (j p) (hj p hp)
    exact ⟨a, ha, b, hb, by rw [← hin₂ a ha]; exact h1, by rw [← hin₂ b hb]; exact h2⟩
  have hagr : ∀ p ∈ s.honest, ∀ q ∈ s.honest, |j p - j q| ≤ 1 := fun p hp q hq =>
    hrA p hp q hq _ _ (hj p hp) (hj q hq)
  obtain ⟨hvalid, hagree⟩ := fromPaths_spec hT r s.input (fun p => lsp k (d p) 2)
    (fun p => lsp k (d p) 1) j hP hPQ hval hagr
  refine ⟨⟨fun p hp => ⟨_, (hdecT p hp _).2 rfl⟩, fun p hp o ho => ?_,
    fun p hp q hq o o' ho ho' => ?_⟩, ?_⟩
  · rw [(hdecT p hp o).1 ho]; exact hvalid p hp
  · rw [(hdecT p hp o).1 ho, (hdecT q hq o').1 ho']; exact hagree p hp q hq
  · exact terminatesBy_seq _ _ _ _ _ s Rreal (terminatesBy_wrap _ _ _ _ _ _ hrTerm)

end TreeAA
