import Papers.PODC2018.PPNaming.Basic

/-!
# Lemma 5 and Proposition 6: the sink state

Setting of Section 3.1: a symmetric leader protocol `Name` with `P` states per mobile agent that
solves naming under weak fairness, with an initialized leader (state `l₀`) and arbitrarily
initialized mobile agents, for the population sizes `P - 1` (mobile agents `B`) and `P` (mobile
agents `Option B`; the extra agent `none` is a "fresh" agent).

* `homonym_reach`: two homonyms in state `s` reach `(hom^[j] s, hom^[j] s)` for every `j`, where
  `hom s` is the common state after `(s, s)` (`LeaderProtocol.hom`).
* **Lemma 5** (`lemma5`): in a stably named configuration of a population of size `n = P - 1`
  (reachable from an initial configuration), no agent is in a state `m` with `(m,m) →⁺ (m,m)`.
  The paper states this for weakly fair executions; we prove the form used in Proposition 6
  (states of a stably named configuration), with the paper's argument: a fresh agent `x'` in
  state `m` can replace the `m`-agent forever.
* **Proposition 6** (`prop6`): there is a unique *sink* `m`: `(m,m) → (m,m)`, every pair of
  homonyms `(s,s)` reaches `(m,m)`, and no other state is `hom`-periodic.
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Function

variable {L Q N : Type*}

/-- `hom s`: the common state of two homonyms in state `s` after they meet. -/
def LeaderProtocol.hom (LP : LeaderProtocol L Q) (s : Q) : Q := (LP.mm s s).1

section Homonyms

variable {A : Type*} [DecidableEq A] {LP : LeaderProtocol L Q}

lemma update_update_swap_eq {c : A → Q} {a b : A} (hab : a ≠ b) (v w x : Q) :
    update (update (update (update c a v) b v) a w) b x = update (update c a w) b x := by
  funext y
  by_cases hya : y = a
  · subst hya; simp [hab]
  · by_cases hyb : y = b
    · subst hyb; simp
    · simp [hya, hyb]

/-- Repeated meetings of two homonyms. -/
lemma homonym_reach (hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1) (l : L) (c : A → Q) {a b : A}
    (hab : a ≠ b) (hc : c a = c b) (j : ℕ) :
    LP.toProtocol.Reachable (ofLM l c)
      (ofLM l (update (update c a (LP.hom^[j] (c a))) b (LP.hom^[j] (c a)))) := by
  induction j with
  | zero =>
    have : update (update c a (c a)) b (c a) = c := by
      rw [update_eq_self, hc, update_eq_self]
    simp only [iterate_zero, id_eq, this]
    exact .refl
  | succ j ih =>
    refine ih.tail ⟨some a, some b, by simpa using hab, ?_⟩
    rw [interact_mobile_mobile LP l _ hab]
    congr 1
    simp only [LeaderProtocol.mmUpd, update_self, update_of_ne hab, hdiag,
      iterate_succ_apply', LeaderProtocol.hom]
    rw [update_update_swap_eq hab]

end Homonyms

/-! ### Lemma 5 -/

section Lemma5

variable {B : Type*} [Fintype B] [DecidableEq B] {LP : LeaderProtocol L Q}

/-- The configuration of the population `Option B`: agent `none` (the fresh agent) in state `q`,
the others as in `c`. -/
def extc (c : B → Q) (q : Q) : Option B → Q := fun o => o.elim q c

@[simp] lemma extc_none (c : B → Q) (q : Q) : extc c q none = q := rfl
@[simp] lemma extc_some (c : B → Q) (q : Q) (b : B) : extc c q (some b) = c b := rfl

lemma update_extc (c : B → Q) (q : Q) (b : B) (v : Q) :
    update (extc c q) (some b) v = extc (update c b v) q := by
  funext o; rcases o with _ | o
  · simp
  · by_cases h : o = b
    · subst h; simp
    · simp [h]

/-- Runs of the population `B` lift to `Option B`, the fresh agent being idle. -/
lemma lift_reachable (q : Q) {l : L} {c : B → Q} {D : Config (Option B) (L ⊕ Q)}
    (h : LP.toProtocol.Reachable (ofLM l c) D) :
    ∃ l' c', D = ofLM l' c' ∧
      LP.toProtocol.Reachable (ofLM l (extc c q)) (ofLM l' (extc c' q)) := by
  induction h with
  | refl => exact ⟨l, c, rfl, .refl⟩
  | tail _ hst ih =>
    obtain ⟨l', c', rfl, hr⟩ := ih
    obtain ⟨x, y, hxy, rfl⟩ := hst
    rcases x with _ | a <;> rcases y with _ | b
    · exact absurd rfl hxy
    · refine ⟨_, _, interact_leader_mobile LP l' c' b, hr.tail ⟨none, some (some b), by simp, ?_⟩⟩
      rw [interact_leader_mobile, extc_some, update_extc]
    · refine ⟨_, _, interact_mobile_leader LP l' c' a, hr.tail ⟨some (some a), none, by simp, ?_⟩⟩
      rw [interact_mobile_leader, extc_some, update_extc]
    · have hab : a ≠ b := fun h => hxy (by rw [h])
      refine ⟨_, _, interact_mobile_mobile LP l' c' hab,
        hr.tail ⟨some (some a), some (some b), by simpa using hab, ?_⟩⟩
      rw [interact_mobile_mobile LP l' _ (by simpa using hab)]
      simp only [LeaderProtocol.mmUpd, extc_some, update_extc]

/-- **Lemma 5** (form used in Proposition 6). Let `ofLM λ d` be a stably named configuration of
the population `B` of size `P - 1`, reachable from an initial configuration. Then no agent of it
is in a state `m` with `(m, m) →⁺ (m, m)` (here `hom^[k] m = m`, `k ≥ 1`), provided the protocol
also solves naming in the population `Option B` of size `P`. -/
theorem lemma5 (hs : LP.Symmetric) {name : Q → N} (hname : Injective name)
    (hnull : ∀ p q, p ≠ q → LP.mm p q = (p, q)) {l₀ : L}
    (hP : SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option (Option B)) (L ⊕ Q)))
      (leaderNames name))
    {b₀ : B → Q} {lam : L} {d : B → Q}
    (hreach : LP.toProtocol.Reachable (ofLM l₀ b₀) (ofLM lam d))
    (hD : StablyNamed LP.toProtocol (leaderNames name) (ofLM lam d)) (z : B) {k : ℕ} (hk : 1 ≤ k)
    (hper : LP.hom^[k] (d z) = d z) : False := by
  have hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1 := fun s => by
    have := congrArg Prod.fst (hs.1 s s); simpa using this.symm
  have hdinj : Injective d := by
    have := (leaderNames_ofLM_injective_iff name lam d).1 hD.1
    exact fun a b h => this (by simp [h])
  set m := d z with hm
  let G : Config (Option (Option B)) (L ⊕ Q) → Prop := fun Y => ∃ lam',
    LP.toProtocol.Reachable (ofLM lam d) (ofLM lam' d) ∧ Y = ofLM lam' (extc d m)
  -- every configuration of `G` has the homonyms `none` and `some z` (both in `m`)
  have hnotinj : ∀ Y, G Y → ¬ Injective (leaderNames name Y) := by
    rintro Y ⟨lam', -, rfl⟩ hinj
    have := hinj (a₁ := none) (a₂ := some z) (by simp [hm])
    exact absurd this (by simp)
  have hleader : ∀ Y, G Y → ∀ o, G (LP.toProtocol.interact Y none (some o)) := by
    rintro Y ⟨lam', hr, rfl⟩ o
    obtain ⟨b, hb⟩ : ∃ b, d b = extc d m o := by
      rcases o with _ | b
      · exact ⟨z, rfl⟩
      · exact ⟨b, rfl⟩
    have hr' := hr.tail (show LP.toProtocol.Step (ofLM lam' d)
      (LP.toProtocol.interact (ofLM lam' d) none (some b)) from ⟨none, some b, by simp, rfl⟩)
    rw [interact_leader_mobile] at hr'
    have hc := ofLM_stable hname hD hr'
    have hv : (LP.lm lam' (d b)).2 = d b := by
      have := congrFun hc b; rwa [update_self] at this
    rw [hc] at hr'
    refine ⟨_, hr', ?_⟩
    rw [interact_leader_mobile, ← hb, hv, hb, update_eq_self]
  have hph : ∀ Y, G Y → ∀ x y, x ≠ y → ∃ Y₁ Y₂, LP.toProtocol.Reachable Y Y₁ ∧
      LP.toProtocol.Reachable (LP.toProtocol.interact Y₁ x y) Y₂ ∧ G Y₂ ∧
      ¬ Injective (leaderNames name Y) := by
    intro Y hY x y hxy
    refine ⟨Y, ?_⟩
    rcases x with _ | o₁ <;> rcases y with _ | o₂
    · exact absurd rfl hxy
    · exact ⟨_, .refl, .refl, hleader Y hY o₂, hnotinj Y hY⟩
    · rw [← hs.isSymmetric.interact_comm _ hxy]
      exact ⟨_, .refl, .refl, hleader Y hY o₁, hnotinj Y hY⟩
    · have ho : o₁ ≠ o₂ := fun h => hxy (by rw [h])
      obtain ⟨lam', hr, rfl⟩ := hY
      by_cases he : extc d m o₁ = extc d m o₂
      · -- the two homonyms `none`, `some z` (in state `m`) cycle back
        have hq : extc d m o₁ = m := by
          rcases o₁ with _ | b₁
          · rfl
          · rcases o₂ with _ | b₂
            · exact he
            · exact absurd (congrArg some (hdinj he)) ho
        refine ⟨ofLM lam' (extc d m), .refl, ?_, ⟨lam', hr, rfl⟩, hnotinj _ ⟨lam', hr, rfl⟩⟩
        rw [interact_mobile_mobile LP lam' _ ho]
        have h1 := homonym_reach hdiag lam' (LP.mmUpd (extc d m) o₁ o₂) ho
          (by simp [LeaderProtocol.mmUpd, update_of_ne ho, hdiag, he]) (k - 1)
        convert h1 using 2
        simp only [LeaderProtocol.mmUpd, update_self, update_of_ne ho, hdiag, he]
        rw [update_update_swap_eq ho]
        have hk' : LP.hom^[k - 1] (LP.mm (extc d m o₂) (extc d m o₂)).1 = extc d m o₂ := by
          change LP.hom^[k - 1] (LP.hom (extc d m o₂)) = extc d m o₂
          rw [← iterate_succ_apply, show (k - 1).succ = k by omega, ← he, hq]
          exact hper
        rw [hk', ← he, update_eq_self, he, update_eq_self]
      · refine ⟨ofLM lam' (extc d m), .refl, ?_, ⟨lam', hr, rfl⟩, hnotinj _ ⟨lam', hr, rfl⟩⟩
        rw [interact_mobile_mobile LP lam' _ ho]
        have : LP.mmUpd (extc d m) o₁ o₂ = extc d m := by
          simp only [LeaderProtocol.mmUpd, hnull _ _ he, update_eq_self]
        rw [this]
        exact .refl
  obtain ⟨l', c', heq, hlift⟩ := lift_reachable (LP := LP) m hreach
  obtain ⟨rfl, rfl⟩ := ofLM_injective heq
  exact hP.false_of_phases G hph ⟨_, rfl⟩ hlift ⟨lam, .refl, rfl⟩
    (show (none : Option (Option B)) ≠ some none by simp)

end Lemma5

/-! ### Proposition 6 -/

/-- `s` is `hom`-periodic: `(s, s) →⁺ (s, s)`. -/
def LeaderProtocol.IsPer (LP : LeaderProtocol L Q) (s : Q) : Prop :=
  ∃ k, 1 ≤ k ∧ LP.hom^[k] s = s

/-- In a finite set of states, every orbit of `hom` reaches a periodic state. -/
lemma exists_iterate_isPer [Finite Q] (LP : LeaderProtocol L Q) (s : Q) :
    ∃ i, LP.IsPer (LP.hom^[i] s) := by
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun j : ℕ => LP.hom^[j] s)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨i, j - i, by omega, ?_⟩
    rw [← iterate_add_apply, Nat.sub_add_cancel h.le]; exact he.symm
  · refine ⟨j, i - j, by omega, ?_⟩
    rw [← iterate_add_apply, Nat.sub_add_cancel h.le]; exact he

lemma LeaderProtocol.IsPer.hom {LP : LeaderProtocol L Q} {s : Q} (h : LP.IsPer s) :
    LP.IsPer (LP.hom s) := by
  obtain ⟨k, hk, he⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [← iterate_succ_apply, iterate_succ_apply', he]

section Prop6

variable [Fintype Q] {B : Type*} [Fintype B] [DecidableEq B] {LP : LeaderProtocol L Q}

/-- Lemma 2 in the setting of Section 3.1 (population `Option B` of size `P`). -/
lemma lemma2_sec31 (hcard : Fintype.card B + 1 = Fintype.card Q) {name : Q → N} {l₀ : L}
    (hP : SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option (Option B)) (L ⊕ Q)))
      (leaderNames name)) :
    Injective name ∧ ∀ p q, p ≠ q → LP.mm p q = (p, q) := by
  obtain ⟨q⟩ : Nonempty Q := Fintype.card_pos_iff.1 (by omega)
  exact lemma2_leader (by simp [hcard])
    (I := (initLeader l₀ : Set (Config (Option (Option B)) (L ⊕ Q)))) (c₀ := fun _ => q) ⟨_, rfl⟩
    (hP.reachNamed (show (none : Option (Option B)) ≠ some none by simp))

/-- **Proposition 6** (existence and uniqueness of the sink). If a symmetric protocol with `P`
states per mobile agent and an initialized leader solves naming under weak fairness for the
population sizes `P - 1` and `P` (mobile agents arbitrarily initialized), then there is a state
`m` with `(m, m) → (m, m)`, such that every pair of homonyms `(s, s)` reaches `(m, m)`
(`hom^[k] s = m`), and `m` is the only state with `(m, m) →⁺ (m, m)`. -/
theorem prop6 (hs : LP.Symmetric) (h2 : 2 ≤ Fintype.card Q)
    (hcard : Fintype.card B + 1 = Fintype.card Q) {name : Q → N} {l₀ : L}
    (hP : SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option (Option B)) (L ⊕ Q)))
      (leaderNames name))
    (hP1 : SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option B) (L ⊕ Q)))
      (leaderNames name)) :
    ∃ m, LP.hom m = m ∧ (∀ s, ∃ k, LP.hom^[k] s = m) ∧ ∀ s, LP.IsPer s → s = m := by
  classical
  obtain ⟨hname, hnull⟩ := lemma2_sec31 hcard hP
  obtain ⟨q⟩ : Nonempty Q := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨b₁⟩ : Nonempty B := Fintype.card_pos_iff.1 (by omega)
  -- a stably named configuration of the population `B` of size `P - 1`
  obtain ⟨D, hD, hDs⟩ := hP1.reachNamed (show (none : Option B) ≠ some b₁ by simp)
    (ofLM l₀ (fun _ => q)) ⟨_, rfl⟩ _ .refl
  obtain ⟨lam, d, rfl⟩ := exists_ofLM_of_reachable LP hD
  have hdinj : Injective d := by
    have := (leaderNames_ofLM_injective_iff name lam d).1 hDs.1
    exact fun a b h => this (by simp [h])
  have hnoper : ∀ b, ¬ LP.IsPer (d b) := fun b ⟨k, hk, he⟩ =>
    lemma5 hs hname hnull hP hD hDs b hk he
  -- at most one periodic state
  have huniq : ∀ p₁ p₂, LP.IsPer p₁ → LP.IsPer p₂ → p₁ = p₂ := by
    intro p₁ p₂ h₁ h₂
    by_contra hne
    have hsub : Finset.univ.image d ⊆ (Finset.univ.erase p₁).erase p₂ := by
      intro x hx
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hnoper b (h ▸ h₂), fun h => hnoper b (h ▸ h₁)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hdinj, Finset.card_univ,
      Finset.card_erase_of_mem (by simp [Ne.symm hne]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ] at this
    omega
  obtain ⟨i, hi⟩ := exists_iterate_isPer LP q
  set m := LP.hom^[i] q
  refine ⟨m, huniq _ _ hi.hom hi, fun s => ?_, fun s hs => huniq _ _ hs hi⟩
  obtain ⟨j, hj⟩ := exists_iterate_isPer LP s
  exact ⟨j, huniq _ _ hj hi⟩

end Prop6

end Podc.PPNaming
