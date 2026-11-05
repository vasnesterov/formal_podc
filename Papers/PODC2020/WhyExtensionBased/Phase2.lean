import Papers.PODC2020.WhyExtensionBased.OutputQuery

/-!
# The adversary at the end of phase 1 ("the adversarial strategy for later phases")

When the prover ends phase 1 with a schedule `α(2)` whose first process `p` has input `a`, the
adversary subdivides once more and completes the protocol (`dstar A a`) on all states with `t + 1`
rounds:
* a state adjacent (in `G_{t+1}`) to a vertex that terminated with `b` outputs `b`;
* otherwise, a state that has seen `a` outputs `a`;
all other undecided states stay active forever. Every state reachable after `α(2)` has seen `a`
(`seen_of_first`), so from phase 2 on every process terminates after at most `t + 1` rounds
(`depth_le`), at most two values `a, b` are output in any configuration and every output is valid
(`not_violates_dstar`), and all answers given in phase 1 stay correct (`dstar_agree`, `dstar_none`).
-/

namespace Podc.WhyExtensionBased

open Cslib.NIS Cslib.NIS.Subdiv St
open scoped Classical

variable {P X : Type} [DecidableEq P]

/-- The completed protocol at the start of phase 2. -/
noncomputable def dstar (A : AState P X) (a : X) : Protocol P X X := fun s =>
  if decided A.term s ≠ none then A.term s
  else if s.rounds = A.t + 1 then
    if h : ∃ w b, decided A.term w = some b ∧ Adj A.term (A.t + 1) s w then
      some (Classical.choose (Classical.choose_spec h))
    else if Seen a s then some a else none
  else none

section
variable {A : AState P X} {a : X}

lemma decided_dstar_of_decided {s : St P X} (h : decided A.term s ≠ none) :
    decided (dstar A a) s = decided A.term s := by
  cases s <;> simp_all [decided, dstar]

lemma decided_dstar_of_undecided {s : St P X} (h : decided A.term s = none) (hs : s.Settled)
    (hs0 : ¬ s.IsInit) :
    decided (dstar A a) s =
      if s.rounds = A.t + 1 then
        (if h : ∃ w b, decided A.term w = some b ∧ Adj A.term (A.t + 1) s w then
          some (Classical.choose (Classical.choose_spec h))
        else if Seen a s then some a else none)
      else none := by
  cases s with
  | init => exact absurd trivial hs0
  | upd => exact absurd hs id
  | scan s v =>
    show dstar A a (scan s v) = _
    unfold dstar; rw [if_neg (by rw [h]; simp)]

lemma dstar_ext {s : St P X} (h : decided (dstar A a) s = none) : decided A.term s = none := by
  by_contra hne
  rw [decided_dstar_of_decided hne] at h; exact hne h

/-- The completion agrees with the adversary state on all decided states. -/
lemma dstar_agree (hA : AInv A) : Agree A (dstar A a) := by
  intro s hs
  by_cases hd : decided A.term s = none
  · rcases hs with hs | hs
    · by_cases hss : s.Settled
      · by_cases hs0 : s.IsInit
        · cases s <;> simp_all [decided, IsInit]
        · rw [decided_dstar_of_undecided hd hss hs0, if_neg (by omega), hd]
      · rw [decided_eq_none_of_not_settled hss, decided_eq_none_of_not_settled hss]
    · exact absurd hd hs
  · exact decided_dstar_of_decided hd

/-- Outputs of the completion: a decided output, or an output adjacent to a terminated vertex with the
same value, or `a` from a state that has seen `a`. -/
lemma dstar_cases {s : St P X} {z : X} (h : decided (dstar A a) s = some z) :
    decided A.term s = some z ∨
    (decided A.term s = none ∧ s.Settled ∧ s.rounds = A.t + 1 ∧
      ((∃ w, decided A.term w = some z ∧ Adj A.term (A.t + 1) s w) ∨
       (z = a ∧ Seen a s ∧ ¬ ∃ w b, decided A.term w = some b ∧ Adj A.term (A.t + 1) s w))) := by
  by_cases hd : decided A.term s = none
  · right
    have hss : s.Settled := by
      by_contra hn; rw [decided_eq_none_of_not_settled hn] at h; simp at h
    have hs0 : ¬ s.IsInit := by
      intro hi; cases s <;> simp_all [decided, IsInit]
    rw [decided_dstar_of_undecided hd hss hs0] at h
    split_ifs at h with h1 h2 h3
    · refine ⟨hd, hss, h1, Or.inl ⟨Classical.choose h2, ?_⟩⟩
      have := Classical.choose_spec (Classical.choose_spec h2)
      simp only [Option.some.injEq] at h; rw [← h]; exact this
    · simp at h; subst h; exact ⟨hd, hss, h1, Or.inr ⟨rfl, h3, h2⟩⟩
  · left; rw [← decided_dstar_of_decided hd]; exact h

end

/-! ## Every state after a schedule starting with `p` has seen the input of `p` -/

/-- After a schedule whose first step is by `p`, every settled state with at least one round has seen
`p`'s input. -/
lemma seen_of_first (x : P → X) (p : P) (rest : List P) :
    ∀ j, ∀ z ∈ (exec (initC x) (p :: rest) j).anc, z.Settled → 1 ≤ z.rounds →
      Seen (x p) z := by
  have hR : ∀ γ : List P, Rch (exec (initC x) (p :: γ)) := fun γ => ⟨x, p :: γ, rfl⟩
  suffices H : ∀ γ : List P, (exec (initC x) (p :: γ) p).hist[0]? = some (init p (x p)) ∧
      ∀ j, ∀ z ∈ (exec (initC x) (p :: γ) j).anc, z.Settled → 1 ≤ z.rounds → Seen (x p) z from
    (H rest).2
  intro γ
  induction γ using List.reverseRecOn with
  | nil =>
    have hE : exec (initC x) [p] = step (initC x) p := rfl
    have hp : step (initC x) p p = upd (init p (x p)) := by
      rw [step_self]; rfl
    refine ⟨by rw [hE, hp]; rfl, fun j z hz hzs hzr => ?_⟩
    rw [hE] at hz
    by_cases hj : j = p
    · subst hj; rw [hp] at hz; simp [St.anc] at hz
      rcases hz with rfl | rfl
      · exact absurd hzs id
      · simp [rounds] at hzr
    · rw [step_ne _ hj] at hz; simp [initC, St.anc] at hz; subst hz; simp [rounds] at hzr
  | append_singleton γ q ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hE : exec (initC x) (p :: (γ ++ [q])) = step (exec (initC x) (p :: γ)) q := by
      rw [← List.cons_append, exec_append]; rfl
    set E := exec (initC x) (p :: γ) with hEdef
    rw [hE]
    have hanc : ∀ j, ∀ z ∈ (step E q j).anc, z ∈ (E j).anc ∨ (j = q ∧ z = stepState E q) := by
      intro j z hz
      by_cases hj : j = q
      · subst hj; rw [step_self, anc_stepState] at hz
        rcases List.mem_cons.1 hz with h | h
        · exact Or.inr ⟨rfl, h⟩
        · exact Or.inl h
      · rw [step_ne _ hj] at hz; exact Or.inl hz
    refine ⟨?_, fun j z hz hzs hzr => ?_⟩
    · by_cases hpq : q = p
      · subst hpq
        rw [step_self]
        rcases stepState_cases E q with ⟨s, h1, h2⟩ | ⟨_, h2⟩
        · rw [h2]; simp only [St.hist]; rw [← ih1, h1]; rfl
        · rw [h2]; simp only [St.hist]
          rw [List.getElem?_append_left]; exact ih1
          by_contra hlen; push_neg at hlen
          rw [List.getElem?_eq_none hlen] at ih1; simp at ih1
      · rw [step_ne _ (Ne.symm hpq)]; exact ih1
    · rcases hanc j z hz with h | ⟨rfl, rfl⟩
      · exact ih2 j z h hzs hzr
      · rcases stepState_cases E j with ⟨s, h1, h2⟩ | ⟨_, h2⟩
        · rw [h2] at hzr ⊢
          have hsa : s ∈ (E j).anc := by rw [h1]; simp [St.anc, St.mem_anc_self]
          simp only [rounds] at hzr
          by_cases hs0 : s.rounds = 0
          · refine ⟨p, InPast.scanView (k := p) (w := init p (x p)) ?_ (InPast.upd (InPast.refl _))⟩
            rw [hs0]; exact ih1
          · have hss : s.Settled := Rch.upd_settled (hR γ) (by rw [← h1]; exact St.mem_anc_self _)
            exact (ih2 j s hsa hss (by omega)).mono
              (InPast.scanSelf (InPast.upd (InPast.refl _)))
        · rw [h2] at hzs; exact absurd hzs id

/-- `reinit` of an execution from an initial configuration is again an execution from an initial
configuration with the same schedule. -/
lemma reinit_exec_initC (x u : P → X) (α : List P) :
    ∃ x' : P → X, (∀ j ∈ α, x' j = x j) ∧ reinit (exec (initC x) α) u = exec (initC x') α := by
  refine ⟨fun j => if j ∈ α then x j else u j, fun j hj => by simp [hj], ?_⟩
  have key := exec_reinit (δ := fun (_ : St P X) => (none : Option X)) (initC x)
    (fun j => if j ∈ α then x j else u j) (α := α) (fun j hj _ => by simp [initC, hj])
  rw [reinit_initC] at key
  rw [key.1]
  funext j
  by_cases hj : j ∈ α
  · simp [reinit, not_isInit_exec_of_mem _ hj]
  · simp [reinit, exec_apply_of_not_mem _ hj, initC, hj]


/-! ## Properties of the completion -/

section
variable {A : AState P X} {a : X}

/-- After the extra subdivision at the start of phase 2: `T(b)` and `U(b)` are at distance `≥ 3`,
different `T`'s at distance `≥ 4`. -/
lemma far_next (hA : AInv A) :
    (∀ b, Far (Adj A.term (A.t + 1)) (Tset A.term (A.t + 1) b) (Uset A.term (A.t + 1) b) 3) ∧
    (∀ b c, b ≠ c →
      Far (Adj A.term (A.t + 1)) (Tset A.term (A.t + 1) b) (Tset A.term (A.t + 1) c) 4) :=
  subdiv_far hA.dec_le hA.far4 hA.far5 le_rfl le_rfl

/-- Answers `none` of phase 1 stay correct for the completed protocol. -/
lemma dstar_none (hA : AInv A) {rec : Config P X × Finset P × X} (hrec : rec ∈ A.recs)
    {μ : List P} (hμQ : ∀ p ∈ μ, p ∈ rec.2.1) (hμ : IsSched (dstar A a) rec.1 μ) :
    ∀ p ∈ rec.2.1, outs (dstar A a) (exec rec.1 μ) p ≠ some rec.2.2 := by
  intro p hp hout
  obtain ⟨hRC, hok⟩ := hA.recs rec hrec
  have hx : QDesc A.term rec.1 rec.2.1 (exec rec.1 μ p) :=
    ⟨μ, hμQ, hμ.mono fun s hs => dstar_ext hs, p, hp, rfl⟩
  obtain ⟨h1, h2⟩ := hok _ hx
  obtain ⟨h4, h5⟩ := far_next hA
  rcases dstar_cases hout with h | ⟨hd, hss, hr, hcase⟩
  · exact h1 h
  · have hprot := h2 (by omega) hss hd
    have hocc : Occ A.term (exec rec.1 μ p) := hx.occ hRC.1
    rcases hcase with ⟨w, hw, hadj⟩ | ⟨hya, hsa, hnadj⟩
    · have hwT : w ∈ Tset A.term (A.t + 1) rec.2.2 := mem_Tset_of_adj hadj hw
      rcases hprot with hns | ⟨w', b, hb, hw'b, hadj'⟩
      · exact far_not_adj (h4 _) (by norm_num) hwT ⟨⟨hss, Or.inl hr⟩, hocc, hns⟩ hadj.symm
      · rw [hr] at hadj'
        exact far_not_path2 (h5 _ b (Ne.symm hb)) (by norm_num) hwT (mem_Tset_of_adj hadj' hw'b)
          hadj.symm hadj'
    · rcases hprot with hns | ⟨w', b, -, hw'b, hadj'⟩
      · exact hns (hya ▸ hsa)
      · rw [hr] at hadj'; exact hnadj ⟨w', b, hw'b, hadj'⟩

/-- From phase 2 on, every process terminates within `t + 1` rounds. -/
lemma depth_le (hA : AInv A) {x : P → X} {p : P} {rest : List P}
    (hsch : IsSched (dstar A (x p)) (initC x) (p :: rest)) (j : P) :
    (exec (initC x) (p :: rest) j).depth ≤ 2 * (A.t + 1) := by
  by_contra hlt
  push_neg at hlt
  have hR : Rch (exec (initC x) (p :: rest)) := ⟨x, _, rfl⟩
  set z := (exec (initC x) (p :: rest) j).cut (2 * (A.t + 1)) with hz
  have hzm : z ∈ (exec (initC x) (p :: rest) j).anc := St.cut_mem_anc _ _
  have hzd : z.depth = 2 * (A.t + 1) := by rw [hz, St.depth_cut]; omega
  have hzs : z.Settled := by
    cases hzc : z with
    | init => trivial
    | upd s =>
      have := Rch.depth_upd hR (hzc ▸ hzm); rw [← hzc] at this; omega
    | scan => trivial
  have hzr : z.rounds = A.t + 1 := by have := Rch.depth_settled hR hzm hzs; omega
  have hseen := seen_of_first x p rest j z hzm hzs (by omega)
  have hact := ((isSched_iff _ _).1 hsch) j z hzm (by simp [initC, St.depth]) (by omega)
  by_cases hd : decided A.term z = none
  · have hs0 : ¬ z.IsInit := Settled.not_isInit_of_rounds (by omega)
    rw [decided_dstar_of_undecided hd hzs hs0, if_pos hzr] at hact
    split_ifs at hact
  · rw [decided_dstar_of_decided hd] at hact; exact hd hact

/-- **Correctness from phase 2 on**: no configuration reachable after a schedule starting with `p`
violates `k`-set agreement (`k ≥ 2`). -/
lemma not_violates_dstar [Finite X] {k : ℕ} (hk : 2 ≤ k) (hA : AInv A) {x : P → X} {p : P}
    {rest : List P} (hsch : IsSched (dstar A (x p)) (initC x) (p :: rest)) :
    ¬ Violates (setAgreement X k) (dstar A (x p)) (exec (initC x) (p :: rest)) := by
  set E := exec (initC x) (p :: rest) with hE
  have hR : Reach A.term E := Reach.mono (fun s hs => dstar_ext hs) ⟨x, _, hsch, rfl⟩
  obtain ⟨h4, h5⟩ := far_next hA
  -- every output is seen, and an output other than `x p` is near a terminated vertex
  have hinfo : ∀ q z, outs (dstar A (x p)) E q = some z →
      Seen z (E q) ∧ (z ≠ x p → Vtx A.term (A.t + 1) (E q) ∧
        (E q ∈ Tset A.term (A.t + 1) z ∨
          ∃ w ∈ Tset A.term (A.t + 1) z, Adj A.term (A.t + 1) (E q) w)) := by
    intro q z hz
    have hocc : Occ A.term (E q) := ⟨E, hR, by rw [hR.pid]⟩
    rcases dstar_cases hz with h | ⟨hd, hss, hr, hcase⟩
    · have hss : (E q).Settled := by cases hE : E q <;> simp_all [decided, Settled]
      have hv : Vtx A.term (A.t + 1) (E q) :=
        ⟨hss, Or.inr ⟨by have := hA.dec_le _ (by rw [h]; simp); omega, by rw [h]; simp⟩⟩
      have hT : E q ∈ Tset A.term (A.t + 1) z := ⟨hv, hocc, h⟩
      refine ⟨?_, fun _ => ⟨hv, Or.inl hT⟩⟩
      by_contra hn; exact far_not_mem (h4 z) (by norm_num) hT ⟨hv, hocc, hn⟩
    · have hv : Vtx A.term (A.t + 1) (E q) := ⟨hss, Or.inl hr⟩
      rcases hcase with ⟨w, hw, hadj⟩ | ⟨rfl, hsa, -⟩
      · have hwT := mem_Tset_of_adj hadj hw
        refine ⟨?_, fun _ => ⟨hv, Or.inr ⟨w, hwT, hadj⟩⟩⟩
        by_contra hn; exact far_not_adj (h4 z) (by norm_num) hwT ⟨hv, hocc, hn⟩ hadj.symm
      · exact ⟨hsa, fun h => absurd rfl h⟩
  -- two outputs other than `x p` are equal
  have hpair : ∀ q1 q2 z1 z2, outs (dstar A (x p)) E q1 = some z1 →
      outs (dstar A (x p)) E q2 = some z2 → z1 ≠ x p → z2 ≠ x p → z1 = z2 := by
    intro q1 q2 z1 z2 hz1 hz2 hn1 hn2
    by_cases hq : q1 = q2
    · subst hq; rw [hz1] at hz2; exact Option.some_injective _ hz2
    by_contra hne
    obtain ⟨hv1, hn1'⟩ := (hinfo q1 z1 hz1).2 hn1
    obtain ⟨hv2, hn2'⟩ := (hinfo q2 z2 hz2).2 hn2
    have hadj : Adj A.term (A.t + 1) (E q1) (E q2) := hR.adj hq hv1 hv2
    have hf1 : Far (Adj A.term (A.t + 1)) {E q1} (Tset A.term (A.t + 1) z2) 3 := by
      rcases hn1' with h | ⟨w, hw, hwa⟩
      · exact (h5 z1 z2 hne).mono (by simpa using h) subset_rfl (by norm_num)
      · exact Far.of_adj adj_symm (h5 z1 z2 hne) hw hwa.symm
    have hf2 : Far (Adj A.term (A.t + 1)) {E q2} (Tset A.term (A.t + 1) z2) 2 :=
      Far.of_adj adj_symm hf1 rfl hadj
    rcases hn2' with h | ⟨w, hw, hwa⟩
    · exact far_not_mem hf2 (by norm_num) rfl h
    · exact far_not_adj hf2 le_rfl rfl hw hwa
  -- the set of output values
  set S : Set X := insert (x p) {z | ∃ q, outs (dstar A (x p)) E q = some z ∧ z ≠ x p} with hS
  have hsub : ({z | ∃ q, outs (dstar A (x p)) E q = some z ∧ z ≠ x p} : Set X).Subsingleton := by
    rintro z1 ⟨q1, h1, n1⟩ z2 ⟨q2, h2, n2⟩; exact hpair q1 q2 z1 z2 h1 h2 n1 n2
  refine not_violates (by omega) S ?_ ?_ ?_
  · calc S.ncard ≤ _ + 1 := Set.ncard_insert_le _ _
      _ ≤ 1 + 1 := by gcongr; exact (Set.ncard_le_one_iff_subsingleton).2 hsub
      _ ≤ k := by omega
  · rintro z (rfl | ⟨q, hq, -⟩)
    · exact ⟨p, by rw [hE, input_exec]; rfl⟩
    · exact Rch.seen_input hR.rch (hinfo q z hq).1
  · intro q z hz
    by_cases hza : z = x p
    · rw [hza]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨q, hz, hza⟩

end

end Podc.WhyExtensionBased
