import Papers.PODC2023.ValidityConsensus.Triviality
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Podc.Foundations.Data.Finset.Quorum
import Podc.Computability.Distributed.Byzantine.PartialSync.Merge

/-!
# On the Validity of Consensus — §5.1: the quadratic lower bound (Theorem 4)

Any algorithm solving consensus with a non-trivial validity property has a (synchronous,
`gst = 0`) execution in which correct processes send more than `⌈t/2⌉²` messages
(in fact at least `⌈t/2⌉ (⌈t/2⌉ + 1)`).

* `ValidityConsensus.pigeonhole`: the counting step of Lemma 5.
* `ValidityConsensus.message_lower_bound`: Theorem 4 (Lemmas 5, 6, 7).
-/

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

open Classical in
/-- Counting step of Lemma 5: if every `Q ∈ B` receives messages from at least `|B| + 1`
distinct processes outside `B`, then processes outside `B` send at least `|B| (|B| + 1)`
messages to processes other than themselves within some finite time `N`. Here `f τ p q` is the number of messages sent by `p` to
`q` at time `τ`. -/
theorem pigeonhole (B : Finset P) (f : ℕ → P → P → ℕ)
    (h : ∀ Q ∈ B, B.card + 1 ≤ (univ.filter fun p => p ∉ B ∧ ∃ τ, f τ p Q ≠ 0).card) :
    ∃ N, B.card * (B.card + 1) ≤
      ∑ τ ∈ range N, ∑ p ∈ univ.filter (· ∉ B), ∑ q ∈ univ.filter (· ≠ p), f τ p q := by
  obtain ⟨N, hN⟩ := exists_sum_card_filter_exists_ne_zero_le (univ.filter (· ∉ B)) B
    (disjoint_left.2 fun _ ha hb => (mem_filter.1 ha).2 hb) f
  refine ⟨N, le_trans ?_ hN⟩
  calc B.card * (B.card + 1) = ∑ _Q ∈ B, (B.card + 1) := by simp
    _ ≤ ∑ Q ∈ B, ((univ.filter (· ∉ B)).filter fun p => ∃ τ, f τ p Q ≠ 0).card :=
        sum_le_sum fun Q hQ => (h Q hQ).trans_eq (by rw [filter_filter])

/-- **Lemma 6.** For a non-trivial validity property and any process `Q` and value `vQ`, there is
a canonical execution in which `Q` is faulty (hence silent) and a correct process decides a
value different from `vQ`. -/
theorem exists_run_decides_ne [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuth Au t δ A val)
    (hnt : ¬ val.Trivial t) (ht : 0 < t) (htn : t + 2 ≤ Fintype.card P) (Q : P) (vQ : VO) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.Canonical ∧ Q ∈ R.faulty ∧
      ∃ p ∉ R.faulty, ∃ v, v ≠ vQ ∧ R.Decides A p v := by
  classical
  let d : VI := Classical.arbitrary VI
  obtain ⟨c₀, hc₀, hvQ⟩ : ∃ c₀ : Config P VI, IsInputConfig t c₀ ∧ vQ ∉ val c₀ := by
    by_contra h
    push Not at h
    exact hnt ⟨vQ, h⟩
  -- `c₁`: drop `Q`, give every other process outside `π(c₀)` the proposal `d`
  let c₁ : Config P VI := fun p => if p = Q then none else if c₀ p = none then some d else c₀ p
  have hc₁procs : c₁.procs = univ.erase Q := by
    ext p; by_cases hp : p = Q
    · simp [c₁, hp]
    · by_cases hp' : c₀ p = none <;> simp [c₁, hp, hp', Option.isSome_iff_ne_none]
  have hc₁ : IsInputConfig t c₁ := by
    unfold IsInputConfig; rw [hc₁procs, card_erase_of_mem (mem_univ _), card_univ]; omega
  let R := canonRun (M := M) c₁ d
  have hR : R.Valid t δ := canonRun.valid c₁ d hc₁ δ
  obtain ⟨q, hq⟩ : (univ.erase Q).Nonempty := card_pos.mp (by
    rw [card_erase_of_mem (mem_univ _), card_univ]; omega)
  have hqF : q ∉ R.faulty := by
    simp only [R, canonRun, hc₁procs, mem_compl, mem_erase, mem_univ, and_true, not_not]
    exact (mem_erase.mp hq).1
  obtain ⟨v, hv⟩ := hA.termination R hR (canonRun_authValid _ _) q hqF
  refine ⟨R, hR, canonRun.canonical c₁ d, by simp [R, canonRun, hc₁procs], q, hqF, v, ?_, hv⟩
  rintro rfl
  apply hvQ
  refine canonical_similarity_auth hU hA hR (canonRun.canonical c₁ d) hqF hv hc₀ ⟨?_, ?_⟩
  · -- `π(c₀) \ {Q}` is nonempty
    have h1 : (c₀.procs.erase Q).card ≥ c₀.procs.card - 1 := pred_card_le_card_erase
    unfold IsInputConfig at hc₀
    obtain ⟨r, hr⟩ : (c₀.procs.erase Q).Nonempty := card_pos.mp (by omega)
    rw [mem_erase] at hr
    refine ⟨r, mem_inter.mpr ⟨hr.2, ?_⟩⟩
    rw [canonRun.inputConf, hc₁procs]; simp [hr.1]
  · intro r hr
    rw [mem_inter, canonRun.inputConf, hc₁procs, mem_erase, Config.mem_procs_iff_ne_none] at hr
    rw [canonRun.inputConf]; simp [c₁, hr.2.1, hr.1]

/-- **Lemma 7 (merging with an isolated behaviour).** If `Q` (proposing `v⋆`) decides `vQ`
when running in isolation, and `Q` is faulty and silent in a canonical execution in which a
correct process decides `v`, then `v = vQ`: delay all messages from and to `Q` until both
decisions have happened, and make `Q` correct. (The merged run is `Run.merge` of the execution
and `Q`'s isolated run; the other silent faulty processes become correct too, their messages
delayed the same way, so the merged run has no faulty process.) -/
theorem eq_of_isoRun_decides (hA : SolvesConsensusAuth Au t δ A val) {R : Run P M VI}
    (hR : R.Valid t δ) (hcan : R.Canonical) {Q : P} (hQ : Q ∈ R.faulty) {p : P}
    (hp : p ∉ R.faulty) {v : VO} (hv : R.Decides A p v) (vstar : VI) {vQ : VO}
    (hiso : (isoRun (M := M) Q vstar).Decides A Q vQ) : v = vQ := by
  obtain ⟨τv, hτv⟩ := hv
  obtain ⟨τQ, hτQ⟩ := hiso
  -- merge `R` with `Q` running in isolation: nobody is correct in both, so nobody is Byzantine
  set R' := R.merge A (isoRun (M := M) Q vstar) (max τv τQ)
  have hcov : ∀ r, r ∈ R.faulty ∨ r ∈ (isoRun (M := M) Q vstar).faulty := fun r => by
    by_cases hr : r = Q
    · exact Or.inl (hr ▸ hQ)
    · exact Or.inr (by simp [isoRun, hr])
  have hpQ := (hcov p).resolve_left hp
  refine hA.agreement R' (Run.merge_valid_of_forall_mem hcov hR.dl_ge fun _ _ _ _ _ => le_rfl)
    (Run.merge_authValid_of_forall_mem hcov) p (by simp [R', hpQ]) Q (by simp [R', hQ]) v vQ
    (Run.merge_decides_left hcan hp hpQ (le_max_left _ _) hτv)
    (Run.merge_decides_right (isoRun_canonical Q vstar) hQ (isoRun_correct Q vstar)
      (le_max_right _ _) hτQ)

/-- **Theorem 4 (generalized Dolev–Reischuk bound).** Any algorithm solving consensus with a
non-trivial validity property has a synchronous (`gst = 0`) execution in which correct processes
send at least `⌈t/2⌉ (⌈t/2⌉ + 1) > ⌈t/2⌉²` messages (already within a finite time `N`). -/
theorem message_lower_bound_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuth Au t δ A val)
    (hnt : ¬ val.Trivial t) (ht : 0 < t) (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      ∃ N, ((t + 1) / 2) * ((t + 1) / 2 + 1) ≤ R.msgsUpTo A N := by
  classical
  have h3 : 3 * t < Fintype.card P := by
    by_contra h
    exact hnt (trivial_of_solvesConsensus_auth hU hA ht htn (by omega))
  set k := (t + 1) / 2 with hk
  obtain ⟨B, -, hB⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := k)
    (by simp; omega)
  let vstar : VI := Classical.arbitrary VI
  -- `E_base`: the processes of `B` are faulty: they run in isolation (ignoring every message)
  -- and do not send messages to `B`
  let Eb : Run P M VI :=
    { faulty := B
      inp := fun _ => vstar
      gst := 0
      byz := fun q τ r => if r ∈ B then [] else A.send q ((isoRun (M := M) q vstar).st A τ q) r
      dl := fun _ τ _ => τ }
  have hEb : Eb.Valid t δ :=
    ⟨by simp only [Eb, hB]; omega, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => by simp [Eb]⟩
  -- the faulty processes of `E_base` only emit their own tokens
  have hEba : Eb.AuthValid Au A := by
    intro b hb τ r _ m hm x hx
    simp only [Eb] at hm
    split_ifs at hm
    · simp at hm
    · exact Or.inl (by rw [isoRun_tokens hU b vstar τ r m hm x hx]; exact hb)
  refine ⟨Eb, hEb, hEba, rfl, ?_⟩
  by_contra hcon
  push Not at hcon
  have hmsgs : ∀ N, Eb.msgsUpTo A N =
      ∑ τ ∈ range N, ∑ p ∈ univ.filter (· ∉ B), ∑ q ∈ univ.filter (· ≠ p),
        (Eb.out A p τ q).length := by
    intro N; rw [Run.msgsUpTo, range_eq_Ico]; rfl
  -- Lemma 5, counting step: some `Q ∈ B` hears from at most `k` processes
  obtain ⟨Q, hQB, hSQ⟩ : ∃ Q ∈ B,
      (univ.filter fun p => p ∉ B ∧ ∃ τ, (Eb.out A p τ Q).length ≠ 0).card ≤ k := by
    by_contra h
    push Not at h
    obtain ⟨N, hN⟩ := pigeonhole B (fun τ p q => (Eb.out A p τ q).length)
      (fun Q hQ => by have := h Q hQ; rw [hB]; omega)
    have := hcon N
    rw [hmsgs, ← hB] at this
    omega
  set SQ := univ.filter fun p => p ∉ B ∧ ∃ τ, (Eb.out A p τ Q).length ≠ 0 with hSQdef
  have hSQB : ∀ p ∈ SQ, p ∉ B := fun p hp => (mem_filter.mp hp).2.1
  have hnotSQ : ∀ p, p ∉ B → p ∉ SQ → ∀ τ, Eb.out A p τ Q = [] := by
    intro p hpB hpS τ
    by_contra hne
    exact hpS (mem_filter.mpr ⟨mem_univ _, hpB, τ, by simpa using hne⟩)
  -- Lemma 5, `E'_base`: `Q` becomes correct, the processes of `SQ` become faulty and stop
  -- sending to `Q`; then `Q` receives nothing (except its own messages)
  let E' : Run P M VI :=
    { faulty := B.erase Q ∪ SQ
      inp := fun _ => vstar
      gst := 0
      byz := fun q τ r => if r = Q then [] else Eb.out A q τ r
      dl := fun _ τ _ => τ }
  have hE'f : ∀ r, r ∈ E'.faulty ↔ (r ≠ Q ∧ r ∈ B) ∨ r ∈ SQ := by simp [E']
  have hE' : E'.Valid t δ := by
    refine ⟨?_, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => by simp [E']⟩
    have h1 := card_union_le (B.erase Q) SQ
    have h2 : (B.erase Q).card = k - 1 := by rw [card_erase_of_mem hQB, hB]
    simp only [E']
    omega
  have hQE' : Q ∉ E'.faulty := by
    rw [hE'f]; rintro (h | h)
    · exact h.1 rfl
    · exact hSQB Q h hQB
  let ref : P → Run P M VI := fun r => if r = Q then isoRun Q vstar else Eb
  have hX : ∀ T, ∀ τ ≤ T, ∀ r ∈ {r | (r ∉ B ∧ r ∉ SQ) ∨ r = Q}, E'.st A τ r = (ref r).st A τ r := by
    intro T
    refine E'.st_eq_of_inbox_eq A ?_ ?_
    · intro r _
      show vstar = (ref r).inp r
      by_cases hr : r = Q
      · simp only [ref, hr, ↓reduceIte]; rfl
      · simp only [ref, hr, ↓reduceIte]; rfl
    · intro τ _ ih r hr
      refine E'.inbox_eq_of_dlv_eq A fun q τ' hτ' => ?_
      have hdl1 : E'.dl q τ' r = τ' := rfl
      have hdl2 : (ref r).dl q τ' r = τ' := by by_cases hr : r = Q <;> simp [ref, hr, isoRun, Eb]
      simp only [Run.dlv, hdl1, hdl2]
      split_ifs with hτ
      swap; · rfl
      by_cases hrQ : r = Q
      · -- `Q` receives exactly what it receives in isolation
        subst hrQ
        simp only [ref, ↓reduceIte]
        by_cases hqQ : q = r
        · subst hqQ
          rw [Run.out_of_correct A _ hQE', Run.out_of_correct A _ (isoRun_correct q vstar)]
          have := ih q (Or.inr rfl) τ' hτ'
          simp only [ref, ↓reduceIte] at this
          rw [this]
        · rw [Run.out_eq_nil_of_canonical A (isoRun_canonical r vstar) (by simp [isoRun, hqQ])]
          by_cases hqF : q ∈ E'.faulty
          · rw [Run.out_of_faulty A _ hqF]; simp [E']
          · have hqB : q ∉ B := fun h => hqF ((hE'f q).2 (Or.inl ⟨hqQ, h⟩))
            have hqS : q ∉ SQ := fun h => hqF ((hE'f q).2 (Or.inr h))
            have := ih q (Or.inl ⟨hqB, hqS⟩) τ' hτ'
            simp only [ref, hqQ, ↓reduceIte] at this
            rw [Run.out_of_correct A _ hqF, this, ← Run.out_of_correct A Eb hqB]
            exact hnotSQ q hqB hqS τ'
      · simp only [ref, hrQ, ↓reduceIte]
        have hrB : r ∉ B := by rcases hr with h | h; exact h.1; exact absurd h hrQ
        by_cases hqF : q ∈ E'.faulty
        · rw [Run.out_of_faulty A _ hqF]; simp [E', hrQ]
        · by_cases hqQ : q = Q
          · subst hqQ
            rw [Run.out_of_correct A _ hqF, Run.out_of_faulty A Eb hQB]
            have := ih q (Or.inr rfl) τ' hτ'
            simp only [ref, ↓reduceIte] at this
            simp [Eb, hrB, this]
          · have hqB : q ∉ B := fun h => hqF ((hE'f q).2 (Or.inl ⟨hqQ, h⟩))
            have hqS : q ∉ SQ := fun h => hqF ((hE'f q).2 (Or.inr h))
            have := ih q (Or.inl ⟨hqB, hqS⟩) τ' hτ'
            simp only [ref, hqQ, ↓reduceIte] at this
            rw [Run.out_of_correct A _ hqF, this, ← Run.out_of_correct A Eb hqB]
  -- the Byzantine processes of `E'_base` only replay messages of `E_base`
  have hE'a : E'.AuthValid Au A := by
    intro b hb τ r hr m hm x hx
    simp only [E'] at hm
    split_ifs at hm with hrQ
    · simp at hm
    refine Run.tokens_replay hU (Ri := Eb) (T := τ) (fun q σ r' _ => ?_) τ le_rfl b r m hm x hx
    by_cases hqB : q ∈ B
    · by_cases hqQ : q = Q
      · subst hqQ
        by_cases hr'B : r' ∈ B
        · right; right; intro m' hm'
          simp [Run.out_of_faulty A Eb hqB, Eb, hr'B] at hm'
        · left
          refine ⟨hQE', ?_⟩
          have := hX σ σ le_rfl q (Or.inr rfl)
          simp only [ref, ↓reduceIte] at this
          rw [Run.out_of_correct A _ hQE', this, Run.out_of_faulty A Eb hqB]
          simp [Eb, hr'B]
      · right; right; intro m' hm' y hy
        have hqF : q ∈ E'.faulty := (hE'f q).2 (Or.inl ⟨hqQ, hqB⟩)
        rw [Run.out_of_faulty A Eb hqB] at hm'
        simp only [Eb] at hm'
        split_ifs at hm'
        · simp at hm'
        · rw [isoRun_tokens hU q vstar σ r' m' hm' y hy]; exact hqF
    · by_cases hqS : q ∈ SQ
      · right; left; exact ⟨(hE'f q).2 (Or.inr hqS), hqB⟩
      · left
        have hqF : q ∉ E'.faulty := by
          rw [hE'f]; rintro (h | h)
          · exact hqB h.2
          · exact hqS h
        refine ⟨hqF, ?_⟩
        have := hX σ σ le_rfl q (Or.inl ⟨hqB, hqS⟩)
        have hqQ : q ≠ Q := fun h => hqB (h ▸ hQB)
        simp only [ref, hqQ, ↓reduceIte] at this
        rw [Run.out_of_correct A _ hqF, this, Run.out_of_correct A Eb hqB]
  -- `Q` decides some `vQ` in `E'_base`, hence in isolation
  obtain ⟨vQ, τQ, hτQ⟩ := hA.termination E' hE' hE'a Q hQE'
  have hiso : (isoRun (M := M) Q vstar).Decides A Q vQ := by
    refine ⟨τQ, ?_⟩
    have := hX τQ τQ le_rfl Q (Or.inr rfl)
    simp only [ref, ↓reduceIte] at this
    rw [← this]; exact hτQ
  -- Lemma 6 and Lemma 7
  obtain ⟨Rv, hRv, hcan, hQv, p, hp, v, hne, hv⟩ :=
    exists_run_decides_ne hU hA hnt ht (by omega) Q vQ (M := M)
  exact hne (eq_of_isoRun_decides hA hRv hcan hQv hp hv vstar hiso)

/-- **Theorem 4 (generalized Dolev–Reischuk bound)**, unauthenticated model. -/
theorem message_lower_bound [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (hnt : ¬ val.Trivial t) (ht : 0 < t) (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.gst = 0 ∧
      ∃ N, ((t + 1) / 2) * ((t + 1) / 2 + 1) ≤ R.msgsUpTo A N := by
  obtain ⟨R, hR, -, h⟩ := message_lower_bound_auth A.unforging_none (hA.auth _) hnt ht htn
  exact ⟨R, hR, h⟩

/-- **Theorem 4**, message-complexity form (authenticated model, which includes the
unauthenticated one via `Auth.none`): some execution has message complexity `> ⌈t/2⌉²`. -/
theorem message_complexity_lower_bound_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuth Au t δ A val)
    (hnt : ¬ val.Trivial t) (ht : 0 < t) (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.AuthValid Au A ∧
      ((((t + 1) / 2) ^ 2 : ℕ) : ℕ∞) < R.msgComplexity A := by
  obtain ⟨R, hR, hRa, -, N, hN⟩ := message_lower_bound_auth hU hA hnt ht htn
  refine ⟨R, hR, hRa, lt_of_lt_of_le ?_ (le_iSup (fun N => (R.msgsUpTo A N : ℕ∞)) N)⟩
  have hk : 0 < (t + 1) / 2 := by omega
  have hlt : ((t + 1) / 2) ^ 2 < (t + 1) / 2 * ((t + 1) / 2 + 1) := by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (by omega) hk
  exact_mod_cast lt_of_lt_of_le hlt hN

/-- **Theorem 4**, message-complexity form: some execution has message complexity
`> ⌈t/2⌉²`. -/
theorem message_complexity_lower_bound [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (hnt : ¬ val.Trivial t) (ht : 0 < t) (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ ((((t + 1) / 2) ^ 2 : ℕ) : ℕ∞) < R.msgComplexity A := by
  obtain ⟨R, hR, -, h⟩ :=
    message_complexity_lower_bound_auth A.unforging_none (hA.auth _) hnt ht htn
  exact ⟨R, hR, h⟩

end ValidityConsensus
