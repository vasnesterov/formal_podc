import Papers.PODC2023.ValidityConsensus.Triviality
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod

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
  classical
  let τ₀ : P × P → ℕ := fun pq => if hh : ∃ τ, f τ pq.1 pq.2 ≠ 0 then Classical.choose hh else 0
  let N := (univ : Finset (P × P)).sup τ₀ + 1
  refine ⟨N, ?_⟩
  have key : ∀ p q, (if ∃ τ, f τ p q ≠ 0 then 1 else 0) ≤ ∑ τ ∈ range N, f τ p q := by
    intro p q
    split_ifs with hh
    · have hlt : τ₀ (p, q) < N := Nat.lt_succ_of_le (le_sup (f := τ₀) (mem_univ (p, q)))
      have hτ : τ₀ (p, q) = Classical.choose hh := by simp [τ₀, hh]
      calc 1 ≤ f (τ₀ (p, q)) p q := by
              rw [hτ]; exact Nat.one_le_iff_ne_zero.mpr (Classical.choose_spec hh)
        _ ≤ ∑ τ ∈ range N, f τ p q :=
              single_le_sum (f := fun τ => f τ p q) (fun _ _ => Nat.zero_le _) (mem_range.mpr hlt)
    · exact Nat.zero_le _
  calc B.card * (B.card + 1) = ∑ _Q ∈ B, (B.card + 1) := by simp
    _ ≤ ∑ Q ∈ B, (univ.filter fun p => p ∉ B ∧ ∃ τ, f τ p Q ≠ 0).card := sum_le_sum h
    _ = ∑ Q ∈ B, ∑ p ∈ univ.filter (· ∉ B), (if ∃ τ, f τ p Q ≠ 0 then 1 else 0) := by
        refine sum_congr rfl fun Q _ => ?_
        rw [card_eq_sum_ones, sum_filter, sum_filter]
        refine sum_congr rfl fun p _ => ?_
        by_cases hp : p ∈ B <;> simp [hp]
    _ = ∑ p ∈ univ.filter (· ∉ B), ∑ Q ∈ B, (if ∃ τ, f τ p Q ≠ 0 then 1 else 0) := sum_comm
    _ ≤ ∑ p ∈ univ.filter (· ∉ B), ∑ Q ∈ univ.filter (· ≠ p), ∑ τ ∈ range N, f τ p Q := by
        refine sum_le_sum fun p _ => ?_
        calc ∑ Q ∈ B, (if ∃ τ, f τ p Q ≠ 0 then 1 else 0)
            ≤ ∑ Q ∈ B, ∑ τ ∈ range N, f τ p Q := sum_le_sum fun Q _ => key p Q
          _ ≤ ∑ Q ∈ univ.filter (· ≠ p), ∑ τ ∈ range N, f τ p Q := by
              refine sum_le_sum_of_subset_of_nonneg (fun Q hQ => ?_) fun _ _ _ => Nat.zero_le _
              have hp : p ∉ B := (mem_filter.mp ‹p ∈ univ.filter (· ∉ B)›).2
              exact mem_filter.mpr ⟨mem_univ _, fun h => hp (h ▸ hQ)⟩
    _ = ∑ τ ∈ range N, ∑ p ∈ univ.filter (· ∉ B), ∑ q ∈ univ.filter (· ≠ p), f τ p q := by
        rw [Finset.sum_comm (s := range N)]
        refine sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm (s := range N)]

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
decisions have happened, and make `Q` correct. -/
theorem eq_of_isoRun_decides (hA : SolvesConsensusAuth Au t δ A val) {R : Run P M VI}
    (hR : R.Valid t δ) (hcan : R.Canonical) {Q : P} (hQ : Q ∈ R.faulty) {p : P}
    (hp : p ∉ R.faulty) {v : VO} (hv : R.Decides A p v) (vstar : VI) {vQ : VO}
    (hiso : (isoRun (M := M) Q vstar).Decides A Q vQ) : v = vQ := by
  obtain ⟨τv, hτv⟩ := hv
  obtain ⟨τQ, hτQ⟩ := hiso
  set T := max τv τQ
  let R' : Run P M VI :=
    { faulty := R.faulty.erase Q
      inp := fun r => if r = Q then vstar else R.inp r
      gst := T + 1
      byz := R.byz
      dl := fun q τ r => if τ ≤ T then
          (if q = Q ∧ r = Q then τ
           else if q ∉ R.faulty ∧ r ∉ R.faulty then min (R.dl q τ r) (T + 1) else T + 1)
        else τ }
  have hR'f : ∀ r, r ∈ R'.faulty ↔ r ≠ Q ∧ r ∈ R.faulty := by simp [R']
  have hR' : R'.Valid t δ := by
    refine ⟨?_, ?_, ?_⟩
    · exact (card_erase_le).trans hR.card_faulty
    · intro q τ r hq hr
      simp only [R']
      split_ifs with h0 h1 h2
      · exact le_rfl
      · exact le_min (hR.dl_ge q τ r h2.1 h2.2) (by omega)
      · omega
      · exact le_rfl
    · intro q τ r _ _
      simp only [R']
      split_ifs <;> omega
  have hpQ : p ≠ Q := fun h => hp (h ▸ hQ)
  -- the correct processes of `R` cannot distinguish `R'` from `R` up to `T`
  have h₁ : ∀ τ ≤ T, ∀ r ∈ {r | r ∉ R.faulty}, R'.st A τ r = R.st A τ r := by
    refine R'.st_eq_of_inbox_eq A (ref := fun _ => R) ?_ ?_
    · intro r hr
      have : r ≠ Q := fun h => hr (h ▸ hQ)
      simp [R', this]
    · intro τ hτ ih r hr
      have hr : r ∉ R.faulty := hr
      have hrQ : r ≠ Q := fun h => hr (h ▸ hQ)
      refine R'.inbox_eq_of_dlv_eq A fun q τ' hτ' => ?_
      by_cases hq : q ∈ R.faulty
      · rw [R'.dlv_eq_nil_of_ne A (by simp [R', hq, hrQ, show τ' ≤ T by omega]; omega)]
        simp [Run.dlv, Run.out_eq_nil_of_canonical A hcan hq]
      · have hqQ : q ≠ Q := fun h => hq (h ▸ hQ)
        have hdl : R'.dl q τ' r = min (R.dl q τ' r) (T + 1) := by
          simp [R', hq, hr, hqQ, show τ' ≤ T by omega]
        have hiff : (min (R.dl q τ' r) (T + 1) = τ) ↔ R.dl q τ' r = τ := by omega
        simp only [Run.dlv, hdl, hiff]
        split_ifs
        · rw [Run.out_of_correct A _ (by simp [hR'f, hq]), Run.out_of_correct A _ hq,
            ih q hq τ' hτ']
        · rfl
  -- `Q` cannot distinguish `R'` from running in isolation up to `T`
  have h₂ : ∀ τ ≤ T, ∀ r ∈ ({Q} : Set P), R'.st A τ r = (isoRun (M := M) Q vstar).st A τ r := by
    refine R'.st_eq_of_inbox_eq A (ref := fun _ => isoRun Q vstar) ?_ ?_
    · rintro r rfl; simp [R', isoRun]
    · intro τ hτ ih r hr
      simp only [Set.mem_singleton_iff] at hr
      subst r
      refine R'.inbox_eq_of_dlv_eq A fun q τ' hτ' => ?_
      by_cases hqQ : q = Q
      · rw [hqQ]
        have hdl : R'.dl Q τ' Q = τ' := by simp [R', show τ' ≤ T by omega]
        have hdl' : (isoRun (M := M) Q vstar).dl Q τ' Q = τ' := rfl
        simp only [Run.dlv, hdl, hdl']
        split_ifs
        · rw [Run.out_of_correct A _ (by simp [hR'f]),
            Run.out_of_correct A _ (isoRun_correct Q vstar), ih Q rfl τ' hτ']
        · rfl
      · rw [R'.dlv_eq_nil_of_ne A (by simp [R', hqQ, hQ, show τ' ≤ T by omega]; omega)]
        simp [Run.dlv, Run.out_eq_nil_of_canonical A (isoRun_canonical Q vstar)
          (show q ∈ (isoRun (M := M) Q vstar).faulty by simp [isoRun, hqQ])]
  have hR'a : R'.AuthValid Au A := Run.authValid_of_canonical fun q hq τ r =>
    hcan q ((hR'f q).1 hq).2 τ r
  refine hA.agreement R' hR' hR'a p (by simp [hR'f, hp]) Q (by simp [hR'f]) v vQ ⟨τv, ?_⟩ ⟨τQ, ?_⟩
  · rw [h₁ τv (le_max_left _ _) p hp]; exact hτv
  · rw [h₂ τQ (le_max_right _ _) Q rfl]; exact hτQ

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
