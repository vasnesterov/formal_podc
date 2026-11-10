import Papers.PODC2022.AdaptiveBAFewerWords.BBModel

/-!
# Correctness of the repaired Algorithms 1 and 2 of [CKS22]

For the repaired relay rule (`Rule.fixed`: the leader relays any `BB_valid` value), `n ≥ 2t + 1`
(the paper: `n = 2t + 1`), `|F| ≤ t` and every unforgeability-respecting adversary:

* `vPh_valid`: correct processes hold only `⊥` or `BB_valid` values (requirement (2) of a phase);
* `lemma9`: a non-silent phase with a correct leader makes every correct process return a
  `BB_valid` value;
* `lemma10`: if all correct processes start phase `j` with a value, `QC_idk(j)` cannot be produced;
* `lemma11`: all correct processes enter the weak BA (line 9) with a `BB_valid` value;
* `lemma12_values`, `lemma12_avail`: if the sender is correct, the only `BB_valid` value that
  correct processes hold or the adversary can produce is `⟨v_sender⟩_sender` (for either rule);
* `theorem13` (Theorem 4 / 13): composed with any black-box weak BA (`WeakBASpec`), the BB decisions
  of lines 10-13 satisfy agreement, termination and BB validity.
-/

set_option linter.unusedSectionVars false

namespace Podc.AdaptiveBAFewerWords.BB

variable {n : ℕ} {V : Type} [DecidableEq V]

section lists

lemma bbValid_of_mem_initVals {s : Fin n} {ms : List (Msg n V)} {x : Item n V}
    (h : x ∈ initVals s ms) : bbValid s x = true := by
  simp only [initVals, List.mem_filterMap] at h
  obtain ⟨m, -, hm⟩ := h
  rcases m with (⟨s', v⟩ | j) | j | ⟨x', j⟩ | ⟨p, j⟩ | ⟨x', j⟩ <;> simp at hm
  obtain ⟨rfl, rfl⟩ := hm
  simp [bbValid]

lemma mem_relayVals {s : Fin n} {j : ℕ} {ms : List (Msg n V)} {x : Item n V} :
    x ∈ relayVals s j ms ↔ Msg.relay x j ∈ ms ∧ bbValid s x = true := by
  simp only [relayVals, List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, h⟩
    rcases m with x' | j' | ⟨x', j'⟩ | ⟨p, j'⟩ | ⟨x', j'⟩ <;> simp at h
    obtain ⟨⟨rfl, h1⟩, rfl⟩ := h
    exact ⟨hm, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, by simp [h2]⟩

lemma mem_replyVals {rule : Rule} {s : Fin n} {j : ℕ} {ms : List (Msg n V)} {x : Item n V} :
    x ∈ replyVals rule s j ms ↔ Msg.reply x j ∈ ms ∧ relayable rule s x = true := by
  simp only [replyVals, List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, h⟩
    rcases m with x' | j' | ⟨x', j'⟩ | ⟨p, j'⟩ | ⟨x', j'⟩ <;> simp at h
    obtain ⟨⟨rfl, h1⟩, rfl⟩ := h
    exact ⟨hm, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, by simp [h2]⟩

lemma mem_idkSigners {j : ℕ} {ms : List (Msg n V)} {p : Fin n} :
    p ∈ idkSigners j ms ↔ Msg.idk p j ∈ ms := by
  simp only [idkSigners, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, h⟩
    rcases m with x' | j' | ⟨x', j'⟩ | ⟨p', j'⟩ | ⟨x', j'⟩ <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact hm
  · intro h
    exact ⟨_, h, by simp⟩

lemma relayable_fixed (s : Fin n) (x : Item n V) : relayable .fixed s x = bbValid s x := rfl

lemma bbValid_of_relayable {rule : Rule} {s : Fin n} {x : Item n V}
    (h : relayable rule s x = true) : bbValid s x = true := by
  cases rule
  · rcases x with ⟨s', v⟩ | j <;> simp_all [relayable, bbValid]
  · exact h

lemma bbValid_of_pick {t : ℕ} {rule : Rule} {s : Fin n} {j : ℕ} {ms : List (Msg n V)}
    {x : Item n V} (h : pick t rule s j ms = some x) : bbValid s x = true := by
  unfold pick at h
  split at h
  · rename_i y hy
    cases h
    exact bbValid_of_relayable (mem_replyVals.mp (List.mem_of_mem_head? hy)).2
  · split_ifs at h
    cases h
    rfl

end lists

section run
variable [NeZero n] (t : ℕ) (rule : Rule) (sc : Scenario n V)

lemma vPh_succ (j : ℕ) : vPh t rule sc (j + 1) = step t rule sc (j + 1) (vPh t rule sc j) := rfl

lemma ret_valid {j : ℕ} {v : Fin n → Option (Item n V)} {w : Fin n} {x : Item n V}
    (h : ret t rule sc j v w = some x) : bbValid sc.sender x = true :=
  (mem_relayVals.mp (List.mem_of_mem_head? h)).2

/-- Requirement (2) of a phase: every value held (by any process, in particular by a correct one)
is `⊥` or `BB_valid`. -/
theorem vPh_valid (j : ℕ) (u : Fin n) (x : Item n V) (h : vPh t rule sc j u = some x) :
    bbValid sc.sender x = true := by
  induction j generalizing x with
  | zero => exact bbValid_of_mem_initVals (List.mem_of_mem_head? h)
  | succ j ih =>
    rw [vPh_succ, step] at h
    rcases hr : ret t rule sc (j + 1) (vPh t rule sc j) u with _ | y
    · rw [hr, Option.none_or] at h; exact ih _ h
    · rw [hr, Option.some_or] at h; cases h; exact ret_valid t rule sc hr

/-- Values are never reset to `⊥` (line 7). -/
lemma vPh_mono {j j' : ℕ} (hjj' : j ≤ j') (u : Fin n) (h : vPh t rule sc j u ≠ none) :
    vPh t rule sc j' u ≠ none := by
  induction hjj' with
  | refl => exact h
  | step _ ih =>
    rw [vPh_succ, step]
    rcases hr : ret t rule sc _ (vPh t rule sc _) u with _ | y
    · simpa using ih
    · simp

lemma reqOut_honest {j : ℕ} {v : Fin n → Option (Item n V)} {u w : Fin n} (hu : u ∉ sc.F) :
    reqOut sc j v u w = reqH j v u w := by simp [reqOut, hu]

lemma repOut_honest {j : ℕ} {v : Fin n → Option (Item n V)} {u w : Fin n} (hu : u ∉ sc.F) :
    repOut sc j v u w = repH sc j v u w := by simp [repOut, hu]

lemma relOut_honest {j : ℕ} {v : Fin n → Option (Item n V)} {u w : Fin n} (hu : u ∉ sc.F) :
    relOut t rule sc j v u w = relH t rule sc j v u w := by simp [relOut, hu]

/-- In a phase whose correct leader starts with `⊥`, every correct process answers the help
request (lines 17-21). -/
lemma repH_of_nonSilent {j : ℕ} {v : Fin n → Option (Item n V)} (hl : ldr j ∉ sc.F)
    (hv : v (ldr j) = none) (u : Fin n) :
    repH sc j v u (ldr j) = [answer j u (v u)] := by
  simp [repH, reqOut_honest sc hl, reqH, hv]

/-- The generic phase statement behind Lemma 9: in a phase whose correct leader starts with `⊥`,
the leader (with the repaired rule) broadcasts some `BB_valid` value. -/
lemma pick_isSome {j : ℕ} {v : Fin n → Option (Item n V)} (hn : 2 * t < n) (hF : sc.F.card ≤ t)
    (hl : ldr j ∉ sc.F) (hv : v (ldr j) = none)
    (hval : ∀ u x, v u = some x → bbValid sc.sender x = true) :
    ∃ y, pick t .fixed sc.sender j (inboxRep sc j v) = some y := by
  have hin : ∀ u, u ∉ sc.F → answer j u (v u) ∈ inboxRep sc j v := by
    intro u hu
    simp only [inboxRep, List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨u, by rw [repOut_honest sc hu, repH_of_nonSilent sc hl hv]; simp⟩
  unfold pick
  by_cases hex : ∃ u, u ∉ sc.F ∧ v u ≠ none
  · obtain ⟨u, hu, hvu⟩ := hex
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hvu
    have hmem : x ∈ replyVals .fixed sc.sender j (inboxRep sc j v) := by
      rw [mem_replyVals]
      refine ⟨?_, by rw [relayable_fixed]; exact hval u x hx⟩
      have := hin u hu
      rwa [hx] at this
    rcases hh : (replyVals Rule.fixed sc.sender j (inboxRep sc j v)).head? with _ | y
    · simp [List.head?_eq_none_iff] at hh; simp [hh] at hmem
    · exact ⟨y, rfl⟩
  · push Not at hex
    have hlen : t + 1 ≤ (idkSigners j (inboxRep sc j v)).length := by
      have hsub : Finset.univ.filter (· ∉ sc.F) ⊆ (idkSigners j (inboxRep sc j v)).toFinset := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rw [List.mem_toFinset, mem_idkSigners]
        have := hin u hu
        rwa [hex u hu] at this
      have h1 := Finset.card_le_card hsub
      rw [List.card_toFinset, List.Nodup.dedup (by unfold idkSigners; exact List.nodup_dedup _)]
        at h1
      have h2 : (Finset.univ.filter (· ∉ sc.F)).card = n - sc.F.card := by
        rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have : sc.F.card ≤ n := by simpa using Finset.card_le_univ sc.F
      omega
    split
    · exact ⟨_, rfl⟩
    · simp [hlen]

/-- **Lemma 9 of [CKS22]** (repaired rule, `n ≥ 2t + 1`, `|F| ≤ t`): if phase `j` is non-silent and
its leader is correct, then all correct processes return a valid value. -/
theorem lemma9 (hn : 2 * t < n) (hF : sc.F.card ≤ t) (j : ℕ) (hj : NonSilent t .fixed sc j) :
    ∀ w ∉ sc.F, ∃ x, ret t .fixed sc j (vPh t .fixed sc (j - 1)) w = some x ∧
      bbValid sc.sender x = true := by
  intro w _
  obtain ⟨hl, hv⟩ := hj
  obtain ⟨y, hy⟩ := pick_isSome t sc hn hF hl hv (vPh_valid t .fixed sc (j - 1))
  have hyv := bbValid_of_pick hy
  refine ⟨y, ?_, hyv⟩
  simp [ret, relOut_honest t _ sc hl, relH, hv, hy, relayVals, hyv]

/-- Only `p` itself sends `⟨idk, j⟩_p`, and only if it starts phase `j` with `⊥` (line 21). -/
lemma idk_mem_honOut {r : ℕ} {u w p : Fin n} {j : ℕ} (h : Msg.idk p j ∈ honOut t rule sc r u w) :
    u = p ∧ vPh t rule sc (j - 1) p = none := by
  unfold honOut at h
  split_ifs at h with h0 h1 h2 h3
  · simp only [initH] at h; split_ifs at h <;> simp at h
  · simp at h
  · simp only [reqH] at h; split_ifs at h <;> simp at h
  · simp only [repH] at h
    split_ifs at h with h4
    · simp only [List.mem_singleton] at h
      rcases hv : vPh t rule sc ((r + 2) / 3 - 1) u with _ | x <;> rw [hv] at h <;>
        simp [answer] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hv⟩
    · simp at h
  · simp only [relH] at h
    split_ifs at h <;> simp at h

/-- **Lemma 10 of [CKS22]** (`|F| ≤ t`, either rule): if all correct processes invoke phase `j` with
a value `≠ ⊥`, then the adversary can never produce an idk certificate `QC_idk(j)`. -/
theorem lemma10 (hF : sc.F.card ≤ t) (j : ℕ)
    (hall : ∀ u ∉ sc.F, vPh t rule sc (j - 1) u ≠ none) (r : ℕ) :
    ¬ ItemAvail t rule sc r (.qc j) := by
  rintro ⟨σ, hσ, hav⟩
  have hsub : σ ⊆ sc.F := by
    intro p hp
    rcases hav p hp with h | ⟨r', -, u, w, hu, hm⟩
    · exact h
    · obtain ⟨rfl, hv⟩ := idk_mem_honOut t rule sc hm
      exact absurd hv (hall u hu)
  have := Finset.card_le_card hsub
  omega

/-- The phase `j ∈ [1, n]` led by `w`. -/
def ledPhase (w : Fin n) : ℕ := if (w : ℕ) = 0 then n else w

lemma ledPhase_spec (w : Fin n) : 1 ≤ ledPhase w ∧ ledPhase w ≤ n ∧ ldr (ledPhase w) = w := by
  have hn := NeZero.pos n
  refine ⟨?_, ?_, ?_⟩
  · unfold ledPhase; split_ifs <;> omega
  · unfold ledPhase; split_ifs <;> omega
  · apply Fin.ext
    unfold ledPhase ldr
    split_ifs with h
    · simp [h]
    · exact Nat.mod_eq_of_lt w.isLt

/-- **Lemma 11 of [CKS22]** (repaired rule, `n ≥ 2t + 1`, `|F| ≤ t`): all correct processes execute
line 9 with a valid initial value. -/
theorem lemma11 (hn : 2 * t < n) (hF : sc.F.card ≤ t) :
    ∀ w ∉ sc.F, ∃ x, vEnd t .fixed sc w = some x ∧ bbValid sc.sender x = true := by
  intro w hw
  suffices h : vEnd t .fixed sc w ≠ none by
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨x, hx, vPh_valid t _ sc n w x hx⟩
  obtain ⟨h1, h2, hl⟩ := ledPhase_spec w
  apply vPh_mono t _ sc h2
  by_cases hv : vPh t .fixed sc (ledPhase w - 1) w = none
  · obtain ⟨x, hx, -⟩ :=
      lemma9 t sc hn hF (ledPhase w) ⟨by rw [hl]; exact hw, by rw [hl]; exact hv⟩ w hw
    have : ledPhase w = (ledPhase w - 1) + 1 := by omega
    rw [this, vPh_succ, step, ← this, hx]
    simp
  · exact vPh_mono t _ sc (by omega) w hv

lemma v0_of_correct_sender (hs : sc.sender ∉ sc.F) (w : Fin n) :
    v0 sc w = some (.signed sc.sender sc.inp) := by
  simp [v0, out0, hs, initH, initVals]

/-- If the sender is correct, every process holds a value after round 1, and keeps one. -/
lemma vPh_ne_none_of_correct_sender (hs : sc.sender ∉ sc.F) (j : ℕ) (u : Fin n) :
    vPh t rule sc j u ≠ none :=
  vPh_mono t rule sc (Nat.zero_le j) u (by simp [vPh, v0_of_correct_sender sc hs])

/-- **Lemma 12 of [CKS22]**, core (`|F| ≤ t`, either rule): if the sender is correct, the only
`BB_valid` value the adversary can ever produce is `⟨v_sender⟩_sender`. -/
theorem lemma12_avail (hF : sc.F.card ≤ t) (hs : sc.sender ∉ sc.F) {r : ℕ} {x : Item n V}
    (hx : ItemAvail t rule sc r x) (hv : bbValid sc.sender x = true) :
    x = .signed sc.sender sc.inp := by
  rcases x with ⟨s, v⟩ | j
  · simp only [bbValid, decide_eq_true_eq] at hv
    subst hv
    rcases hx with h | ⟨-, rfl⟩
    · exact absurd h hs
    · rfl
  · exact absurd hx
      (lemma10 t rule sc hF j (fun u _ => vPh_ne_none_of_correct_sender t rule sc hs _ u) r)

/-- **Lemma 12 of [CKS22]**, core (`|F| ≤ t`, either rule): if the sender is correct, every correct
process holds `⟨v_sender⟩_sender` after round 1 and after every phase. -/
theorem lemma12_values (hF : sc.F.card ≤ t) (hs : sc.sender ∉ sc.F)
    (hadv : AdvValid t rule sc) (j : ℕ) :
    ∀ u ∉ sc.F, vPh t rule sc j u = some (.signed sc.sender sc.inp) := by
  induction j with
  | zero => intro u _; exact v0_of_correct_sender sc hs u
  | succ j ih =>
    intro u hu
    rw [vPh_succ, step]
    rcases hr : ret t rule sc (j + 1) (vPh t rule sc j) u with _ | y
    · simp [ih u hu]
    · simp only [Option.some_or, Option.some.injEq]
      obtain ⟨hmem, hval⟩ := mem_relayVals.mp (List.mem_of_mem_head? hr)
      by_cases hl : ldr (n := n) (j + 1) ∈ sc.F
      · simp only [relOut, hl, ite_true] at hmem
        exact lemma12_avail t rule sc hF hs (hadv _ _ _ _ hl hu hmem) hval
      · rw [relOut_honest t rule sc hl] at hmem
        have hne := vPh_ne_none_of_correct_sender t rule sc hs j (ldr (j + 1))
        simp [relH, hne] at hmem

end run

section theorem13
variable [NeZero n] (t : ℕ) (rule : Rule) (sc : Scenario n V)

/-- The values that *exist* in the weak BA run (Section 3): the inputs of correct processes and the
`BB_valid` items the adversary can produce. (After the phases correct processes sign no further
`⟨idk, ·⟩` shares, so the adversary's power does not grow during the weak BA.) -/
def Ex : Set (Item n V) :=
  {x | (∃ u ∉ sc.F, vEnd t rule sc u = some x) ∨ ∃ r, ItemAvail t rule sc r x}

/-- The black-box weak BA of line 9 with predicate `valid`, values existing in the run `Ex`,
correct processes `C`, inputs `inp` (`none` = `⊥`) and decisions `dec` (`none` = undecided,
`some none` = `⊥`): if all correct inputs are valid, it satisfies agreement, termination and
unique validity (Definition 3), and a correct process decides only `⊥` or a value that exists in the
run (an assumption not contained in Definition 3, but needed by Lemma 12; it follows from
unforgeability for any real protocol). -/
def WeakBASpec {P W : Type*} (valid : W → Prop) (Ex : Set W) (C : Set P) (inp : P → Option W)
    (dec : P → Option (Option W)) : Prop :=
  (∀ p ∈ C, ∃ x, inp p = some x ∧ valid x) →
    Agreement C dec ∧ Termination C dec ∧ UniqueValidity valid Ex C dec ∧
      ∀ p ∈ C, ∀ x, dec p = some (some x) → x ∈ Ex

/-- The BB decisions of lines 10-13 given the weak BA decisions. -/
def bbDec (decBA : Fin n → Option (Option (Item n V))) (u : Fin n) : Option (Option V) :=
  (decBA u).map (bbOut sc.sender)

/-- **Theorem 4 / Theorem 13 of [CKS22]** (repaired rule, `n ≥ 2t + 1`, `|F| ≤ t`, unforgeability):
Algorithm 1 composed with any weak BA solves Byzantine Broadcast — the BB decisions (lines 10-13)
satisfy agreement, termination and validity. Decisions are in `Option V`, `none` being `⊥`. -/
theorem theorem13 (hn : 2 * t < n) (hF : sc.F.card ≤ t) (hadv : AdvValid t .fixed sc)
    (decBA : Fin n → Option (Option (Item n V)))
    (hBA : WeakBASpec (fun x => bbValid sc.sender x = true) (Ex t .fixed sc) {u | u ∉ sc.F}
      (vEnd t .fixed sc) decBA) :
    Agreement {u | u ∉ sc.F} (bbDec sc decBA) ∧ Termination {u | u ∉ sc.F} (bbDec sc decBA) ∧
      BBValidity {u | u ∉ sc.F} sc.sender (some sc.inp) (bbDec sc decBA) := by
  obtain ⟨hAg, hTe, hUV, hExi⟩ := hBA (lemma11 t sc hn hF)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp q hq a b ha hb
    simp only [bbDec, Option.map_eq_some_iff] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [hAg p hp q hq a' b' ha' hb']
  · intro p hp
    obtain ⟨a, ha⟩ := hTe p hp
    exact ⟨bbOut sc.sender a, by simp [bbDec, ha]⟩
  · intro hs p hp
    have hs' : sc.sender ∉ sc.F := hs
    -- every valid existing value is `⟨v_sender⟩_sender`
    have huniq : ∀ x ∈ Ex t .fixed sc, bbValid sc.sender x = true →
        x = .signed sc.sender sc.inp := by
      rintro x (⟨u, hu, hx⟩ | ⟨r, hx⟩) hv
      · have := lemma12_values t .fixed sc hF hs' hadv n u hu
        rw [vEnd, this] at hx
        exact (Option.some.inj hx).symm
      · exact lemma12_avail t .fixed sc hF hs' hx hv
    obtain ⟨d, hd⟩ := hTe p hp
    have hu := hUV p hp d hd
    rcases d with _ | x
    · obtain ⟨a, ha, b, hb, hva, hvb, hab⟩ := hu
      exact absurd ((huniq a ha hva).trans (huniq b hb hvb).symm) hab
    · rw [huniq x (hExi p hp x hd) hu] at hd
      simp [bbDec, hd, bbOut]

end theorem13

end Podc.AdaptiveBAFewerWords.BB
