import Papers.PODC2018.Silence.LowerBounds

/-!
# Committing in mid-round (Appendix D of Goren–Moses): the model `γ̃_f` and lower bounds

In `γ̃_f` (the model of Guerraoui–Wang) a process may decide *in the middle of round `m + 1`*:
after its round-`m + 1` sending phase and before receiving. A process that performs a sending
action in its crashing round is guaranteed that the message is delivered. We model this with the
same runs as `γ_f` and a mid-round decision event `DecidesMid alg r p m d` ("decides at time
`m + ½`"): `p` is alive at time `m`, all its round-`m + 1` messages are delivered (so it did not
crash before completing its sending phase), and its decision function (applied to its state at time
`m`) returns `d`. "Deciding before time 2" means `m ≤ 1`.

Results:
* `silent_choir_mid`, `chain_to_correct_mid`: the Silent Choir Theorem / Lemma 4 for mid-round
  deciders (proved at the run level: KoP does not apply verbatim to mid-round decisions, because
  whether the decision is performed depends on the crash pattern, not only on the local state);
* `lemma16a`, `lemma16b` (Lemma 16), `corollary5`, `corollary6` (`n² + fn − n` messages).
-/

namespace Papers.PODC2018.Silence.MidRound

open Podc.SyncCrash Classical

variable {P M : Type*}

/-- `p` decides `d` in the middle of round `m + 1` (after its sending phase). -/
def DecidesMid (alg : ACProtocol P M) (r : Run P Bool) (p : P) (m : ℕ) (d : Decision) : Prop :=
  r.Alive p m ∧ (∀ q, q ≠ p → alg.send p (r.input p) (hist alg r m p) q ≠ none → r.Deliv p q m) ∧
    alg.decide p (r.input p) (hist alg r m p) = some d

/-- The AC conditions for mid-round decisions. -/
structure ACRunMid (alg : ACProtocol P M) (r : Run P Bool) : Prop where
  decision : ∀ i, ¬ r.Faulty i → ∃ m d, DecidesMid alg r i m d
  agreement : ∀ i m d i' m' d', DecidesMid alg r i m d → DecidesMid alg r i' m' d' → d = d'
  commit_validity : ∀ i m, DecidesMid alg r i m .commit → ∀ j, r.input j = true
  abort_validity : ∀ i m, DecidesMid alg r i m .abort →
    (∃ j, r.input j = false) ∨ ∃ j, r.Faulty j

/-- `alg` solves AC in `γ̃_f`. -/
def SolvesACMid [Fintype P] (alg : ACProtocol P M) (f : ℕ) : Prop :=
  ∀ r : Run P Bool, r.Admissible f → ACRunMid alg r

variable {alg : ACProtocol P M}

/-- A mid-round decision transfers to a run where the process has the same state and the same
crash pattern. -/
lemma DecidesMid.transfer {r r' : Run P Bool} {p : P} {m : ℕ} {d : Decision}
    (h : DecidesMid alg r p m d) (hs : state alg r' p m = state alg r p m)
    (hc : r'.crash p = r.crash p) (hre : r'.reach p = r.reach p) : DecidesMid alg r' p m d := by
  obtain ⟨ha, hdel, hdec⟩ := h
  have ha' : r'.Alive p m := fun c h' => ha c (hc ▸ h')
  rw [state_of_alive ha, state_of_alive ha'] at hs
  obtain ⟨hin, hh⟩ := Prod.mk.inj (Option.some.inj hs)
  refine ⟨ha', fun q hq hsend => ?_, by rw [hin, hh]; exact hdec⟩
  rw [hin, hh] at hsend
  have := hdel q hq hsend
  simpa only [Run.Deliv, Run.Alive, hc, hre] using this

lemma DecidesMid.of_nice [Fintype P] {f : ℕ} (hAC : SolvesACMid alg f) {i : P} {m : ℕ}
    {d : Decision} (h : DecidesMid alg nice i m d) : d = .commit := by
  cases d with
  | commit => rfl
  | abort =>
    rcases (hAC nice (nice_admissible f)).abort_validity i m h with ⟨j, hj⟩ | ⟨j, hj⟩
    · simp [nice] at hj
    · exact absurd hj (nice_not_faulty j)

variable [Fintype P] {f : ℕ}

/-- **Silent Choir Theorem for mid-round deciders**: if `i` commits in mid-round `m + 1` of a run
of an AC protocol for `γ̃_f` and no message chain from `j` reaches `i` by time `m`, then
`|F_r ∪ S_j^r(m − 1)| > f`. -/
theorem silent_choir_mid (hAC : SolvesACMid alg f) {r : Run P Bool} (hr : r.Admissible f)
    {i j : P} {m : ℕ} (h : DecidesMid alg r i m .commit) (hno : ¬ Chain alg r j 0 i m) :
    f < (r.faulty ∪ S alg r j (m - 1)).card := by
  by_contra hle
  push Not at hle
  have hS : ¬ Chain alg r j 0 i (m - 1) := fun hc => hno (hc.trans_le (by omega))
  have h' : DecidesMid alg (choirRun alg r j m) i m .commit :=
    h.transfer (state_choirRun hno) (by simp [choirRun, hS]) (by simp [choirRun, hS])
  have := (hAC _ (choirRun_admissible hr hle)).commit_validity i m h' j
  simp [choirRun] at this

/-- **Lemma 4 for mid-round deciders** (run level): if some process commits (in mid-round) in a run
of an AC protocol for `γ̃_f` (`f < n`), every `j` has a message chain to a correct process. -/
theorem chain_to_correct_mid (hAC : SolvesACMid alg f) (hfn : f < Fintype.card P)
    {r : Run P Bool} (hr : r.Admissible f) {i : P} {m : ℕ} (h : DecidesMid alg r i m .commit)
    (j : P) : ∃ z, ¬ r.Faulty z ∧ ∃ t, Chain alg r j 0 z t := by
  obtain ⟨z0, hz0⟩ := hr.exists_correct hfn
  obtain ⟨m', d, hd⟩ := (hAC r hr).decision z0 hz0
  obtain rfl : d = .commit := (hAC r hr).agreement _ _ _ _ _ _ hd h
  by_cases hc : Chain alg r j 0 z0 m'
  · exact ⟨z0, hz0, m', hc⟩
  · have hlt := silent_choir_mid hAC hr hd hc
    by_contra hno
    push Not at hno
    have hsub : r.faulty ∪ S alg r j (m' - 1) = r.faulty := by
      apply Finset.union_eq_left.2
      intro z hz
      rw [mem_S] at hz
      rw [Run.mem_faulty]
      by_contra hf
      exact hno z hf _ hz
    rw [hsub] at hlt
    exact absurd hr.1 (by omega)

/-- **Lemma 16(a)** of Goren–Moses: a process that decides before time `2` in the nice run of an AC
protocol for `γ̃_f` (`1 ≤ f < n`) decides in mid-round 2 (`m = 1`), after receiving a first-round
message from every other process. (The paper assumes `f > 1`; `f ≥ 1` suffices.) -/
theorem lemma16a (hAC : SolvesACMid alg f) (hf : 1 ≤ f) (hfn : f < Fintype.card P) {i : P}
    {m : ℕ} {d : Decision} (hm : m ≤ 1) (h : DecidesMid alg nice i m d) :
    m = 1 ∧ ∀ j, j ≠ i → Sent alg nice j i 0 := by
  obtain rfl := DecidesMid.of_nice hAC h
  have key : ∀ j, j ≠ i → Sent alg nice j i 0 ∧ 1 ≤ m := by
    intro j hji
    by_cases hc : Chain alg nice j 0 i m
    · obtain ⟨y, t', hcy, hs, ht⟩ := hc.exists_last (Ne.symm hji)
      obtain rfl : t' = 0 := by omega
      obtain rfl := hcy.eq_of_le le_rfl
      exact ⟨hs, by omega⟩
    · have hlt := silent_choir_mid hAC (nice_admissible f) h hc
      rw [nice_faulty, Finset.empty_union] at hlt
      have : S alg nice j (m - 1) ⊆ {j} := by
        intro z hz
        rw [mem_S] at hz
        rw [Finset.mem_singleton]
        exact hz.eq_of_le (by omega)
      have := Finset.card_le_card this
      simp at this
      omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  exact ⟨by have := (key j hj).2; omega, fun j hj => (key j hj).1⟩

/-- The processes to which `i` sends a round-2 message in the nice run. -/
noncomputable def R2 (alg : ACProtocol P M) (i : P) : Finset P :=
  Finset.univ.filter (fun q => Sent alg nice i q 1)

/-- The run of the proof of Lemma 16(b): values `1`; `j` crashes in round 1 reaching only `i`;
`i` crashes in round 2 after its sending phase (all its round-2 messages are delivered); the
processes of `T` crash in round 3 sending nothing. -/
noncomputable def run16 (i j : P) (T : Finset P) : Run P Bool where
  input _ := true
  crash z := if z = j then some 1 else if z = i then some 2 else if z ∈ T then some 3 else none
  reach z := if z = j then {i} else if z = i then Set.univ else ∅

/-- **Lemma 16(b)** of Goren–Moses: if `f > 1`, a process that decides before time `2` in the nice
run of an AC protocol for `γ̃_f` sends round-2 messages to at least `f` processes. -/
theorem lemma16b (hAC : SolvesACMid alg f) (hf : 2 ≤ f) (hfn : f < Fintype.card P) {i : P}
    {m : ℕ} {d : Decision} (hm : m ≤ 1) (h : DecidesMid alg nice i m d) :
    f ≤ (R2 alg i).card := by
  obtain ⟨rfl, -⟩ := lemma16a hAC (by omega) hfn hm h
  obtain rfl := DecidesMid.of_nice hAC h
  have hiR : i ∉ R2 alg i := by
    simp only [R2, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => h.ne rfl
  -- for every `j ≠ i`, at least `f − 1` round-2 recipients other than `j`
  have step : ∀ j, j ≠ i → f ≤ ((R2 alg i).erase j).card + 1 := by
    intro j hji
    by_contra hlt
    push Not at hlt
    set T := (R2 alg i).erase j with hT
    have hiT : i ∉ T := fun h => hiR (Finset.mem_of_mem_erase h)
    have hjT : j ∉ T := Finset.notMem_erase j _
    have hij : i ≠ j := Ne.symm hji
    let r' : Run P Bool := run16 i j T
    have hr' : r'.Admissible f := by
      refine ⟨?_, ?_⟩
      · have : r'.faulty ⊆ insert j (insert i T) := by
          intro z hz
          simp only [Run.mem_faulty, Run.Faulty, r', run16] at hz
          simp only [Finset.mem_insert]
          split_ifs at hz with h1 h2 h3 <;> simp_all
        exact (Finset.card_le_card this).trans
          ((Finset.card_insert_le _ _).trans (by
            have := Finset.card_insert_le i T; omega))
      · intro z c hc
        simp only [r', run16] at hc
        split_ifs at hc <;> (simp at hc; omega)
    have hist1 : hist alg r' 1 i = hist alg nice 1 i := by
      rw [hist_succ, hist_succ, hist_zero, hist_zero, List.nil_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, rfl⟩
      funext p
      refine msg_congr rfl (fun _ => ?_) ?_
      · rfl
      simp only [Run.Deliv, Run.Alive, r', run16, nice]
      by_cases hp : p = j <;> by_cases hp' : p = i <;> by_cases hp'' : p ∈ T <;> simp_all
    have hs : state alg r' i 1 = state alg nice i 1 := by
      have ha : r'.Alive i 1 := by intro c hc; simp [r', run16, hij] at hc; omega
      rw [state_of_alive ha, state_of_alive (nice_alive i 1), hist1]; rfl
    have hdec : DecidesMid alg r' i 1 .commit := by
      obtain ⟨-, -, hdec⟩ := h
      refine ⟨fun c hc => by simp [r', run16, hij] at hc; omega, fun q _ _ => ?_, ?_⟩
      · refine ⟨fun c hc => by simp [r', run16, hij] at hc; omega, ?_⟩
        simp [r', run16, hij]
      · rw [hist1]; exact hdec
    -- chains from `j` in `r'` stay inside `{j, i} ∪ T`
    have key : ∀ z t, Chain alg r' j 0 z t →
        z = j ∨ (z = i ∧ 1 ≤ t) ∨ (z ∈ T ∧ 2 ≤ t) := by
      intro z t hc
      generalize hs0 : (0 : ℕ) = s at hc
      induction hc with
      | refl _ => exact Or.inl rfl
      | snoc hc' hs' hle ih =>
        rename_i w v s0 t₀ t'
        rcases ih hs0 with rfl | ⟨rfl, ht1⟩ | ⟨hwT, ht2⟩
        · have h1 := hs'.le_crash (c := 1) (by simp [r', run16])
          have := h1.2 (by omega)
          simp only [r', run16, ite_true, Set.mem_singleton_iff] at this
          exact Or.inr (Or.inl ⟨this, by omega⟩)
        · have h1 := hs'.le_crash (c := 2) (by simp [r', run16, hij])
          obtain rfl : t₀ = 1 := by omega
          have hsn : Sent alg nice w v 1 := by
            have : msg alg r' w v 1 = msg alg nice w v 1 := by
              refine msg_congr rfl (fun _ => hist1) ?_
              simp only [Run.Deliv, Run.Alive, r', run16, nice, hij, ite_false, ite_true]
              constructor
              · intro _; simp
              · intro _; exact ⟨fun c hc => by simp at hc; omega, by simp⟩
            unfold Sent; rw [← this]; exact hs'
          by_cases hvj : v = j
          · exact Or.inl hvj
          · right; right
            refine ⟨?_, by omega⟩
            rw [hT, Finset.mem_erase]
            exact ⟨hvj, by simp [R2, hsn]⟩
        · have hwi : w ≠ i := fun h => hiT (h ▸ hwT)
          have hwj : w ≠ j := fun h => hjT (h ▸ hwT)
          have h1 := hs'.le_crash (c := 3) (by simp [r', run16, hwi, hwj, hwT])
          have := h1.2
          by_cases h3 : t₀ + 1 = 3
          · have := this h3; simp [r', run16, hwi, hwj] at this
          · omega
    obtain ⟨z, hz, t, hc⟩ := chain_to_correct_mid hAC hfn hr' hdec j
    apply hz
    rcases key z t hc with rfl | ⟨rfl, -⟩ | ⟨hzT, -⟩
    · simp [Run.Faulty, r', run16]
    · simp [Run.Faulty, r', run16, hij]
    · have hzi : z ≠ i := fun h => hiT (h ▸ hzT)
      have hzj : z ≠ j := fun h => hjT (h ▸ hzT)
      simp [Run.Faulty, r', run16, hzi, hzj, hzT]
  by_cases hne : (R2 alg i).Nonempty
  · obtain ⟨j, hj⟩ := hne
    have hji : j ≠ i := fun h => hiR (h ▸ hj)
    have := step j hji
    rw [Finset.card_erase_of_mem hj] at this
    have : 0 < (R2 alg i).card := Finset.card_pos.2 ⟨j, hj⟩
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
    have := step j hj
    rw [hne] at this
    simp at this
    omega

/-- **Corollary 5** of Goren–Moses: for `f > 1`, an AC protocol for `γ̃_f` cannot commit before time
`2` in the nice run without sending round-2 messages. -/
theorem corollary5 (hAC : SolvesACMid alg f) (hf : 2 ≤ f) (hfn : f < Fintype.card P) {i : P}
    {m : ℕ} {d : Decision} (hm : m ≤ 1) (h : DecidesMid alg nice i m d) :
    ∃ q, Sent alg nice i q 1 := by
  have := lemma16b hAC hf hfn hm h
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (by omega : 0 < (R2 alg i).card)
  exact ⟨q, by simpa [R2] using hq⟩

/-- **Corollary 6** of Goren–Moses: if `f > 1` and all processes decide before time `2` in the nice
run of an AC protocol for `γ̃_f`, at least `n(n − 1) + f n = n² + f n − n` messages are sent in the
nice run. -/
theorem corollary6 (hAC : SolvesACMid alg f) (hf : 2 ≤ f) (hfn : f < Fintype.card P)
    (hD : ∀ i, ∃ m ≤ 1, ∃ d, DecidesMid alg nice i m d) :
    ((Fintype.card P * (Fintype.card P - 1) + f * Fintype.card P : ℕ) : ℕ∞) ≤
      (msgs alg nice).encard := by
  let D1 : Finset (P × P × ℕ) := (Finset.univ : Finset P).offDiag.image (fun e => (e.1, e.2, 0))
  let D2 : Finset (P × P × ℕ) := Finset.univ.biUnion (fun i => (R2 alg i).image (fun q => (i, q, 1)))
  have hD1 : D1.card = Fintype.card P * (Fintype.card P - 1) := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by
      simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 hab.2.1), Finset.offDiag_card,
      Finset.card_univ, Nat.mul_sub_one]
  have hD2 : f * Fintype.card P ≤ D2.card := by
    rw [Finset.card_biUnion]
    · rw [mul_comm, ← smul_eq_mul, ← Finset.card_univ]
      apply Finset.card_nsmul_le_sum
      intro a _
      rw [Finset.card_image_of_injective _ (fun b c hbc => by simpa using hbc)]
      obtain ⟨m, hm, d, hd⟩ := hD a
      exact lemma16b hAC hf hfn hm hd
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e hea heb
      simp only [Finset.mem_image] at hea heb
      obtain ⟨x, -, rfl⟩ := hea
      obtain ⟨y, -, hy⟩ := heb
      exact hab (congrArg Prod.fst hy).symm
  have hdisj : Disjoint D1 D2 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [D1, D2, Finset.mem_image, Finset.mem_biUnion] at h1 h2
    obtain ⟨_, -, rfl⟩ := h1
    obtain ⟨_, -, _, -, hy⟩ := h2
    simp at hy
  have hsub : ((D1 ∪ D2 : Finset (P × P × ℕ)) : Set (P × P × ℕ)) ⊆ msgs alg nice := by
    intro e he
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at he
    rcases he with he | he
    · simp only [D1, Finset.mem_image, Finset.mem_offDiag, Finset.mem_univ, true_and] at he
      obtain ⟨⟨j, i⟩, hji, rfl⟩ := he
      obtain ⟨m, hm, d, hd⟩ := hD i
      exact (lemma16a hAC (by omega) hfn hm hd).2 j hji
    · simp only [D2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at he
      obtain ⟨i, q, hq, rfl⟩ := he
      exact (by simpa [R2] using hq : Sent alg nice i q 1)
  calc ((Fintype.card P * (Fintype.card P - 1) + f * Fintype.card P : ℕ) : ℕ∞)
      ≤ ((D1 ∪ D2).card : ℕ∞) := by
        rw [Finset.card_union_of_disjoint hdisj, hD1]; exact_mod_cast Nat.add_le_add_left hD2 _
    _ = ((D1 ∪ D2 : Finset (P × P × ℕ)) : Set (P × P × ℕ)).encard :=
        (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (msgs alg nice).encard := Set.encard_le_encard hsub

end Papers.PODC2018.Silence.MidRound
