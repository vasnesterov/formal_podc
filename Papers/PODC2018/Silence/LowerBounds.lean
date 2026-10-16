import Papers.PODC2018.Silence.SilentChoir

/-!
# Lower bounds on AC in the common case (§4.1 of Goren–Moses)

* `lemma3`: if every process has message chains to at least `k > 0` others, at least `n + k − 1`
  messages are sent;
* `corollary1` (Hadzilacos): a committing process knows `all[1]`;
* `lemma4`: a committing process knows that every `j` has a message chain to a correct process;
* `theorem3a` … `theorem3d`: the tradeoff between decision time `D` and message count `M` in nice
  runs; `theorem3_D1`: the missing case `D = 1` (`M ≥ n(n − 1)`);
* `corollary3`: message-optimal AC protocols use silence when `f < n − 1`.
-/

namespace Papers.PODC2018.Silence

open Cslib.SyncCrash Classical

variable {P M : Type*} [Fintype P]

section Lemma3

variable {I O : Type*} {alg : Cslib.Byzantine.LockStep.Protocol P I M O}

/-- **Lemma 3** of Goren–Moses. If in the run `r` every process has message chains to at least
`k > 0` other processes, then at least `n + k − 1` messages are sent in `r`.

(Our proof replaces the paper's "minimal rank" argument by "the process whose first message is
sent last"; this also covers infinite runs.) -/
theorem lemma3 [Nonempty P] (r : Run P I) {k : ℕ} (hk : 0 < k)
    (h : ∀ j : P, k ≤ (Finset.univ.filter (fun z => z ≠ j ∧ ∃ t, Chain alg r j 0 z t)).card) :
    ((Fintype.card P + k - 1 : ℕ) : ℕ∞) ≤ (msgs alg r).encard := by
  -- every process sends some message
  have hsend : ∀ j : P, ∃ t z, Sent alg r j z t := by
    intro j
    obtain ⟨z, hz⟩ := Finset.card_pos.1 (lt_of_lt_of_le hk (h j))
    simp only [Finset.mem_filter] at hz
    obtain ⟨t, ht⟩ := hz.2.2
    obtain ⟨y, t', hs, -, -⟩ := ht.exists_first hz.2.1
    exact ⟨t', y, hs⟩
  let first : P → ℕ := fun j => Nat.find (hsend j)
  obtain ⟨h0, -, hmax⟩ := Finset.exists_max_image Finset.univ first Finset.univ_nonempty
  have hfirst : ∀ j, ∃ z, Sent alg r j z (first j) := fun j => Nat.find_spec (hsend j)
  choose zz hzz using hfirst
  -- the first messages of the processes `j ≠ h0` are not on chains from `h0`
  have hnot : ∀ j, j ≠ h0 → ¬ Chain alg r h0 0 j (first j) := by
    intro j hj hc
    obtain ⟨y, t', hs, -, ht'⟩ := hc.exists_first hj
    have h1 : first h0 ≤ t' := Nat.find_min' (hsend h0) ⟨y, hs⟩
    have h2 : first j ≤ first h0 := hmax j (Finset.mem_univ _)
    omega
  -- the last messages of chains from `h0`
  have hlast : ∀ x, x ≠ h0 → (∃ t, Chain alg r h0 0 x t) →
      ∃ y t, Chain alg r h0 0 y t ∧ Sent alg r y x t := by
    rintro x hx ⟨t, ht⟩
    obtain ⟨y, t', h1, h2, -⟩ := ht.exists_last hx
    exact ⟨y, t', h1, h2⟩
  let X := Finset.univ.filter (fun z => z ≠ h0 ∧ ∃ t, Chain alg r h0 0 z t)
  have hX : ∀ x ∈ X, ∃ y t, Chain alg r h0 0 y t ∧ Sent alg r y x t := by
    intro x hx
    simp only [X, Finset.mem_filter] at hx
    exact hlast x hx.2.1 hx.2.2
  choose! yy tt hyy using hX
  let A : Finset (P × P × ℕ) := (Finset.univ.erase h0).image (fun j => (j, zz j, first j))
  let B : Finset (P × P × ℕ) := X.image (fun x => (yy x, x, tt x))
  have hA : A.card = Fintype.card P - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hB : B.card = X.card := by
    apply Finset.card_image_of_injOn
    intro a _ b _ hab
    simpa using congrArg (fun e => e.2.1) hab
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    simp only [A, B, Finset.mem_image, Finset.mem_erase] at heA heB
    obtain ⟨j, ⟨hj, -⟩, rfl⟩ := heA
    obtain ⟨x, hx, hxe⟩ := heB
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨h1, -, h3⟩ := hxe
    have := (hyy x hx).1
    rw [h1, h3] at this
    exact hnot j hj this
  have hsub : ((A ∪ B : Finset (P × P × ℕ)) : Set (P × P × ℕ)) ⊆ msgs alg r := by
    intro e he
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, A, B, Finset.mem_image] at he
    rcases he with ⟨j, -, rfl⟩ | ⟨x, hx, rfl⟩
    · exact hzz j
    · exact (hyy x hx).2
  have hcard : Fintype.card P + k - 1 ≤ (A ∪ B).card := by
    rw [Finset.card_union_of_disjoint hdisj, hA, hB]
    have : k ≤ X.card := h h0
    have : 0 < Fintype.card P := Fintype.card_pos
    omega
  calc ((Fintype.card P + k - 1 : ℕ) : ℕ∞) ≤ ((A ∪ B).card : ℕ∞) := by exact_mod_cast hcard
    _ = ((A ∪ B : Finset (P × P × ℕ)) : Set (P × P × ℕ)).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (msgs alg r).encard := Set.encard_le_encard hsub

end Lemma3

section AC

variable {alg : ACProtocol P M} {f : ℕ}

/-- The fact `all[1]`: all initial values are `1`. -/
def AllOne (r : Run P Bool) : Prop := ∀ j, r.input j = true

/-- **Corollary 1** (Hadzilacos): when a process commits in a run of an AC protocol, it knows
`all[1]`. -/
theorem corollary1 (hAC : SolvesAC alg f) {r : Run P Bool} (hr : r.Admissible f) {i : P} {m : ℕ}
    (h : DecidesAt alg r i m .commit) : Knows alg f i m r AllOne :=
  kop (fun r' hr' m' hp => (hAC r' hr').commit_validity i m' hp) h

/-- The run-level content of Lemma 4: if some process commits in a run of an AC protocol (with
`f < n`), every process `j` has a message chain to some correct process. -/
theorem chain_to_correct (hAC : SolvesAC alg f) (hfn : f < Fintype.card P) {r : Run P Bool}
    (hr : r.Admissible f) {i : P} {m : ℕ} (h : DecidesAt alg r i m .commit) (j : P) :
    ∃ z, ¬ r.Faulty z ∧ ∃ t, Chain alg r j 0 z t := by
  obtain ⟨z0, hz0⟩ := hr.exists_correct hfn
  obtain ⟨m', d, hd⟩ := (hAC r hr).decision z0 hz0
  obtain rfl : d = .commit := (hAC r hr).agreement _ _ _ _ _ _ hd h
  have hK : Knows alg f z0 m' r (fun r' => r'.input j = true) :=
    (corollary1 hAC hr hd).mono (fun r' _ h' => h' j)
  by_cases hc : Chain alg r j 0 z0 m'
  · exact ⟨z0, hz0, m', hc⟩
  · obtain ⟨-, hlt⟩ := silent_choir_at hr hK hc
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

/-- **Lemma 4** of Goren–Moses: when a process `i` commits in a run of an AC protocol, it knows that,
for every `j`, the run contains a message chain from `j` to some correct process. -/
theorem lemma4 (hAC : SolvesAC alg f) (hfn : f < Fintype.card P) {r : Run P Bool}
    (hr : r.Admissible f) {i : P} {m : ℕ} (h : DecidesAt alg r i m .commit) :
    Knows alg f i m r (fun r' => ∀ j, ∃ z, ¬ r'.Faulty z ∧ ∃ t, Chain alg r' j 0 z t) :=
  kop (fun r' hr' _ hp j => chain_to_correct hAC hfn hr' hp j) h

lemma nice_faulty : (nice : Run P Bool).faulty = ∅ := by
  ext z; simp [nice_not_faulty]

/-- **Theorem 3(a)** of Goren–Moses: an AC protocol for `γ_f` (`1 ≤ f < n`) sends at least
`n + f − 1` messages in its nice run. -/
theorem theorem3a (hAC : SolvesAC alg f) (hf : 1 ≤ f) (hfn : f < Fintype.card P) :
    ((Fintype.card P + f - 1 : ℕ) : ℕ∞) ≤ (msgs alg nice).encard := by
  haveI : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  apply lemma3 nice hf
  intro j
  by_cases hall : ∀ z, z ≠ j → ∃ t, Chain alg nice j 0 z t
  · have : Finset.univ.filter (fun z => z ≠ j ∧ ∃ t, Chain alg nice j 0 z t) =
        Finset.univ.erase j := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      exact ⟨fun h => h.1, fun h => ⟨h, hall z h⟩⟩
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  · push Not at hall
    obtain ⟨i, hij, hi⟩ := hall
    obtain ⟨m, hm⟩ := nice_exists_commit hAC i
    have hK : Knows alg f i m nice (fun r' => r'.input j = true) :=
      (corollary1 hAC (nice_admissible f) hm).mono (fun r' _ h' => h' j)
    obtain ⟨-, hlt⟩ := silent_choir_at (nice_admissible f) hK (hi m)
    rw [nice_faulty, Finset.empty_union] at hlt
    have hj : j ∈ S alg nice j (m - 1) := by rw [mem_S]; exact Chain.refl (Nat.zero_le _)
    have hsub : (S alg nice j (m - 1)).erase j ⊆
        Finset.univ.filter (fun z => z ≠ j ∧ ∃ t, Chain alg nice j 0 z t) := by
      intro z hz
      rw [Finset.mem_erase, mem_S] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz.1, _, hz.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hj] at this
    omega

/-- The run of the proof of Theorem 3(b): all values `1`; `j` crashes in round 1 sending only to
`i`; `i` crashes in round 2 sending nothing. -/
noncomputable def run3b (i j : P) : Run P Bool where
  input _ := true
  crash z := if z = j then some 1 else if z = i then some 2 else none
  reach z := if z = j then {i} else ∅

/-- **Theorem 3(b)** of Goren–Moses: if `f > 1` (and `f < n`), no process decides before time `2` in
the nice run of an AC protocol; in particular `D > 1`. -/
theorem theorem3b (hAC : SolvesAC alg f) (hf : 2 ≤ f) (hfn : f < Fintype.card P) {i : P}
    {m : ℕ} {d : Decision} (h : DecidesAt alg nice i m d) : 2 ≤ m := by
  obtain rfl := nice_decides_commit hAC i h
  by_contra hm
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  have hij : i ≠ j := Ne.symm hji
  -- `r'` is admissible
  have hr' : (run3b i j : Run P Bool).Admissible f := by
    refine ⟨?_, ?_⟩
    · have : (run3b i j : Run P Bool).faulty ⊆ {i, j} := by
        intro z hz
        simp only [Run.mem_faulty, Run.Faulty, run3b] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        split_ifs at hz with h1 h2 <;> simp_all
      exact (Finset.card_le_card this).trans (Finset.card_le_two.trans hf)
    · intro z c hc
      simp only [run3b] at hc
      split_ifs at hc <;> (simp at hc; omega)
  -- `i` cannot distinguish `r'` from the nice run at time `m ≤ 1`
  have hs : state alg (run3b i j) i m = state alg nice i m := by
    have ha : (run3b i j : Run P Bool).Alive i m := by
      intro c hc; simp [run3b, hij] at hc; omega
    rw [state_of_alive ha, state_of_alive (nice_alive i m)]
    suffices hh : hist alg (run3b i j) m i = hist alg nice m i by rw [hh]; rfl
    interval_cases m
    · rfl
    · rw [hist_succ, hist_succ, hist_zero, hist_zero, List.nil_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, rfl⟩
      funext p
      refine msg_congr rfl (fun _ => ?_) ?_
      · rfl
      simp only [Run.Deliv, Run.Alive, run3b, nice]
      by_cases hp : p = j <;> by_cases hp' : p = i <;> simp_all
  have hdec : DecidesAt alg (run3b i j) i m .commit := Performs.of_state_eq h hs
  obtain ⟨z, hz, t, hc⟩ := chain_to_correct hAC hfn hr' hdec j
  -- chains from `j` in `r'` only reach `j` and `i`
  have key : ∀ z t, Chain alg (run3b i j) j 0 z t → z = j ∨ z = i := by
    intro z t hc
    generalize hs0 : (0 : ℕ) = s at hc
    induction hc with
    | refl _ => exact Or.inl rfl
    | snoc hc' hs' hle ih =>
      rename_i y z' t₀ _
      rcases ih hs0 with rfl | rfl
      · have := hs'.le_crash (c := 1) (by simp [run3b])
        right
        have h2 := this.2 (by omega)
        simpa [run3b] using h2
      · have h1 := hs'.le_crash (c := 2) (by simp [run3b, hij])
        have := hc'.lt_of_ne hij
        have h2 := h1.2
        by_cases ht : t₀ + 1 = 2
        · have := h2 ht; simp [run3b, hij] at this
        · omega
  have hzf : (run3b i j : Run P Bool).Faulty z := by
    rcases key z t hc with rfl | rfl
    · simp [Run.Faulty, run3b]
    · simp [Run.Faulty, run3b, hij]
  exact hz hzf

/-- The processes to which `i` sends a message in the first two rounds of the nice run. -/
noncomputable def T2 (alg : ACProtocol P M) (i : P) : Finset P :=
  Finset.univ.filter (fun z => Sent alg nice i z 0 ∨ Sent alg nice i z 1)

/-- The run of the proof of Theorem 3(c): all values `1`; `i` crashes in round `m + 1` (right after
deciding at time `m`) sending nothing; every `h ∈ T` crashes in round 2 sending only to `i`. -/
noncomputable def run3c (i : P) (T : Finset P) (m : ℕ) : Run P Bool where
  input _ := true
  crash z := if z = i then some (m + 1) else if z ∈ T then some 2 else none
  reach z := if z = i then ∅ else {i}

/-- The key step of Theorem 3(c): a process that decides by time `2` in the nice run sends messages
to at least `f` processes in the first two rounds. -/
theorem card_T2 (hAC : SolvesAC alg f) (hfn : f < Fintype.card P) {i : P} {m : ℕ} {d : Decision}
    (hm : m ≤ 2) (h : DecidesAt alg nice i m d) : f ≤ (T2 alg i).card := by
  obtain rfl := nice_decides_commit hAC i h
  by_contra hlt
  push Not at hlt
  set T := T2 alg i with hT
  have hiT : i ∉ T := by simp [hT, T2, fun t => (show ¬ Sent alg nice i i t from fun h => h.ne rfl)]
  let r' : Run P Bool := run3c i T m
  have hr' : r'.Admissible f := by
    refine ⟨?_, ?_⟩
    · have : r'.faulty ⊆ insert i T := by
        intro z hz
        simp only [Run.mem_faulty, Run.Faulty, r', run3c] at hz
        simp only [Finset.mem_insert]
        split_ifs at hz with h1 h2 <;> simp_all
      exact (Finset.card_le_card this).trans ((Finset.card_insert_le _ _).trans (by omega))
    · intro z c hc
      simp only [r', run3c] at hc
      split_ifs at hc <;> (simp at hc; omega)
  -- in round 1 everything is as in the nice run (if `m ≥ 1`)
  have hist1 : 1 ≤ m → ∀ p, hist alg r' 1 p = hist alg nice 1 p := by
    intro hm1
    refine fun p => hist_congr (alg := alg) (r := r') (r' := nice) (T := 1) (fun _ => rfl)
      (fun t ht p q => ?_) 1 le_rfl p
    obtain rfl : t = 0 := by omega
    simp only [Run.Deliv, Run.Alive, r', run3c, nice]
    by_cases hp : p = i <;> by_cases hp' : p ∈ T <;> simp_all <;> omega
  have histi : ∀ t ≤ 1, t < m → hist alg r' t i = hist alg nice t i := by
    intro t ht htm
    interval_cases t
    · rfl
    · exact hist1 (by omega) i
  have hs : state alg r' i m = state alg nice i m := by
    have ha : r'.Alive i m := by intro c hc; simp [r', run3c] at hc; omega
    rw [state_of_alive ha, state_of_alive (nice_alive i m)]
    suffices hh : hist alg r' m i = hist alg nice m i by rw [hh]; rfl
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
    · rfl
    · exact hist1 le_rfl i
    · rw [hist_succ r' 1 i, hist_succ nice 1 i, hist1 (by omega) i]
      congr 2
      funext p
      refine msg_congr rfl (fun _ => hist1 (by omega) p) ?_
      simp only [Run.Deliv, Run.Alive, r', run3c, nice]
      by_cases hp : p = i <;> by_cases hp' : p ∈ T <;> simp_all
  have hdec : DecidesAt alg r' i m .commit := Performs.of_state_eq h hs
  -- chains from `i` in `r'` only reach `i` and `T`
  have key : ∀ z t, Chain alg r' i 0 z t → z = i ∨ (z ∈ T ∧ 1 ≤ t) := by
    intro z t hc
    generalize hs0 : (0 : ℕ) = s at hc
    induction hc with
    | refl _ => exact Or.inl rfl
    | snoc hc' hs' hle ih =>
      rename_i w v s0 t₀ t'
      rcases ih hs0 with rfl | ⟨hwT, ht1⟩
      · right
        have h1 := hs'.le_crash (c := m + 1) (by simp [r', run3c])
        have ht : t₀ < m := by
          by_contra hc
          have := h1.2 (by omega)
          simp [r', run3c] at this
        refine ⟨?_, by omega⟩
        have hsn : Sent alg nice w v t₀ := by
          have : msg alg r' w v t₀ = msg alg nice w v t₀ := by
            refine msg_congr rfl (fun _ => histi t₀ (by omega) ht) ?_
            simp only [Run.Deliv, Run.Alive, r', run3c, nice]
            simp only [if_true, Option.some.injEq]
            constructor
            · intro _; simp
            · intro _
              refine ⟨fun c hc => by omega, fun hc => by omega⟩
          unfold Sent; rw [← this]; exact hs'
        simp only [hT, T2, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases (show t₀ = 0 ∨ t₀ = 1 by omega) with rfl | rfl
        · exact Or.inl hsn
        · exact Or.inr hsn
      · left
        have hwi : w ≠ i := fun h => hiT (h ▸ hwT)
        have h1 := hs'.le_crash (c := 2) (by simp [r', run3c, hwi, hwT])
        have := h1.2 (by omega)
        simpa [r', run3c, hwi] using this
  obtain ⟨z, hz, t, hc⟩ := chain_to_correct hAC hfn hr' hdec i
  apply hz
  rcases key z t hc with rfl | ⟨hzT, -⟩
  · simp [Run.Faulty, r', run3c]
  · have hzi : z ≠ i := fun h => hiT (h ▸ hzT)
    simp [Run.Faulty, r', run3c, hzi, hzT]

/-- **Theorem 3(c)** of Goren–Moses: if all processes decide by time `D = 2` in the nice run of an AC
protocol for `γ_f` (`f < n`), then at least `f · n` messages are sent in the nice run. -/
theorem theorem3c (hAC : SolvesAC alg f) (hfn : f < Fintype.card P)
    (hD : ∀ i, ∃ m ≤ 2, ∃ d, DecidesAt alg nice i m d) :
    ((f * Fintype.card P : ℕ) : ℕ∞) ≤ (msgs alg nice).encard := by
  let g : P → P → P × P × ℕ := fun a b => (a, b, if Sent alg nice a b 0 then 0 else 1)
  let D : Finset (P × P × ℕ) := Finset.univ.biUnion (fun a => (T2 alg a).image (g a))
  have hcardD : f * Fintype.card P ≤ D.card := by
    rw [Finset.card_biUnion]
    · rw [mul_comm, ← smul_eq_mul, ← Finset.card_univ]
      apply Finset.card_nsmul_le_sum
      intro a _
      rw [Finset.card_image_of_injective _ (fun b c hbc => by simpa [g] using congrArg (·.2.1) hbc)]
      obtain ⟨m, hm, d, hd⟩ := hD a
      exact card_T2 hAC hfn hm hd
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e hea heb
      simp only [Finset.mem_image] at hea heb
      obtain ⟨x, -, rfl⟩ := hea
      obtain ⟨y, -, hy⟩ := heb
      exact hab (congrArg Prod.fst hy).symm
  have hsub : (D : Set (P × P × ℕ)) ⊆ msgs alg nice := by
    intro e he
    simp only [D, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.coe_image, Set.mem_image, Finset.mem_coe] at he
    obtain ⟨a, b, hb, rfl⟩ := he
    simp only [T2, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    show Sent alg nice a b (if Sent alg nice a b 0 then 0 else 1)
    split_ifs with h0
    · exact h0
    · exact hb.resolve_left h0
  calc ((f * Fintype.card P : ℕ) : ℕ∞) ≤ (D.card : ℕ∞) := by exact_mod_cast hcardD
    _ = (D : Set (P × P × ℕ)).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (msgs alg nice).encard := Set.encard_le_encard hsub

/-- **Theorem 3(d)** of Goren–Moses: a message-optimal AC protocol (`M = n + f − 1`) for `f > 1`
cannot have all processes decide by time `D ≤ 2` in its nice run: `D ≥ 3`. -/
theorem theorem3d (hAC : SolvesAC alg f) (hf : 2 ≤ f) (hfn : f < Fintype.card P)
    (hM : (msgs alg nice).encard ≤ ((Fintype.card P + f - 1 : ℕ) : ℕ∞)) {D : ℕ}
    (hD : ∀ i, ∃ m ≤ D, ∃ d, DecidesAt alg nice i m d) : 3 ≤ D := by
  by_contra hlt
  have h2 : ∀ i, ∃ m ≤ 2, ∃ d, DecidesAt alg nice i m d := by
    intro i
    obtain ⟨m, hm, d, hd⟩ := hD i
    exact ⟨m, by omega, d, hd⟩
  have := (theorem3c hAC hfn h2).trans hM
  have h' : f * Fintype.card P ≤ Fintype.card P + f - 1 := by exact_mod_cast this
  have : 2 * Fintype.card P ≤ f * Fintype.card P := Nat.mul_le_mul_right _ hf
  -- `f n ≥ n + f` when `f, n ≥ 2`
  have : (f - 1) * (Fintype.card P - 1) ≥ 1 := Nat.one_le_iff_ne_zero.2 (by
    apply Nat.mul_ne_zero <;> omega)
  have e : (f - 1) * (Fintype.card P - 1) = f * Fintype.card P - f - Fintype.card P + 1 := by
    obtain ⟨a, rfl⟩ : ∃ a, f = a + 1 := ⟨f - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, Fintype.card P = b + 1 := ⟨Fintype.card P - 1, by omega⟩
    rw [hb]; simp only [Nat.add_sub_cancel]; ring_nf; omega
  omega

/-- **The case `D = 1`** (not stated in the paper, which leaves Theorem 3 without a matching lower
bound for the protocol D1f1): a process that decides by time `1` in the nice run of an AC protocol
(`f ≥ 1`) has received a first-round message from every other process. -/
theorem decide_time1_receives (hAC : SolvesAC alg f) (hf : 1 ≤ f) {i : P} {m : ℕ} {d : Decision}
    (hm : m ≤ 1) (h : DecidesAt alg nice i m d) (j : P) (hji : j ≠ i) : Sent alg nice j i 0 := by
  obtain rfl := nice_decides_commit hAC i h
  have hK : Knows alg f i m nice (fun r' => r'.input j = true) :=
    (corollary1 hAC (nice_admissible f) h).mono (fun r' _ h' => h' j)
  by_cases hc : Chain alg nice j 0 i m
  · obtain ⟨y, t', hcy, hs, ht⟩ := hc.exists_last (Ne.symm hji)
    obtain rfl : t' = 0 := by omega
    obtain rfl := hcy.eq_of_le le_rfl
    exact hs
  · obtain ⟨-, hlt⟩ := silent_choir_at (nice_admissible f) hK hc
    rw [nice_faulty, Finset.empty_union] at hlt
    have : S alg nice j (m - 1) ⊆ {j} := by
      intro z hz
      rw [mem_S] at hz
      rw [Finset.mem_singleton]
      exact hz.eq_of_le (by omega)
    have := Finset.card_le_card this
    simp at this
    omega

/-- **Theorem 3, case `D = 1`**: if all processes decide by time `1` in the nice run of an AC protocol
for `γ_f` (`f ≥ 1`), then at least `n(n − 1)` messages are sent. Together with the protocol D1f1
this completes the time/message tradeoff for `f = 1`. -/
theorem theorem3_D1 (hAC : SolvesAC alg f) (hf : 1 ≤ f)
    (hD : ∀ i, ∃ m ≤ 1, ∃ d, DecidesAt alg nice i m d) :
    ((Fintype.card P * (Fintype.card P - 1) : ℕ) : ℕ∞) ≤ (msgs alg nice).encard := by
  let D : Finset (P × P × ℕ) := (Finset.univ : Finset P).offDiag.image (fun e => (e.1, e.2, 0))
  have hcard : D.card = Fintype.card P * (Fintype.card P - 1) := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by
      simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 hab.2.1), Finset.offDiag_card,
      Finset.card_univ, Nat.mul_sub_one]
  have hsub : (D : Set (P × P × ℕ)) ⊆ msgs alg nice := by
    intro e he
    simp only [D, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_offDiag,
      Finset.mem_univ, true_and] at he
    obtain ⟨⟨j, i⟩, hji, rfl⟩ := he
    obtain ⟨m, hm, d, hd⟩ := hD i
    exact decide_time1_receives hAC hf hm hd j hji
  calc ((Fintype.card P * (Fintype.card P - 1) : ℕ) : ℕ∞) = (D.card : ℕ∞) := by rw [hcard]
    _ = (D : Set (P × P × ℕ)).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (msgs alg nice).encard := Set.encard_le_encard hsub

/-- **Corollary 3** of Goren–Moses: when `f < n − 1`, a message-optimal AC protocol (`M = n + f − 1`)
must use silence: in its nice run some process `i` commits although there is no message chain from
some `j` to `i` (so `i` learns `v_j = 1` without a message chain). -/
theorem corollary3 (hAC : SolvesAC alg f) (hf : 1 ≤ f) (hfn : f + 1 < Fintype.card P)
    (hM : (msgs alg nice).encard ≤ ((Fintype.card P + f - 1 : ℕ) : ℕ∞)) :
    ∃ i j, (∃ m, DecidesAt alg nice i m .commit) ∧ ∀ t, ¬ Chain alg nice j 0 i t := by
  haveI : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  by_contra hno
  push Not at hno
  have hall : ∀ i j, ∃ t, Chain alg nice j 0 i t := fun i j =>
    hno i j (nice_exists_commit hAC i)
  have := (lemma3 (alg := alg) nice (k := Fintype.card P - 1) (by omega) (fun j => by
    have : Finset.univ.filter (fun z => z ≠ j ∧ ∃ t, Chain alg nice j 0 z t) =
        Finset.univ.erase j := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      exact ⟨fun h => h.1, fun h => ⟨h, hall z j⟩⟩
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ])).trans hM
  have : Fintype.card P + (Fintype.card P - 1) - 1 ≤ Fintype.card P + f - 1 := by
    exact_mod_cast this
  omega

end AC

end Papers.PODC2018.Silence
