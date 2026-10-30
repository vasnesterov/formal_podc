import Papers.PODC2023.OptimalEBAOmission.Runs

/-!
# Implementations of `P0` (Proposition 6.1)

* `Implements.deciding_zero_iff`, `deciding_one_iff`: the decision rules of `P0` at reachable states.
* `Implements.exists_chain`: an agent deciding `0` at time `m` receives a (repaired) 0-chain of length
  `m`; `Implements.receivedChain_iff`: receiving a 0-chain by `(c, m)` is deciding `0` at a time `≤ m`.
* `prop_6_1`: every implementation of `P0` is an EBA decision protocol in every EBA context with
  sending-omission failures; nonfaulty agents decide after at most `t + 1` rounds, and Validity
  holds for all agents.
* `Implements.state_eq`: all implementations of `P0` generate the same runs (so "all
  implementations" in Definition 6.2, Theorem 6.3 and Proposition 6.4 is one protocol up to
  unreachable states).
-/

namespace Podc.OptimalEBAOmission

open Classical

namespace Context

variable {n : ℕ} {γ : Context n}

/-- The test of `P0` for deciding `0`: `init_i = 0 ∨ K_i(⋁_j jdecided_j = 0)`. -/
def ZTest (P : γ.Protocol) (i : Fin n) (s : γ.L) : Prop :=
  s.1.init = 0 ∨ Knows P i s (fun c m => ∃ j, JDecided P c m j 0)

/-- The test of `P0` for deciding `1`: `K_i(⋀_j ¬(deciding_j = 0))`. -/
def OTest (P : γ.Protocol) (i : Fin n) (s : γ.L) : Prop :=
  Knows P i s (fun c m => ∀ j, ¬ Deciding P c m j 0)

theorem P0_of_undecided (P : γ.Protocol) (i : Fin n) (s : γ.L) (h : s.1.decided = none) :
    P0 P i s = if ZTest P i s then .decide 0 else if OTest P i s then .decide 1 else .noop := by
  unfold P0 ZTest OTest; split_ifs <;> simp_all

theorem val_cases (v : Val) : v = 0 ∨ v = 1 := by fin_cases v <;> simp

section Impl

variable {P : γ.Protocol} (hP : Implements P) {c : γ.Config} (hc : c.Valid)
include hP hc

theorem Implements.deciding_zero_iff {m : ℕ} {i : Fin n} :
    Deciding P c m i 0 ↔ dec P c m i = none ∧ ZTest P i (γ.state P c m i) := by
  rw [deciding_iff hP.oneShotOn hc, hP c hc]
  constructor
  · rintro ⟨hd, ha⟩
    refine ⟨hd, ?_⟩
    rw [P0_of_undecided _ _ _ hd] at ha
    split_ifs at ha with h1 h2 <;> first | exact h1 | cases ha
  · rintro ⟨hd, hz⟩
    exact ⟨hd, by rw [P0_of_undecided _ _ _ hd, if_pos hz]⟩

theorem Implements.deciding_one_iff {m : ℕ} {i : Fin n} :
    Deciding P c m i 1 ↔ dec P c m i = none ∧ ¬ ZTest P i (γ.state P c m i) ∧
      OTest P i (γ.state P c m i) := by
  rw [deciding_iff hP.oneShotOn hc, hP c hc]
  constructor
  · rintro ⟨hd, ha⟩
    rw [P0_of_undecided _ _ _ hd] at ha
    split_ifs at ha with h1 h2
    · cases ha
    · exact ⟨hd, h1, h2⟩
  · rintro ⟨hd, hz, ho⟩
    exact ⟨hd, by rw [P0_of_undecided _ _ _ hd, if_neg hz, if_pos ho]⟩

theorem Implements.act_noop_iff {m : ℕ} {i : Fin n} (hd : dec P c m i = none) :
    P i (γ.state P c m i) = .noop ↔ ¬ ZTest P i (γ.state P c m i) ∧
      ¬ OTest P i (γ.state P c m i) := by
  rw [hP c hc, P0_of_undecided _ _ _ hd]
  split_ifs with h1 h2 <;> simp_all

/-- An undecided agent with initial preference `0` decides `0`. -/
theorem Implements.deciding_of_init {m : ℕ} {i : Fin n} (hd : dec P c m i = none)
    (h0 : c.init i = 0) : Deciding P c m i 0 :=
  (hP.deciding_zero_iff hc).2 ⟨hd, Or.inl (by simpa using h0)⟩

/-- An undecided agent with `jd = 0` decides `0`. -/
theorem Implements.deciding_of_jd {m : ℕ} {i : Fin n} (hd : dec P c m i = none)
    (hj : (γ.state P c m i).1.jd = some 0) : Deciding P c m i 0 :=
  (hP.deciding_zero_iff hc).2 ⟨hd, Or.inr (knows_of_jd hP.oneShotOn hj)⟩

/-- Agents deciding `0` at time `0` have initial preference `0`... -/
theorem Implements.init_of_deciding_zero {i : Fin n} (h : Deciding P c 0 i 0) :
    c.init i = 0 := by
  rcases ((hP.deciding_zero_iff hc).1 h).2 with h1 | h1
  · simpa using h1
  · obtain ⟨j, hj⟩ := h1 c hc 0 rfl
    exact absurd hj (not_jDecided_zero hP.oneShotOn hc)

/-- ... agents deciding `1` have initial preference `1`... -/
theorem Implements.init_of_deciding_one {m : ℕ} {i : Fin n} (h : Deciding P c m i 1) :
    c.init i = 1 := by
  have hz := ((hP.deciding_one_iff hc).1 h).2.1
  rcases val_cases (c.init i) with h0 | h0
  · exact absurd (Or.inl (by simpa using h0)) hz
  · exact h0

/-- ...and agents deciding later have initial preference `1`. -/
theorem Implements.init_of_deciding_succ {m : ℕ} {i : Fin n} {v : Val}
    (h : Deciding P c (m + 1) i v) : c.init i = 1 := by
  rcases val_cases (c.init i) with h0 | h0
  swap; · exact h0
  exfalso
  have := hP.deciding_of_init hc (dec_zero P c i) h0
  exact absurd (deciding_unique hP.oneShotOn hc h this).1 (by omega)

/-- An agent deciding `0` at time `m + 1` learned that some agent decided `0` at time `m`. -/
theorem Implements.exists_prev {m : ℕ} {i : Fin n} (h : Deciding P c (m + 1) i 0) :
    ∃ j, Deciding P c m j 0 := by
  have h1 := hP.init_of_deciding_succ hc h
  obtain ⟨-, hz⟩ := (hP.deciding_zero_iff hc).1 h
  rcases hz with hz | hz
  · simp [h1] at hz
  · obtain ⟨j, hj⟩ := hz c hc (m + 1) rfl
    exact ⟨j, (jDecided_succ_iff hP.oneShotOn hc).1 hj⟩

/-- An agent deciding `0` at time `m` receives a (repaired) 0-chain of length `m` (the
"observation" in the proof of Proposition 6.1). -/
theorem Implements.exists_chain {m : ℕ} {i : Fin n} (h : Deciding P c m i 0) :
    ∃ a, IsZeroChain P c m a ∧ a m = i := by
  have key : ∀ m i, Deciding P c m i 0 → ∃ a : ℕ → Fin n, a m = i ∧ c.init (a 0) = 0 ∧
      (∀ k ≤ m, Deciding P c k (a k) 0) ∧ ∀ k, 1 ≤ k → k ≤ m →
        Knows P (a k) (γ.state P c k (a k)) (fun c' m' => ∃ j, JDecided P c' m' j 0) := by
    intro m
    induction m with
    | zero =>
      intro i h
      refine ⟨fun _ => i, rfl, hP.init_of_deciding_zero hc h, ?_, fun k hk hk' => by omega⟩
      intro k hk; obtain rfl : k = 0 := by omega
      exact h
    | succ m ih =>
      intro i h
      obtain ⟨j, hj⟩ := hP.exists_prev hc h
      obtain ⟨a, ham, ha0, hdec, hkn⟩ := ih j hj
      have h1 := hP.init_of_deciding_succ hc h
      obtain ⟨-, hz⟩ := (hP.deciding_zero_iff hc).1 h
      have hK : Knows P i (γ.state P c (m + 1) i) (fun c' m' => ∃ j, JDecided P c' m' j 0) := by
        rcases hz with hz | hz
        · simp [h1] at hz
        · exact hz
      refine ⟨fun k => if k = m + 1 then i else a k, by simp, ?_, ?_, ?_⟩
      · simpa using ha0
      · intro k hk
        by_cases hk' : k = m + 1
        · subst hk'; simpa using h
        · simpa [hk'] using hdec k (by omega)
      · intro k hk1 hk2
        by_cases hk' : k = m + 1
        · subst hk'; simpa using hK
        · simpa [hk'] using hkn k hk1 (by omega)
  obtain ⟨a, ham, ha0, hdec, hkn⟩ := key m i h
  exact ⟨a, ⟨inj_of_deciding hP.oneShotOn hc hdec, ha0, hdec, hkn⟩, ham⟩

/-- Receiving a (repaired) 0-chain by `(c, m)` is the same as having decided `0` by time `m + 1`. -/
theorem Implements.receivedChain_iff {m : ℕ} {i : Fin n} :
    ReceivedChain P c m i ↔ dec P c (m + 1) i = some 0 := by
  constructor
  · rintro ⟨m', hm', a, ha, rfl⟩
    exact dec_stable hP.oneShotOn hc (ha.2.2.1 m' le_rfl).2 (m + 1) (by omega)
  · intro hd
    obtain ⟨d, hd', hD⟩ := exists_deciding hP.oneShotOn hc hd
    obtain ⟨a, ha, hai⟩ := hP.exists_chain hc hD
    exact ⟨d, by omega, a, ha, hai⟩

/-- A nonfaulty agent deciding `0` at time `d` makes every undecided agent decide `0` at `d + 1`. -/
theorem Implements.deciding_of_nonfaulty {d : ℕ} {j i : Fin n} (hSO : c.pat ∈ SO n t)
    (hj : j ∈ c.pat.N) (hD : Deciding P c d j 0) (hi : dec P c (d + 1) i = none) :
    Deciding P c (d + 1) i 0 := by
  refine hP.deciding_of_jd hc hi ((jd_succ_eq_zero_iff P c d i).2 ⟨j, ?_, ?_⟩)
  · by_contra hF
    exact hSO.2 d j i (by simpa using hF) hj
  · exact ((deciding_iff hP.oneShotOn hc).1 hD).2

/-- No agent decides `0` at a time at which some agent decides `1` (`K_i` is veridical). -/
theorem Implements.not_deciding_zero_of_one {d : ℕ} {i j : Fin n} (h1 : Deciding P c d i 1) :
    ¬ Deciding P c d j 0 :=
  ((hP.deciding_one_iff hc).1 h1).2.2 c hc d rfl j

/-- A 0-chain contains an agent deciding at every earlier time. -/
theorem Implements.exists_deciding_le {m d : ℕ} {i : Fin n} (h : Deciding P c m i 0) (hd : d ≤ m) :
    ∃ j, Deciding P c d j 0 := by
  obtain ⟨a, ha, -⟩ := hP.exists_chain hc h
  exact ⟨a d, ha.2.2.1 d hd⟩

end Impl

/-- **Proposition 6.1.** In an EBA context with sending-omission failures (`γ.FM ⊆ SO(t)`), every
implementation `P` of `P0` is an EBA decision protocol. Moreover every nonfaulty agent has decided
after at most `t + 1` rounds of message exchange (by time `t + 2`), and Validity holds even for
faulty agents. -/
theorem prop_6_1 {t : ℕ} (hFM : γ.FM ⊆ SO n t) {P : γ.Protocol} (hP : Implements P) :
    IsEBA P ∧ (∀ c : γ.Config, c.Valid → ∀ i ∈ c.pat.N, dec P c (t + 2) i ≠ none) ∧
      (∀ c : γ.Config, c.Valid → ∀ i m v, dec P c m i = some v → ∃ j, c.init j = v) := by
  have hOS := hP.oneShotOn
  -- Validity for all agents
  have hval : ∀ c : γ.Config, c.Valid → ∀ i m v, dec P c m i = some v → ∃ j, c.init j = v := by
    intro c hc i m v hd
    obtain ⟨d, -, hD⟩ := exists_deciding hOS hc hd
    rcases val_cases v with rfl | rfl
    · obtain ⟨a, ha, -⟩ := hP.exists_chain hc hD
      exact ⟨a 0, ha.2.1⟩
    · exact ⟨i, hP.init_of_deciding_one hc hD⟩
  -- Termination by time t + 2
  have hterm : ∀ c : γ.Config, c.Valid → ∀ i ∈ c.pat.N, dec P c (t + 2) i ≠ none := by
    intro c hc i hi hd
    have hd1 : dec P c (t + 1) i = none := dec_none_of_le hOS hc hd (by omega)
    have hnoop : P i (γ.state P c (t + 1) i) = .noop := by
      cases ha : P i (γ.state P c (t + 1) i) with
      | noop => rfl
      | decide v =>
        have := (deciding_iff hOS hc).2 ⟨hd1, ha⟩
        rw [this.2] at hd; cases hd
    obtain ⟨hz, ho⟩ := (hP.act_noop_iff hc hd1).1 hnoop
    apply ho
    intro c' hc' m' hs j hj
    have hm := time_eq_of_state_eq hs
    subst hm
    obtain ⟨a, ha, -⟩ := hP.exists_chain hc' hj
    obtain ⟨k, hk, hkN⟩ := exists_nonfaulty_of_inj (hFM hc'.1).1
      (fun k hk l hl he => ha.1 k (by omega) l (by omega) he)
    have hi' : dec P c' (t + 1) i = none := by
      have := congrArg (fun s => s.1.decided) hs; simpa [hd1] using this
    have hD : Deciding P c' (k + 1) i 0 :=
      hP.deciding_of_nonfaulty hc' (hFM hc'.1) hkN (ha.2.2.1 k (by omega))
        (dec_none_of_le hOS hc' hi' (by omega))
    by_cases hkt : k = t
    · subst hkt
      exact hz (by rw [← hs]; exact ((hP.deciding_zero_iff hc').1 hD).2)
    · have := dec_stable hOS hc' hD.2 (t + 1) (by omega)
      rw [hi'] at this; cases this
  refine ⟨⟨?_, ?_, fun c hc i _ m v hd => hval c hc i m v hd, ?_⟩, hterm, hval⟩
  · -- Unique Decision
    intro c hc i m v hd m' hm' h'
    rw [dec_stable hOS hc hd m' hm'] at h'
    have := Option.some_injective _ h'
    revert this; rcases val_cases v with rfl | rfl <;> decide
  · -- Agreement
    intro c hc i hi j hj m v v' hdi hdj
    by_contra hne
    wlog hv : v = 0 generalizing i j v v'
    · refine this j hj i hi v' v hdj hdi (Ne.symm hne) ?_
      rcases val_cases v with h | h
      · exact absurd h hv
      · rcases val_cases v' with h' | h'
        · exact h'
        · exact absurd (h.trans h'.symm) hne
    subst hv
    have hv' : v' = 1 := by
      rcases val_cases v' with h' | h'
      · exact absurd h'.symm hne
      · exact h'
    subst hv'
    obtain ⟨di, -, hDi⟩ := exists_deciding hOS hc hdi
    obtain ⟨dj, -, hDj⟩ := exists_deciding hOS hc hdj
    by_cases hle : dj ≤ di
    · obtain ⟨l, hl⟩ := hP.exists_deciding_le hc hDi hle
      exact hP.not_deciding_zero_of_one hc hDj hl
    · have hund : dec P c (di + 1) j = none := dec_none_of_le hOS hc hDj.1 (by omega)
      have hD0 := hP.deciding_of_nonfaulty hc (hFM hc.1) hi hDi hund
      have := (deciding_unique hOS hc hD0 hDj).2
      exact absurd this (by decide)
  · -- Termination
    intro c hc i hi m
    refine ⟨max m (t + 2), le_max_left _ _, ?_⟩
    intro h
    exact hterm c hc i hi (dec_none_of_le hOS hc h (le_max_right _ _))

/-! ### Uniqueness of implementations -/

/-- All implementations of `P0` generate the same runs. -/
theorem Implements.state_eq {P Q : γ.Protocol} (hP : Implements P) (hQ : Implements Q) :
    ∀ m, ∀ c : γ.Config, c.Valid → γ.state P c m = γ.state Q c m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hc
    cases m with
    | zero => rfl
    | succ m =>
      -- equal states at all times `≤ m`
      have heq : ∀ k ≤ m, ∀ c' : γ.Config, c'.Valid → γ.state P c' k = γ.state Q c' k :=
        fun k hk c' hc' => ih k (by omega) c' hc'
      -- the 0-tests agree at time `m`
      have hZ : ∀ c' : γ.Config, c'.Valid → ∀ i,
          ZTest P i (γ.state P c' m i) ↔ ZTest Q i (γ.state Q c' m i) := by
        intro c' hc' i
        rw [heq m le_rfl c' hc']
        unfold ZTest
        refine or_congr Iff.rfl ⟨fun h c'' hc'' m'' hs => ?_, fun h c'' hc'' m'' hs => ?_⟩
        · have hm : m'' = m := by have := congrArg (fun s => s.1.time) hs; simpa using this
          subst hm
          have hs' : γ.state P c'' m'' i = γ.state Q c' m'' i := by rw [heq _ le_rfl c'' hc'']; exact hs
          obtain ⟨j, hj⟩ := h c'' hc'' m'' hs'
          refine ⟨j, ?_⟩
          simpa only [JDecided, dec, heq m'' le_rfl c'' hc'', heq (m'' - 1) (by omega) c'' hc''] using hj
        · have hm : m'' = m := by have := congrArg (fun s => s.1.time) hs; simpa using this
          subst hm
          have hs' : γ.state Q c'' m'' i = γ.state Q c' m'' i := by rw [← heq _ le_rfl c'' hc'']; exact hs
          obtain ⟨j, hj⟩ := h c'' hc'' m'' hs'
          refine ⟨j, ?_⟩
          simpa only [JDecided, dec, heq m'' le_rfl c'' hc'', heq (m'' - 1) (by omega) c'' hc''] using hj
      -- deciding `0` at time `m` agrees
      have hD : ∀ c' : γ.Config, c'.Valid → ∀ j,
          Deciding P c' m j 0 ↔ Deciding Q c' m j 0 := by
        intro c' hc' j
        rw [hP.deciding_zero_iff hc', hQ.deciding_zero_iff hc', hZ c' hc' j]
        simp only [dec, heq m le_rfl c' hc']
      -- the 1-tests agree at time `m`
      have hO : ∀ c' : γ.Config, c'.Valid → ∀ i,
          OTest P i (γ.state P c' m i) ↔ OTest Q i (γ.state Q c' m i) := by
        intro c' hc' i
        rw [heq m le_rfl c' hc']
        unfold OTest
        constructor
        · intro h c'' hc'' m'' hs j
          have hm : m'' = m := by have := congrArg (fun s => s.1.time) hs; simpa using this
          subst hm
          rw [← hD c'' hc'' j]
          exact h c'' hc'' m'' (by rw [heq _ le_rfl c'' hc'']; exact hs) j
        · intro h c'' hc'' m'' hs j
          have hm : m'' = m := by have := congrArg (fun s => s.1.time) hs; simpa using this
          subst hm
          rw [hD c'' hc'' j]
          exact h c'' hc'' m'' (by rw [← heq _ le_rfl c'' hc'']; exact hs) j
      -- hence the actions agree at time `m`
      have hact : ∀ i, P i (γ.state P c m i) = Q i (γ.state Q c m i) := by
        intro i
        rw [hP c hc, hQ c hc]
        by_cases hd : (γ.state P c m i).1.decided = none
        · have hd' : (γ.state Q c m i).1.decided = none := by rwa [← heq m le_rfl c hc]
          rw [P0_of_undecided _ _ _ hd, P0_of_undecided _ _ _ hd']
          simp only [hZ c hc i, hO c hc i]
        · have hd' : (γ.state Q c m i).1.decided ≠ none := by rwa [← heq m le_rfl c hc]
          simp only [P0, if_pos hd, if_pos hd']
      have hact' : ∀ i, P i (γ.state Q c m i) = Q i (γ.state Q c m i) := by
        intro i; have := hact i; rwa [heq m le_rfl c hc] at this
      funext i
      have hrcv : rcv P c m i = rcv Q c m i := by
        funext j; simp only [rcv, heq m le_rfl c hc, hact']
      simp only [state_succ, hrcv, heq m le_rfl c hc, hact']

end Context

end Podc.OptimalEBAOmission
