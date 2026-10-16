import Papers.PODC2018.AtomicCrossChainSwaps.Facts

/-!
# Safety of the repaired protocol (Theorem 4.9, Lemma 4.8)

Main result: `Setting.safety` — in the repaired protocol (`fixed = true`), for any digraph, any set
of leaders, any base timeout `B`, any deviating coalition (with or without front-running), no
conforming party ends Underwater.

The proof follows the paper (Lemma 4.8 + Theorem 4.9) with the two missing ingredients made
explicit: unforgeability (a key containing a conforming `v` was signed by `v`, so `v`'s first
observed key does not contain `v`) and the timing of the leader's release.
-/

namespace AtomicSwap

namespace Setting

variable {V : Type*} [DecidableEq V] [Fintype V] (P : Setting V) (C : Finset V)
  (sch : ℕ → Moves V)

local notation "S" t => P.run C sch t

/-! ### Conforming keys -/

lemma confKey_spec {t : ℕ} {s : St V} {m : Moves V} {u v ℓ : V} {p : List V}
    (h : P.confKey C t s m u v ℓ = some p) :
    v ∉ C ∧ P.D.Adj u v ∧ ℓ ∈ P.L ∧
      ((ℓ = v ∧ p = [v] ∧ P.Releases C t s v) ∨
        (ℓ ≠ v ∧ ∃ p1, P.obs s m v ℓ = some p1 ∧ p = v :: p1)) := by
  unfold confKey at h
  by_cases h1 : v ∈ C ∨ ¬ P.D.Adj u v ∨ ℓ ∉ P.L
  · simp [h1] at h
  rw [ite_eq_right h1] at h
  push Not at h1
  refine ⟨h1.1, h1.2.1, h1.2.2, ?_⟩
  by_cases h2 : ℓ = v
  · rw [ite_eq_left h2] at h
    split_ifs at h with h3
    · cases h; exact Or.inl ⟨h2, rfl, h3⟩
  · rw [ite_eq_right h2] at h
    refine Or.inr ⟨h2, ?_⟩
    cases ho : P.obs s m v ℓ with
    | none => simp [ho] at h
    | some p1 =>
      simp only [ho] at h
      split_ifs at h <;> cases h <;> exact ⟨p1, rfl, rfl⟩

/-! ### First observations -/

lemma first_succ (t : ℕ) (v ℓ : V) :
    (S (t + 1)).first v ℓ = if v ∉ C ∧ ℓ ∈ P.L ∧ ℓ ≠ v then P.obs (S t) (sch t) v ℓ else none :=
  rfl

lemma first_spec {t : ℕ} {v ℓ : V} {p : List V} (h : (S t).first v ℓ = some p) :
    v ∉ C ∧ ℓ ∈ P.L ∧ ℓ ≠ v := by
  cases t with
  | zero => simp [St.init] at h
  | succ t =>
    rw [first_succ] at h
    split_ifs at h with h1
    · exact h1

omit [DecidableEq V] [Fintype V] in
lemma obs_of_first {s : St V} {m : Moves V} {v ℓ : V} {p : List V} (h : s.first v ℓ = some p) :
    P.obs s m v ℓ = some p := by
  simp [obs, h]

lemma first_mono {t t' : ℕ} (htt : t ≤ t') {v ℓ : V} {p : List V}
    (h : (S t).first v ℓ = some p) : (S t').first v ℓ = some p := by
  induction htt with
  | refl => exact h
  | step _ ih =>
    rw [first_succ, ite_eq_left (P.first_spec C sch ih)]
    exact P.obs_of_first ih

omit [DecidableEq V] [Fintype V] in
/-- A first observation is taken from an unlocked leaving arc. -/
lemma obs_new {s : St V} {m : Moves V} {v ℓ : V} {p : List V} (h0 : s.first v ℓ = none)
    (h : P.obs s m v ℓ = some p) :
    P.D.Adj v (m.pick v ℓ) ∧ ∃ τ, s.unl v (m.pick v ℓ) ℓ = some (τ, p) := by
  simp only [obs, h0] at h
  split_ifs at h with ha
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ha, x.1, hx⟩

lemma first_origin {t : ℕ} {v ℓ : V} {p : List V} (h : (S t).first v ℓ = some p) :
    ∃ t1 < t, (S t1).first v ℓ = none ∧ (S (t1 + 1)).first v ℓ = some p ∧
      ∃ w τ, P.D.Adj v w ∧ (S t1).unl v w ℓ = some (τ, p) := by
  induction t with
  | zero => simp [St.init] at h
  | succ t ih =>
    cases h0 : (S t).first v ℓ with
    | some p' =>
      have := P.first_mono C sch (Nat.le_succ t) h0
      rw [this] at h; cases h
      obtain ⟨t1, ht1, h1⟩ := ih h0
      exact ⟨t1, by omega, h1⟩
    | none =>
      refine ⟨t, by omega, h0, h, ?_⟩
      rw [first_succ] at h
      split_ifs at h
      obtain ⟨ha, τ, hτ⟩ := P.obs_new h0 h
      exact ⟨_, τ, ha, hτ⟩

variable {P C sch}

/-- Conforming parties notice unlocks on their leaving arcs (validity of the tie-breaking). -/
lemma first_set (hsch : P.ValidSched C sch) {t : ℕ} {v w ℓ : V} (hv : v ∉ C) (hℓ : ℓ ∈ P.L)
    (hℓv : ℓ ≠ v) (hvw : P.D.Adj v w) (hu : ((S t).unl v w ℓ).isSome) :
    ((S (t + 1)).first v ℓ).isSome := by
  rw [first_succ, ite_eq_left ⟨hv, hℓ, hℓv⟩]
  cases h0 : (S t).first v ℓ with
  | some p => simp [P.obs_of_first h0]
  | none =>
    obtain ⟨ha, hs⟩ := (hsch t).2.2 v ℓ hv hℓ hℓv h0 ⟨w, hvw, hu⟩
    simp only [obs, h0, ite_eq_left ha]
    simpa using hs

/-- The key of the first observation landed exactly in the round of the observation. -/
lemma first_origin' (hsch : P.ValidSched C sch) {t : ℕ} {v ℓ : V} {p : List V}
    (h : (S t).first v ℓ = some p) :
    ∃ t1 < t, (S t1).first v ℓ = none ∧ (S (t1 + 1)).first v ℓ = some p ∧
      ∃ w, P.D.Adj v w ∧ (S t1).unl v w ℓ = some (t1, p) := by
  obtain ⟨t1, ht1, h0, h1, w, τ, hw, hτ⟩ := P.first_origin C sch h
  refine ⟨t1, ht1, h0, h1, w, hw, ?_⟩
  obtain ⟨hv, hℓ, hℓv⟩ := P.first_spec C sch h
  have hτle := (P.unl_ok C sch hτ).2.1
  rcases Nat.lt_or_ge τ t1 with hlt | hge
  · exfalso
    have := first_set hsch hv hℓ hℓv hw (by rw [P.unl_at_landing C sch hτ]; rfl)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp this
    have := P.first_mono C sch (by omega : τ + 1 ≤ t1) hq
    rw [this] at h0; cases h0
  · rwa [show τ = t1 by omega] at hτ

variable (P C sch)

lemma first_known {t : ℕ} {v ℓ : V} {p : List V} (h : (S t).first v ℓ = some p) :
    (S t).Known ℓ p := by
  obtain ⟨t1, ht1, -, -, w, τ, -, hτ⟩ := P.first_origin C sch h
  exact P.known_mono C sch ht1.le (P.unl_known C sch hτ)

lemma obs_known {t : ℕ} {v ℓ : V} {p : List V} (h : P.obs (S t) (sch t) v ℓ = some p) :
    (S t).Known ℓ p := by
  cases h0 : (S t).first v ℓ with
  | some p' =>
    rw [P.obs_of_first h0] at h; cases h; exact P.first_known C sch h0
  | none =>
    obtain ⟨-, τ, hτ⟩ := P.obs_new h0 h
    exact P.unl_known C sch hτ

/-! ### Unforgeability -/

/-- Every suffix `x :: r` of `q` with `x` conforming was submitted by `x` itself before time
`t` (the signature of `x` is unforgeable). -/
def Good (t : ℕ) (ℓ : V) (q : List V) : Prop :=
  ∀ x r, (x :: r) <:+ q → x ∉ C →
    ∃ u, ∃ t' < t, P.confKey C t' (S t') (sch t') u x ℓ = some (x :: r)

variable {P C sch}

lemma Good.mono {t t' : ℕ} (htt : t ≤ t') {ℓ : V} {q : List V} (h : P.Good C sch t ℓ q) :
    P.Good C sch t' ℓ q := by
  intro x r hs hx
  obtain ⟨u, t'', ht'', hk⟩ := h x r hs hx
  exact ⟨u, t'', by omega, hk⟩

lemma Good.suffix {t : ℕ} {ℓ : V} {q q' : List V} (h : P.Good C sch t ℓ q) (hq : q' <:+ q) :
    P.Good C sch t ℓ q' :=
  fun x r hs hx => h x r (hs.trans hq) hx

lemma good_of_derivable {K : List V → Prop} {t : ℕ} {ℓ : V}
    (hK : ∀ q, K q → P.Good C sch t ℓ q) : ∀ q, Derivable C K ℓ q → P.Good C sch t ℓ q
  | [], h => h.elim
  | [c], h => by
    rcases h with h | ⟨hc, -⟩
    · exact hK _ h
    · intro x r hs hx
      rcases List.suffix_cons_iff.mp hs with h' | h'
      · cases h'; exact absurd hc hx
      · simp at h'
  | c :: d :: q, h => by
    rcases h with h | ⟨hc, h⟩
    · exact hK _ h
    · have ih := good_of_derivable hK (d :: q) h
      intro x r hs hx
      rcases List.suffix_cons_iff.mp hs with h' | h'
      · cases h'; exact absurd hc hx
      · exact ih x r h' hx

/-- The unforgeability invariant: all public keys are `Good`. -/
theorem known_good (hsch : P.ValidSched C sch) :
    ∀ t ℓ q, (S t).Known ℓ q → P.Good C sch t ℓ q := by
  intro t
  induction t with
  | zero => intro ℓ q ⟨u, v, p, hp, _⟩; simp [St.init] at hp
  | succ t ih =>
    -- keys submitted by conforming parties in round `t` are good at `t + 1`
    have hconf : ∀ u v ℓ p, P.confKey C t (S t) (sch t) u v ℓ = some p →
        P.Good C sch (t + 1) ℓ p := by
      intro u v ℓ p hk
      obtain ⟨hv, -, -, hcase⟩ := P.confKey_spec C hk
      rcases hcase with ⟨rfl, rfl, -⟩ | ⟨-, p1, hp1, rfl⟩
      · intro x r hs hx
        rcases List.suffix_cons_iff.mp hs with h' | h'
        · cases h'; exact ⟨u, t, by omega, hk⟩
        · simp at h'
      · have hg := (ih ℓ p1 (P.obs_known C sch hp1)).mono (Nat.le_succ t)
        intro x r hs hx
        rcases List.suffix_cons_iff.mp hs with h' | h'
        · cases h'; exact ⟨u, t, by omega, hk⟩
        · exact hg x r h' hx
    intro ℓ q ⟨u, v, p, hp, hq⟩
    rw [sub_succ] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ((ih ℓ p ⟨u, v, p, hp, List.suffix_refl p⟩).mono (Nat.le_succ t)).suffix hq
    · apply Good.suffix _ hq
      unfold roundKeys at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hconf u v ℓ p (Option.mem_toList.mp hp)
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
        obtain ⟨hc, hon⟩ := List.mem_filter.mp hc
        simp only [IsOn, decide_eq_true_eq] at hon
        obtain ⟨-, -, hℓ⟩ := hon
        have hd := ((hsch t).2.1 c hc).2
        rw [hℓ] at hd
        apply good_of_derivable _ _ hd
        rintro q' (hq' | ⟨-, u', v', p', hp', hs'⟩)
        · exact (ih ℓ q' hq').mono (Nat.le_succ t)
        · exact (hconf u' v' ℓ p' (Option.mem_toList.mp hp')).suffix hs'

/-- A conforming party's first observed key does not contain it (it never signed a key for that
hashlock before observing one). -/
theorem not_mem_first (hsch : P.ValidSched C sch) {t : ℕ} {v ℓ : V} {p : List V}
    (h : (S t).first v ℓ = some p) : v ∉ p := by
  obtain ⟨t1, -, h0, h1, w, -, hτ⟩ := first_origin' hsch h
  obtain ⟨hv, -, hℓv⟩ := P.first_spec C sch h
  intro hvp
  obtain ⟨pre, r, rfl⟩ := List.append_of_mem hvp
  have hg := known_good hsch t1 ℓ _ (P.unl_known C sch hτ)
  obtain ⟨u, t', ht', hk⟩ := hg v r (List.suffix_append _ _) hv
  obtain ⟨-, -, -, hcase⟩ := P.confKey_spec C hk
  rcases hcase with ⟨h', -⟩ | ⟨-, p1, hp1, -⟩
  · exact hℓv h'
  · -- `v` had already observed `ℓ` in round `t'`, so `first` was set at `t' + 1 ≤ t1`
    have : ((S (t' + 1)).first v ℓ).isSome := by
      rw [first_succ, ite_eq_left ⟨hv, (P.first_spec C sch h).2.1, hℓv⟩, hp1]; rfl
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp this
    rw [P.first_mono C sch (by omega : t' + 1 ≤ t1) hq] at h0
    cases h0

/-! ### The leader's release -/

lemma releases_unl {t : ℕ} {u v : V} (hfix : P.fixed = true)
    (hr : P.Releases C t (S t) v) (huv : P.D.Adj u v) : ((S (t + 1)).unl u v v).isSome := by
  obtain ⟨hv, hL, hrel, hall, hB⟩ := hr
  cases h0 : (S t).unl u v v with
  | some x => simp [P.unl_succ C sch h0]
  | none =>
    have hk : P.confKey C t (S t) (sch t) u v v = some [v] := by
      unfold confKey
      rw [ite_eq_right (by simp [hv, huv, hL]), ite_eq_left rfl, ite_eq_left ⟨hv, hL, hrel, hall, hB⟩]
    have hok : P.Ok t (S t) u v v [v] :=
      ⟨hall u huv, hL, ⟨⟨by simp, by simp, by simp⟩, rfl, rfl⟩, by simpa [dl] using hB hfix⟩
    have : P.newKey C t (S t) (sch t) u v v = some [v] := by
      unfold newKey; rw [ite_eq_right hv, hk]; simp [hok]
    rw [run_succ]; simp [step, h0, this]

/-- If a hashlock of a conforming leader `v` is unlocked anywhere, `v` has released its secret,
which it does only when all its entering arcs have contracts (and, repaired, early enough). -/
theorem released_of_unl (hsch : P.ValidSched C sch) {t : ℕ} {a b v : V} {τ : ℕ} {p : List V}
    (hv : v ∉ C) (h : (S t).unl a b v = some (τ, p)) :
    ∃ r, P.Releases C r (S r) v := by
  have hkey := (P.unl_ok C sch h).2.2.1.2.2.1
  have hlast : [v] <:+ p := by
    obtain ⟨-, -, hl⟩ := hkey
    rw [List.getLast?_eq_some_iff] at hl
    obtain ⟨ys, rfl⟩ := hl
    exact List.suffix_append _ _
  obtain ⟨u, t', -, hk⟩ := known_good hsch t v p (P.unl_known C sch h) v [] hlast hv
  obtain ⟨-, -, -, hcase⟩ := P.confKey_spec C hk
  rcases hcase with ⟨-, -, hr⟩ | ⟨hne, -⟩
  · exact ⟨t', hr⟩
  · exact absurd rfl hne

/-! ### Forwarding (Lemma 4.8) -/

/-- **Lemma 4.8 (repaired protocol).** If hashlock `ℓ ≠ v` is unlocked on an arc leaving a
conforming `v` by time `τ`, and the entering arc `(u, v)` has a contract by time `c` (where
`c ≤ B` if `v` is a leader), then `ℓ` is unlocked on `(u, v)` by time `max τ c + 1`. -/
theorem forward (hfix : P.fixed = true) (hsch : P.ValidSched C sch) {τ c : ℕ} {u v w ℓ : V}
    (hv : v ∉ C) (hℓ : ℓ ∈ P.L) (hℓv : ℓ ≠ v) (hvw : P.D.Adj v w)
    (hτ : ((S τ).unl v w ℓ).isSome) (huv : P.D.Adj u v) (hc : ((S c).con u v).isSome)
    (hcB : v ∈ P.L → c ≤ P.B) : ((S (max τ c + 1)).unl u v ℓ).isSome := by
  -- the first observation
  obtain ⟨p1, hp1⟩ := Option.isSome_iff_exists.mp (first_set hsch hv hℓ hℓv hvw hτ)
  obtain ⟨t1, ht1, h0, h1, w1, hw1, hu1⟩ := first_origin' hsch hp1
  have hnot := not_mem_first hsch hp1
  obtain ⟨-, -, hok1, -⟩ := P.unl_ok C sch hu1
  obtain ⟨hcon1, -, hkey1, hdl1⟩ := hok1
  -- the actual publication time of the contract on `(u, v)`
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hc
  have hc0le := (P.con_le C sch hc0).2
  have hlen1 : 1 ≤ p1.length := List.length_pos_iff.mpr hkey1.1.1
  have hBdl : P.B ≤ dl P.B p1 := by unfold dl; omega
  have hc0' : c0 ≤ dl P.B p1 ∧ c0 ≤ max t1 c0 := by
    refine ⟨?_, le_max_right _ _⟩
    by_cases hvL : v ∈ P.L
    · have := hcB hvL; omega
    · -- a follower publishes on `(v, w1)` only after all entering contracts exist
      obtain ⟨c1, hc1⟩ := Option.isSome_iff_exists.mp hcon1
      have hc1le := (P.con_le C sch hc1).2
      obtain ⟨-, -, hall⟩ := P.con_conforming C sch hc1 hv
      obtain ⟨c0', hc0'⟩ := Option.isSome_iff_exists.mp (hall hvL u huv)
      have := (P.con_le C sch hc0').2
      have := P.con_mono C sch (show c1 - 1 ≤ max (c1 - 1) c from le_max_left _ _) hc0'
      have := P.con_mono C sch (show c ≤ max (c1 - 1) c from le_max_right _ _) hc0
      have hc0eq : c0' = c0 := by simp_all
      omega
  -- the round in which `v` forwards on `(u, v)`
  set tf := max t1 c0 with htf
  have hobs : P.obs (S tf) (sch tf) v ℓ = some p1 := by
    rcases Nat.eq_or_lt_of_le (le_max_left t1 c0) with heq | hlt
    · rw [htf, ← heq]
      rw [first_succ, ite_eq_left ⟨hv, hℓ, hℓv⟩] at h1; exact h1
    · exact P.obs_of_first (P.first_mono C sch (by omega) h1)
  have hcon : ((S tf).con u v).isSome := by
    rw [htf, P.con_mono C sch (le_max_right t1 c0) (P.con_at_landing C sch hc0)]; rfl
  have hfin : ((S (tf + 1)).unl u v ℓ).isSome := by
    cases h0' : (S tf).unl u v ℓ with
    | some x => simp [P.unl_succ C sch h0']
    | none =>
      have hdl : tf + 1 ≤ dl P.B (v :: p1) := by
        have := hc0'.1
        unfold dl at hdl1 this ⊢; simp; omega
      have hk : P.confKey C tf (S tf) (sch tf) u v ℓ = some (v :: p1) := by
        unfold confKey
        rw [ite_eq_right (by simp [hv, huv, hℓ]), ite_eq_right hℓv, hobs]
        simp [hfix, hnot, hcon, h0', hdl]
      have hpath : IsKey P.D ℓ v (v :: p1) := by
        obtain ⟨⟨hne, hch, hnd⟩, hhd, hlast⟩ := hkey1
        refine ⟨⟨by simp, ?_, ?_⟩, rfl, ?_⟩
        · obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
          simp only [List.head?_cons, Option.some.injEq] at hhd
          subst hhd
          exact List.IsChain.cons_cons hw1 hch
        · rw [List.dropLast_cons_of_ne_nil hne]
          exact List.nodup_cons.mpr ⟨fun h => hnot (List.mem_of_mem_dropLast h), hnd⟩
        · rw [List.getLast?_cons, hlast]; rfl
      have hok : P.Ok tf (S tf) u v ℓ (v :: p1) := ⟨hcon, hℓ, hpath, hdl⟩
      have : P.newKey C tf (S tf) (sch tf) u v ℓ = some (v :: p1) := by
        unfold newKey; rw [ite_eq_right hv, hk]; simp [hok]
      rw [run_succ]; simp [step, h0', this]
  apply P.unl_isSome_mono C sch _ hfin
  have : t1 ≤ τ := by
    -- `first` is set by round `τ + 1`, hence `t1 ≤ τ`
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (first_set hsch hv hℓ hℓv hvw hτ)
    rw [P.first_mono C sch (by omega : τ + 1 ≤ t1) hq] at h0
    cases h0
  omega

/-- The entering arcs of a conforming `v` that has a triggered (or just partially unlocked)
leaving arc carry contracts, early enough if `v` is a leader. -/
lemma entering_con (hfix : P.fixed = true) (hsch : P.ValidSched C sch) {t : ℕ} {u v w ℓ : V}
    {x : ℕ × List V} (hv : v ∉ C) (hvL : v ∈ P.L → (S t).unl v w v ≠ none)
    (hx : (S t).unl v w ℓ = some x) (huv : P.D.Adj u v) :
    ∃ c, ((S c).con u v).isSome ∧ (v ∈ P.L → c ≤ P.B) := by
  by_cases hL : v ∈ P.L
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hvL hL)
    obtain ⟨r, hr⟩ := released_of_unl hsch hv (τ := y.1) (p := y.2) (by simpa using hy)
    exact ⟨r, hr.2.2.2.1 u huv, fun _ => by have := hr.2.2.2.2 hfix; omega⟩
  · obtain ⟨c1, -, hc1⟩ := P.unl_con C sch (τ := x.1) (p := x.2) (by simpa using hx)
    obtain ⟨-, -, hall⟩ := P.con_conforming C sch hc1 hv
    exact ⟨c1 - 1, hall hL u huv, fun h => absurd h hL⟩

/-- **Theorem 4.9 (repaired protocol).** For every swap digraph, every set of leaders, every base
timeout `B` and every deviating coalition `C` (front-running or not), no conforming party ends up
Underwater. -/
theorem safety (hfix : P.fixed = true) (hsch : P.ValidSched C sch) {v : V} (hv : v ∉ C) :
    ¬ Underwater P.D {v} (P.Final C sch) := by
  rintro ⟨⟨u, a, ⟨huv, hu, ha⟩, hnt⟩, ⟨b, w, ⟨hvw, hb, hw⟩, ht⟩⟩
  simp only [Set.mem_singleton_iff] at hu ha hb hw
  subst a b
  obtain ⟨t0, ht0⟩ := ht
  apply hnt
  -- each hashlock is eventually unlocked on `(u, v)`
  have key : ∀ ℓ ∈ P.L, ∃ t, ((S t).unl u v ℓ).isSome := by
    intro ℓ hℓ
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ht0 ℓ hℓ)
    have hvL : v ∈ P.L → (S t0).unl v w v ≠ none := fun h => by
      have := ht0 v h; intro h'; simp [h'] at this
    obtain ⟨c, hc, hcB⟩ := entering_con hfix hsch hv hvL hx huv
    by_cases hℓv : ℓ = v
    · subst hℓv
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (ht0 ℓ hℓ)
      obtain ⟨r, hr⟩ := released_of_unl hsch hv (τ := y.1) (p := y.2) (by simpa using hy)
      exact ⟨r + 1, releases_unl hfix hr huv⟩
    · exact ⟨_, forward hfix hsch hv hℓ hℓv hvw (ht0 ℓ hℓ) huv hc hcB⟩
  choose! f hf using key
  exact ⟨P.L.sup f, fun ℓ hℓ => P.unl_isSome_mono C sch (Finset.le_sup hℓ) (hf ℓ hℓ)⟩

end Setting

end AtomicSwap
