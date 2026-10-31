import Papers.PODC2012.NonEquivocationLimits.SmallCases

/-!
# Non-equivocation *with* transferable authentication: r-broadcast for every `n`

Section 3 states that non-equivocation and transferable authentication "together, but not
individually, are sufficient to improve the resiliency bound to `n ≥ 2f + 1`" (the positive half
is Section 4's translation, applied e.g. to the crash-tolerant r-broadcast of Figure 3). We check
the r-broadcast instance directly.

**Model.** Messages are *attestations* `valid_p(k, v)` (`Att`): transferable signatures by `p`
on a key `k` and a value `v` (`attAuth`: an attestation is its own token, signed by its
`signer`). Unforgeability is CSLib's (`Algorithm.Unforging`, `Run.AuthValid`).
Non-equivocation (`AttNonEquivocating`): two attestations of the same faulty signer with the same
key that the adversary shows to correct processes are equal.

**Protocol** (`relay s`, the translation of Figure 3 in spirit). The sender attests `(0, v)` for
its input `v` and delivers `v`. Every process that sees an attestation of `s` with key `0` for the
first time delivers its value and relays the attestation to everybody, forever.

`relay_isRBroadcast`: it solves r-broadcast in every asynchronous run, for **every** `n` and `f`.
Together with `claim_3_1` and `claim_3_2`, this confirms the separation of Section 3.
-/

set_option linter.unusedSectionVars false

namespace Podc.NonEquivocationLimits

open Cslib.Byzantine.PartialSync Finset

variable {P V : Type*} [DecidableEq P]

/-- An attestation `valid_p(k, v)`: a transferable signature by `signer` on the pair `(key, val)`
(Sections 2.3 and 2.4). -/
structure Att (P V : Type*) where
  /-- The process whose (non-equivocation) key was used. -/
  signer : P
  /-- The key `k`. -/
  key : ℕ
  /-- The attested value. -/
  val : V

/-- Attestations are transferable signatures: an attestation is its own (single) token. -/
def attAuth (P V : Type*) : Auth P (Att P V) (Att P V) := ⟨Att.signer, fun a => {a}⟩

/-- **Non-equivocation for attestations**: the faulty processes never show correct processes two
different attestations of the same faulty signer with the same key. -/
def AttNonEquivocating {VI : Type*} (R : Run P (Att P V) VI) : Prop :=
  ∀ b ∈ R.faulty, ∀ b' ∈ R.faulty, ∀ τ τ' r r', r ∉ R.faulty → r' ∉ R.faulty →
    ∀ x ∈ R.byz b τ r, ∀ x' ∈ R.byz b' τ' r', x.signer = x'.signer → x.signer ∈ R.faulty →
      x.key = x'.key → x = x'

/-- The first attestation of `s` with key `0` in an inbox (if any). -/
noncomputable def pick (s : P) (ib : P → List (Att P V)) : Option V :=
  open Classical in
  if h : ∃ x : Att P V, (∃ q, x ∈ ib q) ∧ x.signer = s ∧ x.key = 0 then some (Classical.choose h).val
  else none

theorem pick_eq_some {s : P} {ib : P → List (Att P V)} {v : V} (h : pick s ib = some v) :
    ∃ q, (⟨s, 0, v⟩ : Att P V) ∈ ib q := by
  unfold pick at h
  split_ifs at h with h'
  obtain ⟨⟨q, hq⟩, hs, hk⟩ := Classical.choose_spec h'
  obtain rfl := Option.some.inj h
  refine ⟨q, ?_⟩
  convert hq using 1
  cases hc : Classical.choose h'
  simp_all

theorem pick_isSome {s : P} {ib : P → List (Att P V)} {q : P} {x : Att P V} (hx : x ∈ ib q)
    (hs : x.signer = s) (hk : x.key = 0) : ∃ v, pick s ib = some v := by
  unfold pick
  rw [dite_eq_left_of_eq_true (eq_true ⟨x, ⟨q, hx⟩, hs, hk⟩)]
  exact ⟨_, rfl⟩

/-- The relay protocol with sender `s`. -/
noncomputable def relay (s : P) : Algorithm P (Att P V) (Option V) V V where
  init p v := if p = s then some v else none
  step _ st ib := st.or (pick s ib)
  send _ st _ := st.toList.map fun v => ⟨s, 0, v⟩
  decide _ st := st

namespace relay

variable {s : P} {VI : Type*} {R : Run P (Att P V) V}

theorem st_succ (τ : ℕ) (p : P) :
    R.st (relay s) (τ + 1) p = (R.st (relay s) τ p).or (pick s (R.inbox (relay s) p τ)) :=
  R.st_succ (relay s) τ p

theorem send_eq (p : P) (st : Option V) (q : P) :
    (relay s).send p st q = st.toList.map fun v => ⟨s, 0, v⟩ := rfl

theorem st_mono {p : P} {τ : ℕ} {v : V} (h : R.st (relay s) τ p = some v) :
    ∀ τ', τ ≤ τ' → R.st (relay s) τ' p = some v := by
  intro τ' hτ'
  induction τ', hτ' using Nat.le_induction with
  | base => exact h
  | succ τ' _ ih => rw [st_succ, ih]; rfl

theorem decides_unique {p : P} {v w : V} (hv : R.Decides (relay s) p v)
    (hw : R.Decides (relay s) p w) : v = w := by
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨τ', hτ'⟩ := hw
  have h1 := st_mono hτ (max τ τ') (le_max_left _ _)
  have h2 := st_mono hτ' (max τ τ') (le_max_right _ _)
  change R.st (relay s) _ p = _ at h1 h2
  rw [h1] at h2; exact Option.some.inj h2

theorem st_sender (τ : ℕ) : R.st (relay s) τ s = some (R.inp s) :=
  st_mono (τ := 0) (by simp [relay]) τ (Nat.zero_le _)

/-- A non-sender only adopts values attested by `s` that it has received. -/
theorem st_eq_some {p : P} (hp : p ≠ s) {v : V} :
    ∀ τ, R.st (relay s) τ p = some v → ∃ τ' < τ, ∃ q, ⟨s, 0, v⟩ ∈ R.inbox (relay s) p τ' q := by
  intro τ
  induction τ with
  | zero => simp [relay, hp]
  | succ τ ih =>
    intro h
    rw [st_succ] at h
    cases hτ : R.st (relay s) τ p with
    | some w =>
      rw [hτ] at h
      obtain ⟨τ', hτ', q, hq⟩ := ih (by rw [hτ]; simpa using h)
      exact ⟨τ', by omega, q, hq⟩
    | none =>
      rw [hτ, Option.none_or] at h
      obtain ⟨q, hq⟩ := pick_eq_some h
      exact ⟨τ, by omega, q, hq⟩

/-- The relay protocol is unforging: it only emits `s`'s attestations, and a process other than
`s` only relays attestations it has received. -/
theorem unforging : (relay (V := V) s).Unforging (attAuth P V) := by
  intro R p τ q m hm x hx
  simp only [attAuth, Set.mem_singleton_iff] at hx
  subst hx
  rw [send_eq] at hm
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
  by_cases hp : p = s
  · exact Or.inl hp.symm
  · right
    obtain ⟨τ', hτ', q', hq'⟩ := st_eq_some hp τ (Option.mem_toList.mp hv)
    exact ⟨τ', hτ', q', _, hq', rfl⟩

/-- Where an attestation of `s` with key `0` known to correct processes can come from. -/
def Orig (R : Run P (Att P V) V) (s : P) (v : V) : Prop :=
  (s ∉ R.faulty ∧ v = R.inp s) ∨
    (s ∈ R.faulty ∧ ∃ b ∈ R.faulty, ∃ τ r, r ∉ R.faulty ∧ (⟨s, 0, v⟩ : Att P V) ∈ R.byz b τ r)

/-- **Invariant.** The value held by a correct process has a legitimate origin. -/
theorem orig_of_st (hA : R.AuthValid (attAuth P V) (relay s)) :
    ∀ τ, ∀ σ ≤ τ, ∀ p ∉ R.faulty, ∀ v, R.st (relay s) σ p = some v → Orig R s v := by
  intro τ
  induction τ with
  | zero =>
    intro σ hσ p hp v h
    obtain rfl : σ = 0 := by omega
    by_cases hps : p = s
    · subst hps; simp [relay] at h; exact Or.inl ⟨hp, h.symm⟩
    · simp [relay, hps] at h
  | succ τ ih =>
    intro σ hσ p hp v h
    rcases Nat.lt_or_ge σ (τ + 1) with hlt | hge
    · exact ih σ (by omega) p hp v h
    obtain rfl : σ = τ + 1 := by omega
    rw [st_succ] at h
    cases hτ : R.st (relay s) τ p with
    | some w => rw [hτ] at h; exact ih τ le_rfl p hp v (by rw [hτ]; simpa using h)
    | none =>
      rw [hτ, Option.none_or] at h
      obtain ⟨q, hq⟩ := pick_eq_some h
      obtain ⟨σ', hσ', -, hm⟩ := Run.mem_inbox.mp hq
      by_cases hqf : q ∈ R.faulty
      · rw [Run.out_of_faulty _ _ hqf] at hm
        by_cases hsf : s ∈ R.faulty
        · exact Or.inr ⟨hsf, q, hqf, σ', p, hp, hm⟩
        · -- `s` is correct: the attestation was emitted by a correct process
          rcases hA q hqf σ' p hp _ hm _ rfl with hs | ⟨σ'', hσ'', q', hq', r, m, hm', hx⟩
          · exact absurd hs hsf
          · simp only [attAuth, Set.mem_singleton_iff] at hx
            subst hx
            rw [Run.out_of_correct _ _ hq', send_eq] at hm'
            obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm'
            obtain rfl : w = v := by cases hwe; rfl
            exact ih σ'' (by omega) q' hq' w (Option.mem_toList.mp hw)
      · rw [Run.out_of_correct _ _ hqf, send_eq] at hm
        obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
        obtain rfl : w = v := by cases hwe; rfl
        exact ih σ' (by omega) q hqf w (Option.mem_toList.mp hw)

/-- **Non-equivocation plus transferable authentication suffice for r-broadcast**, for every
number of processes and of faults, in the asynchronous model. -/
theorem isRBroadcast (f : ℕ) :
    IsRBroadcast (relay (V := V) s) s
      {R | R.AsyncValid f ∧ R.AuthValid (attAuth P V) (relay s) ∧ AttNonEquivocating R} where
  senderTermination R _ _ := ⟨0, st_sender 0⟩
  completeness R hR := by
    rintro ⟨p, hp, v, τ, hv⟩ q hq
    set d := R.dl p τ q
    have hmem : (⟨s, 0, v⟩ : Att P V) ∈ R.inbox (relay s) q d p :=
      Run.mem_inbox.mpr ⟨τ, hR.1.dl_ge p τ q hp hq, rfl, by
        rw [Run.out_of_correct _ _ hp, send_eq]; simp [show R.st (relay s) τ p = some v from hv]⟩
    obtain ⟨w, hw⟩ : ∃ w, R.st (relay s) (d + 1) q = some w := by
      rw [st_succ]
      cases R.st (relay s) d q with
      | some w => exact ⟨w, rfl⟩
      | none =>
        obtain ⟨w, hw⟩ := pick_isSome hmem rfl rfl
        exact ⟨w, by rw [hw]; rfl⟩
    exact ⟨w, d + 1, hw⟩
  validity R hR hs p hp v := by
    rintro ⟨τ, hτ⟩
    rcases orig_of_st hR.2.1 τ τ le_rfl p hp v hτ with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hs
  agreement R hR p hp q hq v w := by
    rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩
    rcases orig_of_st hR.2.1 τ τ le_rfl p hp v hτ with ⟨hn, h⟩ | ⟨hs, b, hb, σ, r, hr, hx⟩ <;>
      rcases orig_of_st hR.2.1 τ' τ' le_rfl q hq w hτ' with
        ⟨hn', h'⟩ | ⟨hs', b', hb', σ', r', hr', hx'⟩
    · rw [h, h']
    · exact absurd hs' hn
    · exact absurd hs hn'
    · have := hR.2.2 b hb b' hb' σ σ' r r' hr hr' _ hx _ hx' rfl hs rfl
      exact congrArg Att.val this
  integrity R _ p _ v w hv hw := decides_unique hv hw

end relay

/-- **Section 3 (positive part).** With non-equivocation *and* transferable authentication,
r-broadcast is solvable in the asynchronous model for every `n` and `f`, by an unforging protocol
that never equivocates. -/
theorem ne_plus_ta_rbroadcast (s : P) (f : ℕ) :
    (relay (V := V) s).Unforging (attAuth P V) ∧
      IsRBroadcast (relay (V := V) s) s
        {R | R.AsyncValid f ∧ R.AuthValid (attAuth P V) (relay s) ∧ AttNonEquivocating R} :=
  ⟨relay.unforging, relay.isRBroadcast f⟩

end Podc.NonEquivocationLimits
