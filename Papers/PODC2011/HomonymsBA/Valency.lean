import Papers.PODC2011.HomonymsBA.Basic

/-!
# Proposition 16: `ℓ ≤ t` makes synchronous BA unsolvable, even against restricted Byzantine
# processes and with numerate processes

The valency argument of Section 5.1 and Appendix A.2 of the paper. We fix the system
`P = Fin n` in which processes `k < ℓ` are Byzantine and have identifier `k` (one Byzantine
process per identifier, `ℓ ≤ t` of them), and all `n - ℓ ≥ 2` correct processes have identifier
`0`. Runs are synchronous, without losses, and the Byzantine processes deliver at most one message
per identifier, recipient and round (`AdvOK`, restricted).

* `Dec inp adv k`: the decisions of correct processes in admissible runs that agree with
  `adv` before round `k` (the decisions reachable from the configuration at round `k`);
  `Multi` = at least two different reachable decisions (multivalent).
* **Lemma 17** (`exists_common_dec`): if two runs give the same states to all correct processes
  except `p` up to round `k`, some decision is reachable from both. The Byzantine process `0`
  (identifier of `p`) impersonates `p` with the other run's state (`simCfg`, `simCfg_swap`).
* **Lemma 21** (`exists_multi_init`): some initial configuration is multivalent.
* **Lemma 22** (`exists_multi_succ`): every multivalent configuration has a multivalent successor.
* `prop16`: an infinite run of multivalent configurations, in which no correct process decides.
-/

namespace Podc.HomonymsBA

open Finset

namespace Valency

variable {n ℓ : ℕ} (hℓ : 0 < ℓ)

/-- Identifiers: `k < ℓ` has identifier `k`, the others (the correct processes) identifier `0`. -/
def idV (k : Fin n) : Fin ℓ := if h : k.val < ℓ then ⟨k, h⟩ else ⟨0, hℓ⟩

variable (n ℓ) in
/-- The Byzantine processes: one per identifier. -/
def byzV : Finset (Fin n) := univ.filter (·.val < ℓ)

lemma mem_byzV {k : Fin n} : k ∈ byzV n ℓ ↔ k.val < ℓ := by simp [byzV]

lemma idV_of_correct {k : Fin n} (hk : k ∉ byzV n ℓ) : idV hℓ k = ⟨0, hℓ⟩ := by
  rw [mem_byzV] at hk; simp [idV, hk]

variable {V M S : Type*} (A : Algorithm ℓ V M S)

/-- The run with inputs `inp` and Byzantine deliveries `adv`. -/
def mkRun (inp : Fin n → V) (adv : ℕ → Fin n → Multiset (Fin ℓ × M)) : Run (Fin n) ℓ V M where
  id := idV hℓ
  byz := byzV n ℓ
  inp := inp
  gst := 0
  drop _ _ _ := False
  adv := adv

/-- Restricted deliveries: at most one pair per identifier and recipient. -/
def AdvOK (a : Fin n → Multiset (Fin ℓ × M)) : Prop := ∀ p (j : Fin ℓ), ((a p).filter (·.1 = j)).card ≤ 1

/-- `adv'` agrees with `adv` before round `k`. -/
def Agrees (adv adv' : ℕ → Fin n → Multiset (Fin ℓ × M)) (k : ℕ) : Prop := ∀ r < k, adv' r = adv r

/-- Decisions reachable from the configuration at round `k` of the run `(inp, adv)`. -/
def Dec (inp : Fin n → V) (adv : ℕ → Fin n → Multiset (Fin ℓ × M)) (k : ℕ) : Set V :=
  {v | ∃ adv', (∀ r, AdvOK (adv' r)) ∧ Agrees adv adv' k ∧
    ∃ r, ∃ q ∉ byzV n ℓ, A.decide ((mkRun hℓ inp adv').st A r q) = some v}

/-- Multivalent configuration. -/
def Multi (inp : Fin n → V) (adv : ℕ → Fin n → Multiset (Fin ℓ × M)) (k : ℕ) : Prop :=
  ∃ v w, v ≠ w ∧ v ∈ Dec hℓ A inp adv k ∧ w ∈ Dec hℓ A inp adv k

variable (n) in
/-- The standing hypothesis: `A` solves BA in all these runs. -/
def Good : Prop := ∀ inp adv, (∀ r, AdvOK (adv r)) → (mkRun hℓ inp adv : Run (Fin n) ℓ V M).BA A

/-! ### Basic facts -/

lemma inbox_mkRun (inp : Fin n → V) (adv : ℕ → Fin n → Multiset (Fin ℓ × M)) (r : ℕ) (q : Fin n) :
    (mkRun hℓ inp adv).inbox A r q =
      (∑ q' ∈ univ.filter (· ∉ byzV n ℓ), (mkRun hℓ inp adv).msgFrom A
        ((mkRun hℓ inp adv).st A r q') q' q) + adv r q := by
  rw [Run.inbox_eq]
  congr 1
  exact Finset.sum_congr (by ext; simp [mkRun]) fun _ _ => rfl

/-- States up to round `k` depend only on the deliveries before `k`. -/
lemma st_eq_of_agrees {inp : Fin n → V} {adv adv' : ℕ → Fin n → Multiset (Fin ℓ × M)} {k : ℕ}
    (h : Agrees adv adv' k) : ∀ r ≤ k, (mkRun hℓ inp adv).st A r = (mkRun hℓ inp adv').st A r := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
    intro hr
    funext q
    rw [Run.st_succ, Run.st_succ, inbox_mkRun, inbox_mkRun, ih (by omega), h r (by omega)]
    rfl

lemma Agrees.trans {adv adv' adv'' : ℕ → Fin n → Multiset (Fin ℓ × M)} {k : ℕ}
    (h1 : Agrees adv adv' k) (h2 : Agrees adv' adv'' k) : Agrees adv adv'' k :=
  fun r hr => (h2 r hr).trans (h1 r hr)

lemma Agrees.symm {adv adv' : ℕ → Fin n → Multiset (Fin ℓ × M)} {k : ℕ}
    (h : Agrees adv adv' k) : Agrees adv' adv k := fun r hr => (h r hr).symm

lemma Agrees.mono {adv adv' : ℕ → Fin n → Multiset (Fin ℓ × M)} {k m : ℕ}
    (h : Agrees adv adv' k) (hm : m ≤ k) : Agrees adv adv' m := fun r hr => h r (by omega)

lemma dec_congr {inp : Fin n → V} {adv adv' : ℕ → Fin n → Multiset (Fin ℓ × M)} {k : ℕ}
    (h : Agrees adv adv' k) : Dec hℓ A inp adv k = Dec hℓ A inp adv' k := by
  ext v
  constructor
  · rintro ⟨a, ha, hag, hd⟩; exact ⟨a, ha, h.symm.trans hag, hd⟩
  · rintro ⟨a, ha, hag, hd⟩; exact ⟨a, ha, h.trans hag, hd⟩

lemma multi_congr {inp : Fin n → V} {adv adv' : ℕ → Fin n → Multiset (Fin ℓ × M)} {k : ℕ}
    (h : Agrees adv adv' k) : Multi hℓ A inp adv k ↔ Multi hℓ A inp adv' k := by
  simp [Multi, dec_congr hℓ A h]

variable {hℓ A}

/-- Some correct process. -/
lemma exists_correct (hn : ℓ < n) : ∃ q : Fin n, q ∉ byzV n ℓ :=
  ⟨⟨ℓ, hn⟩, by simp [mem_byzV]⟩

/-- Reachable decisions exist. -/
lemma dec_nonempty (hA : Good n hℓ A) (hn : ℓ < n) {inp : Fin n → V}
    {adv : ℕ → Fin n → Multiset (Fin ℓ × M)} (hadv : ∀ r, AdvOK (adv r)) (k : ℕ) :
    ∃ v, v ∈ Dec hℓ A inp adv k := by
  obtain ⟨q, hq⟩ := exists_correct hn
  obtain ⟨v, r, hr⟩ := (hA inp adv hadv).termination q hq
  exact ⟨v, adv, hadv, fun _ _ => rfl, r, q, hq, hr⟩

/-- A multivalent configuration: no correct process has decided yet. -/
lemma undecided_of_multi (hA : Good n hℓ A) {inp : Fin n → V}
    {adv : ℕ → Fin n → Multiset (Fin ℓ × M)} {k : ℕ} (hm : Multi hℓ A inp adv k) :
    ∀ r ≤ k, ∀ q ∉ byzV n ℓ, A.decide ((mkRun hℓ inp adv).st A r q) = none := by
  intro r hr q hq
  by_contra hne
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hne
  have key : ∀ x ∈ Dec hℓ A inp adv k, x = u := by
    rintro x ⟨a, ha, hag, r', q', hq', hx⟩
    have hs := st_eq_of_agrees hℓ A (inp := inp) hag r hr
    have hu' : (mkRun hℓ inp a).Decides A q u := ⟨r, by rw [← hs]; exact hu⟩
    exact (hA inp a ha).agreement q' hq' q hq x u ⟨r', hx⟩ hu'
  obtain ⟨v, w, hvw, hv, hw⟩ := hm
  exact hvw ((key v hv).trans (key w hw).symm)

/-! ### Lemma 17: impersonation -/

section Sim

variable (hℓ A)

/-- What correct `q'` in state `σ` sends to `q`. -/
def msgC (σ : S) (q' q : Fin n) : Multiset (Fin ℓ × M) :=
  oms ((A.send σ (idV hℓ q)).map fun m => (idV hℓ q', m))

/-- What the impersonator (identifier `0`) in state `s` sends to `q`. -/
def msgB (s : S) (q : Fin n) : Multiset (Fin ℓ × M) :=
  oms ((A.send s (idV hℓ q)).map fun m => ((⟨0, hℓ⟩ : Fin ℓ), m))

/-- Inbox of `q` in configuration `c` with impersonator state `s`. -/
noncomputable def cfgIn (c : Fin n → S) (s : S) (q : Fin n) : Multiset (Fin ℓ × M) :=
  (∑ q' ∈ univ.filter (· ∉ byzV n ℓ), msgC hℓ A (c q') q' q) + msgB hℓ A s q

/-- Joint execution of the correct processes and the impersonator (which receives what `p`
receives). -/
noncomputable def simCfg (p : Fin n) (c : Fin n → S) (s : S) : ℕ → (Fin n → S) × S
  | 0 => (c, s)
  | j + 1 =>
    ((fun q => A.step ((simCfg p c s j).1 q) (cfgIn hℓ A (simCfg p c s j).1 (simCfg p c s j).2 q)),
     A.step (simCfg p c s j).2 (cfgIn hℓ A (simCfg p c s j).1 (simCfg p c s j).2 p))

/-- The deliveries of the continuation: before `k` as in `adv`, from `k` on the impersonator's
messages. -/
noncomputable def contAdv (adv : ℕ → Fin n → Multiset (Fin ℓ × M)) (k : ℕ) (p : Fin n)
    (c : Fin n → S) (s : S) : ℕ → Fin n → Multiset (Fin ℓ × M) := fun r q =>
  if r < k then adv r q else msgB hℓ A (simCfg hℓ A p c s (r - k)).2 q

end Sim

lemma msgB_ok (s : S) : AdvOK (msgB (n := n) hℓ A s) := by
  intro q j
  unfold msgB
  cases A.send s (idV hℓ q) with
  | none => simp
  | some m =>
    simp only [Option.map_some, oms_some]
    rw [Multiset.filter_singleton]; split_ifs <;> simp

lemma contAdv_ok {adv : ℕ → Fin n → Multiset (Fin ℓ × M)} (hadv : ∀ r, AdvOK (adv r)) (k : ℕ)
    (p : Fin n) (c : Fin n → S) (s : S) (r : ℕ) : AdvOK (contAdv hℓ A adv k p c s r) := by
  unfold contAdv
  by_cases h : r < k
  · simp only [h, if_true]; exact hadv r
  · simp only [h, if_false]; exact msgB_ok _

lemma contAdv_agrees (adv : ℕ → Fin n → Multiset (Fin ℓ × M)) (k : ℕ) (p : Fin n)
    (c : Fin n → S) (s : S) : Agrees adv (contAdv hℓ A adv k p c s) k := by
  intro r hr; funext q; simp [contAdv, hr]

/-- The continuation computes the joint execution. -/
lemma st_cont (inp : Fin n → V) (adv : ℕ → Fin n → Multiset (Fin ℓ × M)) (k : ℕ) (p : Fin n)
    (s : S) : ∀ j, ∀ q ∉ byzV n ℓ,
      (mkRun hℓ inp (contAdv hℓ A adv k p ((mkRun hℓ inp adv).st A k) s)).st A (k + j) q =
        (simCfg hℓ A p ((mkRun hℓ inp adv).st A k) s j).1 q := by
  set c := (mkRun hℓ inp adv).st A k
  intro j
  induction j with
  | zero =>
    intro q _
    rw [Nat.add_zero, ← st_eq_of_agrees hℓ A (contAdv_agrees adv k p c s) k le_rfl]
    rfl
  | succ j ih =>
    intro q hq
    rw [← Nat.add_assoc, Run.st_succ, inbox_mkRun, ih q hq]
    simp only [simCfg]
    congr 1
    unfold cfgIn
    congr 1
    · refine Finset.sum_congr rfl fun q' hq' => ?_
      rw [ih q' (by simpa using hq')]
      rfl
    · simp [contAdv]

/-- The swap: two joint executions whose correct processes agree except `p`, with `p` and the
impersonator exchanged. -/
lemma simCfg_swap {p : Fin n} (hp : p ∉ byzV n ℓ) {c₁ c₂ : Fin n → S} {s₁ s₂ : S}
    (hc : ∀ q ∉ byzV n ℓ, q ≠ p → c₁ q = c₂ q) (h1 : s₁ = c₂ p) (h2 : s₂ = c₁ p) :
    ∀ j, (∀ q ∉ byzV n ℓ, q ≠ p → (simCfg hℓ A p c₁ s₁ j).1 q = (simCfg hℓ A p c₂ s₂ j).1 q) ∧
      (simCfg hℓ A p c₂ s₂ j).2 = (simCfg hℓ A p c₁ s₁ j).1 p ∧
      (simCfg hℓ A p c₁ s₁ j).2 = (simCfg hℓ A p c₂ s₂ j).1 p := by
  intro j
  induction j with
  | zero => exact ⟨hc, h2, h1⟩
  | succ j ih =>
    obtain ⟨ihc, ih1, ih2⟩ := ih
    set d₁ := simCfg hℓ A p c₁ s₁ j
    set d₂ := simCfg hℓ A p c₂ s₂ j
    -- the inboxes coincide
    have hin : ∀ q, cfgIn hℓ A d₁.1 d₁.2 q = cfgIn hℓ A d₂.1 d₂.2 q := by
      intro q
      unfold cfgIn
      have hsplit : ∀ d : Fin n → S, ∑ q' ∈ univ.filter (· ∉ byzV n ℓ), msgC hℓ A (d q') q' q =
          (∑ q' ∈ (univ.filter (· ∉ byzV n ℓ)).erase p, msgC hℓ A (d q') q' q) + msgB hℓ A (d p) q := by
        intro d
        rw [← Finset.sum_erase_add _ _ (by simpa using hp)]
        congr 1
        simp [msgC, msgB, idV_of_correct hℓ hp]
      rw [hsplit, hsplit]
      have hrest : ∑ q' ∈ (univ.filter (· ∉ byzV n ℓ)).erase p, msgC hℓ A (d₁.1 q') q' q =
          ∑ q' ∈ (univ.filter (· ∉ byzV n ℓ)).erase p, msgC hℓ A (d₂.1 q') q' q := by
        refine Finset.sum_congr rfl fun q' hq' => ?_
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
        rw [ihc q' hq'.2 hq'.1]
      rw [hrest, ih2, ← ih1]
      abel
    refine ⟨fun q hq hqp => ?_, ?_, ?_⟩
    · show A.step (d₁.1 q) (cfgIn hℓ A d₁.1 d₁.2 q) = A.step (d₂.1 q) (cfgIn hℓ A d₂.1 d₂.2 q)
      rw [ihc q hq hqp, hin]
    · show A.step d₂.2 (cfgIn hℓ A d₂.1 d₂.2 p) = A.step (d₁.1 p) (cfgIn hℓ A d₁.1 d₁.2 p)
      rw [← hin, ih1]
    · show A.step d₁.2 (cfgIn hℓ A d₁.1 d₁.2 p) = A.step (d₂.1 p) (cfgIn hℓ A d₂.1 d₂.2 p)
      rw [hin, ih2]

/-- **Lemma 17.** If two runs give the same states to all correct processes except `p` up to
round `k`, some decision is reachable from both configurations at round `k`. -/
theorem exists_common_dec (hA : Good n hℓ A) (hn : ℓ + 1 < n) {inp₁ inp₂ : Fin n → V}
    {adv₁ adv₂ : ℕ → Fin n → Multiset (Fin ℓ × M)} (h₁ : ∀ r, AdvOK (adv₁ r))
    (h₂ : ∀ r, AdvOK (adv₂ r)) {k : ℕ} {p : Fin n} (hp : p ∉ byzV n ℓ)
    (hst : ∀ r ≤ k, ∀ q ∉ byzV n ℓ, q ≠ p →
      (mkRun hℓ inp₁ adv₁).st A r q = (mkRun hℓ inp₂ adv₂).st A r q) :
    ∃ v, v ∈ Dec hℓ A inp₁ adv₁ k ∧ v ∈ Dec hℓ A inp₂ adv₂ k := by
  -- a correct process other than `p`
  obtain ⟨q, hq, hqp⟩ : ∃ q : Fin n, q ∉ byzV n ℓ ∧ q ≠ p := by
    by_cases h : p.val = ℓ
    · exact ⟨⟨ℓ + 1, hn⟩, by simp [mem_byzV], fun e => by rw [← e] at h; simp at h⟩
    · exact ⟨⟨ℓ, by omega⟩, by simp [mem_byzV], fun e => h (by rw [← e])⟩
  set c₁ := (mkRun hℓ inp₁ adv₁).st A k
  set c₂ := (mkRun hℓ inp₂ adv₂).st A k
  set a₁ := contAdv hℓ A adv₁ k p c₁ (c₂ p)
  set a₂ := contAdv hℓ A adv₂ k p c₂ (c₁ p)
  have ha₁ := contAdv_ok (hℓ := hℓ) (A := A) h₁ k p c₁ (c₂ p)
  have ha₂ := contAdv_ok (hℓ := hℓ) (A := A) h₂ k p c₂ (c₁ p)
  obtain ⟨v, r, hr⟩ := (hA inp₁ a₁ ha₁).termination q hq
  refine ⟨v, ⟨a₁, ha₁, contAdv_agrees _ _ _ _ _, r, q, hq, hr⟩, ?_⟩
  by_cases hrk : r ≤ k
  · refine ⟨adv₂, h₂, fun _ _ => rfl, r, q, hq, ?_⟩
    rw [← hst r hrk q hq hqp,
      st_eq_of_agrees hℓ A (contAdv_agrees adv₁ k p c₁ (c₂ p)) r hrk]
    exact hr
  · obtain ⟨j, rfl⟩ : ∃ j, r = k + j := ⟨r - k, by omega⟩
    refine ⟨a₂, ha₂, contAdv_agrees _ _ _ _ _, k + j, q, hq, ?_⟩
    rw [st_cont inp₂ adv₂ k p (c₁ p) j q hq]
    rw [st_cont inp₁ adv₁ k p (c₂ p) j q hq] at hr
    rw [← (simCfg_swap (A := A) hp (c₁ := c₁) (c₂ := c₂)
      (fun q' hq' hq'p => hst k le_rfl q' hq' hq'p) rfl rfl j).1 q hq hqp]
    exact hr

/-! ### Chains of univalent configurations -/

/-- Along a chain of univalent configurations in which consecutive ones share a reachable
decision, the first and the last have the same decision. -/
lemma chain_const {D : ℕ → Set V} {N : ℕ}
    (huni : ∀ j ≤ N, ∀ v ∈ D j, ∀ w ∈ D j, v = w)
    (hcom : ∀ j < N, ∃ v, v ∈ D j ∧ v ∈ D (j + 1)) :
    ∀ v ∈ D 0, ∀ w ∈ D N, v = w := by
  induction N with
  | zero => exact huni 0 le_rfl
  | succ N ih =>
    intro v hv w hw
    obtain ⟨u, hu, hu'⟩ := hcom N (by omega)
    have := ih (fun j hj => huni j (by omega)) (fun j hj => hcom j (by omega)) v hv u hu
    rw [this]
    exact huni (N + 1) le_rfl u hu' w hw

/-- A correct process with identifier `0` used when the hybrid step changes nothing. -/
def p₀ (hn : ℓ < n) : Fin n := ⟨ℓ, hn⟩

lemma p₀_correct (hn : ℓ < n) : p₀ hn ∉ byzV n ℓ := by simp [p₀, mem_byzV]

/-! ### Lemma 21 -/

/-- The silent adversary. -/
def silent : ℕ → Fin n → Multiset (Fin ℓ × M) := fun _ _ => 0

lemma silent_ok : ∀ r, AdvOK (silent (n := n) (ℓ := ℓ) (M := M) r) := by
  intro r q j; simp [silent]

/-- **Lemma 21.** Some initial configuration is multivalent. -/
theorem exists_multi_init (hA : Good n hℓ A) (hn : ℓ + 1 < n) {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    ∃ inp : Fin n → V, Multi hℓ A inp silent 0 := by
  by_contra hno
  push Not at hno
  set inpj : ℕ → Fin n → V := fun j q => if q.val < j then v₁ else v₀
  set D : ℕ → Set V := fun j => Dec hℓ A (inpj j) silent 0
  have huni : ∀ j ≤ n, ∀ v ∈ D j, ∀ w ∈ D j, v = w := by
    intro j _ v hv w hw
    by_contra hvw
    exact hno (inpj j) ⟨v, w, hvw, hv, hw⟩
  have hcom : ∀ j < n, ∃ v, v ∈ D j ∧ v ∈ D (j + 1) := by
    intro j hj
    set p : Fin n := if (⟨j, hj⟩ : Fin n) ∈ byzV n ℓ then p₀ (ℓ := ℓ) (by omega) else ⟨j, hj⟩
    have hp : p ∉ byzV n ℓ := by
      simp only [p]; split_ifs with h
      · simp [p₀, mem_byzV]
      · exact h
    refine exists_common_dec hA hn silent_ok silent_ok hp ?_
    intro r hr q hq hqp
    obtain rfl : r = 0 := by omega
    have hqj : q.val ≠ j := by
      intro e
      apply hqp
      simp only [p]
      have : (⟨j, hj⟩ : Fin n) = q := Fin.ext e.symm
      rw [this, if_neg hq]
    simp only [Run.st_zero, mkRun, inpj]
    congr 1
    by_cases h : q.val < j
    · simp [h, show q.val < j + 1 by omega]
    · simp [h, show ¬ q.val < j + 1 by omega]
  obtain ⟨v, hvD⟩ := dec_nonempty hA (by omega) (inp := inpj 0) silent_ok 0
  obtain ⟨w, hwD⟩ := dec_nonempty hA (by omega) (inp := inpj n) silent_ok 0
  have hvw := chain_const huni hcom v hvD w hwD
  -- validity pins `v` and `w`
  have hv0 : v = v₀ := by
    obtain ⟨a, ha, -, r, q, hq, hd⟩ := hvD
    exact (hA _ a ha).validity v₀ (fun p _ => by simp [mkRun, inpj]) q hq v ⟨r, hd⟩
  have hw1 : w = v₁ := by
    obtain ⟨a, ha, -, r, q, hq, hd⟩ := hwD
    exact (hA _ a ha).validity v₁ (fun p _ => by simp [mkRun, inpj, p.isLt]) q hq w ⟨r, hd⟩
  exact hv (hv0 ▸ hw1 ▸ hvw)

/-! ### Lemma 22 -/

/-- **Lemma 22.** Every multivalent configuration has a multivalent successor. -/
theorem exists_multi_succ (hA : Good n hℓ A) (hn : ℓ + 1 < n) {inp : Fin n → V}
    {adv : ℕ → Fin n → Multiset (Fin ℓ × M)} (hadv : ∀ r, AdvOK (adv r)) {k : ℕ}
    (hm : Multi hℓ A inp adv k) :
    ∃ a, AdvOK a ∧ Multi hℓ A inp (Function.update adv k a) (k + 1) := by
  by_contra hno
  push Not at hno
  obtain ⟨v, w, hvw, ⟨adv₁, h₁, hag₁, r₁, q₁, hq₁, hd₁⟩, ⟨adv₂, h₂, hag₂, r₂, q₂, hq₂, hd₂⟩⟩ := hm
  set H : ℕ → Fin n → Multiset (Fin ℓ × M) := fun j q => if q.val < j then adv₂ k q else adv₁ k q
  have hH : ∀ j, AdvOK (H j) := by
    intro j q i; simp only [H]; split_ifs
    · exact h₂ k q i
    · exact h₁ k q i
  have hupd : ∀ j, ∀ r, AdvOK (Function.update adv k (H j) r) := by
    intro j r
    by_cases hr : r = k
    · subst hr; simpa using hH j
    · simpa [hr] using hadv r
  set D : ℕ → Set V := fun j => Dec hℓ A inp (Function.update adv k (H j)) (k + 1)
  have huni : ∀ j ≤ n, ∀ x ∈ D j, ∀ y ∈ D j, x = y := by
    intro j _ x hx y hy
    by_contra hxy
    exact hno (H j) (hH j) ⟨x, y, hxy, hx, hy⟩
  have hcom : ∀ j < n, ∃ x, x ∈ D j ∧ x ∈ D (j + 1) := by
    intro j hj
    set p : Fin n := if (⟨j, hj⟩ : Fin n) ∈ byzV n ℓ then p₀ (ℓ := ℓ) (by omega) else ⟨j, hj⟩
    have hp : p ∉ byzV n ℓ := by
      simp only [p]; split_ifs with h
      · simp [p₀, mem_byzV]
      · exact h
    refine exists_common_dec hA hn (hupd j) (hupd (j + 1)) hp ?_
    have hagr : Agrees (Function.update adv k (H j)) (Function.update adv k (H (j + 1))) k := by
      intro r hr; simp [show r ≠ k by omega]
    intro r hr q hq hqp
    rcases Nat.lt_or_ge r (k + 1) with hrk | hrk
    · rw [st_eq_of_agrees hℓ A hagr r (by omega)]
    · obtain rfl : r = k + 1 := by omega
      have hqj : q.val ≠ j := by
        intro e
        apply hqp
        simp only [p]
        have : (⟨j, hj⟩ : Fin n) = q := Fin.ext e.symm
        rw [this, if_neg hq]
      rw [Run.st_succ, Run.st_succ, inbox_mkRun, inbox_mkRun,
        st_eq_of_agrees hℓ A hagr k le_rfl]
      congr 2
      simp only [mkRun, Function.update_self, H]
      by_cases h : q.val < j
      · simp [h, show q.val < j + 1 by omega]
      · simp [h, show ¬ q.val < j + 1 by omega]
  have hv : v ∈ D 0 := by
    refine ⟨adv₁, h₁, ?_, r₁, q₁, hq₁, hd₁⟩
    intro r hr
    by_cases hrk : r = k
    · subst hrk; funext q; simp [H]
    · simp only [Function.update_of_ne hrk]; exact hag₁ r (by omega)
  have hw : w ∈ D n := by
    refine ⟨adv₂, h₂, ?_, r₂, q₂, hq₂, hd₂⟩
    intro r hr
    by_cases hrk : r = k
    · subst hrk; funext q; simp [H, q.isLt]
    · simp only [Function.update_of_ne hrk]; exact hag₂ r (by omega)
  exact hvw (chain_const huni hcom v hv w hw)

/-! ### The infinite undecided run -/

/-- The adversary sequence: at step `k`, choose round `k` so that the configuration stays
multivalent. -/
noncomputable def advSeq (hℓ : 0 < ℓ) (A : Algorithm ℓ V M S) (inp : Fin n → V) :
    ℕ → ℕ → Fin n → Multiset (Fin ℓ × M)
  | 0 => silent
  | k + 1 => Function.update (advSeq hℓ A inp k) k
      (Classical.epsilon fun a => AdvOK a ∧ Multi hℓ A inp (Function.update (advSeq hℓ A inp k) k a)
        (k + 1))

lemma advSeq_spec (hA : Good n hℓ A) (hn : ℓ + 1 < n) {inp : Fin n → V}
    (h0 : Multi hℓ A inp silent 0) :
    ∀ k, (∀ r, AdvOK (advSeq hℓ A inp k r)) ∧ Multi hℓ A inp (advSeq hℓ A inp k) k := by
  intro k
  induction k with
  | zero => exact ⟨silent_ok, h0⟩
  | succ k ih =>
    obtain ⟨hok, hm⟩ := ih
    have hex := exists_multi_succ hA hn hok hm
    have hspec := Classical.epsilon_spec hex
    refine ⟨fun r => ?_, hspec.2⟩
    simp only [advSeq]
    by_cases hr : r = k
    · subst hr; simpa using hspec.1
    · simpa [hr] using hok r

lemma advSeq_agrees {inp : Fin n → V} : ∀ k m, k ≤ m →
    Agrees (advSeq hℓ A inp k) (advSeq hℓ A inp m) k := by
  intro k m hkm
  induction m with
  | zero => obtain rfl : k = 0 := by omega
            exact fun r hr => absurd hr (by omega)
  | succ m ih =>
    rcases Nat.lt_or_ge m k with h | h
    · obtain rfl : k = m + 1 := by omega
      exact fun _ _ => rfl
    · intro r hr
      simp only [advSeq]
      rw [Function.update_of_ne (by omega)]
      exact ih h r hr

/-- The limit adversary. -/
noncomputable def advLim (hℓ : 0 < ℓ) (A : Algorithm ℓ V M S) (inp : Fin n → V) :
    ℕ → Fin n → Multiset (Fin ℓ × M) := fun r => advSeq hℓ A inp (r + 1) r

lemma advLim_agrees {inp : Fin n → V} (k : ℕ) :
    Agrees (advSeq hℓ A inp k) (advLim hℓ A inp) k := by
  intro r hr
  exact (advSeq_agrees (r + 1) k (by omega) r (by omega)).symm

/-- No algorithm satisfies `Good` (for `ℓ + 1 < n` and two distinct values). -/
theorem not_good (hn : ℓ + 1 < n) {v₀ v₁ : V} (hv : v₀ ≠ v₁) : ¬ Good n hℓ A := by
  intro hA
  obtain ⟨inp, h0⟩ := exists_multi_init hA hn hv
  have hspec := advSeq_spec hA hn h0
  have hok : ∀ r, AdvOK (advLim hℓ A inp r) := fun r => (hspec (r + 1)).1 r
  have hmulti : ∀ k, Multi hℓ A inp (advLim hℓ A inp) k :=
    fun k => (multi_congr hℓ A (advLim_agrees k)).1 (hspec k).2
  obtain ⟨q, hq⟩ := exists_correct (n := n) (ℓ := ℓ) (by omega)
  obtain ⟨v, r, hr⟩ := (hA inp _ hok).termination q hq
  rw [undecided_of_multi hA (hmulti r) r le_rfl q hq] at hr
  simp at hr

end Valency

open Valency

/-- **Proposition 16.** Synchronous Byzantine agreement is unsolvable with numerate processes
against restricted Byzantine processes if `ℓ ≤ t` (`n > 3t`, `1 ≤ ℓ`, two distinct values). -/
theorem prop16 {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : 0 < ℓ) (hℓt : ℓ ≤ t) {V : Type}
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) : ¬ Solvable .sync .restricted .numerate n ℓ t V := by
  classical
  rintro ⟨M, S, A, -, hA⟩
  refine not_good (n := n) (hℓ := hℓ) (A := A) (by omega) hv ?_
  intro inp adv hadv
  refine hA (Fin n) (Fintype.card_fin n) (mkRun hℓ inp adv) ⟨⟨?_, ?_, ?_, ?_⟩, fun _ => rfl, fun _ => ?_⟩
  · intro i; exact ⟨⟨i, by omega⟩, by simp [mkRun, idV]⟩
  · refine le_trans (Finset.card_le_card_of_injOn (fun k => (k.val : ℕ)) (t := range ℓ)
      (fun k hk => by simpa [mkRun, mem_byzV] using hk) (fun k _ k' _ e => Fin.ext e)) ?_
    simpa using hℓt
  · intro r p x _
    refine ⟨⟨x.1.val, by omega⟩, by simp [mkRun, mem_byzV], ?_⟩
    simp [mkRun, idV]
  · intro _ _ _ _ _ _ h; exact h
  · intro r p j
    refine le_trans (hadv r p j) ?_
    refine Finset.card_pos.2 ⟨⟨j.val, by omega⟩, ?_⟩
    exact Finset.mem_filter.2 ⟨mem_byzV.2 j.isLt, by simp [mkRun, idV]⟩

end Podc.HomonymsBA
