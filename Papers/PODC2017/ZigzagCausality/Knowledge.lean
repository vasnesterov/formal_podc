import Papers.PODC2017.ZigzagCausality.Zigzag
import Cslib.Computability.Distributed.Knowledge.Basic

/-!
# Knowledge in full-information protocols: Lemma 3 and the Visible Zigzag Theorem (⇐)

Dan, Manohar, Moses, *On Using Time Without Clocks via Zigzag Causality*, PODC 2017.

* `HB.transfer` — **Lemma 3**: in a full-information protocol, if `σ' ⇝_r σ` and `σ` appears in
  `r'`, then `σ' ⇝_{r'} σ`. Consequently the past of `σ` is the same set of basic nodes in all runs
  in which `σ` appears (`HB_iff_of_appears`), with the same message relation between its nodes
  (`recv_iff_of_past`) and the same local order on each process (`timer_le_iff_of_appears`).
* For flooding FIPs, message chains that start in the past of `σ` exist in every run in which `σ`
  appears: their prefix inside the past is the same, and once they leave the past they stay
  outside it (`gbasic_transfer`). Hence a σ-visible zigzag pattern of `r` is a zigzag pattern of
  the same weight in every run `r' ∼_σ r` (`zigzag_transfer`).
* `visible_zigzag_sufficiency` — **Theorem 4 (Visible Zigzag Theorem), direction (⇐)**.
* `indistSys`, `knows_iff_K` — a bridge to CSLib's indistinguishability systems
  (`Cslib.Knowledge.IndistSystem`): `Knows σ φ` is `K_σ φ` at every run in which `σ` appears.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

namespace Sys

variable {γ : Sys P S M E} {r r' : Sched P S E} [Finite P]

/-! ### Lemma 3 and the past of a node -/

theorem init_of_appears {σ : BNode P S M E} (h : γ.appears r σ) : σ.2.init = r.g σ.1 := by
  have := γ.st_init r (γ.timer r σ) σ.1
  rwa [γ.st_timer r h] at this

/-- If `σ` precedes `τ` on the same process in `r` and `τ` appears in `r'`, then `σ` appears in
`r'` and precedes `τ` there as well (local states only grow by appending). -/
theorem appears_of_local {σ τ : BNode P S M E} (hσ : γ.appears r σ) (hτ : γ.appears r τ)
    (hp : σ.1 = τ.1) (hle : γ.timer r σ ≤ γ.timer r τ) (hτ' : γ.appears r' τ) :
    γ.appears r' σ ∧ γ.timer r' σ ≤ γ.timer r' τ := by
  have hpre := (γ.timer_le_iff_prefix r hp hσ hτ).1 hle
  have hσeq : σ = (τ.1, ⟨τ.2.init, τ.2.hist.take σ.2.hist.length⟩) := by
    refine Prod.ext hp (LState.ext' ?_ ?_)
    · simp only; rw [init_of_appears hσ, init_of_appears hτ, hp]
    · exact List.prefix_iff_eq_take.1 hpre
  have ha := γ.appears_take r' (i := τ.1) (ℓ := τ.2) hτ' σ.2.hist.length
  rw [← hσeq] at ha
  exact ha

/-- In an FIP, a message received at a node that appears in `r'` was sent in `r'` by the same
node (its content determines the sender's state). -/
theorem recv_transfer (hF : γ.IsFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {a b : BNode P S M E} {j : P} (h : γ.recv r a j = some b) (hb : γ.appears r' b) :
    γ.recv r' a j = some b := by
  obtain ⟨m, hm, bt, hbt, hmem⟩ := recv_mem_last hr h
  obtain ⟨a', ha', hrecv, hm'⟩ := exists_recv_of_mem_last hr' hb hbt hmem
  have hj : b.1 = j := (recv_spec hr h).1
  have h2 : a'.2 = a.2 := hF _ _ _ _ _ _ hm' hm
  have : a' = a := Prod.ext ha' h2
  rw [this, hj] at hrecv
  exact hrecv

theorem hbStep_transfer (hF : γ.IsFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {a b : BNode P S M E} (h : γ.HBStep r a b) (hb : γ.appears r' b) : γ.HBStep r' a b := by
  rcases h with ⟨ha, hb0, hp, hle⟩ | ⟨j, hj⟩
  · obtain ⟨ha', hle'⟩ := appears_of_local ha hb0 hp hle hb
    exact Or.inl ⟨ha', hb, hp, hle'⟩
  · exact Or.inr ⟨j, recv_transfer hF hr hr' hj hb⟩

/-- **Lemma 3.** Let `P` be an FIP and `r, r' ∈ R(P, γ)`. If `σ' ⇝_r σ` and `r' ∼_σ r` (i.e. `σ`
appears in `r'`), then `σ' ⇝_{r'} σ`. -/
theorem HB.transfer (hF : γ.IsFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ' σ : BNode P S M E} (h : γ.HB r σ' σ) (hσ : γ.appears r' σ) : γ.HB r' σ' σ := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact .single (hbStep_transfer hF hr hr' h hσ)
  | head h _ ih => exact .head (hbStep_transfer hF hr hr' h (HB.appears ih).1) ih

/-- In an FIP the past of `σ` is the same set of basic nodes in all runs in which `σ` appears. -/
theorem HB_iff_of_appears (hF : γ.IsFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ τ : BNode P S M E} (hσ : γ.appears r σ) (hσ' : γ.appears r' σ) :
    γ.HB r τ σ ↔ γ.HB r' τ σ :=
  ⟨fun h => HB.transfer hF hr hr' h hσ', fun h => HB.transfer hF hr' hr h hσ⟩

/-- In an FIP the message relation into the past of `σ` is the same in all runs in which `σ`
appears. -/
theorem recv_iff_of_past (hF : γ.IsFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ a b : BNode P S M E} {j : P} (hσ' : γ.appears r' σ)
    (hb : γ.HB r b σ) : γ.recv r a j = some b ↔ γ.recv r' a j = some b := by
  have hb' := HB.transfer hF hr hr' hb hσ'
  exact ⟨fun h => recv_transfer hF hr hr' h (HB.appears hb').1,
    fun h => recv_transfer hF hr' hr h (HB.appears hb).1⟩

/-- The local order between nodes of the same process does not depend on the run. -/
theorem timer_le_iff_of_appears {a b : BNode P S M E} (hp : a.1 = b.1) (ha : γ.appears r a)
    (hb : γ.appears r b) (ha' : γ.appears r' a) (hb' : γ.appears r' b) :
    γ.timer r a ≤ γ.timer r b ↔ γ.timer r' a ≤ γ.timer r' b := by
  rw [γ.timer_le_iff_prefix r hp ha hb, γ.timer_le_iff_prefix r' hp ha' hb']

/-- Whether a node is initial does not depend on the run. -/
theorem timer_pos_iff_of_appears {a : BNode P S M E} (ha : γ.appears r a)
    (ha' : γ.appears r' a) : 0 < γ.timer r a ↔ 0 < γ.timer r' a := by
  rw [γ.timer_pos_iff r ha, γ.timer_pos_iff r' ha']

/-! ### Message chains starting in the past (flooding FIPs) -/

/-- A message from the past of `σ` to a node outside the past of `σ` in `r` leads, in any run
`r'` in which `σ` appears, to a node outside the past of `σ` in `r'` (flooding FIP). -/
theorem recv_out_of_past (hF : γ.IsFFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ : BNode P S M E} (hσ' : γ.appears r' σ) {a b : BNode P S M E} {j : P}
    (h : γ.recv r a j = some b) (ha : γ.HB r a σ) (hb : ¬ γ.HB r b σ) :
    ∃ b', γ.recv r' a j = some b' ∧ ¬ γ.HB r' b' σ := by
  have hσ : γ.appears r σ := (HB.appears ha).2
  have ha' : γ.appears r' a := (HB.appears (HB.transfer hF.1 hr hr' ha hσ')).1
  have h0 := recv_appears_left h
  have h0' : 0 < γ.timer r' a := (timer_pos_iff_of_appears h0.1 ha').1 h0.2
  have hc := (recv_spec hr h).2.2.1
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (recv_isSome_of_FFIP hF ha' h0' hc)
  refine ⟨b', hb', fun hb'σ => hb ?_⟩
  have hb'r := HB.transfer hF.1 hr' hr hb'σ hσ
  have e := recv_transfer hF.1 hr' hr hb' (HB.appears hb'r).1
  rw [h] at e
  cases e
  exact hb'r

/-- A message chain of `r` that has left the past of `σ` can be followed in `r'` from any
non-initial node of the same process outside the past of `σ` in `r'`; it stays outside the past. -/
theorem gbasic_nonpast (hF : γ.IsFFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ : BNode P S M E} :
    ∀ (q : List P) {τ τ' υ : BNode P S M E}, τ.1 = τ'.1 → γ.appears r' τ' →
      0 < γ.timer r' τ' → ¬ γ.HB r' τ' σ → γ.gbasic r τ q = some υ →
      ∃ υ', γ.gbasic r' τ' q = some υ' ∧ ¬ γ.HB r' υ' σ
  | [], _, τ', _, _, ha, _, hn, _ => ⟨τ', γ.gbasic_self r' ha, hn⟩
  | j :: q, τ, τ', υ, hp, ha, h0, hn, h => by
    simp only [gbasic_cons] at h
    obtain ⟨τ1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have hc : γ.net.Chan τ'.1 j := hp ▸ (recv_spec hr h1).2.2.1
    obtain ⟨τ1', h1'⟩ := Option.isSome_iff_exists.1 (recv_isSome_of_FFIP hF ha h0 hc)
    have hs := recv_spec hr' h1'
    have hs1 := recv_spec hr h1
    have hL := γ.net.one_le_L _ _ hc
    have hle := hs.2.2.2.2.1
    obtain ⟨υ', hυ', hn'⟩ := gbasic_nonpast hF hr hr' q (hs1.1.trans hs.1.symm) hs.2.1
      (by omega) (fun hh => hn ((HB.of_recv h1').trans hh)) h2
    exact ⟨υ', by simp only [gbasic_cons, h1', Option.bind_some]; exact hυ', hn'⟩

/-- **Message chains from the past of `σ` (flooding FIP).** If `ρ ⇝_r σ`, `σ` appears in `r'`
and the chain from `ρ` along `q` ends at `υ` in `r`, then it ends at some `υ'` in `r'`; if `υ` is
in the past of `σ` then `υ' = υ`, otherwise `υ'` is not in the past of `σ` in `r'`. -/
theorem gbasic_transfer (hF : γ.IsFFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ : BNode P S M E} (hσ' : γ.appears r' σ) :
    ∀ (q : List P) {ρ υ : BNode P S M E}, γ.HB r ρ σ → γ.gbasic r ρ q = some υ →
      ∃ υ', γ.gbasic r' ρ q = some υ' ∧ (γ.HB r υ σ → υ' = υ) ∧
        (¬ γ.HB r υ σ → ¬ γ.HB r' υ' σ)
  | [], ρ, υ, hρ, h => by
    simp only [gbasic_nil] at h
    split_ifs at h
    cases h
    exact ⟨ρ, γ.gbasic_self r' (HB.appears (HB.transfer hF.1 hr hr' hρ hσ')).1, fun _ => rfl,
      fun hn => absurd hρ hn⟩
  | j :: q, ρ, υ, hρ, h => by
    simp only [gbasic_cons] at h
    obtain ⟨ρ1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    by_cases hp1 : γ.HB r ρ1 σ
    · have h1' := (recv_iff_of_past hF.1 hr hr' hσ' hp1).1 h1
      obtain ⟨υ', e, h3, h4⟩ := gbasic_transfer hF hr hr' hσ' q hp1 h2
      exact ⟨υ', by simp only [gbasic_cons, h1', Option.bind_some]; exact e, h3, h4⟩
    · obtain ⟨ρ1', h1', hn'⟩ := recv_out_of_past hF hr hr' hσ' h1 hρ hp1
      have hnυ : ¬ γ.HB r υ σ := fun hh => hp1 ((HB.of_gbasic h2).trans hh)
      have hs := recv_spec hr' h1'
      have hs1 := recv_spec hr h1
      have hL := γ.net.one_le_L _ _ hs.2.2.1
      have hle := hs.2.2.2.2.1
      obtain ⟨υ', e, hn⟩ := gbasic_nonpast hF hr hr' q (hs1.1.trans hs.1.symm) hs.2.1
        (by omega) hn' h2
      exact ⟨υ', by simp only [gbasic_cons, h1', Option.bind_some]; exact e,
        fun hh => absurd hh hnυ, fun _ => hn⟩

/-- `gbasic_transfer` for general nodes. -/
theorem basic_transfer (hF : γ.IsFFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ : BNode P S M E} (hσ' : γ.appears r' σ) {θ : GNode P S M E} {υ : BNode P S M E}
    (hθ : γ.HB r θ.root σ) (h : γ.basic r θ = some υ) :
    ∃ υ', γ.basic r' θ = some υ' ∧ (γ.HB r υ σ → υ' = υ) ∧
      (¬ γ.HB r υ σ → ¬ γ.HB r' υ' σ) :=
  gbasic_transfer hF hr hr' hσ' θ.path hθ h

theorem basic_appears {θ : GNode P S M E} {υ : BNode P S M E} (h : γ.basic r θ = some υ) :
    γ.appears r υ := (γ.gbasic_appears r h).2

/-! ### Visible zigzag patterns persist -/

/-- A fork whose base is σ-recognized is a fork in every run in which `σ` appears. -/
theorem forkIn_transfer (hF : γ.IsFFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ : BNode P S M E} (hσ' : γ.appears r' σ) {F : Fork P S M E}
    (hroot : γ.HB r F.base.root σ) (h : γ.ForkIn r F) : γ.ForkIn r' F := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.1 h.1
  obtain ⟨υ, hυ⟩ := Option.isSome_iff_exists.1 h.2
  obtain ⟨τ', hτ', -⟩ := basic_transfer hF hr hr' hσ' (θ := F.head) hroot hτ
  obtain ⟨υ', hυ', -⟩ := basic_transfer hF hr hr' hσ' (θ := F.tail) hroot hυ
  exact ⟨by simp [appearsG, hτ'], by simp [appearsG, hυ']⟩

/-- A junction whose first node is in the past of `σ` is preserved, with the same gap, in every
run in which `σ` appears: a node outside the past of `σ` is later than every node of its process
in the past of `σ`. -/
theorem adj_transfer (hF : γ.IsFFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ : BNode P S M E} (hσ' : γ.appears r' σ) {θ θ' : GNode P S M E}
    (hθ : γ.HB r θ.root σ) (hθ' : γ.HB r θ'.root σ) {τ : BNode P S M E}
    (hτ : γ.basic r θ = some τ) (hτσ : γ.HB r τ σ) (hadj : γ.Adj r θ θ') :
    γ.Adj r' θ θ' ∧ γ.gap r' θ θ' = γ.gap r θ θ' := by
  obtain ⟨τ0, υ, h1, h2, hp, hle⟩ := hadj
  rw [hτ] at h1
  cases h1
  obtain ⟨τ', e1, e1', -⟩ := basic_transfer hF hr hr' hσ' hθ hτ
  obtain rfl := e1' hτσ
  obtain ⟨υ', e2, e2a, e2b⟩ := basic_transfer hF hr hr' hσ' hθ' h2
  have hτσ' := HB.transfer hF.1 hr hr' hτσ hσ'
  have hτ' : γ.appears r' τ' := (HB.appears hτσ').1
  by_cases hυ : γ.HB r υ σ
  · obtain rfl := e2a hυ
    have hυ' := (HB.appears (HB.transfer hF.1 hr hr' hυ hσ')).1
    refine ⟨⟨τ', υ', e1, e2, hp, (appears_of_local (basic_appears hτ) (basic_appears h2) hp hle
      hυ').2⟩, ?_⟩
    simp only [gap, e1, e2, hτ, h2]
  · have hn := e2b hυ
    have hpυ : υ'.1 = υ.1 := by rw [γ.basic_proc r' e2, γ.basic_proc r h2]
    have hlt : γ.timer r' τ' ≤ γ.timer r' υ' := by
      by_contra hc
      push Not at hc
      exact hn ((HB.of_local (basic_appears e2) hτ' (hpυ.trans hp.symm) hc.le).trans hτσ')
    refine ⟨⟨τ', υ', e1, e2, hp.trans hpυ.symm, hlt⟩, ?_⟩
    have n1 : τ' ≠ υ := fun e => hυ (e ▸ hτσ)
    have n2 : τ' ≠ υ' := fun e => hn (e ▸ hτσ')
    simp only [gap, e1, e2, hτ, h2, Option.some.injEq, n1, n2, ite_false]

/-- The root of the first fork of a σ-visible zigzag pattern is in the past of `σ`. -/
theorem Visible.root {σ : BNode P S M E} :
    ∀ {F : Fork P S M E} {Z : List (Fork P S M E)}, γ.Visible r σ (F :: Z) →
      γ.HB r F.base.root σ
  | _, [], h => h
  | _, _ :: _, h => by
    obtain ⟨⟨τ, hτ, hτσ⟩, -⟩ := h
    exact (HB.of_gbasic hτ).trans hτσ

/-- A σ-visible zigzag pattern of `r` is a zigzag pattern with the same weight in every run `r'`
in which `σ` appears (flooding FIP). -/
theorem zigzag_transfer (hF : γ.IsFFIP) (hr : γ.Valid r) (hr' : γ.Valid r')
    {σ : BNode P S M E} (hσ' : γ.appears r' σ) :
    ∀ {Z : List (Fork P S M E)} {θ₁ θ₂ : GNode P S M E}, γ.IsZigzag r Z θ₁ θ₂ →
      γ.Visible r σ Z → γ.IsZigzag r' Z θ₁ θ₂ ∧ γ.wtZ r' Z = γ.wtZ r Z
  | [], _, _, h, _ => h.elim
  | [_], _, _, ⟨hF', h1, h2⟩, hV => ⟨⟨forkIn_transfer hF hr hr' hσ' hV hF', h1, h2⟩, by simp [wtZ]⟩
  | F :: G :: Z, _, _, ⟨hF', h1, hadj, hZ⟩, hV => by
    have hroot := Visible.root hV
    obtain ⟨⟨τ, hτ, hτσ⟩, hV'⟩ := hV
    obtain ⟨hadj', hgap⟩ := adj_transfer hF hr hr' hσ' (θ := F.head) (θ' := G.tail) hroot
      (Visible.root hV') hτ hτσ hadj
    obtain ⟨hZ', hw⟩ := zigzag_transfer hF hr hr' hσ' hZ hV'
    exact ⟨⟨forkIn_transfer hF hr hr' hσ' hroot hF', h1, hadj', hZ'⟩,
      by simp only [wtZ, hgap, hw]⟩

/-- **Theorem 4 (Visible Zigzag Theorem), direction (⇐).** Let `P` be an FFIP and `σ` a basic
node of `r ∈ R(P, γ)`. If there is a σ-visible zigzag pattern `Z` from `θ₁` to `θ₂` in `r` with
`wt(Z) ≥ x`, then `(R, r) ⊨ K_σ(θ₁ --x--> θ₂)`.

(The paper also assumes that `θ₁, θ₂` are σ-recognized with positive timers; this direction does
not need it: the endpoints of a σ-visible zigzag pattern are automatically σ-recognized.) -/
theorem visible_zigzag_sufficiency (hF : γ.IsFFIP) (hr : γ.Valid r) {σ : BNode P S M E}
    {Z : List (Fork P S M E)} {θ₁ θ₂ : GNode P S M E} (hZ : γ.IsZigzag r Z θ₁ θ₂)
    (hV : γ.Visible r σ Z) {x : ℤ} (hx : x ≤ γ.wtZ r Z) :
    γ.Knows σ (fun r' => γ.Prec r' θ₁ x θ₂) := by
  intro r' hr' hσ'
  obtain ⟨hZ', hw⟩ := zigzag_transfer hF hr hr' hσ' hZ hV
  obtain ⟨a, b, ha, hb, hab⟩ := zigzag_sufficiency hr' hZ'
  exact ⟨a, b, ha, hb, by rw [hw] at hab; omega⟩

/-! ### Bridge to CSLib's knowledge operator -/

variable (γ) in
/-- The runs of `R(P, γ)` as an indistinguishability system: `r ∼_σ r'` iff `σ` appears in both
runs or in neither. -/
noncomputable def indistSys :
    Cslib.Knowledge.IndistSystem (BNode P S M E) {r : Sched P S E // γ.Valid r} where
  indist σ r r' := (γ.appears r.1 σ ↔ γ.appears r'.1 σ)
  equiv _ := ⟨fun _ => Iff.rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- At a run in which `σ` appears, `Knows σ φ` is CSLib's `K_σ φ` in `indistSys γ`. -/
theorem knows_iff_K {σ : BNode P S M E} {φ : Sched P S E → Prop}
    {w : {r : Sched P S E // γ.Valid r}} (hw : γ.appears w.1 σ) :
    γ.Knows σ φ ↔ (indistSys γ).K σ (fun w' => φ w'.1) w := by
  constructor
  · intro h w' hw'
    exact h w'.1 w'.2 (hw'.1 hw)
  · intro h r' hr' hσ'
    exact h ⟨r', hr'⟩ (iff_of_true hw hσ')

end Sys

end Podc.ZigzagCausality
