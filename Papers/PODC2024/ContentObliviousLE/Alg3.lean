import Cslib.Computability.Distributed.ContentOblivious.Model
import Mathlib
import Papers.PODC2024.ContentObliviousLE.RingCounting

/-!
# Algorithm 3: quiescently stabilizing leader election on non-oriented rings

Frei, Gelles, Ghazy, Nolin, *Content-Oblivious Leader Election on Rings*, arXiv 2405.03646,
Section 4 (Algorithm 3, Proposition 14, Lemma 15, Theorem 2).

Each node runs two copies of Algorithm 1, one per direction, without knowing which is which: a
pulse received at `Port_p` is forwarded on `Port_{¬p}` unless the counter `ρ_p` just reached the
virtual ID `vid ID (¬p)`. We keep the virtual IDs `vid : ℕ → Bool → ℕ` (`vid ID i = ID^(i)`)
abstract: Proposition 14 uses `2·ID − 1 + i`, Theorem 2 uses `ID + i`.

The ring is `flipped n flip`: node `v`'s physical port `p` is the oriented port `p xor flip v`
(`true` = towards `v + 1`).
-/

namespace Podc.ContentOblivious.Alg3

open Cslib.ContentOblivious Finset

/-- Local state: ID and the two counters `ρ_0, ρ_1` of pulses received per port. -/
structure S where
  id : ℕ
  r : Bool → ℕ

/-- Algorithm 3 with virtual IDs `vid`. The output (lines 8–16) is a function of the state:
`leader` and `cwPort` (see below). -/
abbrev alg (vid : ℕ → Bool → ℕ) : Algo where
  State := S
  init i := (⟨i, fun _ => 0⟩, fun _ => 1)
  recv s p := (⟨s.id, Function.update s.r p (s.r p + 1)⟩,
    fun q => if q = !p ∧ s.r p + 1 ≠ vid s.id q then 1 else 0)
  leader s := decide (vid s.id true ≤ max (s.r false) (s.r true) ∧ s.r false = vid s.id true ∧
    s.r true < vid s.id true)

/-- The port a node names clockwise (lines 13–16): `Port1` iff `ρ_0 > ρ_1`. -/
def cwPort (s : S) : Bool := decide (s.r true < s.r false)

variable {n : ℕ} [NeZero n] {flip : ZMod n → Bool}

lemma flipped_peer_dir (v : ZMod n) (p : Bool) :
    xor ((flipped n flip).peer (v, p)).2 (flip ((flipped n flip).peer (v, p)).1) =
      !(xor p (flip v)) := by
  cases p <;> cases h : flip v <;> simp [flipped, oriented, h]

lemma flipped_peer_next (v : ZMod n) :
    (flipped n flip).peer (v + 1, flip (v + 1)) = (v, xor true (flip v)) := by
  simp [flipped, oriented]

lemma flipped_peer_prev (v : ZMod n) :
    (flipped n flip).peer (v, !flip v) = (v + 1, xor false (flip (v + 1))) := by
  simp [flipped, oriented]

variable {vid : ℕ → Bool → ℕ} {id : ZMod n → ℕ} {M : Bool → ℕ}

/-- The virtual ID used by `v` for the copy of Algorithm 1 that sends on physical port `p`; the
direction of that copy is `p xor flip v` (`true` = towards `v + 1`). -/
def Inv (flip : ZMod n → Bool) (vid : ℕ → Bool → ℕ) (id : ZMod n → ℕ) (M : Bool → ℕ)
    (c : Config (ZMod n) S) : Prop :=
  ∀ v, (c.st v).id = id v ∧ (∀ p, (c.st v).r p = c.recvd (v, p)) ∧
    (∀ p, c.sent (v, p) = c.recvd (v, !p) + if c.recvd (v, !p) < vid (id v) p then 1 else 0) ∧
    (∀ p, c.recvd (v, !p) ≤ M (xor p (flip v)))

/-- `M d` bounds the virtual IDs of the copy running in direction `d`. -/
def Bounds (flip : ZMod n → Bool) (vid : ℕ → Bool → ℕ) (id : ZMod n → ℕ) (M : Bool → ℕ) : Prop :=
  ∀ v p, vid (id v) p ≤ M (xor p (flip v))

lemma inv_init (hpos : ∀ v p, 0 < vid (id v) p) :
    Inv flip vid id M (initCfg (alg vid) id) := by
  intro v
  refine ⟨rfl, fun p => rfl, fun p => ?_, fun p => Nat.zero_le _⟩
  simp [initCfg, hpos v p]

lemma inv_step (hB : Bounds flip vid id M) {c : Config (ZMod n) S} (h : Inv flip vid id M c)
    {v : ZMod n} {p : Bool} (hen : Enabled (flipped n flip) (alg vid) c v p) :
    Inv flip vid id M (deliver (alg vid) c v p) := by
  obtain ⟨-, -, hlt⟩ := hen
  -- bound for the receiving counter
  set w := ((flipped n flip).peer (v, p)).1 with hw
  set q := ((flipped n flip).peer (v, p)).2 with hq
  have hpeer : (flipped n flip).peer (v, p) = (w, q) := rfl
  have hdir : xor q (flip w) = !(xor p (flip v)) := flipped_peer_dir v p
  have hsent : c.sent (w, q) ≤ M (xor q (flip w)) := by
    obtain ⟨-, -, h3, h4⟩ := h w
    rw [h3 q]; have := h4 q; have := hB w q; split_ifs <;> omega
  rw [hpeer] at hlt
  have hbnd : c.recvd (v, p) + 1 ≤ M (!(xor p (flip v))) := by rw [← hdir]; omega
  intro u
  by_cases hu : u = v
  · subst hu
    obtain ⟨h1, h2, h3, h4⟩ := h u
    refine ⟨by simp [deliver, h1], fun k => ?_, fun k => ?_, fun k => ?_⟩
    · by_cases hk : k = p
      · subst hk; simp [deliver, h2]
      · simp [deliver, h2, Function.update_of_ne hk, hk]
    · by_cases hk : k = !p
      · subst hk
        simp only [deliver_sent, deliver_recvd, h3, if_true, Bool.not_not, h1, h2]
        simp
        split_ifs <;> omega
      · have hk' : k = p := by cases k <;> cases p <;> simp at hk ⊢
        subst hk'
        simp only [deliver_sent, deliver_recvd, h3]
        simp
    · by_cases hk : k = !p
      · subst hk
        have e1 : (deliver (alg vid) c u p).recvd (u, !!p) = c.recvd (u, p) + 1 := by simp [deliver]
        have e2 : xor (!p) (flip u) = !(xor p (flip u)) := by cases p <;> simp
        rw [e1, e2]; exact hbnd
      · have hk' : k = p := by cases k <;> cases p <;> simp at hk ⊢
        subst hk'
        have e1 : (deliver (alg vid) c u k).recvd (u, !k) = c.recvd (u, !k) := by
          simp [deliver]
        rw [e1]; exact h4 k
  · obtain ⟨h1, h2, h3, h4⟩ := h u
    refine ⟨by simp [deliver, hu, h1], fun k => ?_, fun k => ?_, fun k => ?_⟩
    · simp [deliver, hu, h2]
    · simp [deliver, hu, h3]
    · simp [deliver, hu, h4]

theorem reach_inv (hpos : ∀ v p, 0 < vid (id v) p) (hB : Bounds flip vid id M)
    {c : Config (ZMod n) S} (h : Reach (flipped n flip) (alg vid) id c) : Inv flip vid id M c := by
  induction h with
  | refl => exact inv_init hpos
  | tail _ hs ih => obtain ⟨v, j, hen⟩ := hs; exact inv_step hB ih hen

/-- **Lemma 15, applied to both directions** (proof of Proposition 14 / Theorem 2): in a final
configuration the network is quiescent and every node has received exactly `M d` pulses of the copy
running in direction `d` (`M d` = the maximal virtual ID in that direction, attained at some node). -/
theorem final_counts (hpos : ∀ v p, 0 < vid (id v) p) (hB : Bounds flip vid id M)
    (hM : ∀ d, ∃ v p, xor p (flip v) = d ∧ vid (id v) p = M d)
    {c : Config (ZMod n) S} (hr : Reach (flipped n flip) (alg vid) id c)
    (hfin : Final (flipped n flip) (alg vid) c) :
    Quiescent (flipped n flip) (alg vid) c ∧
      ∀ v p, c.recvd (v, !p) = M (xor p (flip v)) ∧ c.sent (v, p) = M (xor p (flip v)) := by
  have h := reach_inv hpos hB hr
  have hq : Quiescent (flipped n flip) (alg vid) c := by
    intro x
    by_contra hne
    apply hfin x.1 x.2
    exact ⟨rfl, rfl, lt_of_le_of_ne (hr.recvd_le x) hne⟩
  refine ⟨hq, ?_⟩
  -- direction `true` (towards `v + 1`): sending port `xor true (flip v)`
  have hT : ∀ v, c.recvd (v, !(xor true (flip v))) = M true ∧
      c.sent (v, xor true (flip v)) = M true := by
    have hprof : Ring.Profile (fun v => c.recvd (v, !(xor true (flip v))))
        (fun v => c.sent (v, xor true (flip v))) (fun v => vid (id v) (xor true (flip v))) :=
      fun v => (h v).2.2.1 _
    have htight : ∀ v, c.recvd (v + 1, !(xor true (flip (v + 1)))) = c.sent (v, xor true (flip v)) := by
      intro v; have := hq (v + 1, flip (v + 1)); rw [flipped_peer_next] at this
      simpa using this
    have hgood := hprof.good_of_tight htight
    obtain ⟨v0, p0, hd, hv0⟩ := hM true
    have hp0 : p0 = xor true (flip v0) := by cases p0 <;> cases h' : flip v0 <;> simp_all
    subst hp0
    exact hprof.eq_max_of_good (fun v => (htight v).le) hgood
      (fun v => by have := (h v).2.2.2 (xor true (flip v)); simpa using this) hv0
  have hF : ∀ v, c.recvd (v, !(xor false (flip v))) = M false ∧
      c.sent (v, xor false (flip v)) = M false := by
    have hprof : Ring.Profile (fun v => c.recvd (-v, !(xor false (flip (-v)))))
        (fun v => c.sent (-v, xor false (flip (-v)))) (fun v => vid (id (-v)) (xor false (flip (-v)))) :=
      fun v => (h (-v)).2.2.1 _
    have htight : ∀ v, c.recvd (-(v + 1), !(xor false (flip (-(v + 1))))) =
        c.sent (-v, xor false (flip (-v))) := by
      intro v
      have := hq (-(v + 1), !flip (-(v + 1)))
      rw [flipped_peer_prev] at this
      simp only [Bool.false_xor] at this ⊢
      rw [this, show -(v + 1) + 1 = -v by ring]
    have hgood := hprof.good_of_tight htight
    obtain ⟨v0, p0, hd, hv0⟩ := hM false
    have hp0 : p0 = xor false (flip v0) := by cases p0 <;> cases h' : flip v0 <;> simp_all
    subst hp0
    have := hprof.eq_max_of_good (fun v => (htight v).le) hgood
      (fun v => by have := (h (-v)).2.2.2 (xor false (flip (-v))); simpa using this) (ℓ := -v0)
      (by simpa using hv0)
    intro v; simpa using this (-v)
  intro v p
  cases hd : xor p (flip v)
  · have hp : p = xor false (flip v) := by cases p <;> cases h' : flip v <;> simp_all
    subst hp; exact hF v
  · have hp : p = xor true (flip v) := by cases p <;> cases h' : flip v <;> simp_all
    subst hp; exact hT v

/-- Message complexity of Algorithm 3: never more than `n (M true + M false)` pulses. -/
theorem totalSent_le (hpos : ∀ v p, 0 < vid (id v) p) (hB : Bounds flip vid id M)
    {c : Config (ZMod n) S} (hr : Reach (flipped n flip) (alg vid) id c) :
    totalSent c ≤ n * (M true + M false) := by
  have h := reach_inv hpos hB hr
  have : ∀ v p, c.sent (v, p) ≤ M (xor p (flip v)) := by
    intro v p
    obtain ⟨-, -, h3, h4⟩ := h v
    rw [h3 p]; have := h4 p; have := hB v p; split_ifs <;> omega
  rw [totalSent, sum_ports]
  calc ∑ v, (c.sent (v, false) + c.sent (v, true)) ≤ ∑ _v : ZMod n, (M true + M false) := by
        refine sum_le_sum fun v _ => ?_
        have h0 := this v false; have h1 := this v true
        cases hf : flip v <;> simp [hf] at h0 h1 <;> omega
    _ = n * (M true + M false) := by simp [ZMod.card]

/-- In a final configuration exactly `n (M true + M false)` pulses have been sent. -/
theorem totalSent_final (hpos : ∀ v p, 0 < vid (id v) p) (hB : Bounds flip vid id M)
    (hM : ∀ d, ∃ v p, xor p (flip v) = d ∧ vid (id v) p = M d)
    {c : Config (ZMod n) S} (hr : Reach (flipped n flip) (alg vid) id c)
    (hfin : Final (flipped n flip) (alg vid) c) : totalSent c = n * (M true + M false) := by
  have h := (final_counts hpos hB hM hr hfin).2
  rw [totalSent, sum_ports]
  have : ∀ v, c.sent (v, false) + c.sent (v, true) = M true + M false := by
    intro v; rw [(h v false).2, (h v true).2]; cases flip v <;> simp [add_comm]
  simp [this, ZMod.card]

end Podc.ContentOblivious.Alg3
