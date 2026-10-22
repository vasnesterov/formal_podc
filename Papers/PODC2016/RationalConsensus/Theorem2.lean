import Papers.PODC2016.RationalConsensus.Fairness

/-!
# Theorem 2: `σ_cons` solves fair consensus

[Halpern, Vilaça, *Rational Consensus*, PODC 2016], Theorem 2: `σ_cons` solves fair consensus if at
most `f` agents crash, `f + 1 < n`, and nobody deviates.

Analysis of the runs of `σ_cons` in which nobody deviates:
* `recTab_H`: the status reports computed by the protocol are the records `ghost` of the failure
  pattern (`Records.lean`), so all nonfaulty agents agree on the decision set `NC` (`ghost_agree`);
* `secret_H`: every nonfaulty agent reconstructs `x_l[t]` for every `l ∈ NC` — *provided* it gets a
  second share of `l`'s polynomial in round `f + 1` (`ShareCond`);
* `decideVal_H`: all nonfaulty agents decide the preference of the same random dictator; fairness
  follows from `seedMeasure_dictator` (`Fairness.lean`).

Results: `theorem_2` (Algorithm 1 as written: line 20 forwards `(y_li)_{l ≠ j}`, including the
sender's own share `y_ii`; every `f + 1 < n`), `theorem_2_receivedOnly` (the prose reading "forward
only the shares received", `f ≥ 1` and `f + 3 ≤ n`), `theorem_2_receivedOnly_false` (the prose
reading fails for `n = f + 2` and for `f = 0`: some nonfaulty agent cannot interpolate and decides
`⊥`).
-/

namespace Podc.RationalConsensus.Cons

open Cslib Cslib.SyncCrash Classical MeasureTheory

variable {n f p : ℕ} {ss : Bool}

/-- The history of `q` after `t` rounds of `σ_cons`. -/
noncomputable abbrev H (ss : Bool) (c : Context (Fin n)) (ω : Fin n → Seed n f p) (t : ℕ)
    (q : Fin n) : Hist n f p :=
  SyncCrash.hist (sigmaCons ss) (c.run ω) t q

section Run

variable (c : Context (Fin n)) (ω : Fin n → Seed n f p)

lemma send_some (me : Fin n) (x : Bool × Seed n f p) (h : Hist n f p) (q : Fin n)
    (hl : h.length ≤ f) :
    send ss me x h q = some
      { sr := recTab me h h.length
        pref := if h.length = 0 then some x.1 else none
        share := if h.length = 0 then some (shareOf x.2 q) else none
        fwd := fun l =>
          if h.length = f ∧ l ≠ q then
            (if l = me then (if ss then some (shareOf x.2 me) else none)
             else (rcv h 0 l).bind Msg.share)
          else none } := by
  simp [send, hl]

/-- What `q` receives from `y` in round `t + 1 ≤ f + 1`. -/
lemma rcv_H {t m : ℕ} (ht : t < m) (_htf : t ≤ f) (q y : Fin n) :
    rcv (H ss c ω m q) t y =
      if y ≠ q ∧ c.Deliv y q t then send ss y (c.pref y, ω y) (H ss c ω t y) q else none := by
  rw [H, rcv_hist _ _ _ ht, msg_eq_deliv]
  simp only [Context.run_deliv]
  by_cases hd : y ≠ q ∧ c.Deliv y q t
  · rw [ite_eq_left hd, ite_eq_left hd]; rfl
  · rw [ite_eq_right hd, ite_eq_right hd]

/-- `σ_cons` computes the records `ghost`. -/
lemma recTab_H (t : ℕ) (ht : t ≤ f + 1) (m : ℕ) (hm : t ≤ m) (q : Fin n) :
    recTab q (H ss c ω m q) t = ghost c t q := by
  induction t generalizing m q with
  | zero => rfl
  | succ t ih =>
    funext l
    simp only [recTab, ghost]
    by_cases hlq : l = q
    · simp [hlq]
    rw [ite_eq_right hlq, ite_eq_right hlq, ih (by omega) m (by omega) q]
    have h1 : (if rcv (H ss c ω m q) t l = none then ((t + 1 : ℕ) : ℕ∞) else ⊤) =
        (if c.Deliv l q t then ⊤ else ((t + 1 : ℕ) : ℕ∞)) := by
      rw [rcv_H c ω (by omega) (by omega)]
      by_cases hd : c.Deliv l q t
      · rw [ite_eq_left (show l ≠ q ∧ c.Deliv l q t from ⟨hlq, hd⟩), ite_eq_left hd,
          send_some _ _ _ _ (by simp; omega)]
        simp
      · rw [ite_eq_right (show ¬ (l ≠ q ∧ c.Deliv l q t) from fun h => hd h.2), ite_eq_right hd]
        simp
    have h2 : (Finset.univ.inf fun y => ((rcv (H ss c ω m q) t y).map fun m => m.sr l).getD ⊤) =
        Finset.univ.inf fun y => if y ≠ q ∧ c.Deliv y q t then ghost c t y l else ⊤ := by
      refine Finset.inf_congr rfl fun y _ => ?_
      rw [rcv_H c ω (by omega) (by omega)]
      by_cases hd : y ≠ q ∧ c.Deliv y q t
      · rw [ite_eq_left hd, ite_eq_left hd, send_some _ _ _ _ (by simp; omega)]
        simp only [Option.map_some, Option.getD_some, length_hist]
        rw [ih (by omega) t le_rfl y]
      · rw [ite_eq_right hd, ite_eq_right hd]; simp
    rw [h1, h2]; convert rfl


/-- `q`'s round-1 message from `l ≠ q` carries `l`'s preference and `q`'s shares. -/
lemma rcv_H_zero {m : ℕ} (hm : 1 ≤ m) {q l : Fin n} (hlq : l ≠ q) (hd : c.Deliv l q 0) :
    (rcv (H ss c ω m q) 0 l).bind Msg.pref = some (c.pref l) ∧
      (rcv (H ss c ω m q) 0 l).bind Msg.share = some (shareOf (ω l) q) := by
  rw [rcv_H c ω (by omega) (Nat.zero_le _), ite_eq_left (show l ≠ q ∧ c.Deliv l q 0 from ⟨hlq, hd⟩),
    send_some _ _ _ _ (by simp)]
  simp

/-- The shares of `l`'s polynomials forwarded to `q` by `y` in round `f + 1`. -/
lemma fwdFrom_H {q l y : Fin n} {s : Fin (f + 1) → ZMod p}
    (h : fwdFrom q (H ss c ω (f + 1) q) l y = some s) : y ≠ q ∧ s = shareOf (ω l) y := by
  unfold fwdFrom at h
  by_cases hyq : y = q
  · simp [hyq] at h
  rw [ite_eq_right hyq, rcv_H c ω (by omega) le_rfl] at h
  by_cases hd : y ≠ q ∧ c.Deliv y q f
  · rw [ite_eq_left hd, send_some _ _ _ _ (by simp)] at h
    simp only [length_hist, true_and, Option.bind_some] at h
    refine ⟨hyq, ?_⟩
    by_cases hlq : l = q
    · simp [hlq] at h
    rw [ite_eq_left hlq] at h
    by_cases hly : l = y
    · subst hly
      cases ss <;> simp_all
    · rw [ite_eq_right hly] at h
      rcases Nat.eq_zero_or_pos f with hf | hf
      · subst hf; simp [rcv] at h
      · rw [rcv_H c ω hf (Nat.zero_le _)] at h
        by_cases hd' : l ≠ y ∧ c.Deliv l y 0
        · rw [ite_eq_left hd', send_some _ _ _ _ (by simp)] at h
          simp at h; exact h.symm
        · rw [ite_eq_right hd'] at h; simp at h
  · rw [ite_eq_right hd] at h; simp at h

/-- A forwarded share is available from `y`: either `y = l` (with `selfShare`, line 20), or `y`
received `l`'s round-1 message (`f ≥ 1`). -/
lemma fwdFrom_H_isSome {q l y : Fin n} (hyq : y ≠ q) (hlq : l ≠ q) (hd : c.Deliv y q f)
    (h : (l = y ∧ ss = true) ∨ (l ≠ y ∧ 1 ≤ f ∧ c.Deliv l y 0)) :
    (fwdFrom q (H ss c ω (f + 1) q) l y).isSome := by
  unfold fwdFrom
  rw [ite_eq_right hyq, rcv_H c ω (by omega) le_rfl, ite_eq_left (show y ≠ q ∧ c.Deliv y q f from ⟨hyq, hd⟩),
    send_some _ _ _ _ (by simp)]
  simp only [length_hist, true_and, Option.bind_some]
  rw [ite_eq_left hlq]
  rcases h with ⟨rfl, rfl⟩ | ⟨hly, hf, hd'⟩
  · simp
  · rw [ite_eq_right hly, rcv_H c ω hf (Nat.zero_le _), ite_eq_left (show l ≠ y ∧ c.Deliv l y 0 from ⟨hly, hd'⟩),
      send_some _ _ _ _ (by simp)]
    simp

end Run

/-- Interpolation recovers the secret from two shares. -/
lemma interp_shareOf [Fact p.Prime] (hp : n < p) (w : Seed n f p) (t : Fin (f + 1)) {a b : Fin n}
    (hab : a ≠ b) :
    interp (evalPt a) (shareOf w a t) (evalPt b) (shareOf w b t) = (((w t).1 : ℕ) : ZMod p) := by
  have hne : (evalPt a : ZMod p) - evalPt b ≠ 0 := by
    rw [sub_ne_zero, evalPt, evalPt, Ne, ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    intro h; exact hab (Fin.ext (by omega))
  unfold interp shareOf
  field_simp
  ring


end Podc.RationalConsensus.Cons

namespace Podc.RationalConsensus.Cons

open Cslib Cslib.SyncCrash Classical MeasureTheory

variable {n f p : ℕ} {ss : Bool} {c : Context (Fin n)} {ω : Fin n → Seed n f p}

/-- `σ_cons` decides exactly at time `f + 1`. -/
lemma decides_iff {q : Fin n} {o : Option Bool} :
    Decides (sigmaCons ss) c ω q o ↔
      (c.run ω).Alive q (f + 1) ∧ o = decideVal q (c.pref q, ω q) (H ss c ω (f + 1) q) := by
  unfold Decides
  rw [Cslib.Byzantine.LockStep.firstSome_iff_of_ne (f + 1)]
  · simp only [status, SyncCrash.state]
    by_cases ha : (c.run ω).Alive q (f + 1)
    · rw [ite_eq_left ha]
      simp only [Option.bind_some, sigmaCons, length_hist, ite_true, Option.some.injEq, ha,
        true_and]
      exact eq_comm
    · simp [ha]
  · intro t ht
    simp only [status, SyncCrash.state]
    split_ifs <;> simp [sigmaCons, ht]

/-- The set `NC` on which all nonfaulty agents agree. -/
lemma exists_agreed (hadm : c.Admissible f) (hfn : f < n) :
    ∃ S : Finset (Fin n), ∀ q, ¬ c.Faulty q →
      ∃ m, 1 ≤ m ∧ firstClean f (ghost c (f + 1) q) = some m ∧ NC (ghost c (f + 1) q) m = S := by
  obtain ⟨q₀, hq₀⟩ : ∃ q, ¬ c.Faulty q := by
    by_contra h
    push Not at h
    have : c.faulty = Finset.univ := by ext q; simp [Context.faulty, h q]
    have := hadm.1; rw [‹c.faulty = _›, Finset.card_univ, Fintype.card_fin] at this; omega
  have key : ∀ q, ∃ m, firstClean f (ghost c (f + 1) q) = some m :=
    fun q => Option.isSome_iff_exists.1 (firstClean_isSome hadm q)
  obtain ⟨m₀, hm₀⟩ := key q₀
  refine ⟨NC (ghost c (f + 1) q₀) m₀, fun q hq => ?_⟩
  obtain ⟨m, hm⟩ := key q
  refine ⟨m, ?_, hm, ?_⟩
  · unfold firstClean at hm
    obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 hm
    omega
  · have := ghost_agree hadm hq hq₀
    rw [hm, hm₀] at this
    simpa using this


/-- When a second share of every polynomial reaches every nonfaulty agent: with
`selfShare` (line 20 as written) as soon as `f + 1 < n`; for the received-only reading if `f ≥ 1`
and `f + 3 ≤ n`. -/
def ShareCond (ss : Bool) (n f : ℕ) : Prop := (ss = true ∧ f + 1 < n) ∨ (1 ≤ f ∧ f + 3 ≤ n)

lemma ShareCond.lt (h : ShareCond ss n f) : f + 1 < n := by
  rcases h with h | h <;> omega

lemma card_nonfaulty (hadm : c.Admissible f) :
    n - f ≤ (Finset.univ.filter fun q => ¬ c.Faulty q).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun q => c.Faulty q)
  have h2 : (Finset.univ.filter fun q => c.Faulty q) = c.faulty := rfl
  rw [h2, Finset.card_univ, Fintype.card_fin] at h
  have := hadm.1
  omega

lemma exists_nonfaulty_notMem (hadm : c.Admissible f) (A : Finset (Fin n))
    (hA : A.card + f < n) : ∃ y, ¬ c.Faulty y ∧ y ∉ A := by
  by_contra h
  push Not at h
  have : (Finset.univ.filter fun q => ¬ c.Faulty q) ⊆ A := fun y hy => h y (by simpa using hy)
  have := Finset.card_le_card this
  have := card_nonfaulty hadm
  omega

section Agreed

variable {S : Finset (Fin n)}
  (hS : ∀ q, ¬ c.Faulty q →
    ∃ m, 1 ≤ m ∧ firstClean f (ghost c (f + 1) q) = some m ∧ NC (ghost c (f + 1) q) m = S)
include hS

lemma mem_agreed_of_not_faulty {l q : Fin n} (hq : ¬ c.Faulty q) (hl : ¬ c.Faulty l) : l ∈ S := by
  obtain ⟨m, -, -, hNC⟩ := hS q hq
  rw [← hNC, mem_NC, ghost_eq_top_of_not_faulty hl]
  exact ENat.natCast_lt_top _

lemma deliv_of_mem_agreed {l q : Fin n} (hq : ¬ c.Faulty q) (hl : l ∈ S) (hlq : l ≠ q) :
    c.Deliv l q 0 := by
  by_contra hd
  obtain ⟨m, hm, -, hNC⟩ := hS q hq
  rw [← hNC, mem_NC] at hl
  have h1 := ghost_le_one_of_not_deliv (c := c) hlq hd (t := f + 1) (by omega)
  have : ((m : ℕ) : ℕ∞) < 1 := lt_of_lt_of_le hl h1
  norm_cast at this
  omega

lemma card_agreed (hadm : c.Admissible f) (hq : ¬ c.Faulty q) : n - f ≤ S.card := by
  refine (card_nonfaulty hadm).trans (Finset.card_le_card fun l hl => ?_)
  exact mem_agreed_of_not_faulty hS hq (by simpa using hl)

/-- A nonfaulty agent reconstructs the secrets of all agents of `S`. -/
lemma secret_H [Fact p.Prime] (hp : n < p) (hadm : c.Admissible f) (hsc : ShareCond ss n f)
    {q l : Fin n} (hq : ¬ c.Faulty q) (hl : l ∈ S) (t : Fin (f + 1)) :
    secret q (ω q) (H ss c ω (f + 1) q) t l = some ((ω l t).1 : ℕ) := by
  by_cases hlq : l = q
  · simp [secret, hlq]
  unfold secret
  rw [ite_eq_right hlq]
  -- some agent forwards a share of `l`'s polynomials
  have hY : (Finset.univ.filter fun y => (fwdFrom q (H ss c ω (f + 1) q) l y).isSome).Nonempty := by
    have hfaulty : c.Faulty l → 1 ≤ f := by
      intro hlf
      have : 0 < c.faulty.card := Finset.card_pos.2 ⟨l, by simpa [Context.faulty] using hlf⟩
      have := hadm.1; omega
    by_cases hss : ss = true ∧ ¬ c.Faulty l
    · refine ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      exact fwdFrom_H_isSome c ω hlq hlq ((Context.run_deliv c ω _ _ _).1
        (Run.deliv_of_not_faulty (show ¬ (c.run ω).Faulty l from hss.2) _ _))
        (Or.inl ⟨rfl, hss.1⟩)
    · have hf1 : 1 ≤ f := by
        rcases hsc with h | h
        · by_cases hlf : c.Faulty l
          · exact hfaulty hlf
          · exact absurd ⟨h.1, hlf⟩ hss
        · exact h.1
      have hex : ∃ y, ¬ c.Faulty y ∧ y ≠ q ∧ y ≠ l := by
        rcases hsc with h | h
        · have hlf : c.Faulty l := by
            by_contra hlf; exact hss ⟨h.1, hlf⟩
          obtain ⟨y, hy, hyq⟩ := exists_nonfaulty_notMem hadm {q} (by simp; omega)
          exact ⟨y, hy, by simpa using hyq, fun h => hy (h ▸ hlf)⟩
        · obtain ⟨y, hy, hyA⟩ := exists_nonfaulty_notMem hadm {q, l}
            (by have := Finset.card_le_two (a := q) (b := l); omega)
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyA
          exact ⟨y, hy, hyA⟩
      obtain ⟨y, hy, hyq, hyl⟩ := hex
      refine ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      exact fwdFrom_H_isSome c ω hyq hlq ((Context.run_deliv c ω _ _ _).1
        (Run.deliv_of_not_faulty (show ¬ (c.run ω).Faulty y from hy) _ _))
        (Or.inr ⟨Ne.symm hyl, hf1, deliv_of_mem_agreed hS hy hl (Ne.symm hyl)⟩)
  rw [dite_eq_left hY]
  have hy := Finset.min'_mem _ hY
  rw [Finset.mem_filter] at hy
  obtain ⟨s₂, hs₂⟩ := Option.isSome_iff_exists.1 hy.2
  obtain ⟨hyq, rfl⟩ := fwdFrom_H c ω hs₂
  rw [(rcv_H_zero c ω (by omega) hlq (deliv_of_mem_agreed hS hq hl hlq)).2, hs₂]
  dsimp only
  rw [interp_shareOf hp _ _ (Ne.symm hyq), ZMod.val_natCast_of_lt]
  have := (ω l t).1.2
  omega

lemma prefOf_H {q l : Fin n} (hq : ¬ c.Faulty q) (hl : l ∈ S) :
    prefOf q (c.pref q) (H ss c ω (f + 1) q) l = some (c.pref l) := by
  by_cases hlq : l = q
  · simp [prefOf, hlq]
  rw [prefOf, ite_eq_right hlq, (rcv_H_zero c ω (by omega) hlq (deliv_of_mem_agreed hS hq hl hlq)).1]

/-- **The decision of a nonfaulty agent**: the preference of the random dictator, the agent with
the `(S + 1)`-st highest identifier in the agreed set, `S = Σ x_l[t] mod |NC|`. -/
lemma decideVal_H [Fact p.Prime] (hp : n < p) (hadm : c.Admissible f) (hsc : ShareCond ss n f)
    {q : Fin n} (hq : ¬ c.Faulty q) (ht : n - S.card < f + 1) :
    decideVal q (c.pref q, ω q) (H ss c ω (f + 1) q) =
      ((S.sort (· ≤ ·)).reverse[(∑ l ∈ S, ((ω l ⟨n - S.card, ht⟩).1 : ℕ)) %
        (n - (n - S.card))]?).map c.pref := by
  obtain ⟨m, -, hfc, hNC⟩ := hS q hq
  have hR : recTab q (H ss c ω (f + 1) q) (f + 1) = ghost c (f + 1) q :=
    recTab_H c ω (f + 1) le_rfl (f + 1) le_rfl q
  unfold decideVal
  simp only [hR, hfc, hNC]
  rw [dite_eq_left (by omega)]
  rw [ite_eq_left (fun l hl => ⟨by rw [prefOf_H hS hq hl]; rfl,
    by rw [secret_H hS hp hadm hsc hq hl]; rfl⟩)]
  rw [Finset.sum_congr rfl fun l hl => by rw [secret_H hS hp hadm hsc hq hl]]
  simp only [Option.getD_some]
  have key : ∀ o : Option (Fin n), (∀ l, o = some l → l ∈ S) →
      o.bind (prefOf q (c.pref q) (H ss c ω (f + 1) q)) = o.map c.pref := by
    rintro (_ | l) h
    · rfl
    · simp [prefOf_H hS hq (h l rfl)]
  refine key _ fun l hl => ?_
  have := List.mem_of_getElem? hl
  simpa using this

end Agreed


/-- The decision of an agent nonfaulty in an admissible context is the preference of some
agent. -/
lemma decideVal_valid [Fact p.Prime] (hp : n < p) (hadm : c.Admissible f)
    (hsc : ShareCond ss n f) {q : Fin n} (hq : ¬ c.Faulty q) :
    ∃ l, decideVal q (c.pref q, ω q) (H ss c ω (f + 1) q) = some (c.pref l) := by
  obtain ⟨S, hS⟩ := exists_agreed hadm (by have := hsc.lt; omega)
  have hcard := card_agreed hS hadm hq
  have hqS := mem_agreed_of_not_faulty hS hq hq
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  rw [decideVal_H hS hp hadm hsc hq (by omega)]
  set L := (S.sort (· ≤ ·)).reverse
  have hlen : L.length = S.card := by simp [L]
  have hnS : n - (n - S.card) = S.card := by omega
  have hk : (∑ l ∈ S, ((ω l ⟨n - S.card, by omega⟩).1 : ℕ)) % (n - (n - S.card)) < L.length := by
    rw [hlen]
    exact lt_of_lt_of_eq (Nat.mod_lt _ (by have := Finset.card_pos.2 ⟨q, hqS⟩; omega)) hnS
  exact ⟨L[_]'hk, by rw [List.getElem?_eq_getElem hk]; rfl⟩

/-- An agent that is alive at time `f + 1` but crashes later behaves as a nonfaulty one: its
decision is the preference of some agent. -/
lemma decideVal_valid_of_alive [Fact p.Prime] (hp : n < p) (hadm : c.Admissible f)
    (hsc : ShareCond ss n f) {q : Fin n} (ha : (c.run ω).Alive q (f + 1)) :
    ∃ l, decideVal q (c.pref q, ω q) (H ss c ω (f + 1) q) = some (c.pref l) := by
  let c' : Context (Fin n) := { c with crash := Function.update c.crash q none }
  have hadm' : c'.Admissible f := by
    refine ⟨le_trans (Finset.card_le_card fun x hx => ?_) hadm.1, fun x m hm => ?_⟩
    · simp only [Context.faulty, Context.Faulty, Finset.mem_filter, Finset.mem_univ, true_and,
        c'] at hx ⊢
      by_cases hxq : x = q
      · subst hxq; simp at hx
      · rwa [Function.update_of_ne hxq] at hx
    · by_cases hxq : x = q
      · subst hxq; simp [c'] at hm
      · exact hadm.2 x m (by simpa [c', Function.update_of_ne hxq] using hm)
  have hq' : ¬ c'.Faulty q := by simp [Context.Faulty, c']
  have hH : H ss c ω (f + 1) q = H ss c' ω (f + 1) q := by
    unfold H
    refine hist_congr (r := c.run ω) (r' := c'.run ω) (fun _ => rfl) (fun t ht x y => ?_)
      (f + 1) le_rfl q
    by_cases hxq : x = q
    · subst hxq
      simp only [Run.Deliv, Run.Alive, Context.run_crash, c', Function.update_self,
        reduceCtorEq, false_imp_iff, implies_true, false_and, not_false_eq_true, and_true,
        iff_true]
      refine ⟨fun m hm => by have := ha m hm; omega, fun h => ?_⟩
      have := ha _ h.1; omega
    · simp [Run.Deliv, Run.Alive, c', Function.update_of_ne hxq]
  rw [hH]
  exact decideVal_valid (c := c') hp hadm' hsc hq'

/-- **Theorem 2** (with `selfShare`, or for the received-only reading under
`ShareCond`): if at most `f` agents crash, `f + 1 < n`, and nobody deviates, `σ_cons` solves fair
consensus. -/
theorem theorem_2_of_shareCond [Fact p.Prime] [Fact (f < n)] (hp : n < p)
    (hsc : ShareCond ss n f) : SolvesFairConsensus (seedMeasure n f p) (sigmaCons ss) f := by
  -- the decision of nonfaulty agents
  have hdec : ∀ c : Context (Fin n), c.Admissible f → ∃ S : Finset (Fin n),
      ∃ ht : n - S.card < f + 1, S.card = n - (n - S.card) ∧ S.Nonempty ∧
      (∀ q, ¬ c.Faulty q → q ∈ S) ∧ ∀ (ω : Fin n → Seed n f p) q, ¬ c.Faulty q →
        decideVal q (c.pref q, ω q) (H ss c ω (f + 1) q) =
          ((S.sort (· ≤ ·)).reverse[(∑ l ∈ S, ((ω l ⟨n - S.card, ht⟩).1 : ℕ)) %
            (n - (n - S.card))]?).map c.pref := by
    intro c hadm
    obtain ⟨S, hS⟩ := exists_agreed hadm (by have := hsc.lt; omega)
    obtain ⟨q₀, hq₀, -⟩ := exists_nonfaulty_notMem hadm ∅ (by simp; have := hsc.lt; omega)
    have hcard := card_agreed hS hadm hq₀
    have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
    exact ⟨S, by omega, by omega, ⟨q₀, mem_agreed_of_not_faulty hS hq₀ hq₀⟩,
      fun q hq => mem_agreed_of_not_faulty hS hq₀ hq,
      fun ω q hq => decideVal_H hS hp hadm hsc hq _⟩
  have hnf : ∀ c : Context (Fin n), c.Admissible f → ∃ q, ¬ c.Faulty q := fun c hadm => by
    obtain ⟨q, hq, -⟩ := exists_nonfaulty_notMem hadm ∅ (by simp; have := hsc.lt; omega)
    exact ⟨q, hq⟩
  refine ⟨fun c hadm => Filter.Eventually.of_forall fun ω => ⟨?_, ?_, ?_⟩, fun c hadm b => ?_⟩
  · intro q₁ q₂ h₁ h₂ o o' ho ho'
    obtain ⟨S, ht, -, -, -, hD⟩ := hdec c hadm
    rw [decides_iff] at ho ho'
    rw [ho.2, ho'.2, hD ω q₁ h₁, hD ω q₂ h₂]
  · intro q hq
    exact ⟨_, decides_iff.2 ⟨Run.alive_of_not_faulty (show ¬ (c.run ω).Faulty q from hq) _, rfl⟩⟩
  · intro q o ho
    rw [decides_iff] at ho
    obtain ⟨l, hl⟩ := decideVal_valid_of_alive hp hadm hsc ho.1
    exact ⟨_, ho.2.trans hl, l, rfl⟩
  · obtain ⟨S, ht, hSc, hne, hNF, hD⟩ := hdec c hadm
    obtain ⟨q₀, hq₀⟩ := hnf c hadm
    have hev : {ω : Fin n → Seed n f p | outcome (sigmaCons ss) c ω = .cons b} =
        {ω : Fin n → Seed n f p | ((S.sort (· ≤ ·)).reverse[(∑ l ∈ S, ((ω l ⟨n - S.card, ht⟩).1 : ℕ)) %
          (n - (n - S.card))]?).map c.pref = some b} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [outcome_eq_cons_iff hq₀]
      constructor
      · intro h
        have := h q₀ hq₀
        rw [decides_iff, hD ω q₀ hq₀] at this
        exact this.2.symm
      · intro h q hq
        rw [decides_iff, hD ω q hq]
        exact ⟨Run.alive_of_not_faulty (show ¬ (c.run ω).Faulty q from hq) _, h.symm⟩
    rw [hev]
    have := seedMeasure_dictator (f := f) (p := p) S ⟨n - S.card, ht⟩ hSc hne c.pref b
    simp only at this
    rw [this, Fintype.card_fin]
    refine ENNReal.div_le_div ?_ (by exact_mod_cast (by simpa using Finset.card_le_univ S))
    exact_mod_cast Finset.card_le_card fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact ⟨hNF l hl.1, hl.2⟩

/-- **Theorem 2** of [Halpern–Vilaça]. With `selfShare` (Algorithm 1, line 20: in round `f + 1`
agent `i` sends `(y_li)_{l ≠ j}`, which includes its own share `y_ii = q_i(i)`), `σ_cons` solves
fair consensus whenever `f + 1 < n`, as claimed. -/
theorem theorem_2 [Fact p.Prime] [Fact (f < n)] (hp : n < p) (hfn : f + 1 < n) :
    SolvesFairConsensus (seedMeasure n f p) (sigmaCons true) f :=
  theorem_2_of_shareCond hp (Or.inl ⟨rfl, hfn⟩)

/-- **Theorem 2 for the received-only reading** (agents forward only shares received from
others, as the prose says) holds when `f ≥ 1` and `f + 3 ≤ n` (at least three
nonfaulty agents). -/
theorem theorem_2_receivedOnly [Fact p.Prime] [Fact (f < n)] (hp : n < p) (hf : 1 ≤ f)
    (hfn : f + 3 ≤ n) : SolvesFairConsensus (seedMeasure n f p) (sigmaCons false) f :=
  theorem_2_of_shareCond hp (Or.inr ⟨hf, hfn⟩)


/-! ### The received-only reading fails for `n = f + 2` and for `f = 0` -/

/-- The context of the counterexample: agents `0` and `1` are nonfaulty; if `f ≠ 0`, all other
agents crash at the very beginning (round 1, reaching nobody). -/
def badCtx (n f : ℕ) : Context (Fin n) where
  pref _ := true
  crash y := if 2 ≤ (y : ℕ) ∧ f ≠ 0 then some 1 else none
  reach _ := ∅

lemma badCtx_admissible (h2 : 2 ≤ n) (hcase : n = f + 2 ∨ f = 0) : (badCtx n f).Admissible f := by
  refine ⟨?_, fun y m hm => ?_⟩
  · by_cases hf : f = 0
    · have : (badCtx n f).faulty = ∅ := by
        ext y; simp [Context.faulty, Context.Faulty, badCtx, hf]
      simp [this]
    · have hsub : (badCtx n f).faulty ⊆ Finset.univ \ {⟨0, by omega⟩, ⟨1, by omega⟩} := by
        intro y hy
        have hy' : (badCtx n f).Faulty y := by simpa [Context.faulty] using hy
        simp only [Context.Faulty, badCtx] at hy'
        have h2y : 2 ≤ (y : ℕ) := by
          by_contra hc; exact hy' (ite_eq_right (fun h => hc h.1))
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and, not_or, Fin.ext_iff]
        omega
      have := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        Finset.card_pair (by simp [Fin.ext_iff])] at this
      omega
  · simp only [badCtx] at hm
    split_ifs at hm
    simp at hm; omega

/-- **Theorem 2 fails for the received-only reading when `n = f + 2` or `f = 0`.** In `badCtx`, agent `0`
never receives a second share of agent `1`'s polynomials (agent `1` does not forward its own share,
and nobody else forwards anything in round `f + 1`), so it cannot interpolate `x_1[t]` and decides
`⊥` — violating validity (and fairness) with probability `1`. -/
theorem theorem_2_receivedOnly_false [Fact p.Prime] [Fact (f < n)] (h2 : 2 ≤ n)
    (hcase : n = f + 2 ∨ f = 0) :
    ¬ SolvesFairConsensus (seedMeasure n f p) (sigmaCons false) f := by
  intro h
  set c := badCtx n f
  have hadm := badCtx_admissible h2 hcase
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hba : b ≠ a := by simp [a, b, Fin.ext_iff]
  have hnf : ∀ y : Fin n, (y : ℕ) < 2 → ¬ c.Faulty y := by
    intro y hy; simp [c, Context.Faulty, badCtx]; omega
  have ha : ¬ c.Faulty a := hnf a (by simp [a])
  have hb : ¬ c.Faulty b := hnf b (by simp [b])
  have : IsProbabilityMeasure (seedMeasure n f p) := by unfold seedMeasure; infer_instance
  have : (ae (seedMeasure n f p)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨ω, hω⟩ := (h.consensus c hadm).exists
  -- nobody forwards a share of `b`'s polynomials to `a`
  have hfwd : ∀ y, fwdFrom a (H false c ω (f + 1) a) b y = none := by
    intro y
    unfold fwdFrom
    split_ifs with hya
    · rfl
    rw [rcv_H c ω (by omega) le_rfl]
    split_ifs with hd
    · rw [send_some _ _ _ _ (by simp)]
      simp only [length_hist, true_and, Option.bind_some, ne_eq, hba, not_false_eq_true,
        ite_true]
      by_cases hyb : b = y
      · simp [hyb]
      · rw [ite_eq_right hyb]
        rcases Nat.eq_zero_or_pos f with hf | hf
        · subst hf; simp [rcv]
        · exfalso
          have hy2 : 2 ≤ (y : ℕ) := by
            have : (y : ℕ) ≠ 0 := fun h => hya (Fin.ext h)
            have : (y : ℕ) ≠ 1 := fun h => hyb (Fin.ext h.symm)
            omega
          have := hd.2.1 1 (by simp [c, badCtx, hy2, hf.ne'])
          omega
    · rfl
  have hsec : ∀ t, secret a (ω a) (H false c ω (f + 1) a) t b = none := by
    intro t
    unfold secret
    rw [ite_eq_right hba, dite_eq_right]
    rintro ⟨y, hy⟩
    simp [hfwd y] at hy
  have hdec : decideVal a (c.pref a, ω a) (H false c ω (f + 1) a) = none := by
    have hR : recTab a (H false c ω (f + 1) a) (f + 1) = ghost c (f + 1) a :=
      recTab_H c ω (f + 1) le_rfl (f + 1) le_rfl a
    unfold decideVal
    simp only [hR]
    split
    · rfl
    · rename_i m _
      split_ifs with ht hall
      · exfalso
        have hbS : b ∈ NC (ghost c (f + 1) a) m := by
          rw [mem_NC, ghost_eq_top_of_not_faulty hb]; exact ENat.natCast_lt_top _
        have := (hall b hbS).2
        rw [hsec] at this
        simp at this
      · rfl
      · rfl
  have hdecides : Decides (sigmaCons false) c ω a none :=
    decides_iff.2 ⟨Run.alive_of_not_faulty (show ¬ (c.run ω).Faulty a from ha) _, hdec.symm⟩
  obtain ⟨_, h1, -⟩ := hω.validity a none hdecides
  cases h1

end Podc.RationalConsensus.Cons
