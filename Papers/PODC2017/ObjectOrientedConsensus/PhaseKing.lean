import Mathlib
import Cslib.Computability.Distributed.Byzantine.KingPhase
import Papers.PODC2017.ObjectOrientedConsensus.Template

/-!
# Phase-King as adopt-commit + conciliator (Section 4.1 of [AACV])

Synchronous message passing, `n = Fintype.card P` processes, the processes outside `H` are Byzantine,
`#Hᶜ ≤ t` and `3t < n`. Values are `Fin 3`: inputs are `0, 1`, and `2` is the "no value" mark of the
Phase-King algorithm.

* Algorithm 3 (adopt-commit). One instance is determined by the honest inputs `x` and the messages the
  Byzantine processes send (`b1 p q`, `b2 p q`: what `p` receives from `q ∉ H` in exchange 1/2); honest
  messages are computed. `acOut … p` is the output of `p`.
  - Lemma 2 (coherence, convergence): `lemma2_coherence`, `lemma2_convergence`.
  - Lemma 2 (validity) is **false**: fault-free, inputs `0, 0, 1, 1`, everybody returns `(adopt, 2)`
    (`lemma2_validity_false`). The returned value is an input or `2` (`lemma2_validity_bot`), and returning
    the own input instead of `2` gives a correct adopt-commit object (`lemma2_fixed`).
* The composed protocol (Algorithm 2 with Algorithms 3 and 4, all processes keep participating, the king
  of round `m` is `king m`): `val`, `out`.
  - Lemma 3 (eventual agreement at an honest king): `lemma3_honest_king`; persistence: `persistence`.
  - Lemma 3 (validity) is **false** for a Byzantine king, and Algorithm 2's rule "decide on commit"
    then **violates agreement**: `template_disagreement` (`n = 4`, `t = 1`).
  - Repair (Phase-King's own rule): decide on a commit only in rounds `≥ t` (0-based), i.e. after
    `t + 1` distinct kings: `repaired_agreement`, `repaired_validity`, `repaired_termination`.
-/

namespace Podc.ObjectOrientedConsensus.PhaseKing

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `cnt r k`: the number of processes from which the received messages `r` contain `k`. -/
def cnt (r : P → Option (Fin 3)) (k : Fin 3) : ℕ := #{q | r q = some k}

/-- Exchange 1 of Algorithm 3: `v ← 2`; for `k = 0, 1`: if `C(k) ≥ n − t` then `v ← k`. -/
def ex1 (t : ℕ) (r : P → Option (Fin 3)) : Fin 3 :=
  if Fintype.card P - t ≤ cnt r 1 then 1 else if Fintype.card P - t ≤ cnt r 0 then 0 else 2

/-- Exchange 2 of Algorithm 3: for `k = 2 downto 0`: if `D(k) > t` then `v ← k` (so `v` becomes the
smallest `k` with `D(k) > t`, if any). -/
def ex2 (t : ℕ) (v : Fin 3) (r : P → Option (Fin 3)) : Fin 3 :=
  if t < cnt r 0 then 0 else if t < cnt r 1 then 1 else if t < cnt r 2 then 2 else v

/-- Return statement of Algorithm 3. -/
def acRet (t : ℕ) (v : Fin 3) (r : P → Option (Fin 3)) : Conf × Fin 3 :=
  if ex2 t v r ≠ 2 ∧ Fintype.card P - t ≤ cnt r (ex2 t v r) then (.commit, ex2 t v r)
  else (.adopt, ex2 t v r)

variable (t : ℕ) (H : Finset P)

/-- Messages received by `p` in exchange 1: honest `q` sends its input `x q`. -/
def recv1 (b1 : P → P → Option (Fin 3)) (x : P → Fin 3) (p : P) : P → Option (Fin 3) :=
  fun q => if q ∈ H then some (x q) else b1 p q

/-- The value of `p` after exchange 1. -/
def v1 (b1 : P → P → Option (Fin 3)) (x : P → Fin 3) (p : P) : Fin 3 := ex1 t (recv1 H b1 x p)

/-- Messages received by `p` in exchange 2: honest `q` sends `v1 q`. -/
def recv2 (b1 b2 : P → P → Option (Fin 3)) (x : P → Fin 3) (p : P) : P → Option (Fin 3) :=
  fun q => if q ∈ H then some (v1 t H b1 x q) else b2 p q

/-- **Algorithm 3** (Phase-King's adopt-commit): the output of `p`. -/
def acOut (b1 b2 : P → P → Option (Fin 3)) (x : P → Fin 3) (p : P) : Conf × Fin 3 :=
  acRet t (v1 t H b1 x p) (recv2 t H b1 b2 x p)

variable {t H}

/-! ### Counting -/

lemma card_compl_add : #H + #Hᶜ = Fintype.card P := by
  rw [card_compl]; have := H.card_le_univ; omega

/-- If every honest `q` delivers `y q`, the count of `k` is between the honest count and the honest
count plus `#Hᶜ`. -/
lemma cnt_bounds {r : P → Option (Fin 3)} {y : P → Fin 3} (hr : ∀ q ∈ H, r q = some (y q)) (k : Fin 3) :
    #{q ∈ H | y q = k} ≤ cnt r k ∧ cnt r k ≤ #{q ∈ H | y q = k} + #Hᶜ := by
  have hH : ({q ∈ H | y q = k} : Finset P) = {q ∈ H | r q = some k} := by
    ext q; simp only [mem_filter]
    constructor
    · rintro ⟨hq, rfl⟩; exact ⟨hq, hr q hq⟩
    · rintro ⟨hq, h⟩; rw [hr q hq] at h; exact ⟨hq, Option.some_injective _ h⟩
  constructor
  · rw [hH, cnt]; exact card_le_card fun q => by simp +contextual
  · rw [hH, cnt]
    calc #{q | r q = some k} ≤ #({q ∈ H | r q = some k} ∪ Hᶜ) :=
          card_le_card fun q => by by_cases hq : q ∈ H <;> simp_all
      _ ≤ _ := card_union_le _ _

lemma ex1_ne_two {r : P → Option (Fin 3)} (h : ex1 t r ≠ 2) : Fintype.card P - t ≤ cnt r (ex1 t r) := by
  unfold ex1 at *
  split_ifs at * with h1 h0 <;> simp_all

/-- Two distinct values cannot both reach `n − t` among the honest-plus-Byzantine counts. -/
lemma eq_of_two_quorums (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {y : P → Fin 3} {a b : Fin 3}
    (ha : Fintype.card P - t ≤ #{q ∈ H | y q = a} + #Hᶜ)
    (hb : Fintype.card P - t ≤ #{q ∈ H | y q = b} + #Hᶜ) : a = b := by
  by_contra hab
  have hdisj : Disjoint ({q ∈ H | y q = a} : Finset P) {q ∈ H | y q = b} := by
    rw [disjoint_filter]; intro q _ h1 h2; exact hab (h1 ▸ h2)
  have := card_union_of_disjoint hdisj
  have hsub : ({q ∈ H | y q = a} ∪ {q ∈ H | y q = b} : Finset P) ⊆ H := by
    intro q; simp only [mem_union, mem_filter]; tauto
  have := card_le_card hsub
  have := card_compl_add (H := H)
  omega

variable (b1 b2 : P → P → Option (Fin 3)) (x : P → Fin 3)

lemma recv1_honest : ∀ q ∈ H, recv1 H b1 x p q = some (x q) := fun q hq => by simp [recv1, hq]

lemma recv2_honest : ∀ q ∈ H, recv2 t H b1 b2 x p q = some (v1 t H b1 x q) := fun q hq => by
  simp [recv2, hq]

/-- After exchange 1, all non-`2` values (of any process) coincide. -/
lemma v1_agree (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {p p' : P}
    (hp : v1 t H b1 x p ≠ 2) (hp' : v1 t H b1 x p' ≠ 2) : v1 t H b1 x p = v1 t H b1 x p' := by
  have h1 := ex1_ne_two hp
  have h2 := ex1_ne_two hp'
  exact eq_of_two_quorums hB hn
    (h1.trans (cnt_bounds (recv1_honest b1 x) _).2) (h2.trans (cnt_bounds (recv1_honest b1 x) _).2)

/-- A non-`2` value after exchange 1 is an honest input. -/
lemma v1_valid (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {p : P} (hp : v1 t H b1 x p ≠ 2) :
    ∃ q ∈ H, x q = v1 t H b1 x p := by
  have h1 := (ex1_ne_two hp).trans (cnt_bounds (recv1_honest (H := H) (p := p) b1 x) (v1 t H b1 x p)).2
  have hpos : 0 < #{q ∈ H | x q = v1 t H b1 x p} := by omega
  obtain ⟨q, hq⟩ := card_pos.1 hpos
  simp only [mem_filter] at hq
  exact ⟨q, hq.1, hq.2⟩

/-- The returned value of an honest process is the exchange-1 value of an honest process. -/
lemma acOut_eq_v1 (hB : #Hᶜ ≤ t) {p : P} (hp : p ∈ H) :
    ∃ q ∈ H, v1 t H b1 x q = (acOut t H b1 b2 x p).2 := by
  have key : ∀ k, t < cnt (recv2 t H b1 b2 x p) k → ∃ q ∈ H, v1 t H b1 x q = k := by
    intro k hk
    have := (cnt_bounds (recv2_honest (t := t) (H := H) (p := p) b1 b2 x) k).2
    obtain ⟨q, hq⟩ := card_pos.1 (show 0 < #{q ∈ H | v1 t H b1 x q = k} by omega)
    simp only [mem_filter] at hq
    exact ⟨q, hq⟩
  have hret : (acOut t H b1 b2 x p).2 = ex2 t (v1 t H b1 x p) (recv2 t H b1 b2 x p) := by
    simp only [acOut, acRet]; split_ifs <;> rfl
  rw [hret]
  unfold ex2
  split_ifs with h0 h1 h2
  · exact key 0 h0
  · exact key 1 h1
  · exact key 2 h2
  · exact ⟨p, hp, rfl⟩

/-- **Lemma 2 of [AACV], validity (corrected form).** An honest process returns an honest input or the
mark `2`. -/
theorem lemma2_validity_bot (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {p : P} (hp : p ∈ H) :
    (acOut t H b1 b2 x p).2 = 2 ∨ ∃ q ∈ H, x q = (acOut t H b1 b2 x p).2 := by
  obtain ⟨q, hq, hqv⟩ := acOut_eq_v1 b1 b2 x hB hp
  by_cases h2 : v1 t H b1 x q = 2
  · left; rw [← hqv, h2]
  · right; rw [← hqv]; exact v1_valid b1 x hB hn h2

/-- **Lemma 2 of [AACV], coherence.** If an honest process commits, every honest process returns the
same value. -/
theorem lemma2_coherence (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {p : P} (hp : p ∈ H)
    (hc : (acOut t H b1 b2 x p).1 = .commit) {q : P} (hq : q ∈ H) :
    (acOut t H b1 b2 x q).2 = (acOut t H b1 b2 x p).2 := by
  set w := ex2 t (v1 t H b1 x p) (recv2 t H b1 b2 x p) with hw
  have hcw : (acOut t H b1 b2 x p) = (.commit, w) ∧ w ≠ 2 ∧
      Fintype.card P - t ≤ cnt (recv2 t H b1 b2 x p) w := by
    simp only [acOut, acRet] at hc ⊢
    split_ifs at hc ⊢ with h
    · exact ⟨rfl, h⟩
  obtain ⟨hpo, hw2, hwc⟩ := hcw
  rw [hpo]
  show _ = w
  -- many honest processes hold `w` after exchange 1
  have hHw := (cnt_bounds (recv2_honest (t := t) (H := H) (p := p) b1 b2 x) w).2
  have hpos : 0 < #{r ∈ H | v1 t H b1 x r = w} := by omega
  obtain ⟨r, hr⟩ := card_pos.1 hpos
  simp only [mem_filter] at hr
  -- all honest non-2 exchange-1 values are `w`
  have hother : ∀ k, k ≠ w → k ≠ 2 → cnt (recv2 t H b1 b2 x q) k ≤ t := by
    intro k hkw hk2
    have h := (cnt_bounds (recv2_honest (t := t) (H := H) (p := q) b1 b2 x) k).2
    have h0 : #{s ∈ H | v1 t H b1 x s = k} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro s _ hs
      apply hkw
      rw [← hs, ← hr.2]
      exact v1_agree b1 x hB hn (hs ▸ hk2) (hr.2 ▸ hw2)
    omega
  have hwq : t < cnt (recv2 t H b1 b2 x q) w := by
    have := (cnt_bounds (recv2_honest (t := t) (H := H) (p := q) b1 b2 x) w).1
    omega
  have hret : (acOut t H b1 b2 x q).2 = ex2 t (v1 t H b1 x q) (recv2 t H b1 b2 x q) := by
    simp only [acOut, acRet]; split_ifs <;> rfl
  rw [hret]
  have hw01 : w = 0 ∨ w = 1 := by omega
  rcases hw01 with h | h
  · simp only [ex2, h] at hwq ⊢; simp [hwq]
  · have h0 := hother 0 (by rw [h]; decide) (by decide)
    simp only [ex2, h] at hwq ⊢
    simp [hwq, not_lt.2 h0]

/-- **Lemma 2 of [AACV], convergence.** If all honest inputs are `v ∈ {0, 1}`, every honest process
returns `(commit, v)`. -/
theorem lemma2_convergence (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {v : Fin 3} (hv : v ≠ 2)
    (hx : ∀ q ∈ H, x q = v) (p : P) : acOut t H b1 b2 x p = (.commit, v) := by
  have hHc := card_compl_add (H := H)
  have hall : ∀ (y : P → Fin 3), (∀ q ∈ H, y q = v) → #{q ∈ H | y q = v} = #H := fun y hy => by
    rw [filter_true_of_mem hy]
  have hnone : ∀ (y : P → Fin 3), (∀ q ∈ H, y q = v) → ∀ k ≠ v, #{q ∈ H | y q = k} = 0 :=
    fun y hy k hk => by
      rw [card_eq_zero, filter_eq_empty_iff]; intro q hq h; exact hk (h ▸ hy q hq)
  have hv1 : ∀ p, v1 t H b1 x p = v := by
    intro p
    have hc := cnt_bounds (recv1_honest (H := H) (p := p) b1 x)
    have hcv := (hc v).1; rw [hall x hx] at hcv
    simp only [v1, ex1]
    have hv01 : v = 0 ∨ v = 1 := by omega
    rcases hv01 with rfl | rfl
    · have h1 := (hc 1).2; rw [hnone x hx 1 (by decide)] at h1
      rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_pos (by omega)]
  have hc := cnt_bounds (recv2_honest (t := t) (H := H) (p := p) b1 b2 x)
  have hv1' : ∀ q ∈ H, v1 t H b1 x q = v := fun q _ => hv1 q
  have hcv := (hc v).1; rw [hall _ hv1'] at hcv
  have hk : ∀ k ≠ v, cnt (recv2 t H b1 b2 x p) k ≤ t := fun k hkv => by
    have := (hc k).2; rw [hnone _ hv1' k hkv] at this; omega
  have hex : ex2 t (v1 t H b1 x p) (recv2 t H b1 b2 x p) = v := by
    have hv01 : v = 0 ∨ v = 1 := by omega
    rcases hv01 with rfl | rfl
    · simp only [ex2]; rw [if_pos (by omega)]
    · simp only [ex2]; rw [if_neg (not_lt.2 (hk 0 (by decide))), if_pos (by omega)]
  simp only [acOut, acRet, hex]
  rw [if_pos ⟨hv, by omega⟩]

/-- **Lemma 2 of [AACV], validity, is false.** Fault-free (`H = univ`), `n = 4`, `t = 1`, inputs
`0, 0, 1, 1`: every process returns `(adopt, 2)`, and `2` is not an input. -/
theorem lemma2_validity_false :
    let x : Fin 4 → Fin 3 := ![0, 0, 1, 1]
    (#(univ : Finset (Fin 4))ᶜ ≤ 1 ∧ 3 * 1 < Fintype.card (Fin 4)) ∧
    ∀ (b1 b2 : Fin 4 → Fin 4 → Option (Fin 3)) (p : Fin 4),
      acOut 1 univ b1 b2 x p = (.adopt, 2) ∧ ∀ q, x q ≠ 2 := by
  intro x
  refine ⟨by decide, fun b1 b2 p => ?_⟩
  have hr1 : ∀ p, recv1 univ b1 x p = fun q => some (x q) := fun p => by
    funext q; simp [recv1]
  have h1 : ∀ p, v1 1 univ b1 x p = 2 := by
    intro p; simp only [v1, hr1]; revert p; decide
  have hr2 : ∀ p, recv2 1 univ b1 b2 x p = fun _ => some 2 := fun p => by
    funext q; simp [recv2, h1]
  have h2 : ∀ p, acOut 1 univ b1 b2 x p = (.adopt, 2) := by
    intro p; simp only [acOut, hr2, h1]; revert p; decide
  exact ⟨h2 p, by decide⟩

/-- Algorithm 3 with the one-line fix "return `(adopt, own input)` instead of `(adopt, 2)`". -/
def acOutFix (b1 b2 : P → P → Option (Fin 3)) (x : P → Fin 3) (p : P) : Conf × Fin 3 :=
  if (acOut t H b1 b2 x p).2 = 2 then (.adopt, x p) else acOut t H b1 b2 x p

/-- **Lemma 2 of [AACV], repaired.** With binary honest inputs, the fixed Algorithm 3 is an
adopt-commit object on the honest processes (validity, coherence, convergence). -/
theorem lemma2_fixed (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) (hx : ∀ q ∈ H, x q ≠ 2) :
    IsAC (↑H : Set P) ↑H x (acOutFix (t := t) (H := H) b1 b2 x) where
  sub := subset_rfl
  noVac p _ := by
    simp only [acOutFix, acOut, acRet]; split_ifs <;> simp
  validity p hp := by
    simp only [acOutFix]
    split_ifs with h
    · exact ⟨p, hp, rfl⟩
    · rcases lemma2_validity_bot b1 b2 x hB hn hp with h' | ⟨q, hq, hqv⟩
      · exact absurd h' h
      · exact ⟨q, hq, hqv.symm⟩
  convergence v hv p hp := by
    by_cases hH : H.Nonempty
    · obtain ⟨q, hq⟩ := hH
      have hv2 : v ≠ 2 := hv q hq ▸ hx q hq
      have := lemma2_convergence b1 b2 x hB hn hv2 hv p
      simp [acOutFix, this, hv2]
    · exact absurd hp (by simp [not_nonempty_iff_eq_empty.1 hH])
  coherence p hp hc q hq := by
    have hpc : (acOut t H b1 b2 x p).1 = .commit ∧ (acOut t H b1 b2 x p).2 ≠ 2 := by
      simp only [acOutFix] at hc
      split_ifs at hc with h
      exact ⟨hc, h⟩
    have hcoh := lemma2_coherence b1 b2 x hB hn hp hpc.1 hq
    simp only [acOutFix, hcoh, if_neg hpc.2]

/-! ### The composed protocol: Algorithm 2 with Algorithms 3 and 4 -/

/-- The Byzantine processes' messages in all rounds: `b1 m p q`, `b2 m p q` (exchanges 1, 2 of
round `m`, from `q ∉ H` to `p`) and `bk m p` (what a Byzantine king of round `m` makes `p` adopt). -/
structure Adv (P : Type*) where
  /-- Exchange-1 messages of Byzantine processes. -/
  b1 : ℕ → P → P → Option (Fin 3)
  /-- Exchange-2 messages of Byzantine processes. -/
  b2 : ℕ → P → P → Option (Fin 3)
  /-- The king's message from a Byzantine king. -/
  bk : ℕ → P → Fin 3

variable (t H) (king : ℕ → P) (adv : Adv P) (inp : P → Fin 3)

/-- **Algorithm 4** (Phase-King's conciliator): the value `p` receives from the king of round `m`. An
honest king broadcasts `min 1 σ` of its adopt-commit output `σ`; a Byzantine king sends anything. -/
def kingMsg (m : ℕ) (y : P → Fin 3) (p : P) : Fin 3 :=
  if king m ∈ H then min 1 (acOut t H (adv.b1 m) (adv.b2 m) y (king m)).2 else adv.bk m p

/-- One round of Algorithm 2: on commit keep the committed value, on adopt take the conciliator's. -/
def step (m : ℕ) (y : P → Fin 3) (p : P) : Fin 3 :=
  if (acOut t H (adv.b1 m) (adv.b2 m) y p).1 = .commit then (acOut t H (adv.b1 m) (adv.b2 m) y p).2
  else kingMsg t H king adv m y p

/-- The values entering round `m` (only those of honest processes matter). -/
def val : ℕ → P → Fin 3
  | 0 => inp
  | m + 1 => step t H king adv m (val m)

/-- The adopt-commit outputs of round `m`. -/
def out (m : ℕ) (p : P) : Conf × Fin 3 := acOut t H (adv.b1 m) (adv.b2 m) (val t H king adv inp m) p

variable {t H king adv inp}

lemma val_succ (m : ℕ) (p : P) : val t H king adv inp (m + 1) p =
    if (out t H king adv inp m p).1 = .commit then (out t H king adv inp m p).2
    else kingMsg t H king adv m (val t H king adv inp m) p := rfl

lemma out_commit_ne_two {m : ℕ} {p : P} (h : (out t H king adv inp m p).1 = .commit) :
    (out t H king adv inp m p).2 ≠ 2 := by
  simp only [out, acOut, acRet] at h ⊢; split_ifs at h ⊢ with h' <;> simp_all

/-- **Lemma 3 of [AACV] (eventual agreement).** After a round with an honest king, all honest processes
hold the same value, namely `min 1 σ` for the king's adopt-commit output `σ`. -/
theorem lemma3_honest_king (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {m : ℕ} (hk : king m ∈ H) :
    ∀ p ∈ H, val t H king adv inp (m + 1) p = min 1 (out t H king adv inp m (king m)).2 := by
  refine Cslib.Byzantine.kingPhase_agreement (H := (↑H : Set P))
    (val := fun p => (out t H king adv inp m p).2)
    (strong := fun p => (out t H king adv inp m p).1 = .commit)
    (keep := id) (adopt := fun v => min 1 v) ?_ ?_ ?_ ?_
  · intro i hi hc
    exact (lemma2_coherence _ _ _ hB hn hi hc hk)
  · intro i _ hc; simp only [val_succ, if_pos hc, id]
  · intro i _ hc; simp only [val_succ, if_neg hc, kingMsg, if_pos hk]; rfl
  · intro i _ hc
    have := out_commit_ne_two hc
    simp only [id]
    generalize (out t H king adv inp m i).2 = w at this ⊢
    revert w; decide

/-- **Persistence.** If all honest processes enter round `m` with `v ∈ {0, 1}`, they commit `v` in
round `m` and every later round. -/
theorem persistence (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {m : ℕ} {v : Fin 3} (hv : v ≠ 2)
    (h : ∀ p ∈ H, val t H king adv inp m p = v) :
    ∀ k, ∀ p ∈ H, val t H king adv inp (m + k) p = v ∧ out t H king adv inp (m + k) p = (.commit, v) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    exact ⟨h p hp, lemma2_convergence _ _ _ hB hn hv h p⟩
  | succ k ih =>
    have hval : ∀ p ∈ H, val t H king adv inp (m + (k + 1)) p = v := fun p hp => by
      rw [← add_assoc, val_succ, (ih p hp).2]; simp
    exact fun p hp => ⟨hval p hp, lemma2_convergence _ _ _ hB hn hv hval p⟩

/-- Among `t + 1` distinct kings one is honest. -/
theorem exists_honest_king (hB : #Hᶜ ≤ t) (hinj : Set.InjOn king (Set.Iic t)) :
    ∃ m ≤ t, king m ∈ H := by
  by_contra hne
  push Not at hne
  have hsub : (range (t + 1)).image king ⊆ Hᶜ := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.1 hp
    simp only [mem_compl]; exact hne m (by simpa [Nat.lt_succ_iff] using hm)
  have := card_le_card hsub
  rw [card_image_of_injOn (fun a ha b hb h => hinj (by simpa [Nat.lt_succ_iff] using ha)
    (by simpa [Nat.lt_succ_iff] using hb) h), card_range] at this
  omega

/-- After an honest king's round `m₀`, every honest commit (in round `m₀` or later) has the value all
honest processes hold after round `m₀`. -/
theorem commit_after_honest_king (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) {m₀ m : ℕ}
    (hk : king m₀ ∈ H) (hm : m₀ ≤ m) {p : P} (hp : p ∈ H)
    (hc : (out t H king adv inp m p).1 = .commit) :
    (out t H king adv inp m p).2 = min 1 (out t H king adv inp m₀ (king m₀)).2 := by
  set w := min 1 (out t H king adv inp m₀ (king m₀)).2
  have hw : w ≠ 2 := by
    simp only [w]; generalize (out t H king adv inp m₀ (king m₀)).2 = a; revert a; decide
  rcases hm.eq_or_lt with rfl | hlt
  · have hcoh := lemma2_coherence _ _ _ hB hn hp hc hk
    have h2 := out_commit_ne_two hc
    simp only [w, out] at hcoh h2 ⊢
    rw [hcoh]
    generalize (acOut t H (adv.b1 m₀) (adv.b2 m₀) (val t H king adv inp m₀) p).2 = a at h2 ⊢
    revert a; decide
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have := (persistence hB hn hw (lemma3_honest_king hB hn hk) k p hp).2
    rw [show m₀ + k + 1 = m₀ + 1 + k by omega, this]

/-- **Repaired template, agreement.** If the kings of rounds `0, …, t` are distinct and honest
processes decide on a commit only from round `t` on (0-based; the paper's round `t + 1`), all honest
decisions agree. -/
theorem repaired_agreement (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P)
    (hinj : Set.InjOn king (Set.Iic t)) {m m' : ℕ} (hm : t ≤ m) (hm' : t ≤ m') {p q : P}
    (hp : p ∈ H) (hq : q ∈ H) (hpc : (out t H king adv inp m p).1 = .commit)
    (hqc : (out t H king adv inp m' q).1 = .commit) :
    (out t H king adv inp m p).2 = (out t H king adv inp m' q).2 := by
  obtain ⟨m₀, hm₀, hk⟩ := exists_honest_king hB hinj
  rw [commit_after_honest_king hB hn hk (hm₀.trans hm) hp hpc,
    commit_after_honest_king hB hn hk (hm₀.trans hm') hq hqc]

/-- **Repaired template, termination.** Every honest process commits in round `t + 1` (0-based). -/
theorem repaired_termination (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P)
    (hinj : Set.InjOn king (Set.Iic t)) : ∀ p ∈ H, (out t H king adv inp (t + 1) p).1 = .commit := by
  obtain ⟨m₀, hm₀, hk⟩ := exists_honest_king hB hinj
  have hw : min 1 (out t H king adv inp m₀ (king m₀)).2 ≠ 2 := by
    generalize (out t H king adv inp m₀ (king m₀)).2 = a; revert a; decide
  have := persistence hB hn hw (lemma3_honest_king hB hn hk) (t - m₀)
  intro p hp
  rw [show t + 1 = m₀ + 1 + (t - m₀) by omega, (this p hp).2]

/-- **Validity of the composed protocol.** With binary honest inputs, every honest commit value is an
honest input. -/
theorem repaired_validity (hB : #Hᶜ ≤ t) (hn : 3 * t < Fintype.card P) (hinp : ∀ q ∈ H, inp q ≠ 2)
    {m : ℕ} {p : P} (hp : p ∈ H) (hc : (out t H king adv inp m p).1 = .commit) :
    ∃ q ∈ H, inp q = (out t H king adv inp m p).2 := by
  have h2 := out_commit_ne_two hc
  by_cases hu : ∃ v, ∀ q ∈ H, inp q = v
  · obtain ⟨v, hv⟩ := hu
    have hv2 : v ≠ 2 := hv p hp ▸ hinp p hp
    have := (persistence (king := king) (adv := adv) (m := 0) hB hn hv2 (by simpa [val] using hv) m p hp).2
    rw [zero_add] at this
    exact ⟨p, hp, by rw [this, hv p hp]⟩
  · push Not at hu
    obtain ⟨q₀, hq₀, h0⟩ := hu 0
    obtain ⟨q₁, hq₁, h1⟩ := hu 1
    have hq₀' : inp q₀ = 1 := by have := hinp q₀ hq₀; omega
    have hq₁' : inp q₁ = 0 := by have := hinp q₁ hq₁; omega
    generalize (out t H king adv inp m p).2 = w at h2 ⊢
    have : w = 0 ∨ w = 1 := by omega
    rcases this with rfl | rfl
    · exact ⟨q₁, hq₁, hq₁'⟩
    · exact ⟨q₀, hq₀, hq₀'⟩

/-! ### Counterexample: Algorithm 2 with Algorithms 3–4 violates agreement -/

/-- The honest processes `1, 2, 3` of the counterexample (process `0` is Byzantine). -/
def cxH : Finset (Fin 4) := {1, 2, 3}

/-- The king of round `m` is process `m` (mod 4), as in the paper (round `m` has king `m`). -/
def cxKing (m : ℕ) : Fin 4 := Fin.ofNat 4 m

/-- The Byzantine process `0` (king of round 0). Round 0, exchange 1: it sends `1` to process `3` and
`0` to the others; exchange 2: `0` to process `1`, `2` to the others; as king it sends `1`. Round 1:
it sends `1` everywhere. -/
def cxAdv : Adv (Fin 4) where
  b1 m p _ := if m = 0 then (if p = 3 then some 1 else some 0) else some 1
  b2 m p _ := if m = 0 then (if p = 1 then some 0 else some 2) else some 1
  bk _ _ := 1

/-- Honest inputs: process `1` and `2` start with `0`, process `3` with `1`. -/
def cxInp : Fin 4 → Fin 3 := ![0, 0, 0, 1]

/-- **The Phase-King decomposition violates agreement** (`n = 4`, `t = 1`). In round 0 (king: the
Byzantine process 0) honest process 1 commits `0` and decides; honest processes 2 and 3 adopt `0`
but take the king's `1` (so the conciliator returns a value nobody adopted: Algorithm 4 is not
valid, contrary to Lemma 3). In round 1 processes 2 and 3 commit and decide `1`. -/
theorem template_disagreement :
    (#cxHᶜ ≤ 1 ∧ 3 * 1 < Fintype.card (Fin 4) ∧ Set.InjOn cxKing (Set.Iic 1) ∧ ∀ q ∈ cxH, cxInp q ≠ 2) ∧
    out 1 cxH cxKing cxAdv cxInp 0 1 = (.commit, 0) ∧
    out 1 cxH cxKing cxAdv cxInp 0 2 = (.adopt, 0) ∧
    out 1 cxH cxKing cxAdv cxInp 0 3 = (.adopt, 0) ∧
    kingMsg 1 cxH cxKing cxAdv 0 cxInp 2 = 1 ∧
    out 1 cxH cxKing cxAdv cxInp 1 2 = (.commit, 1) ∧
    out 1 cxH cxKing cxAdv cxInp 1 3 = (.commit, 1) := by
  refine ⟨⟨by decide, by decide, ?_, by decide⟩, ?_⟩
  · intro a ha b hb h
    simp only [Set.mem_Iic] at ha hb
    interval_cases a <;> interval_cases b <;> first | rfl | (revert h; decide)
  · refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Podc.ObjectOrientedConsensus.PhaseKing
