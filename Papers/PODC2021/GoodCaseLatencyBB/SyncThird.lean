import Papers.PODC2021.GoodCaseLatencyBB.Basic
import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth
import Cslib.Foundations.Combinatorics.Labelling

/-!
# BRB good-case latency `≥ Δ + δ` for `f ≥ n/3` under synchronized start (Theorem 9)

Abraham, Nayak, Ren, Xiang, *Good-case Latency of Byzantine Broadcast: a Complete
Categorization*, PODC 2021, Theorem 9 (proof in Appendix C.2).

We split the processes into three groups `A = {g = 0}`, `B = {g = 1}`, `C = {g = 2}` of size
`≤ f` each, with the broadcaster `s ∈ C` and `A`, `B` nonempty. The three executions of the paper:

* **Ex1** = `(world … a).enlarge A {g = 1}`: `B` is Byzantine but behaves honestly in a world
  where every link touching `B` has effective delay `Δ` (all other links `δ`); `s` has input `a`.
  It is a synchronous run with delay bound `δ`, so some `x ∈ A` commits `a` before `Δ + δ`.
* **Ex2**: the mirror image (`A` Byzantine, `s` has input `b`, some `y ∈ B` commits `b`).
* **Ex3** (`ex3`): `C` is Byzantine and replays, up to time `Δ + δ - 1`, to `A` what it sent in
  Ex1 and to `B` what it sent in Ex2; the `A`–`B` links have delay `Δ`, all others `δ`. It is a
  synchronous run with delay bound `Δ`.

`A` cannot distinguish Ex3 from Ex1 before `Δ + δ` (`side_st`): messages from `B` arriving
before `Δ + δ` were sent before `δ`, when `B` has received nothing in both runs. Unforgeability of
the replay in Ex3 follows from `Run.tokens_replay_dl` (`side_tokens`). The mirror side is obtained by
relabelling (`mirror`), so `side_st`/`side_tokens`/`side_decides` are proved once.
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P]

namespace SyncThird

/-- A process all of whose incoming batches are delivered at times `≥ τ₀` has received nothing
before `τ₀`. -/
theorem st_eq_quiet [Fintype P] (A : Algorithm P M S V V) (R : Run P M V) {q : P} {τ₀ : ℕ}
    (h : ∀ r σ, τ₀ ≤ R.dl r σ q) : ∀ τ ≤ τ₀, R.st A τ q = quiet A q (R.inp q) τ := by
  intro τ hτ
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [Run.st_succ, ih (by omega)]
    change _ = A.step q (quiet A q (R.inp q) τ) fun _ => []
    congr 1
    funext r
    rw [Run.inbox_eq_flatMap]
    apply List.flatMap_eq_nil_iff.mpr
    intro τ' _
    exact Run.dlv_eq_nil_of_ne A R (by have := h r τ'; omega)

/-- The honest world behind Ex1: nobody is faulty, `s` has input `v` (others `I₀`), every link
touching group `1` has effective delay `Δ`, all other links `δ`. -/
def world (I₀ : P → V) (s : P) (g : P → ℕ) (δ Δ : ℕ) (v : V) : Run P M V where
  faulty := ∅
  inp := Function.update I₀ s v
  gst := 0
  byz _ _ _ := []
  dl q τ p := τ + (if g q = 1 ∨ g p = 1 then Δ else δ) - 1

section side

variable [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V}
  {I₀ : P → V} {s : P} {g : P → ℕ} {δ Δ : ℕ} {v : V} {R : Run P M V}

/-- Hypotheses on Ex3 seen from group `0` (with reference world `world I₀ s g δ Δ v`). -/
structure Side (I₀ : P → V) (s : P) (g : P → ℕ) (δ Δ : ℕ) (v : V) (A : Algorithm P M S V V)
    (R : Run P M V) : Prop where
  hg : ∀ p, g p ≤ 2
  hs : g s = 2
  hF : ∀ p, p ∈ R.faulty ↔ g p = 2
  hinp : ∀ p, g p ≠ 2 → R.inp p = I₀ p
  hdl0 : ∀ q τ p, g p = 0 → R.dl q τ p = τ + (if g q = 1 then Δ else δ) - 1
  hdl1 : ∀ q τ p, g p = 1 → δ - 1 ≤ R.dl q τ p
  hbyz : ∀ q τ p, g q = 2 → g p = 0 → τ ≤ Δ + δ - 1 →
    R.byz q τ p = (world I₀ s g δ Δ v : Run P M V).out A q τ p

/-- Group `1` has received nothing before `δ - 1`, both in Ex3 and in the world. -/
theorem side_st_one (h : Side I₀ s g δ Δ v A R) (hδΔ : δ ≤ Δ) {q : P} (hq : g q = 1) {τ : ℕ}
    (hτ : τ ≤ δ - 1) : R.st A τ q = (world I₀ s g δ Δ v : Run P M V).st A τ q := by
  have hqs : q ≠ s := by rintro rfl; have := h.hs; omega
  rw [st_eq_quiet A R (fun r σ => h.hdl1 r σ q hq) τ hτ,
    st_eq_quiet A (world I₀ s g δ Δ v) (fun r σ => by simp [world, hq]; omega) τ hτ,
    h.hinp q (by omega)]
  simp [world, Function.update_of_ne hqs]

/-- **Indistinguishability for group `0`**: up to time `Δ + δ - 1`, group `0` has the same
states in Ex3 as in the world. -/
theorem side_st_zero (h : Side I₀ s g δ Δ v A R) (hδΔ : δ ≤ Δ) :
    ∀ τ ≤ Δ + δ - 1, ∀ p, g p = 0 →
      R.st A τ p = (world I₀ s g δ Δ v : Run P M V).st A τ p := by
  have hW : ∀ q, q ∉ (world I₀ s g δ Δ v : Run P M V).faulty := by simp [world]
  have hX := R.st_eq_of_inbox_eq A (ref := fun _ => world I₀ s g δ Δ v) (X := {p | g p = 0})
    (T := Δ + δ - 1) ?_ ?_
  · exact fun τ hτ p hp => hX τ hτ p hp
  · intro p hp
    have hps : p ≠ s := by rintro rfl; have := h.hs; simp at hp; omega
    simp only [Set.mem_ofPred_eq] at hp
    rw [h.hinp p (by omega)]
    simp [world, Function.update_of_ne hps]
  · intro τ hτ ih p hp
    simp only [Set.mem_ofPred_eq] at hp
    refine R.inbox_eq_of_dlv_eq A fun q τ' hτ' => ?_
    have hdl : R.dl q τ' p = (world I₀ s g δ Δ v : Run P M V).dl q τ' p := by
      rw [h.hdl0 q τ' p hp]; simp [world, hp]
    simp only [Run.dlv, hdl]
    split_ifs with hd
    · have := h.hg q
      rcases (by omega : g q = 0 ∨ g q = 1 ∨ g q = 2) with hq | hq | hq
      · rw [Run.out_of_correct A R (by rw [h.hF]; omega), Run.out_of_correct A _ (hW q),
          ih q hq τ' hτ']
      · have : τ' ≤ δ - 1 := by simp [world, hq] at hd; omega
        rw [Run.out_of_correct A R (by rw [h.hF]; omega), Run.out_of_correct A _ (hW q),
          side_st_one h hδΔ hq this]
      · rw [Run.out_of_faulty A R ((h.hF q).2 hq), h.hbyz q τ' p hq hp (by omega)]
    · rfl

/-- Processes of groups `0` and `1` send the same in Ex3 and in the world, as long as they
have the same states. -/
theorem side_out (h : Side I₀ s g δ Δ v A R) (hδΔ : δ ≤ Δ) {q : P} {σ : ℕ}
    (h0 : g q = 0 → σ ≤ Δ + δ - 1) (h1 : g q = 1 → σ ≤ δ - 1) (h2 : g q ≠ 2) (r : P) :
    R.out A q σ r = (world I₀ s g δ Δ v : Run P M V).out A q σ r := by
  have hW : q ∉ (world I₀ s g δ Δ v : Run P M V).faulty := by simp [world]
  rw [Run.out_of_correct A R (by rw [h.hF]; exact h2), Run.out_of_correct A _ hW]
  have := h.hg q
  rcases (by omega : g q = 0 ∨ g q = 1) with hq | hq
  · rw [side_st_zero h hδΔ σ (h0 hq) q hq]
  · rw [side_st_one h hδΔ hq (h1 hq)]

/-- **Unforgeability of the replay**: what a group-`2` process sends in the world up to time
`Δ + δ - 1` carries only tokens available to the adversary of Ex3 at that time. -/
theorem side_tokens (hU : A.Unforging Au) (h : Side I₀ s g δ Δ v A R) (hδΔ : δ ≤ Δ) :
    ∀ σ ≤ Δ + δ - 1, ∀ q, g q = 2 → ∀ r,
      ∀ m ∈ (world I₀ s g δ Δ v : Run P M V).out A q σ r, ∀ x ∈ Au.tokens m,
        Au.signer x ∈ R.faulty ∨ x ∈ R.honestTokens Au A σ := by
  intro σ hσ q hq r
  refine Run.tokens_replay_dl hU (Ri := world I₀ s g δ Δ v) (R' := R) (T := Δ + δ - 1) ?_ σ hσ q
    (by simp [world]) ((h.hF q).2 hq) r
  intro q' σ' r' hlt hle
  have := h.hg q'
  by_cases h2 : g q' = 2
  · exact Or.inl ⟨(h.hF q').2 h2, by simp [world]⟩
  · right
    intro m hm x hx
    have hσ' : g q' = 1 → σ' ≤ δ - 1 := fun h1 => by simp [world, h1] at hlt; omega
    rw [← side_out h hδΔ (by omega) hσ' h2] at hm
    exact Or.inr (Run.mem_honestTokens_of_out (by rw [h.hF]; exact h2) hle hm hx)

/-- **One side of the argument**: if `world … v` enlarged by group `1` (Ex1) is admissible for
the good case with delay `δ`, a group-`0` process `x` decides `v` in Ex3. -/
theorem side_decides {s : P} {f : ℕ} (hU : A.Unforging Au) (h : Side I₀ s g δ Δ v A R)
    (hδ : 1 ≤ δ) (hδΔ : δ ≤ Δ) (hf : (univ.filter (g · = 1)).card ≤ f)
    (hA : IsBRB Au A s (syncRuns f Δ)) (hL : LatencyWithin Au A s (syncRuns f δ) (Δ + δ - 1))
    {x : P} (hx : g x = 0) : R.Decides A x v := by
  set W : Run P M V := world I₀ s g δ Δ v
  set F := univ.filter (g · = 1)
  have hWF : W.faulty ⊆ F := by simp [W, world]
  set E1 := W.enlarge A F
  have hE1 : SyncValid f δ E1 := by
    refine ⟨hf, fun q τ p hq hp => ?_, fun q τ p hq hp => ?_⟩ <;>
      simp [E1, F, W, world] at hq hp ⊢ <;> simp [hq, hp] <;> omega
  have hE1a : E1.AuthValid Au A :=
    Run.enlarge_authValid hU (fun b hb => by simp [W, world] at hb) hWF
  have hsF : s ∉ E1.faulty := by simp [E1, F, h.hs]
  have hxF : x ∉ E1.faulty := by simp [E1, F, hx]
  have hval := hA.validity E1 (hE1.mono hδΔ) hE1a hsF x hxF
  have hinp : E1.inp s = v := by simp [E1, W, world]
  rw [hinp] at hval
  obtain ⟨τ, hτ, hd⟩ := CommitsBy.eq_of_agreement
    (fun w hw hv => hA.agreement E1 (hE1.mono hδΔ) hE1a x hxF x hxF w v hw hv)
    (hL E1 hE1 hE1a hsF x hxF) hval
  refine ⟨τ, ?_⟩
  rw [side_st_zero h hδΔ τ hτ x hx, ← Run.enlarge_st hWF τ x (by simpa [E1] using hxF)]
  exact hd

end side

/-! ### The mirror labelling and Ex3 -/

/-- Swap groups `0` and `1`. -/
def mirror (g : P → ℕ) (p : P) : ℕ := if g p = 0 then 1 else if g p = 1 then 0 else g p

theorem mirror_spec (g : P → ℕ) (p : P) :
    (g p = 0 ∧ mirror g p = 1) ∨ (g p = 1 ∧ mirror g p = 0) ∨ (g p ≠ 0 ∧ g p ≠ 1 ∧
      mirror g p = g p) := by
  unfold mirror; split_ifs <;> omega

/-- Execution 3: group `2` is Byzantine and replays (up to `Δ + δ - 1`) to group `0` what it
sent in the world with input `a`, and to the other groups what it sent in the mirrored world
with input `b`; links between groups `0` and `1` have delay `Δ`, all others `δ`. -/
def ex3 [Fintype P] (A : Algorithm P M S V V) (I₀ : P → V) (s : P) (g : P → ℕ) (δ Δ : ℕ) (a b : V) :
    Run P M V where
  faulty := univ.filter (g · = 2)
  inp := I₀
  gst := 0
  byz q τ p := if τ ≤ Δ + δ - 1 then
    (if g p = 0 then (world I₀ s g δ Δ a : Run P M V).out A q τ p
      else (world I₀ s (mirror g) δ Δ b : Run P M V).out A q τ p) else []
  dl q τ p := τ + (if (g q = 0 ∧ g p = 1) ∨ (g q = 1 ∧ g p = 0) then Δ else δ) - 1

section ex3

variable [Fintype P]

theorem ex3_side (A : Algorithm P M S V V) (I₀ : P → V) {s : P} {g : P → ℕ} {δ Δ : ℕ} (a b : V)
    (hg : ∀ p, g p ≤ 2) (hs : g s = 2) (hδΔ : δ ≤ Δ) :
    Side I₀ s g δ Δ a A (ex3 A I₀ s g δ Δ a b) where
  hg := hg
  hs := hs
  hF p := by simp [ex3]
  hinp p _ := rfl
  hdl0 q τ p hp := by simp [ex3, hp]
  hdl1 q τ p hp := by simp [ex3, hp]; split_ifs <;> omega
  hbyz q τ p _ hp hτ := by simp [ex3, hp, hτ]

theorem ex3_side_mirror (A : Algorithm P M S V V) (I₀ : P → V) {s : P} {g : P → ℕ} {δ Δ : ℕ}
    (a b : V) (hg : ∀ p, g p ≤ 2) (hs : g s = 2) (hδΔ : δ ≤ Δ) :
    Side I₀ s (mirror g) δ Δ b A (ex3 A I₀ s g δ Δ a b) where
  hg p := by have := mirror_spec g p; have := hg p; omega
  hs := by simp [mirror, hs]
  hF p := by have := mirror_spec g p; simp only [ex3, mem_filter, mem_univ, true_and]; omega
  hinp p _ := rfl
  hdl0 q τ p hp := by
    have := mirror_spec g p; have := mirror_spec g q
    simp only [ex3]
    split_ifs <;> omega
  hdl1 q τ p hp := by simp only [ex3]; split_ifs <;> omega
  hbyz q τ p _ hp hτ := by
    have := mirror_spec g p
    simp only [ex3, hτ, ite_true, show g p ≠ 0 by omega, ite_false]

end ex3

/-- A partition of `P` into three groups of size `≤ f`, the first two nonempty and the
broadcaster in the third. -/
theorem exists_partition [Fintype P] (s : P) {f : ℕ} (h3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 3 * f) :
    ∃ g : P → ℕ, (∀ p, g p ≤ 2) ∧ g s = 2 ∧ (∃ x, g x = 0) ∧ (∃ y, g y = 1) ∧
      ∀ i, (univ.filter (g · = i)).card ≤ f := by
  obtain ⟨g, hs, hg, hc⟩ := Fintype.exists_labelling_apply_eq 3 (fun _ => 1) (fun _ => f)
    (fun _ _ => by omega) (by simpa using h3) (by simpa [mul_comm] using hn) s (i₀ := 2) (by omega)
    le_rfl
  have hne : ∀ i < 3, ∃ x, g x = i := fun i hi => by
    obtain ⟨x, -, hx⟩ := filter_nonempty_iff.1 (card_pos.1 (hc i hi).1); exact ⟨x, hx⟩
  refine ⟨g, fun p => by have := hg p; omega, hs, hne 0 (by omega), hne 1 (by omega),
    fun i => ?_⟩
  by_cases hi : i < 3
  · exact (hc i hi).2
  · rw [filter_false_of_mem fun p _ => by have := hg p; omega]; simp

end SyncThird

open SyncThird

/-- **Theorem 9 of [ANRX21].** Under synchronized start, if `f ≥ n/3` (and `n ≥ 3`), a
Byzantine reliable broadcast protocol that is correct in all synchronous runs with delay bound
`Δ` does not have good-case latency `< Δ + δ`: in some synchronous run with honest broadcaster
and actual delay bound `δ`, some honest process has not committed before time `Δ + δ`. -/
theorem theorem_9 [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V} (hU : A.Unforging Au)
    {s : P} {f Δ δ : ℕ} (hδ : 1 ≤ δ) (hδΔ : δ ≤ Δ) (h3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 3 * f) {a b : V} (hab : a ≠ b) (hA : IsBRB Au A s (syncRuns f Δ)) :
    ¬ LatencyWithin Au A s (syncRuns f δ) (Δ + δ - 1) := by
  intro hL
  obtain ⟨g, hg, hs, ⟨x, hx⟩, ⟨y, hy⟩, hcard⟩ := exists_partition s h3 hn
  set R := ex3 A (fun _ => a) s g δ Δ a b
  have h1 := ex3_side A (fun _ => a) a b hg hs hδΔ
  have h2 := ex3_side_mirror A (fun _ => a) a b hg hs hδΔ
  have hdx : R.Decides A x a := side_decides hU h1 hδ hδΔ (hcard 1) hA hL hx
  have hdy : R.Decides A y b := by
    refine side_decides hU h2 hδ hδΔ ?_ hA hL (by simp [mirror, hy])
    refine (card_le_card fun p hp => ?_).trans (hcard 0)
    have := mirror_spec g p
    simp only [mem_filter, mem_univ, true_and] at hp ⊢; omega
  have hR : SyncValid f Δ R := by
    refine ⟨hcard 2, fun q τ p _ _ => ?_, fun q τ p _ _ => ?_⟩ <;>
      simp only [R, ex3] <;> split_ifs <;> omega
  have hRa : R.AuthValid Au A := by
    intro q hq τ r hr m hm k hk
    have hq2 : g q = 2 := by simpa [R, ex3] using hq
    have hr2 : g r ≠ 2 := by simpa [R, ex3] using hr
    simp only [R, ex3] at hm
    split_ifs at hm with hτ hr0
    · exact side_tokens hU h1 hδΔ τ hτ q hq2 r m hm k hk
    · exact side_tokens hU h2 hδΔ τ hτ q (by simp [mirror, hq2]) r m hm k hk
    · simp at hm
  exact hab (hA.agreement R hR hRa x (by simp [R, ex3, hx]) y (by simp [R, ex3, hy]) a b hdx hdy)

end GoodCaseLatencyBB
