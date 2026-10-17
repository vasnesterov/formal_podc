import Papers.PODC2015.CrashConsensusDigraph.WASafety

/-!
# Algorithm WA: termination, Theorem 7, and the asynchronous tight condition

* `delivered` — in a fair execution, every message in a channel between two nodes that never
  crash is eventually processed by the receiver (FIFO: induction on its position in the
  channel).
* `flood_path` — a message recorded by a never-crashing node `k` is eventually recorded by every
  node reachable from `k` through never-crashing nodes (relays forward every first-time message).
* `reach_phase` — every never-crashing node completes every phase: with `F` the set of nodes that
  ever crash, all nodes of `reachᵢ(F)` eventually reach phase `p` and their phase-`p` messages
  reach `i`, so Condition WAIT holds with `Fᵢ = F`, and a node never stays in a phase whose WAIT
  condition holds (`Closed`).
* **Theorem 7** (`theorem7`): under the condition of Theorem 6 (`CCA`), Algorithm WA with `pend`
  phases solves asynchronous approximate crash consensus for inputs in `[lo, hi]` as soon as
  `(1 − 1/n)^pend · (hi − lo) ≤ ε` (the paper: "`pend` sufficiently large as a function of
  `n, f, M, m`").
* `async_consensus_iff` — Theorems 6 and 7: for `0 < ε < hi − lo`, asynchronous approximate crash
  consensus on `[lo, hi]` is solvable iff `G` satisfies the condition of Theorem 6.
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj] {f pend : ℕ}

/-! ## Channel evolution -/

theorem chan_step {M S : Type*} (A : Algorithm V M S) (B : Finset V) (C : Config V M S)
    (e : Event V M) (he : ∀ x y m, e ≠ .byz x y m) (x y : V) :
    ((e = .deliver x y → C.chan x y = [] ∨ y ∈ B) ∧ ∃ l, (step A G B C e).chan x y = C.chan x y ++ l) ∨
      (e = .deliver x y ∧ ∃ m rest l, C.chan x y = m :: rest ∧ y ∉ B ∧
        (step A G B C e).chan x y = rest ++ l ∧
        step A G B C e = process A G B (C.pop x y rest) y x m) := by
  cases e with
  | skip => left; exact ⟨(fun h => by cases h), [], by simp [step]⟩
  | byz a b m => exact absurd rfl (he a b m)
  | deliver a b =>
    cases hc : C.chan a b with
    | nil =>
      left
      exact ⟨(fun h => by cases h; exact Or.inl hc), [], by simp [step, hc]⟩
    | cons m rest =>
      by_cases hb : b ∈ B
      · left
        exact ⟨(fun h => by cases h; exact Or.inr hb), [], by simp [step, hc, hb]⟩
      · have hs : step A G B C (.deliver a b) = process A G B (C.pop a b rest) b a m := by
          simp only [step, hc, hb, ↓reduceIte]
        have hch : (process A G B (C.pop a b rest) b a m).chan x y =
            if x = b then (if x = a ∧ y = b then rest else C.chan x y) ++
              sendTo G B b (A.recv b (C.st b) a m).2 y
            else (if x = a ∧ y = b then rest else C.chan x y) := rfl
        rw [hs, hch]
        by_cases hxy : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := hxy
          right
          refine ⟨rfl, m, rest, if x = y then sendTo G B y (A.recv y (C.st y) x m).2 y else [],
            hc, hb, ?_, rfl⟩
          have hT : (x = x ∧ y = y) = True := by simp
          rw [ite_eq_left_of_eq_true _ _ hT]
          split_ifs <;> simp
        · left
          refine ⟨(fun h => by cases h; exact absurd ⟨rfl, rfl⟩ hxy), ?_⟩
          rw [ite_eq_right_of_eq_false _ _ (eq_false hxy)]
          split_ifs
          · exact ⟨_, rfl⟩
          · exact ⟨[], (List.append_nil _).symm⟩

section Live

variable (ct : V → Option ℕ) (inp : V → ℝ) (ev : ℕ → Event V (ℝ × V × ℕ))

local notation "RC" => runC (wa G f pend) G ct inp ev

theorem seen_mono (hev : ∀ t x y m, ev t ≠ .byz x y m) {t t' : ℕ} (h : t ≤ t') (j : V) :
    ((RC t).st j).seen ⊆ ((RC t').st j).seen :=
  (ext_runC ct inp ev hev h j).2.2

theorem ph_mono (hev : ∀ t x y m, ev t ≠ .byz x y m) {t t' : ℕ} (h : t ≤ t') (j : V) :
    ((RC t).st j).ph ≤ ((RC t').st j).ph :=
  (ext_runC ct inp ev hev h j).1

/-- One step, tracking the position of a message in the channel `x → y` (`y` alive). -/
theorem index_step (hev : ∀ t x y m, ev t ≠ .byz x y m) {x y : V} (hy : ct y = none) {s k : ℕ}
    {m : ℝ × V × ℕ} (hk : ((RC s).chan x y)[k]? = some m) :
    (((RC (s + 1)).chan x y)[k]? = some m ∧ ev s ≠ .deliver x y) ∨
      (ev s = .deliver x y ∧ ((k = 0 ∧ m ∈ ((RC (s + 1)).st y).seen) ∨
        ∃ j, k = j + 1 ∧ ((RC (s + 1)).chan x y)[j]? = some m)) := by
  have hlt : k < ((RC s).chan x y).length := by
    by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hk; simp at hk
  rcases chan_step (G := G) (wa G f pend) (crashedAt ct s) (RC s) (ev s) (hev s) x y with
    ⟨hnd, l, hl⟩ | ⟨hd, m0, rest, l, hc, hyB, hl, hproc⟩
  · by_cases hd : ev s = .deliver x y
    · exfalso
      rcases hnd hd with h | h
      · rw [h] at hlt; simp at hlt
      · exact notMem_crashedAt_of_none hy h
    · left
      refine ⟨?_, hd⟩
      rw [runC_succ, hl, List.getElem?_append_left hlt, hk]
  · right
    refine ⟨hd, ?_⟩
    rw [hc] at hk
    have hstep : RC (s + 1) = process (wa G f pend) G (crashedAt ct s) ((RC s).pop x y rest) y x m0 :=
      by rw [runC_succ]; exact hproc
    cases k with
    | zero =>
      left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      refine ⟨rfl, ?_⟩
      rw [hstep]
      exact (winv_process (winv_runC ct inp ev hev s) hc).2.2
    | succ j =>
      right
      refine ⟨j, rfl, ?_⟩
      simp only [List.getElem?_cons_succ] at hk
      have hlt' : j < rest.length := by
        by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hk; simp at hk
      rw [runC_succ, hl, List.getElem?_append_left hlt', hk]

/-- **Fair delivery**: a message in a channel between nodes that never crash is eventually
processed by the receiver. -/
theorem delivered (hev : ∀ t x y m, ev t ≠ .byz x y m) (hfair : FairC (wa G f pend) G ct inp ev)
    {x y : V} (hx : ct x = none) (hy : ct y = none) {m : ℝ × V × ℕ} :
    ∀ (k t : ℕ), ((RC t).chan x y)[k]? = some m → ∃ t', m ∈ ((RC t').st y).seen := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t hk
    have hne : (RC t).chan x y ≠ [] := by intro h; rw [h] at hk; simp at hk
    obtain ⟨t1, ht1, hd⟩ := hfair x y hx hy t hne
    -- persistence until `t1`
    have hpers : ∀ s, t ≤ s → s ≤ t1 → (∃ t', m ∈ ((RC t').st y).seen) ∨
        ∃ k' ≤ k, ((RC s).chan x y)[k']? = some m := by
      intro s hs
      induction s, hs using Nat.le_induction with
      | base => intro _; exact Or.inr ⟨k, le_rfl, hk⟩
      | succ s hs ihs =>
        intro hs1
        rcases ihs (by omega) with h | ⟨k', hk', hk's⟩
        · exact Or.inl h
        · rcases index_step ct inp ev hev hy hk's with ⟨h1, -⟩ | ⟨-, ⟨-, h1⟩ | ⟨j, rfl, h1⟩⟩
          · exact Or.inr ⟨k', hk', h1⟩
          · exact Or.inl ⟨_, h1⟩
          · exact Or.inr ⟨j, by omega, h1⟩
    rcases hpers t1 ht1 le_rfl with h | ⟨k', hk', hk't1⟩
    · exact h
    · rcases index_step ct inp ev hev hy hk't1 with ⟨-, h1⟩ | ⟨-, ⟨-, h1⟩ | ⟨j, rfl, h1⟩⟩
      · exact absurd hd h1
      · exact ⟨_, h1⟩
      · exact ih j (by omega) (t1 + 1) h1

/-- A recorded message crosses an edge between nodes that never crash. -/
theorem flood_edge (hev : ∀ t x y m, ev t ≠ .byz x y m) (hfair : FairC (wa G f pend) G ct inp ev)
    {x y : V} (hx : ct x = none) (hy : ct y = none) (e : G.Adj x y) {m : ℝ × V × ℕ} {t : ℕ}
    (hm : m ∈ ((RC t).st x).seen) : ∃ t', m ∈ ((RC t').st y).seen := by
  by_cases hxy : x = y
  · subst hxy; exact ⟨t, hm⟩
  rcases (winv_runC ct inp ev hev t).flood x y m e hxy (notMem_crashedAt_of_none hx)
    (notMem_crashedAt_of_none hy) hm with h | h
  · exact ⟨t, h⟩
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
    exact delivered ct inp ev hev hfair hx hy k t hk

/-- The set of nodes that ever crash. -/
def faulty (ct : V → Option ℕ) : Finset V := univ.filter fun x => ct x ≠ none

theorem notMem_faulty {x : V} : x ∉ faulty ct ↔ ct x = none := by
  simp [faulty]

theorem faulty_card {f : ℕ} (h : CrashAdm ct f) : (faulty ct).card ≤ f := by
  obtain ⟨F, hF, hmem⟩ := h
  refine le_trans (card_le_card fun x hx => ?_) hF
  simp only [faulty, mem_filter, mem_univ, true_and] at hx
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hx
  exact hmem x c hc

/-- A recorded message reaches every node reachable through never-crashing nodes. -/
theorem flood_path (hev : ∀ t x y m, ev t ≠ .byz x y m) (hfair : FairC (wa G f pend) G ct inp ev)
    {k i : V} (h : Reaches G (faulty ct) k i) {m : ℝ × V × ℕ} {t : ℕ}
    (hm : m ∈ ((RC t).st k).seen) : ∃ t', m ∈ ((RC t').st i).seen := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact ⟨t, hm⟩
  | tail _ e ih =>
    obtain ⟨t', ht'⟩ := ih
    exact flood_edge ct inp ev hev hfair ((notMem_faulty ct).mp e.2.1) ((notMem_faulty ct).mp e.2.2)
      e.1 ht'

/-- **Every phase is completed** by the nodes that never crash. -/
theorem reach_phase (hev : ∀ t x y m, ev t ≠ .byz x y m) (hfair : FairC (wa G f pend) G ct inp ev)
    (hadm : CrashAdm ct f) :
    ∀ p, 1 ≤ p → p ≤ pend + 1 → ∀ i, ct i = none → ∃ t, p ≤ ((RC t).st i).ph := by
  intro p hp1
  induction p, hp1 using Nat.le_induction with
  | base => intro _ i _; exact ⟨0, ((winv_runC ct inp ev hev 0).li i).ph_pos⟩
  | succ p hp1 ih =>
    intro hp i hi
    have ih' := ih (by omega)
    have hk : ∀ k, ∃ t, ct k = none → p ≤ ((RC t).st k).ph := by
      intro k
      by_cases hk : ct k = none
      · obtain ⟨t, ht⟩ := ih' k hk; exact ⟨t, fun _ => ht⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose tk htk using hk
    -- every node of `reachᵢ(F)` is eventually heard in phase `p`
    have hheard : ∀ k, ∃ t, Reaches G (faulty ct) k i → k ∈ ((RC t).st i).heard p := by
      intro k
      by_cases hr : Reaches G (faulty ct) k i
      · have hkc : ct k = none := (notMem_faulty ct).mp hr.1
        have hown := ((winv_runC ct inp ev hev (tk k)).li k).own p hp1 (htk k hkc) (by omega)
        obtain ⟨t', ht'⟩ := flood_path ct inp ev hev hfair hr hown
        exact ⟨t', fun _ => mem_heard.mpr ⟨_, ht'⟩⟩
      · exact ⟨0, fun h => absurd h hr⟩
    choose τ hτ using hheard
    set T := max (tk i) (univ.sup τ)
    have hphT : p ≤ ((RC T).st i).ph :=
      le_trans (htk i hi) (ph_mono ct inp ev hev (le_max_left _ _) i)
    have hwait : Wait G f i (((RC T).st i).heard p) := by
      refine ⟨faulty ct, (notMem_faulty ct).mpr hi, faulty_card ct hadm, fun w hw => ?_⟩
      have hle : τ w ≤ T := le_trans (le_sup (mem_univ w)) (le_max_right _ _)
      exact heard_mono (seen_mono ct inp ev hev hle i) p (hτ w hw)
    refine ⟨T, ?_⟩
    by_contra hlt
    have heq : ((RC T).st i).ph = p := by omega
    exact (winv_runC ct inp ev hev T).closed i ⟨by omega, heq ▸ hwait⟩

end Live

/-! ## Theorem 7 -/

/-- **Theorem 7.** If `G` satisfies the condition of Theorem 6 (every partition `L, C, R` with
`L, R ≠ ∅` has `L ∪ C → R` or `C ∪ R → L`), then Algorithm WA with `pend` phases solves
asynchronous approximate crash consensus with at most `f` crashes for inputs in `[lo, hi]`,
provided `(1 − 1/n)^pend · (hi − lo) ≤ ε`. -/
theorem theorem7 (hG : CCA G f) {lo hi ε : ℝ} (hlohi : lo ≤ hi)
    (hp : (1 - 1 / (Fintype.card V : ℝ)) ^ pend * (hi - lo) ≤ ε) :
    CrashSolvesGenOn (Set.Icc lo hi) (wa G f pend) G f ε := by
  have h2 : TwoReach G f := cca_iff_twoReach.mp hG
  intro ct hadm inp hinp ev hev
  refine ⟨fun t v u y z _ _ hy hz => ?_, fun t v y _ hy => ?_, fun hfair v hv => ?_⟩
  · exact (wa_agreement h2 hlohi hinp (winv_runC ct inp ev hev t) hy hz).trans hp
  · exact wa_validity h2 (winv_runC ct inp ev hev t) hy
  · obtain ⟨t, ht⟩ := reach_phase (G := G) (f := f) (pend := pend) ct inp ev hev hfair hadm
      (pend + 1) (by omega) le_rfl v hv
    have hne := (winv_runC (G := G) (f := f) (pend := pend) ct inp ev hev t).dec_none v (by omega)
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hne
    exact ⟨t, y, hy⟩

/-- **Tight condition for asynchronous approximate crash consensus** (Theorems 6 and 7): for
inputs in `[lo, hi]` and `0 < ε < hi − lo`, approximate consensus tolerating `f` crashes is
solvable on `G` iff every partition `L, C, R` of `V` with `L, R ≠ ∅` has `L ∪ C → R` or
`C ∪ R → L`. -/
theorem async_consensus_iff {lo hi ε : ℝ} (hε : 0 < ε) (hεlh : ε < hi - lo) :
    (∃ (M S : Type u) (A : Algorithm V M S), CrashSolvesGenOn (Set.Icc lo hi) A G f ε) ↔
      CCA G f := by
  constructor
  · rintro ⟨M, S, A, h⟩
    exact theorem6_gen (a := lo) (b := hi) (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩)
      (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩) hεlh h
  · intro hG
    refine ⟨ℝ × V × ℕ, WS V, ?_⟩
    have hlh : 0 < hi - lo := by linarith
    rcases isEmpty_or_nonempty V with hV | hV
    · refine ⟨wa G f 0, ?_⟩
      intro ct _ inp _ ev _
      exact ⟨fun _ v => (hV.false v).elim, fun _ v => (hV.false v).elim,
        fun _ v => (hV.false v).elim⟩
    · have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
      have hq0 : 0 ≤ 1 - 1 / (Fintype.card V : ℝ) := by
        rw [sub_nonneg, div_le_one (by linarith)]; exact hn
      have hq1 : 1 - 1 / (Fintype.card V : ℝ) < 1 := by
        have : 0 < 1 / (Fintype.card V : ℝ) := by positivity
        linarith
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hlh) hq1
      refine ⟨wa G f k, theorem7 hG (by linarith) ?_⟩
      rw [lt_div_iff₀ hlh] at hk
      exact hk.le

end CrashConsensusDigraph
