import Papers.PODC2018.FairLeaderElection.TreeBounds
import Papers.PODC2018.FairLeaderElection.TreeTwoParty

/-!
# Theorem 7.2 of [YM18] for two processors, and the failure of its boundary case

[YM18] A. Yifrach, Y. Mansour. *Fair Leader Election for Rational Agents in Asynchronous Rings and
Networks.* PODC 2018 (arXiv:1805.04778v2).

On a graph with two adjacent vertices `x, y` (the graph `K₂`), an execution of the general model
under the alternating schedule `alt x y` is an execution of the two-processor ring of
`Cslib.UniRing` (`grun_alt`); hence the outcome is `some o` iff the two processors `Agree` on
`some o` (`goutcome_alt`). With Lemma F.2 (`lemma_F2`) this gives:

* `thm_7_2_two`: **Theorem 7.2 for `n = 2`**: on every graph with two vertices (each is a
  `1`-simulated tree), no FLE protocol is `ε`-`k`-resilient for `ε < 1/2` and `1 ≤ k ≤ 2`.
* `k2FLE`, `k2FLE_isFLE`: an FLE protocol on `K₂` (`0` draws the leader, sends it and outputs it,
  `1` outputs what it receives).
* `thm_7_2_boundary_false`: the statement of Theorem 7.2 for `ε = 1/n` is false: `k2FLE` is
  `1/2`-`1`-resilient on `K₂`, which is a `1`-simulated tree (by the general upper bound
  `isResilient_one_sub`).
-/

namespace Podc.FairLeaderElection.Trees

open Cslib.UniRing

variable {V M : Type*} [DecidableEq V]

/-! ### Two-vertex graphs are two-processor rings -/

/-- A processor of a two-vertex graph seen as a ring processor receiving from and sending to `z`. -/
def toRing (p : GProc V M) (z : V) : Proc M (Option V) where
  sent h := p.sent (h.map (Prod.mk z)) z
  sent_snoc h m := by simpa using p.sent_snoc (h.map (Prod.mk z)) (z, m) z
  out h := p.out (h.map (Prod.mk z))

/-- A ring processor as a processor of a two-vertex graph sending to `z`. -/
def fromRing (q : Proc M (Option V)) (z : V) : GProc V M where
  sent h w := if w = z then q.sent (h.map Prod.snd) else []
  sent_snoc h e w := by
    split_ifs
    · simpa using q.sent_snoc (h.map Prod.snd) e.2
    · exact List.nil_prefix
  out h := q.out (h.map Prod.snd)

theorem toRing_fromRing (q : Proc M (Option V)) (z : V) : toRing (fromRing q z) z = q := by
  cases q
  simp [toRing, fromRing, Function.comp_def]

/-- The alternating schedule on the edge `xy`. -/
def alt (x y : V) (t : ℕ) : V × V := if t % 2 = 0 then (x, y) else (y, x)

/-- The alternating ring schedule. -/
def altR (t : ℕ) : Fin 2 := if t % 2 = 0 then 1 else 0

theorem fair_altR : Fair altR := by
  intro i N
  fin_cases i
  · exact ⟨2 * N + 1, by omega, by simp [altR, Nat.add_mod]⟩
  · exact ⟨2 * N, by omega, by simp [altR]⟩

section bridge

variable (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}

theorem grun_alt (hxy : x ≠ y) (hadj : G.Adj x y) (Q : V → GProc V M) (t : ℕ) :
    grun G Q (alt x y) t x =
        (run (sys (toRing (Q x) y) (toRing (Q y) x)) altR t 0).map (Prod.mk y) ∧
      grun G Q (alt x y) t y =
        (run (sys (toRing (Q x) y) (toRing (Q y) x)) altR t 1).map (Prod.mk x) := by
  induction t with
  | zero => simp [grun, run, init]
  | succ t ih =>
    obtain ⟨ih0, ih1⟩ := ih
    simp only [grun, run]
    set r := run (sys (toRing (Q x) y) (toRing (Q y) x)) altR t
    set c := grun G Q (alt x y) t
    have o0 : (sys (toRing (Q x) y) (toRing (Q y) x) 0).out (r 0) = (Q x).out (c x) := by
      simp [toRing, ih0]
    have o1 : (sys (toRing (Q x) y) (toRing (Q y) x) 1).out (r 1) = (Q y).out (c y) := by
      simp [toRing, ih1]
    have f0 : ((c x).filter (fun e => decide (e.1 = y))).length = (r 0).length := by
      rw [ih0, List.filter_map]; simp [Function.comp_def]
    have f1 : ((c y).filter (fun e => decide (e.1 = x))).length = (r 1).length := by
      rw [ih1, List.filter_map]; simp [Function.comp_def]
    have s0 : (Q x).sent (c x) y = (sys (toRing (Q x) y) (toRing (Q y) x) 0).sent (r 0) := by
      simp [toRing, ih0]
    have s1 : (Q y).sent (c y) x = (sys (toRing (Q x) y) (toRing (Q y) x) 1).sent (r 1) := by
      simp [toRing, ih1]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · simp only [alt, altR, h, ite_true]
      unfold gdeliver deliver pending received inbox
      simp only [hadj, true_and, o1, f1, s0, show (1 : Fin 2) - 1 = 0 from rfl]
      split_ifs <;> simp [Function.update, hxy, ih0, ih1]
    · simp only [alt, altR, h, ite_false, show (1 : ℕ) ≠ 0 from one_ne_zero]
      unfold gdeliver deliver pending received inbox
      simp only [hadj.symm, true_and, o0, f0, s1, show (0 : Fin 2) - 1 = 1 from rfl]
      split_ifs <;> simp [Function.update, Ne.symm hxy, ih0, ih1]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem gfair_alt (hV : ∀ v, v = x ∨ v = y) : GFair G (alt x y) := by
  intro u v huv N
  have hne : u ≠ v := G.ne_of_adj huv
  rcases hV u with rfl | rfl <;> rcases hV v with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨2 * N, by omega, by simp [alt]⟩
  · exact ⟨2 * N + 1, by omega, by simp [alt, Nat.add_mod]⟩
  · exact absurd rfl hne

theorem goutcome_alt (hxy : x ≠ y) (hadj : G.Adj x y) (hV : ∀ v, v = x ∨ v = y)
    (Q : V → GProc V M) (o : V) :
    goutcome G Q (alt x y) = some o ↔ Agree (toRing (Q x) y) (toRing (Q y) x) (some o) := by
  have : Nonempty V := ⟨x⟩
  rw [goutcome_eq_some_iff, agree_iff_run fair_altR]
  have e : ∀ v, (∃ t, (Q v).out (grun G Q (alt x y) t v) = some (some o)) ↔
      (v = x → ∃ t, (toRing (Q x) y).out
        (run (sys (toRing (Q x) y) (toRing (Q y) x)) altR t 0) = some (some o)) ∧
      (v = y → ∃ t, (toRing (Q y) x).out
        (run (sys (toRing (Q x) y) (toRing (Q y) x)) altR t 1) = some (some o)) := by
    intro v
    rcases hV v with rfl | rfl
    · simp only [(grun_alt G hxy hadj Q _).1, toRing, true_implies, hxy, false_implies, and_true]
    · simp only [(grun_alt G hxy hadj Q _).2, toRing, Ne.symm hxy, false_implies, true_implies,
        true_and]
  simp only [e]
  constructor
  · intro h; exact ⟨(h x).1 rfl, (h y).2 rfl⟩
  · intro h v; exact ⟨fun _ => h.1, fun _ => h.2⟩

end bridge

/-! ### Graphs without edges -/

section edgeless

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V] {I : V → Type*}
  [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]

omit [Fintype V] in
theorem grun_edgeless (hG : ∀ u v, ¬ G.Adj u v) (Q : V → GProc V M) (σ : ℕ → V × V) (t : ℕ) :
    grun G Q σ t = fun _ => [] := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [grun, gdeliver, hG, false_and, ite_false, ih]

/-- Without edges there is no FLE protocol on two or more processors. -/
theorem not_isFLE_of_edgeless (hG : ∀ u v, ¬ G.Adj u v) (hn : 2 ≤ Fintype.card V)
    (P : Protocol V M I) : ¬ IsFLE G P := by
  classical
  intro hP
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hn
  have : Nonempty V := ⟨x⟩
  let σ : ℕ → V × V := fun _ => (x, x)
  have hσ : GFair G σ := fun u v h => absurd h (hG u v)
  have hout : ∀ ω o, goutcome G (P.profile ω) σ = some o ↔
      ∀ v, (P.proc v (ω v)).out [] = some (some o) := by
    intro ω o
    rw [goutcome_eq_some_iff]
    simp [grun_edgeless G hG, Protocol.profile]
  have hex := fun ω => exists_outcome_of_isFLE G hP hσ ω
  choose f hf using hex
  have hconst : ∀ ω ω', f ω = f ω' := by
    intro ω ω'
    let ω'' : ∀ v, I v := fun v => if h : v = x then h ▸ ω x else ω' v
    have h1 := (hout _ _).mp (hf ω'')
    have hx := h1 x
    have hy := h1 y
    simp only [ω'', ↓reduceDIte] at hx
    simp only [ω'', Ne.symm hxy, ↓reduceDIte] at hy
    rw [(hout _ _).mp (hf ω) x] at hx
    rw [(hout _ _).mp (hf ω') y] at hy
    simp only [Option.some.injEq] at hx hy
    rw [hx, hy]
  obtain ⟨ω₀⟩ : Nonempty (∀ v, I v) := inferInstance
  have h1 : prob G P σ (some (f ω₀)) = 1 := by
    unfold prob
    rw [Finset.filter_true_of_mem (fun ω _ => by rw [hf ω, hconst ω ω₀]), Finset.card_univ,
      div_self (by positivity)]
  have h2 := hP σ hσ (f ω₀)
  rw [h1] at h2
  have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  rw [eq_div_iff (by positivity)] at h2
  linarith

end edgeless

/-! ### Theorem 7.2 for two processors -/

/-- The strategy "terminate at once with output `some o`, sending nothing". -/
def stopWith (o : V) : GProc V M where
  sent _ _ := []
  sent_snoc _ _ _ := List.nil_prefix
  out _ := some (some o)

/-- **Theorem 7.2 of [YM18] for `n = 2`.** On a graph with two vertices (every such graph is a
`1`-simulated tree), no FLE protocol with finite input sets is `ε`-`k`-resilient for `ε < 1/n` and
`1 ≤ k ≤ n`. The coalition of size `1` comes from Lemma F.2 (`lemma_F2`); for `k = 2` the coalition
of both processors trivially fixes the leader. -/
theorem thm_7_2_two [Fintype V] (hV : Fintype.card V = 2) {I : V → Type*} [∀ v, Fintype (I v)]
    [∀ v, Nonempty (I v)] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (_hT : IsKSimTree G k) (hk1 : 1 ≤ k) (hk2 : k ≤ Fintype.card V)
    (P : Protocol V M I) (hP : IsFLE G P) {ε : ℝ} (hε : ε < 1 / Fintype.card V) :
    ¬ IsResilient G P ε k := by
  classical
  obtain ⟨x, y, hxy, huniv⟩ := Finset.card_eq_two.mp (show (Finset.univ : Finset V).card = 2 from hV)
  have hVxy : ∀ v, v = x ∨ v = y := by
    intro v; have : v ∈ ({x, y} : Finset V) := by rw [← huniv]; exact Finset.mem_univ v
    simpa using this
  have hσ := gfair_alt G hVxy
  have : Nonempty V := ⟨x⟩
  have hSx : ({x} : Finset V) ≠ Finset.univ := by
    intro h; have : y ∈ ({x} : Finset V) := by rw [h]; exact Finset.mem_univ y
    simp at this; exact hxy this.symm
  have hSy : ({y} : Finset V) ≠ Finset.univ := by
    intro h; have : x ∈ ({y} : Finset V) := by rw [h]; exact Finset.mem_univ x
    simp at this; exact hxy this
  -- the coalition of everybody
  by_cases hk : k = 2
  · subst hk
    refine not_resilient_of_assures G hP hσ (C := Finset.univ) (by simp [hV]) hk2
      (fun _ _ => stopWith x) hSx (fun ω => ⟨x, by simp, ?_⟩) hε
    rw [goutcome_eq_some_iff]
    intro v
    exact ⟨0, by simp [Protocol.profile, Protocol.deviate, stopWith]⟩
  have hk1' : k = 1 := by omega
  subst hk1'
  by_cases hadj : G.Adj x y
  swap
  · refine absurd hP (not_isFLE_of_edgeless G (fun u v huv => ?_) (by omega) P)
    rcases hVxy u with rfl | rfl <;> rcases hVxy v with rfl | rfl
    · exact G.irrefl huv
    · exact hadj huv
    · exact hadj huv.symm
    · exact G.irrefl huv
  let SA : Set (Cslib.UniRing.Proc M (Option V)) :=
    Set.range fun ω : (∀ v, I v) => toRing (P.proc x (ω x)) y
  let SB : Set (Cslib.UniRing.Proc M (Option V)) :=
    Set.range fun ω : (∀ v, I v) => toRing (P.proc y (ω y)) x
  have hsucc : ∀ a ∈ SA, ∀ b ∈ SB, ∃ o ∈ ({some x} : Set (Option V)) ∪ {some y}, Agree a b o := by
    rintro _ ⟨ω₁, rfl⟩ _ ⟨ω₂, rfl⟩
    let ω : ∀ v, I v := fun v => if v = x then ω₁ v else ω₂ v
    obtain ⟨o, ho⟩ := exists_outcome_of_isFLE G hP hσ ω
    have := (goutcome_alt G hxy hadj hVxy _ o).mp ho
    simp only [Protocol.profile, ω, Ne.symm hxy, ↓reduceIte] at this
    refine ⟨some o, ?_, this⟩
    rcases hVxy o with rfl | rfl <;> simp
  rcases lemma_F2 (Set.finite_range _) (Set.finite_range _) hsucc with ⟨a', ha'⟩ | ⟨b', hb'⟩
  · refine not_resilient_of_assures G hP hσ (C := {x}) (by simp) hk2
      (fun _ _ => fromRing a' y) hSx (fun ω => ⟨x, by simp, ?_⟩) hε
    rw [goutcome_alt G hxy hadj hVxy]
    obtain ⟨o, ho, hag⟩ := ha' _ ⟨ω, rfl⟩
    simp only [Set.mem_singleton_iff] at ho
    subst ho
    simpa [Protocol.profile, Protocol.deviate, Ne.symm hxy, toRing_fromRing] using hag
  · refine not_resilient_of_assures G hP hσ (C := {y}) (by simp) hk2
      (fun _ _ => fromRing b' x) hSy (fun ω => ⟨y, by simp, ?_⟩) hε
    rw [goutcome_alt G hxy hadj hVxy]
    obtain ⟨o, ho, hag⟩ := hb' _ ⟨ω, rfl⟩
    simp only [Set.mem_singleton_iff] at ho
    subst ho
    simpa [Protocol.profile, Protocol.deviate, hxy, toRing_fromRing] using hag

/-! ### The boundary case `ε = 1/n` fails for `n = 2` -/

/-- `K₂`, the complete graph on two vertices. -/
abbrev K2 : SimpleGraph (Fin 2) := ⊤

theorem K2_isTree : K2.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.connected_top, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  decide

/-- `K₂` is a tree, hence a `1`-simulated tree. -/
theorem K2_isKSimTree : IsKSimTree K2 1 := by
  refine ⟨Fin 2, K2, id, K2_isTree,
    fun w => ?_, fun w => ?_, fun x y h => Or.inr h⟩
  · simp
  · have : Unique ↥((id : Fin 2 → Fin 2) ⁻¹' {w}) := Set.uniqueSingleton w
    exact SimpleGraph.Connected.of_subsingleton

/-- The sender: outputs its random input `i` and sends it to `1`. -/
def k2Sender (i : Fin 2) : GProc (Fin 2) (Fin 2) where
  sent _ w := if w = 1 then [i] else []
  sent_snoc _ _ _ := List.prefix_refl _
  out _ := some (some i)

/-- The receiver: outputs the first message it receives. -/
def k2Receiver : GProc (Fin 2) (Fin 2) where
  sent _ _ := []
  sent_snoc _ _ _ := List.nil_prefix
  out h := match h with
    | [] => none
    | e :: _ => some (some e.2)

/-- A fair leader election protocol on `K₂`: processor `0` draws the leader uniformly, sends it to
`1` and outputs it; processor `1` outputs what it receives. -/
def k2FLE : Protocol (Fin 2) (Fin 2) (fun _ => Fin 2) :=
  ⟨fun v i => if v = 0 then k2Sender i else k2Receiver⟩

theorem k2FLE_run (ω : Fin 2 → Fin 2) (σ : ℕ → Fin 2 × Fin 2) (t : ℕ) :
    grun K2 (k2FLE.profile ω) σ t 0 = [] ∧
      (grun K2 (k2FLE.profile ω) σ t 1 = [] ∨ grun K2 (k2FLE.profile ω) σ t 1 = [(0, ω 0)]) := by
  induction t with
  | zero => simp [grun]
  | succ t ih =>
    obtain ⟨h0, h1⟩ := ih
    simp only [grun]
    set c := grun K2 (k2FLE.profile ω) σ t
    obtain ⟨a, b⟩ := σ t
    unfold gdeliver pending received
    fin_cases b
    · simp [k2FLE, Protocol.profile, k2Sender, h0, h1]
    · rcases h1 with h1 | h1
      · fin_cases a
        · simp [k2FLE, Protocol.profile, k2Sender, k2Receiver, h0, h1, Function.update]
        · simp [h0, h1]
      · simp [k2FLE, Protocol.profile, k2Receiver, h0, h1]

theorem k2FLE_outcome (ω : Fin 2 → Fin 2) {σ : ℕ → Fin 2 × Fin 2} (hσ : GFair K2 σ) :
    goutcome K2 (k2FLE.profile ω) σ = some (ω 0) := by
  rw [goutcome_eq_some_iff]
  intro v
  fin_cases v
  · exact ⟨0, by simp [grun, k2FLE, Protocol.profile, k2Sender]⟩
  · obtain ⟨t, -, ht⟩ := hσ 0 1 (by simp) 0
    rcases (k2FLE_run ω σ t).2 with h | h
    · refine ⟨t + 1, ?_⟩
      have h0 := (k2FLE_run ω σ t).1
      simp only [grun, ht, gdeliver, pending, received, h, h0]
      simp [k2FLE, Protocol.profile, k2Sender, k2Receiver]
    · refine ⟨t, ?_⟩
      show (k2FLE.profile ω 1).out (grun K2 (k2FLE.profile ω) σ t 1) = _
      rw [h]; rfl

theorem k2FLE_isFLE : IsFLE K2 k2FLE := by
  intro σ hσ j
  unfold prob
  simp only [k2FLE_outcome _ hσ, Option.some.injEq]
  have : (Finset.univ.filter fun x : Fin 2 → Fin 2 => x 0 = j).card = 2 := by
    rw [Finset.filter_congr_decidable]
    fin_cases j <;> rfl
  rw [this]; simp; norm_num

/-- **Theorem 7.2 of [YM18] is false at `ε = 1/n`.** `K₂` is a `1`-simulated tree, `k2FLE` is an
FLE protocol on it, and it is `1/n`-`1`-resilient (`n = 2`): by `isResilient_one_sub` every FLE
protocol is `(1 - 1/n)`-`k`-resilient. -/
theorem thm_7_2_boundary_false :
    IsKSimTree K2 1 ∧ IsFLE K2 k2FLE ∧
      IsResilient K2 k2FLE (1 / Fintype.card (Fin 2)) 1 := by
  refine ⟨K2_isKSimTree, k2FLE_isFLE, ?_⟩
  have := isResilient_one_sub K2 k2FLE_isFLE (k := 1) le_rfl
  convert this using 2
  norm_num

end Podc.FairLeaderElection.Trees
