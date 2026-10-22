import Papers.PODC2013.SpeculativeStabilization.Theorem2

/-!
# Section 5: the synchronous lower bound `⌈diam(g)/2⌉`

* `lemma_5`: under the synchronous daemon, the state of `v` after `k` steps only depends on the
  initial states in the ball of radius `k` around `v` (for protocols given by local rules).
* `theorem_4`: if the predicate `privileged_v` depends only on the ball of radius `r` around `v`,
  every protocol whose synchronous executions satisfy mutual exclusion from time `T` on has
  `⌈D/2⌉ ≤ T + r`. For `r = 0` (privileged determined by the state of `v`, as in SSME) this is the
  paper's Theorem 4: `conv_time(π, sd) ≥ ⌈D/2⌉`.
* `conv_time_ssme`: hence `conv_time(SSME, sd) = ⌈D/2⌉` exactly.
* `theorem_4_false`: the paper's specification lets `privileged_v` depend on the states of the
  neighbours of `v` (`r = 1`); then Theorem 4 is false: on every complete graph `K_n` (`D = 1`,
  `n ≥ 2`) a token-passing protocol (`RoundRobin`) satisfies mutual exclusion from time `0` on,
  under the synchronous and even the unfair daemon; and on every star `K_{1,n-1}` (`D = 2`,
  `n ≥ 3`) a pointer protocol (`theorem_4_false_star`) does the same under the synchronous daemon.
  In general (`theorem_4_false_centre`, `theorem_4_false_of_radius`), a clock broadcast from a centre
  along a BFS tree achieves `⌈D/2⌉ - 1` on every graph of radius `⌈D/2⌉` (e.g. every tree).
  `theorem_4_radius` with `r = 1` gives the correct bound `⌈D/2⌉ - 1`, tight on those graphs.
-/

namespace Podc.SpeculativeStabilization

open Cslib.SelfStabilization Cslib.SelfStabilization.ResetUnison

variable {V Q : Type*} (G : SimpleGraph V)

/-- The next state of `v` depends only on the states of `v` and of its neighbours (guarded rules
reading the neighbours' variables). -/
def IsLocalRule (next : (V → Q) → V → Q) : Prop :=
  ∀ γ γ' v, (∀ u, (u = v ∨ G.Adj v u) → γ u = γ' u) → next γ v = next γ' v

/-- `priv v γ` depends only on the states in the ball of radius `r` around `v`. -/
def PrivLocal (r : ℕ) (priv : V → (V → Q) → Prop) : Prop :=
  ∀ v γ γ', (∀ u, G.dist v u ≤ r → γ u = γ' u) → (priv v γ ↔ priv v γ')

variable {G}

/-- **Lemma 5** (locality of synchronous executions). Configurations agreeing on the ball of
radius `r + k` around `v` lead, after `k` synchronous steps, to configurations agreeing on the
ball of radius `r`. -/
theorem lemma_5 (hconn : G.Connected) {next : (V → Q) → V → Q} (hloc : IsLocalRule G next) :
    ∀ k (γ γ' : V → Q) v r, (∀ u, G.dist v u ≤ r + k → γ u = γ' u) →
      ∀ u, G.dist v u ≤ r → next^[k] γ u = next^[k] γ' u := by
  intro k
  induction k with
  | zero => intro γ γ' v r h u hu; exact h u (by simpa using hu)
  | succ k ih =>
    intro γ γ' v r h u hu
    simp only [Function.iterate_succ_apply]
    refine ih (next γ) (next γ') v r (fun w hw => hloc γ γ' w fun x hx => h x ?_) u hu
    rcases hx with rfl | hx
    · omega
    · have := hconn.dist_triangle (u := v) (v := w) (w := x)
      rw [SimpleGraph.dist_eq_one_iff_adj.2 hx] at this
      omega

/-- **Theorem 4** (generalized to `privileged` predicates reading a ball of radius `r`): if all
synchronous executions (from all configurations of a product domain) satisfy mutual exclusion from
time `T` on, then `⌈D/2⌉ ≤ T + r`. -/
theorem theorem_4_radius [Nonempty V] [Finite V] (hconn : G.Connected) {next : (V → Q) → V → Q}
    (hloc : IsLocalRule G next) {dom : Q → Prop} (hdom : ∃ q, dom q)
    (hnext : ∀ γ : V → Q, (∀ w, dom (γ w)) → ∀ w, dom (next γ w)) {r : ℕ}
    {priv : V → (V → Q) → Prop} (hpriv : PrivLocal G r priv) {T : ℕ}
    (hT : PseudoStabilizingWithin (syncExecs next fun γ => ∀ v, dom (γ v))
      (MutualExclusion priv) T) : (G.diam + 1) / 2 ≤ T + r := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨q, hq⟩ := hdom
  -- synchronous executions as elements of the class
  let ex : (V → Q) → ℕ → (V → Q) × Set V := fun γ t =>
    (next^[t] γ, syncSet (next := next) (fun s => next^[s] γ) t)
  have hex : ∀ γ, (∀ w, dom (γ w)) → ex γ ∈ syncExecs next fun γ => ∀ v, dom (γ v) :=
    fun γ hγ => ⟨isSyncExec_iterate γ, fun _ => rfl, hγ⟩
  let γ0 : V → Q := fun _ => q
  obtain ⟨-, hlive⟩ := hT _ (hex γ0 fun _ => hq)
  obtain ⟨tu, -, hpu, -⟩ := hlive u 0
  obtain ⟨tv, -, hpv, -⟩ := hlive v 0
  simp only [ex] at hpu hpv
  -- the spliced configuration
  let γ' : V → Q := fun w => if G.dist u w ≤ T + r then next^[tu] γ0 w else next^[tv] γ0 w
  have hγ' : ∀ w, dom (γ' w) := by
    have hd : ∀ t w, dom (next^[t] γ0 w) := by
      intro t
      induction t with
      | zero => exact fun _ => hq
      | succ t ih => intro w; rw [Function.iterate_succ_apply']; exact hnext _ ih w
    intro w; simp only [γ']; split_ifs <;> exact hd _ _
  obtain ⟨hsafe, -⟩ := hT _ (hex γ' hγ')
  have h1 : priv u (next^[T] γ') := by
    rw [hpriv u (next^[T] γ') (next^[T + tu] γ0) ?_]
    · exact (by assumption)
    · rw [Function.iterate_add_apply]
      refine lemma_5 hconn hloc T _ _ u r (fun w hw => ?_)
      simp only [γ']; rw [ite_eq_left (by omega)]
  have h2 : priv v (next^[T] γ') := by
    rw [hpriv v (next^[T] γ') (next^[T + tv] γ0) ?_]
    · exact (by assumption)
    · rw [Function.iterate_add_apply]
      refine lemma_5 hconn hloc T _ _ v r (fun w hw => ?_)
      simp only [γ']
      rw [ite_eq_right]
      intro hw'
      have := hconn.dist_triangle (u := u) (v := w) (w := v)
      rw [SimpleGraph.dist_comm (u := w)] at this
      omega
  have := hsafe 0 u v (by simpa [ex] using h1) (by simpa [ex] using h2)
  subst this
  simp at huv
  omega

/-- **Theorem 4** (for `privileged_v` determined by the state of `v`, as in SSME): any protocol
whose synchronous executions satisfy mutual exclusion from time `T` on has `T ≥ ⌈D/2⌉`. -/
theorem theorem_4 [Nonempty V] [Finite V] (hconn : G.Connected) {next : (V → Q) → V → Q}
    (hloc : IsLocalRule G next) {dom : Q → Prop} (hdom : ∃ q, dom q)
    (hnext : ∀ γ : V → Q, (∀ w, dom (γ w)) → ∀ w, dom (next γ w))
    {priv : V → (V → Q) → Prop} (hown : ∀ v γ γ', γ v = γ' v → (priv v γ ↔ priv v γ')) {T : ℕ}
    (hT : PseudoStabilizingWithin (syncExecs next fun γ => ∀ v, dom (γ v))
      (MutualExclusion priv) T) : (G.diam + 1) / 2 ≤ T := by
  have hp : PrivLocal G 0 priv := fun v γ γ' h => hown v γ γ' (h v (by simp))
  simpa using theorem_4_radius hconn hloc hdom hnext hp hT

/-! ### Optimality of SSME -/

section SSME

variable [Fintype V] [DecidableRel G.Adj]

theorem ssme_local : IsLocalRule G (ssme G) := by
  intro γ γ' v h
  have hv := h v (Or.inl rfl)
  have hn : ∀ u, G.Adj v u → γ u = γ' u := fun u hu => h u (Or.inr hu)
  have e1 : AllCorrect (clockSize G) G γ v ↔ AllCorrect (clockSize G) G γ' v :=
    forall_congr' fun u => imp_congr_right fun hu => by rw [hv, hn u hu]
  have e2 : NormalStep (clockSize G) G γ v ↔ NormalStep (clockSize G) G γ' v :=
    and_congr e1 (forall_congr' fun u => imp_congr_right fun hu => by rw [hv, hn u hu])
  have e3 : ConvergeStep (Fintype.card V) G γ v ↔ ConvergeStep (Fintype.card V) G γ' v := by
    unfold ConvergeStep
    rw [hv]
    exact and_congr Iff.rfl (forall_congr' fun u => imp_congr_right fun hu => by rw [hn u hu])
  have e4 : ResetInit (clockSize G) G γ v ↔ ResetInit (clockSize G) G γ' v := by
    unfold ResetInit; rw [e1, hv]
  unfold ssme next
  by_cases h2 : NormalStep (clockSize G) G γ v
  · rw [ite_eq_left h2, ite_eq_left (e2.1 h2), hv]
  rw [ite_eq_right h2, ite_eq_right (fun h' => h2 (e2.2 h'))]
  by_cases h3 : ConvergeStep (Fintype.card V) G γ v
  · rw [ite_eq_left h3, ite_eq_left (e3.1 h3), hv]
  rw [ite_eq_right h3, ite_eq_right (fun h' => h3 (e3.2 h'))]
  by_cases h4 : ResetInit (clockSize G) G γ v
  · rw [ite_eq_left h4, ite_eq_left (e4.1 h4)]
  rw [ite_eq_right h4, ite_eq_right (fun h' => h4 (e4.2 h')), hv]

/-- **Optimality of SSME** (Theorem 2 + Theorem 4): `conv_time(SSME, sd) = ⌈diam(g)/2⌉`: SSME
satisfies mutual exclusion from time `⌈D/2⌉` on in every synchronous execution, and for no
earlier time. -/
theorem conv_time_ssme [Nontrivial V] (hconn : G.Connected) (ident : V → ℕ)
    (hinj : Function.Injective ident) (hid : ∀ v, ident v < Fintype.card V) :
    PseudoStabilizingWithin (syncExecs (ssme G) (SValid G)) (MutualExclusion (Privileged G ident))
        ((G.diam + 1) / 2) ∧
      ∀ T, PseudoStabilizingWithin (syncExecs (ssme G) (SValid G))
        (MutualExclusion (Privileged G ident)) T → (G.diam + 1) / 2 ≤ T := by
  refine ⟨theorem_2 hconn ident hinj hid, fun T hT => ?_⟩
  have hK := three_le_clockSize (G := G)
  refine theorem_4 (dom := fun c => -(Fintype.card V : ℤ) ≤ c ∧ c < clockSize G) hconn ssme_local
    ⟨0, by omega, by omega⟩ (fun γ hγ w => ?_) (fun v γ γ' h => by simp [Privileged, h]) hT
  have := Fintype.card_pos (α := V)
  have hr : IsUnfairRun (ssme G) (fun t => (ssme G)^[t] γ) _ :=
    (isSyncExec_iterate (next := ssme G) γ).isUnfairRun
  have := valid_succ (by omega) hr (t := 0) hγ w
  simpa using this

end SSME

/-! ### Theorem 4 is false when `privileged` reads the neighbours -/

section RoundRobin

variable (n : ℕ)

/-- Token passing on the complete graph `K_n` with registers in `ZMod n`: process `v` is
privileged iff the sum of all registers is `v`, and a privileged process increments its
register (passing the privilege to `v + 1`). `privileged_v` reads the neighbours of `v` (all
processes), as the paper's Specification 1 allows. -/
def rrNext (γ : Fin n → ZMod n) (v : Fin n) : ZMod n :=
  if ∑ u, γ u = ((v : ℕ) : ZMod n) then γ v + 1 else γ v

/-- `privileged_v ≡ (∑ registers = v)`. -/
def rrPriv (v : Fin n) (γ : Fin n → ZMod n) : Prop := ∑ u, γ u = ((v : ℕ) : ZMod n)

variable {n} [Fact (1 < n)]

omit [Fact (1 < n)] in
theorem rr_unique {γ : Fin n → ZMod n} {u v : Fin n} (hu : rrPriv n u γ) (hv : rrPriv n v γ) :
    u = v := by
  unfold rrPriv at hu hv
  rw [hu, ZMod.natCast_eq_natCast_iff'] at hv
  exact Fin.ext (by rwa [Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt v.2] at hv)

theorem rr_enabled_iff {γ : Fin n → ZMod n} {v : Fin n} :
    Enabled (rrNext n) γ v ↔ rrPriv n v γ := by
  unfold Enabled rrNext rrPriv
  split_ifs with h
  · simp [h]
  · simp [h]

/-- In every unfair run of the token-passing protocol, the privileged process is activated at
every step and the sum of the registers grows by one per step. -/
theorem rr_run {e : ℕ → Fin n → ZMod n} {S : ℕ → Set (Fin n)} (h : IsUnfairRun (rrNext n) e S)
    (t : ℕ) : (∀ v, rrPriv n v (e t) → v ∈ S t) ∧ ∑ u, e (t + 1) u = ∑ u, e t u + 1 := by
  have hn : NeZero n := ⟨by have := (Fact.out : 1 < n); omega⟩
  set p : Fin n := ⟨(∑ u, e t u).val, ZMod.val_lt _⟩
  have hp : rrPriv n p (e t) := by simp [rrPriv, p]
  have hS : ∀ v, v ∈ S t → v = p := fun v hv =>
    rr_unique (rr_enabled_iff.1 (h.enabled t v hv)) hp
  have hpS : p ∈ S t := by
    rcases h.progress t with ⟨v, hv⟩ | ht
    · rwa [← hS v hv]
    · exact absurd (ht p) (rr_enabled_iff.2 hp)
  refine ⟨fun v hv => rr_unique hp hv ▸ hpS, ?_⟩
  have hstep : e (t + 1) = Function.update (e t) p (e t p + 1) := by
    funext v
    by_cases hv : v = p
    · subst hv; rw [h.move t _ hpS, Function.update_self]
      unfold rrNext; rw [ite_eq_left (show ∑ u, e t u = ((p : ℕ) : ZMod n) from hp)]
    · rw [h.stay t v (fun hm => hv (hS v hm)), Function.update_of_ne hv]
  rw [hstep, Finset.sum_update_of_mem (Finset.mem_univ _)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), Finset.sdiff_singleton_eq_erase]
  ring

/-- The token-passing protocol satisfies mutual exclusion from time `0` on, in every execution
under the unfair distributed daemon. -/
theorem rr_unfair (ω : ℕ → (Fin n → ZMod n) × Set (Fin n))
    (hω : ω ∈ unfairExecs (rrNext n) fun _ => True) : MutualExclusion (rrPriv n) ω := by
  have hn : NeZero n := ⟨by have := (Fact.out : 1 < n); omega⟩
  obtain ⟨h, -⟩ := hω
  refine ⟨fun t u v hu hv => rr_unique hu hv, fun v T => ?_⟩
  have hsum : ∀ k, ∑ u, (ω (T + k)).1 u = ∑ u, (ω T).1 u + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [← add_assoc, (rr_run h (T + k)).2, ih]; push_cast; ring
  set k : ℕ := (((v : ℕ) : ZMod n) - ∑ u, (ω T).1 u).val
  have hpv : rrPriv n v (ω (T + k)).1 := by
    simp only [rrPriv, hsum, k, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  exact ⟨T + k, by omega, hpv, (rr_run h (T + k)).1 v hpv⟩

/-- **Theorem 4 is false as stated** (with the paper's `privileged_v` over the variables of `v` and
of its neighbours): on the complete graph `K_n` (`n ≥ 2`, `diam = 1`) the token-passing protocol
is a local protocol that satisfies mutual exclusion from time `0` in all synchronous executions,
while `⌈diam/2⌉ = 1`. -/
theorem theorem_4_false :
    IsLocalRule (⊤ : SimpleGraph (Fin n)) (rrNext n) ∧
      PrivLocal (⊤ : SimpleGraph (Fin n)) 1 (rrPriv n) ∧
      PseudoStabilizingWithin (syncExecs (rrNext n) fun _ => True) (MutualExclusion (rrPriv n)) 0 ∧
      ((⊤ : SimpleGraph (Fin n)).diam + 1) / 2 = 1 := by
  have h1 : 1 < n := Fact.out
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 h1
  refine ⟨fun γ γ' v h => ?_, fun v γ γ' h => ?_, fun ω hω => ?_, by simp⟩
  · have hall : γ = γ' := funext fun u => by
      by_cases huv : u = v
      · exact h u (Or.inl huv)
      · exact h u (Or.inr (Ne.symm huv))
    rw [hall]
  · have hall : γ = γ' := funext fun u => h u (by
      by_cases huv : v = u
      · simp [huv]
      · rw [SimpleGraph.dist_eq_one_iff_adj.2 huv])
    rw [hall]
  · have := rr_unfair ω (syncExecs_subset hω)
    simpa using this

end RoundRobin

/-! ### Also for `diam = 2`: a pointer on the star -/

section Star

variable (n : ℕ) [NeZero n]

/-- The star `K_{1, n-1}` on `Fin n` with centre `0`. -/
def star : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Pointer protocol on the star: the centre holds a pointer that advances at every step; a leaf
toggles its bit when pointed at. `privileged_v ≡ (pointer of the centre = v)` reads the centre,
a neighbour of `v`. -/
def ptrNext (γ : Fin n → Fin n × Bool) (v : Fin n) : Fin n × Bool :=
  if v = 0 then ((γ 0).1 + 1, (γ 0).2)
  else if (γ 0).1 = v then ((γ v).1, !(γ v).2) else γ v

/-- `privileged_v ≡ (pointer of the centre = v)`. -/
def ptrPriv (v : Fin n) (γ : Fin n → Fin n × Bool) : Prop := (γ 0).1 = v

variable {n}

theorem star_adj {a b : Fin n} : (star n).Adj a b ↔ a ≠ b ∧ (a = 0 ∨ b = 0) := Iff.rfl

variable [Fact (2 < n)]

theorem star_diam : (star n).diam = 2 := by
  have h2 : 2 < n := Fact.out
  have hadj0 : ∀ v : Fin n, v ≠ 0 → (star n).Adj 0 v := fun v hv =>
    star_adj.2 ⟨hv.symm, Or.inl rfl⟩
  have hle : (star n).ediam ≤ 2 := by
    rw [SimpleGraph.ediam_le_iff]
    intro u v
    by_cases huv : u = v
    · subst huv; simp
    by_cases hu : u = 0
    · subst hu; rw [SimpleGraph.edist_eq_one_iff_adj.2 (hadj0 v (Ne.symm huv))]; norm_num
    by_cases hv : v = 0
    · subst hv; rw [SimpleGraph.edist_eq_one_iff_adj.2 (hadj0 u hu).symm]; norm_num
    exact (SimpleGraph.edist_le (SimpleGraph.Walk.cons (hadj0 u hu).symm
      (SimpleGraph.Walk.cons (hadj0 v hv) .nil))).trans (by simp)
  set a : Fin n := ⟨1, by omega⟩
  set b : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have ha : a ≠ 0 := by simp [a, Fin.ext_iff]
  have hb : b ≠ 0 := by simp [b, Fin.ext_iff]
  have hge : 2 ≤ (star n).edist a b := by
    have h0 : (star n).edist a b ≠ 0 := by simpa using hab
    have h1 : (star n).edist a b ≠ 1 := by
      rw [Ne, SimpleGraph.edist_eq_one_iff_adj, star_adj]
      rintro ⟨-, h | h⟩
      · exact ha h
      · exact hb h
    have h3 : (star n).edist a b ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.2
      ((hadj0 a ha).symm.reachable.trans (hadj0 b hb).reachable)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h3
    rw [← hk] at h0 h1 ⊢
    norm_cast at h0 h1 ⊢
    omega
  have : (star n).ediam = 2 := le_antisymm hle (hge.trans SimpleGraph.edist_le_ediam)
  rw [SimpleGraph.diam, this]; rfl

open Fin.NatCast in
/-- **Theorem 4 is false as stated, also for `diam = 2`**: on every star with at least two leaves
the pointer protocol is local, `privileged` reads only the neighbours, and mutual exclusion holds
from time `0` in all synchronous executions, while `⌈diam/2⌉ = 1`. -/
theorem theorem_4_false_star :
    IsLocalRule (star n) (ptrNext n) ∧ PrivLocal (star n) 1 (ptrPriv n) ∧
      PseudoStabilizingWithin (syncExecs (ptrNext n) fun _ => True) (MutualExclusion (ptrPriv n)) 0 ∧
      ((star n).diam + 1) / 2 = 1 := by
  have h2 : 2 < n := Fact.out
  have hsucc : ∀ x : Fin n, x + 1 ≠ x := by
    intro x hx
    rw [add_eq_left, Fin.one_eq_zero_iff] at hx
    omega
  refine ⟨fun γ γ' v h => ?_, fun v γ γ' h => ?_, fun ω hω => ?_, by rw [star_diam]⟩
  · have h0 : γ 0 = γ' 0 := by
      by_cases hv : v = 0
      · exact h 0 (Or.inl hv.symm)
      · exact h 0 (Or.inr (star_adj.2 ⟨hv, Or.inr rfl⟩))
    have hv : γ v = γ' v := h v (Or.inl rfl)
    simp only [ptrNext, h0, hv]
  · have h0 : γ 0 = γ' 0 := by
      apply h 0
      by_cases hv : v = 0
      · subst hv; simp
      · rw [SimpleGraph.dist_eq_one_iff_adj.2 (star_adj.2 ⟨hv, Or.inr rfl⟩)]
    simp only [ptrPriv, h0]
  · obtain ⟨h, hS, -⟩ := hω
    have hω0 : (fun t => ω (0 + t)) = ω := funext fun t => by simp
    rw [hω0]
    set e := fun t => (ω t).1
    have hptr : ∀ t, (e (t + 1) 0).1 = (e t 0).1 + 1 := fun t => by
      rw [show e (t + 1) = ptrNext n (e t) from h t]; simp [ptrNext]
    have hen : ∀ t v, (e t 0).1 = v → v ∈ (ω t).2 := by
      intro t v hv
      rw [hS t]
      show ptrNext n (e t) v ≠ e t v
      unfold ptrNext
      by_cases h0 : v = 0
      · rw [ite_eq_left h0]; subst h0; intro heq; exact hsucc _ (congrArg Prod.fst heq)
      · rw [ite_eq_right h0, ite_eq_left hv]; intro heq; have := congrArg Prod.snd heq; simp at this
    refine ⟨fun t u v hu hv => ?_, fun v T => ?_⟩
    · simp only [ptrPriv] at hu hv; rw [← hu, ← hv]
    · have hsum : ∀ k : ℕ, (e (T + k) 0).1 = (e T 0).1 + (k : Fin n) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [← add_assoc, hptr, ih]; push_cast; rw [add_assoc]
      set k : ℕ := (v - (e T 0).1).val
      have hk : (e (T + k) 0).1 = v := by
        rw [hsum, Fin.cast_val_eq_self]; abel
      exact ⟨T + k, by omega, hk, hen _ _ hk⟩

end Star

/-! ### In general: a clock broadcast from a centre

If some vertex `z` has eccentricity `≤ R`, a clock held by `z` and copied outwards along a BFS
tree (`c_v := c_{parent v} + 1`) is synchronised on the ball of radius `R - 1` after `R - 1`
synchronous steps. With `privileged_v ≡ (c_{parent v} = id_v)` (reading a neighbour), mutual
exclusion holds from time `R - 1` on. For graphs whose radius is `⌈diam/2⌉` (every tree, every
complete graph, every star, …) this beats the paper's bound `⌈diam/2⌉` by one, and matches
`theorem_4_radius` with `r = 1`. -/

section Centre

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Every vertex `v ≠ z` has a neighbour one step closer to `z` (a BFS parent). -/
theorem exists_bfsParent (hconn : G.Connected) (z v : V) (hv : v ≠ z) :
    ∃ w, G.Adj v w ∧ G.dist z w + 1 = G.dist z v := by
  obtain ⟨p, -, hp⟩ := hconn.exists_path_of_dist v z
  cases p with
  | nil => exact absurd rfl hv
  | @cons _ w _ h q =>
    refine ⟨w, h, ?_⟩
    have h1 := SimpleGraph.dist_le q
    have h2 := hconn.dist_triangle (u := z) (v := w) (w := v)
    rw [SimpleGraph.dist_comm (u := w) (v := v), SimpleGraph.dist_eq_one_iff_adj.2 h] at h2
    simp only [SimpleGraph.Walk.length_cons] at hp
    rw [SimpleGraph.dist_comm (u := w), SimpleGraph.dist_comm (u := v)] at *
    omega

/-- The clock-broadcast protocol, for a BFS parent function `par` towards the centre `z`. -/
def bcNext (z : V) (par : V → V) (γ : V → ZMod (Fintype.card V)) (v : V) :
    ZMod (Fintype.card V) :=
  if v = z then γ z + 1 else γ (par v) + 1

/-- `privileged_v ≡ (c_{parent v} = id_v)` (`c_z = id_z` for the centre), with identities given
by the bijection `e`. -/
def bcPriv (z : V) (par : V → V) (e : V ≃ Fin (Fintype.card V)) (v : V)
    (γ : V → ZMod (Fintype.card V)) : Prop :=
  γ (if v = z then z else par v) = ((e v : ℕ) : ZMod (Fintype.card V))

theorem bcNext_iterate (hconn : G.Connected) {z : V} {par : V → V}
    (hpar : ∀ v, v ≠ z → G.Adj v (par v) ∧ G.dist z (par v) + 1 = G.dist z v)
    (γ : V → ZMod (Fintype.card V)) :
    ∀ t v, G.dist z v ≤ t → (bcNext z par)^[t] γ v = γ z + t := by
  intro t
  induction t with
  | zero =>
    intro v hv
    have : v = z := ((hconn.dist_eq_zero_iff).1 (by omega)).symm
    subst this; simp
  | succ t ih =>
    intro v hv
    rw [Function.iterate_succ_apply', bcNext]
    split_ifs with hvz
    · rw [ih z (by simp)]; push_cast; ring
    · rw [ih (par v) (by have := (hpar v hvz).2; omega)]; push_cast; ring

/-- **Theorem 4 fails on every graph of radius `⌈diam/2⌉`** (when `privileged_v` may read the
neighbours of `v`): if some vertex `z` is within distance `R` of all vertices, the
clock-broadcast protocol is local, its `privileged` reads only neighbours, and all synchronous
executions satisfy mutual exclusion from time `R - 1` on. -/
theorem theorem_4_false_centre [Nontrivial V] (hconn : G.Connected) (z : V) {R : ℕ}
    (hR : ∀ w, G.dist z w ≤ R) :
    ∃ (next : (V → ZMod (Fintype.card V)) → V → ZMod (Fintype.card V))
      (priv : V → (V → ZMod (Fintype.card V)) → Prop),
      IsLocalRule G next ∧ PrivLocal G 1 priv ∧
        PseudoStabilizingWithin (syncExecs next fun _ => True) (MutualExclusion priv) (R - 1) := by
  classical
  have : Fact (1 < Fintype.card V) := ⟨Fintype.one_lt_card⟩
  have hpar : ∀ v, ∃ w, v ≠ z → G.Adj v w ∧ G.dist z w + 1 = G.dist z v := fun v => by
    by_cases hv : v = z
    · exact ⟨z, fun h => absurd hv h⟩
    · obtain ⟨w, hw⟩ := exists_bfsParent hconn z v hv
      exact ⟨w, fun _ => hw⟩
  choose par hpar using hpar
  let e := Fintype.equivFin V
  refine ⟨bcNext z par, bcPriv z par e, fun γ γ' v h => ?_, fun v γ γ' h => ?_, fun ω hω => ?_⟩
  · unfold bcNext
    split_ifs with hv
    · subst hv; rw [h v (Or.inl rfl)]
    · rw [h (par v) (Or.inr (hpar v hv).1)]
  · unfold bcPriv
    split_ifs with hv
    · rw [h z (by rw [hv]; simp)]
    · rw [h (par v) (by rw [SimpleGraph.dist_eq_one_iff_adj.2 (hpar v hv).1])]
  · obtain ⟨h, hS, -⟩ := hω
    set γ0 := (ω 0).1
    have hit : ∀ t, (ω t).1 = (bcNext z par)^[t] γ0 := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        have ht := h t
        simp only at ht
        rw [ht, ih, Function.iterate_succ_apply']
    have hval : ∀ t v, G.dist z v ≤ t → (ω t).1 v = γ0 z + t := fun t v hv => by
      rw [hit]; exact bcNext_iterate hconn hpar γ0 t v hv
    -- after `R - 1` steps, `privileged_v` reads the common clock value
    have hpriv : ∀ t v, R - 1 ≤ t →
        (bcPriv z par e v (ω t).1 ↔ γ0 z + t = ((e v : ℕ) : ZMod (Fintype.card V))) := by
      intro t v ht
      unfold bcPriv
      split_ifs with hv
      · rw [hval t z (by simp)]
      · rw [hval t (par v) (by have := (hpar v hv).2; have := hR v; omega)]
    have hinj : ∀ a b : V, ((e a : ℕ) : ZMod (Fintype.card V)) = ((e b : ℕ) : ZMod _) → a = b := by
      intro a b hab
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (e a).2, Nat.mod_eq_of_lt (e b).2] at hab
      exact e.injective (Fin.ext hab)
    refine ⟨fun t u v hu hv => ?_, fun v T => ?_⟩
    · rw [hpriv _ _ (by omega)] at hu hv
      exact hinj u v (hu.symm.trans hv)
    · set k : ℕ := (((e v : ℕ) : ZMod (Fintype.card V)) - (γ0 z + ((R - 1 + (T + 1) : ℕ) : ZMod _))).val
      refine ⟨T + 1 + k, by omega, ?_, ?_⟩
      · rw [hpriv _ _ (by omega)]
        simp only [k]
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id', id]
        ring
      · rw [hS]
        set s := R - 1 + (T + 1 + k)
        have ht := h s
        simp only at ht
        show bcNext z par (ω s).1 v ≠ (ω s).1 v
        rw [← ht, hval _ v (by have := hR v; omega), hval _ v (by have := hR v; omega)]
        push_cast
        intro heq
        have : (1 : ZMod (Fintype.card V)) = 0 := by
          linear_combination heq
        exact one_ne_zero this

/-- **Theorem 4 is false on every graph whose radius is `⌈diam/2⌉`** (e.g. every tree), for
`privileged` predicates reading the neighbours: some local protocol has synchronous convergence
time `< ⌈diam/2⌉`. -/
theorem theorem_4_false_of_radius [Nontrivial V] (hconn : G.Connected) (z : V)
    (hz : ∀ w, G.dist z w ≤ (G.diam + 1) / 2) :
    ∃ (next : (V → ZMod (Fintype.card V)) → V → ZMod (Fintype.card V))
      (priv : V → (V → ZMod (Fintype.card V)) → Prop) (T : ℕ),
      IsLocalRule G next ∧ PrivLocal G 1 priv ∧
        PseudoStabilizingWithin (syncExecs next fun _ => True) (MutualExclusion priv) T ∧
        T < (G.diam + 1) / 2 := by
  classical
  obtain ⟨next, priv, h1, h2, h3⟩ := theorem_4_false_centre hconn z hz
  refine ⟨next, priv, _, h1, h2, h3, ?_⟩
  have := one_le_diam hconn (G := G)
  omega

end Centre

end Podc.SpeculativeStabilization
