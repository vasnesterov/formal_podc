import Papers.PODC2026.ForgetIT.Invariant

/-!
# Agreement of Forget-IT (Theorem 2, safety part)

The proof follows the paper's sketch (Section 4.2.1, "Agreement"), made precise as an invariant.

Fix a view `V₀ ≥ 1`, a value `v₀`, and a set `L` of at least `f + 1` correct processes, each of
which, if it broadcasts a `vote-2` message for `V₀` at all, broadcasts one with lock `v₀`
(`Hyp`). This is the situation after a decision of `v₀` in `V₀`. Then (`Concl`):

* every correct process guards `v₀` (or nothing) in every view `> V₀`;
* every echo slot of a correct process for a view `≥ V₀` holds `v₀`, and no second (`SAFE`)
  echo is ever sent for such a view;
* every `vote-1` of a correct process in a view `> V₀` is for `v₀`;
* every `vote-2` of a correct process in a view `> V₀` carries guard `v₀`.

The base case is the observation that every quorum of accepted `vote-2` messages for `V₀`
contains a member of `L` (`base`): hence `decision_alert[V₀]` can never become `false` and
`potential_decision[V₀]` can only be `v₀`. Note that `Hyp` is "anti-monotone" in time (it only
gets harder as more messages are sent), so `Hyp` in the final state gives `Hyp` in all earlier
states, and `Concl` is proved by induction along the execution (`concl_reach`).

Remark on the paper's sketch: it states that a decision implies that "at least `2f + 1` correct
processes broadcast" the deciding `vote-2`; only `f + 1` correct ones are guaranteed, which
suffices (`|S| + |L| = 2f + 1 + f + 1 > n`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ForgetIT

open Finset

variable {P Val : Type} [Fintype P] [DecidableEq P] [DecidableEq Val]
variable {prm : Params P} {F : Finset P}

/-- `L` is a set of at least `f + 1` correct processes whose `vote-2` messages for `V₀` (if
any) lock `v₀`. -/
def Hyp (F : Finset P) (f : ℕ) (g : GS P Val) (L : Finset P) (V₀ : ℕ) (v₀ : Val) : Prop :=
  (∀ r ∈ L, r ∉ F) ∧ f + 1 ≤ L.card ∧
    ∀ r ∈ L, ∀ l gd, (r, .vote2 V₀ l gd) ∈ g.sent → l = some v₀

/-- The consequences of `Hyp` (see the module docstring). -/
structure Concl (F : Finset P) (g : GS P Val) (V₀ : ℕ) (v₀ : Val) : Prop where
  guard : ∀ p ∉ F, ∀ V, V₀ < V → (g.loc p).guard V = none ∨ (g.loc p).guard V = some (.val v₀)
  echo : ∀ p ∉ F, ∀ k V x, V₀ ≤ V → (g.loc p).echo k V = some x → x = .val v₀
  echoS : ∀ p ∉ F, ∀ k V, V₀ ≤ V → (g.loc p).echoS k V = false
  vote1 : ∀ p ∉ F, ∀ V x, V₀ < V → (g.loc p).vote1 V = some x → x = v₀
  vote2 : ∀ p ∉ F, ∀ V l gd, V₀ < V → (g.loc p).vote2 V = some (l, gd) → gd = some (.val v₀)

section lemmas

variable {g : GS P Val} {L : Finset P} {V₀ : ℕ} {v₀ : Val}

/-- Correct echo messages for views `≥ V₀` carry `v₀`. -/
lemma Concl.echo_sent (hc : Concl F g V₀ v₀) (hg : Inv prm F g) {r : P} (hr : r ∉ F) {k : Fin 3}
    {V : ℕ} {x : GV Val} (hV : V₀ ≤ V) (h : (r, .echo k V x) ∈ g.sent) : x = .val v₀ := by
  rcases hg.refl r hr _ h with h' | ⟨rfl, h'⟩
  · exact hc.echo r hr k V x hV h'
  · rw [hc.echoS r hr k V hV] at h'; exact absurd h' (by simp)

/-- Correct `vote-1` messages for views `> V₀` are for `v₀`. -/
lemma Concl.vote1_sent (hc : Concl F g V₀ v₀) (hg : Inv prm F g) {r : P} (hr : r ∉ F) {V : ℕ}
    {x : Val} (hV : V₀ < V) (h : (r, .vote1 V x) ∈ g.sent) : x = v₀ :=
  hc.vote1 r hr V x hV (hg.refl r hr _ h)

/-- Correct `vote-2` messages for views `> V₀` carry guard `v₀`. -/
lemma Concl.vote2_sent (hc : Concl F g V₀ v₀) (hg : Inv prm F g) {r : P} (hr : r ∉ F) {V : ℕ}
    {l : Option Val} {gd : Option (GV Val)} (hV : V₀ < V) (h : (r, .vote2 V l gd) ∈ g.sent) :
    gd = some (.val v₀) :=
  hc.vote2 r hr V l gd hV (hg.refl r hr _ h)

/-- A certificate with threshold `≥ f + 1` for a view `≥ V₀` is for `v₀`. -/
lemma cert_val (hF : F.card ≤ prm.f) (hc : Concl F g V₀ v₀) (hg : Inv prm F g) {p : P}
    (hp : p ∉ F) {k : Fin 3} {th V : ℕ} {x : GV Val} (hth : prm.f + 1 ≤ th) (hV : V₀ ≤ V)
    (h : cert (g.loc p) k th V x) : x = .val v₀ := by
  obtain ⟨r, hr, m, hm, hb⟩ := exists_correct_of_snd hF hth h
  obtain ⟨y, rfl, hy⟩ := isEcho_eq hb
  have := hc.echo_sent hg hr hV (hg.rcv p hp r _ hm hr)
  subst this
  rcases hy with hy | hy
  · exact hy.symm
  · exact absurd hy (by simp)

/-- **Base case**: every quorum of `vote-2` messages for `V₀` meets `L`. -/
lemma base (hn : Fintype.card P = 3 * prm.f + 1) (hg : Inv prm F g)
    (hH : Hyp F prm.f g L V₀ v₀) {p : P} (hp : p ∉ F) :
    (∀ ℓ, (g.loc p).pot V₀ = some ℓ → ℓ = v₀) ∧ (g.loc p).alert V₀ ≠ some false := by
  have meet : ∀ S : Finset P, 2 * prm.f + 1 ≤ S.card → ∃ r ∈ S, r ∈ L := by
    intro S hS
    have := hH.2.1
    obtain ⟨r, hr⟩ := Finset.inter_nonempty_of_card_univ_lt_card_add_card (s := S) (t := L)
      (by omega)
    exact ⟨r, (Finset.mem_inter.1 hr).1, (Finset.mem_inter.1 hr).2⟩
  have hpot : ∀ ℓ, (g.loc p).pot V₀ = some ℓ → ℓ = v₀ := by
    intro ℓ h
    obtain ⟨S, hS, hm⟩ := hg.potW p hp V₀ ℓ h
    obtain ⟨r, hrS, hrL⟩ := meet S hS
    obtain ⟨l, gd, h1, h2⟩ := hm r hrS (hH.1 r hrL)
    have := hH.2.2 r hrL l gd h1
    subst this
    rcases h2 with h2 | h2
    · simp at h2
    · exact (Option.some_injective _ h2).symm
  refine ⟨hpot, fun h => ?_⟩
  obtain ⟨S, hS, hm⟩ := hg.falseW p hp V₀ h
  obtain ⟨r, hrS, hrL⟩ := meet S hS
  obtain ⟨l, gd, h1, h2⟩ := hm r hrS (hH.1 r hrL)
  have := hH.2.2 r hrL l gd h1
  subst this
  rcases h2 with h2 | ⟨ℓ, hℓ, h2⟩
  · simp at h2
  · exact h2 (by rw [hpot ℓ hℓ])

/-- The value with which a correct process invokes `send_echo_*` for a view `≥ V₀` is `v₀`. -/
lemma src_val (hn : Fintype.card P = 3 * prm.f + 1) (hF : F.card ≤ prm.f) (hg : Inv prm F g)
    (hc : Concl F g V₀ v₀) (hH : Hyp F prm.f g L V₀ v₀) {p : P} (hp : p ∉ F) {a : Act P Val}
    (hen : En prm p a (g.loc p)) {k : Fin 3} {W : ℕ} {x : GV Val} (hsrc : EchoSrc a k W x)
    (hW : V₀ ≤ W) : x = .val v₀ := by
  obtain ⟨hpot, hal⟩ := base hn hg hH hp
  cases a <;> simp only [EchoSrc] at hsrc
  case echoLock V q y =>
    obtain ⟨-, rfl, rfl⟩ := hsrc
    obtain ⟨-, hl, hpa, -⟩ := hen
    rcases Nat.eq_or_lt_of_le hW with rfl | hlt
    · rcases hpa with h | h
      · rw [hpot y h]
      · exact absurd h hal
    · obtain ⟨r, hr, h⟩ := hg.accLock p hp _ q y hl
      rw [hc.vote1_sent hg hr hlt h]
  case echoGuard V G =>
    obtain ⟨-, rfl, rfl⟩ := hsrc
    obtain ⟨-, hcard, hfalse, -⟩ := hen
    rcases Nat.eq_or_lt_of_le hW with rfl | hlt
    · exact absurd hfalse hal
    · obtain ⟨r, hrG, hr⟩ :=
        Finset.exists_mem_notMem_of_card_le_of_lt (s := accG (g.loc p) W x) hF (by omega)
      simp only [accG, Finset.mem_filter, Finset.mem_univ, true_and] at hrG
      rcases he : (g.loc p).acc W r with _ | ⟨l, gd⟩
      · simp [he, guardOf] at hrG
      · simp only [he, guardOf, Option.bind_some] at hrG
        subst hrG
        have := hc.vote2_sent hg hr hlt (hg.acc p hp W r l _ he hr)
        exact (Option.some_injective _ this)
  case echoDiv V =>
    obtain ⟨-, rfl, rfl⟩ := hsrc
    obtain ⟨-, hfalse, hdiv, -⟩ := hen
    rcases Nat.eq_or_lt_of_le hW with rfl | hlt
    · exact absurd hfalse hal
    · exfalso
      have h1 := hdiv (.val v₀)
      have h2 : accAll (g.loc p) W ⊆ accG (g.loc p) W (.val v₀) ∪ F := by
        intro r hr
        by_cases hrF : r ∈ F
        · exact Finset.mem_union_right _ hrF
        · apply Finset.mem_union_left
          simp only [accAll, Finset.mem_filter, Finset.mem_univ, true_and] at hr
          obtain ⟨⟨l, gd⟩, he⟩ := Option.ne_none_iff_exists'.1 hr
          have := hc.vote2_sent hg hrF hlt (hg.acc p hp W r l gd he hrF)
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [guardOf, he, this]⟩
      have h3 := (Finset.card_le_card h2).trans (Finset.card_union_le _ _)
      omega
  case echo2 V y =>
    obtain ⟨-, rfl, rfl⟩ := hsrc
    exact cert_val hF hc hg hp (by omega) hW hen.2
  case echo3 V y =>
    obtain ⟨-, rfl, rfl⟩ := hsrc
    exact cert_val hF hc hg hp (by omega) hW hen.2

end lemmas

lemma concl_setLoc {g : GS P Val} {V₀ : ℕ} {v₀ : Val} (hc : Concl F g V₀ v₀) {p : P}
    {s' : LS P Val} (h1 : s'.guard = (g.loc p).guard) (h2 : s'.echo = (g.loc p).echo)
    (h3 : s'.echoS = (g.loc p).echoS) (h4 : s'.vote1 = (g.loc p).vote1)
    (h5 : s'.vote2 = (g.loc p).vote2) : Concl F (g.setLoc p s') V₀ v₀ := by
  have hl : ∀ q, (g.setLoc p s').loc q = if q = p then s' else g.loc q := fun q => setLoc_loc
  constructor <;> intro q hq <;> rw [hl] <;> split <;> subst_vars
  all_goals first
    | (rw [h1]; exact hc.guard _ hq) | (rw [h2]; exact hc.echo _ hq)
    | (rw [h3]; exact hc.echoS _ hq) | (rw [h4]; exact hc.vote1 _ hq)
    | (rw [h5]; exact hc.vote2 _ hq)
    | exact hc.guard _ hq | exact hc.echo _ hq | exact hc.echoS _ hq | exact hc.vote1 _ hq
    | exact hc.vote2 _ hq

/-- `Concl` is preserved by every step, given `Hyp` after the step. -/
theorem concl_step (hn : Fintype.card P = 3 * prm.f + 1) (hF : F.card ≤ prm.f)
    {g g' : GS P Val} {L : Finset P} {V₀ : ℕ} {v₀ : Val} (hg : Inv prm F g)
    (hc : Concl F g V₀ v₀) (hH : Hyp F prm.f g' L V₀ v₀) (hs : Step prm F g g') :
    Concl F g' V₀ v₀ := by
  cases hs with
  | vol p hp rcv acc => exact concl_setLoc hc rfl rfl rfl rfl rfl
  | aux p hp clk entered active out => exact concl_setLoc hc rfl rfl rfl rfl rfl
  | act p a hp hen =>
    have hH0 : Hyp F prm.f g L V₀ v₀ :=
      ⟨hH.1, hH.2.1, fun r hr l gd h => hH.2.2 r hr l gd (sent_sub_act h)⟩
    have hg' : Inv prm F (g.act prm p a) := inv_act hF hg hp hen
    set s := g.loc p with hsdef
    have srcv := fun {k W x} (h1 : EchoSrc a k W x) (h2 : V₀ ≤ W) =>
      src_val hn hF hg hc hH0 hp hen h1 h2
    -- guards
    have hguard : ∀ V, V₀ < V → (exec prm p a s).1.guard V = none ∨
        (exec prm p a s).1.guard V = some (.val v₀) := by
      intro V hV
      rcases exec_guard prm p s a hen V with h | ⟨x, rfl, rfl, h⟩ | ⟨-, -, k, W', y, h, hcert, hle⟩
      · rw [h]; exact hc.guard p hp V hV
      · exfalso
        obtain ⟨hcert, h1, h2⟩ := hen
        have hx := cert_val hF hc hg hp le_rfl (by omega) hcert
        subst hx
        rcases hc.guard p hp _ hV with h3 | h3
        · exact hg.guardV p hp h3
        · exact h2 h3
      · rw [h, cert_val hF hc hg hp le_rfl (by omega) hcert]; simp
    constructor
    · intro q hq V hV
      by_cases hqp : q = p
      · subst hqp; rw [act_loc_self]; exact hguard V hV
      · rw [act_loc_ne hqp]; exact hc.guard q hq V hV
    · intro q hq k V x hV h
      by_cases hqp : q = p
      · subst hqp
        rw [act_loc_self] at h
        rcases exec_echo prm q s a k V with h' | ⟨-, y, h', hsrc⟩
        · rw [h'] at h; exact hc.echo q hq k V x hV h
        · rw [h'] at h; cases h; exact srcv hsrc hV
      · rw [act_loc_ne hqp] at h; exact hc.echo q hq k V x hV h
    · intro q hq k V hV
      by_cases hqp : q = p
      · subst hqp
        rw [act_loc_self]
        by_contra hne
        rcases exec_echoS prm q s a k V (by simpa using hne) with h | ⟨x, y, hsrc, hy, -, hys, hxy⟩
        · rw [hc.echoS q hq k V hV] at h; exact absurd h (by simp)
        · have hx := srcv hsrc hV
          have hy' := hc.echo q hq k V y hV hy
          subst hx hy'
          rcases hxy with h | h <;> simp at h
      · rw [act_loc_ne hqp]; exact hc.echoS q hq k V hV
    · intro q hq V x hV h
      by_cases hqp : q = p
      · subst hqp
        rw [act_loc_self] at h
        rcases exec_vote1 prm q s a V with h' | ⟨w, rfl, rfl, h'⟩
        · rw [h'] at h; exact hc.vote1 q hq V x hV h
        · rw [h'] at h; cases h
          obtain ⟨-, hgd, -, -⟩ := hen
          rcases hc.guard q hq _ hV with h3 | h3 <;> rw [h3] at hgd <;> simp at hgd
          exact hgd.symm
      · rw [act_loc_ne hqp] at h; exact hc.vote1 q hq V x hV h
    · intro q hq V l gd hV h
      by_cases hqp : q = p
      · subst hqp
        rw [act_loc_self] at h
        rcases exec_vote2 prm q s a hen V with h' | ⟨-, l', gd', h1, -, h2⟩
        · rw [h'] at h; exact hc.vote2 q hq V l gd hV h
        · rw [h1] at h; cases h
          rcases h2 with ⟨rfl, rfl⟩ | ⟨hle, rfl⟩ | ⟨y, rfl, hcert⟩
          · rcases hc.guard q hq _ hV with h3 | h3
            · exact absurd h3 (hg.guardV q hq)
            · exact h3
          · have hv := hg'.guardV q hq
            rw [act_loc_self] at hv
            rcases hguard (exec prm q a s).1.view (by omega) with h3 | h3
            · exact absurd h3 hv
            · exact h3
          · rw [cert_val hF hc hg hq le_rfl hV.le hcert]
      · rw [act_loc_ne hqp] at h; exact hc.vote2 q hq V l gd hV h

theorem concl_init {inp : P → Val} {V₀ : ℕ} {v₀ : Val} (h1 : 1 ≤ V₀) :
    Concl F (initGS prm F inp) V₀ v₀ := by
  have hl : ∀ q, (initGS prm F inp).loc q =
      { (enterV prm q 1 (startLS (inp q))).1 with out := (enterV prm q 1 (startLS (inp q))).2 } :=
    fun _ => rfl
  constructor <;> simp only [hl]
  · intro q _ V hV; left; simp [startLS, Function.update_apply]; omega
  · intro q _ k V x _ h; simp [startLS] at h
  · intro q _ k V _; simp [startLS]
  · intro q _ V x _ h; simp [startLS] at h
  · intro q _ V l gd hV h
    rcases enterV_vote2 prm q 1 (startLS (inp q)) V with h' | ⟨-, h2, -⟩
    · rw [h'] at h; simp [startLS] at h
    · omega

/-- `Hyp` in a reachable state implies `Concl` there. -/
theorem concl_reach (hn : Fintype.card P = 3 * prm.f + 1) (hF : F.card ≤ prm.f) {inp : P → Val}
    {g : GS P Val} (hr : Reach prm F inp g) {L : Finset P} {V₀ : ℕ} {v₀ : Val} (h1 : 1 ≤ V₀) :
    Hyp F prm.f g L V₀ v₀ → Concl F g V₀ v₀ := by
  induction hr with
  | refl => intro _; exact concl_init h1
  | @tail b c hab hbc ih =>
    intro hH
    have hsub : b.sent ⊆ c.sent := by
      cases hbc with
      | act p a hp hen => exact fun e he => sent_sub_act he
      | vol => exact fun e he => he
      | aux => exact fun e he => he
    have hH' : Hyp F prm.f b L V₀ v₀ :=
      ⟨hH.1, hH.2.1, fun r hr l gd h => hH.2.2 r hr l gd (hsub h)⟩
    exact concl_step hn hF (reach_inv hF hab) (ih hH') hH hbc

/-- **Agreement** (Theorem 2 of the paper, agreement part): in every reachable state of the
asynchronous system (no timing assumptions, crash–recovery of correct processes, lossy network),
all decisions of correct processes are on the same value. Assumes `n = 3f + 1` and at most `f`
Byzantine processes. -/
theorem agreement (hn : Fintype.card P = 3 * prm.f + 1) (hF : F.card ≤ prm.f) {inp : P → Val}
    {g : GS P Val} (hreach : Reach prm F inp g) {p p' : P} {V V' : ℕ} {v v' : Val}
    (hd : (p, V, v) ∈ g.dec) (hd' : (p', V', v') ∈ g.dec) : v = v' := by
  have hg := reach_inv hF hreach
  -- correct processes behind a decision
  have lockers : ∀ {q W w}, (q, W, w) ∈ g.dec → 1 ≤ W ∧ ∃ L : Finset P, (∀ r ∈ L, r ∉ F) ∧
      prm.f + 1 ≤ L.card ∧ ∀ r ∈ L, ∃ gd, (r, .vote2 W (some w) gd) ∈ g.sent := by
    intro q W w h
    obtain ⟨-, h1, S, hS, hm⟩ := hg.dec _ h
    refine ⟨h1, S \ F, fun r hr => (Finset.mem_sdiff.1 hr).2, ?_, fun r hr => ?_⟩
    · have := Finset.le_card_sdiff F S; omega
    · obtain ⟨hrS, hrF⟩ := Finset.mem_sdiff.1 hr
      exact hm r hrS hrF
  -- lock quorums of the lockers
  have lockQ : ∀ {r W w gd}, r ∉ F → (r, .vote2 W (some w) gd) ∈ g.sent → Q1 prm F g W w :=
    fun hr h => hg.vote2Q _ hr _ _ _ (hg.refl _ hr _ h)
  -- two `vote-1` quorums of the same view agree
  have same : ∀ {W w w'}, Q1 prm F g W w → Q1 prm F g W w' → w = w' := by
    intro W w w' ⟨S, hS, hm⟩ ⟨S', hS', hm'⟩
    obtain ⟨r, hr, hr', hrF⟩ := Finset.exists_mem_inter_notMem_of_card_le (s := S) (t := S') hF
      (by omega)
    have h1 := hg.refl r hrF _ (hm r hr hrF)
    have h2 := hg.refl r hrF _ (hm' r hr' hrF)
    simp only [Refl] at h1 h2
    rw [h1] at h2; exact Option.some_injective _ h2
  -- the decision with the smaller view constrains the other one
  have key : ∀ {q q' W W' w w'}, (q, W, w) ∈ g.dec → (q', W', w') ∈ g.dec → W ≤ W' → w = w' := by
    intro q q' W W' w w' h h' hle
    obtain ⟨h1, L, hLF, hL, hLm⟩ := lockers h
    obtain ⟨-, L', hLF', hL', hLm'⟩ := lockers h'
    obtain ⟨r, hrL⟩ := Finset.card_pos.1 (by omega : 0 < L.card)
    obtain ⟨gd, hr⟩ := hLm r hrL
    obtain ⟨r', hrL'⟩ := Finset.card_pos.1 (by omega : 0 < L'.card)
    obtain ⟨gd', hr'⟩ := hLm' r' hrL'
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact same (lockQ (hLF r hrL) hr) (lockQ (hLF' r' hrL') hr')
    · have hH : Hyp F prm.f g L W w := by
        refine ⟨hLF, hL, fun r hr l gd h => ?_⟩
        obtain ⟨gd'', h''⟩ := hLm r hr
        have e1 := hg.refl r (hLF r hr) _ h
        have e2 := hg.refl r (hLF r hr) _ h''
        simp only [Refl] at e1 e2
        rw [e1] at e2; cases e2; rfl
      have hc := concl_reach hn hF hreach h1 hH
      obtain ⟨S, hS, hm⟩ := lockQ (hLF' r' hrL') hr'
      obtain ⟨t, htS, htF⟩ := Finset.exists_mem_notMem_of_card_le_of_lt (s := S) hF (by omega)
      exact (hc.vote1_sent hg htF hlt (hm t htS htF)).symm
  rcases le_total V V' with h | h
  · exact key hd hd' h
  · exact (key hd' hd h).symm

end Podc.ForgetIT
