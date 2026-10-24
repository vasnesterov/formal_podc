import Papers.PODC2021.TrustedHardwareUnidirectional.Echo

/-!
# Correctness of the echo protocol over SRB

The invariant `Inv` of reachable configurations, and from it the four properties of
`RoundSystem.ImplementsUnidirectional`.
-/

namespace Podc.TrustedHW

namespace Echo

open SRBProtocol

variable {P V : Type} [Fintype P] [DecidableEq P] {f : ℕ}

local notation "E" => echoProtocol P V f

local notation "Cfg" => SRBConfig P (Msg P V) (State P V)

/-- The step of the echo protocol, in two cases. -/
lemma step_cases (p : P) (cl : Client P V) (st : State P V) (s : P) (m : Msg P V) :
    let H := Function.update st.hist s (st.hist s ++ [m])
    (Fires f H st.done.length p ∧ (E).step p cl st s m =
        (⟨H, st.done ++ [H]⟩,
          echoOut s m ++ [.val (st.done.length + 1) (cl (results (st.done ++ [H])))])) ∨
      (¬ Fires f H st.done.length p ∧ (E).step p cl st s m = (⟨H, st.done⟩, echoOut s m)) := by
  intro H
  by_cases h : Fires f H st.done.length p
  · left; refine ⟨h, ?_⟩; simp only [echoProtocol]; rw [ite_eq_left h]
  · right; refine ⟨h, ?_⟩; simp only [echoProtocol]; rw [ite_eq_right h]

lemma val_notMem_echoOut {s : P} {m : Msg P V} {r : ℕ} {w : V} :
    Msg.val r w ∉ echoOut s m := by
  cases m <;> simp [echoOut]

lemma mem_echoOut {s q : P} {m : Msg P V} {r : ℕ} {w : V} (h : Msg.echo r q w ∈ echoOut s m) :
    q = s ∧ m = .val r w := by
  cases m <;> simp_all [echoOut]

lemma echoers_mono {H H' : P → List (Msg P V)} (h : ∀ s, H s ⊆ H' s) (r : ℕ) (p : P) :
    echoers H r p ⊆ echoers H' r p := by
  intro s hs
  simp only [echoers, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  obtain ⟨w, hw⟩ := hs; exact ⟨w, h s hw⟩

variable (f) in
/-- The invariant of reachable configurations of the echo protocol. -/
structure Inv (F : Finset P) (cl : P → Client P V) (c : Cfg) : Prop where
  dl_le : ∀ q s, c.dl q s ≤ (c.log s).length
  hist : ∀ p, p ∉ F → ∀ s, (c.st p).hist s = (c.log s).take (c.dl p s)
  done_prefix : ∀ p, p ∉ F → ∀ H ∈ (c.st p).done, ∀ s, H s <+: c.log s
  done_card : ∀ p, p ∉ F → ∀ r (h : r < (c.st p).done.length),
    Fintype.card P - f ≤ (echoers ((c.st p).done[r]) r p).card
  val_log : ∀ p, p ∉ F → ∀ r w, Msg.val r w ∈ c.log p →
    r ≤ (c.st p).done.length ∧ w = cl p ((results (c.st p).done).take r)
  val_mem : ∀ p, p ∉ F → ∀ r ≤ (c.st p).done.length,
    Msg.val r (cl p ((results (c.st p).done).take r)) ∈ c.log p
  echo_log : ∀ s r q w, Msg.echo r q w ∈ c.log s → q ∉ F → Msg.val r w ∈ c.log q
  echo_of_hist : ∀ p, p ∉ F → ∀ q r w, Msg.val r w ∈ (c.st p).hist q →
    Msg.echo r q w ∈ c.log p
  below : ∀ p, p ∉ F → (echoers (c.st p).hist (c.st p).done.length p).card < Fintype.card P - f

lemma inv_init (hf : f < Fintype.card P) {F : Finset P} {cl : P → Client P V} {c : Cfg}
    (h : (E).Init F cl c) : Inv f F cl c := by
  obtain ⟨h1, h2, h3⟩ := h
  have hst : ∀ p, p ∉ F → c.st p = ⟨fun _ => [], []⟩ := fun p hp => (h1 p hp).1
  have hlog : ∀ p, p ∉ F → c.log p = [Msg.val 0 (cl p [])] := fun p hp => (h1 p hp).2
  have hlog' : ∀ p r q w, Msg.echo r q w ∉ c.log p := by
    intro p r q w hm
    by_cases hp : p ∈ F
    · rw [h2 p hp] at hm; exact List.not_mem_nil hm
    · rw [hlog p hp, List.mem_singleton] at hm; cases hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q s; simp [h3]
  · intro p hp s; rw [hst p hp, h3]; rfl
  · intro p hp H hH; rw [hst p hp] at hH; simp at hH
  · intro p hp r hr; rw [hst p hp] at hr; simp at hr
  · intro p hp r w hm; rw [hlog p hp, List.mem_singleton] at hm; rw [hst p hp]
    cases hm; simp [results]
  · intro p hp r hr; rw [hst p hp] at hr ⊢; simp at hr; subst hr; rw [hlog p hp]; exact List.mem_singleton.2 rfl
  · intro s r q w hm; exact absurd hm (hlog' _ _ _ _)
  · intro p hp q r w hm; rw [hst p hp] at hm; simp at hm
  · intro p hp; rw [hst p hp]; simp [echoers]; omega


@[simp] lemma relays_val (r : ℕ) (w : V) : (E).relays (Msg.val r w) = ∅ := rfl

@[simp] lemma relays_echo (r : ℕ) (q : P) (w : V) :
    (E).relays (Msg.echo r q w) = {(q, Msg.val r w)} := rfl

lemma Inv.append {F : Finset P} {cl : P → Client P V} {c : Cfg} (hI : Inv f F cl c) {s : P}
    {m : Msg P V} (hs : s ∈ F) (hm : ∀ x ∈ (E).relays m, x.1 ∈ F ∨ x.2 ∈ c.log x.1) :
    Inv f F cl (c.append s m) := by
  have hpre : ∀ x, c.log x <+: (c.append s m).log x := fun x => append_log_prefix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q s'; exact (hI.dl_le q s').trans (hpre s').length_le
  · intro p hp s'
    simp only [append_st, append_dl]
    rw [hI.hist p hp s', take_of_prefix (hpre s') (hI.dl_le p s')]
  · intro p hp H hH s'; exact (hI.done_prefix p hp H hH s').trans (hpre s')
  · intro p hp r hr; exact hI.done_card p hp r hr
  · intro p hp r w hmem
    have hps : p ≠ s := fun h => hp (h ▸ hs)
    rw [append_log_of_ne hps] at hmem
    exact hI.val_log p hp r w hmem
  · intro p hp r hr; exact (hpre p).subset (hI.val_mem p hp r hr)
  · intro s' r q w hmem hq
    by_cases hss : s' = s
    · subst hss
      rw [append_log_self, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact (hpre q).subset (hI.echo_log _ r q w hmem hq)
      · rcases hm (q, Msg.val r w) (by simp) with h | h
        · exact absurd h hq
        · exact (hpre q).subset h
    · rw [append_log_of_ne hss] at hmem
      exact (hpre q).subset (hI.echo_log _ r q w hmem hq)
  · intro p hp q r w hmem; exact (hpre p).subset (hI.echo_of_hist p hp q r w hmem)
  · intro p hp; exact hI.below p hp

lemma Inv.deliver (hf : f < Fintype.card P) {F : Finset P} {cl : P → Client P V} {c : Cfg}
    (hI : Inv f F cl c) {q s : P} {m : Msg P V} (hq : q ∉ F)
    (hm : (c.log s)[c.dl q s]? = some m) : Inv f F cl ((E).deliver c cl q s m) := by
  set c' := (E).deliver c cl q s m with hc'
  set st := c.st q with hst
  set H := Function.update st.hist s (st.hist s ++ [m]) with hHdef
  set L := st.done.length with hL
  have hlt : c.dl q s < (c.log s).length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hm
    exact absurd hm (by simp)
  have hmem : m ∈ c.log s := List.mem_of_getElem? hm
  have hpre : ∀ x, c.log x <+: c'.log x := fun x => deliver_log_prefix
  have hdl : ∀ x y, c'.dl x y = if x = q ∧ y = s then c.dl q s + 1 else c.dl x y := by
    intro x y
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; simp [c']
    · exact deliver_dl_of_ne (by tauto)
  have hdl_le : ∀ y, c'.dl q y ≤ (c.log y).length := by
    intro y; rw [hdl]; split_ifs with h
    · obtain ⟨-, rfl⟩ := h; omega
    · exact hI.dl_le q y
  have hH' : ∀ y, H y = (c.log y).take (c'.dl q y) := by
    intro y
    by_cases hy : y = s
    · subst hy
      rw [hdl, ite_eq_left ⟨rfl, rfl⟩, List.take_add_one, hm]
      simp [H, hst, hI.hist q hq]
    · rw [hdl, ite_eq_right (by tauto)]
      simp [H, Function.update_of_ne hy, hst, hI.hist q hq]
  have hH : ∀ y, H y = (c'.log y).take (c'.dl q y) := by
    intro y; rw [hH' y, take_of_prefix (hpre y) (hdl_le y)]
  have hHpre : ∀ y, H y <+: c.log y := by
    intro y; rw [hH' y]; exact List.take_prefix _ _
  have key : ∃ nd extra, (E).step q (cl q) st s m = (⟨H, nd⟩, echoOut s m ++ extra) ∧
      ((Fires f H L q ∧ nd = st.done ++ [H] ∧
          extra = [Msg.val (L + 1) (cl q (results (st.done ++ [H])))]) ∨
        (¬ Fires f H L q ∧ nd = st.done ∧ extra = [])) := by
    rcases step_cases (f := f) q (cl q) st s m with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, h2, Or.inl ⟨h1, rfl, rfl⟩⟩
    · exact ⟨_, [], by rw [h2, List.append_nil], Or.inr ⟨h1, rfl, rfl⟩⟩
  obtain ⟨nd, extra, hstep, hcase⟩ := key
  have hstq : c'.st q = ⟨H, nd⟩ := by simp only [c', deliver_st_self, ← hst, hstep]
  have hlogq : c'.log q = c.log q ++ (echoOut s m ++ extra) := by
    simp only [c', deliver_log_self, ← hst, hstep]
  have hndpre : st.done <+: nd := by
    rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  have hndlen : L ≤ nd.length := hndpre.length_le
  have hndtake : ∀ r ≤ L, (results nd).take r = (results st.done).take r := by
    intro r hr
    rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact take_results_append _ _ hr
    · rfl
  have hextra : ∀ x ∈ extra, ∃ w, x = Msg.val (L + 1) w ∧ w = cl q (results nd) ∧
      nd = st.done ++ [H] := by
    intro x hx
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl⟩
    · simp only [List.mem_singleton] at hx; exact ⟨_, hx, rfl, rfl⟩
    · simp at hx
  have hst_ne : ∀ p, p ≠ q → c'.st p = c.st p := fun p h => deliver_st_of_ne h
  have hlog_ne : ∀ p, p ≠ q → c'.log p = c.log p := fun p h => deliver_log_of_ne h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- dl_le
  · intro x y
    by_cases hx : x = q
    · subst hx; exact (hdl_le y).trans (hpre y).length_le
    · rw [hdl, ite_eq_right (by tauto)]; exact (hI.dl_le x y).trans (hpre y).length_le
  -- hist
  · intro p hp y
    by_cases hpq : p = q
    · subst hpq; rw [hstq]; exact hH y
    · rw [hst_ne p hpq, hdl, ite_eq_right (by tauto), hI.hist p hp y,
        take_of_prefix (hpre y) (hI.dl_le p y)]
  -- done_prefix
  · intro p hp G hG y
    by_cases hpq : p = q
    · subst hpq
      rw [hstq] at hG
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
      · rcases List.mem_append.1 hG with hG | hG
        · exact (hI.done_prefix p hp G hG y).trans (hpre y)
        · rw [List.mem_singleton] at hG; subst hG; exact (hHpre y).trans (hpre y)
      · exact (hI.done_prefix p hp G hG y).trans (hpre y)
    · rw [hst_ne p hpq] at hG; exact (hI.done_prefix p hp G hG y).trans (hpre y)
  -- done_card
  · intro p hp r hr
    by_cases hpq : p = q
    · subst hpq
      simp only [hstq] at hr ⊢
      rcases hcase with ⟨hF, rfl, -⟩ | ⟨-, rfl, -⟩
      · by_cases hrL : r < L
        · rw [List.getElem_append_left (by simpa using hrL)]
          exact hI.done_card p hp r hrL
        · have hr' : r < L + 1 := by
            have := hr; simp only [List.length_append, List.length_singleton] at this; omega
          have : r = L := by omega
          subst this
          rw [List.getElem_append_right (by omega)]
          simp only [List.getElem_singleton]
          exact hF
      · exact hI.done_card p hp r hr
    · simp only [hst_ne p hpq] at hr ⊢; exact hI.done_card p hp r hr
  -- val_log
  · intro p hp r w hw
    by_cases hpq : p = q
    · subst hpq
      rw [hstq]; dsimp only
      rw [hlogq, List.mem_append, List.mem_append] at hw
      rcases hw with hw | hw | hw
      · obtain ⟨h1, h2⟩ := hI.val_log p hp r w hw
        exact ⟨h1.trans hndlen, by rw [hndtake r h1]; exact h2⟩
      · exact absurd hw val_notMem_echoOut
      · obtain ⟨w', hw', hw'', hnd⟩ := hextra _ hw
        cases hw'
        subst hnd
        refine ⟨by simp [hL], ?_⟩
        rw [List.take_of_length_le (by simp [hL])]; exact hw''
    · rw [hlog_ne p hpq] at hw; rw [hst_ne p hpq]; exact hI.val_log p hp r w hw
  -- val_mem
  · intro p hp r hr
    by_cases hpq : p = q
    · subst hpq
      rw [hstq] at hr ⊢; dsimp only at hr ⊢
      by_cases hrL : r ≤ L
      · rw [hndtake r hrL]; exact (hpre p).subset (hI.val_mem p hp r hrL)
      · rcases hcase with ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩
        · have : r = L + 1 := by simp at hr; omega
          subst this
          rw [hlogq, List.take_of_length_le (by simp [hL])]
          simp
        · exact absurd hr hrL
    · rw [hst_ne p hpq] at hr ⊢; rw [hlog_ne p hpq]; exact hI.val_mem p hp r hr
  -- echo_log
  · intro x r q' w hw hq'
    by_cases hxq : x = q
    · subst hxq
      rw [hlogq, List.mem_append, List.mem_append] at hw
      rcases hw with hw | hw | hw
      · exact (hpre q').subset (hI.echo_log _ r q' w hw hq')
      · obtain ⟨rfl, rfl⟩ := mem_echoOut hw
        exact (hpre _).subset hmem
      · obtain ⟨w', hw', -⟩ := hextra _ hw; cases hw'
    · rw [hlog_ne x hxq] at hw; exact (hpre q').subset (hI.echo_log _ r q' w hw hq')
  -- echo_of_hist
  · intro p hp y r w hw
    by_cases hpq : p = q
    · subst hpq
      rw [hstq] at hw; dsimp only at hw
      by_cases hy : y = s
      · subst hy
        simp only [H, Function.update_self, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact (hpre p).subset (hI.echo_of_hist p hp y r w hw)
        · rw [hlogq]; simp [echoOut]
      · simp only [H, Function.update_of_ne hy] at hw
        exact (hpre p).subset (hI.echo_of_hist p hp y r w hw)
    · rw [hst_ne p hpq] at hw; exact (hpre p).subset (hI.echo_of_hist p hp y r w hw)
  -- below
  · intro p hp
    by_cases hpq : p = q
    · subst hpq
      rw [hstq]; dsimp only
      rcases hcase with ⟨-, rfl, -⟩ | ⟨hF, rfl, -⟩
      · have : echoers H (st.done ++ [H]).length p = ∅ := by
          ext y
          simp only [echoers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_exists]
          intro w hw
          have h1 := hI.echo_log y _ p w ((hHpre y).subset hw) hp
          have h2 := (hI.val_log p hp _ w h1).1
          rw [← hst] at h2; simp at h2
        rw [this]; simp; omega
      · have hL' : L = st.done.length := hL
        unfold Fires at hF; rw [← hL']; omega
    · rw [hst_ne p hpq]; exact hI.below p hp

/-- The invariant holds in all reachable configurations. -/
lemma inv_of_reachable (hf : f < Fintype.card P) {F : Finset P} {cl : P → Client P V} {c : Cfg}
    (hc : ((E).system F cl).Reachable c) : Inv f F cl c := by
  obtain ⟨c₀, h₀, hr⟩ := hc
  induction hr with
  | refl => exact inv_init hf h₀
  | tail _ h ih =>
    cases h with
    | deliver q s m hq hm => exact ih.deliver hf hq hm
    | byz s m hs hm => exact ih.append hs hm


/-! ### The four properties -/

omit [Fintype P] [DecidableEq P] in
lemma results_prefix {d d' : List (P → List (Msg P V))} (h : d <+: d') :
    results d <+: results d' := by
  obtain ⟨t, rfl⟩ := h
  simp only [results, List.mapIdx_append]
  exact List.prefix_append _ _

/-- Completed rounds are only extended (any step, any process). -/
lemma done_prefix_step {F : Finset P} {cl : P → Client P V} {c c' : Cfg}
    (h : (E).Step F cl c c') (p : P) : (c.st p).done <+: (c'.st p).done := by
  cases h with
  | byz s m hs hm => exact List.prefix_refl _
  | deliver q s m hq hm =>
    by_cases hpq : p = q
    · subst hpq
      rw [deliver_st_self]
      rcases step_cases (f := f) p (cl p) (c.st p) s m with ⟨-, h2⟩ | ⟨-, h2⟩
      · rw [h2]; exact List.prefix_append _ _
      · rw [h2]
    · rw [deliver_st_of_ne hpq]

omit [Fintype P] [DecidableEq P] in
lemma take_prefix_take_of_prefix {α : Type*} {l l' : List α} (h : l <+: l') {a b : ℕ}
    (hab : a ≤ b) (ha : a ≤ l.length) : l.take a <+: l'.take b := by
  rw [← take_of_prefix h ha]; exact List.take_prefix_take_left hab

lemma getElem_rounds {F : Finset P} {cl : P → Client P V} (c : Cfg) (p : P) (r : ℕ)
    (h : r < (c.st p).done.length) (h' : r < (((E).system F cl).rounds c p).length) :
    (((E).system F cl).rounds c p)[r] = recv r ((c.st p).done[r]) :=
  getElem_results _ _ _

@[simp] lemma rounds_def (st : State P V) : (E).rounds st = results st.done := rfl

lemma rounds_eq {F : Finset P} {cl : P → Client P V} (c : Cfg) (p : P) :
    ((E).system F cl).rounds c p = results (c.st p).done := rfl

section Exec

variable {F : Finset P} {cl : P → Client P V} {e : ℕ → SRBConfig P (Msg P V) (State P V)}

lemma done_prefix_of_le (he : ((E).system F cl).IsExec e) {t t' : ℕ} (h : t ≤ t') (p : P) :
    ((e t).st p).done <+: ((e t').st p).done :=
  RoundSystem.IsExec.mono (S := (E).system F cl) he (R := fun a b => (a.st p).done <+: (b.st p).done)
    (fun _ => List.prefix_refl _) (fun _ _ _ h1 h2 => h1.trans h2)
    (fun _ _ _ h => done_prefix_step h p) h

lemma hist_mem_of_le (hf : f < Fintype.card P) (he : ((E).system F cl).IsExec e) {t t' : ℕ}
    (h : t ≤ t') {p : P} (hp : p ∉ F) {y : P} {x : Msg P V}
    (hx : x ∈ ((e t).st p).hist y) : x ∈ ((e t').st p).hist y := by
  have hI := inv_of_reachable hf (he.reachable t)
  have hI' := inv_of_reachable hf (he.reachable t')
  rw [hI.hist p hp y] at hx; rw [hI'.hist p hp y]
  exact (take_prefix_take_of_prefix (log_prefix_of_le he h y) (dl_le_of_le he h p y)
    (hI.dl_le p y)).subset hx

/-- If correct `p` has delivered at least `i + 1` messages of `y`, then the `i`-th one is in its
history. -/
lemma mem_hist_of_lt (hf : f < Fintype.card P) (he : ((E).system F cl).IsExec e) {t : ℕ} {p : P}
    (hp : p ∉ F) {y : P} {i : ℕ} (hi : i < (e t).dl p y) (hil : i < ((e t).log y).length) :
    ((e t).log y)[i] ∈ ((e t).st p).hist y := by
  have hI := inv_of_reachable hf (he.reachable t)
  rw [hI.hist p hp y]
  have : i < (((e t).log y).take ((e t).dl p y)).length := by simp; omega
  rw [← List.getElem_take (j := (e t).dl p y) (h := this)]
  exact List.getElem_mem _

/-- Liveness: in a fair execution every correct process completes every round. -/
lemma live (hf : f < Fintype.card P) (hF : F.card ≤ f) (he : ((E).system F cl).IsExec e)
    (hfair : Fair F e) {p : P} (hp : p ∉ F) : ∀ r, ∃ t, r ≤ ((e t).st p).done.length := by
  intro r
  induction r with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ r ih =>
    obtain ⟨t0, h0⟩ := ih
    by_contra hne
    push Not at hne
    have hlen : ∀ t, t0 ≤ t → ((e t).st p).done.length = r := by
      intro t ht
      have := (done_prefix_of_le he ht p).length_le
      have := hne t; omega
    set w := cl p ((results ((e t0).st p).done).take r) with hw
    have hv := (inv_of_reachable hf (he.reachable t0)).val_mem p hp r h0
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hv
    have hall : ∀ s, ∃ ts, s ∉ F → ∀ t, ts ≤ t → s ∈ echoers ((e t).st p).hist r p := by
      intro s
      by_cases hs : s ∈ F
      · exact ⟨0, fun h => absurd hs h⟩
      refine (fun h => ?_) hs
      -- `s` delivers `val r w` from `p`
      obtain ⟨t1, ht1⟩ := hfair s hs p i ⟨t0, hi⟩ (Or.inl hp)
      set t1' := max t0 t1
      have hi1 : i < (e t1').dl s p := lt_of_lt_of_le ht1 (dl_le_of_le he (le_max_right _ _) s p)
      have hpre1 := log_prefix_of_le he (le_max_left t0 t1) p
      have hil1 : i < ((e t1').log p).length := lt_of_lt_of_le hi hpre1.length_le
      have hval : Msg.val r w ∈ ((e t1').st s).hist p := by
        have := mem_hist_of_lt hf he hs hi1 hil1
        rwa [← hpre1.getElem hi, hgi] at this
      have hecho := (inv_of_reachable hf (he.reachable t1')).echo_of_hist s hs p r w hval
      obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hecho
      obtain ⟨t2, ht2⟩ := hfair p hp s j ⟨t1', hj⟩ (Or.inl hs)
      set t2' := max t1' t2
      have hj2 : j < (e t2').dl p s := lt_of_lt_of_le ht2 (dl_le_of_le he (le_max_right _ _) p s)
      have hpre2 := log_prefix_of_le he (le_max_left t1' t2) s
      have hjl2 : j < ((e t2').log s).length := lt_of_lt_of_le hj hpre2.length_le
      have hech2 : Msg.echo r p w ∈ ((e t2').st p).hist s := by
        have := mem_hist_of_lt hf he hp hj2 hjl2
        rwa [← hpre2.getElem hj, hgj] at this
      refine ⟨t2', fun _ t ht => ?_⟩
      simp only [echoers, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hist_mem_of_le hf he ht hp hech2⟩
    choose ts hts using hall
    set T := max t0 (Finset.univ.sup ts)
    have hT : ((e T).st p).done.length = r := hlen T (le_max_left _ _)
    have hsub : Finset.univ \ F ⊆ echoers ((e T).st p).hist r p := by
      intro s hs
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hs
      exact hts s hs T ((Finset.le_sup (Finset.mem_univ s)).trans (le_max_right _ _))
    have hbelow := (inv_of_reachable hf (he.reachable T)).below p hp
    rw [hT] at hbelow
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ F), Finset.card_univ] at h1
    omega

end Exec

/-- **The echo protocol implements unidirectional rounds over SRB whenever `n > 2f`** (for every
`f`, in particular `f > 1`): this refutes the Claim of Section 4.1. -/
theorem echoProtocol_implements (hf : 2 * f < Fintype.card P) : (E).Implements f := by
  intro F hF cl
  have hf' : f < Fintype.card P := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c c' _ h p _
    simp only [rounds_def]
    exact results_prefix (done_prefix_step h p)
  · intro c hc p q hp hq hpq r hrp hrq
    have hI := inv_of_reachable hf' hc
    have hrp' : r < (c.st p).done.length := by simpa using hrp
    have hrq' : r < (c.st q).done.length := by simpa using hrq
    rw [getElem_rounds _ _ _ hrp', getElem_rounds _ _ _ hrq']
    have hcp := hI.done_card p hp r hrp'
    have hcq := hI.done_card q hq r hrq'
    have hpp := fun s => hI.done_prefix p hp _ (List.getElem_mem hrp') s
    have hqp := fun s => hI.done_prefix q hq _ (List.getElem_mem hrq') s
    generalize (c.st p).done[r] = Hp at hcp hpp ⊢
    generalize (c.st q).done[r] = Hq at hcq hqp ⊢
    obtain ⟨s, hs⟩ : (echoers Hp r p ∩ echoers Hq r q).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      have h1 := Finset.card_union_add_card_inter (echoers Hp r p) (echoers Hq r q)
      rw [h0, Finset.card_empty] at h1
      have h2 := Finset.card_le_univ (echoers Hp r p ∪ echoers Hq r q)
      omega
    simp only [Finset.mem_inter, echoers, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨⟨w, hw⟩, ⟨w', hw'⟩⟩ := hs
    rcases List.prefix_or_prefix_of_prefix (hpp s) (hqp s) with h | h
    · right; rw [recv_isSome_iff]; exact ⟨w, Or.inr ⟨s, h.subset hw⟩⟩
    · left; rw [recv_isSome_iff]; exact ⟨w', Or.inr ⟨s, h.subset hw'⟩⟩
  · intro c hc p q hp hq r hrp w hw
    have hI := inv_of_reachable hf' hc
    have hrp' : r < (c.st p).done.length := by simpa using hrp
    rw [getElem_rounds _ _ _ hrp'] at hw
    have hval : Msg.val r w ∈ c.log q := by
      rcases recv_eq_some hw with h | ⟨s, h⟩
      · exact (hI.done_prefix p hp _ (List.getElem_mem _) q).subset h
      · exact hI.echo_log s r q w ((hI.done_prefix p hp _ (List.getElem_mem _) s).subset h) hq
    simpa using hI.val_log q hq r w hval
  · intro e he hfair p hp r
    obtain ⟨t, ht⟩ := live hf' hF he hfair hp (r + 1)
    exact ⟨t, by simp only [rounds_def, length_results]; omega⟩

end Echo

end Podc.TrustedHW
