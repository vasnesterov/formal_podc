import Papers.PODC2017.RegisterEmulationSpace.Model

/-!
# Runs: basic facts, solo strategies, fairness of strategy runs

Generic tools for the lower-bound constructions:
* `WF`: identifiers of pending operations are distinct and smaller than the client's counter;
* events of one client do not touch the other clients (`step_other`);
* `splice P e`: a finite prefix `P` followed by an infinite event sequence `e`;
* `soloEv δ c Z`: the solo strategy of `c` that never lets registers on servers in `Z` respond:
  respond to some pending operation of `c` on a server outside `Z`, otherwise schedule `c`;
* `fair_solo`: a run following `soloEv δ c (Z t)` with `Z t` eventually constant `Zs` is fair for the
  failure pattern "all clients but `c` crashed, the servers `Zs` crashed";
* `exists_ret_of_solo`: hence, by obstruction freedom, `c` returns (if `|Zs| ≤ f`);
* `SoloRel`: two configurations that agree on `c` and on the registers outside `Z` have the same solo
  behaviour of `c` (indistinguishability).
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace

variable {C B V W L S : Type*} [DecidableEq C] [DecidableEq B]

open Function

/-- Well-formedness of configurations: identifiers of pending operations of a client are distinct
and below its counter. -/
def WF (X : Cfg C B V W L) : Prop :=
  ∀ c, ((X.pend c).map POp.n).Nodup ∧ ∀ p ∈ X.pend c, p.n < X.cnt c

namespace Alg

variable (A : Alg C B V W L)

/-! ### Basic simp lemmas -/

@[simp] lemma step_inv (X : Cfg C B V W L) (c : C) (o : HOp V) :
    A.step X (.inv c o) = A.doInv X c o := rfl
@[simp] lemma step_step (X : Cfg C B V W L) (c : C) : A.step X (.step c) = A.doStep X c := rfl
@[simp] lemma step_resp (X : Cfg C B V W L) (c : C) (n : ℕ) :
    A.step X (.resp c n) = A.doResp X c n := rfl

@[simp] lemma exec_nil (X : Cfg C B V W L) : A.exec X [] = X := rfl
@[simp] lemma exec_cons (X : Cfg C B V W L) (e : Ev C V) (E : List (Ev C V)) :
    A.exec X (e :: E) = A.exec (A.step X e) E := rfl
lemma exec_append (X : Cfg C B V W L) (E E' : List (Ev C V)) :
    A.exec X (E ++ E') = A.exec (A.exec X E) E' := by
  simp [exec, List.foldl_append]
lemma run_append (E E' : List (Ev C V)) : A.run (E ++ E') = A.exec (A.run E) E' :=
  A.exec_append _ _ _
@[simp] lemma exec_singleton (X : Cfg C B V W L) (e : Ev C V) : A.exec X [e] = A.step X e := rfl

@[simp] lemma doStep_val (X : Cfg C B V W L) (c : C) : (A.doStep X c).val = X.val := by
  unfold doStep; split <;> (try split) <;> rfl

lemma doStep_other (X : Cfg C B V W L) {c c' : C} (h : c' ≠ c) :
    (A.doStep X c).pend c' = X.pend c' ∧ (A.doStep X c).loc c' = X.loc c' ∧
    (A.doStep X c).cur c' = X.cur c' ∧ (A.doStep X c).cnt c' = X.cnt c' := by
  unfold doStep; split <;> (try split) <;> simp [update_of_ne h]

lemma apply_other (X : Cfg C B V W L) {c c' : C} (p : POp B W) (h : c' ≠ c) :
    (A.apply X c p).pend c' = X.pend c' ∧ (A.apply X c p).loc c' = X.loc c' ∧
    (A.apply X c p).cur c' = X.cur c' ∧ (A.apply X c p).cnt c' = X.cnt c' := by
  unfold apply; split <;> simp [update_of_ne h]

lemma doResp_other (X : Cfg C B V W L) {c c' : C} (n : ℕ) (h : c' ≠ c) :
    (A.doResp X c n).pend c' = X.pend c' ∧ (A.doResp X c n).loc c' = X.loc c' ∧
    (A.doResp X c n).cur c' = X.cur c' ∧ (A.doResp X c n).cnt c' = X.cnt c' := by
  unfold doResp; split
  · simp
  · exact A.apply_other _ _ h

/-- Events of client `c` do not touch the other clients. -/
lemma step_other (X : Cfg C B V W L) {c c' : C} {e : Ev C V} (he : e.IsOf c) (h : c' ≠ c) :
    (A.step X e).pend c' = X.pend c' ∧ (A.step X e).loc c' = X.loc c' ∧
    (A.step X e).cur c' = X.cur c' ∧ (A.step X e).cnt c' = X.cnt c' := by
  cases e with
  | inv _ _ => exact he.elim
  | step d => subst he; exact A.doStep_other X h
  | resp d n => subst he; exact A.doResp_other X n h

lemma exec_other (X : Cfg C B V W L) {c c' : C} {E : List (Ev C V)} (hE : ∀ e ∈ E, e.IsOf c)
    (h : c' ≠ c) :
    (A.exec X E).pend c' = X.pend c' ∧ (A.exec X E).loc c' = X.loc c' ∧
    (A.exec X E).cur c' = X.cur c' ∧ (A.exec X E).cnt c' = X.cnt c' := by
  induction E generalizing X with
  | nil => simp
  | cons e E ih =>
    simp only [exec_cons]
    obtain ⟨h1, h2, h3, h4⟩ := A.step_other X (hE e (by simp)) h
    obtain ⟨g1, g2, g3, g4⟩ := ih (A.step X e) (fun e' he' => hE e' (by simp [he']))
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4⟩

lemma doInv_other (X : Cfg C B V W L) {c c' : C} (o : HOp V) (h : c' ≠ c) :
    (A.doInv X c o).pend c' = X.pend c' ∧ (A.doInv X c o).loc c' = X.loc c' ∧
    (A.doInv X c o).cur c' = X.cur c' ∧ (A.doInv X c o).cnt c' = X.cnt c' := by
  unfold doInv; split <;> simp [update_of_ne h]

@[simp] lemma doInv_val (X : Cfg C B V W L) (c : C) (o : HOp V) : (A.doInv X c o).val = X.val := by
  unfold doInv; split <;> rfl
@[simp] lemma doInv_pend (X : Cfg C B V W L) (c : C) (o : HOp V) :
    (A.doInv X c o).pend = X.pend := by
  unfold doInv; split <;> rfl
@[simp] lemma doInv_cnt (X : Cfg C B V W L) (c : C) (o : HOp V) :
    (A.doInv X c o).cnt = X.cnt := by
  unfold doInv; split <;> rfl

lemma doInv_of_idle (X : Cfg C B V W L) (c : C) (o : HOp V) (h : X.cur c = none) :
    (A.doInv X c o).cur c = some o ∧ (A.doInv X c o).hist = X.hist ++ [.inv c o] := by
  simp [doInv, h]

/-! ### Well-formedness -/

lemma wf_init : WF A.initCfg := fun c => by simp [initCfg]

lemma mem_filter_ne {X : Cfg C B V W L} (hwf : WF X) {c : C} {p q : POp B W}
    (hp : p ∈ X.pend c) :
    q ∈ (X.pend c).filter (fun q => q.n ≠ p.n) ↔ q ∈ X.pend c ∧ q ≠ p := by
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hq, hne⟩; exact ⟨hq, fun h => hne (h ▸ rfl)⟩
  · rintro ⟨hq, hne⟩
    exact ⟨hq, fun h => hne (List.inj_on_of_nodup_map (hwf c).1 hq hp h)⟩

lemma find_n {X : Cfg C B V W L} (hwf : WF X) {c : C} {p : POp B W} (hp : p ∈ X.pend c) :
    (X.pend c).find? (fun q => q.n = p.n) = some p := by
  obtain ⟨q, hq⟩ : ∃ q, (X.pend c).find? (fun q => q.n = p.n) = some q := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨p, hp, by simp⟩
  rw [hq]
  have h1 := List.mem_of_find?_eq_some hq
  have h2 : q.n = p.n := by simpa using List.find?_some hq
  rw [List.inj_on_of_nodup_map (hwf c).1 h1 hp h2]

lemma doResp_of_mem {X : Cfg C B V W L} (hwf : WF X) {c : C} {p : POp B W} (hp : p ∈ X.pend c) :
    A.doResp X c p.n = A.apply X c p := by
  simp [doResp, find_n hwf hp]

lemma apply_pend_self (X : Cfg C B V W L) (c : C) (p : POp B W) :
    (A.apply X c p).pend c = (X.pend c).filter (fun q => q.n ≠ p.n) := by
  unfold apply; split <;> simp

lemma apply_cur (X : Cfg C B V W L) (c : C) (p : POp B W) : (A.apply X c p).cur = X.cur := by
  unfold apply; split <;> rfl
lemma apply_cnt (X : Cfg C B V W L) (c : C) (p : POp B W) : (A.apply X c p).cnt = X.cnt := by
  unfold apply; split <;> rfl
lemma apply_hist (X : Cfg C B V W L) (c : C) (p : POp B W) : (A.apply X c p).hist = X.hist := by
  unfold apply; split <;> rfl

lemma apply_val (X : Cfg C B V W L) (c : C) (p : POp B W) (b : B) :
    (A.apply X c p).val b = match p.op with | .read => X.val b | .write w => update X.val p.reg w b := by
  unfold apply; split <;> simp_all

lemma apply_val_of_ne (X : Cfg C B V W L) (c : C) (p : POp B W) {b : B} (hb : b ≠ p.reg) :
    (A.apply X c p).val b = X.val b := by
  rw [apply_val]; split <;> simp [update_of_ne hb]

lemma apply_pend (X : Cfg C B V W L) (c : C) (p : POp B W) :
    (A.apply X c p).pend = update X.pend c ((X.pend c).filter (fun q => q.n ≠ p.n)) := by
  unfold apply; split <;> rfl

lemma wf_apply {X : Cfg C B V W L} (hwf : WF X) (c : C) (p : POp B W) : WF (A.apply X c p) := by
  intro d
  rw [apply_pend, apply_cnt]
  by_cases hd : d = c
  · subst hd
    simp only [update_self]
    refine ⟨((hwf d).1.sublist ?_), fun q hq => (hwf d).2 q (List.mem_of_mem_filter hq)⟩
    exact (List.filter_sublist).map _
  · simp only [update_of_ne hd]; exact hwf d

lemma wf_step {X : Cfg C B V W L} (hwf : WF X) (e : Ev C V) : WF (A.step X e) := by
  cases e with
  | inv c o => intro d; simpa using hwf d
  | resp c n =>
    simp only [step_resp, doResp]
    split
    · exact hwf
    · exact A.wf_apply hwf _ _
  | step c =>
    simp only [step_step, doStep]
    split
    · intro d
      by_cases hd : d = c
      · subst hd
        simp only [update_self, List.map_append, List.map_cons, List.map_nil]
        refine ⟨?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨(hwf d).1, List.nodup_singleton _, ?_⟩
          intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst hy
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          exact (hwf d).2 q hq |>.ne
        · intro q hq
          rcases List.mem_append.1 hq with hq | hq
          · exact Nat.lt_succ_of_lt ((hwf d).2 q hq)
          · simp at hq; subst hq; simp
      · simpa [update_of_ne hd] using hwf d
    · split
      · intro d; simpa using hwf d
      · intro d; simpa using hwf d
    · intro d; simpa using hwf d

lemma wf_exec {X : Cfg C B V W L} (hwf : WF X) (E : List (Ev C V)) : WF (A.exec X E) := by
  induction E generalizing X with
  | nil => exact hwf
  | cons e E ih => exact ih (A.wf_step hwf e)

lemma wf_run (E : List (Ev C V)) : WF (A.run E) := A.wf_exec A.wf_init E

/-! ### Sequences of configurations and spliced runs -/

/-- A sequence of configurations driven by events `e`, given as a list. -/
lemma seq_exec {X : ℕ → Cfg C B V W L} {e : ℕ → Ev C V} (hX : ∀ t, X (t + 1) = A.step (X t) (e t))
    (t : ℕ) : X t = A.exec (X 0) ((List.range t).map e) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [hX, ih, List.range_succ, List.map_append, exec_append]; rfl

/-- A finite prefix `P` followed by the infinite sequence `e`. -/
def _root_.Podc.RegisterEmulationSpace.splice (P : List (Ev C V)) (e : ℕ → Ev C V) :
    ℕ → Ev C V :=
  fun t => if h : t < P.length then P[t] else e (t - P.length)

lemma traj_splice_le (P : List (Ev C V)) (e : ℕ → Ev C V) :
    ∀ t ≤ P.length, A.traj (splice P e) t = A.run (P.take t) := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t < P.length := ht
    rw [traj, ih hlt.le, List.take_add_one, run_append, List.getElem?_eq_getElem hlt]
    simp [splice, hlt]

lemma traj_splice_add (P : List (Ev C V)) (e : ℕ → Ev C V) {X : ℕ → Cfg C B V W L}
    (hX0 : X 0 = A.run P) (hX : ∀ t, X (t + 1) = A.step (X t) (e t)) :
    ∀ t, A.traj (splice P e) (P.length + t) = X t := by
  intro t
  induction t with
  | zero => rw [Nat.add_zero, A.traj_splice_le P e _ le_rfl, List.take_length, hX0]
  | succ t ih =>
    rw [← Nat.add_assoc, traj, ih, hX]
    simp [splice]

lemma traj_splice_of_ge (P : List (Ev C V)) (e : ℕ → Ev C V) {X : ℕ → Cfg C B V W L}
    (hX0 : X 0 = A.run P) (hX : ∀ t, X (t + 1) = A.step (X t) (e t)) {t : ℕ}
    (ht : P.length ≤ t) : A.traj (splice P e) t = X (t - P.length) := by
  rw [← A.traj_splice_add P e hX0 hX]; congr 1; omega

lemma splice_of_ge (P : List (Ev C V)) (e : ℕ → Ev C V) {t : ℕ} (ht : P.length ≤ t) :
    splice P e t = e (t - P.length) := by
  simp [splice, Nat.not_lt.2 ht]

end Alg

/-! ### Solo strategies -/

section Solo

variable [DecidableEq S]

/-- The solo strategy of `c` with the servers `Z` frozen. -/
def soloEv (δ : B → S) (c : C) (Z : Finset S) (X : Cfg C B V W L) : Ev C V :=
  match (X.pend c).find? (fun p => δ p.reg ∉ Z) with
  | some p => .resp c p.n
  | none => .step c

lemma soloEv_isOf (δ : B → S) (c : C) (Z : Finset S) (X : Cfg C B V W L) :
    (soloEv δ c Z X).IsOf c := by
  unfold soloEv; split <;> rfl

lemma soloEv_cases (δ : B → S) (c : C) (Z : Finset S) (X : Cfg C B V W L) :
    (soloEv δ c Z X = .step c ∧ ∀ p ∈ X.pend c, δ p.reg ∈ Z) ∨
    ∃ p ∈ X.pend c, δ p.reg ∉ Z ∧ soloEv δ c Z X = .resp c p.n := by
  unfold soloEv
  split
  · rename_i p hp
    exact Or.inr ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, rfl⟩
  · rename_i hp
    refine Or.inl ⟨rfl, fun p hpm => ?_⟩
    have := List.find?_eq_none.1 hp p hpm
    simpa using this

namespace Alg

variable (A : Alg C B V W L)

lemma length_pend_apply_lt {X : Cfg C B V W L} {c : C} {p : POp B W} (hp : p ∈ X.pend c) :
    ((A.apply X c p).pend c).length < (X.pend c).length := by
  rw [apply_pend_self, List.length_filter_lt_length_iff_exists]
  exact ⟨p, hp, by simp⟩

/-- A run following the solo strategy of `c` (with frozen servers `Z t`, eventually equal to `Zs`)
after a finite prefix `P` is fair for the pattern "all other clients crashed, `Zs` crashed". -/
theorem fair_solo {δ : B → S} {P : List (Ev C V)} {e : ℕ → Ev C V} {X : ℕ → Cfg C B V W L}
    {Z : ℕ → Finset S} {Zs : Finset S} {c : C} {T : ℕ}
    (hX0 : X 0 = A.run P) (hX : ∀ t, X (t + 1) = A.step (X t) (e t))
    (he : ∀ t, e t = soloEv δ c (Z t) (X t)) (hZ : ∀ t ≥ T, Z t = Zs) :
    A.Fair δ (splice P e) {c}ᶜ ↑Zs := by
  have hwf : ∀ t, WF (X t) := fun t => by
    rw [A.seq_exec hX t, hX0]; exact A.wf_exec (A.wf_run P) _
  -- `c` is scheduled infinitely often in the strategy part
  have hsched : ∀ u, ∃ u' ≥ u, e u' = .step c := by
    intro u
    induction h : (X u).pend c |>.length using Nat.strong_induction_on generalizing u with
    | _ m ih =>
      rcases soloEv_cases δ c (Z u) (X u) with ⟨hs, -⟩ | ⟨p, hp, -, hr⟩
      · exact ⟨u, le_rfl, (he u).trans hs⟩
      · have hlt : ((X (u + 1)).pend c).length < m := by
          rw [hX, he, hr, step_resp, A.doResp_of_mem (hwf u) hp, ← h]
          exact A.length_pend_apply_lt hp
        obtain ⟨u', hu', h'⟩ := ih _ hlt (u + 1) rfl
        exact ⟨u', by omega, h'⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd t
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hd
    subst hd
    obtain ⟨u', hu', h'⟩ := hsched (t - P.length)
    exact ⟨P.length + u', by omega, by rw [splice_of_ge _ _ (by omega)]; simpa using h'⟩
  · intro d hd
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hd
    refine ⟨P.length, fun t ht => ?_⟩
    rw [splice_of_ge _ _ ht, he]
    have := soloEv_isOf δ c (Z (t - P.length)) (X (t - P.length))
    constructor
    · intro h; rw [h] at this; exact hd this
    · intro o h; rw [h] at this; exact this
  · intro s hs
    refine ⟨P.length + T, fun t ht d n p hev hfind => ?_⟩
    rw [splice_of_ge _ _ (by omega), he] at hev
    rw [A.traj_splice_of_ge P e hX0 hX (by omega)] at hfind
    set u := t - P.length
    rcases soloEv_cases δ c (Z u) (X u) with ⟨hs', -⟩ | ⟨q, hq, hqZ, hr⟩
    · rw [hs'] at hev; cases hev
    · rw [hr] at hev
      injection hev with h1 h2
      subst h1; subst h2
      rw [find_n (hwf u) hq] at hfind
      cases hfind
      rw [hZ u (by omega)] at hqZ
      exact fun h => hqZ (h ▸ hs)
  · intro t d p hd hp hpZ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hd
    subst hd
    obtain ⟨u', hu', h'⟩ := hsched (max (t - P.length) T)
    refine ⟨P.length + u', by omega, ?_⟩
    rw [A.traj_splice_add P e hX0 hX]
    rcases soloEv_cases δ d (Z u') (X u') with ⟨-, hall⟩ | ⟨q, -, -, hr⟩
    · intro hp'
      have := hall p hp'
      rw [hZ u' (by omega)] at this
      exact hpZ this
    · rw [← he, h'] at hr; cases hr

/-- Obstruction freedom applied to a solo strategy run: the client returns. -/
theorem exists_ret_of_solo {δ : B → S} {f : ℕ} {Wr : Set C} (hOF : A.ObstructionFree δ f Wr)
    {P₀ : List (Ev C V)} {c : C} {o : HOp V} {e : ℕ → Ev C V} {X : ℕ → Cfg C B V W L}
    {Z : ℕ → Finset S} {Zs : Finset S} {T : ℕ} (hZs : Zs.card ≤ f)
    (hw : ∀ d v, Ev.inv d (.write v) ∈ P₀ ++ [.inv c o] → d ∈ Wr)
    (hidle : (A.run P₀).cur c = none)
    (hX0 : X 0 = A.run (P₀ ++ [.inv c o])) (hX : ∀ t, X (t + 1) = A.step (X t) (e t))
    (he : ∀ t, e t = soloEv δ c (Z t) (X t)) (hZ : ∀ t ≥ T, Z t = Zs) :
    ∃ u, (X u).cur c = none := by
  set P := P₀ ++ [.inv c o]
  have hfair := A.fair_solo hX0 hX he hZ
  have hlen : P.length = P₀.length + 1 := by simp [P]
  have hwo : WritersOnly Wr (splice P e) := by
    intro t d v ht
    by_cases hlt : t < P.length
    · simp only [splice, hlt, dite_true] at ht
      exact hw d v (ht ▸ List.getElem_mem hlt)
    · rw [splice_of_ge _ _ (Nat.not_lt.1 hlt), he] at ht
      have := soloEv_isOf δ c (Z (t - P.length)) (X (t - P.length))
      rw [ht] at this; exact this.elim
  have hinv : splice P e P₀.length = .inv c o := by simp [splice, P]
  have htraj : A.traj (splice P e) P₀.length = A.run P₀ := by
    rw [A.traj_splice_le P e _ (by omega)]; simp [P]
  obtain ⟨t', ht', hcur⟩ := hOF (splice P e) {c}ᶜ Zs hZs hfair hwo P₀.length c o (by simp) hinv
    (htraj ▸ hidle) (fun t' _ c' hc' hc'F => by simp [hc'] at hc'F)
  refine ⟨t' - P.length, ?_⟩
  rw [← A.traj_splice_of_ge P e hX0 hX (by omega)]
  exact hcur

/-! ### Indistinguishability of solo runs -/

/-- `X` and `Y` agree on client `c` and on the registers outside the servers `Z`. -/
def _root_.Podc.RegisterEmulationSpace.SoloRel (δ : B → S) (c : C) (Z : Finset S)
    (X Y : Cfg C B V W L) : Prop :=
  X.loc c = Y.loc c ∧ X.pend c = Y.pend c ∧ X.cur c = Y.cur c ∧ X.cnt c = Y.cnt c ∧
    ∀ b, δ b ∉ Z → X.val b = Y.val b

lemma soloRel_step {δ : B → S} {c : C} {Z : Finset S} {X Y : Cfg C B V W L} (hwf : WF X)
    (h : SoloRel δ c Z X Y) :
    soloEv δ c Z Y = soloEv δ c Z X ∧
    SoloRel δ c Z (A.step X (soloEv δ c Z X)) (A.step Y (soloEv δ c Z X)) ∧
    ∃ D, (A.step X (soloEv δ c Z X)).hist = X.hist ++ D ∧
      (A.step Y (soloEv δ c Z X)).hist = Y.hist ++ D := by
  obtain ⟨hl, hp, hc, hn, hv⟩ := h
  have hev : soloEv δ c Z Y = soloEv δ c Z X := by simp [soloEv, hp]
  refine ⟨hev, ?_⟩
  rcases soloEv_cases δ c Z X with ⟨hs, -⟩ | ⟨p, hpm, hpZ, hr⟩
  · rw [hs]
    simp only [step_step, doStep, ← hl]
    split
    · refine ⟨⟨by simp, by simp [hp, hn], by simp [hc], by simpa using hn, fun b hb => by simpa using hv b hb⟩,
        [], by simp, by simp⟩
    · rename_i x _
      rw [← hc]
      split
      · exact ⟨⟨by simp, by simpa using hp, by simp, by simpa using hn,
          fun b hb => by simpa using hv b hb⟩, [.ret c x], rfl, rfl⟩
      · exact ⟨⟨by simp, by simpa using hp, by simpa using hc, by simpa using hn,
          fun b hb => by simpa using hv b hb⟩, [], by simp, by simp⟩
    · exact ⟨⟨by simp, by simpa using hp, by simpa using hc, by simpa using hn,
          fun b hb => by simpa using hv b hb⟩, [], by simp, by simp⟩
  · have hwfY : (Y.pend c).find? (fun q => q.n = p.n) = some p := hp ▸ find_n hwf hpm
    rw [hr]
    simp only [step_resp, doResp, find_n hwf hpm, hwfY]
    have hval := hv p.reg hpZ
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, [], by simp [apply_hist], by simp [apply_hist]⟩
    · unfold apply; split <;> simp [hl, hval]
    · simp [apply_pend, hp]
    · simp [apply_cur, hc]
    · simp [apply_cnt, hn]
    · intro b hb
      rw [apply_val, apply_val]
      split
      · exact hv b hb
      · by_cases hbp : b = p.reg
        · subst hbp; simp
        · simp [update_of_ne hbp, hv b hb]

/-! ### The high-level history while one client acts -/

lemma hist_isOf (X : Cfg C B V W L) {c : C} {e : Ev C V} (he : e.IsOf c) :
    ((A.step X e).cur c = X.cur c ∧ (A.step X e).hist = X.hist) ∨
    ((∃ o, X.cur c = some o) ∧ (A.step X e).cur c = none ∧
      ∃ x, (A.step X e).hist = X.hist ++ [.ret c x]) := by
  cases e with
  | inv _ _ => exact he.elim
  | resp d n =>
    subst he
    left
    simp only [step_resp, doResp]
    split
    · simp
    · simp [apply_cur, apply_hist]
  | step d =>
    subst he
    simp only [step_step, doStep]
    split
    · left; simp
    · rename_i x _
      split
      · rename_i o ho
        right; exact ⟨⟨o, ho⟩, by simp, x, rfl⟩
      · left; simp
    · left; simp

/-- While only `c` acts after invoking `o`: either `c` is still busy and the history is unchanged, or
`c` returned once. -/
def _root_.Podc.RegisterEmulationSpace.RetInv (c : C) (o : HOp V) (H : List (HEv C V))
    (X : Cfg C B V W L) : Prop :=
  (X.cur c = some o ∧ X.hist = H) ∨ (X.cur c = none ∧ ∃ x, X.hist = H ++ [.ret c x])

lemma retInv_step {c : C} {o : HOp V} {H : List (HEv C V)} {X : Cfg C B V W L}
    (h : RetInv c o H X) {e : Ev C V} (he : e.IsOf c) : RetInv c o H (A.step X e) := by
  rcases A.hist_isOf X he with ⟨h1, h2⟩ | ⟨⟨o', ho'⟩, h1, x, h2⟩
  · rw [RetInv, h1, h2]; exact h
  · rcases h with ⟨-, h3⟩ | ⟨h3, -⟩
    · exact Or.inr ⟨h1, x, h3 ▸ h2⟩
    · simp [h3] at ho'

lemma retInv_exec {c : C} {o : HOp V} {H : List (HEv C V)} {X : Cfg C B V W L}
    (h : RetInv c o H X) {E : List (Ev C V)} (hE : ∀ e ∈ E, e.IsOf c) :
    RetInv c o H (A.exec X E) := by
  induction E generalizing X with
  | nil => exact h
  | cons e E ih =>
    exact ih (A.retInv_step h (hE e (by simp))) (fun e' he' => hE e' (by simp [he']))

end Alg

end Solo

end Podc.RegisterEmulationSpace
