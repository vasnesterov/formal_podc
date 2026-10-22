import Papers.PODC2014.AbstractMACConsensus.ValidSteps

/-!
# Theorem 3.2: no 1-crash-tolerant consensus with an abstract MAC layer (single hop)

Newport, *Consensus with an abstract MAC layer*, PODC 2014, Section 3.1.

We follow the paper's proof (Lynch's version of FLP), with valencies defined over *crash-free*
extensions by valid steps (`Val`). The paper's case analysis of Lemma 3.1 is replaced by the
uniform statement `stepV_comm` (the two orders agree off one node `w`) plus one crash argument
(`exists_decision_off`): crash `w`, let the others run fairly, and transfer the decision to a
crash-free extension in which `w` is silent (`Rel`).

* `lemma_3_1`: Lemma 3.1.
* `exists_bivalent_init`: a bivalent initial configuration (FLP's Lemma 2).
* `theorem_3_2`: no algorithm solves consensus on a clique of `n ≥ 2` nodes tolerating one crash.
* `theorem_3_2_card_one`: the hypothesis `n ≥ 2` (missing in the paper) is needed.
-/

namespace Podc.AbstractMACConsensus

open Cslib.AbstractMAC Filter

variable {I M S V : Type*} [DecidableEq V] [Fintype V] (A : Algorithm I M S) (id : V → I)

/-- Crash-free configurations reachable by valid steps from an initial configuration. -/
def Reach (c : Config V M S) : Prop :=
  ∃ inp vs, c = runV A (Config.init A id inp) vs

/-- `b` is a possible decision from `c` (some crash-free valid extension has a node deciding `b`). -/
def Val (c : Config V M S) (b : Bool) : Prop :=
  ∃ vs x, ((runV A c vs).loc x).dec = some b

/-- Bivalent configurations. -/
def Biv (c : Config V M S) : Prop := Val A c true ∧ Val A c false

variable {A id}

omit [Fintype V] in
lemma Reach.runV {c : Config V M S} (h : Reach A id c) (vs : List V) :
    Reach A id (runV A c vs) := by
  obtain ⟨inp, ws, rfl⟩ := h
  exact ⟨inp, ws ++ vs, by rw [runV_append]⟩

omit [Fintype V] in
lemma Reach.stepV {c : Config V M S} (h : Reach A id c) (u : V) :
    Reach A id (stepV A c u) := h.runV [u]

omit [Fintype V] in
lemma Reach.down {c : Config V M S} (h : Reach A id c) : c.down = ∅ := by
  obtain ⟨inp, ws, rfl⟩ := h
  rw [runV_down]; rfl

omit [Fintype V] in
lemma Val.of_runV {c : Config V M S} {vs : List V} {b : Bool} (h : Val A (runV A c vs) b) :
    Val A c b := by
  obtain ⟨ws, x, hx⟩ := h
  exact ⟨vs ++ ws, x, by rw [runV_append]; exact hx⟩

omit [Fintype V] in
lemma Val.of_stepV {c : Config V M S} {u : V} {b : Bool} (h : Val A (stepV A c u) b) :
    Val A c b := Val.of_runV (vs := [u]) h

/-! ### Executions made of valid steps -/

variable (A) in
/-- The execution from `c₀`: first the valid steps `vs` followed by the events `extra` (e.g. a
crash), then forever rounds of valid steps of the nodes `ℓ`. -/
noncomputable def flpSched (c₀ : Config V M S) (vs : List V) (extra : List (Event V))
    (ℓ : List V) : ℕ → List (Event V) :=
  stratSched A ⊤ (fun j c => if j = 0 then eventsV A c vs ++ extra else eventsV A c ℓ) c₀

section Exec

variable {c₀ : Config V M S} {vs : List V} {extra : List (Event V)} {ℓ : List V}

omit [Fintype V] in
lemma flpSched_one :
    run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) 1 = extra.foldl (step A ⊤) (runV A c₀ vs) := by
  rw [flpSched, run_stratSched]
  simp [stratCfg, List.foldl_append, foldl_eventsV]

omit [Fintype V] in
lemma flpSched_block (j : ℕ) :
    flpSched A c₀ vs extra ℓ (j + 1) = eventsV A (run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) (j + 1)) ℓ := by
  rw [flpSched, stratSched, ← run_stratSched]; simp

omit [Fintype V] in
lemma flpSched_succ (j : ℕ) :
    run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) (j + 2) =
      runV A (run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) (j + 1)) ℓ := by
  rw [run_succ, flpSched_block, foldl_eventsV]

omit [Fintype V] in
lemma flpSched_eq (j : ℕ) : ∃ L : List V, (∀ v ∈ L, v ∈ ℓ) ∧
    run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) (j + 1) =
      runV A (run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) 1) L := by
  induction j with
  | zero => exact ⟨[], by simp, rfl⟩
  | succ j ih =>
    obtain ⟨L, hL, he⟩ := ih
    refine ⟨L ++ ℓ, fun v hv => ?_, by rw [flpSched_succ, he, runV_append]⟩
    rcases List.mem_append.1 hv with h | h
    · exact hL v h
    · exact h

omit [Fintype V] in
lemma flpSched_down (j : ℕ) :
    (run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) (j + 1)).down =
      (run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) 1).down := by
  obtain ⟨L, -, he⟩ := flpSched_eq (A := A) (c₀ := c₀) (vs := vs) (extra := extra) (ℓ := ℓ) j
  rw [he, runV_down]

lemma flpSched_fair
    (hℓ : ∀ u, u ∉ (run A ⊤ c₀ (flpSched A c₀ vs extra ℓ) 1).down → u ∈ ℓ) :
    Fair A ⊤ c₀ (flpSched A c₀ vs extra ℓ) := by
  refine fair_of_blocks A c₀ _ 1 (fun _ => ℓ) (fun j hj => ?_) (fun j hj u hu => ?_)
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact flpSched_block k
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact hℓ u (by rwa [flpSched_down] at hu)

/-- Applying the consensus hypothesis to such an execution. -/
lemma flpSched_consensus {f : ℕ} (H : SolvesConsensus A ⊤ id f) (inp : V → Bool)
    (hℓ : ∀ u, u ∉ (run A ⊤ (Config.init A id inp)
      (flpSched A (Config.init A id inp) vs extra ℓ) 1).down → u ∈ ℓ)
    (hf : (run A ⊤ (Config.init A id inp)
      (flpSched A (Config.init A id inp) vs extra ℓ) 1).down.encard ≤ f) :
    Agreement A ⊤ (Config.init A id inp) (flpSched A (Config.init A id inp) vs extra ℓ) ∧
      Validity A ⊤ inp (Config.init A id inp) (flpSched A (Config.init A id inp) vs extra ℓ) ∧
      Termination A ⊤ (Config.init A id inp) (flpSched A (Config.init A id inp) vs extra ℓ) := by
  obtain ⟨T, hT, hT'⟩ := (flpSched_fair hℓ).exists_timely
  refine H inp _ T 2 hT hT' fun i => ?_
  cases i with
  | zero => simp [Config.init]
  | succ i => rw [flpSched_down]; exact hf

end Exec

/-! ### Consequences of the consensus hypothesis -/

section Facts

variable [Nonempty V] {f : ℕ} (H : SolvesConsensus A ⊤ id f)
include H

/-- Every reachable configuration has a possible decision. -/
lemma exists_val {c : Config V M S} (hc : Reach A id c) : ∃ b, Val A c b := by
  obtain ⟨inp, vs, rfl⟩ := hc
  obtain ⟨-, -, hT⟩ := flpSched_consensus (vs := vs) (extra := []) (ℓ := Finset.univ.toList) H inp
    (by simp) (by rw [flpSched_one]; simp [runV_down, Config.init])
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨i, hi⟩ := hT x (fun i => by
    cases i with
    | zero => simp [Config.init]
    | succ i => rw [flpSched_down, flpSched_one]; simp [runV_down, Config.init])
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hi
  have hb' := (mono_run A ⊤ x _ _ (Nat.le_succ i)).dec_eq b hb
  obtain ⟨L, -, he⟩ := flpSched_eq (A := A) (c₀ := Config.init A id inp) (vs := vs) (extra := [])
    (ℓ := Finset.univ.toList) i
  rw [he, flpSched_one] at hb'
  exact ⟨b, L, x, hb'⟩

omit [Nonempty V] in
/-- Agreement inside one crash-free reachable configuration. -/
lemma agree {c : Config V M S} (hc : Reach A id c) {x y : V} {b b' : Bool}
    (hx : (c.loc x).dec = some b) (hy : (c.loc y).dec = some b') : b = b' := by
  obtain ⟨inp, vs, rfl⟩ := hc
  obtain ⟨hA, -, -⟩ := flpSched_consensus (vs := vs) (extra := []) (ℓ := Finset.univ.toList) H inp
    (by simp) (by rw [flpSched_one]; simp [runV_down, Config.init])
  exact hA 1 1 x y b b' (by rw [flpSched_one]; exact hx) (by rw [flpSched_one]; exact hy)

omit [Nonempty V] in
/-- Validity inside one crash-free reachable configuration. -/
lemma valid {inp : V → Bool} {vs : List V} {x : V} {b : Bool}
    (hx : ((runV A (Config.init A id inp) vs).loc x).dec = some b) : ∃ w, inp w = b := by
  obtain ⟨-, hV, -⟩ := flpSched_consensus (vs := vs) (extra := []) (ℓ := Finset.univ.toList) H inp
    (by simp) (by rw [flpSched_one]; simp [runV_down, Config.init])
  exact hV 1 x b (by rw [flpSched_one]; exact hx)

omit [Nonempty V] in
/-- Once a node decided `b`, `!b` is no longer a possible decision. -/
lemma not_val_of_dec {c : Config V M S} (hc : Reach A id c) {x : V} {b : Bool}
    (hx : (c.loc x).dec = some b) : ¬ Val A c (!b) := by
  rintro ⟨vs, y, hy⟩
  have hx' := (mono_runV A x c vs).dec_eq b hx
  have := agree H (hc.runV vs) hx' hy
  cases b <;> simp at this

end Facts

/-- **The crash argument.** From a reachable configuration, crash `w` and run the others fairly:
by termination some node `x ≠ w` decides; the same valid steps (with `w` silent instead of
crashed) give a crash-free extension in which `x` decided. -/
lemma exists_decision_off (H : SolvesConsensus A ⊤ id 1) (hV : 2 ≤ Fintype.card V)
    {c : Config V M S} (hc : Reach A id c) (w : V) :
    ∃ L : List V, w ∉ L ∧ ∃ x b, x ≠ w ∧ ((runV A c L).loc x).dec = some b := by
  obtain ⟨inp, vs, rfl⟩ := hc
  set ℓ := (Finset.univ.erase w).toList
  have hdown1 : (run A ⊤ (Config.init A id inp)
      (flpSched A (Config.init A id inp) vs [.crash w] ℓ) 1).down = {w} := by
    rw [flpSched_one]; simp [step, runV_down, Config.init]
  obtain ⟨-, -, hT⟩ := flpSched_consensus (vs := vs) (extra := [.crash w]) (ℓ := ℓ) H inp
    (fun u hu => by rw [hdown1] at hu; simpa [ℓ] using hu) (by rw [hdown1]; simp)
  obtain ⟨x, hxw⟩ : ∃ x, x ≠ w := by
    by_contra h; push Not at h
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
    omega
  obtain ⟨i, hi⟩ := hT x (fun i => by
    cases i with
    | zero => simp [Config.init]
    | succ i => rw [flpSched_down, hdown1]; simpa using hxw)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hi
  have hb' := (mono_run A ⊤ x _ _ (Nat.le_succ i)).dec_eq b hb
  obtain ⟨L, hL, he⟩ := flpSched_eq (A := A) (c₀ := Config.init A id inp) (vs := vs)
    (extra := [.crash w]) (ℓ := ℓ) i
  rw [he, flpSched_one] at hb'
  have hwL : w ∉ L := fun h => by simpa [ℓ] using hL w h
  refine ⟨L, hwL, x, b, hxw, ?_⟩
  have hrel : Rel w ([Event.crash w].foldl (step A ⊤) (runV A (Config.init A id inp) vs))
      (runV A (Config.init A id inp) vs) :=
    ⟨rfl, fun _ _ => rfl, fun y hy => by simp [step, hy]⟩
  rw [← (hrel.runV A L hwL).loc x hxw]
  exact hb'

/-! ### Lemma 3.1 -/

section Lemma31

variable (H : SolvesConsensus A ⊤ id 1) (hV : 2 ≤ Fintype.card V)
include H hV

omit [DecidableEq V] H in
private lemma nonempty_of_two : Nonempty V := by
  rw [← Fintype.card_pos_iff]; omega

/-- Univalent configurations. -/
private def Uni (c : Config V M S) (b : Bool) : Prop := Val A c b ∧ ¬ Val A c (!b)

private lemma exists_uni {c : Config V M S} (hc : Reach A id c) (hb : ¬ Biv A c) :
    ∃ b, Uni (A := A) c b := by
  have := nonempty_of_two hV
  obtain ⟨b, hb'⟩ := exists_val H hc
  refine ⟨b, hb', fun h => hb ?_⟩
  cases b
  · exact ⟨h, hb'⟩
  · exact ⟨hb', h⟩

/-- **Lemma 3.1.** From a bivalent reachable configuration, for every node `u` there is a valid
extension after which the valid step of `u` leads to a bivalent configuration. -/
theorem lemma_3_1 {c : Config V M S} (hc : Reach A id c) (hb : Biv A c) (u : V) :
    ∃ vs, Biv A (stepV A (runV A c vs) u) := by
  classical
  have := nonempty_of_two hV
  by_contra hcon
  push Not at hcon
  have huni : ∀ vs, ∃ b, Uni (A := A) (stepV A (runV A c vs) u) b := fun vs =>
    exists_uni H hV ((hc.runV vs).stepV u) (hcon vs)
  obtain ⟨b0, hb0⟩ := huni []
  -- a crash-free extension in which `!b0` is decided
  obtain ⟨ws, x, hx⟩ : Val A c (!b0) := by cases b0 <;> simp [hb.1, hb.2]
  -- along `ws`, the valency of the `u`-step changes from `b0` to `!b0`
  have hend : ¬ Uni (A := A) (stepV A (runV A c ws) u) b0 := by
    rintro ⟨h1, -⟩
    obtain ⟨vs', y, hy⟩ := h1
    have hx' := (mono_runV A x _ (u :: vs')).dec_eq _ hx
    rw [← runV_cons] at hy
    have := agree H ((hc.runV ws).runV (u :: vs')) hx' hy
    cases b0 <;> simp at this
  have hex : ∃ k, ¬ Uni (A := A) (stepV A (runV A c (ws.take k)) u) b0 :=
    ⟨ws.length, by rwa [List.take_length]⟩
  set k := Nat.find hex
  have hk : ¬ Uni (A := A) (stepV A (runV A c (ws.take k)) u) b0 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0; apply hk; rw [h0]; simpa using hb0
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hprev : Uni (A := A) (stepV A (runV A c (ws.take k')) u) b0 := by
    by_contra h; exact Nat.find_min hex (by omega) h
  have hklt : k' < ws.length := by
    by_contra hlt
    apply hk
    rw [hk', List.take_of_length_le (by omega)]
    rwa [List.take_of_length_le (by omega)] at hprev
  set d := runV A c (ws.take k')
  set v := ws[k']
  have hd' : runV A c (ws.take k) = stepV A d v := by
    rw [hk', List.take_add_one, List.getElem?_eq_getElem hklt, Option.toList_some, runV_append]
    rfl
  have hdR : Reach A id d := hc.runV _
  obtain ⟨b1, hb1⟩ := huni (ws.take k)
  have hb1' : b1 = !b0 := by
    cases b0 <;> cases b1 <;> simp_all
  rw [hb1', hd'] at hb1
  -- now `stepV d u` is `b0`-valent and `stepV (stepV d v) u` is `!b0`-valent
  have hdown := hdR.down
  have contra_ext : ∀ e : Config V M S, Uni (A := A) e b0 → ∀ vs, ¬ Uni (A := A) (runV A e vs) (!b0) :=
    fun e he vs h => he.2 (Val.of_runV h.1)
  by_cases hul : (d.loc u).cur.isSome
  swap
  · have : stepV A d u = d := stepV_of_not_live A (Or.inr (by simpa using hul))
    rw [this] at hprev
    exact contra_ext d hprev [v, u] hb1
  by_cases hvu : v = u
  · rw [hvu] at hb1
    exact contra_ext _ hprev [u] hb1
  by_cases hvl : (d.loc v).cur.isSome
  swap
  · have : stepV A d v = d := stepV_of_not_live A (Or.inr (by simpa using hvl))
    rw [this] at hb1
    cases b0 <;> simp_all [Uni]
  obtain ⟨w, hw⟩ := stepV_comm A (Ne.symm hvu) hdown hul hvl
  obtain ⟨L, hwL, y, b, hyw, hy⟩ := exists_decision_off H hV ((hdR.stepV v).stepV u) w
  have h1 : Val A (stepV A (stepV A d v) u) b := ⟨L, y, hy⟩
  have h2 : Val A (stepV A d u) b :=
    Val.of_stepV ⟨L, y, by rw [← (hw.runV A L hwL).loc y hyw]; exact hy⟩
  have e1 : b = !b0 := by
    cases b0 <;> cases b <;> first | rfl | (exfalso; exact hb1.2 (by simpa using h1))
  have e2 : b = b0 := by
    cases b0 <;> cases b <;> first | rfl | (exfalso; exact hprev.2 (by simpa using h2))
  rw [e1] at e2
  cases b0 <;> simp at e2

/-- **FLP's Lemma 2.** Some initial configuration is bivalent. -/
theorem exists_bivalent_init : ∃ inp : V → Bool, Biv A (Config.init A id inp) := by
  classical
  have := nonempty_of_two hV
  by_contra hcon
  push Not at hcon
  have hR : ∀ inp, Reach A id (Config.init A id inp) := fun inp => ⟨inp, [], rfl⟩
  -- the initial configuration with input `true` exactly on `S` is `false`-univalent
  have key : ∀ S : Finset V, Uni (A := A) (Config.init A id fun v => decide (v ∈ S)) false := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨b, hb⟩ := exists_val H (hR fun v => decide (v ∈ (∅ : Finset V)))
      obtain ⟨vs, x, hx⟩ := hb
      obtain ⟨w, hw⟩ := valid H hx
      simp at hw
      subst hw
      refine ⟨⟨vs, x, hx⟩, ?_⟩
      rintro ⟨vs', y, hy⟩
      obtain ⟨w', hw'⟩ := valid H hy
      simp at hw'
    | insert a S haS ih =>
      obtain ⟨b, hb⟩ := exists_uni H hV (hR _) (hcon _)
      cases b
      · exact hb
      · exfalso
        have hrel : Rel a (Config.init A id fun v => decide (v ∈ insert a S))
            (Config.init A id fun v => decide (v ∈ S)) :=
          ⟨rfl, fun x hx => by simp [Config.init, hx], fun _ _ => Iff.rfl⟩
        obtain ⟨L, haL, y, b', hya, hy⟩ := exists_decision_off H hV (hR _) a
        have h1 : Val A (Config.init A id fun v => decide (v ∈ S)) b' := ⟨L, y, hy⟩
        have h2 : Val A (Config.init A id fun v => decide (v ∈ insert a S)) b' :=
          ⟨L, y, by rw [(hrel.runV A L haL).loc y hya]; exact hy⟩
        cases b'
        · exact hb.2 h2
        · exact ih.2 h1
  obtain ⟨vs, x, hx⟩ := (key Finset.univ).1
  obtain ⟨w, hw⟩ := valid H hx
  simp at hw

end Lemma31

/-- **Theorem 3.2.** No deterministic algorithm solves consensus in a single-hop network (clique)
of `n ≥ 2` nodes in the abstract MAC layer model, if one node may crash. -/
theorem theorem_3_2 (A : Algorithm I M S) (id : V → I) (hV : 2 ≤ Fintype.card V) :
    ¬ SolvesConsensus A ⊤ id 1 := by
  classical
  intro H
  have := nonempty_of_two hV
  obtain ⟨inp, hbi⟩ := exists_bivalent_init H hV
  -- one round of Lemma 3.1 for every node
  have round : ∀ (us : List V) (c : Config V M S), Reach A id c → Biv A c →
      ∃ L, (∀ u ∈ us, u ∈ L) ∧ Biv A (runV A c L) := by
    intro us
    induction us with
    | nil => intro c _ hb; exact ⟨[], by simp, hb⟩
    | cons u us ih =>
      intro c hc hb
      obtain ⟨vs, hvs⟩ := lemma_3_1 H hV hc hb u
      have hc' : Reach A id (stepV A (runV A c vs) u) := (hc.runV vs).stepV u
      obtain ⟨L, hL, hbL⟩ := ih _ hc' hvs
      refine ⟨vs ++ [u] ++ L, fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · simp
        · simp [hL x hx]
      · rwa [runV_append, runV_append]
  have hround := round Finset.univ.toList
  let nextL : Config V M S → List V := fun c =>
    if h : Reach A id c ∧ Biv A c then (hround c h.1 h.2).choose else []
  have hnext : ∀ c, Reach A id c → Biv A c →
      (∀ u, u ∈ nextL c) ∧ Biv A (runV A c (nextL c)) := by
    intro c hc hb
    simp only [nextL, dite_eq_left_of_eq_true (eq_true (And.intro hc hb))]
    obtain ⟨h1, h2⟩ := (hround c hc hb).choose_spec
    exact ⟨fun u => h1 u (by simp), h2⟩
  let c₀ := Config.init A id inp
  let σ := stratSched A ⊤ (fun _ c => eventsV A c (nextL c)) c₀
  have hrun : ∀ j, run A ⊤ c₀ σ (j + 1) = runV A (run A ⊤ c₀ σ j) (nextL (run A ⊤ c₀ σ j)) := by
    intro j; simp only [σ, run_stratSched, stratCfg, foldl_eventsV]
  have hinv : ∀ j, Reach A id (run A ⊤ c₀ σ j) ∧ Biv A (run A ⊤ c₀ σ j) := by
    intro j
    induction j with
    | zero => exact ⟨⟨inp, [], rfl⟩, hbi⟩
    | succ j ih => rw [hrun]; exact ⟨ih.1.runV _, (hnext _ ih.1 ih.2).2⟩
  have hfair : Fair A ⊤ c₀ σ :=
    fair_of_blocks A c₀ σ 0 (fun j => nextL (run A ⊤ c₀ σ j))
      (fun j _ => by simp only [σ, stratSched, run_stratSched])
      (fun j _ u _ => (hnext _ (hinv j).1 (hinv j).2).1 u)
  obtain ⟨T, hT, hT'⟩ := hfair.exists_timely
  obtain ⟨-, -, hterm⟩ := H inp σ T 2 hT hT' (fun i => by rw [(hinv i).1.down]; simp)
  have x : V := Classical.ofNonempty
  obtain ⟨i, hi⟩ := hterm x (fun i => by rw [(hinv i).1.down]; simp)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hi
  have hbiv := (hinv i).2
  apply not_val_of_dec H (hinv i).1 hb
  cases b
  · exact hbiv.1
  · exact hbiv.2


omit [Fintype V] in
/-- The hypothesis `n ≥ 2` of Theorem 3.2 (implicit in the paper) is needed: with a single node,
deciding one's own input solves consensus, even with crashes. -/
theorem theorem_3_2_card_one [Subsingleton V] (id : V → I) (f : ℕ) :
    ∃ A : Algorithm I Unit Bool, SolvesConsensus A ⊤ id f := by
  refine ⟨⟨fun _ b => b, fun s _ => s, fun s => s, fun _ => none, some⟩, ?_⟩
  intro inp σ T F _ _ _
  set A : Algorithm I Unit Bool := ⟨fun _ b => b, fun s _ => s, fun s => s, fun _ => none, some⟩
  have hdec : ∀ i u, ((run A ⊤ (Config.init A id inp) σ i).loc u).dec = some (inp u) :=
    fun i u => (mono_run A ⊤ u _ σ (Nat.zero_le i)).dec_eq _ rfl
  refine ⟨fun i j u v b b' hb hb' => ?_, fun i u b hb => ⟨u, ?_⟩, fun u _ => ⟨0, rfl⟩⟩
  · rw [hdec, Subsingleton.elim u v] at hb; rw [hdec] at hb'
    exact (Option.some.inj hb).symm.trans (Option.some.inj hb')
  · rw [hdec] at hb; exact Option.some.inj hb

end Podc.AbstractMACConsensus
