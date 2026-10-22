import Papers.PODC2016.ReliableStorageSpace.Runs

/-!
# The storage lower bound (Section 4: Corollary 1, Lemma 4, Theorem 2, Corollary 2)

Fix a set `W` of `S` writers and a further client `r` (the reader). The run of `Ad`: the writers invoke
one write each, then `Ad` schedules everything (`R W t`). Assuming that along this run the storage stays
below `S` and `|F(t)| ≤ f`, we derive a contradiction:

* `noReturn` (Corollary 1, via Observation 2 = `reader_restore` and Lemma 3 = `lemma3`): no write returns;
* `rule1_infinitely_often` (Lemma 4): rule 1 of `Ad` (an RMW takes effect and responds) fires infinitely
  often;
* `theorem2`: crashing the objects of the eventual `F(t)` and the clients that receive finitely many
  responses makes the run fair, so lock-freedom forces a write to return.
-/

noncomputable section

namespace Podc.ReliableStorageSpace

open Finset Classical

variable {C N J V : Type}

namespace Alg

variable (A : Alg C N J V) [Fintype C] [Fintype N] [Fintype V]

/-- The writers invoke one write each. -/
def invW (W : Finset C) : List (Event C) := W.toList.map fun c => .inv c .write

omit [Fintype C] [Fintype N] [Fintype V] in
theorem runFrom_invs (X : A.Config) (l : List C) :
    (A.runFrom X (l.map fun c => .inv c .write)).pend = X.pend ∧
    (A.runFrom X (l.map fun c => .inv c .write)).obj = X.obj ∧
    (∀ c, c ∉ l → (A.runFrom X (l.map fun c => .inv c .write)).cur c = X.cur c ∧
      (A.runFrom X (l.map fun c => .inv c .write)).loc c = X.loc c) ∧
    (∀ c, c ∈ l → X.cur c = none → (A.runFrom X (l.map fun c => .inv c .write)).cur c ≠ none) := by
  induction l generalizing X with
  | nil => simp [runFrom]
  | cons d l ih =>
    have hstep : A.runFrom X ((d :: l).map fun c => .inv c .write) =
        A.runFrom (A.step X (.inv d .write)) (l.map fun c => .inv c .write) := rfl
    obtain ⟨h1, h2, h3, h4⟩ := ih (A.step X (.inv d .write))
    rw [hstep]
    by_cases hd : X.cur d = none
    · have hs := step_inv_free (A := A) (op := .write) hd
      refine ⟨by rw [h1, hs], by rw [h2, hs], fun c hc => ?_, fun c hc hcn => ?_⟩
      · have hcd : c ≠ d := fun h => hc (h ▸ List.mem_cons_self ..)
        obtain ⟨h5, h6⟩ := h3 c (fun h => hc (List.mem_cons_of_mem _ h))
        rw [h5, h6, hs]
        simp [Function.update_apply, hcd]
      · by_cases hcl : c ∈ l
        · by_cases hcd : c = d
          · subst hcd
            -- `c` is busy after its invocation; later invocations do not change it
            have key : ∀ (Y : A.Config) (l' : List C), Y.cur c ≠ none →
                (A.runFrom Y (l'.map fun c => .inv c .write)).cur c ≠ none := by
              intro Y l'
              induction l' generalizing Y with
              | nil => intro h; exact h
              | cons d' l' ih' =>
                intro h
                apply ih'
                rcases A.cur_step_cases Y (.inv d' .write) c with h' | ⟨-, -, h', -⟩ | ⟨op, -, h', -⟩
                · rwa [h']
                · cases h'
                · exact absurd h' h
            exact key _ l (by rw [hs]; simp)
          · apply h4 c hcl
            rw [hs]; simp [Function.update_apply, hcd, hcn]
        · have hcd : c = d := by simpa [hcl] using hc
          subst hcd
          rw [(h3 c hcl).1, hs]; simp
    · have hs := step_inv_busy (A := A) (op := .write) hd
      rw [hs] at h1 h2 h3 h4 ⊢
      refine ⟨h1, h2, fun c hc => h3 c (fun h => hc (List.mem_cons_of_mem _ h)), fun c hc hcn => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hcl
      · exact absurd hcn hd
      · exact h4 c hcl hcn

variable [Nonempty C]

/-- The configuration after the writers' invocations. -/
def X₀ (W : Finset C) : A.Config := A.runFrom A.init (invW W)

/-- The run of `Ad`. -/
def adRun (W : Finset C) (t : ℕ) : A.Config := A.srun (A.X₀ W) A.Ad t

theorem adRun_succ (W : Finset C) (t : ℕ) : A.adRun W (t + 1) = A.step (A.adRun W t) (A.Ad (A.adRun W t)) := rfl

theorem adRun_reach (W : Finset C) (t : ℕ) :
    A.runFrom A.init (invW W ++ A.sevs (A.X₀ W) A.Ad t) = A.adRun W t := by
  rw [runFrom_append]
  show A.runFrom (A.X₀ W) (A.sevs (A.X₀ W) A.Ad t) = _
  rw [runFrom_sevs]; rfl

theorem pendOK_adRun (W : Finset C) (t : ℕ) : A.PendOK (A.adRun W t) :=
  A.pendOK_srun (A.pendOK_runFrom A.pendOK_init _) _ t

theorem inv_adRun (W : Finset C) (t : ℕ) : A.Inv (A.adRun W t) :=
  A.inv_srun_Ad (A.pendOK_runFrom A.pendOK_init _)
    (A.inv_runFrom_noExec A.inv_init _ (by simp [invW])) t

theorem curInv_adRun (W : Finset C) (t : ℕ) : A.CurInv (A.adRun W t) :=
  A.curInv_srun (A.curInv_runFrom A.curInv_init _) _ t

theorem Ad_ne_inv (X : A.Config) (c : C) (op : Op) : A.Ad X ≠ .inv c op := by
  rcases A.Ad_cases X with ⟨p, -, -, -, he, -⟩ | ⟨-, he⟩ <;> rw [he] <;> simp

theorem writeOnly_adRun (W : Finset C) (t : ℕ) : A.WriteOnly (A.adRun W t) := by
  induction t with
  | zero =>
    have : ∀ (X : A.Config) (l : List C), A.WriteOnly X →
        A.WriteOnly (A.runFrom X (l.map fun c => .inv c .write)) := by
      intro X l
      induction l generalizing X with
      | nil => exact id
      | cons d l ih => intro h; exact ih _ (A.writeOnly_step h _ (by simp))
    exact this _ _ (fun c => Or.inl (by simp [init]))
  | succ t ih => exact A.writeOnly_step ih _ (fun c => A.Ad_ne_inv _ c .read)

omit [Nonempty C] in
theorem X₀_pend (W : Finset C) : (A.X₀ W).pend = [] := (A.runFrom_invs A.init W.toList).1

omit [Nonempty C] in
theorem X₀_cur_mem (W : Finset C) {c : C} (hc : c ∈ W) : (A.X₀ W).cur c ≠ none :=
  (A.runFrom_invs A.init W.toList).2.2.2 c (by simpa using hc) rfl

/-- The reader is untouched along the run of `Ad`. -/
theorem reader_adRun (W : Finset C) {r : C} (hr : r ∉ W) (t : ℕ) :
    (A.adRun W t).cur r = none ∧ (A.adRun W t).loc r = A.linit r ∧ ∀ p ∈ (A.adRun W t).pend, p.cl ≠ r := by
  induction t with
  | zero =>
    obtain ⟨h1, -, h3, -⟩ := A.runFrom_invs A.init W.toList
    obtain ⟨h4, h5⟩ := h3 r (by simpa using hr)
    refine ⟨h4, h5, fun p hp => ?_⟩
    simp only [adRun, srun, X₀, invW] at hp
    rw [h1] at hp
    simp [init] at hp
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [adRun_succ]
    rcases A.Ad_cases (A.adRun W t) with ⟨p, hp, -, -, he, -⟩ | ⟨-, he⟩ <;> rw [he]
    · rw [step_exec_some ((A.pendOK_adRun W t).findP_eq hp)]
      have hpr := h3 p hp
      refine ⟨h1, by simp [Function.update_apply, Ne.symm hpr, h2], fun q hq => h3 q ?_⟩
      exact List.mem_of_mem_filter hq
    · set c : C := rr (A.adRun W t).tick
      by_cases hcr : c = r
      · rw [hcr, step_step_none h1]; exact ⟨h1, h2, h3⟩
      · rcases hc : (A.adRun W t).cur c with _ | op
        · rw [step_step_none hc]; exact ⟨h1, h2, h3⟩
        · rcases ha : A.act c ((A.adRun W t).cnt c) op ((A.adRun W t).loc c) with ⟨o, rr', l⟩ | l | _
          · rw [step_step_trigger hc ha]
            refine ⟨h1, by simp [Function.update_apply, Ne.symm hcr, h2], fun q hq => ?_⟩
            simp only [List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · exact h3 q hq
            · exact hcr
          · rw [step_step_ret hc ha]
            exact ⟨by simp [Function.update_apply, Ne.symm hcr, h1],
              by simp [Function.update_apply, Ne.symm hcr, h2], h3⟩
          · rw [step_step_idle hc ha]; exact ⟨h1, h2, h3⟩

/-! ### Corollary 1 -/

/-- **Corollary 1**: if `|F(t)| ≤ f` throughout the run of `Ad`, no operation ever returns. -/
theorem noReturn {f : ℕ} {v₀ : V} (hV : 2 ≤ Fintype.card V) (hLF : A.LockFree f)
    (hWR : A.WeakRegular v₀) (W : Finset C) {r : C} (hr : r ∉ W)
    (hF : ∀ t, (A.Full (A.adRun W t)).card ≤ f) (t : ℕ) (c : C) (hc : (A.adRun W t).cur c ≠ none) :
    (A.adRun W (t + 1)).cur c ≠ none := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hD : 0 < D (V := V) := by
    unfold D
    exact Nat.clog_pos (by norm_num) (by omega)
  intro hnone
  rcases A.cur_step_cases (A.adRun W t) (A.Ad (A.adRun W t)) c with h1 | ⟨-, -, -, out, hh⟩ |
    ⟨op, he, -, -⟩
  · rw [← adRun_succ] at h1; exact hc (h1 ▸ hnone)
  · rw [← adRun_succ] at hh
    have hcw : (A.adRun W t).cur c = some .write := by
      rcases A.writeOnly_adRun W t c with h | h
      · exact absurd h hc
      · exact h
    have hinv := A.curInv_adRun W t c .write hcw
    set X := A.adRun W (t + 1)
    have hw : IsWrite X.hist (c, (A.adRun W t).cnt c) := by
      show _ ∈ X.hist
      rw [hh]; exact List.mem_append_left _ hinv
    have hwc : Completed X.hist (c, (A.adRun W t).cnt c) := ⟨out, by rw [hh]; simp⟩
    obtain ⟨hr1, hr2, hr3⟩ := A.reader_adRun W hr (t + 1)
    have hXr := A.adRun_reach W (t + 1)
    obtain ⟨w', -, hw'⟩ := A.reader_restore hLF hWR (invW W ++ A.sevs (A.X₀ W) A.Ad (t + 1)) r
      (by rw [hXr]; exact hr1) (by rw [hXr, hr2, A.linit_blk]) (by rw [hXr]; exact hr3)
      (univ \ A.Full X) (by simpa using hF (t + 1)) _ (by rw [hXr]; exact hw) (by rw [hXr]; exact hwc)
    rw [hXr] at hw'
    have := A.lemma3 (A.inv_adRun W (t + 1)) hD (univ \ A.Full X)
      (fun o ho => (Finset.mem_sdiff.1 ho).2) w'
    omega
  · exact A.Ad_ne_inv _ c op he

/-- Without returns, `cur` is constant along the run of `Ad`. -/
theorem cur_adRun_const (W : Finset C)
    (hnr : ∀ t c, (A.adRun W t).cur c ≠ none → (A.adRun W (t + 1)).cur c ≠ none) (t : ℕ) :
    (A.adRun W t).cur = (A.X₀ W).cur := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext c
    rcases A.cur_step_cases (A.adRun W t) (A.Ad (A.adRun W t)) c with h1 | ⟨h1, h2, -⟩ |
      ⟨op, he, -⟩
    · rw [adRun_succ, h1, ih]
    · exact absurd (by rw [adRun_succ]; exact h1) (hnr t c h2)
    · exact absurd he (A.Ad_ne_inv _ c op)

/-- Rule 1 of `Ad` applies. -/
def Rule1 (X : A.Config) : Prop := ∃ p ∈ X.pend, A.Quiet X p.cl ∧ p.obj ∉ A.Full X

omit [Nonempty C] in
theorem rr_surj [Nonempty C] (τ : ℕ) (c : C) : ∃ d, rr (τ + d) = c := by
  set n := Fintype.card C
  have hn : 0 < n := Fintype.card_pos
  set a := (Fintype.equivFin C c).val
  have ha : a < n := (Fintype.equivFin C c).isLt
  refine ⟨a + n - τ % n, ?_⟩
  have hmod : (τ + (a + n - τ % n)) % n = a := by
    have h1 := Nat.mod_add_div τ n
    have h2 := Nat.mod_lt τ hn
    have : τ + (a + n - τ % n) = a + n * (τ / n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  unfold rr
  rw [Equiv.symm_apply_eq]
  exact Fin.ext hmod

/-- **Lemma 4** (with Theorem 2's counting argument). If the storage stays below `|W|` and `|F(t)| ≤ f`
along the run of `Ad`, then rule 1 of `Ad` (some RMW takes effect and responds) fires infinitely
often. -/
theorem rule1_infinitely_often {f : ℕ} {v₀ : V} (hV : 2 ≤ Fintype.card V) (hLF : A.LockFree f)
    (hWR : A.WeakRegular v₀) (W : Finset C) {r : C} (hr : r ∉ W)
    (hF : ∀ t, (A.Full (A.adRun W t)).card ≤ f) (hS : ∀ t, A.storage (A.adRun W t) < W.card)
    (t : ℕ) : ∃ t' ≥ t, A.Rule1 (A.adRun W t') := by
  have hnr := A.noReturn hV hLF hWR W hr hF
  have hcur := A.cur_adRun_const W hnr
  by_contra hcon
  push Not at hcon
  have hstep : ∀ t' ≥ t, A.Ad (A.adRun W t') = .step (rr (A.adRun W t').tick) := by
    intro t' ht'
    rcases A.Ad_cases (A.adRun W t') with ⟨p, hp, hq, hF', -, -⟩ | ⟨-, he⟩
    · exact absurd ⟨p, hp, hq, hF'⟩ (hcon t' ht')
    · exact he
  have hnoexec : ∀ t' ≥ t, A.NoExec (A.adRun W t') (A.Ad (A.adRun W t')) := by
    intro t' ht' ⟨c, m, p, he, _⟩
    rw [hstep t' ht'] at he
    cases he
  -- a quiet writer
  obtain ⟨c, hcW, hcq⟩ : ∃ c ∈ W, A.Quiet (A.adRun W t) c := by
    by_contra h
    push Not at h
    have := A.obs1 (A.adRun W t) W
    rw [Finset.filter_true_of_mem h] at this
    exact absurd (hS t) (not_lt.2 this)
  have hcw : ∀ t', (A.adRun W t').cur c = some .write := by
    intro t'
    rcases A.writeOnly_adRun W t' c with h | h
    · rw [hcur] at h; exact absurd h (A.X₀_cur_mem W hcW)
    · exact h
  set T := A.Full (A.adRun W t) with hT
  set k := (A.adRun W t).cnt c with hk
  set l₀ := (A.adRun W t).loc c with hl₀
  have hpend₀ : ∀ p ∈ (A.adRun W t).pend, p.cl = c → p.obj ∈ T := by
    intro p hp hpc
    by_contra h
    exact hcon t le_rfl ⟨p, hp, hpc ▸ hcq, h⟩
  have hex : ∃ j, A.Target T (A.act c k .write (A.soloL c k .write l₀ j)) := by
    have := A.solo_progress hLF (invW W ++ A.sevs (A.X₀ W) A.Ad t) c .write T (hF t)
      (by rw [adRun_reach]; exact hcw t) (by rw [adRun_reach]; exact hpend₀)
    rwa [adRun_reach] at this
  -- the invariant while `c` runs without responses
  let P : ℕ → ℕ → Prop := fun i t' =>
    (A.adRun W t').loc c = A.soloL c k .write l₀ i ∧ A.Quiet (A.adRun W t') c ∧
    (∀ p ∈ (A.adRun W t').pend, p.cl = c → p.obj ∈ T) ∧ (A.adRun W t').cnt c = k ∧
    A.Full (A.adRun W t') = T
  have hquiet : ∀ t' ≥ t, A.Quiet (A.adRun W t') c → A.Quiet (A.adRun W (t' + 1)) c := by
    intro t' ht' hq k'
    rw [adRun_succ]
    exact Finset.subset_empty.1 ((hq k') ▸ A.out_noExec (hnoexec t' ht') (c, k'))
  have hfull : ∀ t' ≥ t, A.Full (A.adRun W (t' + 1)) = A.Full (A.adRun W t') := by
    intro t' ht'
    rw [adRun_succ]
    exact A.full_congr (A.obj_eq_of_noExec (hnoexec t' ht'))
  have hother : ∀ i t', t' ≥ t → P i t' → rr (A.adRun W t').tick ≠ c → P i (t' + 1) := by
    intro i t' ht' ⟨h1, h2, h3, h4, h5⟩ hne
    have hs := A.adRun_succ W t'
    rw [hstep t' ht'] at hs
    obtain ⟨hl, hc⟩ := A.step_other (A.adRun W t') hne
    refine ⟨by rw [hs, hl, h1], hquiet t' ht' h2, fun p hp hpc => ?_, by rw [hs, hc, h4],
      by rw [hfull t' ht', h5]⟩
    rw [hs] at hp
    rcases A.pend_step _ _ p hp with hp | ⟨he, -⟩
    · exact h3 p hp hpc
    · simp only [Event.step.injEq] at he
      exact absurd (he.trans hpc) hne
  have hown : ∀ i t', t' ≥ t → P i t' → rr (A.adRun W t').tick = c →
      ¬ A.Target T (A.act c k .write (A.soloL c k .write l₀ i)) → P (i + 1) (t' + 1) := by
    intro i t' ht' ⟨h1, h2, h3, h4, h5⟩ heq hnt
    have hs := A.adRun_succ W t'
    rw [hstep t' ht', heq] at hs
    have hq' := hquiet t' ht' h2
    have hf' := hfull t' ht'
    rw [hs] at hq' hf'
    rcases ha : A.act c k .write (A.soloL c k .write l₀ i) with ⟨o, rr', l⟩ | l | _
    · have ha' : A.act c ((A.adRun W t').cnt c) .write ((A.adRun W t').loc c) = .trigger o rr' l := by
        rw [h1, h4, ha]
      rw [ha] at hnt
      simp only [Target, not_not] at hnt
      rw [step_step_trigger (hcw t') ha'] at hs hq' hf'
      refine ⟨?_, ?_, fun p hp hpc => ?_, ?_, ?_⟩
      · rw [hs]; simp [soloL, ha]
      · rw [hs]; exact hq'
      · rw [hs] at hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact h3 p hp hpc
        · exact hnt
      · rw [hs]; exact h4
      · rw [hs, hf', h5]
    · rw [ha] at hnt; exact absurd trivial hnt
    · have ha' : A.act c ((A.adRun W t').cnt c) .write ((A.adRun W t').loc c) = .idle := by
        rw [h1, h4, ha]
      rw [step_step_idle (hcw t') ha'] at hs hq' hf'
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hs]; simp [soloL, ha, h1]
      · rw [hs]; exact hq'
      · rw [hs]; exact h3
      · rw [hs]; exact h4
      · rw [hs, hf', h5]
  have htarget : ∀ i t', t' ≥ t → P i t' → rr (A.adRun W t').tick = c →
      A.Target T (A.act c k .write (A.soloL c k .write l₀ i)) → False := by
    intro i t' ht' ⟨h1, h2, h3, h4, h5⟩ heq htg
    have hs := A.adRun_succ W t'
    rw [hstep t' ht', heq] at hs
    have hq' := hquiet t' ht' h2
    have hf' := hfull t' ht'
    rw [hs] at hq' hf'
    rcases ha : A.act c k .write (A.soloL c k .write l₀ i) with ⟨o, rr', l⟩ | l | _
    · have ha' : A.act c ((A.adRun W t').cnt c) .write ((A.adRun W t').loc c) = .trigger o rr' l := by
        rw [h1, h4, ha]
      rw [ha] at htg
      simp only [Target] at htg
      rw [step_step_trigger (hcw t') ha'] at hs hq' hf'
      apply hcon (t' + 1) (by omega)
      refine ⟨⟨c, (A.adRun W t').nrmw c, o, rr'⟩, by rw [hs]; simp, by rw [hs]; exact hq', ?_⟩
      rw [hs, hf', h5]; exact htg
    · have ha' : A.act c ((A.adRun W t').cnt c) .write ((A.adRun W t').loc c) = .ret l := by
        rw [h1, h4, ha]
      have := hcw (t' + 1)
      rw [hs, step_step_ret (hcw t') ha'] at this
      simp at this
    · rw [ha] at htg; exact htg
  -- `c` is scheduled again within a round-robin cycle
  have hturn : ∀ i t', t' ≥ t → P i t' → ∃ t'' ≥ t', P i t'' ∧ rr (A.adRun W t'').tick = c := by
    intro i t' ht' hP
    set τ := (A.adRun W t').tick
    have hd : ∃ d, rr (τ + d) = c := rr_surj τ c
    set d := Nat.find hd
    have key : ∀ e ≤ d, P i (t' + e) ∧ (A.adRun W (t' + e)).tick = τ + e := by
      intro e
      induction e with
      | zero => intro _; exact ⟨hP, rfl⟩
      | succ e ih =>
        intro he
        obtain ⟨hP', htk⟩ := ih (by omega)
        have hne : rr (A.adRun W (t' + e)).tick ≠ c := by
          rw [htk]; exact Nat.find_min hd (by omega)
        refine ⟨by rw [← add_assoc]; exact hother i _ (by omega) hP' hne, ?_⟩
        rw [← add_assoc, adRun_succ, tick_step, hstep _ (by omega), htk]
        simp; omega
    obtain ⟨hP', htk⟩ := key d le_rfl
    exact ⟨t' + d, by omega, hP', by rw [htk]; exact Nat.find_spec hd⟩
  set j₀ := Nat.find hex
  have hreach : ∀ i ≤ j₀, ∃ t' ≥ t, P i t' := by
    intro i
    induction i with
    | zero => intro _; exact ⟨t, le_rfl, rfl, hcq, hpend₀, rfl, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨t', ht', hP⟩ := ih (by omega)
      obtain ⟨t'', ht'', hP'', hrr⟩ := hturn i t' ht' hP
      exact ⟨t'' + 1, by omega, hown i t'' (by omega) hP'' hrr (Nat.find_min hex (by omega))⟩
  obtain ⟨t', ht', hP⟩ := hreach j₀ le_rfl
  obtain ⟨t'', ht'', hP'', hrr⟩ := hturn j₀ t' ht' hP
  exact htarget j₀ t'' (by omega) hP'' hrr (Nat.find_spec hex)

/-! ### Theorem 2 -/

theorem full_mono_adRun (W : Finset C) {s s' : ℕ} (h : s ≤ s') :
    A.Full (A.adRun W s) ⊆ A.Full (A.adRun W s') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    refine (ih (by omega)).trans ?_
    rw [← add_assoc, adRun_succ]
    exact A.full_step_Ad (A.pendOK_adRun W _)

/-- **Observation 3**, consequence: `F(t)` is eventually constant (it only grows and has `≤ f`
elements). -/
theorem full_eventually_const (W : Finset C) {f : ℕ} (hF : ∀ t, (A.Full (A.adRun W t)).card ≤ f) :
    ∃ s₁, ∀ s ≥ s₁, A.Full (A.adRun W s) = A.Full (A.adRun W s₁) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k, ∃ s, k ≤ (A.Full (A.adRun W s)).card := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨s', hs', hne⟩ := hcon s
      have hsub := A.full_mono_adRun W hs'
      exact ⟨s', lt_of_lt_of_le' (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨hsub, Ne.symm hne⟩)) hs⟩
  obtain ⟨s, hs⟩ := key (f + 1)
  exact absurd (hF s) (by omega)

/-- Along the run of `Ad` without returns, clients with pending RMWs have outstanding operations. -/
theorem pend_cur_adRun (W : Finset C)
    (hnr : ∀ t c, (A.adRun W t).cur c ≠ none → (A.adRun W (t + 1)).cur c ≠ none) (t : ℕ) :
    ∀ p ∈ (A.adRun W t).pend, (A.adRun W t).cur p.cl ≠ none := by
  have hcur := A.cur_adRun_const W hnr
  induction t with
  | zero => intro p hp; simp [adRun, srun, A.X₀_pend] at hp
  | succ t ih =>
    intro p hp
    rw [hcur, ← hcur t]
    rw [adRun_succ] at hp
    rcases A.pend_step _ _ p hp with hp | ⟨he, -⟩
    · exact ih p hp
    · intro hn
      rw [he, step_step_none hn] at hp
      exact absurd (ih p hp) (by simpa using hn)

/-- A ℕ-valued counter that grows by `0` or `1` per step and grows infinitely often takes every
value from some point on, at a step where it grows. -/
theorem exists_tick {g : ℕ → ℕ} {P : ℕ → Prop}
    (hg : ∀ s, (P s → g (s + 1) = g s + 1) ∧ (¬ P s → g (s + 1) = g s))
    (hinf : ∀ s, ∃ s' ≥ s, P s') (s₀ n : ℕ) : ∃ s ≥ s₀, g s = g s₀ + n ∧ P s := by
  have first : ∀ s₀, ∃ s ≥ s₀, g s = g s₀ ∧ P s := by
    intro s₀
    have hex : ∃ d, P (s₀ + d) := by
      obtain ⟨s', hs', hP⟩ := hinf s₀
      exact ⟨s' - s₀, by rwa [Nat.add_sub_cancel' hs']⟩
    have key : ∀ d ≤ Nat.find hex, g (s₀ + d) = g s₀ := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        rw [← add_assoc, (hg _).2 (Nat.find_min hex (by omega)), ih (by omega)]
    exact ⟨s₀ + Nat.find hex, by omega, key _ le_rfl, Nat.find_spec hex⟩
  induction n with
  | zero => obtain ⟨s, hs, h1, h2⟩ := first s₀; exact ⟨s, hs, by simpa using h1, h2⟩
  | succ n ih =>
    obtain ⟨s, hs, h1, h2⟩ := ih
    obtain ⟨s', hs', h1', h2'⟩ := first (s + 1)
    refine ⟨s', by omega, ?_, h2'⟩
    rw [h1', (hg s).1 h2, h1]; omega

/-- **Theorem 2 of [Spiegelman et al.]**, for the run of `Ad`: with writers `W` and a further client
`r`, for every lock-free weakly regular algorithm, at some time of the run of `Ad` either the storage
is at least `|W|` bits, or more than `f` base objects each store `D` bits of a single write. -/
theorem theorem2_run {f : ℕ} {v₀ : V} (hV : 2 ≤ Fintype.card V) (hLF : A.LockFree f)
    (hWR : A.WeakRegular v₀) (W : Finset C) {r : C} (hr : r ∉ W) :
    ∃ t, W.card ≤ A.storage (A.adRun W t) ∨ f < (A.Full (A.adRun W t)).card := by
  by_contra hcon
  push Not at hcon
  have hF : ∀ t, (A.Full (A.adRun W t)).card ≤ f := fun t => (hcon t).2
  have hS : ∀ t, A.storage (A.adRun W t) < W.card := fun t => (hcon t).1
  have hnr := A.noReturn hV hLF hWR W hr hF
  have hcur := A.cur_adRun_const W hnr
  have hinf := A.rule1_infinitely_often hV hLF hWR W hr hF hS
  -- the full run: the writers' invocations, then `Ad`
  set ev := A.splice (invW W) A.Ad with hev
  set n₀ := (invW W).length
  have hcfg : ∀ s, A.cfg ev (n₀ + s) = A.adRun W s := fun s => A.cfg_splice _ _ s
  have hev_ge : ∀ s, ev (n₀ + s) = A.Ad (A.adRun W s) := fun s => by
    rw [hev, A.splice_ge, A.cfg_splice]; rfl
  have hev_ne_inv : ∀ t ≥ n₀, ∀ c op, ev t ≠ .inv c op := by
    intro t ht c op
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [hev_ge]; exact A.Ad_ne_inv _ c op
  -- rule 1 of `Ad` is an effective execution
  have hrule1 : ∀ s, A.Rule1 (A.adRun W s) → ∃ q ∈ (A.adRun W s).pend,
      ev (n₀ + s) = .exec q.cl q.idx ∧ A.findP (A.cfg ev (n₀ + s)) q.cl q.idx = some q := by
    intro s ⟨p, hp, hq, hpF⟩
    rcases A.Ad_cases (A.adRun W s) with ⟨q, hq', -, -, he, -⟩ | ⟨hno, -⟩
    · exact ⟨q, hq', by rw [hev_ge, he], by rw [hcfg]; exact (A.pendOK_adRun W s).findP_eq hq'⟩
    · exact absurd ⟨hq, hpF⟩ (hno p hp)
  -- responses
  let Resp : ℕ → C → Prop := fun t c =>
    ∃ m p, ev t = .exec c m ∧ A.findP (A.cfg ev t) c m = some p
  set Fc : Finset C := univ.filter (fun c => ∃ T, ∀ t ≥ T, ¬ Resp t c) with hFc
  have hTc : ∀ c, ∃ T, n₀ ≤ T ∧ (c ∈ Fc → ∀ t ≥ T, ¬ Resp t c) := by
    intro c
    by_cases hc : c ∈ Fc
    · obtain ⟨T, hT⟩ := (Finset.mem_filter.1 hc).2
      exact ⟨max T n₀, le_max_right _ _, fun _ t ht => hT t (le_trans (le_max_left _ _) ht)⟩
    · exact ⟨n₀, le_rfl, fun h => absurd h hc⟩
  choose Tc hTc1 hTc2 using hTc
  have hlive : ∀ c, c ∉ Fc → ∀ T, ∃ t ≥ T, Resp t c := by
    intro c hc T
    by_contra h
    push Not at h
    exact hc (Finset.mem_filter.2 ⟨Finset.mem_univ _, T, fun t ht => h t ht⟩)
  -- crashed clients take no steps after their crash time
  let D : ℕ → C → Prop := fun t c => c ∈ Fc ∧ Tc c ≤ t
  let ev' : ℕ → Event C := fun t => if ∃ c, ev t = .step c ∧ D t c then .skip else ev t
  have hsim : ∀ t, A.Rel (D t) (A.cfg ev t) (A.cfg ev' t) := by
    intro t
    induction t with
    | zero => exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, List.Sublist.refl _,
        fun p hp hp' => absurd hp hp'⟩
    | succ t ih =>
      refine (?_ : A.Rel (D t) _ _).mono (fun c ⟨h1, h2⟩ => ⟨h1, by omega⟩)
      show A.Rel (D t) (A.step (A.cfg ev t) (ev t)) (A.step (A.cfg ev' t) (ev' t))
      by_cases hsk : ∃ c, ev t = .step c ∧ D t c
      · obtain ⟨c, hc, hD⟩ := hsk
        have h1 : ev' t = .skip := if_pos ⟨c, hc, hD⟩
        rw [h1, step_skip, hc]
        apply ih.skip hD
        have ht : n₀ ≤ t := le_trans (hTc1 c) hD.2
        obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
        rw [← hc]
        show (A.cfg ev (n₀ + s + 1)).cur c = (A.cfg ev (n₀ + s)).cur c
        rw [show n₀ + s + 1 = n₀ + (s + 1) by omega, hcfg, hcfg, hcur, hcur]
      · have h1 : ev' t = ev t := if_neg hsk
        rw [h1]
        refine ih.step (A.pendOK_cfg ev t) (A.pendOK_cfg ev' t) _ ?_ ?_
        · intro c hc hD; exact hsk ⟨c, hc, hD⟩
        · intro c m p he hp hD
          exact hTc2 c hD.1 t hD.2 ⟨m, p, he, hp⟩
  -- the eventual `F(t)`
  obtain ⟨s₁, hs₁⟩ := A.full_eventually_const W hF
  set Fo := A.Full (A.adRun W s₁) with hFo
  have hev'_exec : ∀ t c m, ev' t = .exec c m → ev t = .exec c m := by
    intro t c m h
    by_cases hsk : ∃ c, ev t = .step c ∧ D t c
    · have : ev' t = .skip := if_pos hsk
      rw [this] at h; cases h
    · rwa [show ev' t = ev t from if_neg hsk] at h
  have hfair : A.Fair f ev' Fc Fo := by
    refine ⟨hF s₁, ?_, ?_, ?_, ?_⟩
    · -- crashed objects: `Ad` never touches `F(t)`
      intro o ho
      refine ⟨n₀ + s₁, fun t ht ⟨c, m, p, he, hp, hpo⟩ => ?_⟩
      have he' := hev'_exec t c m he
      obtain ⟨hp1, hpc, hpm⟩ := findP_spec hp
      have hp2 : A.findP (A.cfg ev t) c m = some p := by
        rw [← hpc, ← hpm]; exact (A.pendOK_cfg ev t).findP_eq ((hsim t).sub.subset hp1)
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show n₀ ≤ t by omega)
      rw [hev_ge] at he'
      rw [hcfg] at hp2
      rcases A.Ad_cases (A.adRun W s) with ⟨q, hq, -, hqF, he'', -⟩ | ⟨-, he''⟩ <;>
        rw [he''] at he'
      · simp only [Event.exec.injEq] at he'
        obtain ⟨rfl, rfl⟩ := he'
        rw [(A.pendOK_adRun W s).findP_eq hq] at hp2
        cases hp2
        rw [hs₁ s (by omega)] at hqF
        exact hqF (hpo ▸ ho)
      · cases he'
    · -- crashed clients
      intro c hc
      refine ⟨Tc c, fun t ht hcl => ?_⟩
      rcases hcl with hcl | ⟨op, hcl⟩
      · by_cases hsk : ∃ c, ev t = .step c ∧ D t c
        · have : ev' t = .skip := if_pos hsk
          rw [this] at hcl; cases hcl
        · rw [show ev' t = ev t from if_neg hsk] at hcl
          exact hsk ⟨c, hcl, hc, ht⟩
      · by_cases hsk : ∃ c, ev t = .step c ∧ D t c
        · have : ev' t = .skip := if_pos hsk
          rw [this] at hcl; cases hcl
        · rw [show ev' t = ev t from if_neg hsk] at hcl
          exact hev_ne_inv t (le_trans (hTc1 c) ht) c op hcl
    · -- correct clients are scheduled infinitely often (round robin)
      intro c hc T
      let P : ℕ → Prop := fun s => ∃ c', A.Ad (A.adRun W s) = .step c'
      have hg : ∀ s, (P s → (A.adRun W (s + 1)).tick = (A.adRun W s).tick + 1) ∧
          (¬ P s → (A.adRun W (s + 1)).tick = (A.adRun W s).tick) := by
        intro s
        rw [adRun_succ, tick_step]
        rcases A.Ad_cases (A.adRun W s) with ⟨q, -, -, -, he, -⟩ | ⟨-, he⟩
        · refine ⟨fun ⟨c', hc'⟩ => ?_, fun _ => ?_⟩
          · rw [he] at hc'; cases hc'
          · rw [he]; rfl
        · exact ⟨fun _ => by rw [he], fun h => absurd ⟨_, he⟩ h⟩
      have hinfP : ∀ s, ∃ s' ≥ s, P s' := by
        intro s
        by_contra h
        push Not at h
        apply A.not_forall_exec ev (n₀ + s)
        intro t ht
        obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le (show n₀ ≤ t by omega)
        rcases A.Ad_cases (A.adRun W s') with ⟨q, hq, -, -, he, -⟩ | ⟨-, he⟩
        · exact ⟨q.cl, q.idx, q, by rw [hev_ge, he],
            by rw [hcfg]; exact (A.pendOK_adRun W s').findP_eq hq⟩
        · exact absurd ⟨_, he⟩ (h s' (by omega))
      obtain ⟨d, hd⟩ := rr_surj (A.adRun W T).tick c
      obtain ⟨s, hs, hgs, hPs⟩ := exists_tick (g := fun s => (A.adRun W s).tick) hg hinfP T d
      have hAd : A.Ad (A.adRun W s) = .step c := by
        rcases A.Ad_cases (A.adRun W s) with ⟨q, -, -, -, he, -⟩ | ⟨-, he⟩
        · obtain ⟨c', hc'⟩ := hPs; rw [he] at hc'; cases hc'
        · rw [he, hgs, hd]
      refine ⟨n₀ + s, by omega, ?_⟩
      have hsk : ¬ ∃ c', ev (n₀ + s) = .step c' ∧ D (n₀ + s) c' := by
        rintro ⟨c', hc', hD⟩
        rw [hev_ge, hAd] at hc'
        cases hc'
        exact hc hD.1
      show (if ∃ c', ev (n₀ + s) = .step c' ∧ D (n₀ + s) c' then .skip else ev (n₀ + s)) = _
      rw [if_neg hsk, hev_ge, hAd]
    · -- RMWs of correct clients on correct objects respond (oldest first)
      intro t p hp hpc hpo
      have hstay_or : ∃ t' ≥ t, p ∉ (A.cfg ev t').pend := by
        by_contra hstay
        push Not at hstay
        set c := p.cl with hc
        let M : ℕ → Finset ℕ := fun t' => (Finset.range p.idx).filter
          (fun i => ∃ q ∈ (A.cfg ev t').pend, q.cl = c ∧ q.idx = i)
        have hMstep : ∀ t' ≥ t, M (t' + 1) ⊆ M t' := by
          intro t' ht' i hi
          simp only [M, Finset.mem_filter, Finset.mem_range] at hi ⊢
          obtain ⟨hi, q, hq, hqc, hqi⟩ := hi
          refine ⟨hi, ?_⟩
          rcases A.pend_step (A.cfg ev t') (ev t') q hq with hq | ⟨-, hqn⟩
          · exact ⟨q, hq, hqc, hqi⟩
          · exfalso
            have : p.idx < (A.cfg ev t').nrmw c := (A.pendOK_cfg ev t').2 p (hstay t' ht')
            rw [hqc] at hqn
            omega
        have hMmono : ∀ t' ≥ t, ∀ d, M (t' + d) ⊆ M t' := by
          intro t' ht' d
          induction d with
          | zero => exact le_rfl
          | succ d ih => exact (hMstep (t' + d) (le_trans ht' (Nat.le_add_right _ _))).trans ih
        set t₂ := max t (n₀ + s₁)
        have hstrict : ∀ t' ≥ t₂, Resp t' c → (M (t' + 1)).card < (M t').card := by
          rintro t' ht' ⟨m, q', he, -⟩
          obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show n₀ ≤ t' by omega)
          rw [hev_ge] at he
          have hsucc : A.cfg ev (n₀ + s + 1) = A.adRun W (s + 1) := by
            rw [show n₀ + s + 1 = n₀ + (s + 1) by omega, hcfg]
          rcases A.Ad_cases (A.adRun W s) with ⟨q, hq, hqq, -, he', as, bs, hpend, has⟩ |
            ⟨-, he'⟩ <;> rw [he'] at he
          · simp only [Event.exec.injEq] at he
            obtain ⟨hqc, -⟩ := he
            have hpX : p ∈ (A.adRun W s).pend := by rw [← hcfg]; exact hstay _ (by omega)
            have hpcand : A.Quiet (A.adRun W s) p.cl ∧ p.obj ∉ A.Full (A.adRun W s) :=
              ⟨by rw [← hc, ← hqc]; exact hqq, by rw [hs₁ s (by omega)]; exact hpo⟩
            have hnext : A.adRun W (s + 1) = A.step (A.adRun W s) (.exec q.cl q.idx) := by
              rw [adRun_succ, he']
            rw [step_exec_some ((A.pendOK_adRun W s).findP_eq hq)] at hnext
            rw [hpend] at hpX
            rcases List.mem_append.1 hpX with hpa | hpb
            · exact absurd hpcand (has p hpa)
            · rcases List.mem_cons.1 hpb with hpq | hpb
              · exfalso
                have := hstay (n₀ + s + 1) (by omega)
                rw [hsucc, hnext, List.mem_filter] at this
                simp [hpq] at this
              · have hlt : q.idx < p.idx := by
                  have hpw := (A.pendOK_adRun W s).1
                  rw [hpend, List.pairwise_append] at hpw
                  exact (List.pairwise_cons.1 hpw.2.1).1 p hpb (by rw [hqc])
                apply Finset.card_lt_card
                refine Finset.ssubset_iff_subset_ne.2 ⟨hMstep _ (by omega), fun heq => ?_⟩
                have hin : q.idx ∈ M (n₀ + s) := by
                  simp only [M, Finset.mem_filter, Finset.mem_range]
                  exact ⟨hlt, q, by rw [hcfg]; exact hq, hqc, rfl⟩
                rw [← heq] at hin
                simp only [M, Finset.mem_filter, Finset.mem_range] at hin
                obtain ⟨-, q'', hq'', hq''c, hq''i⟩ := hin
                rw [hsucc, hnext, List.mem_filter] at hq''
                simp [hq''c, hq''i, hqc] at hq''
          · cases he
        have hdec : ∀ k, ∃ t' ≥ t₂, (M t').card + k ≤ (M t₂).card := by
          intro k
          induction k with
          | zero => exact ⟨t₂, le_rfl, le_rfl⟩
          | succ k ih =>
            obtain ⟨t', ht', hk⟩ := ih
            obtain ⟨t'', ht'', hR⟩ := hlive c hpc t'
            have h1 := hstrict t'' (by omega) hR
            have h2 : M t'' ⊆ M t' := by
              obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht''
              exact hMmono t' (by omega) d
            exact ⟨t'' + 1, by omega, by have := Finset.card_le_card h2; omega⟩
        obtain ⟨t', -, ht'⟩ := hdec ((M t₂).card + 1)
        omega
      obtain ⟨t', ht', hn⟩ := hstay_or
      exact ⟨t', ht', fun h => hn ((hsim t').sub.subset h)⟩
  -- a correct client with an outstanding write
  obtain ⟨cs, hcs⟩ : ∃ c, c ∉ Fc := by
    by_contra h
    push Not at h
    obtain ⟨s, hs, hR1⟩ := hinf (univ.sup Tc)
    obtain ⟨q, -, he, hq⟩ := hrule1 s hR1
    exact hTc2 q.cl (h _) (n₀ + s)
      (le_trans (Finset.le_sup (f := Tc) (Finset.mem_univ _)) (by omega)) ⟨q.idx, q, he, hq⟩
  have hcs_cur : (A.X₀ W).cur cs ≠ none := by
    obtain ⟨t, ht, m, p, -, hp⟩ := hlive cs hcs n₀
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    obtain ⟨hp1, hpc, -⟩ := findP_spec hp
    rw [hcfg] at hp1
    have := A.pend_cur_adRun W hnr s p hp1
    rwa [hpc, hcur] at this
  have h0 : A.cfg ev n₀ = A.adRun W 0 := by simpa using hcfg 0
  obtain ⟨t', ht', c', hret1, hret2⟩ := hLF ev' Fc Fo hfair n₀ cs hcs (by
    rw [(hsim n₀).cur, h0, hcur]; exact hcs_cur)
  rw [(hsim t').cur] at hret1
  rw [(hsim (t' + 1)).cur] at hret2
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht'
  rw [hcfg] at hret1
  rw [show n₀ + s + 1 = n₀ + (s + 1) by omega, hcfg] at hret2
  exact hnr s c' hret1 hret2

omit [Nonempty C] in
/-- **Theorem 2 of [Spiegelman et al.]**: for every `S`, if there are more than `S` clients, every
lock-free, weakly regular MWMR register emulation (in the black-box storage model, with at most `f`
crashed base objects) has a reachable configuration in which the storage is at least `S` bits, or in
which more than `f` base objects each store `D = ⌈log₂ |V|⌉` bits of a single write. -/
theorem theorem2 {f S : ℕ} {v₀ : V} (hV : 2 ≤ Fintype.card V) (hC : S + 1 ≤ Fintype.card C)
    (hLF : A.LockFree f) (hWR : A.WeakRegular v₀) :
    ∃ X, A.Reachable X ∧ (S ≤ A.storage X ∨ f < (A.Full X).card) := by
  haveI : Nonempty C := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨r⟩ := (inferInstance : Nonempty C)
  obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq (s := univ.erase r) (n := S)
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega)
  have hr : r ∉ W := fun h => (Finset.mem_erase.1 (hW h)).1 rfl
  obtain ⟨t, ht⟩ := A.theorem2_run hV hLF hWR W hr
  exact ⟨A.adRun W t, ⟨_, (A.adRun_reach W t).symm⟩, hWc ▸ ht⟩

omit [Nonempty C] in
/-- **Corollary 2 of [Spiegelman et al.]**: a lock-free weakly regular MWMR register emulation whose
storage is bounded by `S` (with more than `S` clients) reaches a configuration in which `f + 1` base
objects each store `D` bits of a single write, so the base objects store at least `(f + 1) D` bits. -/
theorem corollary2 {f S : ℕ} {v₀ : V} (hV : 2 ≤ Fintype.card V) (hC : S + 1 ≤ Fintype.card C)
    (hLF : A.LockFree f) (hWR : A.WeakRegular v₀) (hbound : ∀ X, A.Reachable X → A.storage X < S) :
    ∃ X, A.Reachable X ∧ f + 1 ≤ (A.Full X).card ∧ (f + 1) * D (V := V) ≤ A.objBits X := by
  obtain ⟨X, hX, h⟩ := A.theorem2 hV hC hLF hWR
  have hF : f + 1 ≤ (A.Full X).card := by
    rcases h with h | h
    · exact absurd (hbound X hX) (not_lt.2 h)
    · omega
  refine ⟨X, hX, hF, ?_⟩
  calc (f + 1) * D (V := V) ≤ (A.Full X).card * D (V := V) := Nat.mul_le_mul_right _ hF
    _ = ∑ o ∈ A.Full X, D (V := V) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ o ∈ A.Full X, A.bits (A.oblk (X.obj o)) := by
      apply Finset.sum_le_sum
      intro o ho
      simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at ho
      obtain ⟨w, hw⟩ := ho
      exact le_trans hw (A.bits_mono (Finset.filter_subset _ _))
    _ ≤ A.objBits X := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end Alg

end Podc.ReliableStorageSpace

end
