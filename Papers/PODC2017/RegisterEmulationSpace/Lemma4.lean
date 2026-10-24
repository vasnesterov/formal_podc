import Papers.PODC2017.RegisterEmulationSpace.Runs

/-!
# The indistinguishability argument of Lemma 4

Core of Lemma 4 of the paper (Appendix C), in the form we use: let `X₀` be the configuration after a
sequential run (all clients idle) and let a new writer `a` perform a complete write of a value
`v ≠` (the current value), with only `a` taking steps and only `a`'s operations responding. Then the
registers that are not covered at `X₀` and whose value changed span more than `f` servers.

Proof (as in the paper): otherwise crash these `≤ f` servers. Let the covering writes pending at `X₀`
take effect (one per covered register, `flush`), both after `X₀` (run `r'`) and after `a`'s write
(run `r''`), and run a reader solo. Both configurations agree on the reader and on every register of a
correct server, so the reader returns the same value in both runs (`SoloRel`), it returns by obstruction
freedom, and sequential safety forces the old value in `r'` and `v` in `r''`.

Unlike the paper's Lemma 4 we do not need the adversary here: the statement holds for every schedule
of `a`'s write in which only `a` acts.
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace

variable {C B V W L S : Type*} [DecidableEq C] [DecidableEq B] [DecidableEq S]

open Function

lemma seqHist_append (l₁ l₂ : List (C × HOp V × V)) :
    seqHist (l₁ ++ l₂) = seqHist l₁ ++ seqHist l₂ := by
  simp [seqHist]

@[simp] lemma seqHist_singleton (c : C) (o : HOp V) (x : V) :
    seqHist [(c, o, x)] = [.inv c o, .ret c x] := rfl

lemma lastVal_append_write (v₀ : V) (L : List (C × HOp V × V)) (c : C) (v x : V) :
    lastVal v₀ (L ++ [(c, .write v, x)]) = v := by
  simp [lastVal, List.foldl_append]

/-- The event is a response event. -/
def Ev.IsResp {C V : Type*} : Ev C V → Prop
  | .resp _ _ => True
  | _ => False

namespace Alg

variable (A : Alg C B V W L)

lemma exec_resp_cur_hist (X : Cfg C B V W L) {E : List (Ev C V)} (hE : ∀ e ∈ E, e.IsResp) :
    (A.exec X E).cur = X.cur ∧ (A.exec X E).hist = X.hist := by
  induction E generalizing X with
  | nil => simp
  | cons e E ih =>
    obtain ⟨h1, h2⟩ := ih (A.step X e) (fun e' he' => hE e' (by simp [he']))
    simp only [exec_cons, h1, h2]
    have he := hE e (by simp)
    cases e with
    | inv _ _ => exact he.elim
    | step _ => exact he.elim
    | resp c n =>
      simp only [step_resp, doResp]
      split
      · simp
      · simp [apply_cur, apply_hist]

lemma apply_write (X : Cfg C B V W L) (c : C) (p : POp B W) {w : W} (h : p.op = .write w) :
    A.apply X c p = { X with pend := update X.pend c ((X.pend c).filter (fun q => q.n ≠ p.n)),
                             loc := update X.loc c (A.recv c (X.loc c) p none),
                             val := update X.val p.reg w } := by
  unfold apply; split <;> simp_all

/-- Flushing one pending write per register of `l` keeps two configurations related. -/
lemma flush_rel {a : C} {D : Finset S} {δ : B → S} (cb : B → C) (pb : B → POp B W) :
    ∀ (l : List B), l.Nodup → ∀ {X Y : Cfg C B V W L}, WF X → WF Y →
    (∀ b ∈ l, pb b ∈ X.pend (cb b) ∧ cb b ≠ a ∧ (pb b).reg = b ∧ (pb b).op.IsWrite) →
    (∀ c ≠ a, X.pend c = Y.pend c ∧ X.loc c = Y.loc c ∧ X.cur c = Y.cur c ∧ X.cnt c = Y.cnt c) →
    (∀ b, δ b ∉ D → b ∉ l → X.val b = Y.val b) →
    (∀ c ≠ a, (A.exec X (l.map fun b => .resp (cb b) (pb b).n)).pend c =
        (A.exec Y (l.map fun b => .resp (cb b) (pb b).n)).pend c ∧
      (A.exec X (l.map fun b => .resp (cb b) (pb b).n)).loc c =
        (A.exec Y (l.map fun b => .resp (cb b) (pb b).n)).loc c ∧
      (A.exec X (l.map fun b => .resp (cb b) (pb b).n)).cur c =
        (A.exec Y (l.map fun b => .resp (cb b) (pb b).n)).cur c ∧
      (A.exec X (l.map fun b => .resp (cb b) (pb b).n)).cnt c =
        (A.exec Y (l.map fun b => .resp (cb b) (pb b).n)).cnt c) ∧
    ∀ b, δ b ∉ D → (A.exec X (l.map fun b => .resp (cb b) (pb b).n)).val b =
        (A.exec Y (l.map fun b => .resp (cb b) (pb b).n)).val b := by
  intro l
  induction l with
  | nil => intro _ X Y _ _ _ hrel hval; exact ⟨hrel, fun b hb => hval b hb (by simp)⟩
  | cons b l ih =>
    intro hnd X Y hX hY hmem hrel hval
    obtain ⟨hbl, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hp, hca, hreg, hw⟩ := hmem b (by simp)
    simp only [List.map_cons, exec_cons, step_resp]
    have hpY : pb b ∈ Y.pend (cb b) := (hrel _ hca).1 ▸ hp
    rw [A.doResp_of_mem hX hp, A.doResp_of_mem hY hpY]
    obtain ⟨w, hwop⟩ : ∃ w, (pb b).op = .write w := by
      cases h : (pb b).op with
      | read => rw [h] at hw; exact hw.elim
      | write w => exact ⟨w, rfl⟩
    have hwX := A.wf_apply hX (cb b) (pb b)
    have hwY := A.wf_apply hY (cb b) (pb b)
    rw [A.apply_write _ _ _ hwop] at hwX hwY ⊢
    rw [A.apply_write _ _ _ hwop]
    refine ih hnd' hwX hwY ?_ ?_ ?_
    · intro b' hb'
      obtain ⟨h1, h2, h3, h4⟩ := hmem b' (by simp [hb'])
      refine ⟨?_, h2, h3, h4⟩
      by_cases hc : cb b' = cb b
      · simp only [hc, update_self]
        refine (mem_filter_ne hX hp).2 ⟨hc ▸ h1, fun he => ?_⟩
        have : b' = b := by rw [← h3, ← hreg, he]
        exact hbl (this ▸ hb')
      · simp [update_of_ne hc, h1]
    · intro d hd
      obtain ⟨h1, h2, h3, h4⟩ := hrel d hd
      by_cases hdc : d = cb b
      · subst hdc; simp [h1, h2, h3, h4]
      · simp [update_of_ne hdc, h1, h2, h3, h4]
    · intro b' hb' hb'l
      by_cases hbb : b' = (pb b).reg
      · subst hbb; simp
      · have : b' ∉ b :: l := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => hbb (by rw [h, hreg]), hb'l⟩
        simp [update_of_ne hbb, hval b' hb' this]

end Alg

lemma mem_Cov [Fintype B] {X : Cfg C B V W L} {b : B} :
    b ∈ Cov X ↔ ∃ c, ∃ p ∈ X.pend c, p.reg = b ∧ p.op.IsWrite := by
  simp [Cov]

open Classical in
/-- Servers holding a register outside `K` whose value differs between `X` and `Y`. -/
noncomputable def diffSrv [Fintype B] (δ : B → S) (K : Finset B) (X Y : Cfg C B V W L) :
    Finset S :=
  (Finset.univ.filter fun b => b ∉ K ∧ Y.val b ≠ X.val b).image δ

lemma mem_diffSrv [Fintype B] {δ : B → S} {K : Finset B} {X Y : Cfg C B V W L} {s : S} :
    s ∈ diffSrv δ K X Y ↔ ∃ b, b ∉ K ∧ Y.val b ≠ X.val b ∧ δ b = s := by
  simp [diffSrv, and_assoc]

namespace Alg

variable (A : Alg C B V W L)


/-- **Core of Lemma 4** (Appendix C): a complete write of a new value by a fresh writer, during
which only that writer acts, changes registers outside `Cov(t_{i-1})` on more than `f` servers. -/
theorem fresh_resp [Fintype B] {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ : V}
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr)
    {E₀ : List (Ev C V)} (hE₀ : ∀ d v, Ev.inv d (.write v) ∈ E₀ → d ∈ Wr)
    {Ls : List (C × HOp V × V)} (hL : (A.run E₀).hist = seqHist Ls)
    (hLw : ∀ e ∈ Ls, ∀ v, e.2.1 = .write v → e.1 ∈ Wr)
    (hidle : ∀ c, (A.run E₀).cur c = none)
    {a rd : C} (ha : a ∈ Wr) (hrd : rd ≠ a) (ha0 : (A.run E₀).pend a = [])
    {v : V} (hv : v ≠ lastVal v₀ Ls)
    {E₁ : List (Ev C V)} (hE₁ : ∀ e ∈ E₁, e.IsOf a) {x : V}
    (hY : (A.run (E₀ ++ .inv a (.write v) :: E₁)).hist =
      (A.run E₀).hist ++ [.inv a (.write v), .ret a x]) :
    f < (diffSrv δ (Cov (A.run E₀)) (A.run E₀) (A.run (E₀ ++ .inv a (.write v) :: E₁))).card := by
  set X₀ := A.run E₀
  set Y := A.run (E₀ ++ .inv a (.write v) :: E₁)
  set D := diffSrv δ (Cov X₀) X₀ Y
  by_contra hD
  push Not at hD
  -- `Y` agrees with `X₀` on all clients but `a`
  have hYrel : ∀ c ≠ a, Y.pend c = X₀.pend c ∧ Y.loc c = X₀.loc c ∧ Y.cur c = X₀.cur c ∧
      Y.cnt c = X₀.cnt c := by
    intro c hc
    have hYe : Y = A.exec (A.doInv X₀ a (.write v)) E₁ := by
      simp only [Y, run_append, exec_cons, step_inv]; rfl
    obtain ⟨h1, h2, h3, h4⟩ := A.exec_other (A.doInv X₀ a (.write v)) hE₁ hc
    obtain ⟨g1, g2, g3, g4⟩ := A.doInv_other X₀ (.write v) hc
    rw [hYe]
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩
  -- the flush: one pending (covering) write per covered register
  have hcov : ∀ b ∈ Cov X₀, ∃ c, ∃ p ∈ X₀.pend c, p.reg = b ∧ p.op.IsWrite :=
    fun b hb => mem_Cov.1 hb
  classical
  let cb : B → C := fun b => if h : b ∈ Cov X₀ then (hcov b h).choose else a
  let pb : B → POp B W := fun b =>
    if h : b ∈ Cov X₀ then (hcov b h).choose_spec.choose else ⟨0, b, .read⟩
  have hpb : ∀ b ∈ Cov X₀, pb b ∈ X₀.pend (cb b) ∧ (pb b).reg = b ∧ (pb b).op.IsWrite := by
    intro b hb
    simp only [pb, cb, hb, dite_true]
    exact ⟨(hcov b hb).choose_spec.choose_spec.1, (hcov b hb).choose_spec.choose_spec.2⟩
  set l := (Cov X₀).toList
  set G : List (Ev C V) := l.map fun b => .resp (cb b) (pb b).n
  have hmem : ∀ b ∈ l, pb b ∈ X₀.pend (cb b) ∧ cb b ≠ a ∧ (pb b).reg = b ∧ (pb b).op.IsWrite := by
    intro b hb
    have hb' : b ∈ Cov X₀ := by simpa [l] using hb
    obtain ⟨h1, h2, h3⟩ := hpb b hb'
    refine ⟨h1, fun h => ?_, h2, h3⟩
    rw [h, ha0] at h1; simp at h1
  have hval0 : ∀ b, δ b ∉ D → b ∉ l → X₀.val b = Y.val b := by
    intro b hbD hbl
    have hbC : b ∉ Cov X₀ := by simpa [l] using hbl
    by_contra hne
    exact hbD (mem_diffSrv.2 ⟨b, hbC, Ne.symm hne, rfl⟩)
  obtain ⟨hrel2, hval2⟩ := A.flush_rel (a := a) (D := D) (δ := δ) cb pb l (Finset.nodup_toList _)
    (A.wf_run E₀) (A.wf_run _) hmem (fun c hc => by
      obtain ⟨h1, h2, h3, h4⟩ := hYrel c hc; exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩) hval0
  have hGresp : ∀ e ∈ G, e.IsResp := by
    intro e he; obtain ⟨b, -, rfl⟩ := List.mem_map.1 he; trivial
  set X₂ := A.exec X₀ G
  set Y₂ := A.exec Y G
  obtain ⟨hX₂c, hX₂h⟩ := A.exec_resp_cur_hist X₀ hGresp
  obtain ⟨hY₂c, hY₂h⟩ := A.exec_resp_cur_hist Y hGresp
  have hrdX : X₂.cur rd = none := by rw [hX₂c]; exact hidle rd
  have hrdY : Y₂.cur rd = none := by rw [hY₂c, (hYrel rd hrd).2.2.1]; exact hidle rd
  set X₃ := A.step X₂ (.inv rd .read)
  set Y₃ := A.step Y₂ (.inv rd .read)
  have hX₃ : X₃.cur rd = some .read ∧ X₃.hist = X₂.hist ++ [.inv rd .read] :=
    A.doInv_of_idle X₂ rd .read hrdX
  have hY₃ : Y₃.cur rd = some .read ∧ Y₃.hist = Y₂.hist ++ [.inv rd .read] :=
    A.doInv_of_idle Y₂ rd .read hrdY
  have hrel3 : SoloRel δ rd D X₃ Y₃ := by
    obtain ⟨h1, h2, h3, h4⟩ := hrel2 rd hrd
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [X₃, Y₃, doInv, hrdX, hrdY, h2]
    · simpa [X₃, Y₃] using h1
    · rw [hX₃.1, hY₃.1]
    · simpa [X₃, Y₃] using h4
    · intro b hb; simpa [X₃, Y₃] using hval2 b hb
  -- the two solo runs of the reader
  let Xs : ℕ → Cfg C B V W L := fun t =>
    Nat.rec X₃ (fun _ X => A.step X (soloEv δ rd D X)) t
  let Ys : ℕ → Cfg C B V W L := fun t =>
    Nat.rec Y₃ (fun _ X => A.step X (soloEv δ rd D X)) t
  have hXs : ∀ t, Xs (t + 1) = A.step (Xs t) (soloEv δ rd D (Xs t)) := fun t => rfl
  have hYs : ∀ t, Ys (t + 1) = A.step (Ys t) (soloEv δ rd D (Ys t)) := fun t => rfl
  have hPX : X₃ = A.run ((E₀ ++ G) ++ [.inv rd .read]) := by
    rw [run_append, run_append, exec_singleton]
  have hwfXs : ∀ t, WF (Xs t) := fun t => by
    rw [A.seq_exec hXs t]; exact A.wf_exec (by rw [show Xs 0 = X₃ from rfl, hPX]; exact A.wf_run _) _
  have hsim : ∀ t, SoloRel δ rd D (Xs t) (Ys t) ∧
      ∃ Dh, (Xs t).hist = X₃.hist ++ Dh ∧ (Ys t).hist = Y₃.hist ++ Dh := by
    intro t
    induction t with
    | zero => exact ⟨hrel3, [], by simp [Xs], by simp [Ys]⟩
    | succ t ih =>
      obtain ⟨hr, Dh, h1, h2⟩ := ih
      obtain ⟨hev, hr', Dh', g1, g2⟩ := A.soloRel_step (hwfXs t) hr
      refine ⟨?_, Dh ++ Dh', ?_, ?_⟩
      · rw [hXs, hYs, hev]; exact hr'
      · rw [hXs, g1, h1, List.append_assoc]
      · rw [hYs, hev, g2, h2, List.append_assoc]
  -- the reader returns in the run `r'`
  obtain ⟨u, hu⟩ := A.exists_ret_of_solo hOF (Zs := D) (T := 0) (P₀ := E₀ ++ G) (c := rd)
    (o := .read) (e := fun t => soloEv δ rd D (Xs t)) (X := Xs) (Z := fun _ => D) hD
    (by
      intro d w hd
      rcases List.mem_append.1 hd with hd | hd
      · rcases List.mem_append.1 hd with hd | hd
        · exact hE₀ d w hd
        · exact (hGresp _ hd).elim
      · simp at hd)
    (by rw [run_append]; exact hrdX) hPX hXs (fun t => rfl) (fun _ _ => rfl)
  have hret : RetInv rd .read X₃.hist (Xs u) := by
    rw [A.seq_exec hXs u]
    refine A.retInv_exec (Or.inl ⟨hX₃.1, rfl⟩) ?_
    intro e he
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 he
    exact soloEv_isOf δ rd D _
  obtain ⟨x', hx'⟩ : ∃ x', (Xs u).hist = X₃.hist ++ [.ret rd x'] := by
    rcases hret with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [hu] at h1; cases h1
    · exact h2
  obtain ⟨-, Dh, h1, h2⟩ := hsim u
  have hDh : Dh = [.ret rd x'] := by
    rw [hx'] at h1; exact (List.append_cancel_left h1).symm
  -- sequential safety in both runs
  have hEX : Xs u = A.run (((E₀ ++ G) ++ [.inv rd .read]) ++
      (List.range u).map fun t => soloEv δ rd D (Xs t)) := by
    rw [run_append, ← hPX, A.seq_exec hXs u]; rfl
  have hPY : Y₃ = A.run (((E₀ ++ .inv a (.write v) :: E₁) ++ G) ++ [.inv rd .read]) := by
    rw [run_append, run_append, exec_singleton]
  have hEY : Ys u = A.run ((((E₀ ++ .inv a (.write v) :: E₁) ++ G) ++ [.inv rd .read]) ++
      (List.range u).map fun t => soloEv δ rd D (Ys t)) := by
    rw [run_append, ← hPY, A.seq_exec hYs u]; rfl
  have hsX := hS _ Ls rd x' (by
      rw [← hEX, hx', hX₃.2, hX₂h, hL, seqHist_append]; simp) hLw
  have hsY := hS _ (Ls ++ [(a, .write v, x)]) rd x' (by
      rw [← hEY, h2, hDh, hY₃.2, hY₂h, hY, hL, seqHist_append, seqHist_append]; simp)
    (by
      intro e he w hw
      rcases List.mem_append.1 he with he | he
      · exact hLw e he w hw
      · simp at he; subst he; exact ha)
  rw [lastVal_append_write] at hsY
  exact hv (hsY ▸ hsX)

end Alg

end Podc.RegisterEmulationSpace
