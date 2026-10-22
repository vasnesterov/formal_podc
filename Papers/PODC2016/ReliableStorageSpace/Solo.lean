import Papers.PODC2016.ReliableStorageSpace.Basic
import Papers.PODC2016.ReliableStorageSpace.Coding

/-!
# Solo runs

The *solo strategy* `soloσ c T` lets client `c` run alone while the base objects in `T` are crashed: it
executes `c`'s oldest pending RMW on an object outside `T` if there is one, and otherwise schedules `c`.
Appended to any finite prefix, it yields a fair run in which every client but `c` and every object of
`T` crashes (`solo_fair`), so lock-freedom applies to it.

* `solo_progress` — the argument of Lemma 4: if all pending RMWs of `c` are on objects of `T`
  (`|T| ≤ f`), then the sequence of actions `c` takes without receiving responses eventually returns or
  triggers an RMW outside `T`.
* `reader_restore` — Observation 2: after a write has completed, a fresh reader that runs alone with the
  objects outside `B` crashed must return the value of some write, so (by `restore`) the objects of `B`
  hold at least `D` bits of blocks of one write.
-/

noncomputable section

namespace Podc.ReliableStorageSpace

open Finset Classical

variable {C N J V : Type}

namespace Alg

variable (A : Alg C N J V)

/-- If from time `T₀` on every event is an effective `exec`, the pending list shrinks forever: impossible. -/
theorem not_forall_exec (ev : ℕ → Event C) (T₀ : ℕ)
    (h : ∀ t ≥ T₀, ∃ c m p, ev t = .exec c m ∧ A.findP (A.cfg ev t) c m = some p) : False := by
  have key : ∀ k, (A.cfg ev (T₀ + k)).pend.length + k ≤ (A.cfg ev T₀).pend.length := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨c, m, p, he, hp⟩ := h (T₀ + k) (by omega)
      have := A.length_pend_exec hp
      rw [show T₀ + (k + 1) = T₀ + k + 1 by omega,
        show A.cfg ev (T₀ + k + 1) = A.step (A.cfg ev (T₀ + k)) (ev (T₀ + k)) from rfl, he]
      omega
  have := key ((A.cfg ev T₀).pend.length + 1)
  omega

/-- The solo strategy of client `c` with the objects of `T` crashed. -/
def soloσ (c : C) (T : Finset N) (X : A.Config) : Event C :=
  match X.pend.find? (fun p => decide (p.cl = c ∧ p.obj ∉ T)) with
  | some p => .exec p.cl p.idx
  | none => .step c

theorem soloσ_cases (c : C) (T : Finset N) (X : A.Config) :
    (∃ p ∈ X.pend, p.cl = c ∧ p.obj ∉ T ∧ A.soloσ c T X = .exec p.cl p.idx) ∨
    ((∀ p ∈ X.pend, p.cl = c → p.obj ∈ T) ∧ A.soloσ c T X = .step c) := by
  rcases h : X.pend.find? (fun p => decide (p.cl = c ∧ p.obj ∉ T)) with _ | p
  · right
    refine ⟨fun p hp hpc => ?_, by rw [soloσ, h]⟩
    have := List.find?_eq_none.1 h p hp
    simp only [decide_eq_true_eq, not_and, not_not] at this
    exact this hpc
  · left
    have h1 := List.find?_some h
    simp only [decide_eq_true_eq] at h1
    exact ⟨p, List.mem_of_find?_eq_some h, h1.1, h1.2, by rw [soloσ, h]⟩

variable [Fintype C]

/-- Appending the solo strategy to a finite prefix gives a fair run (crashed: all clients but `c`, and
the objects of `T`). -/
theorem solo_fair (f : ℕ) (evs : List (Event C)) (c : C) (T : Finset N) (hT : T.card ≤ f) :
    A.Fair f (A.splice evs (A.soloσ c T)) (univ.erase c) T := by
  set ev := A.splice evs (A.soloσ c T) with hev
  set n₀ := evs.length
  have hge : ∀ t ≥ n₀, ev t = A.soloσ c T (A.cfg ev t) := by
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact A.splice_ge evs _ s
  -- if `soloσ` executes, the execution is effective
  have heff : ∀ t ≥ n₀, ∀ p ∈ (A.cfg ev t).pend, p.cl = c → p.obj ∉ T →
      ∃ c' m q, ev t = .exec c' m ∧ A.findP (A.cfg ev t) c' m = some q := by
    intro t ht p hp hpc hpT
    rcases A.soloσ_cases c T (A.cfg ev t) with ⟨q, hq, -, -, he⟩ | ⟨hall, -⟩
    · exact ⟨q.cl, q.idx, q, (hge t ht).trans he, (A.pendOK_cfg ev t).findP_eq hq⟩
    · exact absurd (hall p hp hpc) hpT
  refine ⟨hT, ?_, ?_, ?_, ?_⟩
  · intro o ho
    refine ⟨n₀, fun t ht ⟨c', m, p, he, hp, hpo⟩ => ?_⟩
    rcases A.soloσ_cases c T (A.cfg ev t) with ⟨q, hq, -, hqT, he'⟩ | ⟨-, he'⟩
    · rw [hge t ht, he'] at he
      simp only [Event.exec.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [(A.pendOK_cfg ev t).findP_eq hq] at hp
      cases hp
      exact hqT (hpo ▸ ho)
    · rw [hge t ht, he'] at he
      cases he
  · intro c' hc'
    have hne : c' ≠ c := (Finset.mem_erase.1 hc').1
    refine ⟨n₀, fun t ht hcl => ?_⟩
    simp only [ClientEv] at hcl
    rcases A.soloσ_cases c T (A.cfg ev t) with ⟨q, -, -, -, he'⟩ | ⟨-, he'⟩ <;>
      rw [hge t ht, he'] at hcl <;> rcases hcl with hcl | ⟨op, hcl⟩ <;> cases hcl
    exact hne rfl
  · intro c' hc' T₁
    have : c' = c := by simpa using hc'
    subst this
    by_contra hcon
    push Not at hcon
    apply A.not_forall_exec ev (max T₁ n₀)
    intro t ht
    rcases A.soloσ_cases c' T (A.cfg ev t) with ⟨q, hq, -, -, he'⟩ | ⟨-, he'⟩
    · exact ⟨q.cl, q.idx, q, (hge t (by omega)).trans he', (A.pendOK_cfg ev t).findP_eq hq⟩
    · exact absurd ((hge t (by omega)).trans he') (hcon t (by omega))
  · intro t p hp hpc hpT
    have hpc' : p.cl = c := by simpa using hpc
    by_contra hcon
    push Not at hcon
    apply A.not_forall_exec ev (max t n₀)
    intro t' ht'
    exact heff t' (by omega) p (hcon t' (by omega)) hpc' hpT

/-- The local states `c` goes through when it runs without receiving responses. -/
def soloL (c : C) (k : ℕ) (op : Op) (l : A.L) : ℕ → A.L
  | 0 => l
  | i + 1 =>
    match A.act c k op (soloL c k op l i) with
    | .trigger _ _ l' => l'
    | .ret l' => l'
    | .idle => soloL c k op l i

/-- An action that returns or triggers an RMW outside `T`. -/
def Target (T : Finset N) : Act A.L N A.R → Prop
  | .trigger o _ _ => o ∉ T
  | .ret _ => True
  | .idle => False

/-- **Solo progress** (the core of Lemma 4). If client `c` has an outstanding operation and all its
pending RMWs are on objects of `T` (`|T| ≤ f`), then by lock-freedom the actions `c` takes without
receiving responses eventually return or trigger an RMW outside `T`. -/
theorem solo_progress {f : ℕ} (hLF : A.LockFree f) (evs : List (Event C)) (c : C) (op : Op)
    (T : Finset N) (hT : T.card ≤ f) (hcur : (A.runFrom A.init evs).cur c = some op)
    (hpend : ∀ p ∈ (A.runFrom A.init evs).pend, p.cl = c → p.obj ∈ T) :
    ∃ j, A.Target T (A.act c ((A.runFrom A.init evs).cnt c) op
      (A.soloL c ((A.runFrom A.init evs).cnt c) op ((A.runFrom A.init evs).loc c) j)) := by
  set X := A.runFrom A.init evs with hX
  by_contra hcon
  push Not at hcon
  set σ := A.soloσ c T
  -- invariant along the solo run
  have inv : ∀ s, (A.srun X σ s).cur = X.cur ∧ (A.srun X σ s).cnt = X.cnt ∧
      (A.srun X σ s).loc c = A.soloL c (X.cnt c) op (X.loc c) s ∧
      ∀ p ∈ (A.srun X σ s).pend, p.cl = c → p.obj ∈ T := by
    intro s
    induction s with
    | zero => exact ⟨rfl, rfl, rfl, hpend⟩
    | succ s ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hσ : σ (A.srun X σ s) = .step c := by
        rcases A.soloσ_cases c T (A.srun X σ s) with ⟨q, hq, hqc, hqT, -⟩ | ⟨-, he⟩
        · exact absurd (h4 q hq hqc) hqT
        · exact he
      have hc : (A.srun X σ s).cur c = some op := by rw [h1, hcur]
      have hnt := hcon s
      rw [srun, hσ]
      rcases ha : A.act c ((A.srun X σ s).cnt c) op ((A.srun X σ s).loc c) with ⟨o, r, l⟩ | l | _
      · rw [step_step_trigger hc ha]
        rw [h2, h3] at ha
        rw [ha] at hnt
        simp only [Target, not_not] at hnt
        refine ⟨h1, h2, ?_, ?_⟩
        · simp [soloL, ha]
        · intro p hp hpc
          simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact h4 p hp hpc
          · exact hnt
      · rw [h2, h3] at ha
        rw [ha] at hnt
        exact absurd trivial hnt
      · rw [step_step_idle hc ha]
        rw [h2, h3] at ha
        exact ⟨h1, h2, by simp [soloL, ha, h3], h4⟩
  have hfair := A.solo_fair f evs c T hT
  obtain ⟨t', ht', c', hret⟩ := hLF _ _ _ hfair evs.length c (by simp)
    (by rw [A.cfg_splice_le evs σ _ le_rfl, List.take_length, ← hX, hcur]; simp)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht'
  obtain ⟨hr1, hr2⟩ := hret
  rw [A.cfg_splice] at hr1
  rw [show evs.length + s + 1 = evs.length + (s + 1) by omega, A.cfg_splice] at hr2
  rw [(inv s).1] at hr1
  rw [(inv (s + 1)).1] at hr2
  exact hr1 hr2

/-! ### Observation 2 -/

omit [Fintype C] in
/-- The writes of a history, as a finset. -/
def writesOf {Out : Type} (h : List (Label C Out)) : Finset (OpId C) :=
  (h.filterMap (fun x => match x with
    | .inv c k .write => some (c, k)
    | _ => none)).toFinset

omit [Fintype C] in
theorem mem_writesOf {Out : Type} {h : List (Label C Out)} {w : OpId C} :
    w ∈ writesOf h ↔ IsWrite h w := by
  unfold writesOf IsWrite
  simp only [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxw⟩
    rcases x with ⟨c, k, _ | _⟩ | ⟨c, k, o⟩ <;> simp at hxw
    subst hxw
    exact hx
  · intro hw
    exact ⟨_, hw, rfl⟩

/-- **Observation 2** (in its information-theoretic form). Let `X` be reachable, let the write `w` be
completed in `X`, and let `r` be a client without outstanding operation that holds no blocks. Crash
every other client and the objects outside `B` (`|N \ B| ≤ f`) and let `r` read alone. By lock-freedom
the read returns; by weak regularity it returns the value of some write, for every value assignment;
so (`restore`) `r`, and hence the objects of `B` in `X`, hold at least `D` bits of one write. -/
theorem reader_restore [Fintype N] [Fintype V] [Nonempty V] {f : ℕ} {v₀ : V}
    (hLF : A.LockFree f) (hWR : A.WeakRegular v₀)
    (evs : List (Event C)) (r : C) (hr : (A.runFrom A.init evs).cur r = none)
    (hrl : A.lblk ((A.runFrom A.init evs).loc r) = ∅)
    (hrp : ∀ p ∈ (A.runFrom A.init evs).pend, p.cl ≠ r)
    (B : Finset N) (hB : (univ \ B).card ≤ f) (w : OpId C)
    (hw : IsWrite (A.runFrom A.init evs).hist w) (hwc : Completed (A.runFrom A.init evs).hist w) :
    ∃ w', IsWrite (A.runFrom A.init evs).hist w' ∧
      D (V := V) ≤ A.bits (ofW w' (B.biUnion fun o => A.oblk ((A.runFrom A.init evs).obj o))) := by
  set X := A.runFrom A.init evs with hX
  set k := X.cnt r
  set evs₁ := evs ++ [Event.inv r .read]
  set X₁ := A.runFrom A.init evs₁ with hX₁
  have hX₁' : X₁ = A.step X (.inv r .read) := by rw [hX₁, runFrom_concat]
  set T := univ \ B
  set σ := A.soloσ r T
  have hX₁cur : X₁.cur = Function.update X.cur r (some .read) := by
    rw [hX₁', step_inv_free hr]
  have hX₁cnt : X₁.cnt = X.cnt := by rw [hX₁', step_inv_free hr]
  have hX₁obj : X₁.obj = X.obj := by rw [hX₁', step_inv_free hr]
  have hX₁pend : X₁.pend = X.pend := by rw [hX₁', step_inv_free hr]
  have hX₁hist : X₁.hist = X.hist ++ [.inv r k .read] := by rw [hX₁', step_inv_free hr]
  have hX₁loc : X₁.loc r = A.invoke r k .read (X.loc r) := by
    rw [hX₁', step_inv_free hr]; simp [k]
  have hok₁ : A.PendOK X₁ := A.pendOK_runFrom A.pendOK_init _
  have hσc : ∀ Y, (∃ p ∈ Y.pend, p.cl = r ∧ p.obj ∉ T ∧ σ Y = .exec p.cl p.idx) ∨
      ((∀ p ∈ Y.pend, p.cl = r → p.obj ∈ T) ∧ σ Y = .step r) := A.soloσ_cases r T
  -- `cur` along the solo run
  have hcur : ∀ s c, (A.srun X₁ σ s).cur c = X₁.cur c ∨ (c = r ∧ (A.srun X₁ σ s).cur c = none) := by
    intro s
    induction s with
    | zero => intro c; exact Or.inl rfl
    | succ s ih =>
      intro c
      rw [srun]
      rcases hσc (A.srun X₁ σ s) with ⟨q, hq, -, -, he⟩ | ⟨-, he⟩ <;> rw [he]
      · rcases hp : A.findP (A.srun X₁ σ s) q.cl q.idx with _ | p
        · rw [step_exec_none hp]; exact ih c
        · rw [step_exec_some hp]; exact ih c
      · rcases hc : (A.srun X₁ σ s).cur r with _ | op
        · rw [step_step_none hc]; exact ih c
        · rcases ha : A.act r ((A.srun X₁ σ s).cnt r) op ((A.srun X₁ σ s).loc r) with
            ⟨o, rr, l⟩ | l | _
          · rw [step_step_trigger hc ha]; exact ih c
          · rw [step_step_ret hc ha]
            by_cases hcr : c = r
            · subst hcr; right; simp
            · simpa [Function.update_apply, hcr] using ih c
          · rw [step_step_idle hc ha]; exact ih c
  -- invariant of the solo run of the reader, while its read is outstanding
  have inv : ∀ s, (A.srun X₁ σ s).cur r = some .read →
      (A.srun X₁ σ s).cnt r = k ∧ (A.srun X₁ σ s).hist = X₁.hist ∧
      ∀ b, (b ∈ A.held (A.srun X₁ σ s) r ∨ ∃ o ∈ B, b ∈ A.oblk ((A.srun X₁ σ s).obj o)) →
        ∃ o ∈ B, b ∈ A.oblk (X.obj o) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨by simp [srun, hX₁cnt, k], rfl, ?_⟩
      rintro b (hb | ⟨o, ho, hb⟩)
      · rw [mem_held] at hb
        simp only [srun] at hb
        rcases hb with hb | ⟨p, hp, hpr, -⟩
        · rw [hX₁loc] at hb
          rcases A.invoke_blk _ _ _ _ b hb with hb | ⟨hb, -⟩
          · rw [hrl] at hb; simp at hb
          · cases hb
        · rw [hX₁pend] at hp; exact absurd hpr (hrp p hp)
      · exact ⟨o, ho, by simpa [srun, hX₁obj] using hb⟩
    | succ s ih =>
      intro hs
      set Y := A.srun X₁ σ s
      have hY : (A.srun X₁ σ s).cur r = some .read := by
        rcases hcur s r with h | ⟨-, h⟩
        · rw [h, hX₁cur]; simp
        · exfalso
          have : A.srun X₁ σ (s + 1) = A.step Y (σ Y) := rfl
          rw [this] at hs
          rcases hσc Y with ⟨q, hq, -, -, he⟩ | ⟨-, he⟩ <;> rw [he] at hs
          · rcases hp : A.findP Y q.cl q.idx with _ | p
            · rw [step_exec_none hp] at hs; rw [h] at hs; cases hs
            · rw [step_exec_some hp] at hs; simp only at hs; rw [h] at hs; cases hs
          · rw [step_step_none h] at hs; simp only at hs; rw [h] at hs; cases hs
      obtain ⟨ih1, ih2, ih3⟩ := ih hY
      have hokY : A.PendOK Y := A.pendOK_srun hok₁ σ s
      have hsY : A.srun X₁ σ (s + 1) = A.step Y (σ Y) := rfl
      -- the event is an `exec` of a pending RMW of `r` on an object of `B`, or a step of `r`
      have hflow : ∀ b, (b ∈ A.held (A.step Y (σ Y)) r ∨
          ∃ o ∈ B, b ∈ A.oblk ((A.step Y (σ Y)).obj o)) →
          (b ∈ A.held Y r ∨ ∃ o ∈ B, b ∈ A.oblk (Y.obj o)) := by
        rintro b (hb | ⟨o, ho, hb⟩)
        · rcases A.held_step Y (σ Y) r b hb with hb | ⟨hw | hw, -⟩ | ⟨m, p, he, hp, hb⟩
          · exact Or.inl hb
          · rw [hY] at hw; cases hw
          · rcases hσc Y with ⟨q, -, -, -, he⟩ | ⟨-, he⟩ <;> rw [he] at hw <;> cases hw
          · rcases hσc Y with ⟨q, hq, hqr, hqT, he'⟩ | ⟨-, he'⟩ <;> rw [he'] at he
            · simp only [Event.exec.injEq] at he
              obtain ⟨-, rfl⟩ := he
              rw [← hqr, hokY.findP_eq hq] at hp
              cases hp
              exact Or.inr ⟨_, by simpa [T] using hqT, hb⟩
            · cases he
        · rcases A.oblk_step Y (σ Y) o b hb with hb | ⟨c', m, p, he, hp, -, hb⟩
          · exact Or.inr ⟨o, ho, hb⟩
          · obtain ⟨hp1, hp2, -⟩ := findP_spec hp
            refine Or.inl (A.mem_held.2 (Or.inr ⟨p, hp1, ?_, hb⟩))
            rcases hσc Y with ⟨q, -, hqr, -, he'⟩ | ⟨-, he'⟩ <;> rw [he'] at he
            · simp only [Event.exec.injEq] at he
              rw [hp2, ← he.1, hqr]
            · cases he
      rw [hsY] at hs ⊢
      refine ⟨?_, ?_, fun b hb => ih3 b (hflow b hb)⟩ <;>
      · rcases hσc Y with ⟨q, -, -, -, he⟩ | ⟨-, he⟩ <;> rw [he] at hs ⊢
        · rcases hp : A.findP Y q.cl q.idx with _ | p
          · rw [step_exec_none hp]; first | exact ih1 | exact ih2
          · rw [step_exec_some hp]; first | exact ih1 | exact ih2
        · rcases ha : A.act r (Y.cnt r) .read (Y.loc r) with ⟨o, rr, l⟩ | l | _
          · rw [step_step_trigger hY ha]; first | exact ih1 | exact ih2
          · rw [step_step_ret hY ha] at hs; simp at hs
          · rw [step_step_idle hY ha]; first | exact ih1 | exact ih2
  -- the reader's read returns (lock-freedom in the solo run)
  have hfair := A.solo_fair f evs₁ r T hB
  obtain ⟨t', ht', c', hret⟩ := hLF _ _ _ hfair evs₁.length r (by simp)
    (by rw [A.cfg_splice_le evs₁ σ _ le_rfl, List.take_length, ← hX₁, hX₁cur]; simp)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht'
  obtain ⟨hr1, hr2⟩ := hret
  rw [A.cfg_splice] at hr1
  rw [show evs₁.length + s + 1 = evs₁.length + (s + 1) by omega, A.cfg_splice] at hr2
  change (A.srun X₁ σ s).cur c' ≠ none at hr1
  change (A.srun X₁ σ (s + 1)).cur c' = none at hr2
  have hc' : c' = r := by
    by_contra hne
    rcases hcur (s + 1) c' with h | ⟨h, -⟩
    · rcases hcur s c' with h' | ⟨h', -⟩
      · exact hr1 (h'.trans (h.symm.trans hr2))
      · exact hne h'
    · exact hne h
  rw [hc'] at hr1 hr2
  have hYr : (A.srun X₁ σ s).cur r = some .read := by
    rcases hcur s r with h | ⟨-, h⟩
    · rw [h, hX₁cur]; simp
    · exact absurd h hr1
  obtain ⟨hk, hhist, hflowY⟩ := inv s hYr
  set Y := A.srun X₁ σ s with hYdef
  set out := A.rdout r (Y.loc r)
  have hY1 : (A.srun X₁ σ (s + 1)).hist = Y.hist ++ [Label.ret r k (some out)] := by
    have hsY : A.srun X₁ σ (s + 1) = A.step Y (σ Y) := rfl
    rw [hsY] at hr2 ⊢
    rcases hσc Y with ⟨q, -, -, -, he⟩ | ⟨-, he⟩ <;> rw [he] at hr2 ⊢
    · rcases hp : A.findP Y q.cl q.idx with _ | p
      · rw [step_exec_none hp] at hr2; rw [hYr] at hr2; cases hr2
      · rw [step_exec_some hp] at hr2; simp only at hr2; rw [hYr] at hr2; cases hr2
    · rcases ha : A.act r (Y.cnt r) .read (Y.loc r) with ⟨o, rr, l⟩ | l | _
      · rw [step_step_trigger hYr ha] at hr2; simp only at hr2; rw [hYr] at hr2; cases hr2
      · rw [step_step_ret hYr ha, hk]; simp [out]
      · rw [step_step_idle hYr ha] at hr2; simp only at hr2; rw [hYr] at hr2; cases hr2
  -- the history of the whole run
  have hH : (A.runFrom A.init (evs₁ ++ A.sevs X₁ σ (s + 1))).hist =
      X.hist ++ [Label.inv r k .read, Label.ret r k (some out)] := by
    rw [runFrom_append, show A.runFrom A.init evs₁ = X₁ from rfl, runFrom_sevs, hY1, hhist,
      hX₁hist]
    simp
  have hmem : Label.ret r k (some out) ∈ (A.runFrom A.init (evs₁ ++ A.sevs X₁ σ (s + 1))).hist := by
    rw [hH]; simp
  -- weak regularity: the read returns the value of a write of `X`
  have hreg : ∀ val : OpId C → V, ∃ w' ∈ writesOf X.hist,
      out (fun b => A.enc b.2 (val b.1)) = val w' := by
    intro val
    obtain ⟨L, -, hrd, hLw, hLc, hLp, hout⟩ := hWR _ val (r, k) out hmem
    simp only [hH] at hLw hLc hLp
    obtain ⟨o, ho⟩ := hwc
    have hwL : w ∈ L := hLc w (List.mem_append_left _ hw) ⟨o, List.mem_append_left _ ho⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ho
    have hilt : i < X.hist.length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega)] at hi
      cases hi
    have hprec : Precedes (X.hist ++ [Label.inv r k .read, Label.ret r k (some out)]) w (r, k) :=
      ⟨i, X.hist.length, hilt, ⟨o, by rw [List.getElem?_append_left hilt, hi]⟩,
        ⟨.read, by simp⟩⟩
    have hidx := hLp w hwL (r, k) hrd hprec
    have hwt : w ∈ L.take (L.idxOf (r, k)) := (List.mem_take_iff_idxOf_lt hwL).2 hidx
    obtain ⟨x, hx⟩ : ∃ x, (L.take (L.idxOf (r, k))).getLast? = some x :=
      Option.ne_none_iff_exists'.1 (by
        rw [Ne, List.getLast?_eq_none_iff]
        exact List.ne_nil_of_mem hwt)
    have hxt : x ∈ L.take (L.idxOf (r, k)) := List.mem_of_getLast? hx
    have hxL : x ∈ L := List.mem_of_mem_take hxt
    have hxr : x ≠ (r, k) := by
      rintro rfl
      exact absurd ((List.mem_take_iff_idxOf_lt hrd).1 hxt) (lt_irrefl _)
    have hxw := hLw x hxL hxr
    refine ⟨x, mem_writesOf.2 ?_, ?_⟩
    · simp only [IsWrite, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hxw
      rcases hxw with hxw | hxw | hxw
      · exact hxw
      · simp at hxw
      · simp at hxw
    · rw [show (fun b : Blk C J => A.enc b.2 (val b.1)) = A.contents val from rfl, hout,
        lastVal, hx]
      rfl
  -- restoration from the reader's blocks
  obtain ⟨w', hw', hD⟩ := restore A.sz A.enc (A.lblk (Y.loc r)) (writesOf X.hist) out
    (fun g g' hg => A.rdout_congr r _ g g' hg) hreg
  refine ⟨w', mem_writesOf.1 hw', le_trans hD ?_⟩
  unfold bits ofW
  apply Finset.sum_le_sum_of_subset
  intro b hb
  rw [Finset.mem_filter] at hb ⊢
  obtain ⟨o, ho, hbo⟩ := hflowY b (Or.inl (A.mem_held.2 (Or.inl hb.1)))
  exact ⟨Finset.mem_biUnion.2 ⟨o, ho, hbo⟩, hb.2⟩

end Alg

end Podc.ReliableStorageSpace

end
