import Papers.PODC2018.NestingSafeRecoverable.Thm4Basic

/-!
# Theorem 4 of [ABH18], part 2: valency

Valency is defined with crash-free extensions, as in the paper: `Val C x` — some crash-free
extension of `C` (steps only) in which `x` has returned `0` (`false`). Main facts:

* `val_or`: every reachable configuration is `p`-valent or `q`-valent;
* `Biv.running`: in a bivalent configuration both processes are still running;
* `agree_val`: configurations that look the same to one process `y` (memory and `y`'s local
  state), in both of which `p` and `q` are running, share a valency (run `y` solo, then the other
  process solo);
* `exists_crit`: from a bivalent configuration, a crash-free extension leads to a *critical*
  configuration (bivalent, both successors univalent) — otherwise there is an infinite crash-free
  execution in which nobody returns, contradicting wait-freedom.
-/

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL Cslib.SharedMemory.NRL.Alg

variable {P : Type} [DecidableEq P] {A : Alg P tasObj} {p q : P}

/-- `x`-valency (paper: "`C` is `x`-valent if there exists a crash-free execution starting from
`C` in which `x` returns `0` or has already returned `0`"). -/
def Val (C : A.Cfg) (x : P) : Prop := ∃ xs : List P, Ret (C.run (steps xs)) x false

/-- Bivalence. -/
def Biv (p q : P) (C : A.Cfg) : Prop := Val C p ∧ Val C q

lemma val_ext {C : A.Cfg} {xs : List P} {v : P} (h : Val (C.run (steps xs)) v) : Val C v := by
  obtain ⟨ys, hy⟩ := h
  exact ⟨xs ++ ys, by simpa [steps, Cfg.run_append] using hy⟩

lemma val_ext1 {C : A.Cfg} {x v : P} (h : Val (C.ev (.step x)) v) : Val C v :=
  val_ext (xs := [x]) h

lemma val_of_equiv {C D : A.Cfg} (h : Equiv C D) {v : P} (hv : Val C v) : Val D v := by
  obtain ⟨xs, hx⟩ := hv
  refine ⟨xs, ?_⟩
  unfold Ret resps at hx ⊢
  rw [← (h.run (steps xs)).2.2 v]; exact hx

lemma pre_const (a : Ev P tasObj) (n : ℕ) : pre (fun _ => a) n = List.replicate n a := by
  simp [pre]

lemma steps_replicate (x : P) (n : ℕ) :
    steps (List.replicate n x) = List.replicate n (Ev.step (O := tasObj) x) := by
  simp [steps]

lemma Reach.replicate {C : A.Cfg} (hC : Reach A p q C) (x : P) (n : ℕ) :
    Reach A p q (C.run (List.replicate n (.step x))) := by
  rw [← steps_replicate]; exact hC.steps _

section Hyp

variable (H : Hyp A p q)
include H

/-- Linearizability: two completed operations return different values. -/
lemma Reach.ret_ne {C : A.Cfg} (hC : Reach A p q C) {bp bq : Bool} (hp : Ret C p bp)
    (hq : Ret C q bq) : bp ≠ bq := by
  obtain ⟨es, rfl, -⟩ := hC.init
  obtain ⟨-, L, hL⟩ := H.nrl es (hC.oneShot H.ne)
  exact lin_two hL H.ne (hC.ops H.ne) hp hq

lemma Reach.ret_ne' {C : A.Cfg} (hC : Reach A p q C) {x y : P} (hxy : x ≠ y)
    (hx : x = p ∨ x = q) (hy : y = p ∨ y = q) {bx b : Bool} (h1 : Ret C x bx)
    (h2 : Ret C y b) : bx ≠ b := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact hC.ret_ne H h1 h2
  · exact (hC.ret_ne H h2 h1).symm
  · exact absurd rfl hxy

/-- Solo termination (wait-freedom of `T&S` and `T&S.Recover`). -/
lemma solo {C : A.Cfg} (hC : Reach A p q C) {x : P} (hx : x = p ∨ x = q) :
    ∃ n b, Ret (C.run (List.replicate n (.step x))) x b := by
  by_cases hs : C.st x = none
  · exact ⟨0, hC.ret_of_none H.ne hx hs⟩
  obtain ⟨es, hCes, hfam⟩ := hC.init
  have hstep : ∀ n, ∀ e' ∈ pre (fun _ => Ev.step (O := tasObj) x) n, GEv p e' := by
    intro n e' he'
    rw [pre_const] at he'
    rw [List.eq_of_mem_replicate he']; exact Or.inl ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := H.wf es (fun _ => .step x) x
    (fun n => (hfam _ hstep n).oneShot H.ne)
    (by rw [← hCes]; exact Option.isSome_iff_ne_none.2 hs)
    (fun n => by simp) (fun m => ⟨m, le_refl _, rfl⟩)
  rw [← hCes, pre_const] at hn
  refine ⟨n, (Reach.run hC ?_).ret_of_none H.ne hx hn⟩
  intro e he; rw [List.eq_of_mem_replicate he]; exact Or.inl ⟨x, rfl⟩

/-- Every reachable configuration is `p`-valent or `q`-valent. -/
lemma val_or {C : A.Cfg} (hC : Reach A p q C) : Val C p ∨ Val C q := by
  obtain ⟨n, bp, hp⟩ := solo H hC (Or.inl rfl)
  have hC1 := hC.replicate p n
  obtain ⟨m, bq, hq⟩ := solo H hC1 (Or.inr rfl)
  have hC2 := hC1.replicate q m
  have hp' := hp.run H.ne hC2 (Or.inl rfl)
  have hne := hC2.ret_ne H hp' hq
  have hxs : C.run (steps (List.replicate n p ++ List.replicate m q)) =
      (C.run (List.replicate n (.step p))).run (List.replicate m (.step q)) := by
    simp [steps, Cfg.run_append]
  cases bp
  · exact Or.inl ⟨_, by rw [hxs]; exact hp'⟩
  · cases bq
    · exact Or.inr ⟨_, by rw [hxs]; exact hq⟩
    · exact absurd rfl hne

/-- In a bivalent configuration, both processes are still running. -/
lemma Biv.running {C : A.Cfg} (hC : Reach A p q C) (hb : Biv p q C) {x : P}
    (hx : x = p ∨ x = q) : (C.st x).isSome := by
  by_contra hs
  obtain ⟨b, hr⟩ := hC.ret_of_none H.ne hx (by simpa using hs)
  have hothers : ∃ y, y ≠ x ∧ (y = p ∨ y = q) ∧ Val C y := by
    rcases hx with rfl | rfl
    · exact ⟨q, Ne.symm H.ne, Or.inr rfl, hb.2⟩
    · exact ⟨p, H.ne, Or.inl rfl, hb.1⟩
  have hvx : Val C x := by rcases hx with rfl | rfl; exacts [hb.1, hb.2]
  cases b
  · obtain ⟨y, hyx, hy, xs, hxs⟩ := hothers
    have hR := hC.steps xs
    exact hR.ret_ne' H (Ne.symm hyx) hx hy (hr.run H.ne hR hx) hxs rfl
  · obtain ⟨xs, hxs⟩ := hvx
    have := (hr.run H.ne (hC.steps xs) hx).unique hxs
    simp at this

/-- Configurations that look the same to `y`, in which both processes run, share a valency. -/
lemma agree_val {C D : A.Cfg} (hC : Reach A p q C) (hD : Reach A p q D) {x y : P}
    (hxy : x ≠ y) (hx : x = p ∨ x = q) (hy : y = p ∨ y = q) (hag : Agree y C D)
    (hCx : (C.st x).isSome) (hDx : (D.st x).isSome) (hCy : (C.st y).isSome)
    (hDy : (D.st y).isSome) :
    ∃ v, (v = p ∨ v = q) ∧ Val C v ∧ Val D v := by
  obtain ⟨n, b, hb⟩ := solo H hC hy
  obtain ⟨hag', hs, h1, h2⟩ := run_agree hag n
  have hCy0 := (hC.running_iff H.ne hy).1 hCy
  have hDy0 := (hD.running_iff H.ne hy).1 hDy
  have hbD : Ret (D.run (List.replicate n (.step y))) y b := by
    unfold Ret resps at hb hCy0 hDy0 ⊢
    rw [h2, N_append, respsOf_append, hDy0]
    rw [h1, N_append, respsOf_append, hCy0] at hb
    exact hb
  have hC1 := hC.replicate y n
  have hD1 := hD.replicate y n
  cases b
  · exact ⟨y, hy, ⟨_, by rw [steps_replicate]; exact hb⟩, ⟨_, by rw [steps_replicate]; exact hbD⟩⟩
  · -- `y` returned `1`: then `x` returns `0` when run solo afterwards
    have key : ∀ {E : A.Cfg}, Reach A p q E → Ret E y true → Val E x := by
      intro E hE hEy
      obtain ⟨m, bx, hbx⟩ := solo H hE hx
      have hE2 := hE.replicate x m
      have hne := hE2.ret_ne' H hxy hx hy hbx (hEy.run H.ne hE2 hy)
      cases bx
      · exact ⟨_, by rw [steps_replicate]; exact hbx⟩
      · exact absurd rfl hne
    refine ⟨x, hx, ?_, ?_⟩
    · have := key hC1 hb; rw [← steps_replicate] at this; exact val_ext this
    · have := key hD1 hbD; rw [← steps_replicate] at this; exact val_ext this

/-- The first step of a valency witness from a configuration where both processes run. -/
lemma val_first {D : A.Cfg} (hD : Reach A p q D) (hp : (D.st p).isSome)
    (hq : (D.st q).isSome) {w : P} (hw : w = p ∨ w = q) (hv : Val D w) :
    Val (D.ev (.step p)) w ∨ Val (D.ev (.step q)) w := by
  obtain ⟨xs, hxs⟩ := hv
  induction xs with
  | nil =>
    exfalso
    have h0 : resps D w = [] := by
      rcases hw with rfl | rfl
      exacts [(hD.running_iff H.ne (Or.inl rfl)).1 hp, (hD.running_iff H.ne (Or.inr rfl)).1 hq]
    unfold Ret at hxs; simp only [List.map_nil, Cfg.run_nil] at hxs
    rw [h0] at hxs; simp at hxs
  | cons y ys ih =>
    simp only [List.map_cons, Cfg.run_cons] at hxs
    by_cases hyp : y = p
    · subst hyp; exact Or.inl ⟨ys, hxs⟩
    by_cases hyq : y = q
    · subst hyq; exact Or.inr ⟨ys, hxs⟩
    rw [ev_step_of_none D (hD.other H.ne hyp hyq)] at hxs
    exact ih hxs

/-- **Critical configurations exist** (uses wait-freedom; crash-free extensions). -/
lemma exists_crit {C : A.Cfg} (hC : Reach A p q C) (hb : Biv p q C) :
    ∃ xs, Biv p q (C.run (steps xs)) ∧ ¬ Biv p q (C.run (steps (xs ++ [p]))) ∧
      ¬ Biv p q (C.run (steps (xs ++ [q]))) := by
  classical
  by_contra hcon
  push_neg at hcon
  let ch : ℕ → List P := fun n => Nat.rec []
    (fun _ l => l ++ [if Biv p q (C.run (steps (l ++ [p]))) then p else q]) n
  let c : ℕ → P := fun n => if Biv p q (C.run (steps (ch n ++ [p]))) then p else q
  have hch : ∀ n, ch (n + 1) = ch n ++ [c n] := fun n => rfl
  have hbiv : ∀ n, Biv p q (C.run (steps (ch n))) := by
    intro n
    induction n with
    | zero => simpa [ch] using hb
    | succ n ih =>
      rw [hch]
      by_cases h : Biv p q (C.run (steps (ch n ++ [p])))
      · simpa only [c, h, ↓reduceIte] using h
      · simp only [c, h, ↓reduceIte]; exact hcon _ ih h
  have hrange : ∀ n, ch n = (List.range n).map c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hch, ih, List.range_succ, List.map_append]; rfl
  have hc : ∀ n, c n = p ∨ c n = q := by
    intro n; simp only [c]; split_ifs <;> simp
  let e : ℕ → Ev P tasObj := fun n => .step (c n)
  have hpre : ∀ n, pre e n = steps (ch n) := by
    intro n; rw [hrange]; simp [pre, e, steps, List.map_map]
  -- some process takes infinitely many steps
  obtain ⟨z, hz, hinf⟩ : ∃ z, (z = p ∨ z = q) ∧ ∀ m, ∃ n, m ≤ n ∧ e n = .step z := by
    by_cases hinf : ∀ m, ∃ n, m ≤ n ∧ c n = p
    · exact ⟨p, Or.inl rfl, fun m => by
        obtain ⟨n, h1, h2⟩ := hinf m; exact ⟨n, h1, by simp [e, h2]⟩⟩
    · push_neg at hinf
      obtain ⟨m₀, hm₀⟩ := hinf
      refine ⟨q, Or.inr rfl, fun m => ?_⟩
      refine ⟨max m m₀, le_max_left _ _, ?_⟩
      have := hm₀ _ (le_max_right m m₀)
      simp only [e]; rw [(hc _).resolve_left this]
  obtain ⟨es, hCes, hfam⟩ := hC.init
  have hG : ∀ n, ∀ e' ∈ pre e n, GEv p e' := by
    intro n e' he'
    simp only [pre, List.mem_map] at he'
    obtain ⟨k, -, rfl⟩ := he'; exact Or.inl ⟨c k, rfl⟩
  obtain ⟨n, hn⟩ := H.wf es e z (fun n => (hfam e hG n).oneShot H.ne)
    (by rw [← hCes]; exact hb.running H hC hz) (fun n => by simp [e]) hinf
  rw [← hCes, hpre] at hn
  have := (hbiv n).running H (hC.steps _) hz
  rw [hn] at this; simp at this

end Hyp

end Podc.NestingSafeRecoverable
