import Papers.PODC2020.DetectableSpace.Alg1Defs
import Papers.PODC2020.DetectableSpace.Lin

/-!
# Algorithm 1 with the paper's initialization is not durably linearizable + detectable

With `R` initially `⟨v_init, 0, 0⟩` the initial value is attributed to a write of process `0`
with toggle index `0`, but `T_0` is initially `0` as well, so the first write of process `0`
uses the same toggle index as the fictitious initial write. The paper's "key observation"
(a process writes with the same toggle index twice only after completing a write with the
other index) fails for this pair, and so does claim 2) of the proof of Lemma 1.

Execution (`v₀ = v_init ≠ v₁`, processes `0` and `1`):
1. process `0` invokes `Write(v₀)` and executes lines 1–6: it reads `⟨v₀, 0, 0⟩`, sets
   `A[0][0][1] := 0`, `mtoggle = T_0 = 0`, persists `RD_0`, sees `R` unchanged, `CP := 1`;
2. process `1` executes `Write(v₁)` to completion (it writes `⟨v₁, 1, 0⟩`);
3. process `0` executes line 7, writing `⟨v₀, 0, 0⟩` — the initial triple again;
4. process `1` executes `Read` to completion and returns `v₀`;
5. the system crashes; process `0` runs `Write.Recover`: `CP = 1`, `R = ⟨v₀, 0, 0⟩` is the
   triple it read in line 1 and `A[0][0][1] = 0`, so it returns `fail` (line 21).

`Write(v₁)` completed before `Read` was invoked and `Read` returned `v₀`, so some write of `v₀`
must be linearized between them; the only one is process `0`'s, which returned `fail`.
-/

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory Alg1

variable {V : Type} [DecidableEq V]

section Loop

variable (v₀ : V) (n : ℕ) [NeZero n] (t₀ : Bool)

/-- The loop of lines 9–10: from index `i`, `n - i` steps set `A[j][p][mt]` for `j ≥ i`. -/
lemma alg1_loop (p : Fin n) (a : ℕ) (o : RWOp V) (b : Bool) (v : V) (tr : Trip V n)
    (mt : Bool) : ∀ (k : ℕ) (i : Fin n) (C : (alg1 V v₀ n t₀).Cfg), i.val + k + 1 = n →
      C.ps p = .run a o b (.w9 v tr mt i) →
      (alg1 V v₀ n t₀).exec C (RImpl.solo p (k + 1)) =
        (⟨⟨C.sh.R, fun x => if x.2.1 = p ∧ x.2.2 = mt ∧ i.val ≤ x.1.val then true else C.sh.A x⟩,
          C.pv, Function.update C.ps p (.run a o b (.w11 v tr mt)), C.cnt⟩, []) := by
  intro k
  induction k with
  | zero =>
    intro i C hk hC
    rw [Nat.zero_add, RImpl.solo_succ, RImpl.exec_cons]
    simp only [RImpl.step1, hC, alg1, act, show ¬ (i.val + 1 < n) by omega, dite_false]
    rw [RImpl.solo, List.replicate_zero, RImpl.exec_nil]
    simp only [List.append_nil]
    congr 2; (try congr 1)
    funext x
    by_cases hx : x = (i, p, mt)
    · subst hx; simp
    · rw [Function.update_of_ne hx]
      have : ¬ (x.2.1 = p ∧ x.2.2 = mt ∧ i.val ≤ x.1.val) := by
        rintro ⟨h1, h2, h3⟩
        apply hx
        obtain ⟨x1, x2, x3⟩ := x
        simp only at h1 h2 h3
        have : x1 = i := Fin.ext (by have := x1.isLt; omega)
        subst h1 h2 this; rfl
      simp only [this, ite_false]
  | succ k ih =>
    intro i C hk hC
    rw [RImpl.solo_succ, RImpl.exec_cons]
    have hlt : i.val + 1 < n := by omega
    have e1 := ih ⟨i.val + 1, hlt⟩ ((alg1 V v₀ n t₀).step1 C (.step p)).1 (by simp; omega)
      (by simp [RImpl.step1, hC, alg1, act, hlt])
    rw [e1]
    simp only [RImpl.step1, hC, alg1, act, hlt, dite_true, Function.update_idem, List.nil_append]
    refine Prod.ext ?_ rfl
    simp only
    congr 2
    funext x
    by_cases hx : x = (i, p, mt)
    · subst hx; simp
    · rw [Function.update_of_ne hx]
      by_cases h1 : x.2.1 = p ∧ x.2.2 = mt ∧ i.val ≤ x.1.val
      · have h2 : x.2.1 = p ∧ x.2.2 = mt ∧ i.val + 1 ≤ x.1.val := by
          refine ⟨h1.1, h1.2.1, ?_⟩
          rcases Nat.lt_or_eq_of_le h1.2.2 with h | h
          · omega
          · exfalso; apply hx
            obtain ⟨x1, x2, x3⟩ := x
            obtain ⟨e1, e2, -⟩ := h1
            simp only at e1 e2 h
            have : x1 = i := Fin.ext h.symm
            subst e1 e2 this; rfl
        simp only [h1, h2, and_self, ite_true]
      · have h2 : ¬ (x.2.1 = p ∧ x.2.2 = mt ∧ i.val + 1 ≤ x.1.val) := by
          rintro ⟨a1, a2, a3⟩; exact h1 ⟨a1, a2, by omega⟩
        simp only [h1, h2, ite_false]

end Loop

omit [DecidableEq V] in
/-- A sequence of writes of `v` leaves the register with value `v`. -/
lemma runOps_writes {v₀ v : V} : ∀ (L : List (ℕ × RWOp V)) (σ : V), L ≠ [] →
    (∀ x ∈ L, x.2 = .write v) → (register V v₀).runOps σ (L.map Prod.snd) = v := by
  intro L
  induction L with
  | nil => intro _ h; exact absurd rfl h
  | cons x L ih =>
    intro σ _ hx
    rw [List.map_cons, ObjSpec.runOps_cons, hx x (by simp)]
    by_cases hL : L = []
    · subst hL; rfl
    · exact ih _ hL (fun y hy => hx y (by simp [hy]))

/-- **Algorithm 1, as published (`R` initially `⟨v_init, 0, 0⟩`), is not durably linearizable
and detectable**, for every `n ≥ 2` and every value domain with two distinct values. -/
theorem alg1_not_durLinDet (v₀ v₁ : V) (hv : v₀ ≠ v₁) (n : ℕ) [NeZero n] (h2 : 2 ≤ n) :
    ¬ (alg1 V v₀ n false).DurLinDet := by
  intro hcor
  set A := alg1 V v₀ n false with hA
  set p0 : Fin n := 0
  set p1 : Fin n := ⟨1, by omega⟩
  have h10 : p1 ≠ p0 := by simp [p1, p0, Fin.ext_iff]
  have h01 : p0 ≠ p1 := h10.symm
  set es1 : List (Ev (Fin n) (register V v₀).Op) := .inv p0 (.write v₀) :: RImpl.solo (O := register V v₀) p0 6
  set es2 : List (Ev (Fin n) (register V v₀).Op) := .inv p1 (.write v₁) :: RImpl.solo (O := register V v₀) p1 8
  set es3 : List (Ev (Fin n) (register V v₀).Op) := RImpl.solo (O := register V v₀) p1 n
  set es4 : List (Ev (Fin n) (register V v₀).Op) :=
    RImpl.solo (O := register V v₀) p1 3 ++ RImpl.solo (O := register V v₀) p0 1 ++ [.inv p1 .read] ++ RImpl.solo (O := register V v₀) p1 3 ++ [.crash] ++
      RImpl.solo (O := register V v₀) p0 7
  -- stage 1
  set C1 : A.Cfg := ⟨⟨(v₀, 0, false), Function.update (fun _ => false) (p0, p0, true) false⟩,
    Function.update (fun _ => ⟨0, none, none, false⟩) p0 ⟨1, none, some (false, (v₀, 0, false)), false⟩,
    Function.update (fun _ => .idle) p0 (.run 0 (.write v₀) false (.w7 v₀ (v₀, 0, false) false)),
    1⟩ with hC1
  have e1 : A.exec A.init es1 = (C1, [.inv 0 p0 (.write v₀)]) := by
    simp [es1, A, C1, p0, RImpl.exec, RImpl.step1, RImpl.init, alg1, Alg1.act, Alg1.start,
      Alg1.aux, RImpl.solo, List.replicate]
  -- stage 2
  set C2 : A.Cfg := ⟨⟨(v₁, p1, false), Function.update C1.sh.A (p1, p0, true) false⟩,
    Function.update C1.pv p1 ⟨2, none, some (false, (v₀, 0, false)), false⟩,
    Function.update C1.ps p1 (.run 1 (.write v₁) false (.w9 v₁ (v₀, 0, false) false 0)),
    2⟩ with hC2
  have e2 : A.exec C1 es2 = (C2, [.inv 1 p1 (.write v₁)]) := by
    simp [es2, A, C1, C2, p0, RImpl.exec, RImpl.step1, alg1, Alg1.act, Alg1.start,
      Alg1.aux, RImpl.solo, List.replicate, h10]
  -- stage 3: the loop
  have e3 : A.exec C2 es3 = (⟨⟨C2.sh.R, fun x => if x.2.1 = p1 ∧ x.2.2 = false ∧ (0 : Fin n).val ≤
      x.1.val then true else C2.sh.A x⟩, C2.pv,
      Function.update C2.ps p1 (.run 1 (.write v₁) false (.w11 v₁ (v₀, 0, false) false)), C2.cnt⟩,
      []) := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := alg1_loop v₀ n false p1 1 (.write v₁) false v₁ (v₀, 0, false) false k 0 C2
      (by simp; omega) (by simp [C2])
    have hs : es3 = RImpl.solo (O := register V v₀) p1 (k + 1) :=
      congrArg (fun m => List.replicate m (Ev.step p1)) hk
    rw [hs]
    exact this
  -- stage 4
  have e4 : (A.exec (A.exec C2 es3).1 es4).2 =
      [.res 1 (some v₁) false, .inv 2 p1 .read, .res 2 (some v₀) false, .crash, .res 0 none true] := by
    rw [e3]
    simp [es4, A, C1, C2, p0, RImpl.exec, RImpl.step1, alg1, Alg1.act, Alg1.recov, Alg1.start,
      Alg1.aux, RImpl.solo, List.replicate, h10, h01, RImpl.crashPS]
  have hh : (A.exec A.init (es1 ++ es2 ++ es3 ++ es4)).2 =
      [.inv 0 p0 (.write v₀), .inv 1 p1 (.write v₁), .res 1 (some v₁) false, .inv 2 p1 .read,
        .res 2 (some v₀) false, .crash, .res 0 none true] := by
    rw [RImpl.exec_snd_append (es := es1 ++ es2 ++ es3) (fs := es4),
      RImpl.exec_snd_append (es := es1 ++ es2) (fs := es3),
      RImpl.exec_snd_append (es := es1) (fs := es2),
      RImpl.exec_fst_append (es := es1 ++ es2) (fs := es3),
      RImpl.exec_fst_append (es := es1) (fs := es2)]
    rw [e1]; dsimp only; rw [e2]; dsimp only; rw [e4, e3]
    simp
  obtain ⟨⟨L, hL⟩, -⟩ := hcor (es1 ++ es2 ++ es3 ++ es4)
  rw [hh] at hL
  set h : List (HEv (Fin n) (register V v₀).Op (register V v₀).Resp) :=
    [HEv.inv 0 p0 (RWOp.write v₀), .inv 1 p1 (RWOp.write v₁), .res 1 (some v₁) false,
    .inv 2 p1 RWOp.read, .res 2 (some v₀) false, .crash, HEv.res 0 none true] with hhdef
  -- the elements of `L`
  have hmemL : ∀ x ∈ L, x = (1, .write v₁) ∨ x = (2, .read) := by
    intro x hx
    obtain ⟨p, hp⟩ := hL.inv_of_mem x hx
    have h0 : x.1 ≠ 0 := by
      intro h0
      exact hL.not_mem_of_fail 0 true (by simp [h]) (h0 ▸ List.mem_map_of_mem hx)
    simp only [h, List.mem_cons, HEv.inv.injEq, reduceCtorEq, List.mem_nil_iff, or_false,
      false_or] at hp
    rcases hp with ⟨e, -, e'⟩ | ⟨e, -, e'⟩ | ⟨e, -, e'⟩
    · exact absurd e h0
    · left; exact Prod.ext e e'
    · right; exact Prod.ext e e'
  have h2L : (2, (RWOp.read : RWOp V)) ∈ L := by
    obtain ⟨x, hx, hx2⟩ := List.mem_map.1 (hL.mem_of_res 2 v₀ false (by simp [h]))
    rcases hmemL x hx with rfl | rfl
    · simp at hx2
    · exact hx
  have h1L : (1, RWOp.write v₁) ∈ L := by
    obtain ⟨x, hx, hx2⟩ := List.mem_map.1 (hL.mem_of_res 1 v₁ false (by simp [h]))
    rcases hmemL x hx with rfl | rfl
    · exact hx
    · simp at hx2
  obtain ⟨L₁, L₂, hsplit⟩ := List.mem_iff_append.1 h2L
  have hprec : Prec h 1 2 := ⟨[.inv 0 p0 (.write v₀), .inv 1 p1 (.write v₁), .res 1 (some v₁) false],
    [.inv 2 p1 .read, .res 2 (some v₀) false, .crash, .res 0 none true], by simp [h],
    ⟨some v₁, false, by simp⟩, p1, .read, by simp⟩
  have h1L₁ : (1, RWOp.write v₁) ∈ L₁ := by
    have hrt := hL.rt
    rw [hsplit] at hrt h1L
    rcases List.mem_append.1 h1L with h1 | h1
    · exact h1
    · rcases List.mem_cons.1 h1 with h1 | h1
      · simp at h1
      · exfalso
        have := (List.pairwise_cons.1 (List.pairwise_append.1 hrt).2.1).1 _ h1
        exact this hprec
  have hL₁ : ∀ x ∈ L₁, x.2 = .write v₁ := by
    intro x hx
    rcases hmemL x (by rw [hsplit]; simp [hx]) with rfl | rfl
    · rfl
    · exfalso
      have hnd := hL.nodup
      rw [hsplit] at hnd
      simp only [List.map_append, List.map_cons] at hnd
      have := List.nodup_append.1 hnd
      exact this.2.2 _ (List.mem_map_of_mem hx) _ (by simp) rfl
  have hleg := hL.legal
  rw [hsplit] at hleg
  have := (Legal.append hleg).1 v₀ false (by simp [h])
  rw [runOps_writes L₁ v₀ (List.ne_nil_of_mem h1L₁) hL₁] at this
  exact hv (by simpa using this)

end Papers.PODC2020.DetectableSpace
