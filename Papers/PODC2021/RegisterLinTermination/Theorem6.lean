import Papers.PODC2021.RegisterLinTermination.Game
import Podc.Computability.Distributed.SharedMemory.LinPointCheck

/-!
# Theorem 6: with merely linearizable registers, a strong adversary prevents termination

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Section 3.1.

We follow the paper's schedule (Figures 1–2). For `n = m + 3` processes, round `j` with coin `b`
is the event list `round m j b`:

* **Phase 1, before the coin flip** (`roundPre`, independent of `b`): every player writes `⊥` to
  `R1` and `C`; `p₀` and `p₁` invoke their writes `[0, j]`, `[1, j]` to `R1` and every player
  invokes its first read of `R1`; `p₀`'s write returns.
* `p₀` flips the coin `b`.
* **after the flip** (`roundPost`): `p₀` writes `b` to `C`; `p₁`'s write returns; the first reads
  return `[b, j]`, the second reads (sequential) return `[1 - b, j]`; the reads of `C` return `b`.
  The linearization of `R1` puts the write of `p_b` first, then the first reads, then the write of
  `p_{1-b}` and the second reads (`ahistR1`): for `b = 1` this order is fixed only *after* `p₀`'s
  write has returned, which linearizability allows but write strong-linearizability does not.
* **Phase 2**: all write `0` to `R2`; the players read and increment `R2` one after the other;
  `p₀`, `p₁` read `n - 2`.

Linearizability of every prefix is shown with linearization points
(`Cslib.SharedMemory.isLinearization_of_lpRun`). The adversary `adv` reads the coins off the
history and schedules the next event of this run (`genRun_adv`).
-/

namespace Podc.RegisterLinTermination.Game

open Cslib.SharedMemory List

namespace Thm6

variable (m : ℕ)

/-- Host `p₀`. -/
def hp0 : Fin (m + 3) := ⟨0, by omega⟩
/-- Host `p₁`. -/
def hp1 : Fin (m + 3) := ⟨1, by omega⟩

/-- The players `p₂, …, p_{n-1}` in increasing order. -/
def players : List (Fin (m + 3)) := (List.finRange (m + 3)).drop 2

variable {m}

lemma length_players : (players m).length = m + 1 := by simp [players]

lemma getElem_players (i : ℕ) (h : i < (players m).length) : ((players m)[i]).val = i + 2 := by
  simp [players, add_comm]

lemma mem_players {q : Fin (m + 3)} : q ∈ players m ↔ 2 ≤ q.val := by
  constructor
  · intro hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    rw [getElem_players]; omega
  · intro hq
    have h1 : q.val - 2 < (players m).length := by rw [length_players]; omega
    have := getElem_players _ h1
    have heq : (players m)[q.val - 2] = q := Fin.ext (by rw [this]; omega)
    rw [← heq]; exact List.getElem_mem h1

lemma nodup_players : (players m).Nodup :=
  (List.nodup_finRange _).sublist (List.drop_sublist _ _)

lemma players_ne_nil : players m ≠ [] := by
  intro h; have := length_players (m := m); rw [h] at this; simp at this

@[simp] lemma hp0_val : (hp0 m).val = 0 := rfl
@[simp] lemma hp1_val : (hp1 m).val = 1 := rfl

@[simp] lemma hp0_not_mem : hp0 m ∉ players m := by rw [mem_players]; simp
@[simp] lemma hp1_not_mem : hp1 m ∉ players m := by rw [mem_players]; simp
@[simp] lemma hp0_ne_hp1 : hp0 m ≠ hp1 m := by simp [Fin.ext_iff]
@[simp] lemma hp1_ne_hp0 : hp1 m ≠ hp0 m := by simp [Fin.ext_iff]

lemma ne_hp0_of_mem {q : Fin (m + 3)} (hq : q ∈ players m) : q ≠ hp0 m := by
  rintro rfl; exact hp0_not_mem hq

lemma ne_hp1_of_mem {q : Fin (m + 3)} (hq : q ∈ players m) : q ≠ hp1 m := by
  rintro rfl; exact hp1_not_mem hq

/-! ## The run -/

variable (m)

/-- Round `j`, Phase 1 up to the coin flip (independent of the coin). -/
def roundPre (j : ℕ) : List (Ev (m + 3)) :=
  (players m).flatMap (fun q => [.inv q .r1 (.write .bot), .ret q .r1 .bot,
      .inv q .c (.write .bot), .ret q .c .bot])
  ++ [.inv (hp0 m) .r1 (.write (.pair false j)), .inv (hp1 m) .r1 (.write (.pair true j))]
  ++ (players m).map (fun q => .inv q .r1 .read)
  ++ [.ret (hp0 m) .r1 (.pair false j)]

/-- Round `j` after the coin flip `b`. -/
def roundPost (j : ℕ) (b : Bool) : List (Ev (m + 3)) :=
  [.inv (hp0 m) .c (.write (.bit b)), .ret (hp0 m) .c (.bit b), .ret (hp1 m) .r1 (.pair true j)]
  ++ (players m).map (fun q => .ret q .r1 (.pair b j))
  ++ (players m).flatMap (fun q => [.inv q .r1 .read, .ret q .r1 (.pair (!b) j)])
  ++ (players m).flatMap (fun q => [.inv q .c .read, .ret q .c (.bit b)])
  ++ [.inv (hp0 m) .r2 (.write (.num 0)), .ret (hp0 m) .r2 (.num 0),
      .inv (hp1 m) .r2 (.write (.num 0)), .ret (hp1 m) .r2 (.num 0)]
  ++ (players m).flatMap (fun q => [.inv q .r2 (.write (.num 0)), .ret q .r2 (.num 0)])
  ++ (players m).flatMap (fun q => [.inv q .r2 .read, .ret q .r2 (.num (q.val - 2)),
      .inv q .r2 (.write (.num (q.val - 2 + 1))), .ret q .r2 (.num (q.val - 2 + 1))])
  ++ [.inv (hp0 m) .r2 .read, .ret (hp0 m) .r2 (.num (m + 1)),
      .inv (hp1 m) .r2 .read, .ret (hp1 m) .r2 (.num (m + 1))]

/-- Round `j` with coin `b`. -/
def round (j : ℕ) (b : Bool) : List (Ev (m + 3)) :=
  roundPre m j ++ .flip (hp0 m) b :: roundPost m j b

/-! ## Linearization points -/

/-- A sequential operation with its linearization point. -/
def tri {x : Reg} (p : Fin (m + 3)) (o : RWOp Val) (r : Val) :
    List (LPLabel (Fin (m + 3)) (RegObj x)) := [.inv p o, .lin p, .ret p r]

/-- The history of `R1` in round `j`, annotated with linearization points. -/
def ahistR1 (j : ℕ) (b : Bool) : List (LPLabel (Fin (m + 3)) (RegObj .r1)) :=
  (players m).flatMap (fun q => [.inv q (.write .bot), .lin q, .ret q .bot])
  ++ [.inv (hp0 m) (.write (.pair false j)), .inv (hp1 m) (.write (.pair true j))]
  ++ (players m).map (fun q => .inv q .read)
  ++ (if b then .lin (hp1 m) :: (players m).map (fun q => .lin q) else [])
  ++ [.lin (hp0 m), .ret (hp0 m) (.pair false j)]
  ++ (if b then [] else (players m).map (fun q => .lin q) ++ [.lin (hp1 m)])
  ++ [.ret (hp1 m) (.pair true j)]
  ++ (players m).map (fun q => .ret q (.pair b j))
  ++ (players m).flatMap (fun q => [.inv q .read, .lin q, .ret q (.pair (!b) j)])

/-- The history of `C` in round `j`, annotated with linearization points. -/
def ahistC (b : Bool) : List (LPLabel (Fin (m + 3)) (RegObj .c)) :=
  (players m).flatMap (fun q => [.inv q (.write .bot), .lin q, .ret q .bot])
  ++ [.inv (hp0 m) (.write (.bit b)), .lin (hp0 m), .ret (hp0 m) (.bit b)]
  ++ (players m).flatMap (fun q => [.inv q .read, .lin q, .ret q (.bit b)])

/-- The history of `R2` in round `j`, annotated with linearization points. -/
def ahistR2 : List (LPLabel (Fin (m + 3)) (RegObj .r2)) :=
  [.inv (hp0 m) (.write (.num 0)), .lin (hp0 m), .ret (hp0 m) (.num 0),
    .inv (hp1 m) (.write (.num 0)), .lin (hp1 m), .ret (hp1 m) (.num 0)]
  ++ (players m).flatMap (fun q => [.inv q (.write (.num 0)), .lin q, .ret q (.num 0)])
  ++ (players m).flatMap (fun q => [.inv q .read, .lin q, .ret q (.num (q.val - 2)),
      .inv q (.write (.num (q.val - 2 + 1))), .lin q, .ret q (.num (q.val - 2 + 1))])
  ++ [.inv (hp0 m) .read, .lin (hp0 m), .ret (hp0 m) (.num (m + 1)),
    .inv (hp1 m) .read, .lin (hp1 m), .ret (hp1 m) (.num (m + 1))]

variable {m}

@[simp] lemma flatMap_fun_nil {X Y : Type} (l : List X) :
    l.flatMap (fun _ => ([] : List Y)) = [] := by
  induction l <;> simp_all

@[simp] lemma filterMap_fun_none {X Y : Type} (l : List X) :
    l.filterMap (fun _ => (none : Option Y)) = [] := by
  induction l <;> simp_all

lemma hist_r1_round (j : ℕ) (b : Bool) :
    hist .r1 (round m j b) = (ahistR1 m j b).filterMap LPLabel.erase := by
  cases b <;> simp [hist, round, roundPre, roundPost, ahistR1, Ev.toLabel, LPLabel.erase,
    filterMap_flatMap, filterMap_cons, filterMap_map, Function.comp_def]

lemma hist_c_round (j : ℕ) (b : Bool) :
    hist .c (round m j b) = (ahistC m b).filterMap LPLabel.erase := by
  simp [hist, round, roundPre, roundPost, ahistC, Ev.toLabel, LPLabel.erase, filterMap_flatMap,
    filterMap_cons, filterMap_map, Function.comp_def]

lemma hist_r2_round (j : ℕ) (b : Bool) :
    hist .r2 (round m j b) = (ahistR2 m).filterMap LPLabel.erase := by
  simp [hist, round, roundPre, roundPost, ahistR2, Ev.toLabel, LPLabel.erase, filterMap_flatMap,
    filterMap_cons, filterMap_map, Function.comp_def]

end Thm6

end Podc.RegisterLinTermination.Game

namespace Podc.RegisterLinTermination.Game.Thm6

open Cslib.SharedMemory List

variable {m : ℕ}

lemma eq_hp_of_not_mem {q : Fin (m + 3)} (hq : q ∉ players m) : q = hp0 m ∨ q = hp1 m := by
  rw [mem_players] at hq
  rcases Nat.lt_or_ge q.val 1 with h | h
  · left; exact Fin.ext (by rw [hp0_val]; omega)
  · right; exact Fin.ext (by rw [hp1_val]; omega)

/-- All processes idle. -/
abbrev allIdle (x : Reg) : Fin (m + 3) → LPStatus (RegObj x) := fun _ => .idle

lemma lpRun_C (b : Bool) (v : Val) :
    lpRun (v, allIdle .c) (ahistC m b) = some (.bit b, allIdle .c) := by
  unfold ahistC
  rw [lpRun_append (A := RegObj .c), lpRun_append (A := RegObj .c),
    lpRun_flatMap_triple_set (A := RegObj .c) (s₁ := Val.bot) (o := fun _ => .write .bot)
      (r := fun _ => .bot) _ players_ne_nil (by simp) _ (by simp)]
  simp only [Option.bind_some]
  rw [lpRun_triple' (A := RegObj .c) _ rfl (by simp) []]
  simp only [lpRun_nil, Option.bind_some]
  exact lpRun_flatMap_triple_const (A := RegObj .c) (o := fun _ => .read) (r := fun _ => .bit b)
    _ (by simp) _ (by simp)

/-- The players read and increment `R2` one after the other. -/
lemma lpRun_R2_chain : ∀ (ps : List (Fin (m + 3))) (a : ℕ),
    (∀ i (h : i < ps.length), ps[i].val = a + i + 2) →
    lpRun (A := RegObj .r2) (.num a, allIdle .r2) (ps.flatMap (fun q =>
      [LPLabel.inv q .read, .lin q, .ret q (.num (q.val - 2)),
        .inv q (.write (.num (q.val - 2 + 1))), .lin q, .ret q (.num (q.val - 2 + 1))])) =
      some (.num (a + ps.length), allIdle .r2)
  | [], a, _ => by simp
  | q :: ps, a, h => by
    have hq : q.val - 2 = a := by have := h 0 (by simp); simp at this; omega
    rw [flatMap_cons, hq]
    simp only [cons_append, nil_append]
    rw [lpRun_triple' (A := RegObj .r2) _ rfl (by simp),
      lpRun_triple' (A := RegObj .r2) _ rfl (by simp)]
    rw [lpRun_R2_chain ps (a + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega); simp at this; omega)]
    simp; omega

lemma lpRun_R2 (v : Val) :
    lpRun (v, allIdle .r2) (ahistR2 m) = some (.num (m + 1), allIdle .r2) := by
  unfold ahistR2
  rw [lpRun_append (A := RegObj .r2), lpRun_append (A := RegObj .r2),
    lpRun_append (A := RegObj .r2)]
  rw [lpRun_triple' (A := RegObj .r2) _ rfl (by simp),
    lpRun_triple' (A := RegObj .r2) _ rfl (by simp)]
  simp only [lpRun_nil, Option.bind_some]
  rw [lpRun_flatMap_triple_const (A := RegObj .r2) (o := fun _ => .write (.num 0))
    (r := fun _ => .num 0) _ (by simp) _ (by simp), Option.bind_some]
  rw [lpRun_R2_chain (players m) 0 (fun i hi => by rw [getElem_players]; omega),
    Option.bind_some, length_players]
  rw [lpRun_triple' (A := RegObj .r2) _ rfl (by simp),
    lpRun_triple' (A := RegObj .r2) _ rfl (by simp)]
  simp

lemma lpRun_R1 (j : ℕ) (b : Bool) (v : Val) :
    lpRun (v, allIdle .r1) (ahistR1 m j b) = some (.pair (!b) j, allIdle .r1) := by
  unfold ahistR1
  simp only [append_assoc]
  rw [lpRun_append (A := RegObj .r1), lpRun_flatMap_triple_set (A := RegObj .r1) (s₁ := Val.bot)
    (o := fun _ => .write .bot) (r := fun _ => .bot) _ players_ne_nil (by simp) _ (by simp),
    Option.bind_some]
  simp only [cons_append, nil_append, lpRun_cons, lpStep, Option.bind_some, Function.update_apply,
    hp1_ne_hp0, ite_false]
  rw [lpRun_append (A := RegObj .r1), lpRun_map_single (A := RegObj .r1) (fun q => .inv q .read)
    (fun _ => .idle) (fun _ => .pending .read) (by intro p st h; simp [lpStep, h]) _ nodup_players
    _ (by intro q hq; simp [ne_hp0_of_mem hq, ne_hp1_of_mem hq]), Option.bind_some]
  cases b
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false, cons_append, nil_append,
      append_assoc]
    simp only [lpRun_cons, lpStep, hp0_not_mem, ite_false, Function.update_apply, hp0_ne_hp1,
      ite_true, Option.bind_some]
    rw [lpRun_append (A := RegObj .r1), lpRun_map_single (A := RegObj .r1) (fun q => .lin q)
      (fun _ => .pending .read) (fun _ => .linearized (.pair false j))
      (by intro p st h; simp [lpStep, h]) _ nodup_players
      _ (by intro q hq; simp [hq, ne_hp0_of_mem hq]), Option.bind_some]
    simp only [lpRun_cons, lpStep, hp1_not_mem, ite_false, Function.update_apply,
      hp1_ne_hp0, ite_true, Option.bind_some]
    rw [lpRun_append (A := RegObj .r1), lpRun_map_single (A := RegObj .r1)
      (fun q => .ret q (.pair false j)) (fun _ => .linearized (.pair false j)) (fun _ => .idle)
      (by intro p st h; simp [lpStep, h]) _ nodup_players
      _ (by intro q hq; simp [hq, ne_hp1_of_mem hq]),
      Option.bind_some]
    rw [lpRun_flatMap_triple_const (A := RegObj .r1) (o := fun _ => .read)
      (r := fun _ => .pair true j) _ (by simp) _ (by intro q hq; simp [hq])]
    congr 2; funext p
    by_cases hp : p ∈ players m
    · simp [hp]
    · rcases eq_hp_of_not_mem hp with rfl | rfl <;> simp
  · simp only [ite_true, Bool.not_true, cons_append, nil_append]
    rw [lpRun_cons (A := RegObj .r1)]
    simp only [lpStep, hp1_not_mem, ite_false, Function.update_self, Option.bind_some]
    rw [lpRun_append (A := RegObj .r1), lpRun_map_single (A := RegObj .r1) (fun q => .lin q)
      (fun _ => .pending .read) (fun _ => .linearized (.pair true j))
      (by intro p st h; simp [lpStep, h]) _ nodup_players
      _ (by intro q hq; simp [hq, ne_hp1_of_mem hq]), Option.bind_some]
    simp only [lpRun_cons, lpStep, hp0_not_mem, hp1_not_mem, ite_false, Function.update_apply,
      hp0_ne_hp1, hp1_ne_hp0, ite_true, Option.bind_some]
    rw [lpRun_append (A := RegObj .r1), lpRun_map_single (A := RegObj .r1)
      (fun q => .ret q (.pair true j)) (fun _ => .linearized (.pair true j)) (fun _ => .idle)
      (by intro p st h; simp [lpStep, h]) _ nodup_players
      _ (by intro q hq; simp [hq, ne_hp0_of_mem hq, ne_hp1_of_mem hq]),
      Option.bind_some]
    rw [lpRun_flatMap_triple_const (A := RegObj .r1) (o := fun _ => .read)
      (r := fun _ => .pair false j) _ (by simp) _ (by intro q hq; simp [hq])]
    congr 2; funext p
    by_cases hp : p ∈ players m
    · simp [hp]
    · rcases eq_hp_of_not_mem hp with rfl | rfl <;> simp

/-! ## Following the code -/

/-- Replay the events of `p` in `α` from the mode `mo`. -/
def pfold {n : ℕ} (p : Fin n) (mo : Option Mode) (α : List (Ev n)) : Option Mode :=
  (α.filter (fun e => decide (e.proc = p))).foldl (fun m e => m.bind (fun m => pstep n p m e)) mo

lemma procRun_eq_pfold {n : ℕ} (p : Fin n) (α : List (Ev n)) :
    procRun p α = pfold p (some (.run (initLoc p))) α := rfl

lemma pfold_append {n : ℕ} (p : Fin n) (mo : Option Mode) (α β : List (Ev n)) :
    pfold p mo (α ++ β) = pfold p (pfold p mo α) β := by
  simp [pfold, filter_append, foldl_append]

@[simp] lemma pfold_nil {n : ℕ} (p : Fin n) (mo : Option Mode) : pfold p mo [] = mo := rfl

lemma pfold_cons {n : ℕ} (p : Fin n) (mo : Option Mode) (e : Ev n) (α : List (Ev n)) :
    pfold p mo (e :: α) =
      pfold p (if e.proc = p then mo.bind (fun m => pstep n p m e) else mo) α := by
  by_cases h : e.proc = p <;> simp [pfold, h]

lemma pfold_none {n : ℕ} (p : Fin n) (α : List (Ev n)) : pfold p none α = none := by
  induction α with
  | nil => rfl
  | cons e α ih => rw [pfold_cons]; split <;> simpa using ih

lemma pfold_of_forall_ne {n : ℕ} (p : Fin n) (mo : Option Mode) (α : List (Ev n))
    (h : ∀ e ∈ α, e.proc ≠ p) : pfold p mo α = mo := by
  induction α with
  | nil => rfl
  | cons e α ih =>
    rw [pfold_cons, ite_eq_right (h e (by simp))]; exact ih (fun e he => h e (by simp [he]))

lemma pfold_flatMap_of_mem {n : ℕ} (p : Fin n) (mo : Option Mode) (f : Fin n → List (Ev n))
    (hf : ∀ q, ∀ e ∈ f q, e.proc = q) :
    ∀ (ps : List (Fin n)), ps.Nodup → p ∈ ps → pfold p mo (ps.flatMap f) = pfold p mo (f p)
  | [], _, hp => by simp at hp
  | q :: ps, hnd, hp => by
    rw [nodup_cons] at hnd
    rw [flatMap_cons, pfold_append]
    by_cases hq : q = p
    · subst hq
      rw [pfold_of_forall_ne]
      intro e he hep
      obtain ⟨q', hq', he'⟩ := mem_flatMap.1 he
      rw [hf q' e he'] at hep; subst hep; exact hnd.1 hq'
    · rw [pfold_of_forall_ne p mo (f q) (fun e he h => hq (by rw [← hf q e he, h]))]
      exact pfold_flatMap_of_mem p mo f hf ps hnd.2 (by simpa [Ne.symm hq] using hp)

lemma pfold_flatMap_of_not_mem {n : ℕ} (p : Fin n) (mo : Option Mode) (f : Fin n → List (Ev n))
    (hf : ∀ q, ∀ e ∈ f q, e.proc = q) (ps : List (Fin n)) (hp : p ∉ ps) :
    pfold p mo (ps.flatMap f) = mo := by
  apply pfold_of_forall_ne
  intro e he hep
  obtain ⟨q', hq', he'⟩ := mem_flatMap.1 he
  rw [hf q' e he'] at hep; subst hep; exact hp hq'

lemma pfold_map_of_mem {n : ℕ} (p : Fin n) (mo : Option Mode) (f : Fin n → Ev n)
    (hf : ∀ q, (f q).proc = q) (ps : List (Fin n)) (hnd : ps.Nodup) (hp : p ∈ ps) :
    pfold p mo (ps.map f) = pfold p mo [f p] := by
  rw [show ps.map f = ps.flatMap (fun q => [f q]) from (flatMap_pure_eq_map f ps).symm]
  exact pfold_flatMap_of_mem p mo (fun q => [f q]) (by simp [hf]) ps hnd hp

lemma pfold_map_of_not_mem {n : ℕ} (p : Fin n) (mo : Option Mode) (f : Fin n → Ev n)
    (hf : ∀ q, (f q).proc = q) (ps : List (Fin n)) (hp : p ∉ ps) :
    pfold p mo (ps.map f) = mo := by
  rw [show ps.map f = ps.flatMap (fun q => [f q]) from (flatMap_pure_eq_map f ps).symm]
  exact pfold_flatMap_of_not_mem p mo (fun q => [f q]) (by simp [hf]) ps hp

/-- The local state at the beginning of round `j`. -/
def startLoc {n : ℕ} (p : Fin n) (j : ℕ) : Loc := if p.val < 2 then .h1 j else .q1 j

lemma initLoc_eq {n : ℕ} (p : Fin n) : initLoc p = startLoc p 1 := rfl

lemma pfold_round_player (j : ℕ) (b : Bool) {q : Fin (m + 3)} (hq : q ∈ players m) :
    pfold q (some (.run (startLoc q j))) (round m j b) = some (.run (startLoc q (j + 1))) := by
  have h0 : hp0 m ≠ q := Ne.symm (ne_hp0_of_mem hq)
  have h1 : hp1 m ≠ q := Ne.symm (ne_hp1_of_mem hq)
  have hv : 2 ≤ q.val := mem_players.1 hq
  simp only [round, roundPre, roundPost, append_assoc, cons_append, nil_append, pfold_append,
    pfold_cons, Ev.proc, h0, h1, ite_false]
  repeat' (first
    | rw [pfold_flatMap_of_mem q _ _ ?_ _ nodup_players hq]
    | rw [pfold_map_of_mem q _ _ ?_ _ nodup_players hq])
  all_goals try simp [Ev.proc]
  have hv' : ¬ q.val < 2 := by omega
  cases b <;> simp [pfold_cons, Ev.proc, pstep, code, startLoc, passes, Val.toNat, hv']

lemma pfold_round_hp0 (j : ℕ) (b : Bool) :
    pfold (hp0 m) (some (.run (startLoc (hp0 m) j))) (round m j b) =
      some (.run (startLoc (hp0 m) (j + 1))) := by
  simp only [round, roundPre, roundPost, append_assoc, cons_append, nil_append, pfold_append,
    pfold_cons, Ev.proc, hp1_ne_hp0, ite_true, ite_false]
  repeat' (first
    | rw [pfold_flatMap_of_not_mem (hp0 m) _ _ ?_ _ hp0_not_mem]
    | rw [pfold_map_of_not_mem (hp0 m) _ _ ?_ _ hp0_not_mem])
  all_goals try simp [Ev.proc]
  simp [pstep, code, startLoc, Val.toNat]

lemma pfold_round_hp1 (j : ℕ) (b : Bool) :
    pfold (hp1 m) (some (.run (startLoc (hp1 m) j))) (round m j b) =
      some (.run (startLoc (hp1 m) (j + 1))) := by
  simp only [round, roundPre, roundPost, append_assoc, cons_append, nil_append, pfold_append,
    pfold_cons, Ev.proc, hp0_ne_hp1, ite_true, ite_false]
  repeat' (first
    | rw [pfold_flatMap_of_not_mem (hp1 m) _ _ ?_ _ hp1_not_mem]
    | rw [pfold_map_of_not_mem (hp1 m) _ _ ?_ _ hp1_not_mem])
  all_goals try simp [Ev.proc]
  simp [pstep, code, startLoc, Val.toNat]

lemma pfold_round (j : ℕ) (b : Bool) (p : Fin (m + 3)) :
    pfold p (some (.run (startLoc p j))) (round m j b) = some (.run (startLoc p (j + 1))) := by
  by_cases hp : p ∈ players m
  · exact pfold_round_player j b hp
  · rcases eq_hp_of_not_mem hp with rfl | rfl
    · exact pfold_round_hp0 j b
    · exact pfold_round_hp1 j b

variable (m) in
/-- The first `J` rounds, round `k + 1` with coin `ω k`. -/
def rounds (ω : ℕ → Bool) : ℕ → List (Ev (m + 3))
  | 0 => []
  | J + 1 => rounds ω J ++ round m (J + 1) (ω J)

lemma procRun_rounds (ω : ℕ → Bool) (J : ℕ) (p : Fin (m + 3)) :
    procRun p (rounds m ω J) = some (.run (startLoc p (J + 1))) := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [procRun_eq_pfold, rounds, pfold_append, ← procRun_eq_pfold, ih, pfold_round]

/-! ## Linearizability of every prefix -/

variable (m) in
/-- The annotated history of register `x` in round `j` with coin `b`. -/
def ahist : (x : Reg) → ℕ → Bool → List (LPLabel (Fin (m + 3)) (RegObj x))
  | .r1, j, b => ahistR1 m j b
  | .r2, _, _ => ahistR2 m
  | .c, _, b => ahistC m b

lemma hist_round (x : Reg) (j : ℕ) (b : Bool) :
    hist x (round m j b) = (ahist m x j b).filterMap LPLabel.erase := by
  cases x
  · exact hist_r1_round j b
  · exact hist_r2_round j b
  · exact hist_c_round j b

lemma lpRun_ahist (x : Reg) (j : ℕ) (b : Bool) (v : Val) :
    ∃ v', lpRun (v, allIdle x) (ahist m x j b) = some (v', allIdle x) := by
  cases x
  · exact ⟨_, lpRun_R1 j b v⟩
  · exact ⟨_, lpRun_R2 v⟩
  · exact ⟨_, lpRun_C b v⟩

variable (m) in
/-- The annotated history of register `x` in the first `J` rounds. -/
def ahists (x : Reg) (ω : ℕ → Bool) : ℕ → List (LPLabel (Fin (m + 3)) (RegObj x))
  | 0 => []
  | J + 1 => ahists x ω J ++ ahist m x (J + 1) (ω J)

lemma hist_rounds (x : Reg) (ω : ℕ → Bool) (J : ℕ) :
    hist x (rounds m ω J) = (ahists m x ω J).filterMap LPLabel.erase := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [rounds, ahists, filterMap_append, ← ih, ← hist_round]
    simp [hist, filterMap_append]

lemma lpRun_ahists (x : Reg) (ω : ℕ → Bool) (J : ℕ) :
    ∃ v, lpRun ((RegObj x).init, allIdle x) (ahists m x ω J) = some (v, allIdle x) := by
  induction J with
  | zero => exact ⟨_, rfl⟩
  | succ J ih =>
    obtain ⟨v, hv⟩ := ih
    obtain ⟨v', hv'⟩ := lpRun_ahist (m := m) x (J + 1) (ω J) v
    exact ⟨v', by rw [ahists, lpRun_append (A := RegObj x), hv, Option.bind_some, hv']⟩

lemma isLinearization_of_prefix_rounds (x : Reg) (ω : ℕ → Bool) (J : ℕ)
    {β : List (Label (Fin (m + 3)) (RegObj x))} (hβ : β <+: hist x (rounds m ω J)) :
    ∃ L, IsLinearization β L := by
  obtain ⟨v, hv⟩ := lpRun_ahists (m := m) x ω J
  rw [hist_rounds] at hβ
  exact isLinearization_of_lpRun hv hβ

/-! ## The adversary -/

/-- The outcome of a coin flip event. -/
def coin? {n : ℕ} : Ev n → Option Bool
  | .flip _ b => some b
  | _ => none

lemma flipCount_eq {n : ℕ} (α : List (Ev n)) : flipCount α = (α.filterMap coin?).length := by
  induction α with
  | nil => rfl
  | cons e α ih =>
    cases e <;> simp_all [flipCount, coin?, filterMap_cons]

lemma coinify_of_coin_none {n : ℕ} (ω : ℕ → Bool) (α : List (Ev n)) {e : Ev n}
    (he : coin? e = none) : coinify ω α e = e := by
  cases e <;> simp_all [coinify, coin?]

variable (m) in
/-- The length of a round. -/
def Lr : ℕ := (round m 1 false).length

variable (m) in
/-- The position of the coin flip in a round. -/
def Fp : ℕ := (roundPre m 0).length

lemma length_round (j : ℕ) (b : Bool) : (round m j b).length = Lr m := by
  simp [Lr, round, roundPre, roundPost]

lemma length_roundPre (j : ℕ) : (roundPre m j).length = Fp m := by
  simp [Fp, roundPre]

lemma Fp_lt_Lr : Fp m < Lr m := by
  rw [← length_roundPre 1, ← length_round 1 false, round]; simp

lemma coins_roundPre (j : ℕ) : (roundPre m j).filterMap coin? = [] := by
  simp [roundPre, coin?, filterMap_flatMap, filterMap_cons, filterMap_map, Function.comp_def]

lemma coins_roundPost (j : ℕ) (b : Bool) : (roundPost m j b).filterMap coin? = [] := by
  simp [roundPost, coin?, filterMap_flatMap, filterMap_cons, filterMap_map, Function.comp_def]

lemma coins_take_of_nil {n : ℕ} {l : List (Ev n)} (h : l.filterMap coin? = []) (k : ℕ) :
    (l.take k).filterMap coin? = [] := by
  have := (take_sublist k l).filterMap coin?
  rw [h] at this; exact sublist_nil.1 this

lemma coins_round (j : ℕ) (b : Bool) : (round m j b).filterMap coin? = [b] := by
  simp [round, filterMap_append, coins_roundPre, coins_roundPost, coin?]

lemma coins_take_round (j : ℕ) (b : Bool) (s : ℕ) :
    ((round m j b).take s).filterMap coin? = if s ≤ Fp m then [] else [b] := by
  rw [round, take_append, length_roundPre, filterMap_append,
    coins_take_of_nil (coins_roundPre j)]
  split_ifs with h
  · rw [Nat.sub_eq_zero_of_le h]; simp
  · obtain ⟨k, hk⟩ : ∃ k, s - Fp m = k + 1 := ⟨s - Fp m - 1, by omega⟩
    rw [hk, take_succ_cons, filterMap_cons]
    simp [coin?, coins_take_of_nil (coins_roundPost j b)]

lemma coins_rounds (ω : ℕ → Bool) (r : ℕ) :
    (rounds m ω r).filterMap coin? = (range r).map ω := by
  induction r with
  | zero => rfl
  | succ r ih => rw [rounds, filterMap_append, ih, coins_round, range_succ, map_append]; rfl

lemma getElem?_round_lt {j : ℕ} {b : Bool} {s : ℕ} (h : s < Fp m) :
    (round m j b)[s]? = (roundPre m j)[s]? := by
  rw [round, getElem?_append_left (by rw [length_roundPre]; exact h)]

lemma getElem?_round_Fp (j : ℕ) (b : Bool) : (round m j b)[Fp m]? = some (.flip (hp0 m) b) := by
  rw [round, getElem?_append_right (by rw [length_roundPre]), length_roundPre, Nat.sub_self]
  rfl

lemma getElem?_round_gt {j : ℕ} {b : Bool} {s : ℕ} (h : Fp m < s) :
    (round m j b)[s]? = (roundPost m j b)[s - Fp m - 1]? := by
  rw [round, getElem?_append_right (by rw [length_roundPre]; omega), length_roundPre]
  obtain ⟨k, hk⟩ : ∃ k, s - Fp m = k + 1 := ⟨s - Fp m - 1, by omega⟩
  rw [hk, getElem?_cons_succ, Nat.add_sub_cancel]

/-- The `i`-th event of the run with coins `c`. -/
def evAt (c : ℕ → Bool) (i : ℕ) : Ev (m + 3) :=
  (round m (i / Lr m + 1) (c (i / Lr m)))[i % Lr m]?.getD (.noop (hp0 m))

/-- The `k`-th coin of the history `α` (`false` if there is none yet). -/
def coinsOf {n : ℕ} (α : List (Ev n)) (k : ℕ) : Bool := ((α.filterMap coin?)[k]?).getD false

variable (m) in
/-- **The adversary** of Theorem 6: it reads the coins off the history and schedules the next
event of the run of Figures 1–2. -/
def adv (α : List (Ev (m + 3))) : Ev (m + 3) := evAt (coinsOf α) α.length

lemma map_range_getD {X : Type} (l : List X) (d : X) (s : ℕ) (hs : s ≤ l.length) :
    (range s).map (fun t => l[t]?.getD d) = l.take s := by
  apply ext_getElem
  · simp; omega
  · intro i h1 h2
    simp at h1
    simp [getElem?_eq_getElem (show i < l.length by omega)]

lemma evAt_add (c : ℕ → Bool) (r t : ℕ) (ht : t < Lr m) :
    evAt c (r * Lr m + t) = (round m (r + 1) (c r))[t]?.getD (.noop (hp0 m)) := by
  have hL : 0 < Lr m := by have := Fp_lt_Lr (m := m); omega
  have h1 : (r * Lr m + t) / Lr m = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt ht, zero_add]
  have h2 : (r * Lr m + t) % Lr m = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  simp only [evAt, h1, h2]

lemma map_evAt (ω : ℕ → Bool) (r s : ℕ) (hs : s ≤ Lr m) :
    (range (r * Lr m + s)).map (evAt ω) = rounds m ω r ++ (round m (r + 1) (ω r)).take s := by
  induction r generalizing s with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, rounds, nil_append]
    rw [← map_range_getD _ _ s (by rw [length_round]; exact hs)]
    apply map_congr_left
    intro t ht; simp at ht
    have := evAt_add (m := m) ω 0 t (by omega); simpa using this
  | succ r ih =>
    rw [show (r + 1) * Lr m + s = (r * Lr m + Lr m) + s by rw [Nat.add_mul, Nat.one_mul],
      range_add, map_append,
      ih (Lr m) le_rfl, take_of_length_le (by rw [length_round]), ← rounds, map_map]
    congr 1
    rw [← map_range_getD _ (.noop (hp0 m)) s (by rw [length_round]; exact hs)]
    apply map_congr_left
    intro t ht; simp at ht
    simp only [Function.comp_apply]
    rw [show r * Lr m + Lr m + t = (r + 1) * Lr m + t by rw [Nat.add_mul, Nat.one_mul],
      evAt_add ω (r + 1) t (by omega)]

lemma genRun_adv (ω : ℕ → Bool) (i : ℕ) : genRun (adv m) ω i = (range i).map (evAt ω) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [genRun, ih, range_succ, map_append, map_singleton]
    congr 2
    have hL : 0 < Lr m := by have := Fp_lt_Lr (m := m); omega
    set r := i / Lr m
    set s := i % Lr m
    have hs : s < Lr m := Nat.mod_lt _ hL
    have hi : i = r * Lr m + s := by rw [mul_comm]; exact (Nat.div_add_mod i (Lr m)).symm
    have hα := map_evAt ω r s hs.le
    rw [← hi] at hα
    rw [hα]
    have hlen : (rounds m ω r ++ take s (round m (r + 1) (ω r))).length = i := by
      rw [← hα]; simp
    have hcoins : (rounds m ω r ++ take s (round m (r + 1) (ω r))).filterMap coin? =
        (range r).map ω ++ (if s ≤ Fp m then [] else [ω r]) := by
      rw [filterMap_append, coins_rounds, coins_take_round]
    simp only [adv, hlen]
    rw [hi, evAt_add _ r s hs, evAt_add _ r s hs]
    rcases lt_trichotomy s (Fp m) with h | h | h
    · rw [getElem?_round_lt h, getElem?_round_lt h]
      apply coinify_of_coin_none
      have hmem : ((roundPre m (r + 1))[s]?.getD (.noop (hp0 m))) ∈ roundPre m (r + 1) := by
        rw [getElem?_eq_getElem (by rw [length_roundPre]; exact h)]; simp
      have := coins_roundPre (m := m) (r + 1)
      rw [filterMap_eq_nil_iff] at this
      exact this _ hmem
    · rw [h, getElem?_round_Fp, getElem?_round_Fp]
      simp only [Option.getD_some, coinify, flipCount_eq]
      simp [coins_rounds, coins_take_round]
    · have hc : coinsOf (rounds m ω r ++ take s (round m (r + 1) (ω r))) r = ω r := by
        rw [coinsOf, hcoins, ite_eq_right (by omega)]; simp
      rw [hc]
      apply coinify_of_coin_none
      rw [getElem?_round_gt h]
      cases hget : (roundPost m (r + 1) (ω r))[s - Fp m - 1]? with
      | none => rfl
      | some e =>
        have hmem : e ∈ roundPost m (r + 1) (ω r) := mem_of_getElem? hget
        have := coins_roundPost (m := m) (r + 1) (ω r)
        rw [filterMap_eq_nil_iff] at this
        exact this _ hmem

/-! ## The theorem -/

lemma genRun_adv_rounds (ω : ℕ → Bool) (J : ℕ) : genRun (adv m) ω (J * Lr m) = rounds m ω J := by
  rw [genRun_adv, ← Nat.add_zero (J * Lr m), map_evAt ω J 0 (Nat.zero_le _)]; simp

lemma genRun_adv_prefix (ω : ℕ → Bool) (i : ℕ) : genRun (adv m) ω i <+: rounds m ω (i + 1) := by
  have hL : 0 < Lr m := by have := Fp_lt_Lr (m := m); omega
  rw [← genRun_adv_rounds, genRun_adv, genRun_adv]
  apply IsPrefix.map
  have hle : i ≤ (i + 1) * Lr m := by
    calc i ≤ (i + 1) * 1 := by omega
      _ ≤ (i + 1) * Lr m := Nat.mul_le_mul_left _ hL
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, range_add]; exact prefix_append _ _

lemma procRun_isSome_of_prefix {n : ℕ} (p : Fin n) {α β : List (Ev n)} (h : α <+: β)
    (hβ : (procRun p β).isSome) : (procRun p α).isSome := by
  obtain ⟨γ, rfl⟩ := h
  rw [procRun_eq_pfold, pfold_append, ← procRun_eq_pfold] at hβ
  cases hα : procRun p α with
  | none => rw [hα, pfold_none] at hβ; exact absurd hβ (by simp)
  | some _ => rfl

end Podc.RegisterLinTermination.Game.Thm6

namespace Podc.RegisterLinTermination.Game

open Cslib.SharedMemory Thm6

/-- **Theorem 6** of Hadzilacos–Hu–Toueg (PODC 2021). If the registers `R1`, `R2`, `C` of
Algorithm 1 are only linearizable, a strong adversary can construct a run of Algorithm 1 in which
all processes execute infinitely many rounds: there is an adversary `σ` such that for **every**
sequence of coin flips `ω`, every finite prefix of the generated run follows the code and has
linearizable register histories, and every process enters every round `j ≥ 1`. -/
theorem theorem6 (n : ℕ) (hn : 3 ≤ n) : ∃ σ : List (Ev n) → Ev n, ∀ ω : ℕ → Bool,
    (∀ m, Valid (genRun σ ω m) ∧ LinRegs (genRun σ ω m)) ∧
      ∀ p j, 1 ≤ j → ∃ m, Entered p j (genRun σ ω m) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  refine ⟨adv k, fun ω => ⟨fun i => ⟨fun p => ?_, fun x => ?_⟩, fun p j hj => ?_⟩⟩
  · apply procRun_isSome_of_prefix p (genRun_adv_prefix ω i)
    rw [procRun_rounds]; rfl
  · exact isLinearization_of_prefix_rounds x ω (i + 1)
      ((genRun_adv_prefix ω i).filterMap (Ev.toLabel x))
  · refine ⟨(j - 1) * Lr k, _, List.prefix_refl _, ?_⟩
    rw [genRun_adv_rounds, procRun_rounds, Nat.sub_add_cancel hj, startLoc]
    split_ifs <;> simp
