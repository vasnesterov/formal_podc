import Cslib.Computability.Distributed.SharedMemory.Linearization

-- CSLib candidate: `runOps_reads`, `not_precedes_of_after`, `resp_eq_linState`,
-- `linState_eq_of_last_write` (Cslib/Computability/Distributed/SharedMemory/Register…)

/-!
# Linearizations of the histories of the impossibility proof

In all executions of the proof, both writes return before both reads are invoked. Then, in every
linearization, both reads return the value of the last write of the linearization
(`resp_eq_linState`), so the two reads return the same value; if moreover `W₁` precedes `W₂` in
real time, that value is the one written by `W₂` (`linState_eq_of_last_write`).
-/

namespace Podc.FastMWMR

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {v₀ : V}

lemma runOps_reads (q : V) (os : List (RWOp V)) (hos : ∀ o ∈ os, o = .read) :
    (register V v₀).runOps q os = q := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, hos o (by simp)]
    exact ih _ fun o' ho' => hos o' (by simp [ho'])

/-- Elements after a given position of a linearization do not precede it in real time. -/
lemma not_precedes_of_after {h : List (Label P (register V v₀))}
    {L : List (OpId P × RWOp V)} (hL : IsLinearization h L) {A' B : List (OpId P × RWOp V)}
    {y z : OpId P × RWOp V} (hsplit : L = A' ++ y :: B) (hz : z ∈ B) :
    ¬ Precedes h z.1 y.1 := by
  intro hp
  have hy : y.1 ∈ L.map Prod.fst := by simp [hsplit]
  have hsub := hL.realtime _ _ hp hy
  have hnd := hL.nodup
  rw [hsplit, List.map_append, List.map_cons] at hsub hnd
  have hzA := mem_left_of_sublist_pair hnd hsub
  have hzB : z.1 ∈ B.map Prod.fst := List.mem_map_of_mem hz
  rw [List.nodup_append] at hnd
  exact hnd.2.2 _ hzA _ (List.mem_cons_of_mem _ hzB) rfl

/-- A completed read that is preceded in real time by every write of the linearization returns
the final state of the linearization. -/
lemma resp_eq_linState {h : List (Label P (register V v₀))} {L : List (OpId P × RWOp V)}
    (hL : IsLinearization h L) {x : OpId P} (hx : opOf h x = some .read) (hc : Completed h x)
    {v : V} (hv : respOf h x = some v)
    (hw : ∀ z ∈ L, (∃ u, z.2 = .write u) → Precedes h z.1 x) : v = linState (A := register V v₀) L := by
  obtain ⟨y, hyL, hyx⟩ := List.mem_map.1 (hL.complete x hc)
  have hy2 : y.2 = .read := by
    have := hL.op_eq y hyL; rw [hyx, hx] at this; exact (Option.some.inj this).symm
  obtain ⟨A', B, hsplit⟩ := List.append_of_mem hyL
  have hB : ∀ z ∈ B, z.2 = .read := by
    intro z hz
    cases hz2 : z.2 with
    | read => rfl
    | write u =>
      exact absurd (hyx ▸ hw z (by simp [hsplit, hz]) ⟨u, hz2⟩)
        (not_precedes_of_after hL hsplit hz)
  have hseq := hL.seq
  rw [hsplit, seqOK_append] at hseq
  obtain ⟨y1, y2⟩ := y
  simp only at hyx hy2; subst hyx hy2
  have h1 := hseq.2.1 v hv
  rw [linState, hsplit, List.map_append, ObjSpec.runOps_append, List.map_cons,
    ObjSpec.runOps_cons, register_read]
  rw [runOps_reads _ _ (fun o ho => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ho; exact hB z hz)]
  exact h1.symm

/-- If every other write of the linearization precedes the write `x` in real time, the final
state of the linearization is the value written by `x`. -/
lemma linState_eq_of_last_write {h : List (Label P (register V v₀))}
    {L : List (OpId P × RWOp V)} (hL : IsLinearization h L) {x : OpId P} {u : V}
    (hx : opOf h x = some (.write u)) (hc : Completed h x)
    (hw : ∀ z ∈ L, (∃ u, z.2 = .write u) → z.1 ≠ x → Precedes h z.1 x) : linState (A := register V v₀) L = u := by
  obtain ⟨y, hyL, hyx⟩ := List.mem_map.1 (hL.complete x hc)
  have hy2 : y.2 = .write u := by
    have := hL.op_eq y hyL; rw [hyx, hx] at this; exact (Option.some.inj this).symm
  obtain ⟨A', B, hsplit⟩ := List.append_of_mem hyL
  have hB : ∀ z ∈ B, z.2 = .read := by
    intro z hz
    cases hz2 : z.2 with
    | read => rfl
    | write u' =>
      have hne : z.1 ≠ x := by
        intro he
        have hnd := hL.nodup
        rw [hsplit, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd
        apply hnd.2.1.1
        have := List.mem_map_of_mem (f := Prod.fst) hz
        rw [he, ← hyx] at this; exact this
      exact absurd (hyx ▸ hw z (by simp [hsplit, hz]) ⟨u', hz2⟩ hne)
        (not_precedes_of_after hL hsplit hz)
  obtain ⟨y1, y2⟩ := y
  simp only at hyx hy2; subst hyx hy2
  rw [linState, hsplit, List.map_append, ObjSpec.runOps_append, List.map_cons,
    ObjSpec.runOps_cons, register_write]
  exact runOps_reads _ _ (fun o ho => by obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ho; exact hB z hz)

/-- In a history `hW ++ tail` where `hW` contains exactly the writes `(w₁, 0)` and `(w₂, 0)` and
`tail` contains only reads, the writes of a linearization are `(w₁, 0)` and `(w₂, 0)`. -/
lemma write_id_of_mem {hW tail : List (Label P (register V v₀))} {w₁ w₂ : P} {a b : V}
    (h₁ : opsOf hW w₁ = [.write a]) (h₂ : opsOf hW w₂ = [.write b])
    (hO : ∀ p, p ≠ w₁ → p ≠ w₂ → opsOf hW p = []) (hT : ∀ p, ∀ o ∈ opsOf tail p, o = .read)
    {L : List (OpId P × RWOp V)} (hL : IsLinearization (hW ++ tail) L) {z : OpId P × RWOp V}
    (hz : z ∈ L) (hw : ∃ u, z.2 = .write u) : z.1 = (w₁, 0) ∨ z.1 = (w₂, 0) := by
  obtain ⟨⟨p, k⟩, o⟩ := z
  obtain ⟨u, rfl⟩ := hw
  have hop' := hL.op_eq _ hz
  simp only [opOf, opsOf_append] at hop'
  by_cases hp₁ : p = w₁
  · subst hp₁
    rw [h₁] at hop'
    rcases k with _ | k
    · exact Or.inl rfl
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ] at hop'
      exact absurd (hT _ _ (List.mem_of_getElem? hop')) (by simp)
  by_cases hp₂ : p = w₂
  · subst hp₂
    rw [h₂] at hop'
    rcases k with _ | k
    · exact Or.inr rfl
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ] at hop'
      exact absurd (hT _ _ (List.mem_of_getElem? hop')) (by simp)
  rw [hO p hp₁ hp₂, List.nil_append] at hop'
  exact absurd (hT _ _ (List.mem_of_getElem? hop')) (by simp)

/-- In a history `hW ++ tail` where `hW` consists of two completed writes `W₁ = (w₁, 0)`,
`W₂ = (w₂, 0)` and `tail` contains only reads, every completed read `(r, 0)` of `tail` returns the
final state of any linearization. -/
lemma resp_eq_of_writes_first {hW tail : List (Label P (register V v₀))} {w₁ w₂ : P} {a b : V}
    (h₁ : opsOf hW w₁ = [.write a]) (h₂ : opsOf hW w₂ = [.write b])
    (hO : ∀ p, p ≠ w₁ → p ≠ w₂ → opsOf hW p = []) (hR₁ : respsOf hW w₁ ≠ [])
    (hR₂ : respsOf hW w₂ ≠ []) (hT : ∀ p, ∀ o ∈ opsOf tail p, o = .read) {r : P}
    (hr₁ : r ≠ w₁) (hr₂ : r ≠ w₂) (hrR : respsOf hW r = []) (hop : opsOf tail r = [.read])
    {v : V} (hres : respsOf tail r = [v]) {L : List (OpId P × RWOp V)}
    (hL : IsLinearization (hW ++ tail) L) : v = linState (A := register V v₀) L := by
  have hpre : ∀ w, (w = w₁ ∨ w = w₂) → Precedes (hW ++ tail) (w, 0) (r, 0) := by
    intro w hw
    refine ⟨hW, tail, rfl, ?_, ?_⟩
    · rcases hw with rfl | rfl
      · simpa [Completed, List.length_pos_iff] using hR₁
      · simpa [Completed, List.length_pos_iff] using hR₂
    · simp [Invoked, hO r hr₁ hr₂]
  refine resp_eq_linState (x := (r, 0)) hL ?_ ?_ ?_ ?_
  · simp [opOf, hO r hr₁ hr₂, hop]
  · simp [Completed, hrR, hres]
  · simp [respOf, hrR, hres]
  · intro z hz hw
    rcases write_id_of_mem h₁ h₂ hO hT hL hz hw with h | h <;> rw [h]
    · exact hpre _ (Or.inl rfl)
    · exact hpre _ (Or.inr rfl)

end Podc.FastMWMR
