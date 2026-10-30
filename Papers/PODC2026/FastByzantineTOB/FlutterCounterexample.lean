import Papers.PODC2026.FastByzantineTOB.FlutterExample

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-!
# Flutter with the paper's lock-time quorum is not safe for `n = 5f + 2`

The abstract says Flutter "assumes … at least `5f + 1` servers"; the model (§2.1) fixes
`n = 5f + 1`. Flutter's lock time uses the fixed quorum `4f + 1` (line 20). For `n = 5f + 2` the
`f + 1` correct servers that support a message (Representative Validity) and the `4f + 1` servers
that announce a time past its bet need not intersect, Lemma 16 fails, and so does Total Order —
whatever (correct) Representative Binary Consensus is used.

Run for `f = 1`, `n = 7` (servers `0–6`, server `6` Byzantine), two correct clients `0` and `1`,
`Δ̃ = ε = 5`, lock quorum `q = 4f + 1 = 5`:
* client `0` (clock `0`) broadcasts `y` with bet `10`; client `1` (clock `10`) broadcasts `z` with
  bet `20`;
* servers `0, 1` receive `y` in time and propose `True` for `y`; servers `2–5` receive `z` in time,
  propose `True` for `z`, relay it, and schedule `beat()` at time `20` (the other client messages
  are still in transit);
* servers `2–5` reach time `20` and execute the scheduled `beat()`;
* server `2` receives the `Observe z` and `Time 20` messages of `2–5` (FIFO order) and a `Time 20`
  from the Byzantine `6` (lock time `20`), `con[z]`
  decides `True`, and server `2` delivers `z` — it never saw `y`;
* server `0` receives the same `Time` messages, `con[y]` decides `True`, and server `0` delivers `y`.

Both decisions are supported by at least `f + 1 = 2` correct proposals, so the black box satisfies
Representative Validity and Agreement; yet server `0` delivered `[y]` and server `2` delivered `[z]`.
With the quorum `n − f` (or `n = 5f + 1`) the hypothesis `n < (f + 1) + q` of
`theorem8_totalOrder` holds and Total Order is guaranteed.
-/

namespace Podc.FastByzantineTOB.Flutter

/-- `f = 1`, `n = 7`, server `6` Byzantine, lock quorum `4f + 1 = 5`, `Δ̃ = ε = 5`. -/
def S7 : Setup (Fin 7) (Fin 2) ℕ :=
  ⟨{6}, ∅, fun _ => isFalse (Set.notMem_empty _), 1, 5, 5, 5⟩

/-- Client `0`'s message, bet `10`. -/
def ty : Tag (Fin 2) Unit ℕ := ⟨10, 0, ()⟩

/-- Client `1`'s message, bet `20`. -/
def tz : Tag (Fin 2) Unit ℕ := ⟨20, 1, ()⟩

/-- The actions of the counterexample run. -/
def acts7 : List (Action (Fin 7) (Fin 2) Unit ℕ) :=
  [.cBroadcast 0 (), .cBroadcast 1 (),
   .cliMsg 0 0 (.message () 10), .cliMsg 1 0 (.message () 10),
   .cliMsg 2 1 (.message () 20), .cliMsg 3 1 (.message () 20),
   .cliMsg 4 1 (.message () 20), .cliMsg 5 1 (.message () 20),
   .tick 2 20, .tick 3 20, .tick 4 20, .tick 5 20,
   .beat 2, .beat 3, .beat 4, .beat 5,
   -- server 2 reaches lock time 20 and delivers `z`
   .srvRecv 2 2 (.observe tz), .srvRecv 2 2 (.time 20), .srvRecv 2 3 (.observe tz),
   .srvRecv 2 3 (.time 20), .srvRecv 2 4 (.observe tz), .srvRecv 2 4 (.time 20),
   .srvRecv 2 5 (.observe tz), .srvRecv 2 5 (.time 20),
   .srvRecv 2 6 (.time 20),
   .decide 2 tz true, .process 2 tz true,
   -- server 0 reaches lock time 20 and delivers `y`
   .decide 0 ty true,
   .srvRecv 0 2 (.observe tz), .srvRecv 0 2 (.time 20), .srvRecv 0 3 (.observe tz),
   .srvRecv 0 3 (.time 20), .srvRecv 0 4 (.observe tz), .srvRecv 0 4 (.time 20),
   .srvRecv 0 5 (.observe tz), .srvRecv 0 5 (.time 20),
   .srvRecv 0 6 (.time 20),
   .process 0 ty true]

/-- Initial clocks: servers `0`, client `0` at `0`, client `1` at `10`. -/
def init7 : State (Fin 7) (Fin 2) Unit ℕ :=
  State.init (fun _ => 0) (fun θ => if θ = 0 then 0 else 10)

lemma valid7 : ValidList S7 init7 acts7 := by
  unfold ValidList
  decide

/-- The counterexample run. -/
noncomputable def R7 : Run (M := Unit) S7 :=
  Run.ofList S7 (fun _ => 0) (fun θ => if θ = 0 then 0 else 10) acts7 valid7

lemma R7_final (k : ℕ) (hk : acts7.length ≤ k) :
    R7.st k = listState S7 init7 acts7 acts7.length := by
  simp [R7, Run.ofList, listState, init7, List.take_of_length_le hk]

lemma R7_decs (k : ℕ) (p : Fin 7) (x : Tag (Fin 2) Unit ℕ) (v : Bool)
    (h : (x, v) ∈ ((R7.st k).srv p).decs) : (x = ty ∨ x = tz) ∧ v = true := by
  have h' := R7.mono_of_lstep (fun l => l.decs) (fun _ _ h => h.decs_mono) p
    (le_max_left k acts7.length) h
  rw [R7_final _ (le_max_right _ _)] at h'
  have hd : ∀ p : Fin 7, ((listState S7 init7 acts7 acts7.length).srv p).decs ⊆
      {(ty, true), (tz, true)} := by decide
  have := hd p h'
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
  tauto

lemma R7_repValidity : ConRepValidity R7 := by
  intro k p x v _ h
  obtain ⟨hx, rfl⟩ := R7_decs k p x v h
  refine ⟨acts7.length, ?_⟩
  rw [R7_final _ le_rfl]
  rcases hx with rfl | rfl <;> decide

lemma R7_agreement : ConAgreement R7 := by
  intro k k' p q x v w _ _ hv hw
  rw [(R7_decs k p x v hv).2, (R7_decs k' q x w hw).2]

/-- **Flutter's Total Order fails for `n = 5f + 2`** with the paper's lock-time quorum `4f + 1`:
`f = 1`, `n = 7`, one Byzantine server, the consensus black box satisfies Representative Validity
and Agreement, and the correct servers `0` and `2` deliver `[y]` and `[z]`. -/
theorem flutter_totalOrder_fails_5f2 :
    Fintype.card (Fin 7) = 5 * S7.f + 2 ∧ S7.F.card ≤ S7.f ∧ S7.q = 4 * S7.f + 1 ∧
      ConRepValidity R7 ∧ ConAgreement R7 ∧
      ((R7.st acts7.length).srv 0).dels = [(0, ())] ∧
      ((R7.st acts7.length).srv 2).dels = [(1, ())] := by
  refine ⟨rfl, by decide, rfl, R7_repValidity, R7_agreement, ?_, ?_⟩ <;>
    (rw [R7_final _ le_rfl]; decide)

/-- The two delivery sequences are not prefixes of one another (so `theorem8_totalOrder` fails
without its hypothesis `n < (f + 1) + q`). -/
theorem flutter_not_prefix_5f2 :
    ¬ (((R7.st acts7.length).srv 0).dels <+: ((R7.st acts7.length).srv 2).dels ∨
      ((R7.st acts7.length).srv 2).dels <+: ((R7.st acts7.length).srv 0).dels) := by
  obtain ⟨-, -, -, -, -, h0, h2⟩ := flutter_totalOrder_fails_5f2
  rw [h0, h2]
  decide

end Podc.FastByzantineTOB.Flutter
