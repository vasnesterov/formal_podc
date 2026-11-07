import Papers.PODC2010.MultiVersionSTM.Basic

/-!
# Full-information STMs

Any *strategy* — a response function of the history so far — is an STM: a single base object
holds the history, and each transactional step appends its event to it (`ofStrategy`). This is
how we build the competing STMs `X'` in the proof of Theorem 1.
-/

namespace Podc.MultiVersionSTM

variable {Tx O P : Type} [TxSys Tx P]

/-- The full-information STM running the strategy `f`: one base object stores the history. -/
noncomputable def ofStrategy (f : Hist Tx O → Inv Tx O → Resp Tx) : STM Tx O P where
  B := Unit
  M := Hist Tx O
  L := Unit
  mem₀ := fun _ => []
  loc₀ := fun _ => ()
  prog := fun _ _ i => .access () (fun h => h ++ [⟨i, f h i⟩]) (fun h => .ret ((), f h i))

namespace ofStrategy

variable (f : Hist Tx O → Inv Tx O → Resp Tx)

lemma conf_mem (σ : List (Inv Tx O)) :
    ((ofStrategy (P := P) f).conf σ).mem () = (ofStrategy (P := P) f).hist σ := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton σ i ih =>
    rw [STM.hist_snoc, STM.conf_snoc, ← ih]
    simp [STM.step, STM.resp, ofStrategy, Prog.run]

lemma resp_eq (σ : List (Inv Tx O)) (i : Inv Tx O) :
    (ofStrategy (P := P) f).resp σ i = f ((ofStrategy (P := P) f).hist σ) i := by
  rw [← conf_mem]
  simp [STM.step, STM.resp, ofStrategy, Prog.run]

/-- The history of a full-information STM, computed by the strategy. -/
lemma hist_snoc (σ : List (Inv Tx O)) (i : Inv Tx O) :
    (ofStrategy (P := P) f).hist (σ ++ [i]) =
      (ofStrategy (P := P) f).hist σ ++ [⟨i, f ((ofStrategy (P := P) f).hist σ) i⟩] := by
  rw [STM.hist_snoc, resp_eq]

end ofStrategy

end Podc.MultiVersionSTM
