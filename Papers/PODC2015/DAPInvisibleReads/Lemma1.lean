import Papers.PODC2015.DAPInvisibleReads.Commute
import Mathlib.Tactic.FinCases

/-!
# Lemma 1 is false

Lemma 1 of the paper: *in a WDAP TM two concurrent disjoint-access transactions cannot contend on
a common base object* (not even at different times). Its proof only considers executions in
which the two transactions are the only ones taking steps: it postpones the first contending
event of `Tⱼ` so that it becomes concurrent with that of `Tᵢ`. With a third process the claim
fails: information can flow from `Tᵢ` to `Tⱼ` through two *different* transactions of a third
process, the first one sharing an object with `Tᵢ` and the second one sharing an object with
`Tⱼ`. Then `Tⱼ` can read a base object written by `Tᵢ` *after* `Tᵢ` wrote it for the last time,
so the two never concurrently contend, and yet they are disjoint-access.

`chainTM` (three processes, two objects `x₀, x₁`):
* base objects `o(y,q)` (written once, by `q`'s first write to `y`) and `f(x)` (a "board" for
  `x`: a list of pairs `(y,q)` whose `o(y,q)` is known to be written);
* `write x v` by `p`: write `o(x,p)` (if not yet done), then publish everything `p` knows on
  `f(x)`;
* `read x`: read `f(x)`, then read `o(y,q)` for every published pair and `o(x,q)` for every `q`;
  record the written ones.

`chainTM_strongWDAP`: in every reachable configuration, two processes poised to contend on a base
object run transactions whose data sets intersect (so `chainTM` is WDAP in any reading of the
definition based on data sets / the conflict graph of Attiya, Hillel and Milani).

`lemma_1_false`: in the execution `Tᵢ = W(x₀)` (left live), `T_k1 = R(x₀) c`, `T_k2 = W(x₁) c`,
`Tⱼ = R(x₁)…` (left live), `Tᵢ` and `Tⱼ` are concurrent and disjoint-access (`Tᵢ — T_k1` and
`T_k2 — Tⱼ` are the only conflict edges), and `Tⱼ` reads the base object `o(x₀, i)` that `Tᵢ`
wrote.
-/

namespace Podc.DAPInvisibleReads

open Cslib.SharedMemory

/-! ### General definitions -/

section General

variable {X V P : Type} [DecidableEq P] {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]
variable (I : Impl (tmSpec X V) B P L)

omit [DecidableEq ι] in
lemma pstate_concat (α : List (Lbl P X V)) (ℓ : Lbl P X V) (p : P) :
    pstate (α ++ [ℓ]) p = if ℓ.proc = p then (pstate α p).step ℓ else pstate α p := by
  simp only [pstate, projP, List.filter_append, List.filter_cons, List.filter_nil]
  split_ifs <;> simp_all

/-- The pending operation of a process is the pending operation of its current transaction. -/
lemma pend_eq_pstate {α : List (Lbl P X V)} {C : Config (tmSpec X V) B P L}
    (h : I.run α = some C) (p : P) : C.pend p = (pstate α p).cur.pend := by
  refine Impl.run_induction (I := I) (Q := fun α C => ∀ p, C.pend p = (pstate α p).cur.pend)
    (fun _ => rfl) ?_ h p
  intro α C ℓ C' _ hQ hs p
  rw [pstate_concat]
  cases ℓ with
  | inv q o =>
    obtain ⟨-, -, h1, -, -⟩ := Impl.step_inv hs
    by_cases hq : q = p
    · subst hq; simp [h1, PState.step, Label.proc]
    · simp [h1, Function.update_of_ne (Ne.symm hq), hq, Label.proc, hQ p]
  | tau q =>
    obtain ⟨-, h1, -⟩ := Impl.step_tau hs
    split_ifs <;> simp [h1, PState.step, hQ p]
  | ret q r =>
    obtain ⟨h0, h1, -⟩ := Impl.step_ret hs
    by_cases hq : q = p
    · subst hq
      rw [hQ q] at h0
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
      simp only [h1, Function.update_self, Label.proc, ite_true, PState.step, ho]
      split_ifs <;> rfl
    · simp [h1, Function.update_of_ne (Ne.symm hq), hq, Label.proc, hQ p]

omit [DecidableEq P] in
lemma txRec_cur [DecidableEq P] (α : List (Lbl P X V)) (p : P) :
    txRec α (cur α p) = (pstate α p).cur := by
  simp [txRec, cur]

/-- `T` is live at the end of `h`: it has begun and has not ended. -/
def Live (h : List (Lbl P X V)) (T : TxId P) : Prop := cur h T.1 = T ∧ Began h T

instance [DecidableEq X] [DecidableEq V] (h : List (Lbl P X V)) (T : TxId P) :
    Decidable (Live h T) := by
  unfold Live; infer_instance

/-- In the execution `α`, transaction `T` takes a step applying primitive `o` to base object `i`. -/
def StepOn (α : List (Lbl P X V)) (T : TxId P) (i : ι) (o : (B i).Op) : Prop :=
  ∃ α₁ α₂ C k, α = α₁ ++ .tau T.1 :: α₂ ∧ I.run α₁ = some C ∧ cur α₁ T.1 = T ∧
    I.act T.1 (C.loc T.1) = .access i o k

/-- **The claim of Lemma 1** for the TM `I`: two concurrent disjoint-access transactions (here: of
different processes, both live at the end of the execution) never contend on a base object. -/
def Lemma1Claim : Prop :=
  ∀ (α : List (Lbl P X V)) (T T' : TxId P), I.Valid α → T.1 ≠ T'.1 → Live α T → Live α T' →
    ¬ Connected α T T' → ∀ (i : ι) (o o' : (B i).Op), StepOn I α T i o → StepOn I α T' i o' →
      Trivial o ∧ Trivial o'

/-- A strong form of WDAP: two processes poised to contend on a base object run transactions
whose data sets intersect (a direct edge of the conflict graph). -/
def StrongWDAP : Prop :=
  ∀ (α : List (Lbl P X V)) (C : Config (tmSpec X V) B P L), I.run α = some C →
    ∀ a b, a ≠ b → C.pend a ≠ none → C.pend b ≠ none →
    ∀ (i : ι) (o o' : (B i).Op) k k', I.act a (C.loc a) = .access i o k →
      I.act b (C.loc b) = .access i o' k' → (¬ Trivial o ∨ ¬ Trivial o') →
      (DSet α (cur α a) ∩ DSet α (cur α b)).Nonempty

lemma StrongWDAP.wdap {I : Impl (tmSpec X V) B P L} (h : StrongWDAP I) : WDAP I := by
  intro α C hC a b hab ha hb i o o' k k' h1 h2 hnt
  have began : ∀ p, C.pend p ≠ none → Began α (cur α p) := by
    intro p hp
    right; rw [txRec_cur, ← pend_eq_pstate I hC]; exact hp
  exact Relation.ReflTransGen.single ⟨began a ha, began b hb, h α C hC a b hab ha hb i o o' k k'
    h1 h2 hnt⟩

end General

/-! ### The counterexample TM -/

namespace Lemma1

/-- Pairs `(y, q)`: base object `o(y,q)`. -/
abbrev Pair := Fin 2 × Fin 3

/-- Base objects: `inl (y,q)` is `o(y,q)`, `inr x` is the board `f(x)`. -/
abbrev Obj := Pair ⊕ Fin 2

/-- Every base object is a read/write register holding a list of pairs. -/
abbrev Bk : Obj → ObjSpec := fun _ => register (List Pair) []

/-- Phases of an operation. -/
inductive Ph | start | scan | wf | fin
  deriving DecidableEq

/-- Local state of a process. -/
structure LS where
  /-- the pending operation -/
  cur : Option (TOp (Fin 2) ℕ)
  /-- objects `y` for which `o(y, self)` has been written -/
  wr : List (Fin 2)
  /-- pairs known to be written -/
  K : List Pair
  /-- remaining base objects to read in a `read` -/
  todo : List Pair
  /-- phase of the pending operation -/
  ph : Ph
  deriving DecidableEq

/-- The pairs `(x, q)` for all processes `q`. -/
def scanList (x : Fin 2) : List Pair := (List.finRange 3).map (fun q => (x, q))

/-- The program of process `p`. -/
def act (p : Fin 3) (l : LS) : Action (tmSpec (Fin 2) ℕ) Bk LS :=
  match l.cur, l.ph with
  | some (.read x), .start =>
    .access (.inr x) .read
      (fun v => { l with K := l.K ++ v, todo := v ++ scanList x, ph := .scan })
  | some (.read _), .scan =>
    match l.todo with
    | [] => .ret (some 0) { l with cur := none, todo := [], ph := .start }
    | pr :: rest =>
      .access (.inl pr) .read
        (fun v => { l with K := if v = [] then l.K else pr :: l.K, todo := rest })
  | some (.write x _), .start =>
    if x ∈ l.wr then .access (.inl (x, p)) .read (fun _ => { l with ph := .wf })
    else .access (.inl (x, p)) (.write [(x, p)])
      (fun _ => { l with wr := x :: l.wr, K := (x, p) :: l.K, ph := .wf })
  | some (.write x _), .wf => .access (.inr x) (.write l.K) (fun _ => { l with ph := .fin })
  | some (.write _ v), _ => .ret (some v) { l with cur := none, todo := [], ph := .start }
  | some _, _ => .ret (some 0) { l with cur := none, todo := [], ph := .start }
  | none, _ => .ret none l

instance : DecidableEq (tmSpec (Fin 2) ℕ).Resp := inferInstanceAs (DecidableEq (Option ℕ))

/-- The counterexample TM. -/
def chainTM : Impl (tmSpec (Fin 2) ℕ) Bk (Fin 3) LS where
  memInit := fun _ => []
  locInit := fun _ => ⟨none, [], [], [], .start⟩
  invoke := fun _ l o => { l with cur := some o, todo := [], ph := .start }
  act := act

instance (p : Fin 3) (o : TOp (Fin 2) ℕ) : Decidable (chainTM.allowed p o) := isTrue trivial

/-! ### The invariant -/

/-- The invariant of `chainTM`. -/
structure Inv (C : Config (tmSpec (Fin 2) ℕ) Bk (Fin 3) LS) : Prop where
  pend : ∀ p, C.pend p = (C.loc p).cur
  wr : ∀ y q, y ∈ (C.loc q).wr ↔ C.mem (.inl (y, q)) ≠ []
  known : ∀ p, ∀ pr ∈ (C.loc p).K, C.mem (.inl pr) ≠ []
  board : ∀ x, ∀ pr ∈ C.mem (.inr x), C.mem (.inl pr) ≠ []
  todo : ∀ p, ∀ pr ∈ (C.loc p).todo, (C.loc p).cur = some (.read pr.1) ∨ C.mem (.inl pr) ≠ []

/-- The cases of a base-object access. -/
lemma act_access {p : Fin 3} {l : LS} {i : Obj} {o : (Bk i).Op} {k : (Bk i).Resp → LS}
    (h : act p l = .access i o k) :
    (∃ x, i = .inr x ∧ l.ph = .start ∧ l.cur = some (.read x) ∧ o = .read ∧
        k = fun v => { l with K := l.K ++ v, todo := v ++ scanList x, ph := .scan }) ∨
    (∃ x pr rest, i = .inl pr ∧ l.cur = some (.read x) ∧ l.ph = .scan ∧ l.todo = pr :: rest ∧
        o = .read ∧
        k = fun v => { l with K := if v = [] then l.K else pr :: l.K, todo := rest }) ∨
    (∃ x v, i = .inl (x, p) ∧ l.cur = some (.write x v) ∧ l.ph = .start ∧ x ∈ l.wr ∧ o = .read ∧
        k = fun _ => { l with ph := .wf }) ∨
    (∃ x v, i = .inl (x, p) ∧ l.cur = some (.write x v) ∧ l.ph = .start ∧ x ∉ l.wr ∧
        o = .write [(x, p)] ∧
        k = fun _ => { l with wr := x :: l.wr, K := (x, p) :: l.K, ph := .wf }) ∨
    (∃ x v, i = .inr x ∧ l.cur = some (.write x v) ∧ l.ph = .wf ∧ o = .write l.K ∧
        k = fun _ => { l with ph := .fin }) := by
  unfold act at h
  split at h
  · rename_i _ _ x hc hp
    cases h; exact Or.inl ⟨x, rfl, hp, hc, rfl, rfl⟩
  · rename_i _ _ x hc hp
    split at h
    · cases h
    · rename_i pr rest ht
      cases h; exact Or.inr (Or.inl ⟨x, pr, rest, rfl, hc, hp, ht, rfl, rfl⟩)
  · rename_i _ _ x v hc hp
    split_ifs at h with hx
    · cases h; exact Or.inr (Or.inr (Or.inl ⟨x, v, rfl, hc, hp, hx, rfl, rfl⟩))
    · cases h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, v, rfl, hc, hp, hx, rfl, rfl⟩)))
  · rename_i _ _ x v hc hp
    cases h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, v, rfl, hc, hp, rfl, rfl⟩)))
  · cases h
  · cases h
  · cases h

/-- Return steps reset the operation. -/
lemma act_ret {p : Fin 3} {l l' : LS} {r : Option ℕ} (h : act p l = .ret r l') :
    (l.cur ≠ none ∧ l' = { l with cur := none, todo := [], ph := .start }) ∨
      (l.cur = none ∧ l' = l) := by
  rcases l with ⟨cur, wr, K, todo, ph⟩
  rcases cur with _ | (x | ⟨x, v⟩ | _) <;> rcases ph <;> simp only [act] at h <;>
    (try split_ifs at h) <;> (try cases h) <;> (try simp)
  rcases todo with _ | ⟨pr, rest⟩ <;> simp only at h <;> cases h; simp

lemma inv_init : Inv chainTM.initCfg where
  pend := fun _ => rfl
  wr := fun y q => by simp [chainTM, Impl.initCfg]
  known := fun p pr h => by simp [chainTM, Impl.initCfg] at h
  board := fun x pr h => by simp [chainTM, Impl.initCfg] at h
  todo := fun p pr h => by simp [chainTM, Impl.initCfg] at h

lemma inv_step {C C' : Config (tmSpec (Fin 2) ℕ) Bk (Fin 3) LS} {ℓ : Lbl (Fin 3) (Fin 2) ℕ}
    (hC : Inv C) (hs : chainTM.step C ℓ = some C') : Inv C' := by
  cases ℓ with
  | inv q o =>
    obtain ⟨-, -, h1, h2, h3⟩ := Impl.step_inv hs
    refine ⟨fun p => ?_, fun y p => ?_, fun p pr h => ?_, fun x pr h => ?_, fun p pr h => ?_⟩
    · rw [h1, h2]
      by_cases hp : p = q
      · subst hp; simp [chainTM]
      · simp [Function.update_of_ne hp, hC.pend p]
    · rw [h3, h2]
      by_cases hp : p = q
      · subst hp; simp only [Function.update_self, chainTM]; exact hC.wr y p
      · simp only [Function.update_of_ne hp]; exact hC.wr y p
    · rw [h3]; rw [h2] at h
      by_cases hp : p = q
      · subst hp; simp only [Function.update_self, chainTM] at h; exact hC.known _ _ h
      · simp only [Function.update_of_ne hp] at h; exact hC.known _ _ h
    · rw [h3] at h ⊢; exact hC.board x pr h
    · rw [h3]; rw [h2] at h ⊢
      by_cases hp : p = q
      · subst hp; simp [chainTM] at h
      · simp only [Function.update_of_ne hp] at h ⊢; exact hC.todo p pr h
  | ret q r =>
    obtain ⟨h0, h1, h3, l, hl, h2⟩ := Impl.step_ret hs
    have hl' := act_ret hl
    have hK : l.K = (C.loc q).K ∧ l.wr = (C.loc q).wr ∧ l.cur = none ∧
        (∀ pr ∈ l.todo, pr ∈ (C.loc q).todo ∧ (C.loc q).cur = none) := by
      rcases hl' with ⟨-, rfl⟩ | ⟨hn, rfl⟩
      · simp
      · exact ⟨rfl, rfl, hn, fun pr h => ⟨h, hn⟩⟩
    refine ⟨fun p => ?_, fun y p => ?_, fun p pr h => ?_, fun x pr h => ?_, fun p pr h => ?_⟩
    · rw [h1, h2]
      by_cases hp : p = q
      · subst hp; simp [hK.2.2.1]
      · simp [Function.update_of_ne hp, hC.pend p]
    · rw [h3, h2]
      by_cases hp : p = q
      · subst hp; simp only [Function.update_self, hK.2.1]; exact hC.wr y p
      · simp only [Function.update_of_ne hp]; exact hC.wr y p
    · rw [h3]; rw [h2] at h
      by_cases hp : p = q
      · subst hp; simp only [Function.update_self, hK.1] at h; exact hC.known _ _ h
      · simp only [Function.update_of_ne hp] at h; exact hC.known _ _ h
    · rw [h3] at h ⊢; exact hC.board x pr h
    · rw [h3]; rw [h2] at h ⊢
      by_cases hp : p = q
      · subst hp
        simp only [Function.update_self] at h ⊢
        obtain ⟨h4, h5⟩ := hK.2.2.2 pr h
        rcases hC.todo p pr h4 with h6 | h6
        · rw [h5] at h6; cases h6
        · exact Or.inr h6
      · simp only [Function.update_of_ne hp] at h ⊢; exact hC.todo p pr h
  | tau q =>
    obtain ⟨-, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
    -- written `o`-objects stay written
    have mono : ∀ pr, C.mem (.inl pr) ≠ [] → C'.mem (.inl pr) ≠ [] := by
      intro pr hpr
      rw [hmem]
      by_cases hi : Sum.inl pr = i
      · subst hi
        rcases act_access hact with ⟨x, hx, -⟩ | ⟨x, pr', rest, hx, -, -, -, rfl, -⟩ |
          ⟨x, v, hx, -, -, -, rfl, -⟩ | ⟨x, v, hx, -, -, -, rfl, -⟩ | ⟨x, v, hx, -⟩
        · cases hx
        · simpa using hpr
        · simpa using hpr
        · simp
        · cases hx
      · rw [Function.update_of_ne hi]; exact hpr
    have hmemq : ∀ j, j ≠ i → C'.mem j = C.mem j := by
      intro j hj; rw [hmem, Function.update_of_ne hj]
    have hlocp : ∀ p, p ≠ q → C'.loc p = C.loc p := by
      intro p hp; rw [hloc, Function.update_of_ne hp]
    refine ⟨fun p => ?_, fun y p => ?_, fun p pr h => ?_, fun x pr h => ?_, fun p pr h => ?_⟩
    · -- pending operations
      rw [hpend]
      by_cases hp : p = q
      · subst hp
        rw [hloc, Function.update_self, hC.pend]
        rcases act_access hact with ⟨x, -, -, -, -, rfl⟩ | ⟨x, pr', rest, -, -, -, -, -, rfl⟩ |
          ⟨x, v, -, -, -, -, -, rfl⟩ | ⟨x, v, -, -, -, -, -, rfl⟩ | ⟨x, v, -, -, -, -, rfl⟩ <;> rfl
      · rw [hlocp p hp, hC.pend]
    · -- `wr`
      by_cases hp : p = q
      · subst hp
        rw [hloc, Function.update_self]
        rcases act_access hact with ⟨x, rfl, -, -, -, rfl⟩ | ⟨x, pr', rest, rfl, -, -, -, rfl, rfl⟩ |
          ⟨x, v, rfl, -, -, -, rfl, rfl⟩ | ⟨x, v, rfl, -, -, hx, rfl, rfl⟩ |
          ⟨x, v, rfl, -, -, -, rfl⟩
        · simp only [hmemq (.inl (y, p)) (by simp)]; exact hC.wr y p
        · rw [hmem]; by_cases h' : (Sum.inl (y, p) : Obj) = .inl pr'
          · rw [h']; simp only [Function.update_self]; rw [← h']; exact hC.wr y p
          · rw [Function.update_of_ne h']; exact hC.wr y p
        · rw [hmem]; by_cases h' : (Sum.inl (y, p) : Obj) = .inl (x, p)
          · rw [h']; simp only [Function.update_self]; rw [← h']; exact hC.wr y p
          · rw [Function.update_of_ne h']; exact hC.wr y p
        · rw [hmem]; by_cases h' : y = x
          · subst h'; simp
          · rw [Function.update_of_ne (by simp [h'])]; simp [h', hC.wr y p]
        · simp only [hmemq (.inl (y, p)) (by simp)]; exact hC.wr y p
      · rw [hlocp p hp]
        rw [hmem]
        by_cases h' : (Sum.inl (y, p) : Obj) = i
        · subst h'
          rcases act_access hact with ⟨x, hx, -⟩ | ⟨x, pr', rest, hx, -, -, -, rfl, -⟩ |
            ⟨x, v, hx, -, -, -, rfl, -⟩ | ⟨x, v, hx, -⟩ | ⟨x, v, hx, -⟩
          · cases hx
          · simp only [Function.update_self]; exact hC.wr y p
          · simp only [Function.update_self]; exact hC.wr y p
          · simp only [Sum.inl.injEq, Prod.mk.injEq] at hx; exact absurd hx.2 hp
          · cases hx
        · rw [Function.update_of_ne h']; exact hC.wr y p
    · -- known pairs
      by_cases hp : p = q
      · subst hp
        rw [hloc, Function.update_self] at h
        rcases act_access hact with ⟨x, rfl, -, -, rfl, rfl⟩ | ⟨x, pr', rest, rfl, -, -, -, rfl, rfl⟩ |
          ⟨x, v, rfl, -, -, -, rfl, rfl⟩ | ⟨x, v, rfl, -, -, -, rfl, rfl⟩ |
          ⟨x, v, rfl, -, -, rfl, rfl⟩
        · simp only [List.mem_append] at h
          rcases h with h | h
          · exact mono _ (hC.known _ _ h)
          · exact mono _ (hC.board x _ (by simpa using h))
        · simp only at h
          split_ifs at h with hv
          · exact mono _ (hC.known _ _ h)
          · rcases List.mem_cons.1 h with rfl | h
            · rw [hmem]; simpa using hv
            · exact mono _ (hC.known _ _ h)
        · exact mono _ (hC.known _ _ h)
        · rcases List.mem_cons.1 h with rfl | h
          · rw [hmem]; simp
          · exact mono _ (hC.known _ _ h)
        · exact mono _ (hC.known _ _ h)
      · rw [hlocp p hp] at h; exact mono _ (hC.known _ _ h)
    · -- boards
      by_cases hx : (Sum.inr x : Obj) = i
      · subst hx
        rcases act_access hact with ⟨x', hx', -, -, rfl, -⟩ | ⟨x', pr', rest, hx', -⟩ |
          ⟨x', v, hx', -⟩ | ⟨x', v, hx', -⟩ | ⟨x', v, hx', -, -, rfl, -⟩
        · rw [hmem] at h; simp only [Function.update_self] at h
          exact mono _ (hC.board _ _ h)
        · cases hx'
        · cases hx'
        · cases hx'
        · rw [hmem] at h; simp only [Function.update_self] at h
          exact mono _ (hC.known _ _ h)
      · rw [hmemq _ hx] at h; exact mono _ (hC.board _ _ h)
    · -- todo lists
      by_cases hp : p = q
      · subst hp
        rw [hloc, Function.update_self] at h ⊢
        rcases act_access hact with ⟨x, rfl, -, hcur, rfl, rfl⟩ |
          ⟨x, pr', rest, rfl, hcur, -, htodo, rfl, rfl⟩ |
          ⟨x, v, rfl, hcur, -, -, rfl, rfl⟩ | ⟨x, v, rfl, hcur, -, -, rfl, rfl⟩ |
          ⟨x, v, rfl, hcur, -, rfl, rfl⟩
        · simp only [List.mem_append] at h
          rcases h with h | h
          · exact Or.inr (mono _ (hC.board x _ (by simpa using h)))
          · left; simp only [scanList, List.mem_map] at h
            obtain ⟨q', -, rfl⟩ := h; simpa using hcur
        · simp only at h ⊢
          rcases hC.todo p pr (by rw [htodo]; exact List.mem_cons_of_mem _ h) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (mono _ h')
        all_goals
          rcases hC.todo p pr h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (mono _ h')
      · rw [hlocp p hp] at h ⊢
        rcases hC.todo p pr h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (mono _ h')

lemma inv_run {α : List (Lbl (Fin 3) (Fin 2) ℕ)} {C : Config (tmSpec (Fin 2) ℕ) Bk (Fin 3) LS}
    (h : chainTM.run α = some C) : Inv C :=
  Impl.invariant_of_run inv_init (fun _ _ _ hC hs => inv_step hC hs) h

/-! ### `chainTM` is WDAP -/

lemma trivial_read (i : Obj) : Trivial (B := Bk) (i := i) RWOp.read := fun _ => rfl

lemma not_trivial_write (i : Obj) (v : List Pair) (hv : v ≠ []) :
    ¬ Trivial (B := Bk) (i := i) (RWOp.write v) := fun h => hv (h [])

/-- A pending operation on `x` puts `x` into the data set of the current transaction. -/
lemma mem_dSet {α : List (Lbl (Fin 3) (Fin 2) ℕ)} {C : Config (tmSpec (Fin 2) ℕ) Bk (Fin 3) LS}
    (h : chainTM.run α = some C) {p : Fin 3} {op : TOp (Fin 2) ℕ} {x : Fin 2}
    (hc : (C.loc p).cur = some op) (hx : op.obj = some x) : x ∈ DSet α (cur α p) := by
  right
  refine ⟨op, ?_, hx⟩
  rw [txRec_cur, ← pend_eq_pstate chainTM h, (inv_run h).pend, hc]

lemma act_inr {p : Fin 3} {l : LS} {x : Fin 2} {o : (Bk (.inr x)).Op}
    {k : (Bk (.inr x)).Resp → LS} (h : act p l = .access (.inr x) o k) :
    ∃ op, l.cur = some op ∧ op.obj = some x := by
  rcases act_access h with ⟨x', hx, -, hc, -⟩ | ⟨x', pr, rest, hx, -⟩ | ⟨x', v, hx, -⟩ |
    ⟨x', v, hx, -⟩ | ⟨x', v, hx, hc, -⟩
  · cases hx; exact ⟨_, hc, rfl⟩
  · cases hx
  · cases hx
  · cases hx
  · cases hx; exact ⟨_, hc, rfl⟩

lemma act_inl {p : Fin 3} {l : LS} {pr : Pair} {o : (Bk (.inl pr)).Op}
    {k : (Bk (.inl pr)).Resp → LS} (h : act p l = .access (.inl pr) o k) :
    (o = .read ∧ ((∃ x rest, l.cur = some (.read x) ∧ l.todo = pr :: rest) ∨ pr.2 = p)) ∨
      (o = .write [pr] ∧ pr.2 = p ∧ (∃ v, l.cur = some (.write pr.1 v)) ∧ pr.1 ∉ l.wr) := by
  rcases act_access h with ⟨x', hx, -⟩ | ⟨x, pr', rest, hx, hc, -, ht, ho, -⟩ |
    ⟨x, v, hx, -, -, -, ho, -⟩ | ⟨x, v, hx, hc, -, hw, ho, -⟩ | ⟨x', v, hx, -⟩
  · cases hx
  · cases hx; exact Or.inl ⟨ho, Or.inl ⟨x, rest, hc, ht⟩⟩
  · cases hx; exact Or.inl ⟨ho, Or.inr rfl⟩
  · cases hx; exact Or.inr ⟨ho, rfl, ⟨v, hc⟩, hw⟩
  · cases hx

/-- One side writes `o(pr)` for the first time, the other reads it: they share an object. -/
lemma share_of_write_read {α : List (Lbl (Fin 3) (Fin 2) ℕ)}
    {C : Config (tmSpec (Fin 2) ℕ) Bk (Fin 3) LS} (hC : chainTM.run α = some C) {a b : Fin 3}
    (hab : a ≠ b) {pr : Pair} (hw : pr.2 = a ∧ (∃ v, (C.loc a).cur = some (.write pr.1 v)) ∧
      pr.1 ∉ (C.loc a).wr)
    (hr : (∃ x rest, (C.loc b).cur = some (.read x) ∧ (C.loc b).todo = pr :: rest) ∨ pr.2 = b) :
    (DSet α (cur α a) ∩ DSet α (cur α b)).Nonempty := by
  have hI := inv_run hC
  obtain ⟨h2, ⟨v, hca⟩, hwr⟩ := hw
  rcases hr with ⟨x, rest, hcb, htb⟩ | h2'
  · rcases hI.todo b pr (by rw [htb]; exact List.mem_cons_self) with h | h
    · rw [hcb] at h; cases h
      exact ⟨pr.1, mem_dSet hC hca rfl, mem_dSet hC hcb rfl⟩
    · obtain ⟨y, q⟩ := pr; simp only at h2; subst h2
      exact absurd ((hI.wr y q).2 h) hwr
  · exact absurd (h2.symm.trans h2') hab

/-- **`chainTM` is WDAP** (in the strong form: contending transactions share an object). -/
theorem chainTM_strongWDAP : StrongWDAP chainTM := by
  intro α C hC a b hab ha hb i o o' k k' h1 h2 hnt
  rcases i with pr | x
  · rcases act_inl h1 with ⟨rfl, hra⟩ | ⟨rfl, hwa⟩ <;> rcases act_inl h2 with ⟨rfl, hrb⟩ | ⟨rfl, hwb⟩
    · exact absurd hnt (by simp [trivial_read])
    · rw [Set.inter_comm]; exact share_of_write_read hC (Ne.symm hab) hwb hra
    · exact share_of_write_read hC hab hwa hrb
    · exact absurd (hwa.1.symm.trans hwb.1) hab
  · obtain ⟨op, hca, hxa⟩ := act_inr h1
    obtain ⟨op', hcb, hxb⟩ := act_inr h2
    exact ⟨x, mem_dSet hC hca hxa, mem_dSet hC hcb hxb⟩

/-! ### The counterexample execution -/

/-- `Tᵢ = W(x₀)` by process `0` (left live), `T_k1 = R(x₀) c` and `T_k2 = W(x₁) c` by process `1`,
`Tⱼ = R(x₁)` by process `2` (left live, after three steps). -/
def exec : List (Lbl (Fin 3) (Fin 2) ℕ) :=
  [.inv 0 (.write 0 5), .tau 0, .tau 0, .ret 0 (some 5),
   .inv 1 (.read 0), .tau 1, .tau 1, .tau 1, .tau 1, .tau 1, .ret 1 (some 0),
   .inv 1 .tryC, .ret 1 (some 0),
   .inv 1 (.write 1 7), .tau 1, .tau 1, .ret 1 (some 7), .inv 1 .tryC, .ret 1 (some 0),
   .inv 2 (.read 1), .tau 2, .tau 2, .tau 2]

/-- Summary of an action (without the continuation), for computation. -/
def accSum : Action (tmSpec (Fin 2) ℕ) Bk LS → Option (Obj × RWOp (List Pair))
  | .access i o _ => some (i, o)
  | .ret _ _ => none

lemma eq_access_of_accSum {a : Action (tmSpec (Fin 2) ℕ) Bk LS} {i : Obj} {o : RWOp (List Pair)}
    (h : accSum a = some (i, o)) : ∃ k, a = .access i o k := by
  cases a with
  | access i' o' k => simp only [accSum, Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h; exact ⟨k, rfl⟩
  | ret r l => simp [accSum] at h

lemma stepOn_of {α₁ α₂ : List (Lbl (Fin 3) (Fin 2) ℕ)} {T : TxId (Fin 3)} {i : Obj}
    {o : RWOp (List Pair)}
    (h : (chainTM.crun α₁).map (fun C => accSum (chainTM.act T.1 (C.loc T.1))) = some (some (i, o)))
    (hcur : cur α₁ T.1 = T) : StepOn chainTM (α₁ ++ .tau T.1 :: α₂) T i o := by
  cases hr : chainTM.crun α₁ with
  | none => simp [hr] at h
  | some C =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    obtain ⟨k, hk⟩ := eq_access_of_accSum h
    exact ⟨α₁, α₂, C, k, rfl, (chainTM.run_eq_crun α₁).trans hr, hcur, hk⟩

/-- The records of the transactions of `exec`. -/
lemma txRec_exec (p : Fin 3) (k : ℕ) :
    txRec exec (p, k) =
      if k = 0 ∧ p = 0 then ⟨[(.write 0 5, some 5)], none⟩
      else if k = 0 ∧ p = 1 then ⟨[(.read 0, some 0), (.tryC, some 0)], none⟩
      else if k = 1 ∧ p = 1 then ⟨[(.write 1 7, some 7), (.tryC, some 0)], none⟩
      else if k = 0 ∧ p = 2 then ⟨[], some (.read 1)⟩
      else TxRec.empty := by
  rcases k with _ | _ | _ | k
  · fin_cases p <;> decide
  · fin_cases p <;> decide
  · fin_cases p <;> decide
  · have hl : ((pstate exec p).done ++ [(pstate exec p).cur]).length ≤ k + 3 := by
      have : ((pstate exec p).done ++ [(pstate exec p).cur]).length ≤ 3 := by
        fin_cases p <;> decide
      omega
    simp only [txRec, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none hl]; simp

/-- **Lemma 1 is false.** `chainTM` is WDAP, and in its execution `exec` the transactions
`Tᵢ = (0,0)` and `Tⱼ = (2,0)` are concurrent (both live) and disjoint-access, yet `Tⱼ` reads the
base object `o(x₀, 0)` to which `Tᵢ` applied a non-trivial primitive. -/
theorem lemma_1_false : StrongWDAP chainTM ∧ WDAP chainTM ∧ ¬ Lemma1Claim chainTM := by
  refine ⟨chainTM_strongWDAP, chainTM_strongWDAP.wdap, fun H => ?_⟩
  have hvalid : chainTM.Valid exec := Impl.valid_of_crun _ (by decide)
  have hlive0 : Live exec ((0 : Fin 3), 0) := by decide
  have hlive2 : Live exec ((2 : Fin 3), 0) := by decide
  -- `Tᵢ` and `Tⱼ` are disjoint-access: sides `{T_k2, Tⱼ}` (object `x₁`) and the others (`x₀`)
  have hnc : ¬ Connected exec ((0 : Fin 3), 0) ((2 : Fin 3), 0) := by
    intro hc
    have := connected_sideT (fun T => decide (T = (1, 1) ∨ T = (2, 0)))
      (fun s => if s then {1} else {0}) (by simp) ?_ hc
    · simp at this
    · rintro ⟨p, k⟩ x hx
      simp only [DSet, txRec_exec] at hx
      split_ifs at hx with h1 h2 h3 h4 <;>
        simp_all [TOp.obj, TxRec.empty]
  have hstep0 : StepOn chainTM exec ((0 : Fin 3), 0) (.inl (0, 0)) (.write [(0, 0)]) := by
    rw [show exec = [.inv 0 (.write 0 5)] ++ .tau ((0 : Fin 3), (0 : ℕ)).1 :: exec.drop 2 from rfl]
    exact stepOn_of (by decide) (by decide)
  have hstep2 : StepOn chainTM exec ((2 : Fin 3), 0) (.inl (0, 0)) .read := by
    rw [show exec = exec.take 22 ++ [.tau ((2 : Fin 3), (0 : ℕ)).1] from rfl]
    exact stepOn_of (by decide) (by decide)
  exact not_trivial_write _ [(0, 0)] (by simp)
    (H exec _ _ hvalid (by decide) hlive0 hlive2 hnc _ _ _ hstep0 hstep2).1

end Lemma1

end Podc.DAPInvisibleReads
