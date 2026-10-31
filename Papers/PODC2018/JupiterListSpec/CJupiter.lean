import Papers.PODC2018.JupiterListSpec.System

/-!
# The CJupiter protocol (Section 3, Appendix B)

* An operation (`COp`, Algorithm B.1) carries its context `ctx` and its server context `sctx`
  (the operations the server had executed before it, as far as the operation knows).
* `cmp r op op'` is `Compare(op, op', r)` of Algorithm B.1 (`true` = `LT`, i.e. `op ≺s op'`);
  `r = none` is the server.
* An n-ary ordered state space (`CSS`, Algorithm B.4) is represented by its edges (every edge is
  labelled by an operation whose context is the source vertex) and its current vertex.
  `firstEdge r E u` is the first edge from `u` according to `Compare` (the edge that compares `LT`
  with every other edge from `u`).
* `cLoop` / `cxForm` are `xForm(op)` of Algorithm B.4: from the vertex matching `op.ctx`,
  transform `op` along the first edges until the current vertex is reached, linking `op` from
  every visited vertex and the transformed edge from every new vertex (Figure 3).
* Client (Algorithm B.5): local processing links the new operation (with `sctx = ∅`) from the
  current vertex; remote processing calls `xForm`. Server (Algorithm B.6): sets `sctx := soids`,
  adds the operation to `soids`, calls `xForm`, and forwards the *original* operation.
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

/-- An operation of CJupiter (Algorithm B.1). -/
structure COp (n : ℕ) where
  o : LOp (Oid n)
  oid : Oid n
  ctx : Finset (Oid n)
  sctx : Finset (Oid n)
  deriving DecidableEq

/-- `op⟨op'⟩` (Algorithm B.1, procedure `OT`). -/
def COp.xf (op op' : COp n) : COp n :=
  ⟨JupiterListSpec.xf op.o op'.o, op.oid, insert op'.oid op.ctx, op.sctx⟩

/-- `Compare(op, op', r)` (Algorithm B.1): `true` means `LT` (`op ≺s op'`). -/
def cmp (r : Option (Fin n)) (op op' : COp n) : Bool :=
  if op.oid ∈ op'.sctx then true
  else if op'.oid ∈ op.sctx then false
  else if r ≠ some op.oid.1 then true
  else false

/-- An n-ary ordered state space: its edges and its current vertex. -/
structure CSS (n : ℕ) where
  edges : List (COp n)
  cur : Finset (Oid n)

/-- The first edge from `u` according to `Compare` at replica `r` (Algorithm B.2). -/
def firstEdge (r : Option (Fin n)) (E : List (COp n)) (u : Finset (Oid n)) : Option (COp n) :=
  let Eu := E.filter fun e => decide (e.ctx = u)
  Eu.find? fun e => Eu.all fun e' => e'.oid == e.oid || cmp r e e'

/-- The loop of `xForm(op)` (Algorithm B.4, lines 7–19); `op.ctx` is the vertex `u`. -/
def cLoop (r : Option (Fin n)) (cur : Finset (Oid n)) :
    ℕ → List (COp n) → COp n → Option (List (COp n) × COp n)
  | 0, E, op => if op.ctx = cur then some (op :: E, op) else none
  | f + 1, E, op =>
    if op.ctx = cur then some (op :: E, op) else
    match firstEdge r E op.ctx with
    | none => none
    | some e => cLoop r cur f (op :: e.xf op :: E) (op.xf e)

/-- `xForm(op)` (Algorithm B.4) at replica `r`. -/
def cxForm (r : Option (Fin n)) (S : CSS n) (op : COp n) : Option (CSS n × COp n) :=
  match cLoop r S.cur S.cur.card S.edges op with
  | none => none
  | some (E, op') => some (⟨E, insert op.oid S.cur⟩, op')

/-- CJupiter client state. -/
structure CClient (n : ℕ) where
  list : List (Oid n)
  css : CSS n

/-- CJupiter server state. -/
structure CServer (n : ℕ) where
  list : List (Oid n)
  soids : Finset (Oid n)
  css : CSS n

/-- The CJupiter protocol. -/
@[reducible] def cjupiter (n : ℕ) : Proto n where
  CS := CClient n
  SS := CServer n
  Msg := COp n
  cinit := ⟨[], ⟨[], ∅⟩⟩
  sinit := ⟨[], ∅, ⟨[], ∅⟩⟩
  list s := s.list
  slist s := s.list
  oidOf m := m.oid
  cdo _ x o s :=
    let op : COp n := ⟨o, x, s.css.cur, ∅⟩
    (⟨o.apply s.list, ⟨op :: s.css.edges, insert x s.css.cur⟩⟩, op)
  crecv c m s :=
    match cxForm (some c) s.css m with
    | none => none
    | some (S', op') => some ⟨op'.o.apply s.list, S'⟩
  srecv _ m s :=
    let m' : COp n := { m with sctx := s.soids }
    match cxForm none s.css m' with
    | none => none
    | some (S', op') => some (⟨op'.o.apply s.list, insert m.oid s.soids, S'⟩, m')
  oidOf_cdo _ _ _ _ := rfl
  oidOf_srecv c m s s' m' h := by
    simp only at h
    split at h
    · cases h
    · cases h; rfl

end Podc.JupiterListSpec
