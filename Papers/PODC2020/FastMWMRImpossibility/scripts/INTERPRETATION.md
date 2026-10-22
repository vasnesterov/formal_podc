# W2R1 model checker: how the pseudo-code is read (Algorithms 1 & 2, arXiv 2001.07855)

The model is the asynchronous client–server message-passing model. A request is delivered at any
time, or never; that covers crashes and arbitrary delays. A server handles each request
atomically and replies immediately. A client goes on once it has S−t replies of its *current*
round, and it may choose any S−t of the replies that have arrived. Replies to an old round are
ignored. Values are pairs (ts, wid), ordered lexicographically. The initial value is (0,⊥),
encoded as (0,0), and writers have ids 1..W.

## Choices that apply to every variant
- **Server state.** The `valuevector` maps each value to its `updated` set (a set of client ids).
  `val_i` is the largest key. Entries are never deleted.
- **`update(val,c)`.** If val > val_i, add the entry val:{c}, which makes val the new val_i.
  Otherwise add c to `updated[val]`, creating the entry if it is missing.
- **READACK.** It carries a snapshot of the whole `valuevector`.
  - "m has v" means v ∈ keys(m).
  - `m.updated`, for v, means m[v].
  - This reading is forced by the proof of Lemma 3: every READACK "has" maxV_old.
- **Reader, lines 21–31.**
  - maxV is the largest value over all messages.
  - `admissible(v,Msg,a)` holds iff some subset μ of the messages that contain v has |μ| ≥ S−a·t
    and |∩_{m∈μ} m[v]| ≥ a, for some a ∈ [1, R+1].
  - "Remove maxV from all msg" deletes that key from every message. The reader then repeats
    with the next largest value. (0,⊥) always ends the loop.
- **valQueue (line 22, `vq`).**
  - `all` (literal): add every value seen in rcvMsg. This is the default.
  - `ret`: add only the returned value.
  - `max`: add only maxV.
- **Writer's first round `(read, maxTS)` (`wq`).**
  - `A` (default): the request does not change server state, and the reply is ts(val_i).
  - `B`: the request is handled like a read with an empty valQueue, so the writer gets marked.
  - The writer then writes (maxTS+1, wid).

## Ambiguous: which values the server marks a reader on (`srv`)
- **`L` (literal).** The reader is marked only on values in its own valQueue.
- **`D`.** Same as `L`, and the reader is also marked on the server's current val_i. This is the
  direct analogue of the single-writer DGLV algorithm (SIAM J. Comput. 2010), where the server
  adds the reader to `updated` of its current timestamp.
- **`D2`.** Same as `L`, and the reader is also marked on *every* value in the `valuevector`
  ("the reader has now seen all of them").
- **Suffix `c`, for example `D2c`.** Adds DGLV-style read counters: a server ignores a read
  request that is older than the last one it processed from the same reader. The paper's
  pseudo-code has no counters.

## Other ambiguities noted
- What "m has v" means when a server holds several values. We take "the key is present".
- Lemma 8's `m.v.updated` notation fits the per-value `updated` set we use.
- Algorithm 2 writes "update" in some places and "updated" in others. We take them as the same field.
- Algorithm 1, line 8: we take maxTS to be the largest ts over the READACKs.
- The writer's local `ts ← 0` and `maxTS` variables only matter for reading B.

## Scripts (run everything under `ulimit -v` and `timeout`)
- `w2r1.py`: the model.
  - `Sys` holds the state and history.
  - `linearizable`: a brute-force atomic-register check with memoisation.
  - `lemma_checks`: checks Lemmas 2, 6, 8, Corollary 1, MWA2 and MWA4.
  - `dfs`: exhaustive search, with memoisation up to server permutation and up to irrelevant
    history interleavings. Writer query rounds are abstracted exactly, because a query has no
    side effect: the writer can see any ts that a server held during the round.
  - `random_run`, `random_run2`, `random_run3`: random schedulers.
- `dfs.py S t R wops rops srv wq vq [max_states] [time_s] [late_bound]`: exhaustive search.
- `rand.py`, `rand2.py`, `rand3.py`: random testing.
- `lemmas.py`: random testing, counting how often each lemma fails.
- `scenario_late.py [D2|D|L|D2c]`: replays the hand-built counterexample against D2.
- `out/`: logs.
