// Explicit-state checker for Algorithm 2 (CAS-based) of Aghazadeh et al. PODC'19.
// Every register loop may visit registers in ANY order (over-approximates anonymity).
// Register-symmetry reduction. Checks mutual exclusion + deadlock-freedom (fair SCC).
// usage: alg2 n m [maxstates]
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128;
int n, m;

enum { R = 0, S_, W, H_, HW, C, D_ };
struct Loc { int pc = R; int x = 0; int rem = 0; int unl = 0; };
struct St { int mem[8]; Loc l[5]; };
u128 pack(const St& s) {
  u128 k = 0;
  for (int x = 0; x < m; x++) k = (k << 3) | s.mem[x];
  for (int i = 0; i < n; i++) {
    const Loc& L = s.l[i];
    unsigned w = L.pc | (L.x << 3) | (L.rem << 6) | (L.unl << 14);
    k = (k << 15) | w;
  }
  return k;
}
St unpack(u128 k) {
  St s;
  for (int i = n - 1; i >= 0; i--) {
    unsigned w = (unsigned)(k & 0x7fff); k >>= 15;
    Loc& L = s.l[i];
    L.pc = w & 7; L.x = (w >> 3) & 7; L.rem = (w >> 6) & 255; L.unl = (w >> 14) & 1;
  }
  for (int x = m - 1; x >= 0; x--) { s.mem[x] = (int)(k & 7); k >>= 3; }
  return s;
}
St canonR(const St& s) {
  vector<pair<long long, int>> sig(m);
  for (int x = 0; x < m; x++) {
    long long v = s.mem[x];
    for (int i = 0; i < n; i++) {
      const Loc& L = s.l[i];
      int r = 0;
      if ((L.pc == W || L.pc == HW) && L.x == x) r = 1;
      if ((L.pc == H_ || L.pc == HW) && ((L.rem >> x) & 1)) r |= 2;
      v = v * 4 + r;
    }
    sig[x] = {v, x};
  }
  sort(sig.begin(), sig.end());
  int ni[8];
  for (int k = 0; k < m; k++) ni[sig[k].second] = k;
  St t = s;
  for (int k = 0; k < m; k++) t.mem[k] = s.mem[sig[k].second];
  for (int i = 0; i < n; i++) {
    Loc& L = t.l[i];
    if (L.pc == W || L.pc == HW) L.x = ni[s.l[i].x]; else L.x = 0;
    int r = 0; for (int x = 0; x < m; x++) if ((s.l[i].rem >> x) & 1) r |= 1 << ni[x];
    if (L.pc == H_ || L.pc == HW) L.rem = r; else L.rem = 0;
  }
  return t;
}
St canon(const St& s0) {
  int pr[5]; for (int i = 0; i < n; i++) pr[i] = i;
  bool first = true; u128 best = 0; St bs;
  do {
    St t = s0;
    // process pr[i] of new = old i : new id of old process i+1 is pr[i]+1
    for (int i = 0; i < n; i++) t.l[pr[i]] = s0.l[i];
    for (int x = 0; x < m; x++) t.mem[x] = s0.mem[x] ? pr[s0.mem[x] - 1] + 1 : 0;
    St c = canonR(t); u128 k = pack(c);
    if (first || k < best) { best = k; bs = c; first = false; }
  } while (std::next_permutation(pr, pr + n));
  return bs;
}
struct Edge { St t; int proc; bool compl_; };
int FULL; bool noCanon = false;
void succ(const St& s, vector<Edge>& out) {
  out.clear();
  for (int i = 0; i < n; i++) {
    int p = i + 1;
    const Loc& L = s.l[i];
    auto mk = [&](Loc nl, const int* nm, bool c) {
      St t = s; t.l[i] = nl; if (nm) for (int x = 0; x < m; x++) t.mem[x] = nm[x];
      out.push_back({noCanon ? t : canon(t), i, c});
    };
    Loc nl;
    switch (L.pc) {
      case R: nl.pc = S_; mk(nl, nullptr, false); break;
      case S_: {
        int owned = 0, bots = 0; set<int> ids;
        for (int x = 0; x < m; x++) { if (s.mem[x] == p) owned++; if (s.mem[x] == 0) bots++; ids.insert(s.mem[x]); }
        if (!(owned > 0 || bots == m)) { nl.pc = S_; mk(nl, nullptr, false); break; }
        if (bots > 0) { for (int x = 0; x < m; x++) if (s.mem[x] == 0) { nl = Loc(); nl.pc = W; nl.x = x; mk(nl, nullptr, false); } break; }
        if (owned == m) { nl.pc = C; mk(nl, nullptr, true); break; }
        int cnt = ids.size();
        if (owned * cnt < m) { int r = 0; for (int x = 0; x < m; x++) if (s.mem[x] == p) r |= 1 << x; nl.pc = H_; nl.rem = r; nl.unl = 0; mk(nl, nullptr, false); }
        else { nl.pc = S_; mk(nl, nullptr, false); }
        break; }
      case W: { int nm[8]; memcpy(nm, s.mem, sizeof nm); nm[L.x] = p; nl.pc = S_; mk(nl, nm, false); break; }
      case H_:
        if (!L.rem) { nl = Loc(); if (L.unl) { nl.pc = R; mk(nl, nullptr, true); } else { nl.pc = S_; mk(nl, nullptr, false); } break; }
        for (int x = 0; x < m; x++) if ((L.rem >> x) & 1) {
          nl = L; nl.rem = L.rem & ~(1 << x);
          if (s.mem[x] == p) { nl.pc = HW; nl.x = x; } else { nl.pc = H_; }
          mk(nl, nullptr, false);
        }
        break;
      case HW: { int nm[8]; memcpy(nm, s.mem, sizeof nm); nm[L.x] = 0; nl = L; nl.pc = H_; nl.x = 0; mk(nl, nm, false); break; }
      case C: nl.pc = H_; nl.rem = FULL; nl.unl = 1; mk(nl, nullptr, false); break;
    }
  }
}
void print(const St& s) {
  printf("mem=");
  for (int x = 0; x < m; x++) printf("%d", s.mem[x]);
  const char* nm[] = {"R", "S", "W", "H", "HW", "C", "D"};
  for (int i = 0; i < n; i++) { const Loc& L = s.l[i]; printf(" | p%d %s x=%d rem=%x unl=%d", i + 1, nm[L.pc], L.x, L.rem, L.unl); }
  printf("\n");
}
struct H { size_t operator()(const u128& k) const { return std::hash<unsigned long long>()((unsigned long long)k ^ (unsigned long long)(k >> 64) * 0x9e3779b97f4a7c15ULL); } };
int main(int argc, char** argv) {
  n = atoi(argv[1]); m = atoi(argv[2]);
  size_t maxst = argc > 3 ? atoll(argv[3]) : 30000000;
  FULL = (1 << m) - 1;
  unordered_map<u128, uint32_t, H> idx;
  vector<u128> states; vector<uint32_t> parent;
  St init; for (int x = 0; x < m; x++) init.mem[x] = 0;
  u128 k0 = pack(canon(init));
  idx[k0] = 0; states.push_back(k0); parent.push_back(UINT32_MAX);
  vector<Edge> out;
  auto trace = [&](uint32_t v) {
    vector<uint32_t> tr; while (v != UINT32_MAX) { tr.push_back(v); v = parent[v]; }
    for (int i = tr.size() - 1; i >= 0; i--) print(unpack(states[tr[i]]));
  };
  for (size_t q = 0; q < states.size(); q++) {
    St s = unpack(states[q]);
    int incs = 0; for (int i = 0; i < n; i++) incs += s.l[i].pc == C;
    if (incs >= 2) { printf("MUTEX VIOLATION\n"); trace(q); return 0; }
    succ(s, out);
    for (auto& e : out) {
      u128 k = pack(e.t);
      if (!idx.count(k)) { idx[k] = states.size(); states.push_back(k); parent.push_back(q); }
    }
    if (states.size() > maxst) { printf("too many states\n"); return 0; }
  }
  size_t N = states.size();
  printf("states %zu\n", N);
  // iterative Tarjan over non-completion edges
  vector<int> index(N, -1), low(N, 0), comp(N, -1); vector<char> onst(N, 0); vector<uint32_t> stk;
  int counter = 0, ncomp = 0;
  struct Fr { uint32_t v; vector<uint32_t> succs; size_t ei; };
  auto succIds = [&](uint32_t v) {
    vector<uint32_t> r; succ(unpack(states[v]), out);
    for (auto& e : out) if (!e.compl_) r.push_back(idx[pack(e.t)]);
    return r;
  };
  for (uint32_t root = 0; root < N; root++) {
    if (index[root] != -1) continue;
    vector<Fr> work; index[root] = low[root] = counter++; stk.push_back(root); onst[root] = 1;
    work.push_back({root, succIds(root), 0});
    while (!work.empty()) {
      Fr& f = work.back(); bool adv = false;
      while (f.ei < f.succs.size()) {
        uint32_t w = f.succs[f.ei++];
        if (index[w] == -1) {
          index[w] = low[w] = counter++; stk.push_back(w); onst[w] = 1;
          work.push_back({w, succIds(w), 0}); adv = true; break;
        } else if (onst[w]) low[f.v] = min(low[f.v], index[w]);
      }
      if (adv) continue;
      uint32_t v = f.v; work.pop_back();
      if (!work.empty()) { uint32_t u = work.back().v; low[u] = min(low[u], low[v]); }
      if (low[v] == index[v]) {
        while (true) { uint32_t w = stk.back(); stk.pop_back(); onst[w] = 0; comp[w] = ncomp; if (w == v) break; }
        ncomp++;
      }
    }
  }
  vector<int> stepped(ncomp, 0); vector<int> rep(ncomp, -1);
  for (uint32_t v = 0; v < N; v++) {
    succ(unpack(states[v]), out);
    for (auto& e : out) if (!e.compl_) { uint32_t w = idx[pack(e.t)]; if (comp[w] == comp[v]) { stepped[comp[v]] |= 1 << e.proc; if (rep[comp[v]] < 0) rep[comp[v]] = v; } }
  }
  int bad = 0;
  for (int c = 0; c < ncomp; c++) {
    if (rep[c] < 0) continue;
    St s = unpack(states[rep[c]]);
    bool incs = false; int pend = 0;
    for (int i = 0; i < n; i++) { if (s.l[i].pc == C) incs = true; if (s.l[i].pc != R && s.l[i].pc != C) pend |= 1 << i; }
    if (incs || !pend) continue;
    if ((pend & ~stepped[c]) == 0) {
      bad++;
      if (bad <= 2) { printf("DEADLOCK SCC (stepping %x):\n", stepped[c]); trace(rep[c]); }
    }
  }
  printf("fair deadlock SCCs (unsound under proc symmetry): %d\n", bad);
  int emptyCyc = 0;
  for (uint32_t v = 0; v < N; v++) {
    if (rep[comp[v]] < 0) continue;  // trivial SCC
    St s = unpack(states[v]); bool empty = true; for (int x = 0; x < m; x++) if (s.mem[x]) empty = false;
    if (empty) { emptyCyc++; if (emptyCyc <= 3) { printf("EMPTY-MEMORY STATE ON CYCLE:\n"); print(s); } }
  }
  printf("empty-memory states on cycles: %d\n", emptyCyc);
  // find all-S empty state
  St allS; for (int x = 0; x < m; x++) allS.mem[x] = 0; for (int i = 0; i < n; i++) { allS.l[i] = Loc(); allS.l[i].pc = S_; }
  u128 kS = pack(canon(allS));
  if (!idx.count(kS)) { printf("allS not reachable\n"); return 0; }
  uint32_t v0 = idx[kS];
  if (rep[comp[v0]] < 0) { printf("allS not on cycle\n"); return 0; }
  // BFS within SCC from v0 back to v0
  unordered_map<uint32_t, uint32_t> par; deque<uint32_t> dq; dq.push_back(v0); par[v0] = UINT32_MAX;
  uint32_t last = UINT32_MAX;
  while (!dq.empty() && last == UINT32_MAX) {
    uint32_t v = dq.front(); dq.pop_front();
    succ(unpack(states[v]), out);
    for (auto& e : out) { if (e.compl_) continue; uint32_t w = idx[pack(e.t)]; if (comp[w] != comp[v0]) continue;
      if (w == v0) { last = v; break; }
      if (!par.count(w)) { par[w] = v; dq.push_back(w); } }
  }
  vector<uint32_t> cyc; for (uint32_t v = last; v != UINT32_MAX; v = par[v]) cyc.push_back(v);
  reverse(cyc.begin(), cyc.end()); cyc.push_back(v0);
  printf("quotient cycle length %zu\n", cyc.size() - 1);
  // lift
  noCanon = true; St a = allS;
  const char* nm[] = {"R", "S", "W", "H", "HW", "C", "D"};
  for (size_t j = 0; j + 1 < cyc.size(); j++) {
    succ(a, out); bool found = false;
    for (auto& e : out) { if (e.compl_) continue; if (pack(canon(e.t)) == states[cyc[j + 1]]) {
        printf("step p%d (%s x=%d) -> ", e.proc + 1, nm[a.l[e.proc].pc], a.l[e.proc].x); a = e.t; print(a); found = true; break; } }
    if (!found) { printf("lift failed\n"); return 0; }
  }
}
