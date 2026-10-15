// Explicit-state checker for Algorithm 2 (CAS-based) of Aghazadeh et al. PODC'19.
// Every register loop may visit registers in ANY order (over-approximates anonymity).
// Register-symmetry reduction. Checks mutual exclusion + deadlock-freedom (fair SCC).
// usage: alg2 n m [maxstates]
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128;
int n, m;
enum { R = 0, L2, L3, L7, L9, C, U };
struct Loc { int pc = R; int rem = 0; int own = 0; int cnt[4] = {0, 0, 0, 0}; int ab = 0; };
struct St { int mem[8]; Loc l[4]; };

// pack: mem: 3 bits each (8 regs) = 24 bits; per process: pc 3, rem 8, own 8, cnt 4x3=12 (ids 1..4), ab 1 => 32 bits
u128 pack(const St& s) {
  u128 k = 0;
  for (int x = 0; x < m; x++) k = (k << 3) | s.mem[x];
  for (int i = 0; i < n; i++) {
    const Loc& L = s.l[i];
    unsigned w = L.pc | (L.rem << 3) | (L.own << 11) | (L.ab << 19);
    for (int j = 0; j < n; j++) w |= (unsigned)L.cnt[j] << (20 + 3 * j);
    k = (k << 32) | w;
  }
  return k;
}
St unpack(u128 k) {
  St s;
  for (int i = n - 1; i >= 0; i--) {
    unsigned w = (unsigned)(k & 0xffffffffu); k >>= 32;
    Loc& L = s.l[i];
    L.pc = w & 7; L.rem = (w >> 3) & 255; L.own = (w >> 11) & 255; L.ab = (w >> 19) & 1;
    for (int j = 0; j < 4; j++) L.cnt[j] = 0;
    for (int j = 0; j < n; j++) L.cnt[j] = (w >> (20 + 3 * j)) & 7;
  }
  for (int x = m - 1; x >= 0; x--) { s.mem[x] = (int)(k & 7); k >>= 3; }
  return s;
}
St canon(const St& s) { return s; }
St canon_unused(const St& s) {
  vector<pair<long long, int>> sig(m);
  for (int x = 0; x < m; x++) {
    long long v = s.mem[x];
    for (int i = 0; i < n; i++) v = v * 4 + (((s.l[i].rem >> x) & 1) | (((s.l[i].own >> x) & 1) << 1));
    sig[x] = {v, x};
  }
  sort(sig.begin(), sig.end());
  int ni[8];
  for (int k = 0; k < m; k++) ni[sig[k].second] = k;
  St t = s;
  for (int k = 0; k < m; k++) t.mem[k] = s.mem[sig[k].second];
  auto rm = [&](int mask) { int r = 0; for (int x = 0; x < m; x++) if ((mask >> x) & 1) r |= 1 << ni[x]; return r; };
  for (int i = 0; i < n; i++) { t.l[i].rem = rm(s.l[i].rem); t.l[i].own = rm(s.l[i].own); }
  return t;
}
struct Edge { St t; int proc; bool compl_; };
int FULL; int perm[4][8];
void succ(const St& s, vector<Edge>& out) {
  out.clear();
  for (int i = 0; i < n; i++) {
    int p = i + 1;
    const Loc& L = s.l[i];
    auto mk = [&](Loc nl, const int* nm, bool c) {
      St t = s; t.l[i] = nl; if (nm) for (int x = 0; x < m; x++) t.mem[x] = nm[x];
      out.push_back({canon(t), i, c});
    };
    Loc nl;
    switch (L.pc) {
      case R: nl.pc = L2; nl.rem = FULL; mk(nl, nullptr, false); break;
      case L2:
        if (!L.rem) { nl.pc = L3; nl.rem = FULL; mk(nl, nullptr, false); break; }
        { int kk = 0; while (!((L.rem >> perm[i][kk]) & 1)) kk++; int x = perm[i][kk];
          int nm[8]; memcpy(nm, s.mem, sizeof nm);
          if (nm[x] == 0) nm[x] = p;
          nl = Loc(); nl.pc = L2; nl.rem = L.rem & ~(1 << x); mk(nl, nm, false);
        }
        break;
      case L3:
        if (!L.rem) {
          int owned = __builtin_popcount(L.own);
          int most = 0; for (int j = 0; j < n; j++) most = max(most, L.cnt[j]);
          if (owned < most) { nl.pc = L7; nl.rem = L.own; mk(nl, nullptr, false); }
          else if (2 * owned > m) { nl.pc = C; mk(nl, nullptr, true); }
          else { nl.pc = L2; nl.rem = FULL; mk(nl, nullptr, false); }
          break;
        }
        { int kk = 0; while (!((L.rem >> perm[i][kk]) & 1)) kk++; int x = perm[i][kk];
          nl = L; nl.rem = L.rem & ~(1 << x);
          int v = s.mem[x];
          if (v) { nl.cnt[v - 1]++; if (v == p) nl.own |= 1 << x; }
          mk(nl, nullptr, false);
        }
        break;
      case L7:
        if (!L.rem) { nl.pc = L9; nl.rem = FULL; nl.ab = 1; mk(nl, nullptr, false); break; }
        { int kk = 0; while (!((L.rem >> perm[i][kk]) & 1)) kk++; int x = perm[i][kk];
          int nm[8]; memcpy(nm, s.mem, sizeof nm); nm[x] = 0;
          nl = Loc(); nl.pc = L7; nl.rem = L.rem & ~(1 << x); mk(nl, nm, false);
        }
        break;
      case L9:
        if (!L.rem) {
          nl = Loc();
          if (L.ab) { nl.pc = L2; nl.rem = FULL; } else { nl.pc = L9; nl.rem = FULL; nl.ab = 1; }
          mk(nl, nullptr, false); break;
        }
        { int kk = 0; while (!((L.rem >> perm[i][kk]) & 1)) kk++; int x = perm[i][kk];
          nl = Loc(); nl.pc = L9; nl.rem = L.rem & ~(1 << x); nl.ab = L.ab && s.mem[x] == 0; mk(nl, nullptr, false);
        }
        break;
      case C: nl.pc = U; nl.rem = FULL; mk(nl, nullptr, false); break;
      case U:
        if (!L.rem) { nl.pc = R; mk(nl, nullptr, true); break; }
        { int kk = 0; while (!((L.rem >> perm[i][kk]) & 1)) kk++; int x = perm[i][kk];
          int nm[8]; memcpy(nm, s.mem, sizeof nm);
          if (nm[x] == p) nm[x] = 0;
          nl = Loc(); nl.pc = U; nl.rem = L.rem & ~(1 << x); mk(nl, nm, false);
        }
        break;
    }
  }
}
void print(const St& s) {
  printf("mem=");
  for (int x = 0; x < m; x++) printf("%d", s.mem[x]);
  const char* nm[] = {"R", "L2", "L3", "L7", "L9", "C", "U"};
  for (int i = 0; i < n; i++) {
    const Loc& L = s.l[i];
    printf(" | p%d %s rem=%x own=%x cnt=", i + 1, nm[L.pc], L.rem, L.own);
    for (int j = 0; j < n; j++) printf("%d", L.cnt[j]);
    printf(" ab=%d", L.ab);
  }
  printf("\n");
}
struct H { size_t operator()(const u128& k) const { return std::hash<unsigned long long>()((unsigned long long)k ^ (unsigned long long)(k >> 64) * 0x9e3779b97f4a7c15ULL); } };
int main(int argc, char** argv) {
  n = atoi(argv[1]); m = atoi(argv[2]);
  size_t maxst = 30000000;
  // perms given as strings argv[3..3+n-1], e.g. 01234
  for (int i = 0; i < n; i++) for (int x = 0; x < m; x++) perm[i][x] = argv[3 + i][x] - '0';
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
  printf("fair deadlock SCCs: %d\n", bad);
}
