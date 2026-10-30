# Monte Carlo of Algorithm 1 (Kesselheim 2012) on a single link (W = 1), all-or-nothing static algorithm A.
import math, random, sys
def run(n, m, phi, trials, seed=1):
    rnd = random.Random(seed)
    chi = 6*(math.log(m)+9)
    I = n
    T = 2*phi*chi*math.log2(n)
    xi = math.ceil(math.log2(I/T))
    fails = 0
    for _ in range(trials):
        R = n
        for i in range(1, xi+1):
            psi = math.ceil(2**(-i+1)*I/chi)
            counts = [0]*psi
            for _p in range(R):
                counts[rnd.randrange(psi)] += 1
            R = sum(c for c in counts if c > chi)
        if R > T: fails += 1
    return xi, fails/trials
for (n, phi) in [(2376,1),(5000,1),(20000,1),(20000,2),(100000,1)]:
    print(n, phi, run(n, 1, phi, int(sys.argv[1])))
