import sys
sys.argv = ["mc.py", "3"]
exec(open("mc.py").read().split('if __name__')[0])
# r=0, x=1, pi=2
s = ((3, 11, 3), (0, 1, 2), (3, 0, 1), (NIL, G(2), NIL), (G(1), A(0), NIL, TOK), (False, False, False), 2)
print("pre I:", checkI(s), "extra:", checkI(s, True))
t = step(s, 2)
print("post:", t, checkI(t))
