# Committee-level simulator of GraphToStar (PODC'20 Michail-Skretas-Spirakis), literal reading.
import random, sys, itertools
def simulate(n, edges, ids, maxph=200, trace=False):
    # committees keyed by leader node; members sets
    members = {v:{v} for v in range(n)}
    mode = {v:'Sel' for v in range(n)}
    tgt = {v:None for v in range(n)}      # leader-leader edge target (for Merge/Pull)
    acted_prev = {v:False for v in range(n)}  # leader activated edge with another leader in prev phase
    comm = {v:v for v in range(n)}
    for ph in range(1, maxph+1):
        alive = list(members)
        def nbrs(c):
            s=set()
            for (a,b) in edges:
                ca,cb=comm[a],comm[b]
                if ca!=cb:
                    if ca==c: s.add(cb)
                    if cb==c: s.add(ca)
            for d in alive:
                if tgt.get(d)==c and d!=c: s.add(d)
            if tgt.get(c) is not None and tgt[c] in members: s.add(tgt[c])
            return s
        N = {c:nbrs(c) for c in alive}
        if len(alive)==1:
            return ('ok', ph, None)
        # selections this phase
        sel = {}
        for c in alive:
            if mode[c]=='Sel':
                cand=[z for z in N[c] if mode[z]!='Pull']
                if any(ids[z]>ids[c] for z in cand):
                    sel[c]=max(cand,key=lambda z:ids[z])
        selected_by = {}
        for c,v in sel.items(): selected_by.setdefault(v,[]).append(c)
        newmode=dict(mode); newtgt=dict(tgt); acted={c:False for c in alive}
        merges=[]
        for c in alive:
            m=mode[c]
            if m=='Sel':
                if not N[c]: newmode[c]='Term'; continue
                if c in sel:
                    v=sel[c]; newtgt[c]=v; acted[c]=True
                    newmode[c] = 'Pull' if v in sel else 'Merge'
                    if trace: print(ph,'sel',ids[c],'->',ids[v],mode[v],newmode[c])
                else:
                    newmode[c]='Wait' if c in selected_by else 'Sel'
            elif m=='Merge':
                merges.append((c,tgt[c]))
            elif m=='Pull':
                v=tgt[c]
                if v not in members: return ('bug-pull-dead',ph,(ids[c],ids[v]))
                if acted_prev[v]:
                    newtgt[c]=tgt[v]; acted[c]=True
                    if trace: print(ph,'pull',ids[c],'->',ids[tgt[v]])
                else:
                    newmode[c]='Merge'
            elif m=='Wait':
                if not N[c]: newmode[c]='Term'; continue
                recv = any(acted_prev[d] and tgt[d]==c for d in alive) or any(t==c for (_,t) in [(x,tgt[x]) for x in alive if mode[x]=='Merge'])
                if not recv: newmode[c]='Sel'
        # apply merges
        dying={c for c,_ in merges}
        for c,v in merges:
            if v in dying or v not in members:
                return ('bug-merge-into-dying',ph,(ids[c],ids[v]))
        for c,v in merges:
            for x in members[c]: comm[x]=v
            members[v]|=members[c]; del members[c]
            if trace: print(ph,'merge',ids[c],'into',ids[v])
        for c in dying:
            newmode.pop(c,None); newtgt.pop(c,None)
        for d in list(newtgt):
            if d in members and newtgt[d] in dying and d not in dying:
                return ('bug-target-died',ph,(ids[d],ids[newtgt[d]],newmode[d]))
        mode={c:newmode[c] for c in members}; tgt={c:newtgt.get(c) for c in members}
        acted_prev={c:acted.get(c,False) for c in members}
        if any(m=='Term' for m in mode.values()) and len(members)>1:
            return ('bug-term-early',ph,None)
    return ('timeout',maxph,None)

