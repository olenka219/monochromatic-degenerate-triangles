"""Verify the Rule B certificate (standard library only).

Rule B: in a two-colouring of the plane with no monochromatic T(1,3,4), the band offsets of a
unit triangular lattice never turn (a step of 4 followed by 5, or 5 followed by 4).

Checks: (1) the reduction: for steps d0, d1 in {4,5}, the two open points above and below a row
have the same colour exactly when d0 != d1; (2) starting only from rows 0, 1, 2 of Lambda with
offsets 0, 4, 1, every deduction applies one of two rules exactly: a forbidden triangle (T(1),
T(3), T(4) or collinear T(1,3,4)) with two equally coloured vertices forces the third, or two
points of q*Lambda four steps apart along its long direction q*w^j have opposite colours;
(3) each case j = 0, 1, 2 ends in a monochromatic forbidden triangle or an equally coloured
four-apart pair.
"""
import json, os, sys
N=lambda a,b:a*a+a*b+b*b
h=lambda x:x%8 in (0,1,2,3)
inL=lambda p:p[0]%7==0 and p[1]%7==0
inQ=lambda p:(8*p[0]+5*p[1])%49==0 and (3*p[1]-5*p[0])%49==0
ALLOWED={(49,49,49),(441,441,441),(784,784,784),(49,441,784)}
tri=lambda t:tuple(sorted(N(t[i][0]-t[j][0],t[i][1]-t[j][1]) for i,j in ((0,1),(0,2),(1,2)))) in ALLOWED
mul=lambda u,v:(u[0]*v[0]-u[1]*v[1],u[0]*v[1]+u[1]*v[0]+u[1]*v[1])
def reduction():
    # middle row b with offset 0; row b+1 offset d1, row b-1 offset -d0.  The point a+(b+1)w lies
    # above the pair a, a+1 of row b; the point (a+1)+(b-1)w lies below the same pair, at the same x.
    for d0 in (4,5):
        for d1 in (4,5):
            res=set()
            for a in range(8):
                if h(a)!=h(a+1):                   # the pair below/above is open exactly here
                    res.add(h(a+d1)==h(a+1-d0))
            assert res=={d0!=d1},(d0,d1,res)
    return True
def main(path):
    c=json.load(open(path)); assert reduction()
    S0={0:0,1:4,2:1}
    def run(steps,col,j):
        u=mul((3,5),[(1,0),(0,1),(-1,1)][j]) if j is not None else None
        def colour(p):
            p=tuple(p)
            if p in col: return col[p]
            if inL(p) and p[1]//7 in S0: return h(p[0]//7+S0[p[1]//7])
            raise AssertionError(f"colour of {p} not yet established")
        for st in steps:
            p=tuple(st["point"]); new=st["colour"]=="R"; us=[tuple(x) for x in st["using"]]
            assert p not in col and not (inL(p) and p[1]//7 in S0), f"{p} already coloured"
            assert all(inL(x) or inQ(x) for x in [p]+us)
            if st["rule"]=="triangle":
                assert tri([p]+us) and colour(us[0])==colour(us[1])==(not new), f"bad triangle step at {p}"
            else:
                assert j is not None and inQ(p) and inQ(us[0])
                d=(p[0]-us[0][0],p[1]-us[0][1]); assert d in ((4*u[0],4*u[1]),(-4*u[0],-4*u[1])), "not four apart"
                assert colour(us[0])==(not new)
            col[p]=new
        return colour
    col={}; run(c["common"],col,None); n_common=len(col)
    for cs in c["cases"]:
        cc=dict(col); colour=run(cs["steps"],cc,cs["j"]); pts=[tuple(x) for x in cs["contradiction"]["points"]]
        if cs["contradiction"]["kind"]=="triangle":
            assert tri(pts) and colour(pts[0])==colour(pts[1])==colour(pts[2]), "no contradiction"
        else:
            u=mul((3,5),[(1,0),(0,1),(-1,1)][cs["j"]]); d=(pts[1][0]-pts[0][0],pts[1][1]-pts[0][1])
            assert d in ((4*u[0],4*u[1]),(-4*u[0],-4*u[1])) and colour(pts[0])==colour(pts[1])
        print(f"   case {cs['long_direction']:6s}: {len(cs['steps'])} deductions, ends in a {cs['contradiction']['kind']} contradiction")
    print(f"OK {os.path.basename(path)}: reduction checked; {n_common} common deductions in Lambda; all three cases close")
if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else os.path.join(os.path.dirname(os.path.abspath(__file__)),"..","certificates","ruleB_cases.json"))
