"""Verify the Rule A certificates (standard library only).

Rule A: in a two-colouring of the plane with no monochromatic T(1,3,4), no line of a unit
triangular lattice carries a maximal monochromatic run of exactly three points.

Checks: every point lies in Lambda or q*Lambda, q = (3+5w)/7 (exact arithmetic); the forbidden
triangles T(1), T(3), T(4) and collinear T(1,3,4) are re-derived from coordinates (no other
triangle type is used); for the case form, the two reflections fix the row with its colours and
permute the boundary points as stated, and the cases' orbits cover all boundary colourings
allowed by Theorem 3.13 of the thesis; every proof tree closes using only the rule "two equally
coloured vertices of a forbidden triangle force the third".
"""
import json, sys, itertools, os
N=lambda a,b:a*a+a*b+b*b
inL=lambda p:p[0]%7==0 and p[1]%7==0
inQ=lambda p:(8*p[0]+5*p[1])%49==0 and (3*p[1]-5*p[0])%49==0
conj=lambda p:(p[0]+p[1],-p[1]); sigma=lambda p:(14-p[0]-p[1],p[1])
ALLOWED={(49,49,49),(441,441,441),(784,784,784),(49,441,784)}
tri=lambda t:tuple(sorted(N(t[i][0]-t[j][0],t[i][1]-t[j][1]) for i,j in ((0,1),(0,2),(1,2)))) in ALLOWED
def main(path):
    c=json.load(open(path)); P=[tuple(p) for p in c["points"]]; S=set(P)
    assert all(inL(p) or inQ(p) for p in P), "point outside Lambda and q*Lambda"
    T=[t for t in itertools.combinations(P,3) if tri(t)]
    inc={}
    for t in T:
        for v in t: inc.setdefault(v,[]).append(t)
    def force(col):
        q=list(col)
        while q:
            v=q.pop()
            for t in inc.get(v,()):
                vals=[col.get(u) for u in t]
                if None not in vals:
                    if vals[0]==vals[1]==vals[2]: return True
                elif vals.count(None)==1:
                    k=[x for x in vals if x is not None]
                    if k[0]==k[1]: u=t[vals.index(None)]; col[u]=not k[0]; q.append(u)
        return False
    st={"splits":0,"leaves":0,"depth":0}
    def walk(node,col,d):
        st["depth"]=max(st["depth"],d); col=dict(col); bad=force(col)
        if node=="leaf": assert bad,"a leaf does not close"; st["leaves"]+=1; return
        assert not bad,"contradiction before a recorded split"
        v=tuple(node["split"]); assert v in S and v not in col; st["splits"]+=1
        walk(node["blue"],{**col,v:False},d+1); walk(node["red"],{**col,v:True},d+1)
    rd=lambda L:{tuple(p):(x=="R") for p,x in L}
    if "cases" in c:
        base=rd(c["base_pins"]); a,b,cc,d=[tuple(p) for p in c["boundary"]]
        for g in (conj,sigma): assert all(g(p) in base and base[g(p)]==v for p,v in base.items())
        assert (sigma(a),sigma(b),sigma(cc),sigma(d))==(b,a,d,cc) and (conj(a),conj(b),conj(cc),conj(d))==(cc,d,a,b)
        S_=lambda t:(t[1],t[0],t[3],t[2]); C_=lambda t:(t[2],t[3],t[0],t[1])
        orbit=lambda t:{t,S_(t),C_(t),S_(C_(t))}
        allowed={t for t in itertools.product((0,1),repeat=4) if (t[0] or t[1]) and (t[2] or t[3])}
        covered=set()
        for cs in c["cases"]:
            cp=rd(cs["pins"]); covered|=orbit(tuple(int(not cp[p]) for p in (a,b,cc,d)))
        assert covered==allowed
        for cs in c["cases"]: walk(cs["tree"],{**base,**rd(cs["pins"])},0)
        kind=f"{len(c['cases'])} symmetry cases covering all {len(allowed)} boundary colourings"
    else:
        walk(c["proof_tree"],rd(c["pins"]),0); kind="single proof tree"
    print(f"OK {os.path.basename(path)} [{kind}]: {len(P)} points ({sum(map(inL,P))} in Lambda, "
          f"{sum(1 for p in P if inQ(p) and not inL(p))} only in q*Lambda), {len(T)} forbidden triangles, "
          f"{st['splits']} splits, {st['leaves']} leaves, max depth {st['depth']}")
if __name__=="__main__":
    here=os.path.join(os.path.dirname(os.path.abspath(__file__)),"..","certificates")
    for f in sys.argv[1:] or [os.path.join(here,x) for x in ("ruleA_four_cases.json","ruleA_two_splits.json")]: main(f)
