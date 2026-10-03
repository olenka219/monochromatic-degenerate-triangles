"""Generate the forcing tables and figures of the paper from the certificates.
Tables are produced by replaying each certificate with the forcing rule, stopping each branch at
its first contradiction and keeping only deductions some contradiction depends on."""
import json, os, math, itertools
from collections import deque
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
HERE=os.path.dirname(os.path.abspath(__file__)); ROOT=os.path.join(HERE,"..")
CERT=os.path.join(ROOT,"certificates"); OUT=os.path.join(ROOT,"paper"); FIG=os.path.join(OUT,"figures")
N=lambda a,b:a*a+a*b+b*b; R3=math.sqrt(3); h=lambda x:x%8 in (0,1,2,3)
inL=lambda p:p[0]%7==0 and p[1]%7==0
inQ=lambda p:(8*p[0]+5*p[1])%49==0 and (3*p[1]-5*p[0])%49==0
xy=lambda p:((p[0]+p[1]/2)/7,p[1]*R3/14)
CLS={(49,49,49):"T(1)",(441,441,441):"T(3)",(784,784,784):"T(4)",(49,441,784):"T(1,3,4)"}
cls=lambda t:CLS.get(tuple(sorted(N(t[i][0]-t[j][0],t[i][1]-t[j][1]) for i,j in ((0,1),(0,2),(1,2)))))
# bridge lemma configuration (c=1, b=4) is checked here too
w=lambda a,b:(a,b)
def bridge_check():
    c,b=1,4; A=(0,0);B=(c,0);C=(b,0);D=(c,-c);E=(b,c-b);F=(b,-b);G=(c,-b);H=(b+c,-b)
    d=lambda p,q:N(p[0]-q[0],p[1]-q[1])
    for t in [(A,B,C),(A,D,F),(B,D,G),(C,E,F),(F,G,H),(B,E,H)]: assert sorted(d(t[i],t[j]) for i,j in ((0,1),(0,2),(1,2)))==[1,9,16]
    for t,s in zip([(A,B,D),(A,C,F),(B,C,E),(D,F,G),(E,F,H),(B,G,H)],[1,16,9,9,1,16]): assert all(d(t[i],t[j])==s for i,j in ((0,1),(0,2),(1,2)))
bridge_check()
def eis(A,B):
    if A==0 and B==0: return "0"
    s=str(A) if A else ""
    if B: s+=("-" if B<0 else ("+" if A else ""))+("" if abs(B)==1 else str(abs(B)))+r"\omega"
    return s
def name(p):
    p=tuple(p)
    if inL(p): return "$"+eis(p[0]//7,p[1]//7)+"$"
    m=(8*p[0]+5*p[1])//49; n=(3*p[1]-5*p[0])//49
    if (m,n)==(1,0): return "$q$"
    if (m,n)==(-1,0): return "$-q$"
    return "$q("+eis(m,n)+")$"
col=lambda c:"red" if c else "blue"
def table(rows):
    s=[r"\begin{center}\small\begin{longtable}{rlll}\toprule & point & colour & because\\\midrule\endhead"]
    for k,(p,c,why) in enumerate(rows,1): s.append(f"{k} & {name(p)} & {col(c)} & {why}\\\\")
    s.append(r"\bottomrule\end{longtable}\end{center}"); return "\n".join(s)+"\n"
def tri_why(t,p,c):
    o=[x for x in t if x!=p]; return f"${cls(t)[0]}{cls(t)[1:]}$ with {name(o[0])}, {name(o[1])} ({col(1-c)})"
def contra(t,c): return f"\\noindent\\emph{{Contradiction:}} {', '.join(name(x) for x in t)} are all {col(c)} and form ${cls(t)}$.\\par\\medskip\n"
# ---------------- Rule A: replay a certificate
def replay(cert,pins,tree):
    P=[tuple(p) for p in cert["points"]]
    T=[t for t in itertools.combinations(P,3) if cls(t)]
    inc={}
    for t in T:
        for v in t: inc.setdefault(v,[]).append(t)
    nodes=[]
    def go(t,par_col,par_rs,new,parent,split):
        nid=len(nodes); col=dict(par_col); rs=dict(par_rs)
        for v,c in new.items(): col[v]=c; rs[v]=(nid,None)
        q=deque(new); conf=None; order=[]
        def check(u):
            for tt in inc.get(u,()):
                cs=[col.get(x) for x in tt]
                if None not in cs and cs[0]==cs[1]==cs[2]: return tt
        for u in new:
            conf=conf or check(u)
        while q and conf is None:
            v=q.popleft()
            for tt in inc.get(v,()):
                cs=[col.get(x) for x in tt]
                if cs.count(None)!=1: continue
                k=[x for x in cs if x is not None]
                if k[0]!=k[1]: continue
                u=tt[cs.index(None)]; col[u]=1-k[0]; rs[u]=(nid,tt); order.append(u)
                conf=check(u)
                if conf: break
                q.append(u)
        nodes.append(dict(id=nid,parent=parent,split=split,col=col,rs=rs,order=order,conf=conf))
        if conf is None:
            assert isinstance(t,dict); v=tuple(t["split"])
            nodes[nid]["kids"]=[go(t[key],col,rs,{v:b},nid,(v,b)) for b,key in ((0,"blue"),(1,"red"))]
        else: assert t=="leaf" or True
        return nid
    go(tree,{},{},pins,None,None)
    need=set()
    for n in nodes:
        if n["conf"] is None: continue
        st=list(n["conf"])
        while st:
            v=st.pop(); nid,tt=n["rs"][v]
            if tt is None or (nid,v) in need: continue
            need.add((nid,v)); st+=[x for x in tt if x!=v]
    return nodes,need
def render_tree(nodes,need,nid,depth,out):
    n=nodes[nid]
    rows=[(v,n["col"][v],tri_why(n["rs"][v][1],v,n["col"][v])) for v in n["order"] if (nid,v) in need]
    if rows: out.append(table(rows))
    if n["conf"]: out.append(contra(n["conf"],n["col"][n["conf"][0]])); return
    for k in n["kids"]:
        v,b=nodes[k]["split"]
        out.append(f"\\paragraph{{{['Case','Subcase','Sub-subcase'][min(depth,2)]}: {name(v)} {col(b)}.}}\n")
        render_tree(nodes,need,k,depth+1,out)
def ruleA_tables():
    c=json.load(open(os.path.join(CERT,"ruleA_four_cases.json")))
    rd=lambda L:{tuple(p):int(x=="R") for p,x in L}
    base=rd(c["base_pins"]); bd=[tuple(p) for p in c["boundary"]]
    out=[]
    for k,cs in enumerate(c["cases"],1):
        cp=rd(cs["pins"]); blue=[name(p) for p in bd if cp[p]==0]; red=[name(p) for p in bd if cp[p]==1]
        out.append(f"\\subsection*{{Case {k}: blue {', '.join(blue)}"+(f"; red {', '.join(red)}" if red else "")+"}\n")
        out.append(f"\\begin{{figure}}[h]\\centering\\includegraphics[width=\\textwidth]{{figures/ruleA_case{k}.png}}\\caption{{Rule A, case {k}: the row, the four forced points, and the boundary colouring of this case (ringed).}}\\end{{figure}}\n")
        nodes,need=replay(c,{**base,**cp},cs["tree"]); render_tree(nodes,need,0,1,out)
    open(os.path.join(OUT,"tables_ruleA_cases.tex"),"w").write("".join(out))
    c=json.load(open(os.path.join(CERT,"ruleA_two_splits.json")))
    nodes,need=replay(c,rd(c["pins"]),c["proof_tree"]); out=[]; render_tree(nodes,need,0,0,out)
    open(os.path.join(OUT,"tables_ruleA_two_splits.tex"),"w").write("".join(out))
# ---------------- Rule B tables
def ruleB_tables():
    c=json.load(open(os.path.join(CERT,"ruleB_cases.json")))
    S0={0:0,1:4,2:1}; DIR=[r"q",r"q\omega",r"q\omega^2"]
    def colour(p,cols):
        p=tuple(p); return cols[p] if p in cols else int(h(p[0]//7+S0[p[1]//7]))
    def rows(steps,cols,j):
        r=[]
        for st in steps:
            p=tuple(st["point"]); cc=int(st["colour"]=="R"); us=[tuple(x) for x in st["using"]]
            why=tri_why(tuple([p]+us),p,cc) if st["rule"]=="triangle" else f"four apart from {name(us[0])} along ${DIR[j]}$"
            cols[p]=cc; r.append((p,cc,why))
        return r
    cols={}; open(os.path.join(OUT,"table_ruleB_common.tex"),"w").write(table(rows(c["common"],cols,None)))
    out=[]
    for cs in c["cases"]:
        cc=dict(cols); r=rows(cs["steps"],cc,cs["j"]); pts=[tuple(x) for x in cs["contradiction"]["points"]]
        out.append(f"\\paragraph{{Case: the long direction of $q\\Lambda$ is ${DIR[cs['j']]}$.}}\n"+table(r)+contra(pts,colour(pts[0],cc))
               +f"\\begin{{figure}}[h]\\centering\\includegraphics[width=\\textwidth]{{figures/ruleB_case{cs['j']}.png}}\\caption{{Rule B, long direction ${DIR[cs['j']]}$: every deduction of this case (amber), the four-apart steps along the dashed lines, and the contradiction (red).}}\\end{{figure}}\n")
    open(os.path.join(OUT,"tables_ruleB_cases.tex"),"w").write("".join(out))
    return c
# ---------------- figures, in the style of the walkthroughs
plt.rcParams.update({"font.family":"STIXGeneral","mathtext.fontset":"stix"})
PANEL="#F8FAFB"; BORDER="#C9D1D9"; INK="#1D2733"; RED="#C0392B"; BLUE="#2458A6"; AMBER="#C98A00"; GREY="#8a96a3"; LINE="#8796a8"
QV=(5.5/7,2.5*R3/7)
def lam_name(p): return name(p)
def scene(box,coloured={},tris=(),pairs=(),lines=(),rings=(),clash=None,labels=(),bgQ=True,width=12.0):
    x0,y0,x1,y1=box
    fig=plt.figure(figsize=(width,width*(y1-y0)/(x1-x0)))
    ax=fig.add_axes([0,0,1,1]); ax.set_xlim(x0,x1); ax.set_ylim(y0,y1); ax.set_aspect("equal"); ax.axis("off")
    fig.patch.set_facecolor(PANEL)
    ax.add_patch(plt.Rectangle((x0,y0),x1-x0,y1-y0,fill=False,ec=BORDER,lw=1.5,zorder=0))
    ins=lambda p:x0<p[0]<x1 and y0<p[1]<y1
    for b in range(-16,17):
        for a in range(-22,23):
            p=(a+b/2,b*R3/2)
            if ins(p): ax.scatter(*p,s=9,c=GREY,alpha=.45,lw=0,zorder=1)
    if bgQ:
        for m in range(-22,23):
            for n in range(-22,23):
                z=(m+n/2,n*R3/2); p=(QV[0]*z[0]-QV[1]*z[1],QV[0]*z[1]+QV[1]*z[0])
                if ins(p): ax.scatter(*p,s=48,facecolors="none",edgecolors=GREY,lw=.8,alpha=.55,zorder=1)
    for (a,b,ext) in lines:
        P,Q=xy(a),xy(b); d=((Q[0]-P[0])/4,(Q[1]-P[1])/4)
        ax.plot([P[0]-ext*d[0],Q[0]+ext*d[0]],[P[1]-ext*d[1],Q[1]+ext*d[1]],ls=(0,(5,4)),c=LINE,lw=1.3,zorder=2)
    for t in tris: ax.add_patch(plt.Polygon([xy(v) for v in t],fill=False,ec=AMBER,lw=2.0,alpha=.85,joinstyle="round",zorder=3))
    for a,b in pairs:
        P,Q=xy(a),xy(b); ax.plot([P[0],Q[0]],[P[1],Q[1]],c=AMBER,lw=2.6,solid_capstyle="round",zorder=3)
    if clash: ax.add_patch(plt.Polygon([xy(v) for v in clash],fill=False,ec=RED,lw=3.2,joinstyle="round",zorder=4))
    for v,c in coloured.items():
        x,y=xy(v); cc=RED if c else BLUE
        if not inL(v): ax.scatter(x,y,s=150,marker="s",c=cc,edgecolors=INK,linewidths=.7,zorder=5)
        else: ax.scatter(x,y,s=95,c=cc,lw=0,zorder=5)
    for v in rings:
        x,y=xy(v); ax.scatter(x,y,s=520,facecolors="none",edgecolors=RED if clash and v in clash else AMBER,lw=2.4,zorder=6)
    for v in labels:
        x,y=xy(v); ax.text(x+.2,y+.2,name(v),fontsize=15,color=INK,zorder=7)
    return fig
def save(fig,fn): fig.savefig(os.path.join(FIG,fn),dpi=200,facecolor=PANEL); plt.close(fig)
S0={0:0,1:4,2:1}
def turn_rows(box,rows=(0,1,2)):
    x0,_,x1,_=box
    return {(7*a,7*b):int(h(a+S0[b])) for b in rows for a in range(-30,31) if x0<a+b/2<x1}
def fig_overlap():
    box=(-3.6,-2.3,3.6,2.3); shared=[]
    for m in range(-6,7):
        for n in range(-6,7):
            p=(14*m-7*n,7*m+21*n)          # (2+w)(m+nw) in numerator coordinates
            x,y=xy(p)
            if box[0]<x<box[2] and box[1]<y<box[3]: shared.append(p)
    f=scene(box,rings=shared,labels=[(0,0),(3,5),(14,7)])
    ax=f.axes[0]; ax.annotate("",xy=xy((3,5)),xytext=(0,0),arrowprops=dict(arrowstyle="->",color=AMBER,lw=2))
    save(f,"overlap.png")
def fig_ruleA():
    box=(-4.3,-1.5,6.3,1.5)
    row={(7*a,0):int(a in (0,1,2)) for a in range(-3,6)}
    forced={(7,-7):0,(14,-7):0,(0,7):0,(7,7):0}
    bnd=[(0,-7),(21,-7),(-7,7),(14,7)]
    save(scene(box,coloured={**row,**forced},rings=bnd,labels=bnd+[(7,-7),(14,-7),(0,7),(7,7)]),"ruleA_setup.png")
    reps=[(1,1,1,1),(0,1,1,1),(0,1,0,1),(1,0,0,1)]
    for k,rep in enumerate(reps,1):
        cp={p:(0 if b else 1) for p,b in zip(bnd,rep)}
        save(scene(box,coloured={**row,**forced,**cp},rings=bnd,labels=bnd),f"ruleA_case{k}.png")
def ruleB_box(c):
    pts=set()
    for st in c["common"]+[s for cs in c["cases"] for s in cs["steps"]]:
        pts|={tuple(st["point"]),*[tuple(x) for x in st["using"]]}
    for cs in c["cases"]: pts|={tuple(x) for x in cs["contradiction"]["points"]}
    X=[xy(p)[0] for p in pts]; Y=[xy(p)[1] for p in pts]
    return (min(X)-.8,min(Y)-.8,max(X)+1.5,max(Y)+.8)
def fig_ruleB(c):
    box=ruleB_box(c); x0,_,x1,_=box
    rbox=(x0,-1.3,x1,2.7)
    mid={(7*a,7):int(h(a+4)) for a in range(-30,31) if x0<a+.5<x1}
    forced={}; opened=[]
    for a in range(-30,31):
        if x0<a<x1:
            l,r=h(a-1+4),h(a+4); (forced.__setitem__((7*a,0),int(not l)) if l==r else opened.append((7*a,0)))
        if x0<a+1<x1:
            l,r=h(a+4),h(a+5); (forced.__setitem__((7*a,14),int(not l)) if l==r else opened.append((7*a,14)))
    save(scene(rbox,coloured={**mid,**forced},rings=opened),"ruleB_one_row.png")
    save(scene(rbox,coloured=turn_rows(rbox),rings=[(0,0),(-7,14)],labels=[(0,0),(-7,14)]),"ruleB_turn.png")
    base=turn_rows(box); cols={}; tris=[]
    for st in c["common"]:
        p=tuple(st["point"]); cols[p]=int(st["colour"]=="R"); tris.append([p]+[tuple(x) for x in st["using"]])
    save(scene(box,coloured={**base,**cols},tris=tris,labels=list(cols)),"ruleB_common.png")
    for cs in c["cases"]:
        cc=dict(cols); tr=list(tris); pairs=[]; lines=[]; lab=list(cols)
        for st in cs["steps"]:
            p=tuple(st["point"]); us=[tuple(x) for x in st["using"]]; cc[p]=int(st["colour"]=="R"); lab.append(p)
            if st["rule"]=="triangle": tr.append([p]+us)
            else: pairs.append((us[0],p)); lines.append((us[0],p,1.5))
        ct=[tuple(x) for x in cs["contradiction"]["points"]]
        save(scene(box,coloured={**base,**cc},tris=tr,pairs=pairs,lines=lines,rings=ct,clash=ct,labels=lab+[x for x in ct if x not in lab]),f"ruleB_case{cs['j']}.png")
if __name__=="__main__":
    os.makedirs(FIG,exist_ok=True)
    ruleA_tables(); c=ruleB_tables(); fig_overlap(); fig_ruleA(); fig_ruleB(c)
    print("tables and figures written")
