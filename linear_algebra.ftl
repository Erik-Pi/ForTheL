#000 set

Let M,N,A denote sets.
Let x << M stand for x is an element of M.
Let M is subset of N stand for (for all x << M : x << N).

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Axiom SetEq.
Assume for all a << M a << N.
Assume for all a << N a << M.
Then M = N.

Signature. Let a << M. M\{a} is a set.
Axiom. Let a << M. Then M\{a} = {x | x << M and x != a}.


#001 function

Definition.
Let f be a function.
f is injective iff for all elements x,y of Dom(f) we have (f[x] = f[y] => x = y).

Definition.
Let f be a function. Let M,N be sets.
f is from M to N iff Dom(f) = M and for every x << M : f[x] << N.

Let f:M->N stand for (f is a function from M to N).

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

Definition FunId. Let A be a set. id{A} is a function h such that
 Dom(h) = A and for all a << A : h[a] = a.

Definition FunRestr. Let f be a function. Let M be subset of Dom(f). f|{M} is a function h such that
 Dom(h) = M and for all x << M we have h[x] = f[x].

Signature. f*g is a function.
Definition. Let f,g be functions. f and g are composable iff for all x << Dom(g) we have g[x] << Dom(f).
Axiom FunComp. Let f,g be composable functions. Then f*g is a function h such that
 Dom(h) = Dom(g) and for all x << Dom(g) : h[x] = f[g[x]].


#002 structure

Signature. A structure is a notion.
Let S denote a structure.

Signature. |S| is a set.
Let a < S stand for a << |S|.

Signature. 0{S} is an object.
Let a < S* stand for a << |S|\{0{S}}.
Signature. 1{S} is an object.
Signature. Let a,b be objects. a +{S} b is an object.
Signature. Let a,b be objects. a *{S} b is an object.
Signature. Let a be an object. ~{S} a is an object.
Let a -{S} b stand for a +{S} (~{S} b).
Signature. Let a be an object. inv{S} a is an object.
Let a /{S} b stand for a *{S} (inv{S} b).
Signature. Let a,b be objects. a @{S} b is an object.


#003 abelian group

Definition. An abelian group is a structure G such that
     (0{G} < G)
 and (for all a,b < G   : a +{G} b < G)
 and (for all a < G     :   ~{G} a < G)
 and (for all a < G     :       a +{G} 0{G} = a)
 and (for all a < G     :          a -{G} a = 0{G})
 and (for all a,b,c < G : a +{G} (b +{G} c) = (a +{G} b) +{G} c)
 and (for all a,b < G   :          a +{G} b = b +{G} a).

Theorem NegZero. Let G be an abelian group.
Then ~{G} 0{G} = 0{G}.

Theorem ZeroAdd. Let G be an abelian group. Let a < G.
Then 0{G} +{G} a = a.

Theorem NegAdd. Let G be an abelian group. Let a,b < G.
Then ~{G} (a +{G} b) = (~{G} a) -{G} b.
Proof.
 ~{G} (a +{G} b) = (~{G} (a +{G} b)) +{G} ((a -{G} a) +{G} (b -{G} b)).
 (~{G} (a +{G} b)) +{G} ((a -{G} a) +{G} (b -{G} b))
 = ((~{G} (a +{G} b)) +{G} (a +{G} b)) +{G} ((~{G} a) -{G} b).
 ((~{G} (a +{G} b)) +{G} (a +{G} b)) +{G} ((~{G} a) -{G} b) = (~{G} a) -{G} b.
Qed.

Theorem. Let G be an abelian group. Let a,b,c,d,e,f < G.
Then a +{G} (b +{G} (c +{G} (d +{G} (e +{G} f)))) = ((((a +{G} b) +{G} c) +{G} d) +{G} e) +{G} f.


#004 field

Definition. A field is a structure K such that
     (K is an abelian group)
 and (1{K} < K)
 and (for all a,b < K   : a *{K} b < K)
 and (for all a < K     : inv{K} a < K)
 and (for all a < K     :       a *{K} 1{K} = a)
 and (for all a < K*    :          a /{K} a = 1{K})
 and (for all a,b,c < K : a *{K} (b *{K} c) = (a *{K} b) *{K} c)
 and (for all a,b < K   :          a *{K} b = b *{K} a)
 and (for all a,b,c < K : a *{K} (b +{K} c) = (a *{K} b) +{K} (a *{K} c)).

Let K denote a field.


#005 vector space

[synonym space/-s]

Definition. A vector space over K is a structure V such that
     (V is an abelian group)
 and (for all a < K and all v < V   : a @{V} v < V)
 and (for all v < V                 :       1{K} @{V} v = v)
 and (for all a,b < K for all v < V : (a *{K} b) @{V} v = a @{V} (b @{V} v))
 and (for all a,b < K for all v < V : (a +{K} b) @{V} v = (a @{V} v) +{V} (b @{V} v))
 and (for all a < K for all v,w < V : a @{V} (v +{V} w) = (a @{V} v) +{V} (a @{V} w)).

Theorem ZeroSmul. Let V be a vector space over K. Let v < V.
 Then 0{K} @{V} v = 0{V}.
Proof.
 0{K} @{V} v
 = ((0{K} @{V} v) +{V} (1{K} @{V} v)) +{V} (~{V} v)
 = ((0{K} +{K} 1{K}) @{V} v) +{V} (~{V} v)
 = (1{K} @{V} v) +{V} (~{V} v)
 = v +{V} (~{V} v)
 = 0{V}.
Qed.

Theorem SmulZero. Let V be a vector space over K. Let a < K.
 Then a @{V} 0{V} = 0{V}.

Theorem NegSmul. Let V be a vector space over K. Let a < K. Let v < V.
 Then (~{K} a) @{V} v = ~{V} (a @{V} v).
Proof.
 (~{K} a) @{V} v
 = (((~{K} a) @{V} v) +{V} (a @{V} v)) +{V} (~{V} (a @{V} v))
 = ~{V} (a @{V} v).
Qed.

Theorem NegOneSmul. Let V be a vector space over K. Let v < V.
 Then (~{K} 1{K}) @{V} v = ~{V} v.

Theorem SmulNeg. Let V be a vector space over K. Let a < K. Let v < V.
 Then a @{V} (~{V} v) = ~{V} (a @{V} v).
Proof.
 a @{V} (~{V} v)
 = (a @{V} (~{V} v)) +{V} ((a @{V} v) -{V} (a @{V} v))
 = ((a @{V} (~{V} v)) +{V} (a @{V} v)) -{V} (a @{V} v)
 = ~{V} (a @{V} v).
Qed.


#005-011 homomorphisms

Definition. Let V and W be vector spaces over K. Let f be a function.
 f is linear over K from V to W iff
     (f is from |V| to |W|)
 and (for all u,v < V             : f[u +{V} v] = f[u] +{W} f[v])
 and (for all a < K for all v < V : f[a @{V} v] = a @{W} f[v]).

Signature. Let V and W be vector spaces over K. Hom(K,V,W) is a structure.
Axiom. Let V and W be vector spaces over K.
 |Hom(K,V,W)| is the set of functions f such that f is linear over K from V to W.

Axiom. Let V and W be vector spaces over K.
 0{Hom(K,V,W)} is a function h such that Dom(h) = |V| and for all v < V : h[v] = 0{W}.

Axiom. Let V and W be vector spaces over K. Let f,g < Hom(K,V,W).
 f +{Hom(K,V,W)} g is a function h such that Dom(h) = |V| and
 for all v < V : h[v] = f[v] +{W} g[v].

Axiom. Let V and W be vector spaces over K. Let f < Hom(K,V,W).
 ~{Hom(K,V,W)} f is a function h such that Dom(h) = |V| and
 for all v < V : h[v] = ~{W} f[v].

Axiom. Let V and W be vector spaces over K. Let a < K and f < Hom(K,V,W).
 a @{Hom(K,V,W)} f is a function h such that Dom(h) = |V| and
 for all v < V : h[v] = a @{W} f[v].

Lemma. Let V and W be vector spaces over K.
 0{Hom(K,V,W)} is linear over K from V to W.
Proof.
 Take a function h such that h = 0{Hom(K,V,W)}.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  For all u,v < V             : h[u +{V} v] = h[u] +{W} h[v].
  For all a < K for all v < V : h[a @{V} v] = a @{W} h[v].
 qed.
Qed.

Lemma. Let V and W be vector spaces over K. Let f,g < Hom(K,V,W).
 Then f +{Hom(K,V,W)} g is linear over K from V to W.
Proof.
 Take a function h such that h = f +{Hom(K,V,W)} g.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  Let us show that for all u,v < V : h[u +{V} v] = h[u] +{W} h[v].
   Let u,v < V.
   h[u +{V} v] = f[u +{V} v] +{W} g[u +{V} v].
   f[u +{V} v] +{W} g[u +{V} v] = (f[u] +{W} f[v]) +{W} (g[u] +{W} g[v]).
   Let us show that (f[u] +{W} f[v]) +{W} (g[u] +{W} g[v]) = (f[u] +{W} g[u]) +{W} (f[v] +{W} g[v]).
    f[u],f[v],g[u],g[v] < W. 
   qed.
   (f[u] +{W} g[u]) +{W} (f[v] +{W} g[v]) = h[u] +{W} h[v].
  qed.
  Let us show that for all a < K for all v < V : h[a @{V} v] = a @{W} h[v].
   Let a < K and v < V.
   h[a @{V} v] = f[a @{V} v] +{W} g[a @{V} v].
   f[a @{V} v] +{W} g[a @{V} v] = (a @{W} f[v]) +{W} (a @{W} g[v]).
   (a @{W} f[v]) +{W} (a @{W} g[v]) = a @{W} (f[v] +{W} g[v]).
   a @{W} (f[v] +{W} g[v]) = a @{W} h[v].
  qed.
 qed.
Qed.

Lemma. Let V and W be vector spaces over K. Let f < Hom(K,V,W).
 Then ~{Hom(K,V,W)} f is linear over K from V to W.
Proof.
 Take a function h such that h = ~{Hom(K,V,W)} f.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  Let us show that for all u,v < V : h[u +{V} v] = h[u] +{W} h[v].
   Let u,v < V.
   h[u +{V} v] = ~{W} f[u +{V} v].
   ~{W} f[u +{V} v] = ~{W} (f[u] +{W} f[v]).
   ~{W} (f[u] +{W} f[v]) = (~{W} f[u]) +{W} (~{W} f[v]).
   (~{W} f[u]) +{W} (~{W} f[v]) = h[u] +{W} h[v].
  qed.
  Let us show that for all a < K for all v < V : h[a @{V} v] = a @{W} h[v].
   Let a < K and v < V.
   h[a @{V} v]
   = ~{W} f[a @{V} v]
   = ~{W} (a @{W} f[v])
   = a @{W} (~{W} f[v])
   = a @{W} h[v].
  qed.
 qed.
Qed.

Lemma. Let V and W be vector spaces over K. Let a < K and f < Hom(K,V,W).
 Then a @{Hom(K,V,W)} f is linear over K from V to W.
Proof.
 Take a function h such that h = a @{Hom(K,V,W)} f.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  Let us show that for all u,v < V : h[u +{V} v] = h[u] +{W} h[v].
   Let u,v < V.
   h[u +{V} v] = a @{W} f[u +{V} v].
   a @{W} f[u +{V} v] = a @{W} (f[u] +{W} f[v]).
   a @{W} (f[u] +{W} f[v]) = (a @{W} f[u]) +{W} (a @{W} f[v]).
   (a @{W} f[u]) +{W} (a @{W} f[v]) = h[u] +{W} h[v].
  qed.
  Let us show that for all b < K for all v < V : h[b @{V} v] = b @{W} h[v].
   Let b < K and v < V.
   h[b @{V} v]
   = a @{W} f[b @{V} v]
   = a @{W} (b @{W} f[v])
   = b @{W} (a @{W} f[v])
   = b @{W} h[v].
  qed.
 qed.
Qed.

Theorem. Let V and W be vector spaces over K. Then Hom(K,V,W) is a vector space over K.
Proof.
 Take a structure H such that H = Hom(K,V,W).
 Let us show that H is an abelian group.
  0{H} < H.
  For all f,g < H : f +{H} g < H.
  For all f < H   :   ~{H} f < H.
  Let us show that for all f < H : f +{H} 0{H} = f.
   Let f < H.
   Let us show that for all v < V : (f +{H} 0{H})[v] = f[v].
    Let v < V.
    (f +{H} 0{H})[v] = f[v] +{W} (0{H}[v]) = f[v].
   qed.
  qed.
  Let us show that for all f < H : f -{H} f = 0{H}.
   Let f < H.
   Let us show that for all v < V : (f -{H} f)[v] = 0{H}[v].
    Let v < V.
    (f -{H} f)[v] = f[v] +{W} (~{H}f)[v] = f[v] -{W} f[v] = 0{W} = 0{H}[v].
   qed.
  qed.
  Let us show that for all f,g,h < H : f +{H} (g +{H} h) = (f +{H} g) +{H} h.
   Let f,g,h < H.
   Let us show that for all v < V : (f +{H} (g +{H} h))[v] = ((f +{H} g) +{H} h)[v].
    Let v < V.
    (f +{H} (g +{H} h))[v]
    = f[v] +{W} (g[v] +{W} h[v])
    = (f[v] +{W} g[v]) +{W} h[v]
    = ((f +{H} g) +{H} h)[v].
   qed.
  qed.
  Let us show that for all f,g < H : f +{H} g = g +{H} f.
   Let f,g < H.
   Let us show that for all v < V : (f +{H} g)[v] = (g +{H} f)[v].
    Let v < V.
    (f +{H} g)[v] = f[v] +{W} g[v] = g[v] +{W} f[v] = (g +{H} f)[v].
   qed.
  qed.
 qed.
 Let us show that H is a vector space over K.  
  H is an abelian group.
  For all a < K and all f < H : a @{H} f < H.
  Let us show that for all f < H : 1{K} @{H} f = f.
   Let f < H.
   For all v < V : (1{K} @{H} f)[v] = f[v].
  qed.
  Let us show that for all a,b < K and all f < H : (a *{K} b) @{H} f = a @{H} (b @{H} f).
   Let a,b < K and f < H.
   Let us show that for all v < V : ((a *{K} b) @{H} f)[v] = (a @{H} (b @{H} f))[v].
    Let v < V.
    ((a *{K} b) @{H} f)[v]
    = (a *{K} b) @{W} f[v]
    = a @{W} (b @{W} f[v])
    = a @{W} (b @{H} f)[v]
    = (a @{H} (b @{H} f))[v].
   qed.
  qed.
  Let us show that for all a,b < K and all f < H : (a +{K} b) @{H} f = (a @{H} f) +{H} (b @{H} f).
   Let a,b < K and f < H.
   Let us show that for all v < V : ((a +{K} b) @{H} f)[v] = ((a @{H} f) +{H} (b @{H} f))[v].
    Let v < V.
    ((a +{K} b) @{H} f)[v]
    = (a +{K} b) @{W} f[v]
    = (a @{W} f[v]) +{W} (b @{W} f[v])
    = (a @{H} f)[v] +{W} (b @{H} f)[v]
    = ((a @{H} f) +{H} (b @{H} f))[v].
   qed.
  qed.
  Let us show that for all a < K and all f,g < H : a @{H} (f +{H} g) = (a @{H} f) +{H} (a @{H} g).
   Let a < K and f,g < H.
   Let us show that for all v < V : (a @{H} (f +{H} g))[v] = ((a @{H} f) +{H} (a @{H} g))[v].
    Let v < V.
    (a @{H} (f +{H} g))[v]
    = a @{W} (f +{H} g)[v]
    = a @{W} (f[v] +{W} g[v])
    = (a @{W} f[v]) +{W} (a @{W} g[v])
    = (a @{H} f)[v] +{W} (a @{H} g)[v]
    = ((a @{H} f) +{H} (a @{H} g))[v].
   qed.
  qed.
 qed.
Qed.


#012 field2VS (this axiom is fairly different from the original)

Axiom. Let a,b < K. a @{K} b = a *{K} b.

Theorem. K is a vector space over K.
Proof.
 K is an abelian group.
 For all a < K and all v < K : a @{K} v < K.
 For all v < K                 :       1{K} @{K} v = v.
 For all a,b < K for all v < K : (a *{K} b) @{K} v = a @{K} (b @{K} v).
 For all a,b < K for all v < K : (a +{K} b) @{K} v = (a @{K} v) +{K} (b @{K} v).
 For all a < K for all v,w < K : a @{K} (v +{K} w) = (a @{K} v) +{K} (a @{K} w).
Qed.


#013 dual

Axiom Exi. Let V be a vector space over K. Let v,w < V. Assume that v != w.
 There exists a function g such that g is linear over K from V to K and g[v] != g[w].

Definition. Let V be a vector space over K. dual(K,V) = Hom(K,V,K).

Definition. Let V be a vector space over K. Let v < V. eval(dual(K,V), v) is a function f such that
 Dom(f) = |dual(K,V)| and (for every element h of |dual(K,V)| : f[h] = h[v]).

Definition. Let V be a vector space over K. V2ddV(K,V) is a function f such that
 Dom(f) = |V| and (for every element v of |V| : f[v] = eval(dual(K,V),v)).

Theorem. Let V be a vector space over K.
 V2ddV(K,V) is injective and linear over K from V to dual(K,dual(K,V)).
Proof.
 Take a function i such that i = V2ddV(K,V).
 Take a structure ddV such that ddV = dual(K,dual(K,V)).

 Let us show that i is injective.
  Let us show that for all v,w < V : (v != w => i[v] != i[w]).
   Let v,w < V. Assume v != w.
   Take a function g  such that g is linear over K from V to K and g[v] != g[w].
   Thus i[v][g] != i[w][g].
  qed.
 qed.

 Let us show that i is linear over K from V to ddV.

  Let us show that i is from |V| to |ddV|.
   Let us show that for all v < V : (i[v] is linear over K from dual(K,V) to K).
    Let v < V.
    Let us show that i[v] is from |dual(K,V)| to |K|.
     Let us show that for all f < dual(K,V) : i[v][f] < K.
      Let f < dual(K,V).
      i[v][f] = f[v].
     qed.
    qed.
   qed.
  qed.

  Let us show that for all u,v < V : i[u +{V} v] = i[u] +{ddV} i[v].
   Let u,v < V.
   Let us show that for all f < dual(K,V) : i[u +{V} v][f] = (i[u] +{ddV} i[v])[f].
    Let f < dual(K,V).
    i[u +{V} v][f] = f[u +{V} v] = f[u] +{K} f[v] = i[u][f] +{K} i[v][f].
    Let us show that (i[u] +{ddV} i[v])[f] = i[u][f] +{K} i[v][f].
     i[u] +{ddV} i[v] = i[u] +{Hom(K,dual(K,V),K)} i[v].
     dual(K,V) is a vector space over K.
    qed.
   qed.
   Thus i[u +{V} v] = i[u] +{ddV} i[v].
  qed.

  Let us show that for all a < K and all v < V : i[a @{V} v] = a @{ddV} i[v].
   Let a < K and v < V.
   Let us show that for all f < dual(K,V) : i[a @{V} v][f] = (a @{ddV} i[v])[f].
    Let f < dual(K,V).
    i[a @{V} v][f] = f[a @{V} v] = a @{K} f[v].
    a @{ddV} i[v] = a @{Hom(K,dual(K,V),K)} i[v].
    (a @{ddV} i[v])[f] = a @{K} i[v][f] = a @{K} f[v].
   qed.
   Thus i[a @{V} v] = a @{ddV} i[v].
  qed.
 qed.
Qed. 

# Up to this point: Only 14000 characters instead of the original 44000 (that is -68%).
# Takes about 2 minutes up to here.


#100 ring (= ring with 1)

Definition. A ring is a structure R such that
     (R is an abelian group)
 and (1{R} < R)
 and (for all a,b < R   : a *{R} b < R)
 and (for all a < R     :       a *{R} 1{R} = a)
 and (for all a < R     :       1{R} *{R} a = a)
 and (for all a,b,c < R : a *{R} (b *{R} c) = (a *{R} b) *{R} c)
 and (for all a,b,c < R : a *{R} (b +{R} c) = (a *{R} b) +{R} (a *{R} c))
 and (for all a,b,c < R : (a +{R} b) *{R} c = (a *{R} c) +{R} (b *{R} c)).

Let R denote a ring.


#101 unit group

Signature. Un(R) is a structure.
Axiom. |Un(R)| = {r | r < R and there is s < R such that (r *{R} s = 1{R} and s *{R} r = 1{R})}.

Theorem. Let r,s,t < Un(R).
 Assume r *{R} s = 1{R} and s *{R} r = 1{R}. Assume r *{R} t = 1{R} and t *{R} r = 1{R}.
 Then s = t.

# The theorem above allows the following definition.

Axiom. Let r < Un(R). inv{R} r < R.
Axiom. Let r < Un(R). r *{R} (inv{R} r) = 1{R}.
Axiom. Let r < Un(R). (inv{R} r) *{R} r = 1{R}.

Axiom. 1{Un(R)} = 1{R}.
Axiom. Let a,b < Un(R). a *{Un(R)} b = a *{R} b.
Axiom. Let a < Un(R).   inv{Un(R)} a = inv{R} a.

Definition. A group is a structure G such that
     (1{G} < G)
 and (for all a,b < G   : a *{G} b < G)
 and (for all a < G     : inv{G} a < G)
 and (for all a < G     :       a *{G} 1{G} = a)
 and (for all a < G     :          a /{G} a = 1{G})
 and (for all a,b,c < G : a *{G} (b *{G} c) = (a *{G} b) *{G} c).

Theorem. Un(R) is a group.
Proof.
 1{Un(R)} < Un(R).
 For all a,b < Un(R)   : a *{Un(R)} b < Un(R).
 For all a < Un(R)     : inv{Un(R)} a < Un(R).
 For all a < Un(R)     :       a *{Un(R)} 1{Un(R)} = a.
 For all a < Un(R)     :              a /{Un(R)} a = 1{Un(R)}.
 For all a,b,c < Un(R) : a *{Un(R)} (b *{Un(R)} c) = (a *{Un(R)} b) *{Un(R)} c.
Qed.


#102 endomorphisms

Definition. Let V be a vector space over K. End(K,V) is Hom(K,V,V).

Axiom. Let V be a vector space over K. 1{End(K,V)} = id{|V|}.
Axiom. Let V be a vector space over K. Let f,g < End(K,V). f *{End(K,V)} g  = f*g.

Theorem. Let V be a vector space over K. Then id{|V|} is linear over K from V to V.
Proof.
 id{|V|} is a function from |V| to |V|.
Qed.