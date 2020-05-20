# This formalization is a rewrite of the linear algebra library at
# https://github.com/Felix-Thiele/linear_algebra_ftl
# The main difference is in the implementation of operations on algebraic structures.
# For example, every abelian group G used to have a function add{G} from Prod(|G|,|G|) to |G|.
# In this version, a +{G} b is always defined, but for G to be an abelian group, we demand that
# "for all a,b < G : a +{G} b < G".
# This avoidance of chains of functions and cartesian products makes the checking process way more
# efficient. Unlike the original library, the following proofs don't need any additional statements
# just to help the ontological checking. This makes the proofs much shorter and more readable.


#000 set

Let A,B,C,D denote sets.
Let x << A stand for x is an element of A.
Let A is subset of B stand for (for all x << A : x << B).

Definition.
Prod(A,B) = { (x,y) | x << A and y << B }.

Axiom SetEq. Assume A is subset of B. Assume B is subset of A. Then A = B.

Signature. Let a << A. A\{a} is a set.
Axiom. Let a << A. Then A\{a} = {x | x << A and x != a}.


#001 function

Definition. Let f be a function.
f is injective iff for all elements x,y of Dom(f) we have (f[x] = f[y] => x = y).

Definition. Let f be a function.
f is from A to B iff Dom(f) = A and for every x << A : f[x] << B.

Let f:A->B stand for (f is a function from A to B).

Axiom FunExt. Let f,g be functions.
If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

Definition FunId. id{A} is a function h such that Dom(h) = A and for all a << A : h[a] = a.

Definition FunRestr. Let f be a function. Let A be subset of Dom(f). f|A is a function h such that
 Dom(h) = A and for all x << A we have h[x] = f[x].

Signature. Let f,g be functions. f*g is a function.
Definition. Let f,g be functions.
 f and g are composable iff for all x << Dom(g) we have g[x] << Dom(f).
Axiom FunComp. Let f,g be composable functions. Then f*g is a function h such that
 Dom(h) = Dom(g) and for all x << Dom(g) : h[x] = f[g[x]].

Theorem. Let f be a function. Let id{A} and f be composable. Then id{A}*f = f.
Proof.
 For all x << Dom(f) : (id{A}*f)[x] = id{A}[f[x]] = f[x].
Qed.

Theorem. Let f be a function. Let Dom(f) = A. Then f*id{A} = f.
Proof.
 For all x << A : (f*id{A})[x] = f[id{A}[x]] = f[x].
Qed.

Theorem. Let A,B,C be sets. Let g:A->B. Let f:B->C. Then f*g : A->C.

Theorem. Let A,B,C,D be sets. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h : A->D.

Theorem. Let A,B,C,D be sets. Let h:A->B. Let g:B->C. Let f:C->D. Then f*(g*h) : A->D.

Theorem. Let A,B,C,D be sets. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h = f*(g*h).


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

Definition VectorSpace. A vector space over K is a structure V such that
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
   Dom(((a *{K} b) @{H} f)) = |V|.
   Dom((a @{H} (b @{H} f))) = |V|.
   Thus (a *{K} b) @{H} f = a @{H} (b @{H} f).
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
   Thus (a +{K} b) @{H} f = (a @{H} f) +{H} (b @{H} f).
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
   Thus a @{H} (f +{H} g) = (a @{H} f) +{H} (a @{H} g).
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
    i[a @{V} v][f] = f[a @{V} v] = a @{K} f[v] = a @{K} i[v][f].
    Let us show that (a @{ddV} i[v])[f]  = a @{K} i[v][f].
     a @{ddV} i[v] = a @{Hom(K,dual(K,V),K)} i[v].
     dual(K,V) is a vector space over K.
     f < dual(K,V).
    qed.
   qed.
   Thus i[a @{V} v] = a @{ddV} i[v].
  qed.
 qed.
Qed.


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

Theorem. Let U,V,W be vector spaces over K. Let f,g be functions.
 Let g be linear over K from U to V. Let f be linear over K from V to W.
 Then f*g is linear over K from U to W.
Proof.
 f*g is a function from |U| to |W|.
Qed.

Theorem. Let V be a vector space over K. End(K,V) is a ring.
Proof.
 Take a structure R such that R = End(K,V).
 Let us show that R is a ring.
  R is an abelian group.
  1{R} < R.
  Let us show that for all f,g < R : f *{R} g < R.
   Let f,g < R.
   f,g are linear over K from V to V.
   f*g is linear over K from V to V.
  qed.
  For all f < R : f *{R} 1{R} = f.
  For all f < R : 1{R} *{R} f = f.
  Let us show that for all f,g,h < R : f *{R} (g *{R} h) = (f *{R} g) *{R} h.
   Let f,g,h < R.
   f *{R} (g *{R} h) = f*(g*h).
   (f *{R} g) *{R} h = (f*g)*h.
   f,g,h are functions from |V| to |V|.
   f*(g*h) = (f*g)*h.
  qed.
  Let us show that for all f,g,h < R : f *{R} (g +{R} h) = (f *{R} g) +{R} (f *{R} h).
   Let f,g,h < R.
   Let us show that for all v < V : (f *{R} (g +{R} h))[v] = ((f *{R} g) +{R} (f *{R} h))[v].
    Let v < V.
    (f *{R} (g +{R} h))[v]
    = f[(g +{R} h)[v]]
    = f[g[v] +{V} h[v]]
    = f[g[v]] +{V} f[h[v]]
    = (f *{R} g)[v] +{V} (f *{R} h)[v]
    = ((f *{R} g) +{R} (f *{R} h))[v].
   qed.
  qed.
  Let us show that for all f,g,h < R : (f +{R} g) *{R} h = (f *{R} h) +{R} (g *{R} h).
   Let f,g,h < R.
   Let us show that for all v < V : ((f +{R} g) *{R} h)[v] = ((f *{R} h) +{R} (g *{R} h))[v].
    Let v < V.
    ((f +{R} g) *{R} h)[v]
    = (f +{R} g)[h[v]]
    = f[h[v]] +{V} g[h[v]]
    = (f *{R} h)[v] +{V} (g *{R} h)[v]
    = ((f *{R} h) +{R} (g *{R} h))[v].
   qed.
  qed.
 qed.
Qed.


#103 automorphisms

Definition. Let V be a vector space over K. Aut(K,V) is Un(End(K,V)).

Definition. Let f be a function.
 f is surjective onto B iff for all y << B there is an x << Dom(f) such that f[x] = y.

Definition. Let f be a function.
 f is bijective from A to B iff (f is from A to B and f is injective and f is surjective onto B).

Definition. Let V,W be vector spaces over K. Let f be a function.
 f is isomorphism over K from V to W iff (f < Hom(K,V,W) and f is bijective from |V| to |W|).

Signature. Let f be a function. f^(-1) is a function.
Axiom. Let f be a function. Let f be bijective from A to B. Then f^(-1) is a function from B to A
 and (for all x << A : f^(-1)[f[x]] = x) and (for all y << B : f[f^(-1)[y]] = y).

Theorem. Let V,W be vector spaces over K. Let f be a function.
 Let f be isomorphism over K from V to W. Then f^(-1) < Hom(K,W,V).
Proof.
 f is bijective from |V| to |W|.
 f^(-1) is a function from |W| to |V|.
 Let us show that f^(-1) is linear over K from W to V.
  Let us show that for all v,w < W : f^(-1)[v +{W} w] = f^(-1)[v] +{V} f^(-1)[w].
   Let v,w < W.
   f[f^(-1)[v +{W} w]] = v +{W} w.
   f[f^(-1)[v] +{V} f^(-1)[w]] = f[f^(-1)[v]] +{W} f[f^(-1)[w]] = v +{W} w.
   f is injective.
   Thus f^(-1)[v +{W} w] = f^(-1)[v] +{V} f^(-1)[w].
  qed.
  Let us show that for all a < K and all w < W : f^(-1)[a @{W} w] = a @{V} f^(-1)[w].
   Let a < K and w < W.
   f[f^(-1)[a @{W} w]] = a @{W} w.
   f[a @{V} f^(-1)[w]] = a @{W} f[f^(-1)[w]] = a @{W} w.
   f is injective.
   Thus f^(-1)[a @{W} w] = a @{V} f^(-1)[w].
  qed.
 qed.
Qed.

Theorem. Let V be a vector space over K. Let f be a function.
 f < Aut(K,V) iff f is isomorphism over K from V to V.
Proof.
 Let us show that f < Aut(K,V) => (f is isomorphism over K from V to V).
  Let f < Aut(K,V).
  Take g < Aut(K,V) such that (g *{Aut(K,V)} f = id{|V|} and f *{Aut(K,V)} g = id{|V|}).
  g*f = id{|V|}.
  f*g = id{|V|}.
  f is injective.
  f is surjective onto |V|.
 qed.
 Let us show that (f is isomorphism over K from V to V) => f < Aut(K,V).
  Let f be isomorphism over K from V to V.
  f^(-1) < End(K,V).
  f *{End(K,V)} (f^(-1)) = f*(f^(-1)) = 1{End(K,V)}.
  (f^(-1)) *{End(K,V)} f = (f^(-1))*f = 1{End(K,V)}.
 qed.
Qed.


#201 subspace

Definition. Let K be a field. Let V be a vector space over K.
A subspace of V over K is a set U such that
     (U is subset of |V|)
 and (0{V} << U)
 and (for all u,v << U             : u +{V} v << U)
 and (for all u << U               :   ~{V} u << U)
 and (for all a < K and all u << U : a @{V} u << U).

Let sub(K,V,U) stand for (V is a vector space over K and U is a subspace of V over K).

Signature. sub2VS(U) is a structure.
Axiom. Let sub(K,V,U). |sub2VS(U)| = U.
Axiom. Let sub(K,V,U). 0{sub2VS(U)} = 0{V}.
Axiom. Let sub(K,V,U). Let u,v < sub2VS(U).         u +{sub2VS(U)} v = u +{V} v.
Axiom. Let sub(K,V,U). Let u < sub2VS(U).             ~{sub2VS(U)} u = ~{V} u.
Axiom. Let sub(K,V,U). Let a < K and u < sub2VS(U). a @{sub2VS(U)} u = a @{V} u.

Theorem. Let V be a vector space over K. Then |V| is a subspace of V over K.
Proof.
 0{V} << |V|.
 For all u,v << |V|             : u +{V} v << |V|.
 For all u << |V|               :   ~{V} u << |V|.
 For all a < K for all u << |V| : a @{V} u << |V|.
Qed.

Theorem. Let sub(K,V,U). Then sub2VS(U) is a vector space over K.
Proof.
 Take a structure W such that W = sub2VS(U).
 Let us show that W is an abelian group.
  0{W} < W.
  For all u,v < W : u +{W} v < W.
  For all u < W   :   ~{W} u < W.
  For all u < W   :       u +{W} 0{W} = u.
  For all u < W   :          u -{W} u = 0{W}.
  Let us show that for all u,v,w < W : u +{W} (v +{W} w) = (u +{W} v) +{W} w.
   Let u,v,w < W.
   u +{W} (v +{W} w) = u +{V} (v +{V} w) = (u +{V} v) +{V} w = (u +{W} v) +{W} w.
  qed.
  Let us show that for all u,v < W : u +{W} v = v +{W} u.  
   Let u,v < W.
   u +{W} v = u +{V} v = v +{V} u = v +{W} u.
  qed.
 qed.

 Let us show that W is a vector space over K.
  For all a < K and all u < W  : a @{W} u < W.
  For all u < W : 1{K} @{W} u = u.

  Let us show that for all a,b < K and all u < W : (a *{K} b) @{W} u = a @{W} (b @{W} u).
   Let a,b < K and u < W.
   (a *{K} b) @{W} u = (a *{K} b) @{V} u.
   Let us show that (a *{K} b) @{V} u = a @{V} (b @{V} u).
    V is a vector space over K. 
    a,b < K. u < V.
    Therefore the thesis (by VectorSpace).
   qed.
   a @{V} (b @{V} u) = a @{W} (b @{W} u).
  qed.

  Let us show that for all a,b < K for all u < W : (a +{K} b) @{W} u = (a @{W} u) +{W} (b @{W} u).
   Let a,b < K and u < W.
   (a +{K} b) @{W} u = (a +{K} b) @{V} u.
   Let us show that (a +{K} b) @{V} u = (a @{V} u) +{V} (b @{V} u).
    V is a vector space over K.
    a,b < K. u < V.
    Therefore the thesis (by VectorSpace).
   qed.
   (a @{V} u) +{V} (b @{V} u) = (a @{W} u) +{W} (b @{W} u).
  qed.

  Let us show that for all a < K for all u,v < W : a @{W} (u +{W} v) = (a @{W} u) +{W} (a @{W} v).
   Let a < K and u,v < W.
   a @{W} (u +{W} v) = a @{V} (u +{V} v) =  (a @{V} u) +{V} (a @{V} v) = (a @{W} u) +{W} (a @{W} v).
  qed.
 qed.
Qed.


#202 kernel

Signature. Let f be a function. Ker(f) is a set.
Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Ker(f) = {v < V | f[v] = 0{W}}.

Theorem. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Let v,w < V. Let f[v] = f[w]. Then v -{V} w << Ker(f).
Proof.
 f is linear over K from V to W.
 v -{V} w < V.
 f[v -{V} w] = f[v] -{W} f[w].
 f[v] -{W} f[w] = f[v] -{W} f[w] = 0{W}.
Qed.

Theorem. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Assume Ker(f) = {0{V}}. Then f is injective.
Proof.
 Let us show that for all v,w < V : f[v] = f[w] => v = w.
  Let v,w < V. Assume f[v] = f[w].
  v -{V} w << Ker(f).
  v -{V} w = 0{V}.
  w = w +{V} 0{V} = w +{V} (v -{V} w) = v +{V} (w -{V} w) = v +{V} 0{V} = v.
 qed.
Qed.


Theorem. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Then Ker(f) is a subspace of V over K.
Proof.
 Ker(f) is subset of |V|.
 0{V} << Ker(f).
 Let us show that for all u,v << Ker(f) : u +{V} v << Ker(f).
  Let u,v << Ker(f).
  f[u +{V} v] = f[u] +{W} f[v] = 0{W} +{W} 0{W} = 0{W}.
 qed.
 For all u << Ker(f) : ~{V} u << Ker(f).
 Let us show that for all a < K and all u << Ker(f) : a @{V} u << Ker(f).
  Let a < K and u << Ker(f).
  f[a @{V} u] = a @{W} f[u] = a @{W} 0{W} = 0{W}.
 qed.
Qed.


# Up to this point, this formalization is 64% shorter than the corresponding parts of the
# original library (25 kB instead of 70 kB).
# It takes only 05:43 to check instead of approximately 100 minutes.
# The eprover.exe needs way less RAM now (ca. 600MB instead of 4GB).
