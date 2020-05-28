# In this file the linear algebra theorems are replaced by axioms without proofs.

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

Axiom. Let f be a function. Let id{A} and f be composable. Then id{A}*f = f.

Axiom. Let f be a function. Let Dom(f) = A. Then f*id{A} = f.

Axiom. Let A,B,C be sets. Let g:A->B. Let f:B->C. Then f*g : A->C.

Axiom. Let A,B,C,D be sets. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h : A->D.

Axiom. Let A,B,C,D be sets. Let h:A->B. Let g:B->C. Let f:C->D. Then f*(g*h) : A->D.

Axiom. Let A,B,C,D be sets. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h = f*(g*h).


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
Signature. Let a,b be objects. a @@{S} b is an object.


#003 abelian group

Definition AbelianGroup. An abelian group is a structure G such that
     (0{G} < G)
 and (for all a,b < G   : a +{G} b < G)
 and (for all a < G     :   ~{G} a < G)
 and (for all a < G     :       a +{G} 0{G} = a)
 and (for all a < G     :          a -{G} a = 0{G})
 and (for all a,b,c < G : a +{G} (b +{G} c) = (a +{G} b) +{G} c)
 and (for all a,b < G   :          a +{G} b = b +{G} a).

Axiom NegZero. Let G be an abelian group.
 Then ~{G} 0{G} = 0{G}.

Axiom ZeroAdd. Let G be an abelian group. Let a < G.
 Then 0{G} +{G} a = a.

Axiom NegAdd. Let G be an abelian group. Let a,b < G.
 Then ~{G} (a +{G} b) = (~{G} a) -{G} b.


#004 field

Definition Field. A field is a structure K such that
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

Axiom ZeroSmul. Let V be a vector space over K. Let v < V.
 Then 0{K} @{V} v = 0{V}.

Axiom SmulZero. Let V be a vector space over K. Let a < K.
 Then a @{V} 0{V} = 0{V}.

Axiom NegSmul. Let V be a vector space over K. Let a < K. Let v < V.
 Then (~{K} a) @{V} v = ~{V} (a @{V} v).

Axiom NegOneSmul. Let V be a vector space over K. Let v < V.
 Then (~{K} 1{K}) @{V} v = ~{V} v.

Axiom SmulNeg. Let V be a vector space over K. Let a < K. Let v < V.
 Then a @{V} (~{V} v) = ~{V} (a @{V} v).


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

Axiom. Let V and W be vector spaces over K.
 0{Hom(K,V,W)} is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Let f,g < Hom(K,V,W).
 Then f +{Hom(K,V,W)} g is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Let f < Hom(K,V,W).
 Then ~{Hom(K,V,W)} f is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Let a < K and f < Hom(K,V,W).
 Then a @{Hom(K,V,W)} f is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Then Hom(K,V,W) is a vector space over K.


#012 field2VS (this axiom is fairly different from the original)

Axiom. Let a,b < K. a @{K} b = a *{K} b.

Axiom. K is a vector space over K.


#013 dual

Axiom Exi. Let V be a vector space over K. Let v,w < V. Assume that v != w.
 There exists a function g such that g is linear over K from V to K and g[v] != g[w].

Definition. Let V be a vector space over K. dual(K,V) = Hom(K,V,K).

Definition. Let V be a vector space over K. Let v < V. eval(dual(K,V), v) is a function f such that
 Dom(f) = |dual(K,V)| and (for every element h of |dual(K,V)| : f[h] = h[v]).

Definition. Let V be a vector space over K. V2ddV(K,V) is a function f such that
 Dom(f) = |V| and (for every element v of |V| : f[v] = eval(dual(K,V),v)).

Axiom. Let V be a vector space over K.
 V2ddV(K,V) is injective and linear over K from V to dual(K,dual(K,V)).


#100 ring (= ring with 1)

Definition Ring. A ring is a structure R such that
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

Axiom. Let r,s,t < Un(R).
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

Axiom. Un(R) is a group.


#102 endomorphisms

Definition. Let V be a vector space over K. End(K,V) is Hom(K,V,V).

Axiom. Let V be a vector space over K. 1{End(K,V)} = id{|V|}.
Axiom. Let V be a vector space over K. Let f,g < End(K,V). f *{End(K,V)} g  = f*g.

Axiom. Let V be a vector space over K. Then id{|V|} is linear over K from V to V.

Axiom. Let U,V,W be vector spaces over K. Let f,g be functions.
 Let g be linear over K from U to V. Let f be linear over K from V to W.
 Then f*g is linear over K from U to W.

Axiom. Let V be a vector space over K. End(K,V) is a ring.


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

Axiom. Let V,W be vector spaces over K. Let f be a function.
 Let f be isomorphism over K from V to W. Then f^(-1) < Hom(K,W,V).

Axiom. Let V be a vector space over K. Let f be a function.
 f < Aut(K,V) iff f is isomorphism over K from V to V.


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

Axiom. Let V be a vector space over K. Then |V| is a subspace of V over K.

Axiom. Let sub(K,V,U). Then sub2VS(U) is a vector space over K.


#202 kernel

Signature. Let f be a function. Ker(f) is a set.
Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Ker(f) = {v < V | f[v] = 0{W}}.

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Let v,w < V. Let f[v] = f[w]. Then v -{V} w << Ker(f).

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Assume Ker(f) = {0{V}}. Then f is injective.

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Then Ker(f) is a subspace of V over K.