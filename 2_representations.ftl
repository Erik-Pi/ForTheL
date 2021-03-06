[read representations/1_linear_algebra_axioms.ftl]

Let K denote a field.

# 1.1 K-algebras

Definition Algebra. An algebra over K is an object A such that
     (A is a vector space over K)
 and (A is a ring)
 and (for all x < K and all a,b < A : x @{A} (a *{A} b) = (x @{A} a) *{A} b = a *{A} (x @{A} b)).

Theorem. K is an algebra over K.
Proof.
 K is a vector space over K.
 Let us show that K is a ring.
  K is an abelian group.
  1{K} < K.
  For all a,b < K   : a *{K} b < K.
  For all a < K     :       a *{K} 1{K} = a.
  For all a < K     :       1{K} *{K} a = a.
  For all a,b,c < K : a *{K} (b *{K} c) = (a *{K} b) *{K} c (by Field).
  For all a,b,c < K : a *{K} (b +{K} c) = (a *{K} b) +{K} (a *{K} c) (by Field).
  For all a,b,c < K : (a +{K} b) *{K} c = (a *{K} c) +{K} (b *{K} c) (by Field).  
 qed.
 Let us show that for all x < K and all a,b < K :
 x @{K} (a *{K} b) = (x @{K} a) *{K} b = a *{K} (x @{K} b).
  Let x,a,b < K.
  x *{K} (a *{K} b) = (x *{K} a) *{K} b.
  (x *{K} a) *{K} b = (a *{K} x) *{K} b = a *{K} (x *{K} b).
 qed.
Qed.

Theorem. Let V be a vector space over K. Then End(K,V) is an algebra over K.
Proof.
 Take A = End(K,V).
 A is a vector space over K.
 A is a ring.
 Let us show that for all x < K and all f,g < A :
 x @{A} (f *{A} g) = (x @{A} f) *{A} g = f *{A} (x @{A} g).
  Let x < K. Let f,g < A.
  Let us show that for all v < V : (x @{A} (f *{A} g))(v) = ((x @{A} f) *{A} g)(v).
   Let v < V.
   (x @{A} (f *{A} g))(v) = x @{V} (f *{A} g)(v).
   x @{V} (f *{A} g)(v) = x @{V} (f*g)(v).
   x @{V} (f*g)(v) = x @{V} f(g(v)).
   Let us show that x @{V} f(g(v)) = (x @{A} f)(g(v)).
    x < K.
    f < Hom(K,V,V).
    For all w < V : (x @{Hom(K,V,V)} f)(w) = x @{V} f(w) (by MapSmul).
    g(v) < V.
   qed.
   (x @{A} f)(g(v)) = ((x @{A} f)*g)(v).
   x @{A} f < A.
   ((x @{A} f)*g)(v) = ((x @{A} f) *{A} g)(v).
  qed.
  x @{A} (f *{A} g), (x @{A} f) *{A} g < A.
  Dmn(x @{A} (f *{A} g)) = |V|.
  Dmn((x @{A} f) *{A} g) = |V|.
  Thus x @{A} (f *{A} g) = (x @{A} f) *{A} g.
  Let us show that for all v < V : ((x @{A} f) *{A} g)(v) = (f *{A} (x @{A} g))(v).
   Let v < V.
   ((x @{A} f) *{A} g)(v) = ((x @{A} f)*g)(v).
   ((x @{A} f)*g)(v) = (x @{A} f)(g(v)).
   Let us show that (x @{A} f)(g(v)) = x @{V} f(g(v)).
    x < K.
    f < Hom(K,V,V).
    For all w < V : (x @{Hom(K,V,V)} f)(w) = x @{V} f(w) (by MapSmul).
    g(v) < V.
   qed.
   Let us show that x @{V} f(g(v)) = f(x @{V} g(v)).
    f is linear over K from V to V.
    x < K.
    g(v) < V.
   qed.
   f(x @{V} g(v)) = f((x @{A} g)(v)).
   f((x @{A} g)(v)) = (f*(x @{A} g))(v).
   (f*(x @{A} g))(v) = (f *{A} (x @{A} g))(v).
  qed.
  f *{A} (x @{A} g) < A.
  Dmn(f *{A} (x @{A} g)) = |V|.
  Thus (x @{A} f) *{A} g = f *{A} (x @{A} g).
 qed.
 Therefore the thesis (by Algebra).
Qed.


# 1.2 K-algebra homomorphisms

Definition. Let A,B be objects. An algebrahom over K from A to B is a map f such that
     (A,B are algebras over K)
 and (f is linear over K from A to B)
 and (for all a,b < A : f(a *{A} b) = f(a) *{B} f(b))
 and (f(1{A}) = 1{B}).

Theorem. Let A be an algebra over K. Then id{|A|} is an algebrahom over K from A to A.
Proof.
 id{|A|} is linear over K from A to A.
Qed.


# 1.3 representations and A-modules

Definition. Let A,V be objects. A representation of A in V over K is an object p such that
     (A is an algebra over K)
 and (V is a vector space over K)
 and (p is an algebrahom over K from A to End(K,V)).

Let rep(p,K,A,V) stand for (A is an algebra over K and V is a vector space over K
                            and p is a representation of A in V over K).

Definition. Let A be an object. A module over A over K is an object V such that
     (A is an algebra over K)
 and (V is a vector space over K)
 and (for all a < A and all v < V : a @@{V} v < V)
 and (for all a < A and all v,w < V :             a @@{V} (v +{V} w) = (a @@{V} v) +{V} (a @@{V} w))
 and (for all x < K and all a < A and all v < V : a @@{V} (x @{V} v) = x @{V} (a @@{V} v))
 and (for all a,b < A and all v < V :             (a +{A} b) @@{V} v = (a @@{V} v) +{V} (b @@{V} v))
 and (for all x < K and all a < A and all v < V : (x @{A} a) @@{V} v = x @{V} (a @@{V} v))
 and (for all a,b < A and all v < V :             (a *{A} b) @@{V} v = a @@{V} (b @@{V} v))
 and (for all v < V :                                   1{A} @@{V} v = v).

Axiom. Let V be a vector space over K. Let x < K and v < V. x @@{V} v = x @{V} v.

Theorem. Let V be a vector space over K. V is a module over K over K.
Proof.
 K is an algebra over K.
 V is a vector space over K.
 For all a < K and all v < V : a @@{V} v < V.
 Let us show that for all a < K and all v,w < V : a @@{V} (v +{V} w) = (a @@{V} v) +{V} (a @@{V} w).
  Let a < K and v,w < V.
 a @{V} (v +{V} w) = (a @{V} v) +{V} (a @{V} w) (by VectorSpace).
 qed.
 Let us show that for all x,a < K and all v < V : a @@{V} (x @{V} v) = x @{V} (a @@{V} v).
  Let x,a < K and v < V.
  a @{V} (x @{V} v) = x @{V} (a @{V} v) (by VectorSpace).
 qed.
 Let us show that for all a,b < K and all v < V : (a +{K} b) @@{V} v = (a @@{V} v) +{V} (b @@{V} v).
  Let a,b < K and v < V.
  (a +{K} b) @{V} v = (a @{V} v) +{V} (b @{V} v) (by VectorSpace).
  a +{K} b < K.
 qed.
 Let us show that for all x,a < K and all v < V : (x @{K} a) @@{V} v = x @{V} (a @@{V} v).
  Let x,a < K and v < V.
  (x *{K} a) @{V} v = x @{V} (a @{V} v) (by VectorSpace).
  x @{K} a = x *{K} a < K.
 qed.
 Let us show that for all a,b < K and all v < V : (a *{K} b) @@{V} v = a @@{V} (b @@{V} v).
  Let a,b < K and v < V.
  a *{K} b < K.
  (a *{K} b) @@{V} v = (a *{K} b) @{V} v.
  a @@{V} (b @@{V} v) = a @{V} (b @{V} v).
  (a *{K} b) @{V} v = a @{V} (b @{V} v) (by VectorSpace).
 qed.
 For all v < V : 1{K} @@{V} v = v.
Qed.


# 1.3.1 every representation gives a module

Axiom. Let rep(p,K,A,V).  |rep2mod(p,K,A,V)| = |V|.
Axiom. Let rep(p,K,A,V). 0{rep2mod(p,K,A,V)} = 0{V}.
Axiom. Let rep(p,K,A,V). For all v,w < V :              v +{rep2mod(p,K,A,V)} w = v +{V} w.
Axiom. Let rep(p,K,A,V). For all v < V :                  ~{rep2mod(p,K,A,V)} v = ~{V} v.
Axiom. Let rep(p,K,A,V). For all x < K and all v < V :  x @{rep2mod(p,K,A,V)} v = x @{V} v.
Axiom. Let rep(p,K,A,V). For all a < A and all v < V : a @@{rep2mod(p,K,A,V)} v = p(a)(v).

Theorem. Let rep(p,K,A,V). rep2mod(p,K,A,V) is a module over A over K.
Proof.
 Take M = rep2mod(p,K,A,V).
 Let us show that M is a vector space over K.
  |M| = |V|.
  Thus M is a subspace of V over K.
 qed.

 Then End(K,V) is a vector space over K.
 p is linear over K from A to End(K,V).
 Dmn(p) = |A|.

 Let us show that M is a module over A over K.
  Let us show that for all a < A and all v < M : a @@{M} v < M.
   Let a < A and v < M.
   v < V.
   a << Dmn(p).      # When dealing with representations, more detailed proofs are needed.
   p(a) is a map.
   p(a) is linear over K from V to V.
   v << Dmn(p(a)).
   a @@{M} v = p(a)(v).
  qed.
  
  Let us show that for all a < A and all v,w < M :
  a @@{M} (v +{M} w) = (a @@{M} v) +{M} (a @@{M} w).
   Let a < A and v,w < M.
   a @@{M} (v +{M} w) = a @@{M} (v +{V} w).
   (a @@{M} v) +{M} (a @@{M} w) = (a @@{M} v) +{V} (a @@{M} w).
   Let us show that a @@{M} (v +{V} w) = (a @@{M} v) +{V} (a @@{M} w).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    v +{V} w, v, w << Dmn(p(a)).
    a @@{M} (v +{V} w) = p(a)(v +{V} w) = p(a)(v) +{V} p(a)(w) = (a @@{M} v) +{V} (a @@{M} w).
   qed.
  qed.

  Let us show that for all x < K and all a < A and all v < M :
  a @@{M} (x @{M} v) = x @{M} (a @@{M} v).
   Let x < K and a < A and v < M.
   a @@{M} (x @{M} v) = a @@{M} (x @{V} v).
   x @{M} (a @@{M} v) = x @{V} (a @@{M} v).
   Let us show that a @@{M} (x @{V} v) = x @{V} (a @@{M} v).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    x @{V} v, v << Dmn(p(a)).
    a @@{M} (x @{V} v) = p(a)(x @{V} v) = x @{V} p(a)(v) = x @{V} (a @@{M} v).
   qed.
  qed.

  Let us show that for all a,b < A and all v < M :
  (a +{A} b) @@{M} v = (a @@{M} v) +{M} (b @@{M} v).
   Let a,b < A and v < M.
   (a @@{M} v) +{M} (b @@{M} v) = (a @@{M} v) +{V} (b @@{M} v).
   Let us show that (a +{A} b) @@{M} v = (a @@{M} v) +{V} (b @@{M} v).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    v << Dmn(p(a)).
    b << Dmn(p).
    p(b) is a map.
    p(b) is linear over K from V to V.
    v << Dmn(p(b)).
    a +{A} b << Dmn(p).
    p(a +{A} b) is a map.
    p(a +{A} b) is linear over K from V to V.
    v << Dmn(p(a +{A} b)).
    (a +{A} b) @@{M} v = p(a +{A} b)(v).
    p(a) +{End(K,V)} p(b) is a map.
    Let us show that p(a +{A} b) = p(a) +{End(K,V)} p(b).
     p is an algebrahom over K from A to End(K,V).
    qed.
    v << Dmn(p(a) +{End(K,V)} p(b)).
    p(a +{A} b)(v) = (p(a) +{End(K,V)} p(b))(v).
    p(a), p(b) < Hom(K,V,V).
    (p(a) +{Hom(K,V,V)} p(b))(v) = p(a)(v) +{V} p(b)(v) (by MapAdd).
    p(a)(v) +{V} p(b)(v) = (a @@{M} v) +{V} (b @@{M} v).
   qed.
  qed.

  Let us show that for all x < K and all a < A and all v < M :
  (x @{A} a) @@{M} v = x @{M} (a @@{M} v).
   Let x < K and a < A and v < M.
   x @{M} (a @@{M} v) = x @{V} (a @@{M} v).
   Let us show that (x @{A} a) @@{M} v = x @{V} (a @@{M} v).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    v << Dmn(p(a)).
    x @{A} a << Dmn(p).
    p(x @{A} a) is a map.
    p(x @{A} a) is linear over K from V to V.
    v << Dmn(p(x @{A} a)).
    (x @{A} a) @@{M} v = p(x @{A} a)(v).
    x @{End(K,V)} p(a) is a map.
    Let us show that p(x @{A} a) = x @{End(K,V)} p(a).
     p is an algebrahom over K from A to End(K,V).
    qed.
    v << Dmn(x @{End(K,V)} p(a)).
    p(x @{A} a)(v) = (x @{End(K,V)} p(a))(v).
    (x @{End(K,V)} p(a))(v) = x @{V} p(a)(v).
    x @{V} p(a)(v) = x @{V} (a @@{M} v).
   qed.
  qed.

  Let us show that for all a,b < A and all v < M : (a *{A} b) @@{M} v = a @@{M} (b @@{M} v).
   Let a,b < A and v < M.
   Let us show that (a *{A} b) @@{M} v = a @@{M} (b @@{M} v).
    b << Dmn(p).
    p(b) is a map.
    p(b) is linear over K from V to V.
    v << Dmn(p(b)).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    p(b)(v) << Dmn(p(a)).
    a *{A} b << Dmn(p).
    p(a *{A} b) is a map.
    p(a *{A} b) is linear over K from V to V.
    v << Dmn(p(a *{A} b)).
    (a *{A} b) @@{M} v = p(a *{A} b)(v).
    p(a) *{End(K,V)} p(b) is a map.
    Let us show that p(a *{A} b) = p(a)*p(b).
     p is an algebrahom over K from A to End(K,V).
     p(a *{A} b) = p(a) *{End(K,V)} p(b).
     p(a) *{End(K,V)} p(b) = p(a)*p(b).
    qed.
    v << Dmn(p(a)*p(b)).
    p(a *{A} b)(v) = (p(a)*p(b))(v).
    (p(a)*p(b))(v) = p(a)(p(b)(v)).
    p(a)(p(b)(v)) = a @@{M} (p(b)(v)).
    a @@{M} (p(b)(v)) = a @@{M} (b @@{M} v).
   qed.
  qed.

  Let us show that for all v < M : 1{A} @@{M} v = v.
   Let v < M.
   1{A} << Dmn(p).
   p is an algebrahom over K from A to End(K,V).
   p(1{A}) = 1{End(K,V)}.
   1{A} @@{M} v = p(1{A})(v) = 1{End(K,V)}(v) = id{|V|}(v) = v.
  qed.
 qed.
Qed.


# 1.3.2 every module gives a representation

Axiom. Let A be an algebra over K. Let V be a module over A over K.
 mod2rep(K,A,V) is a map p such that Dmn(p) = |A| and for all a < A :
 (p(a) is a map such that Dmn(p(a)) = |V| and for all v < V : p(a)(v) = a @@{V} v).

Theorem. Let A be an algebra over K. Let V be a module over A over K.
 Then mod2rep(K,A,V) is a representation of A in V over K.
Proof.
 Take a map p such that p = mod2rep(K,A,V).
 A is a vector space over K.
 Then End(K,V) is a vector space over K.
 |A| is a set.
 |End(K,V)| is a set.
 Let us show that p is linear over K from A to End(K,V).
  Let us show that p is a map from |A| to |End(K,V)|.
   p is a map.
   Dmn(p) = |A|.
   For all a < A : a << Dmn(p).
   |End(K,V)| is a set.
   Let us show that for all a < A : p(a) < End(K,V).
    Let a < A.
    p(a) is a map.
    Let us show that p(a) is linear over K from V to V.
     Dmn(p(a)) = |V|.
     Let us show that for all v < V : p(a)(v) < V.
      Let v < V.
      p(a)(v) = a @@{V} v < V.
     qed.
     Let us show that for all u,v < V : p(a)(u +{V} v) = p(a)(u) +{V} p(a)(v).
      Let u,v < V.
      p(a)(u +{V} v) = a @@{V} (u +{V} v).
      a @@{V} (u +{V} v) = (a @@{V} u) +{V} (a @@{V} v) (by Module).
      (a @@{V} u) +{V} (a @@{V} v) = p(a)(u) +{V} p(a)(v).
     qed.
     Let us show that for all x < K and all v < V : p(a)(x @{V} v) = x @{V} p(a)(v).
      Let x < K and v < V.
      x @{V} v < V.
      p(a)(x @{V} v) = a @@{V} (x @{V} v).
      a @@{V} (x @{V} v) = x @{V} (a @@{V} v) (by Module).
      x @{V} (a @@{V} v) = x @{V} p(a)(v).
     qed.
    qed.
   qed.  
  qed.
  Let us show that for all a,b < A : p(a +{A} b) = p(a) +{End(K,V)} p(b).
   Let a,b < A.
   Let us show that for all v < V : p(a +{A} b)(v) = (p(a) +{End(K,V)} p(b))(v).
    Let v < V.
    a +{A} b < A.
    p(a +{A} b)(v) = (a +{A} b) @@{V} v.
    (a +{A} b) @@{V} v = (a @@{V} v) +{V} (b @@{V} v) (by Module).
    p(a), p(b) < Hom(K,V,V).
    (a @@{V} v) +{V} (b @@{V} v) = p(a)(v) +{V} p(b)(v) = (p(a) +{Hom(K,V,V)} p(b))(v).
   qed.
  qed.
  Let us show that for all x < K and all a < A : p(x @{A} a) = x @{End(K,V)} p(a).
   Let x < K and a < A.
   Let us show that for all v < V : p(x @{A} a)(v) = (x @{End(K,V)} p(a))(v).
    Let v < V.
    x @{A} a < A.
    p(x @{A} a)(v) = (x @{A} a) @@{V} v.
    (x @{A} a) @@{V} v = x @{V} (a @@{V} v) (by Algebra).
    x @{V} (a @@{V} v) = x @{V} p(a)(v).
    x @{V} p(a)(v) = (x @{End(K,V)} p(a))(v).
   qed.
  qed.
 qed.
 p is a map.
 Let us show that p is an algebrahom over K from A to End(K,V).
  Let us show that for all a,b < A : p(a *{A} b) = p(a) *{End(K,V)} p(b).
   Let a,b < A.
   Dmn(p(a *{A} b)) = |V|.
   Dmn(p(a) *{End(K,V)} p(b)) = |V|.
   Let us show that for all v < V : p(a *{A} b)(v) = (p(a) *{End(K,V)} p(b))(v).
    Let v < V.
    p(a *{A} b)(v) = (a *{A} b) @@{V} v.
    (a *{A} b) @@{V} v = a @@{V} (b @@{V} v).
    a @@{V} (b @@{V} v) = p(a)(b @@{V} v).
    p(a)(b @@{V} v) = p(a)(p(b)(v)).
    p(a)(p(b)(v)) = (p(a)*p(b))(v).
    (p(a)*p(b))(v) = (p(a) *{End(K,V)} p(b))(v).
   qed.
   Dmn(p(a *{A} b)) = |V|.
   Dmn(p(a) *{End(K,V)} p(b)) = |V|.
   Therefore the thesis.
  qed.
  Let us show that p(1{A}) = 1{End(K,V)}.
   Let us show that for all v < V : p(1{A})(v) = 1{End(K,V)}(v).
    Let v < V.
    p(1{A})(v) = 1{A} @@{V} v = v = id{|V|}(v) = 1{End(K,V)}(v).
   qed.
  qed.
 qed.
Qed.
