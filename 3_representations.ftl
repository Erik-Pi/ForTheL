[read representations/2_representations_axioms.ftl]

Let K denote a field.

# 1.4 A-module homomorphisms

Definition ModuleHom. Let A,M,N be objects.
 A modulehom over A over K from M to N is a map f such that
     (A is an algebra over K)
 and (M,N are modules over A over K)
 and (f is from |M| to |N|)
 and (for all x,y < M             : f(x +{M} y) = f(x) +{N} f(y))
 and (for all a < A and all x < M : f(a @@{M} x) = a @@{N} f(x)).

Axiom. Let A be an algebra over K. Let M,N be modules over A over K.
 |Hom(K,A,M,N)| is the set of maps f such that f is a modulehom over A over K from M to N.

Lemma. Let A be an algebra over K. Let M,N be modules over A over K.
 |Hom(K,A,M,N)| is subset of |Hom(K,M,N)|.
Proof.
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 Let us show that |U| is subset of |V|.
  Let us show that for all f < U : f < V.
   Let f < U.
   f is a map.
   Let us show that f is linear over K from M to N.
    f is from |M| to |N|.
    Let us show that for all x,y < M : f(x +{M} y) = f(x) +{N} f(y).
     Let x,y < M.
     Let us show that f(x +{M} y) = f(x) +{N} f(y).
      f is a modulehom over A over K from M to N.
     qed.
     Therefore the thesis.
    qed.
    Let us show that for all a < K and all x < M : f(a @{M} x) = a @{N} f(x).
     Let a < K and x < M.
     a @{M} x = a @{M} (1{A} @@{M} x).
     a @{M} (1{A} @@{M} x) = (a @{A} 1{A}) @@{M} x (by Module).
     f(a @{M} x) = f((a @{A} 1{A}) @@{M} x).
     Let us show that f((a @{A} 1{A}) @@{M} x) = (a @{A} 1{A}) @@{N} f(x).
      f is a modulehom over A over K from M to N.
      (a @{A} 1{A}) < A.
     qed.
     (a @{A} 1{A}) @@{N} f(x) = a @{N} (1{A} @@{N} f(x)) = a @{N} f(x).
    qed.
   qed.
  qed.
 qed.
Qed.

Lemma. Let A be an algebra over K. Let M,N be modules over A over K. Let f,g < Hom(K,A,M,N).
 Then f +{Hom(K,M,N)} g < Hom(K,A,M,N).
Proof.
 f,g < Hom(K,M,N).
 f,g are maps.
 For all x < M: (f +{Hom(K,M,N)} g is a map and (f +{Hom(K,M,N)} g)(x) = f(x) +{N} g(x)).
 f +{Hom(K,M,N)} g is a map and for all x < M : (f +{Hom(K,M,N)} g)(x) = f(x) +{N} g(x).
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 V is a vector space over K.
 Let us show that f +{V} g < U.
  f and g are maps.
  Let us show that f +{V} g is a modulehom over A over K from M to N.
   f < V. g < V.
   f +{V} g < V (by VectorSpace).
   f +{V} g < Hom(K,M,N).
   f +{V} g is a map.
   f +{V} g is linear over K from M to N.
   For all x,y < M : (f +{V} g)(x +{M} y) = (f +{V} g)(x) +{N} (f +{V} g)(y) (by MapAdd).
   Let us show that for all a < A and all x < M : (f +{V} g)(a @@{M} x) = a @@{N} (f +{V} g)(x).
    Let a < A and x < M.
    (f +{V} g)(a @@{M} x) = f(a @@{M} x) +{N} g(a @@{M} x).
    Let us show that f(a @@{M} x) +{N} g(a @@{M} x) = (a @@{N} f(x)) +{N} (a @@{N} g(x)).
     f is a modulehom over A over K from M to N.
     g is a modulehom over A over K from M to N.
     f(a @@{M} x) = a @@{N} f(x).
     g(a @@{M} x) = a @@{N} g(x).
    qed.
    N is a module over A over K.
    f(x) < N.
    g(x) < N.
    (a @@{N} f(x)) +{N} (a @@{N} g(x)) = a @@{N} (f(x) +{N} g(x)) (by Module).
    a @@{N} (f(x) +{N} g(x)) = a @@{N} (f +{V} g)(x).
   qed.
  qed.
 qed.
Qed.

Lemma. Let A be an algebra over K. Let M,N be modules over A over K. Let f < Hom(K,A,M,N).
 Let a < K.  Then a @{Hom(K,M,N)} f < Hom(K,A,M,N).
Proof.
 f < Hom(K,M,N).
 f is a map.
 For all x < M: (a @{Hom(K,M,N)} f is a map and (a @{Hom(K,M,N)} f)(x) = a @{N} f(x)).
 a @{Hom(K,M,N)} f is a map and for all x < M : (a @{Hom(K,M,N)} f)(x) = a @{N} f(x).
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 V is a vector space over K.
 Let us show that a @{V} f < U.
  f is a map.
  Let us show that a @{V} f is a modulehom over A over K from M to N.
   f < V.
   a @{V} f < V (by VectorSpace).
   a @{V} f < Hom(K,M,N).
   a @{V} f is a map.
   a @{V} f is linear over K from M to N.
   For all x,y < M : (a @{V} f)(x +{M} y) = (a @{V} f)(x) +{N} (a @{V} f)(y) (by MapAdd).
   Let us show that for all b < A and all x < M : (a @{V} f)(b @@{M} x) = b @@{N} (a @{V} f)(x).
    Let b < A and x < M.
    (a @{V} f)(b @@{M} x) = a @{N} f(b @@{M} x).
    Let us show that a @{N} f(b @@{M} x) = a @{N} (b @@{N} f(x)).
     f is a modulehom over A over K from M to N.
     f(b @@{M} x) = b @@{N} f(x).
    qed.
    N is a module over A over K.
    f(x) < N.
    a @{N} (b @@{N} f(x)) = b @@{N} (a @{N} f(x)) (by Module).
    b @@{N} (a @{N} f(x)) = b @@{N} (a @{V} f)(x).
   qed.
  qed.
 qed.
Qed.


Theorem. Let A be an algebra over K. Let M,N be modules over A over K.
 Hom(K,M,N) is a vector space over K and Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
Proof.
 Hom(K,M,N) is a vector space over K.
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 Let us show that U is a subspace of V over K.
  |U| is subset of |V|.
  For all f,g < U             : f +{V} g < U.
  For all a < K and all f < U : a @{V} f < U.
  Let us show that 0{V} < U.
   0{V} < V.
   0{V} is a map linear over K from M to N.
   Let us show that 0{V} is a modulehom over A over K from M to N.
    0{V} is from |M| to |N|.
    For all x,y < M : 0{V}(x +{M} y) = 0{V}(x) +{N} 0{V}(y).
    Let us show that for all a < A and all x < M : 0{V}(a @@{M} x) = a @@{N} 0{V}(x).
     Let a < A and x < M.
     0{V}(a @@{M} x) = 0{N}.
     0{N} = 0{K} @{N} (a @@{N} 0{N}) (by ZeroSmul).
     Let us show that 0{K} @{N} (a @@{N} 0{N}) = a @@{N} (0{K} @{N} 0{N}).
      0{K} < K.
      0{N} < N.
      a < A.
      N is a module over A over K.
      Therefore the thesis (by Module).
     qed.
     a @@{N} (0{K} @{N} 0{N}) = a @@{N} 0{N}.
     a @@{N} 0{N} = a @@{N} 0{V}(x).
    qed.
   qed.
  qed.
 qed.
Qed.


Theorem. Let A be an algebra over K. Let M,N be modules over A over K.
 Hom(K,A,M,N) is a vector space over K.
Proof.
 Hom(K,M,N) is a vector space over K and Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
Qed.
