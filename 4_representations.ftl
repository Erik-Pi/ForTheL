[read representations/3_representations_axioms.ftl]

Let K denote a field.

[synonym object/-s] [synonym morphism/-s] [synonym category/categories] [synonym functor/-s]

# 1.5 categories and functors

Signature. A precategory is a notion.
Let C denote a precategory.

Signature. Ob{C} is a set.
Definition. An object in C is an element of Ob{C}.

Signature. Let X,Y be objects. C(X,Y) is a set.    # These objects are not the ones defined above.
Definition. Let X,Y << Ob{C}. A morphism from X to Y in C is an element of C(X,Y).

Signature. Let X be an object. 1{X,C} is an object.

Definition. A category is a precategory C such that 
     (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : g*f << C(X,Z))
 and (for all X << Ob{C} : 1{X,C} << C(X,X))
 and (for all X,Y << Ob{C} and all f << C(X,Y) : f*1{X,C} = f)
 and (for all X,Y << Ob{C} and all f << C(Y,X) : 1{X,C}*f = f)
 and (for all W,X,Y,Z << Ob{C} and all f << C(W,X) and all g << C(X,Y) and all h << C(Y,Z) : 
      h*(g*f) = (h*g)*f).

Definition. Let C and D be categories. A functor from C to D is a map F such that
     (for all X << Ob{C} : F(X) << Ob{D})
 and (for all X,Y << Ob{C} and all f << C(X,Y) : F(f) << D(F(X),F(Y)))
 and (for all X << Ob{C} : F(1{X,C}) = 1{F(X),D})
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : F(g*f) = F(g)*F(f)).

Signature. id is a map.
Axiom. Let x be an object. id(x) = x.

Theorem. Let C be a category. id is a functor from C to C.
Proof.
 for all X << Ob{C} : id(X) << Ob{C}.
 for all X,Y << Ob{C} and all f << C(X,Y) : id(f) << C(id(X),id(Y)).
 for all X << Ob{C} : id(1{X,C}) = 1{id(X),C}.
 for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : id(g*f) = id(g)*id(f).
Qed.

Definition. Let C and D be categories. Let F and G be functors from C to D.
 A natural transformation from F to G over C to D is a map n such that
     (for all X << Ob{C} : n(X) << D(F(X),G(X)))
 and (for all X,Y << Ob{C} and all h << C(X,Y) : G(h)*n(X) = n(Y)*F(h)).


# 1.6 module categories

Signature. Let A be an algebra over K. Mod(K,A) is a precategory.
Axiom. Let A be an algebra over K. Ob{Mod(K,A)} = {M | M is a module over A over K}.
Axiom. Let A be an algebra over K. Let M,N << Ob{Mod(K,A)}. Let M,N be modules over A over K.
 Mod(K,A)(M,N) = |Hom(K,A,M,N)|.
Axiom. Let A be an algebra over K. Let M << Ob{Mod(K,A)}. Let M be a structure.
 1{M,Mod(K,A)} = id{|M|}.

Theorem. Let A be an algebra over K. Mod(K,A) is a category.
Proof.
 Take a precategory C such that C = Mod(K,A).
 Let us show that for all L,M,N << Ob{C} and all f << C(L,M) and all g << C(M,N) : g*f << C(L,N).
  Let L,M,N << Ob{C} and f << C(L,M) and g << C(M,N).
  L,M,N are modules over A over K.
  f is a modulehom over A over K from L to M.
  g is a modulehom over A over K from M to N.
  Let us show that g*f is a modulehom over A over K from L to N.
   f is from |L| to |M|.
   g is from |M| to |N|.
   f*g is a map from |L| to |N| (by CompFromTo).
  qed.
 qed.
 For all M << Ob{C} : 1{M,C} << C(M,M).
 For all M,N << Ob{C} and all f << C(M,N) : f*1{M,C} = f.
 For all M,N << Ob{C} and all f << C(N,M) : 1{M,C}*f = f.
 For all L,M,N,O << Ob{C} and all f << C(L,M) and all g << C(M,N) and all h << C(N,O) :
      h*(g*f) = (h*g)*f.
Qed.

# 1.7 Hom functors




# 1.n quivers

#(synonym vertex/vertices) (synonym arrow/-s)

#Signature. 0 is an object.
#Signature. 1 is an object.
#Signature. s is an object.
#Signature. t is an object.

#Definition. A quiver is a map Q such that
#     (Q(0) is a set)
# and (Q(1) is a set)
# and (Q(s) is a map from Q(1) to Q(0))
# and (Q(t) is a map from Q(1) to Q(0)).

#Let Q denote a quiver.

#Lemma. Q(0) is a set.
#Lemma. Q(1) is a set.

#Definition. A vertex of Q is an element of Q(0).

#Definition. An arrow of Q is an element of Q(1).

#Definition. Let a be an arrow of Q. Let i be a vertex of Q. a starts in i in Q iff Q(s)(a) = i.

#Definition. Let a be an arrow of Q. Let i be a vertex of Q. a ends in i in Q iff Q(t)(a) = i.