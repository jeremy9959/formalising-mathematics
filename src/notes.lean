/- These are some notes on confusing things in lean. 

Let's look at equality first.  Here is a (renamed) version of the definition of equality.

-/
universe u

inductive jteq {α : Sort u} (a : α): α → Prop 
| refl : jteq  a

/-
The type α → Prop means that jteq is a predicate; but it's a predicate that depends on
fixing a type α and a term a with that type.  

The way to think of it is that jteq a is the predicate P where P(b) means a=b.

To decode this declaration, look at 4.5 of the reference manual.  The construction α → Prop
is equivalent to Π (a : α), Sort 0
-/
variable (α : Sort u)
variables (a b : α)

#check Π (a:α), Sort 0
-- α → Prop : Sort (max u 1)

/-
So here is the check that jteq a is a predicate:
-/

#check jteq a 
-- jteq a : α → Prop


/- Often it helps to figure out what's going on if you make all arguments explicit. 
-/

#check @jteq α  a
--jteq a : α → Prop

/- We have a single constructor, jteq.refl a
In the language of 4.5 of the reference manual, the constructor jteq.refl *first* takes
the arguments to the type former, which is jteq, and then inserts the given value from the definition.

It constructs a *term* whose type is the type former. 

In our case this means that jteq.refl a is a term whose type is jteq a a.
-/
#check @jteq.refl α a 
-- jteq.refl : jteq a a




/- 
In the language of propositions as types and proofs as terms, this means we have a *proof* of the proposition
that jteq a a for any type α and any a of that type. This is a sort of universal reflexivity.
-/


/- Creation of a type also creates a recursion function.  In our case it is jteq.rec. 
-/

#check @jteq.rec
-- jteq.rec : Π {α : Sort u_2} {a : α} {C : α → Sort u_1}, C a → Π {ᾰ : α}, jteq a ᾰ → C ᾰ
/- 
This takes as arguments a type α, a term a of that type, and a function that takes terms of type α
to a (potentially) different type.

We also need to decode the portion that says:
C a → Π (b : α), jteq a b → C b

Remember that Π (b : α) has very low priority to this parses as:
C a → (Π (b : α ), (jteq a b → C b))

So: (a : α) and a function C: α → Sort u_1, if we know C a then, for any b of type α, if we know jteq a b
we can conclude C b.

In the special case where C: α → Prop is a predicate, this says:
* if we know C a
* then, for all b of type α, if jteq a b (i.e. if a=b) then we know C b.

We can put this in the form of a theorem, following Buzzard's blog post on induction on equality. 
-/

def jtr {α : Sort u} (a b : α) := jteq b a

theorem jteq.subst {α : Sort u} {r s: α} (P : α → Prop) (h₁ : jteq r s) (h₂ : P r) : P s :=
@jteq.rec α r P h₂ s h₁

/- Amazingly this is sufficient to show that jteq is symmetric and transitive.
-/

theorem jteq.symm {α : Sort u} {a b : α} (h : jteq a b) : jteq b a  :=
@jteq.subst α a b (λ b, jteq b a) h (@jteq.refl α a) 


/- 
To decode this proof, notice that our predicate is jteq _ a, so P a  is jteq a a  and P b is jteq b a
So P a is true by reflexivity and P a with a=b → P b  which is b=a.

**Interestingly the proof is simpler with implicit arguments (as in the core library) because somehow
lean figures out which predicate to use**
-/


/- 
For transitivity, here is a proof. 
 
Our strategy is:
P(x) : x=c
P(b) : true by h₂
b=a : true by symm of h₁
P(b) and b=a implies P(a) which is a=c.

Our predicate is (λ x, jteq x c) 
In jteq.subst, the hypothesis h₁ has type jteq r s, and the arguments are given in the order r s.
We want jteq b a, so we switch h₁, and then we need to switch the order of the arguments in the call. 
-/

theorem jteq.trans {α : Sort u} (a b c :α) (h₁ : jteq a b) (h₂ : jteq b c) : jteq a c:=
@jteq.subst α b a (λ x, jteq x c) (@jteq.symm α a b h₁) (h₂)





inductive jteq2 {α : Sort u} : α → α → Prop 
| refl (a : α) : jteq2 a a 


