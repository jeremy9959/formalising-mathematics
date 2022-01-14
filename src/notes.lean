
/- These are some notes on confusing things in lean. 
First, we set some options to illuminate implicit arguments.
-/


set_option pp.implicit true
set_option pp.notation false 

/-
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
-- jteq.rec : Π {α : Sort u_2} {a : α} {C : α → Sort u_1}, C a → Π {ᾰ : α}, @jteq a ᾰ → C ᾰ
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

def jtr {α : Sort u} (a b : α) := λ (a b : α), jteq b a

theorem jteq.subst : ∀ (α : Sort u) {r s : α} (P : α → Prop), @jteq α r s → P r → P s :=
λ (α : Sort u) (r s : α) (P : α→ Prop) (h₁ : @jteq α r s) (h₂ : P r), @jteq.rec α r P h₂ s h₁ 


/- Amazingly this is sufficient to show that jteq is symmetric and transitive.
-/

theorem jteq.symm {α : Sort u} {a b : α} (h : jteq a b) : jteq b a  :=
@jteq.subst α a b (λ x, jteq x a) h (@jteq.refl α a) 


/- 
To decode this proof, notice that our predicate is jteq _ a, so P a  is jteq a a  and P b is jteq b a
So P a is true by reflexivity and P a with a=b → P b  which is b=a.

**Interestingly the proof is simpler with implicit arguments (as in the core library) because somehow
lean figures out which predicate to use**
-/


/- 
For transitivity, here is a proof. 
 
Our strategy is:
Let  be the predicate P(x) : x=c
P(b) : true by h₂
b=a : true by symm of h₁ (@jteq.symm α a b h₁)
P(b) and b=a implies P(a) which is a=c. Notice that r=b and s = a in this case, so the full proof is:
  @jteq.subst α b a (λ x, @jteq α x c) (@jteq.symm α a b h₁) (h₂)
                r s  P                  b=a                   P(b)  -> P(a) which is a=c

Our predicate is (λ x, jteq x c) 

It takes some thought to see why b and a are switched in the call to @jteq.subst. 
-/

theorem jteq.trans : ∀ {α : Sort u} (a b c : α), @jteq α a b → @jteq α b c  → @jteq α a c:=
λ (α : Sort u) (a b c : α) (h₁ : @jteq α a b) (h₂ : @jteq α b c), @jteq.subst α b a (λ x, @jteq α x c) (@jteq.symm α a b h₁) (h₂)

/- 
Just to illustrate the mystery of implicit arguments, here is the same code from
the core.init file of mathlib.  Notice that the arguments are treated as implicit.
The MOST mysterious part is how does this infer the correct predicate?  (We had to manually construct the predicate
as λ x, jteq x a because we needed the variable on the left of the equality sometimes.

The key seems to be this elab_as_eliminator attribute on subst. This is discussed in Section 6.10 of TPIL
in precisely this context, where the problem is figuring out a predicate for use in eq.subst.  However, no
explanation is given as to how this particular attribute helps in this situation.

Nevertheless we can see that symm infers the correct predicate Q(x) : x=a.

-/


namespace hidden

inductive eq2 {α : Sort u} (a : α) : α → Prop
| refl [] : eq2 a

@[pattern] def rfl {α : Sort u} {a : α} : eq2 a a := eq2.refl a

@[elab_as_eliminator, subst]
lemma eq2.subst {α : Sort u} {P : α → Prop} {a b : α} (h₁ : eq2 a b) (h₂ : P a) : P b :=
eq2.rec h₂ h₁

@[symm] lemma eq2.symm {α : Sort u} {a b : α} (h : eq2 a b) : eq2 b a :=
eq2.subst h rfl 

variables (h : eq2 a b)



#reduce eq2.symm h

-- @eq2.rec α a (λ (_x : α), @eq2 α _x a) (@eq2.refl α a) b h

/-
Note that the predicate is as claimed. 
-/

end hidden
/- 

To beat this horse completely dead, remove that attribute and look at the code again. 


-/

namespace hidden2

inductive eq2 {α : Sort u} (a : α) : α → Prop
| refl [] : eq2 a

@[pattern] def rfl {α : Sort u} {a : α} : eq2 a a := eq2.refl a

@[subst]
lemma eq2.subst {α : Sort u} {P : α → Prop} {a b : α} (h₁ : eq2 a b) (h₂ : P a) : P b :=
eq2.rec h₂ h₁

@[symm] lemma eq2.symm {α : Sort u} {a b : α} (h : eq2 a b) : eq2 b a :=
eq2.subst h rfl 
/-
The error for symm in this case is the following:

type mismatch at application
  h.subst
term
  h
has type
  @eq2 α a b
but is expected to have type
  @eq2 α ?m_1 a

In other words, the inferred predicate has the arguments reversed.....and we can see this by looking at 
the reduction
-/

variables (h : eq2 a b)

#reduce eq2.subst h rfl

/-
@eq2.rec α a (λ (_x : α), @eq2 α a _x) (@eq2.refl α a) b h
 
The predicate that was inferred is P(x) : a=x. 
-/

end hidden2

