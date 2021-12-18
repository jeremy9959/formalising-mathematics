universe u 

inductive jtnat : Type
| zero : jtnat
| succ : Π (a: jtnat), jtnat 

#print jtnat.succ
#print jtnat.zero

/-
protected eliminator
 jtnat.rec : Π {C : jtnat → Sort l},
   C jtnat.zero → 
   (Π (a : jtnat), C a → C a.succ) → 
   Π (n : jtnat), C n
-/

#reduce @jtnat.rec (λ S, ℕ ) 0 (λ a b, b+1) (jtnat.succ jtnat.zero)

/-
protected eliminator list.rec :
 Π {T : Type u} {C : list T → Sort l},
  C list.nil → (Π (hd : T) (tl : list T), C tl → C (hd :: tl)) → Π (n : list T), C n
-/

#print list.rec

#reduce @list.rec ℕ (λ S, list ℕ ) [] (λ hd tl x, x++[hd]) [1,2,3] 

variable X : Type

inductive jteq {α : Type} (a : α) :  α → Prop 
| refl : jteq a
 
variable a : X
#check  (@jteq.rec X a)
/-
protected eliminator jteq.rec :
 Π {α : Type} {a : α} {C : α → Sort l},
  C a → Π {b : α}, jteq a b → C b
-/
-- C a -> (for all b, a=b -> Cb) 

lemma jteq.subst {α : Type} {P : α → Prop}  (a b : α) (h₁ : jteq a b) (h₂ : P a) : P b:=
@jteq.rec α a  P h₂ b h₁ 





#reduce jteq.rec 