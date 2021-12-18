universe u
variable X : Type
variable a : X

inductive jteq {α : Sort u} (a : α) : α → Prop
| refl : jteq a

#print jteq.rec

#check @jteq.refl (list ℕ) 


inductive jteq2 {α : Sort u} : α→ α→ Prop 
| refl : ∀ a : α, jteq2 a a 

#check @jteq2.refl (list ℕ)

def r2 {α : Sort u} (a b : α): Prop := jteq2 b a

example : @r2 (list ℕ ) [1,2] [1,2] := 
begin
  apply jteq2.refl [1,2],
end

lemma r2refl : r2 a a := 
begin
  apply jteq2.refl a,
end

#check r2refl

#print jteq2.rec

lemma jteq2symm {α : Type} (a b : α) (h : jteq2 a b): r2 a b :=
 ((@jteq2.rec α r2 (r2refl α)) a b) h

 lemma jteq2subs {α : Type} (a b : α) (P : α → Prop) (h : jteq2 a b) (h2 : P a) : jteq2 (P a) (P b):=
 begin
   have hk2 := @jteq2.rec α _,
 end



lemma jteq2symm2 {α : Type} (a b : α) (h : jteq2 a b) : jteq2 b a :=
begin
  have hk := @jteq2symm α,
  have h3 := hk a b h,
  exact h3,
end

#check @jteq2.refl (list ℕ )




