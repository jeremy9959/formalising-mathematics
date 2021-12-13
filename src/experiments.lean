


variables p q r : Prop

constant Proof : Prop -> Type 

constant and_comm : Π p q : Prop, Proof (implies (and p q) (and q p))

#check and_comm p q 

#check Proof p 









theorem t1 : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp
