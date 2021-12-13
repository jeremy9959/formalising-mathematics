<<<<<<< HEAD



variables p q r : Prop

constant Proof : Prop -> Type 

constant and_comm : Π p q : Prop, Proof (implies (and p q) (and q p))

#check and_comm p q 

#check Proof p 









theorem t1 : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp
=======
variables  p q r s : Prop 
variable x : p
variable y : q

theorem t1  (hp : p) (hq : q) : p := hp 

theorem t₂ (h₁ : q → r) (h₂ : p→ q) : p → r :=
assume h₃,
show r, from h₁ (h₂ h₃)


example (h : p ∧ q) : q ∧ p :=⟨ h.right, h.left ⟩


theorem t₄ (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)

#check t₄


 
example : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h: p ∧ q,
    show q ∧ p, from (⟨ h.right, h.left ⟩ : q∧ p))
  (assume h: q ∧ p,
    show p∧ q, from (⟨ h.right, h.left⟩ : p∧ q))


example : (p → q → r) ↔ (p ∧ q → r) := 
iff.intro
  (λ hpqr : p → q → r, λ hpaq : p ∧ q, hpqr hpaq.left hpaq.right)
  (λ hpqr  : p ∧ q → r, λ hp : p, λ hq :  q, hpqr ⟨ hp, hq ⟩)
        

theorem t₇ : (p ∧ ¬ q) → ¬ (p → q) :=
  λ hpanq : p ∧ ¬ q,
  λ hpq : p→ q,
  hpanq.right (hpq hpanq.left)
    
open classical
>>>>>>> f5ce07d97373c97b23b05da322cc073b9d351772
