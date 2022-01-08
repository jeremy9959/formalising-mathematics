import tactic
variables  p q r s : Prop 
variable x : p
variable y : q

theorem t1  (hp : p) (hq : q) : p := hp 

theorem t₂ (h₁ : q → r) (h₂ : p→ q) : p → r :=
assume h₃,
show r, from h₁ (h₂ h₃)


example (h : p ∧ q) : q ∧ p :=⟨ h.right, h.left ⟩


theorem t₄ (h : p ∨ q) : q ∨ p :=
h.elim
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)





 
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



example :  (p ∧ q) → q :=
assume hpq,
  show q, from and.right hpq


    
example : ((p ∨ q) ∧ ¬ q) → p :=
assume hpqnq,
  or.elim hpqnq.left
    (assume hp, show p, from hp)
    (assume hq, 
     show p, from false.elim ((hpqnq.right) hq))

   
theorem t₈ : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) :=
begin
intro hpqr,
by_cases hp : p,
{ cases hpqr hp,
{ left, intro, assumption },
{ right, intro, assumption } },
{ left, intro, contradiction },
end 

theorem t₉  : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) :=
begin
intro hpqr,
by_cases hp : p,
  cases hpqr hp,
  left, intro, assumption,
  right, intro, assumption,
left, intro, contradiction,
end


example : ¬ p → (p → q) :=
begin
intro hnp,
intro hp,
exact (hnp hp).elim,
end

theorem t₁₀ : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) :=
assume hpqr,
by_cases
  (assume hp: p, or.elim (hpqr hp)
    (assume hq : q,  or.intro_left (p→ r) (assume hp : p, hq))
    (assume hr : r,  or.intro_right (p→ q) (assume hp : p, hr))
  )
  (assume hnp : ¬ p,  
   or.intro_right (p→ q)(assume hp : p, absurd hp hnp)
  )

theorem t₁₁ : ((p→ q) ∨ (p → r)) → (p → (q ∨ r)) :=
begin
  intro hpqpr,
  cases hpqpr with hpq hpr,
    {intro hp,
    have hq := hpq hp,
    left,
    assumption},
    {intro hp,
    have hr := hpr hp,
    right,
    assumption
    },
end


theorem t₁₂ : ((p → q) ∨ (p → r)) → (p → (q ∨ r)) :=
assume hpqpr,
hpqpr.elim
  (assume hpq : p→ q,  (assume hp : p,  or.intro_left r (hpq hp)))
  (assume hpr : p→ r,  (assume hp : p, or.intro_right q (hpr hp)))


theorem t₁₃ : ((p → q) ∨ (p → r)) ↔ (p → (q ∨ r)) :=
iff.intro
  (t₁₁ p q r)
  (t₁₀ p q r)

theorem t₁₄  (a b c : nat) (hab : a=b) (hbc : b=c) : a=c :=
begin
  rw hbc at hab,
  assumption,
end

theorem t₁₅ (A B C : Prop) : ¬ (A ∨ B) → ((¬ A) ∧ (¬ B)):=
begin
  intro hnAB,
  split,
  intro hnA,
  apply hnAB,
  left,
  exact hnA,
  intro hnB,
  apply hnAB,
  right,
  exact hnB,
end

/- 
Suppose you have a proof that A ∨ B implies false.  Now suppose A is true.
Then A ∨ B is true, so if you apply your proof you conclude false from A. 
Similarly suppose B is true; then A ∨ B is true, so you conclude false from B.
Thus given a proof that A∨ B implies false, you get proofs that A → false and B → false. 
-/
theorem t₁₆ (A B C : Prop) : ¬ (A ∨ B) → ((¬ A) ∧ (¬ B)):=
λ hnAB ,  and.intro (λ hA,  hnAB (or.inl hA)) (λ hB, hnAB (or.inr hB)) 

  

  
variables (A B C : Prop)
