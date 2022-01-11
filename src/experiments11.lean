import tactic

#check @nat.rec (λ x, Prop)
#print nat

#print and
#check @and.rec  

variables (P Q : Prop)
variables hP : P
variables hQ : Q

#print and.intro

#check  (@and.intro P Q) 

theorem jt : P → Q → P∧ Q :=
(@and.intro P Q) 


#check prod ℕ ℕ 
#check prod.mk 2 3

#check @and P Q
#check @and.right
#reduce @and.left P Q (@and.intro P Q hP hQ)

#reduce @nat.rec_on (λ S , list ℕ  ) 5 [0] (λ n m, nat.succ n :: m)
/-
inductive nat : Type
constructors:
nat.zero : ℕ
nat.succ : ℕ → ℕ
-/

#print nat
/-
@[_ext_core id.{1} name list.ext]
inductive list : Type u → Type u
constructors:
list.nil : Π {T : Type u}, list T
list.cons : Π {T : Type u}, T → list T → list T
-/

#print list

def r (k : ℕ ) : list ℕ :=  nat.rec_on k [] (λ n m, n :: m)
/-
list.rec_on :
  Π {T : Type u_2} {C : list T → Sort u_1} (n : list T),
    C list.nil → (Π (hd : T) (tl : list T), C tl → C (hd :: tl)) → C n
-/
#reduce @nat.rec_on (λ S, list ℕ ) 2 []
#reduce @list.rec_on ℕ (λ S,  ℕ ) [1,2,3,4,11] 0 (λ a b c, c+a)
#reduce @list.rec_on ℕ (λ S, list ℕ ) [6,1,2,3,4,2] [] (λ a b c, c++[a])


#eval r 0

#check λ (n : ℕ ) (m : list ℕ ), n 


#check (Π (n : ℕ) , ℕ → ℕ )
#check (λ (n  m : ℕ), n)
#check (λ (S: ℕ ), ℕ )

#check nat.decidable_le
#check (λ a b, nat.decidable_le a b) 

#reduce @list.decidable_pairwise ℕ nat.lt nat.decidable_lt  [5,1,2,3] 
 
#check (λ (a b :ℕ ), decidable (a≤ b))
#eval list.split_on_p (λ n, n≤ 3) [1,2,3,4,5]  

universe u 
theorem jt2 {α : Type u} (a : α) (l : list α) : a::l ≠ list.nil :=
begin
   show_term{apply list.no_confusion,}
end

#check @list.no_confusion
/-
list.no_confusion_type : Π {T : Type u_2}, Sort u_1 → list T → list T → Sort u_1
-/

/-
inductive eq : Π {α : Sort u}, α → α → Prop
constructors:
eq.refl : ∀ {α : Sort u} (a : α), a = a
-/

/-
protected eliminator eq.rec : Π {α : Sort u} {a : α} {C : α → Sort l}, C a → Π {ᾰ : α}, a = ᾰ → C ᾰ
-/

#print eq.rec




#print list.no_confusion
