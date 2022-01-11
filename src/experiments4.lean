import tactic.ring
import data.nat.gcd
import data.nat.basic
import tactic.ring 

example (p : Prop) : ¬ (p ↔ ¬ p) :=
  begin
    rintro ⟨ h1, h2 ⟩, 
    apply h1,          
      {apply h2,intro xp,exact h1 xp xp}, 
      {apply h2,intro xp,exact h1 xp xp }, 
  end

example (p : Prop) : ¬ (p ↔ ¬ p) :=
λ ⟨ h1, h2 ⟩, h1 (h2 (λ xp, h1 xp xp)) (h2 (λ xp, h1 xp xp))

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ :=
λ h1, λ h2, f (prod.mk h1 h2)

variables p q r : Prop

lemma p_or_q_implies_r_implies_p_implies_r : (p ∨ q → r) → (p → r) :=
(λ h, (λ hp,  h (or.inl hp)))

def sum_example (s : ℕ ⊕ ℕ) : ℕ :=
sum.cases_on s (λ n, 2 * n) (λ n, 2 * n + 1)






#reduce sum_example (sum.inl 3)
#reduce sum_example (sum.inr 3)

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday 
| friday : weekday 
| saturday : weekday


open weekday

def next (d : weekday) : weekday :=
weekday.cases_on d monday tuesday wednesday thursday friday
  saturday sunday

def previous (d : weekday) : weekday :=
weekday.cases_on d saturday sunday monday tuesday wednesday
  thursday friday

#reduce next ( previous friday)
/-
theorem next_previous (d : weekday) : next(previous d) = d :=
begin
cases d,
end

def weekday.nd ( d: weekday ) : ℕ := weekday.cases_on d 1 2 3 4 5 6 7
-/



#reduce nd ( friday)

#check thursday 
#check weekday.nd

constant a : option ℕ 
#check a 


#print option 

def f (x : option ℕ) : ℕ  := 
option.cases_on x 0 1





#check [2,1,0] 


def L := (1 :: 0 :: list.nil) 

#check list.mem 0 [0,1,2]



lemma mine : 0 ∈ [0,1,2] := 
begin
  show_term { left},
  refl,
end

#print mine

#print list.mem 
#print list.mem._main 

#print list 
def jtfun { α : Type* }: list α → option α
| [] := none
| (b :: l) := some b 

def tail { α : Type*} : list α → list α
| [] := []
| (a :: t) := t



def jtmain : Π {α : Type*}, list α → list α :=
λ {α : Type*} (l : list α),
  l.cases_on (id_rhs (list α) list.nil) (λ (ᾰ_hd : α) (ᾰ_tl : list α), id_rhs (list α) ᾰ_tl)

def tail1 : Π {α : Type*}, list α → list α :=
λ {α : Type*}, jtmain 


#print tail




#print tail._main


/-
def tail1._main : Π {α : Type _aux_param_0}, list α → list α :=
λ {α : Type _aux_param_0} (ᾰ : list α),
  ᾰ.cases_on (id_rhs (list α) list.nil) (λ (ᾰ_hd : α) (ᾰ_tl : list α), id_rhs (list α) ᾰ_tl)
-/
/-
@[_ext_core id.{1} name list.ext]
inductive list : Type u → Type u
constructors:
list.nil : Π {T : Type u}, list T
list.cons : Π {T : Type u}, T → list T → list T
-/

#print list
#print tail1


def tailfancy {α : Type*} : list α → list α :=
λ {α : Type*} (l : list α), l.cases_on  list.nil (λ (hd : α) (tl : list α), id_rhs (list α) tl)

/-
@[inline, reducible]
def id_rhs : Π (α : Sort u), α → α :=
λ (α : Sort u) (a : α), a
-/

#reduce id_rhs (list ℤ) list.nil





#print jtfun._main

example : jtfun [0,1,2] = some 0 :=
begin
  refl,
end

#eval jtfun [2,1,0]

#eval jtfun L 
#check jtfun 


#print list


#check list.mem

def sub2 : ℕ → ℕ 
| 0 := 0
| 1 := 0
| (a+2) := a

#print sub2
#print sub2._main
#eval id_rhs (list ℕ ) list.nil

namespace hidden
universe u

inductive vector (α : Type u) : nat → Type u
| nil {} : vector 0
| cons   : Π {n}, α → vector n → vector (n+1)

#print vector
namespace vector 
local notation h :: t := cons h t

variables {v : vector ℕ 3}

#check @vector.cases_on 
-- Π {α : Type*}
--   {C : Π (a : ℕ), vector α a → Type*}
--   {a : ℕ}
--   (n : vector α a),
--   (e1 : C 0 nil)
--   (e2 : Π {n : ℕ} (a : α) (a_1 : vector α n),
--           C (n + 1) (cons a a_1)),
--   C a n

end vector
end hidden

def mylen : list ℕ →  ℕ 
| [] := 0
| (a::t) := nat.succ (mylen t)

def myfib : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (k+2) := (myfib k) + (myfib (k+1))

lemma myfib_zero : myfib 0 = 0 := rfl
lemma myfib_one : myfib 1 = 1 := rfl
lemma myfib_two : myfib 2 = 1 := rfl
lemma myfib_three : myfib 3 = 2 := rfl
lemma myfib_four : myfib 4 = 3 := rfl

lemma myfib2 {n : ℕ } : myfib(n+2) = myfib(n+1) + myfib(n) :=
begin
  rw myfib,
  have h := add_comm (myfib n) (myfib (nat.succ n)),
  exact h,
end



