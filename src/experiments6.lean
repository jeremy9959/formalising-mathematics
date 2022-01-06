import tactic
universes u v w

#reduce inhabited.default  ( ℕ ⊕ ℕ )
#print instances decidable

#check list.nil 
def one_list := list.nil.cons 1

lemma one: one_list = (list.nil.cons 1) := begin
refl, 
end

#print ne

lemma two: ¬(one_list = (one_list.cons 2)) := 
begin
dec_trivial,
end

 #print eq



lemma jtt : ¬ (1=0) :=
begin
  dec_trivial,
end

#reduce decidable.is_false 
#reduce one_list.head

namespace hidden

/-
list is defined in init.core.lean
-/
inductive list (T : Type u)
| nil : list
| cons (hd : T) (tl : list) : list

#check list.nil.is_right_id 

variables (L : list ℕ )

def empty_list {a : Type*} : list a := list.nil
def one_list := list.nil.cons 1

lemma one : one_list = empty_list.cons 1 :=
begin
refl,
end






end hidden
