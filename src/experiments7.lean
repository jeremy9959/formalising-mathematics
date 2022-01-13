import tactic
import data.nat.basic
import data.list.sort
universes u v

inductive my2 (α : Type u)
| mk : α → punit  → my2

#check my2.mk ℕ punit.star 

def myf {α : Type u} (k : my2 α) : α :=
my2.rec_on k (λ a s, a)

variable (x : my2 ℕ)
variable (j : ℕ → ℕ )
#reduce myf (my2.mk j punit.star)as
#check myf x 



inductive myprod (α : Type u) (β : Type v)
| mk: α → β → myprod

#check myprod.mk ℕ ℕ 


def mytype := Π (C : Type), C → punit → C 

variable ( x: mytype )
 
def f : ℕ → punit → ℕ  := λ n, λ u, n

#reduce f 3 punit.star 

#reduce is_left_id ℕ (+) 0

example : is_left_id ℕ (+) 0 :=
  ⟨ nat.zero_add ⟩  



variable (α : Type) 
#check is_left_id (list α) has_append.append [] 
#check nat.zero_add 
#check mt 
#print instances is_left_id
#print instances has_append


-- example (a : α) (l : list α) : a::l ≠ l :=
-- mt (congr_arg length) (nat.succ_ne_self _)

#print list.nil_append
#check  is_left_id.mk list.nil_append
#check (is_left_id.mk (@list.nil_append ℕ )).left_id 

def t := is_left_id ℕ (+) 0
#check t

def s:= is_left_id.mk nat.zero_add
#check s 

def z := [0,1,2]



example : ∀ (x: ℕ), [] ++ [0,1,x] = [0,1,x]:=
begin
  intro x,
  apply is_left_id.left_id _,
  exact is_left_id.mk list.nil_append,
end

example : ∀ (x: ℕ), [] ++ [0,1,x] = [0,1,x]:= λ x, rfl



#reduce list.insertion_sort nat.le [12, 13, 11]

