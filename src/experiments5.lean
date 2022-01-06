import tactic 
import data.list.sort
import init.data.nat 
import data.list.pairwise


open list


def  r  : ℕ → ℕ → Prop  :=
λ (a : ℕ), λ (b : ℕ), nat.lt b a 

#check sorted nat.le [3,2,1]
#check r 
#check nat.le

#check 3 ≤ 5

example : r 5 3 :=
begin
  rw r,
apply nat.succ_lt_succ,
apply nat.succ_lt_succ,
apply nat.succ_lt_succ,
apply nat.zero_lt_succ,
end


example : list.pairwise nat.le [0,1,2,3] :=
begin
  rw list.pairwise_iff,
  right,
  use 0,
  use 1::[2,3],
  split,
  intro x,
  intro x1,
  cases x1 with h1 h2 h3,
  rw h1,
  apply nat.le_succ,
  cases h2,
  rw h2,
  apply nat.le_succ_of_le,
  apply nat.le_succ,
  cases h2 with h3,
  rw h3,
  apply nat.le_succ_of_le,
  apply nat.le_succ_of_le,
  apply nat.le_succ,
  cases h2,
  rw list.pairwise_iff,
  split,
  right,
  use 1,
  use 2::[3],
  split,
  intro a,
  intro b,
  cases b with u1 u2, 
  rw u1,
  apply nat.le_succ,
  cases u2,
  rw u2,
  apply nat.le_succ_of_le,
  apply nat.le_succ,
  cases u2,
  split,
  rw list.pairwise_iff,
  right,
  use 2,
  use 3::[],
  split,
  intro z,
  intro z1,
  cases z1,
  rw z1,
  apply nat.le_succ_of_le,
  refl,
  cases z1,
  rw list.pairwise_iff,
  split,
  right,
  use 3,
  use nil,
  split,
  intro,
  intro,
  cases H,
  rw list.pairwise_iff,
  split,
  left,
  refl,
  refl,
  refl,
  refl,
  refl,
end




#check f

#eval f 2 4

#print is_true

variable (P : Prop) 

#check P ∨ (P → false) 

#check nat.decidable_le 

#eval if 5 ≤ 3 then tt else ff


#check ff 

open nat

def step (a b x : ℕ) : ℕ :=
if x < a ∨ x > b then 0 else 1

set_option pp.implicit true
#print  definition step

variables (x a b : ℕ )

#check  if x<a ∨ x>b then tt else ff 

#check @or.decidable