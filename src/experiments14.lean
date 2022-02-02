#print decidable
#print nat.decidable_le._main
#reduce @nat.decidable_le  3 5
#check nat
#check nat.
#check nat.zero_le 3
#check 0≤ 3

universe u 
def h:= (nat.not_succ_le_zero 4)
#check h
#check nat.not_succ_le_zero 0
#check (λ a, (h (nat.le_of_succ_le_succ a)) 
#print nat.not_succ_le_zero

#check false.elim

def circ {α β γ: Type} (f : β→γ ) (g : α→β) := (λ x, f (g x))

def f  (n : ℕ ) : ℕ := n+1
def g (n : ℕ ) : ℕ := 2*n 

#eval circ g f 3