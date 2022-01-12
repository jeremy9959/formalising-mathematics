universe u
inductive jteq {α : Sort u} (a : α) : α → Prop
| refl : jteq a

#check @jteq ℕ (3)