import algebra.group 

variables (R : Type) [comm_ring R] {a b c d e : R}
variables (G : Type) [group G] 
variables x y z : G

/-
@[ancestor id.{1} (list.{0} name) (Prop div_inv_monoid), class, protect_proj list.nil.{0} name, to_additive to_additive.value_type.mk name.anonymous (option.none.{0} string), to_additive_aux id.{1} name add_group]
structure group : Type u → Type u
fields:
group.mul : Π {G : Type u} [c : group G], G → G → G
group.mul_assoc : ∀ {G : Type u} [c : group G] (a b c_1 : G), a * b * c_1 = a * (b * c_1)
group.one : Π {G : Type u} [c : group G], G
group.one_mul : ∀ {G : Type u} [c : group G] (a : G), 1 * a = a
group.mul_one : ∀ {G : Type u} [c : group G] (a : G), a * 1 = a
group.inv : Π {G : Type u} [c : group G], G → G
group.div : Π {G : Type u} [c : group G], G → G → G
group.div_eq_mul_inv : ∀ {G : Type u} [c : group G],
  auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous)
group.mul_left_inv : ∀ {G : Type u} [c : group G] (a : G), a⁻¹ * a = 1
-/

#print group


/-
@[ancestor id.{1} (list.{0} name) (Prop ring comm_semigroup), class, protect_proj list.nil.{0} name]
structure comm_ring : Type u → Type u
fields:
comm_ring.add : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.add_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
comm_ring.zero : Π {α : Type u} [c : comm_ring α], α
comm_ring.zero_add : ∀ {α : Type u} [c : comm_ring α] (a : α), 0 + a = a
comm_ring.add_zero : ∀ {α : Type u} [c : comm_ring α] (a : α), a + 0 = a
comm_ring.neg : Π {α : Type u} [c : comm_ring α], α → α
comm_ring.sub : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.sub_eq_add_neg : ∀ {α : Type u} [c : comm_ring α],
  auto_param (∀ (a b : α), a - b = a + -b) (name.mk_string "try_refl_tac" name.anonymous)
comm_ring.add_left_neg : ∀ {α : Type u} [c : comm_ring α] (a : α), -a + a = 0
comm_ring.add_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a + b = b + a
comm_ring.mul : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.mul_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
comm_ring.one : Π {α : Type u} [c : comm_ring α], α
comm_ring.one_mul : ∀ {α : Type u} [c : comm_ring α] (a : α), 1 * a = a
comm_ring.mul_one : ∀ {α : Type u} [c : comm_ring α] (a : α), a * 1 = a
comm_ring.left_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * (b + c_1) = a * b + a * c_1
comm_ring.right_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), (a + b) * c_1 = a * c_1 + b * c_1
comm_ring.mul_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a * b = b * a
-/

#print comm_ring
#check comm_ring.add_left_neg comm_ring.one

example : ∀ a : R, comm_ring.mul comm_ring.zero a = comm_ring.zero := 
begin
intro a,
have H := comm_ring.add_left_neg comm_ring.one,


end











