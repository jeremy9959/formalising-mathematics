variables (α : Type*) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
assume h : ∀ (x : α), p x ∧ q x,
assume y : α,
show p y, from (h y).left


def f (a b : ℕ ) : ℕ → ℕ := λ c, a+b+c

#eval f 2 3 5

#check bool

#check sum

variables (x y : ℕ )

example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
  -- case hp : p
  right, exact hp,
  -- case hq : q
  left, exact hq
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor,
  left,
  assumption,
end

example (p q : ℕ → Prop) :
  (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
begin
  intro h,
  cases h with x hpq,
  cases hpq with hp hq,
  constructor,
  constructor,
  assumption,
  assumption,
end

def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
begin
  intro p,
  cases p with hp hq,
  split,
  exact hq,
  exact hp,
end

open nat

example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) :
  P m :=
begin
  cases m,
  exact h₀,
  exact h₁ m,
end