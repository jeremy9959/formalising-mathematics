variables (α : Type*) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
assume h : ∀ (x : α), p x ∧ q x,
assume y : α,
show p y, from (h y).left


example (α : Type*) : α → α :=
begin
  intro a,
  exact a
end

example (α : Type*) : ∀ x : α, x = x :=
begin
  intro x,
  exact eq.refl x,
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros a b c hab hac,
  transitivity a,
  symmetry,
  assumption,
  assumption,
end

example  (a : ℕ) : a = a :=
begin
  revert a,
  intro y,
  reflexivity,
end

example : 2 + 3 = 5 :=
begin
  generalize h : 3 = x,
  --revert x,
  rw ←h,
  -- goal is x : ℕ ⊢ 2 + x = 5,
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  existsi x,
  left,
  assumption,
end

example (p q : ℕ → Prop) :
  (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
begin
  intro h,
  cases h with x hpq,
  cases hpq with hp hq,
  existsi x,
  split; assumption,
end

open nat

example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) :
  P m :=
begin
  cases m with m', exact h₀, exact h₁ m'
end

example (n : ℕ) : n + 1 = nat.succ n :=
begin
  show nat.succ n = nat.succ n,
  reflexivity,
end