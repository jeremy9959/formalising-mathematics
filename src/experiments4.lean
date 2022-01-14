import tactic
open classical

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
open function 
namespace xena


def next (d : weekday) : weekday :=
weekday.cases_on d monday tuesday wednesday thursday friday
  saturday sunday

def previous (d : weekday) : weekday :=
weekday.cases_on d saturday sunday monday tuesday wednesday
  thursday friday

#reduce next ( previous friday)

theorem next_previous (d : weekday) : next(previous d) = d :=
begin
cases d,
refl, refl, refl, refl, refl, refl, refl,
end

def weekday.nd ( d: weekday ) : ℕ := weekday.cases_on d 1 2 3 4 5 6 7



variables {X Y : Type} {f: option X → option Y}
variables {a b c : X}


#check inhabited.mk ℕ 




