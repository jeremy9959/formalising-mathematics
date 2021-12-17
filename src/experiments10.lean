-- Lean already has `eq` so let's make `eq2` for this exercise
inductive eq2 {X : Type} : X → X → Prop
| refl (a : X) : eq2 a a

/-
Lean already has `=` so I've used `∼` (type with `\sim`) as notation for eq2.
The 50 is the "binding power", something the parser needs to know.
-/

infix ` ∼ `:50 := eq2

namespace eq2

-- Let `X` be a type/set, and let a,b,c be terms/elements
variables {X : Type} {a b c : X}
variables {R : X → X → Prop}

-- Let's first establish the theorem we will need, using the recursor.

/-- If `a ∼ b`, and if `R` is a binary relation on `X` such that `R x x`
  is true for all `x`, then `R a b` is true  -/
theorem ind (hab :  a ∼ b) (R : X → X → Prop) (h : ∀ (x : X), R x x) :
  R a b :=
-- don't worry about the proof
eq2.rec  h hab

#check ∀ (x : X), R x x  

#check @eq2.rec

-- reflexivity is no problem -- indeed it's a constructor.
example : a ∼ a :=
begin
  exact refl a
end

/-
The game: using only `ind` and `refl`, prove `symm` and `trans`!
-/
def r1 (a : X) (b : X) : Prop := b∼a

#check r1 a a 

lemma r1refl : ∀ (a :X),  r1 a a :=
begin
  intro,
  rw r1,
  exact refl a,
end


-- level 1
theorem symm (hab : a ∼ b) : b ∼ a :=
begin
  have hk := ind hab r1 r1refl,
  exact hk,
end

-- boss level



end eq2