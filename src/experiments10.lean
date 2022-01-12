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
/-
protected eliminator eq2.rec : Π {X : Type} {C : X → X → Sort l}, (Π (a : X), C a a) → Π {ᾰ ᾰ_1 : X}, ᾰ ∼ ᾰ_1 → C ᾰ ᾰ_1
-/

#print eq2.rec



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

lemma r1refl : ∀ (a :X),  r1 a a := (λ a, eq2.refl a)


#check @eq2.rec X r1  r1refl a b

-- level 1
theorem symm (hab : a ∼ b) : b ∼ a := @eq2.rec X r1 r1refl a b hab

#print symm

-- boss level



end eq2
/-
@[derive list.cons.{0} pexpr ``(has_reflect) (list.nil.{0} pexpr)]
inductive bool : Type
constructors:
bool.ff : bool
bool.tt : bool
-/

#print bool

/-
protected eliminator bool.rec : Π {C : bool → Sort l}, C ff → C tt → Π (n : bool), C n
-/

#print bool.rec
/-
@[derive list.cons.{0} pexpr ``(has_reflect) (list.nil.{0} pexpr)]
structure prod : Type u → Type v → Type (max u v)
fields:
prod.fst : Π {α : Type u} {β : Type v}, α × β → α
prod.snd : Π {α : Type u} {β : Type v}, α × β → β
-/

#print prod 


/-
protected eliminator prod.rec : Π {α : Type u} {β : Type v} {C : α × β → Sort l},
  (Π (fst : α) (snd : β), C (fst, snd)) → Π (n : α × β), C n
-/

#print prod.rec


/-
@[derive list.cons.{0} pexpr ``(has_reflect) (list.nil.{0} pexpr)]
inductive sum : Type u → Type v → Type (max u v)
constructors:
sum.inl : Π {α : Type u} {β : Type v}, α → α ⊕ β
sum.inr : Π {α : Type u} {β : Type v}, β → α ⊕ β
-/

#print sum

/-
protected eliminator sum.rec : Π {α : Type u} {β : Type v} {C : α ⊕ β → Sort l},
  (Π (val : α), C (sum.inl val)) → (Π (val : β), C (sum.inr val)) → Π (n : α ⊕ β), C n
-/

#print sum.rec
/-
inductive eq : Π {α : Sort u}, α → α → Prop
constructors:
eq.refl : ∀ {α : Sort u} (a : α), a = a
-/

/-
inductive eq2 : Π {X : Type}, X → X → Prop
constructors:
eq2.refl : ∀ {X : Type} (a : X), a ∼ a
-/

#print eq2
variables (X : Type) (a : X)
example (a : X) : a = a := 
begin
  exact eq.refl a,
end

#print eq


/-
protected eliminator eq.rec : Π {α : Sort u} {a : α} {C : α → Sort l}, C a → Π {ᾰ : α}, a = ᾰ → C ᾰ
-/
/-
protected eliminator eq2.rec : Π {X : Type} {C : X → X → Sort l}, (Π (a : X), C a a) → Π {ᾰ ᾰ_1 : X}, ᾰ ∼ ᾰ_1 → C ᾰ ᾰ_1
-/
#print eq.rec

/-
inductive nat : Type
constructors:
nat.zero : ℕ
nat.succ : ℕ → ℕ
-/

#print nat 

/-
protected eliminator nat.rec : Π {C : ℕ → Sort l}, C 0 → (Π (n : ℕ), C n → C n.succ) → Π (n : ℕ), C n
-/

#print nat.rec 

/-
inductive list : Type u → Type u
constructors:
list.nil : Π {T : Type u}, list T
list.cons : Π {T : Type u}, T → list T → list T
-/

#print list
/-
protected eliminator list.rec : Π {T : Type u} {C : list T → Sort l},
  C list.nil → (Π (hd : T) (tl : list T), C tl → C (hd :: tl)) → Π (n : list T), C n
-/

#print list.rec 

variable (b : X)
universe u
inductive file_eq {α : Sort u}  (a : α) : α → Prop
| refl :  file_eq a 

#print file_eq.rec 

#check file_eq a b
git

#check ff2 
lemma ff2symm (a : X) : file_eq a a := file_eq.refl a



#check X
#check a


