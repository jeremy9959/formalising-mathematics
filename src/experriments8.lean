import tactic
inductive mytype
| AA : mytype 
| ZZ : mytype 

#print prefix mytype
#print mytype.AA.inj_arrow


variable (P : Prop) 
#check @mytype.rec
def mytype_equal'' : mytype → mytype → Prop := 
    λ s t, mytype.rec_on s (mytype.rec_on t true false) (mytype.rec_on  false true)  

inductive X : Type
| p : X

inductive Y : Type
| q : Y
| r : Y

inductive Z : Type
| s : Z

open X Y Z

def f : X → Y
| p := q

def g : Y → Z
| q := s
| r := s

theorem unconfused : q ≠ r := 
begin
  intro h,
  contradiction,
end
open function
#print prefix Y
#check @Y.no_confusion Prop q r

lemma arg : q ≠ r:=
begin 
  contradiction,
end

lemma g_not_inj : ¬ (injective g) :=
begin
  intro h,
  rw injective at h,
  replace h:= @h q r,
  have h4 : (g q = g r), {refl},
  have h5 := h h4,
  exact Y.no_confusion h5,
end

example : ¬ (∀ (X Y Z : Type) (f : X → Y) (g : Y → Z),
  injective (g ∘ f) → injective g) :=
begin
  intro h,
  specialize h X Y Z f g,
  have h1 : injective (g ∘ f),
  { 
    rw injective,
    intros h2 h3,
    cases h2,
    cases h3,
    intro h4,
    apply eq.refl,
  },
  have h3 := h h1,
  have h4 := g_not_inj h3,
  assumption,
  end