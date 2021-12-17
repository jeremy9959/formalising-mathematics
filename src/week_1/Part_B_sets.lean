import tactic

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

namespace xena

/-!

# subsets

Let's think about `X ⊆ Y`. Typeset `⊆` with `\sub` or `\ss`
-/

-- `X ⊆ Y` is the same as `∀ a, a ∈ X → a ∈ Y` , by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma subset_refl : X ⊆ X :=
begin
  refl,
end

lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  rw subset_def at *,
  intros a ha,
  apply hYZ a,
  apply hXY a,
  exact ha,
    -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`
  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.
  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff,
end

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 


lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
    rw set.ext_iff,
    intro,
    split,
    apply hXY,
    apply hYX,
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas

lemma union_self : X ∪ X = X :=
begin
  ext a,
  rw union_def,
  split,
  {intro hAX,
  cases hAX with hX1 hX2,
  exact hX1,
  exact hX2},
  {intro haX,
  left, 
  exact haX}
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  rw subset_def,
  intro ha,
  intro haX,
  rw union_def,
  left,
  exact haX,
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
 -- rw subset_def,
  intro ha,
  intro haY,
  rw union_def,
  right,
  exact haY,
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
    intro hXuYinZ,
    split,
      intro a,
      intro ha,
      apply hXuYinZ,
      left, assumption,
    intros a ha,
    apply hXuYinZ,
    right, assumption,
  
  rintros ⟨ hXZ,hYZ⟩ a (h1 | h2),
  apply hXZ,assumption,
  apply hYZ,assumption,
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  rw union_subset_iff at *,
  split,
    intro a,
    intro haW,
   -- rw union_def,
    left,
    apply hWX, assumption,
  intro a,
  intro haY,
  -- rw union_def,
  right,
  apply hYZ,
  assumption,
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  intro a,
  intro haXY,
  cases haXY with haX haY,
    {have foo:=hXY haX,
    left,
    assumption},
  {right,
  assumption}
end

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  intro a,
  intro haXY,
  cases haXY with haX haY,
  assumption,
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  ext a,
  split,
  apply inter_subset_left,
  intro haX,
  exact ⟨ haX, haX⟩,
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  rw set.ext_iff,
  intro,
  split,
  {
    intro haXY,
    cases haXY with haX haY,
    exact ⟨ haY, haX⟩,
  },
  { 
    intro haYX,
    cases haYX with haY haX,
    exact ⟨ haX, haY⟩,
  }
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  rw set.ext_iff,
  intro,
  split,
    intro hx,
    cases hx with ha hb,
    cases hb with hb hc,
    split,
    split,
    assumption, assumption, assumption,
  intro hx,
  cases hx with ha hb,
  cases ha with hb hc,
  split,
  assumption,
  split,
  assumption,
  assumption,
end

/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split,
  {intro h,
   intro b,
   intro hb,
   apply h,
   use b,
   assumption},
  {intro h,
  rintros ⟨ a, ha⟩,
  have foo := h a,
  apply foo,
  assumption,
  }
  
end

open classical

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
    {intro h,
    by_contra hnX, 
    apply h,
    intro a,
    by_contra hXa,
    apply hnX,
    use a,
    },
    {
      intro h,
      cases h with b hb,
      intro h,
      apply hb,
      apply h,
    }

  
end

end xena

