import data.list.pairwise
import tactic
namespace list

variable r : ℕ → ℕ → Prop


/-
The great thing about using the for all formulation rather than comparing against just the list head
is that the forall formulation automatically handles the case that a one element list is sorted. 

-/
inductive jtsort : list ℕ → Prop
| nil : jtsort [] 
| cons : ∀ (a : ℕ ) (l : list ℕ ), (∀ a' ∈ l, a≥ a') → jtsort l → jtsort (a::l) 


lemma jtsort_cons2 (a : ℕ ) (l : list ℕ ) : jtsort (a::l) ↔ (∀ a' ∈ l, a≥ a') ∧ jtsort (l)
:=
begin
  split,
  intro h,
  cases h with h1 h2 h3 h4,
  exact and.intro h3 h4,
  intro h,
  cases h with h1 h2 h3 h4,
  apply jtsort.cons a l h1 h2,
end


/-
lemma: If l is sorted, and a∈ ℕ, then stinsert a l is also sorted.
Proof.
if l is nil, then stinsert a l is [a] which is sorted. 

Otherwise, write l=(b::s). Then stinsert a l depends on whether a≥ b or not.
if a ≥ b, then stinsert a (b::s) = a::b::s. Since l=(b::s), is sorted, we know that,
for all b' in l, b≥ b'.  We also know a ≥ b. Therefore a≥ b' for all b' and so (a::b::l) is sorted. 

If a < b, then stinsert a (b::s) is b::(stinsert a s).  Since s is shorter than then l,
we know by induction that stinsert a s is sorted.  We also know that b ≥ every element of stinsert a s 
because b is greater then or equal to  every element of s by assumption, and b>a by hypothesis. 
Therefore b::(stinsert a s) is sorted. 
-/

def stinsert  : ℕ → list ℕ → list ℕ 
| a  [] := [a]
| a  (b::l) := if a ≥ b then a::b::l else b::(stinsert a l)

def srt : list ℕ → list ℕ 
| [] := []
| (a::l) := stinsert a (srt l)


lemma nil_sorted : ∀ (l : list ℕ), (l=[]) → jtsort l
:=
begin
  intros l h,
  subst h,
  apply jtsort.nil,
end

lemma tail_sorted : ∀ (a : ℕ ) (l : list ℕ ), jtsort (a::l) → jtsort l :=
begin
  intros a l H,
  cases H with a l h1 h2,
  exact h2,
end

lemma step : ∀ (a b: ℕ ) (l : list ℕ ), (∀ (a'∈ l), (b≥a')) ∧ (a≥ b) → ∀ (a' ∈ (b::l)), a≥ a' :=
begin
  rintros a b l ⟨ Ha, Hb⟩ x Hab,
  cases Hab,
  subst_vars,
  exact Hb,
  have  HK := Ha x Hab,
  linarith,
end

lemma un : ∀ (a x : ℕ) (l : list ℕ ), (x ∈ (stinsert a l)) → (x ∈ (a::l)) :=
begin
  intros a x l,
  induction l with hd tl H,
  { -- empty list case
    rintro  h,
    exact h,
  },
  { -- nonempty list case

    intro Hp,
    rw stinsert at Hp, 
    split_ifs at Hp,
      { -- a gets inserted at beginning
        exact Hp,
      },
    -- a gets inserted inside somewhere
      cases Hp with xhd xtl,
      simp,
      right,
      left,
      exact xhd,
    {
    have H2 := H xtl,
    simp,
    simp at H2,
    cases H2,
    left,
    exact H2,
    right,
    right,
    exact H2,
    },
},
end



lemma ins_sorted : ∀ (a : ℕ ) (l : list ℕ ), jtsort l → jtsort (stinsert a l):=
begin
  intros a l H,
  induction l with b l iH,
  rw stinsert,
  have hK := (jtsort.cons a []) _ H,
  exact hK,
  intros a' hN,
  cases hN,
  rw stinsert,
  split_ifs,
  cases H with a l H1 H2,
  have hK := step a b l (and.intro H1 h),
  have HZ := jtsort.cons b l H1 H2,
  exact jtsort.cons a (b::l) hK HZ,
  have HW := tail_sorted b l H,
  have HN := iH HW,
  apply jtsort.cons, 
  intros x Hx,
  have HM := jtsort_cons2 b l,
  cases HM with HL HR,
  have HP1 := (HL H).left,
  have Hz := un a x l Hx,
  rw mem_cons_iff at Hz,
  cases Hz,
  linarith,
  exact HP1 x Hz,
  exact HN,
end



theorem jtsorter : ∀ (l : list ℕ ), jtsort (srt l):=
begin
  intro,
  induction l with a l ih,
  rw srt,
  apply nil_sorted,
  refl,
  rw srt,
  have HK := ins_sorted a l.srt ih,
  exact HK,
end


end list
#print list.has_mem
#print classes