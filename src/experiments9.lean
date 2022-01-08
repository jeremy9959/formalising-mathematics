import ring_theory.subring
import data.int.parity

theorem ex6b :  ¬ ∃ s : subring ℤ, ∀ x, x ∈ s ↔ odd x :=
begin
  intro h1,
  cases h1 with S h,
  have h2 := h 0,
  have h3 := h2.1,
  have h4 := S.zero_mem,
  have h5 := h3 h4,
  have h6 := (@int.odd_iff_not_even 0).1,
  have h7 := h6 h5,
  have h8 := absurd h7 dec_trivial,
  exact h8,
end

theorem ex6c :  ¬ ∃ s : subring ℤ, ∀ x, x ∈ s ↔ (0:ℤ) < x :=
begin
  intro h1,
  cases h1 with S h,
  have h2 := h (0:ℤ),
  have h3 := subring.zero_mem S,
  have h4 := h2.1,
  have h5 := h4 h3,
  have h6 := lt_irrefl (0:ℤ),
  exact h6 h5,
end
