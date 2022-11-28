-- Working through exercises from Theorem Proving in Lean 4
example : (p → (q → r)) →  (p ∧ q → r) := 
  by exact fun t : p → (q → r) =>
    fun s : p ∧ q =>
      have j₁: p := s.left
      have j₂: q := s.right
      have t₂: q → r := t j₁
      show r  from t₂ j₂ 

example : (p ∧ q → r) → (p → (q → r))  := 
  by exact fun hpqr:(p ∧ q → r) =>
    fun hp:p =>
      fun hq:q =>
        have hpq:(p ∧ q) := And.intro hp hq
        have hr:r := hpqr hpq
        show r from hr

example : ¬(p ∨ q) → ¬p ∧ ¬q := 
  fun wnpq : ¬(p ∨ q) =>
    have wnp : ¬p := (fun wp:p =>
      have j:(p ∨ q):= Or.intro_left q wp
      show False from wnpq j)
    have wnq : ¬q := (fun wq:q =>
      have j:(p ∨ q):= Or.intro_right p wq
      show False from wnpq j)
    show ¬p ∧ ¬q from And.intro wnp wnq 
    
