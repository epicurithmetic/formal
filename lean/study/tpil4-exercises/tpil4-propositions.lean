variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro 
    (λ wpq : p ∧ q =>
      have wp : p := And.left wpq
      have wq : q := And.right wpq
      show q ∧ p from And.intro wq wp)
    (λ wqp : q ∧ p =>
      have wq : q := And.left wqp
      have wp : p := And.right wqp
      show p ∧ q from And.intro wp wq)

example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (λ wpq : p ∨ q =>
      Or.elim wpq
        (λ wp : p =>
          Or.intro_right q wp)
        (λ wq : q =>
          Or.intro_left p wq))
    (λ wqp : q ∨ p =>
      Or.elim wqp
        (λ wq : q =>
          Or.intro_right p wq)
        (λ wp : p =>
          Or.intro_left q wp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    (λ t : (p ∧ q) ∧ r =>
      have wr : r := And.right t
      have wpq : p ∧ q := And.left t
      have wp : p := And.left wpq
      have wq : q := And.right wpq
      show p ∧ (q ∧ r) from And.intro wp (And.intro wq wr))
    (λ s : p ∧ (q ∧ r) => 
      have wp : p := And.left s
      have wqr : q ∧ r := And.right s
      have wq : q := And.left wqr
      have wr : r := And.right wqr
      show (p ∧ q) ∧ r from And.intro (And.intro wp wq) wr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (λ t : (p ∨ q) ∨ r =>
      Or.elim t
        (λ wpq : p ∨ q =>
          Or.elim wpq 
            (λ wp : p =>
              show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) wp)
            (λ wq : q =>
              show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r wq)))
        (λ wr : r =>
          show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q wr)))
    (λ s : p ∨ (q ∨ r) =>
      Or.elim s
        (λ wp : p =>
          show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q wp))
        (λ wqr : q ∨ r =>
          Or.elim wqr
            (λ wq : q =>
              show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p wq))
            (λ wr : r =>
              show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) wr )))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

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
    
