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
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (λ t : p ∧ (q ∨ r) =>
      have wp : p := And.left t
      have wqr : q ∨ r := And.right t
      Or.elim wqr 
        (λ wq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) (And.intro wp wq))
        (λ wr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (And.intro wp wr)))
    (λ s : (p ∧ q) ∨ (p ∧ r) => 
      Or.elim s
        (λ wpq : p ∧ q =>
          have wp : p := And.left wpq
          have wq : q := And.right wpq
          show p ∧ (q ∨ r) from And.intro wp (Or.intro_left r wq))
        (λ wpr : p ∧ r =>
          have wp : p := And.left wpr
          have wr : r := And.right wpr
          show p ∧ (q ∨ r) from And.intro wp (Or.intro_right q wr)))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
    (λ t : p ∨ (q ∧ r) =>
      Or.elim t
        (λ wp : p =>
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.intro_left q wp) (Or.intro_left r wp))
        (λ wqr : q ∧ r =>
          have wq : q := And.left wqr
          have wr : r := And.right wqr
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.intro_right p wq) (Or.intro_right p wr)))
    (λ s : (p ∨ q) ∧ (p ∨ r) =>
      have wpq : p ∨ q := And.left s
      have wpr : p ∨ r := And.right s
      Or.elim wpq
        (λ wp : p =>
          show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) wp)
        (λ wq : q =>
          Or.elim wpr
            (λ wp : p =>
              show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) wp)
            (λ wr : r =>
              show p ∨ (q ∧ r) from Or.intro_right p (And.intro wq wr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
    (λ wpqr : p → (q → r) => 
      λ wpq : p ∧ q =>
        have wp : p := And.left wpq
        have wq : q := And.right wpq
        show r from wpqr wp wq)
    (λ w : p ∧ q → r => 
      λ wp : p =>
        λ wq : q => 
          have t : p ∧ q := And.intro wp wq
          show r from w t)


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (λ w : (p ∨ q) → r =>
      have wpr : p → r := 
        (λ wp : p => w (Or.intro_left q wp))
      have wqr : q → r :=
        (λ wq : q => w (Or.intro_right p wq))
      show (p → r) ∧ (q → r) from And.intro wpr wqr)
    (λ x : (p → r) ∧ (q → r) =>
      have t : p → r := And.left x
      have s : q → r := And.right x
      λ y : p ∨ q =>
        Or.elim y
          (λ wp : p =>
            show r from t wp)
          (λ wq : q =>
            show r from s wq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
    (λ w : ¬(p ∨ q) =>
      have wnp : ¬p :=
        (λ wp : p => w (Or.intro_left q wp))
      have wnq : ¬q :=
        λ wq : q => w (Or.intro_right p wq)
      show ¬p ∧ ¬q from And.intro wnp wnq)
    (λ x : ¬p ∧ ¬q =>
      have wnp : ¬p := And.left x
      have wnq : ¬q := And.right x
      λ y : p ∨ q =>
        Or.elim y
          (λ wp : p =>
            show False from wnp wp)
          (λ wq : q =>
            show False from wnq wq))

-- Here is one direction: the other direction is classical.
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  λ w : ¬p ∨ ¬q =>
    λ t : p ∧ q =>
      have wp : p := And.left t
      have wq : q := And.right t
      Or.elim w
        (λ wnp : ¬p =>
          show False from wnp wp)
        (λ wnq : ¬q =>
          show False from wnq wq)

-- Non-contradiction
example : ¬(p ∧ ¬p) := 
  λ w : p ∧ ¬p =>
    have wp : p := And.left w
    have wnp : ¬p := And.right w
    show False from wnp wp

example : p ∧ ¬q → ¬(p → q) :=
  λ w : p ∧ ¬q =>
    have wp : p := And.left w
    have wnq : ¬q := And.right w
    λ x : p → q =>
      show False from wnq (x wp)

example : ¬p → (p → q) :=
  λ x : ¬p => 
    λ y : p =>
      show q from False.elim (x y)

example : (¬p ∨ q) → (p → q) := 
  λ x : (¬p ∨ q) => 
    λ wp : p =>
      Or.elim x
        (λ wnp : ¬p =>
          show q from False.elim (wnp wp))
        (λ wq : q =>
          show q from wq)

example : p ∨ False ↔ p := 
  Iff.intro
    (λ x : p ∨ False =>
      Or.elim x
        (λ wp : p =>
          show p from wp)
        (λ y : False =>
          show p from False.elim y))
    (λ wp : p =>
      show (p ∨ False) from Or.intro_left False wp)

example : p ∧ False ↔ False := 
  Iff.intro
    (λ x : p ∧ False =>
      show False from And.right x)
    (λ y : False => 
      show p ∧ False from False.elim y)

example : (p → q) → (¬q → ¬p) := 
  λ x : p → q =>
    λ y : ¬q => 
      λ z : p =>
      show False from y (x z)


    
