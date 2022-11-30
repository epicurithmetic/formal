-- Working through exercises from Theorem Proving in Lean 4


example (α : Type) (p q : α → Prop) :(∀ x : α, p x ∧ q x) →  ∀ y : α, p y := 
  λ w : (∀ x : α, p x ∧ q x) => 
    λ wa : α => -- ∀ claims are function types, so we make an assumption.
                -- Let a be an arbitrary α e.g. let p be an arbitrary prime. 
      show p wa from (w wa).left
      
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := 
  by exact λ w : ∀ x, p x ∧ q x => -- This abstraction is for the implication
    have t : (∀ x, p x) :=
      λ a : α => (w a).left -- This abstraction is the ∀ abstraction
    
    have s : (∀ x, q x) := 
      λ b : α => (w b).right -- This abstraction is the ∀ abstraction

    show (∀ x, p x) ∧ (∀ x, q x) from And.intro t s

example : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) :=
  by exact λ t : (∀ x, p x) ∧ (∀ x, q x) => 
    have ap : (∀ x, p x) := t.left
    have aq : (∀ x, q x) := t.right

    λ a : α => -- Let a be an arbitrary... show it satisfies...
      show (p a) ∧ (q a) from And.intro (ap a) (aq a)

example : (∀ x, p x) ∧ (∀ x, q x) ↔ (∀ x, p x ∧ q x) :=
  Iff.intro
    (λ t : (∀ x, p x) ∧ (∀ x, q x) => 
      have ap : (∀ x, p x) := t.left
      have aq : (∀ x, q x) := t.right

      λ a : α =>
        show (p a) ∧ (q a) from And.intro (ap a) (aq a))

    (λ w : ∀ x, p x ∧ q x => -- This abstraction is for the implication
      have t : (∀ x, p x) :=
        λ a : α => (w a).left -- This abstraction is the ∀ abstraction
      
      have s : (∀ x, q x) := 
        λ b : α => (w b).right -- This abstraction is the ∀ abstraction

      show (∀ x, p x) ∧ (∀ x, q x) from And.intro t s)

  

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp





example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry



example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

