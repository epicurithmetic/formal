variable (p q r : Prop)

theorem test (wp : p) (wq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact wp
     apply And.intro
     exact wq
     exact wp

