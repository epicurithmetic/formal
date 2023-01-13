namespace robert

structure group (G : Type) :=
  mul : G → G → G
  e : G -- Identity of the group
  inv : G → G
  (mul_assoc : ∀ x y z : G, mul (mul x y) z = mul x (mul y z))
  (mul_one: ∀ x : G, mul e x = x)
  (one_mul: ∀ x : G, mul x e = x)
  (mul_left_inv : ∀ x : G, mul (inv x) x = e)

end robert

open robert

example 

example mul_left_cancel (a b c : G) (w : (mul a b) = (mul a c)) : b = c :=
  calc b = mul e b := mul_one

  calc b = mul e b               := mul_one
         = mul (mul (inv a) a) b := mul_left_inv
         = mul (inv a) (mul a b) := mul_assoc
         = mul (inv a) (mul a c) := w
         = mul (mul (inv a) a) c := mul_assoc
         = mul e c               := mul_left_inv
         = c                     := mul_one


         


