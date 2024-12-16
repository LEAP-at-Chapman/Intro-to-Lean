inductive NN where
  | z : NN                         -- zero
  | s (n : NN) : NN                -- successor of n, n + 1, NN.s n, n.s

def add : NN → NN → NN
  | NN.z, m => m                   -- 0 + m = m
  | NN.s n, m => NN.s (add n m)    -- (n + 1) + m = (n + m) + 1

def mul : NN → NN → NN
  | NN.z, _ => NN.z                -- 0 * m = 0
  | NN.s n, m => add (mul n m) m   -- (n + 1) * m = (n * m) + m

-- b + 0 = b
theorem add_zero (b : NN) : add b NN.z = b := by
  sorry

-- a + (b + 1) = (a + b) + 1
theorem add_succ (a b : NN) : add a (NN.s b) = NN.s (add a b) := by
  sorry

-- a + b = b + a
theorem add_comm (a b : NN) : add a b = add b a := by
  sorry

-- (a + b) + c = a + (b + c)
theorem add_assoc (a b c : NN) : add (add a b) c = add a (add b c) := by
  sorry

-- a * (b + 1) = a * b + a
theorem mul_succ (a b : NN) : mul a b.s = add (mul a b) a := by
  sorry

-- a * 0 = 0
theorem mul_zero (a : NN) : mul a NN.z = NN.z := by
  sorry

-- a * b = b * a
theorem mul_comm (a b : NN) : mul a b = mul b a := by
  sorry

-- a * (b + c) = a * b + a * c
theorem dist_left (a b c : NN) : mul a (add b c) = add (mul a b) (mul a c) := by
  sorry

-- (a + b) * c = a * c + b * c
theorem dist_right (a b c : NN) : mul (add a b) c = add (mul a c) (mul b c) := by
  sorry

-- (a * b) * c = a * (b * c)
theorem mul_assoc (a b c : NN) : mul (mul a b) c = mul a (mul b c) := by
  induction a with
  | z =>
    simp [mul]
  | s n ih =>
    simp [mul, dist_right, ih]
