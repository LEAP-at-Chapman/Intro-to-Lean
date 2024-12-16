inductive NN where
  | z : NN               -- zero
  | s (n : NN) : NN      -- successor of n, 1 + n

def add : NN → NN → NN
  | NN.z, m => m
  | NN.s n, m => NN.s (add n m)

def mul : NN → NN → NN
  | NN.z, _ => NN.z
  | NN.s n, m => add m (mul n m)

-- b + 0 = b
theorem add_zero (b : NN) : add b NN.z = b := by
  sorry

-- 0 + b = b
theorem zero_add (b : NN) : add NN.z b = b := by
  sorry

-- a + (1 + b) = 1 + (a + b)
theorem add_succ (a b : NN) : add a (NN.s b) = NN.s (add a b) := by
  sorry

-- (1 + a) + b = 1 + (a + b)
theorem succ_add (a b : NN) : add a.s b = NN.s (add a b) := by
  sorry

-- a + b = b + a
theorem add_comm (a b : NN) : add a b = add b a := by
  sorry

-- (a+1) * b = b + (a*b)
theorem succ_mul (a b : NN) : mul (NN.s a) b = add b (mul a b) := by
  sorry

-- 0 * a = 0
theorem zero_mul (a : NN) : mul NN.z a = NN.z := by
  sorry

-- (a + b) + c = a + (b + c)
theorem add_assoc (a b c : NN) : add (add a b) c = add a (add b c) := by
  sorry

-- a * (b + 1) = a * b + a
theorem mul_succ (a b : NN) : mul a (NN.s b) = add (mul a b) a := by
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
