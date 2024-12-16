------------------------
-- define insertion sort
------------------------

-- insert an number into a list of numbers
def insert : Nat → List Nat → List Nat
| x, [] => [x]
| x, y :: ys =>
  if x ≤ y then
    x :: y :: ys
  else
    y :: insert x ys
-- sort by inserting
def insertionSort : List Nat → List Nat
| [] => []
| x :: xs => insert x (insertionSort xs)
-- test insertionSort
#eval insertionSort [5, 2, 9, 1, 5, 6]

-----------------------------------
-- available operations on List Nat
-----------------------------------

-- https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html
#print List
#check List Nat
#eval 1 ≤ 2
#eval List.map (λ x ↦ x+1) (List.reverse (List.range 2))
#eval List.head? [1,2]
#eval [1,2].head?
#eval ([]:List Nat).head?
#eval List.head [1,2] (by simp) -- must provide proof that list is not empty
#eval List.isEmpty [1]
#eval List.elem 2 [1,2]
#eval List.elem 2 []
#eval 2 ∈ [1,2]
#eval List.Mem 2 [1,2]
-- use myIsElem instead
def myIsElem : Nat -> List Nat -> Prop
| _, [] => False
| a, b :: bs => if a = b then True else myIsElem a bs
-- (head x::ys) is an element of (x:ys)
theorem head_isElem_of_cons : ∀ (x : Nat) (ys : List Nat), myIsElem (List.head (x::ys) (by simp)) (x::ys) := by simp [myIsElem]
-- if xs is not empty then (head xs) is an element of xs
theorem head_isElem : ∀ (xs : List Nat), ∀ (p : xs ≠ []), myIsElem (List.head xs p) xs := by
  intros xs p
  induction xs with
  | nil =>
    contradiction
  | cons x ys =>
    exact head_isElem_of_cons x ys
-- if z in (insert x []) then z=x
theorem isElem_singleton : ∀ (x : Nat), ∀ (z : Nat), myIsElem z [x] → z = x := by simp [myIsElem]
-- z in xs -> z in x::xs
theorem isElem_tail : ∀ (a x : Nat) (xs : List Nat), myIsElem a xs → myIsElem a (x :: xs) := by
  intros a x xs h
  have h2 : if a = x then True else myIsElem a xs := by simp [h]
  rw [← myIsElem] at h2
  exact h2
-- z in x:xs -> z=x or z in xs
theorem isElem_cons : ∀ (a b : Nat) (bs : List Nat), myIsElem a (b :: bs) → a = b ∨ myIsElem a bs := by
  intro a b bs h
  rw [myIsElem] at h
  if h_ab : a = b then
    exact Or.inl h_ab
  else
    rw [if_neg h_ab] at h
    exact Or.inr h

----------------------------------
----------------------------------
-- Verification of insertionSort
----------------------------------
----------------------------------

-- define sorted
def sorted : List Nat → Prop
| [] => True
| [_] => True
| x :: y :: xs => x ≤ y ∧ sorted (y :: xs)

-------------------------
-- Lemmas on sorted lists
-------------------------

-- empty list is sorted
theorem sorted_empty : sorted [] :=
  True.intro
-- one element list is sorted
theorem sorted_singleton: ∀ (x : Nat), sorted [x] :=
  λ _ ↦ True.intro
-- if x ≤ y then [x,y] is sorted
theorem sorted_double: ∀(x:Nat), ∀(y:Nat), ∀(_:x ≤ y), sorted [x,y] :=
  λ_ ↦ λ_ ↦ λh ↦ ⟨h,True.intro⟩
-- if x::xs is sorted then xs is sorted
theorem sorted_tail : ∀ (x : Nat) (xs : List Nat), sorted (x :: xs) → sorted xs := by
  intros x xs h_sorted
  cases xs with
  | nil => exact True.intro
  | cons y ys =>
    cases h_sorted with
    | intro h_le h_sorted_tail =>
      exact h_sorted_tail
-- if x::y::zs is sorted then x:zs is sorted
theorem sorted_x_y_zs : ∀ (x y : Nat) (zs : List Nat), sorted (x :: y :: zs) → sorted (x :: zs) := by
  sorry
-- if x:ys is sorted then x ≤ y for all y in ys
theorem sorted_head_le_all : ∀ (x : Nat) (ys : List Nat), sorted (x :: ys) → ∀ (a:Nat), myIsElem a ys →  x ≤ a := by
  sorry

---------------------------------
-- Prove that InsertionSort sorts
---------------------------------

theorem insert_nil : ∀ (x : Nat), insert x [] = [x] := by simp [_root_.insert]

-- insert x ys is not empty
theorem insert_not_empty : ∀ (x : Nat) (ys : List Nat), insert x ys ≠ [] := by
  sorry

-- insert x [y] is sorted
theorem sorted_insert_singleton: ∀ (x : Nat), ∀ (y: Nat), sorted (insert x (y::List.nil)) := by
  sorry

-- if a in (insert x ys) then a=x or a in ys
theorem isElem_insert : ∀ (x : Nat) (ys : List Nat), ∀ (a : Nat), myIsElem a (insert x ys) → a = x ∨ myIsElem a ys := by
  sorry

-- if x ≤ y for all y in ys and ys is sorted then insert x ys is sorted
theorem insert_le_all : ∀ (x : Nat) (ys : List Nat), sorted ys → (∀ (y : Nat), myIsElem y ys → x ≤ y) → sorted (x :: ys) := by
  sorry

-- sorted is an invariant of insert
theorem insert_invariant : ∀ (x : Nat) (ys : List Nat), sorted ys → sorted (insert x ys) := by
  sorry
theorem insertion_sort_correctness : ∀ (xs : List Nat), sorted (insertionSort xs) := by
  intros xs
  induction xs with
  | nil => -- empty list is sorted
    exact True.intro
  | cons x xs ih =>
    cases xs with
    | nil => -- one element list is sorted
      exact True.intro
    | cons y ys =>
      exact insert_invariant x (insertionSort (y :: ys)) ih
