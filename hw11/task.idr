%default total

-- Task 1

-- A
e_sym : {x: a} -> {y: b} -> x = y -> y = x
e_sym Refl = Refl

-- B
e_trans : {x: a} -> {y: b} -> {z: c} -> x = y -> y = z -> x = z
e_trans Refl Refl = Refl

-- C
e_cong : {x: a} -> {y: a} -> (P: a -> b) -> x = y -> P x = P y
e_cong P Refl = Refl


-- check
five_is_five : 5=5
five_is_five = Refl

-- e_sym five_is_five
-- e_trans five_is_five five_is_five
-- e_cong (+ 1) five

-- Task 2

plus_zero_commutative : (a:Nat) -> 0 + a = a + 0
plus_zero_commutative Z = Refl
plus_zero_commutative (S a) = rewrite plus_zero_commutative a in Refl
  --replace {P = \w => S (0 + a) = S w} (plus_zero_commutative a) Refl

-- A
plus_zero : (x: Nat) -> x = x + 0
plus_zero x = e_trans (the (x = 0 + x) Refl) (plus_zero_commutative x)

-- B
one_plus : (x: Nat) -> S x = 1 + x
one_plus x = Refl

-- C
plus_one : (x: Nat) -> S x = x + 1
plus_one Z = Refl
plus_one (S a) = rewrite (plus_one a) in Refl

-- F
plus_S_in_right : (x: Nat) -> (y: Nat) -> S (x + y) = x + (S y)
plus_S_in_right Z y = Refl
plus_S_in_right (S k) y = rewrite plus_S_in_right k y in Refl

-- E
plus_S_out_out : (x: Nat) -> (y: Nat) -> S x + S y = S (S (x + y))
plus_S_out_out x y = rewrite sym (plus_S_in_right x y) in Refl

-- D
plus_S_out_out_x : (x: Nat) -> S x + S x = S (S (x + x))
plus_S_out_out_x x = plus_S_out_out x x

-- G
plus_commutative : (x: Nat) -> (y: Nat) -> x + y = y + x
plus_commutative Z y = plus_zero_commutative y
plus_commutative (S k) y = rewrite plus_commutative k y in plus_S_in_right y k

-- F
plus_associative : (x: Nat) -> (y: Nat) -> (z: Nat) -> x + (y + z) = (x + y) + z
plus_associative Z y z = Refl
plus_associative (S k) y z = rewrite plus_associative k y z in Refl

-- Task 3

-- A
mult_zero_left : (x: Nat) -> 0 = 0 * x
mult_zero_left x = Refl

-- B
mult_zero_right : (x: Nat) -> 0 = x * 0
mult_zero_right Z = Refl
mult_zero_right (S k) = rewrite mult_zero_right k in Refl

-- C
mult_one_left : (x: Nat) -> x = 1 * x
mult_one_left Z = Refl
mult_one_left (S k) = rewrite mult_one_left k in Refl

-- D
mult_one_right : (x: Nat) -> x = x * 1
mult_one_right Z = Refl
mult_one_right (S k) = rewrite mult_one_right k in Refl

-- E
-- mult_one_commutative : (x: Nat) -> 1 * x = x * 1
-- mult_one_commutative Z = Refl
-- mult_one_commutative (S k) = rewrite mult_one_commutative k in Refl
--
-- zero_plus : (x: Nat) -> x + 0 = x
-- zero_plus Z = Refl
-- zero_plus (S k) = rewrite zero_plus k in Refl

mult_right_S_out : (x: Nat) -> (y: Nat) -> x * (S y) = x + x * y
mult_right_S_out Z y = Refl
mult_right_S_out (S k) y =
  rewrite mult_right_S_out k y in
  rewrite plus_associative y k (k * y) in
  rewrite plus_commutative y k in
  rewrite sym (plus_associative k y (k * y)) in
  Refl

mult_commutative : (x: Nat) -> (y: Nat) -> x * y = y * x
mult_commutative Z y = rewrite mult_zero_right y in Refl
mult_commutative (S k) y =
  rewrite mult_commutative k y in
  rewrite mult_right_S_out y k in
  Refl


-- plus_mult_zero : (x: Nat) -> (y: Nat) -> 0 = x * 0 + y * 0
-- plus_mult_zero Z y = rewrite mult_zero_right y in Refl
-- plus_mult_zero (S k) y = rewrite plus_mult_zero k y in Refl

-- H
mult_plus_distributive_out : (x: Nat) -> (y: Nat) -> (z: Nat) -> (x + y) * z = x * z + y * z
mult_plus_distributive_out Z y z = Refl
mult_plus_distributive_out (S k) y z =
  rewrite mult_plus_distributive_out k y z in
  rewrite plus_associative z (k * z) (y * z) in
  Refl

-- F
mult_associative : (x: Nat) -> (y: Nat) -> (z: Nat) -> x * (y * z) = (x * y) * z
mult_associative Z y z = Refl
mult_associative (S k) y z =
  rewrite mult_associative k y z in
  rewrite mult_plus_distributive_out y (k * y) z in
  Refl

-- G
mult_plus_distributive_out_left : (x: Nat) -> (y: Nat) -> (z: Nat) -> x * (y + z) = x * y + x * z
mult_plus_distributive_out_left Z y z = Refl
mult_plus_distributive_out_left (S x) y z =
  rewrite mult_plus_distributive_out_left x y z in          -- (y + x * y) + (z + x * z)
  rewrite plus_associative (y + x * y) z (x * z) in         -- ((y + x * y) + z) + x * z
  rewrite sym (plus_associative y (x * y) z) in             -- (y + (x * y + z)) + x * z
  rewrite plus_commutative (x * y) z in                     -- (y + (z + x * y)) + x * z
  rewrite plus_associative y z (x * y) in                   -- ((y + z) + x * y) + x * z
  rewrite sym (plus_associative (y + z) (x * y) (x * z)) in -- (y + z) + (x * y + x * z)
  Refl

-- I
mult_sum_on_two : (x: Nat) -> (y: Nat) -> (x + y) * 2 = x + x + y + y
mult_sum_on_two x y =
  rewrite trans (mult_commutative (x + y) 2) (mult_plus_distributive_out_left 2 x y) in
  rewrite sym (plus_zero x) in
  rewrite sym (plus_zero y) in
  rewrite plus_associative (x + x) y y in
  Refl


-- Task 4

-- A
lte_3_5 : LTE 3 5
lte_3_5 = LTESucc (LTESucc (LTESucc LTEZero))

-- B
lte_add_one : LTE x y -> LTE x (S y)
lte_add_one LTEZero = LTEZero
lte_add_one (LTESucc x) = LTESucc (lte_add_one x)

-- C
lte_add_right_n : (n: Nat) -> LTE x y -> LTE x (n + y)
lte_add_right_n Z x = x
lte_add_right_n (S k) x = lte_add_one $ lte_add_right_n k x

lte_add_n : LTE x y -> LTE (x + n) (y + n)
lte_add_n {x = Z} {y} {n = n} prf = lte_add_right_n y lteRefl
lte_add_n {x = S x} {y = S y} {n = n} (LTESucc z) = LTESucc (lte_add_n z)



-- D
lte_tranzitive : LTE x y -> LTE y z -> LTE x z
lte_tranzitive LTEZero y = LTEZero
lte_tranzitive (LTESucc x) (LTESucc y) = LTESucc (lte_tranzitive x y)

-- E
lte_eq : LTE x y -> LTE y x -> x = y
lte_eq LTEZero LTEZero = Refl
lte_eq (LTESucc x) (LTESucc y) = rewrite lte_eq x y in Refl

-- F
lte_xx : LTE x x
lte_xx {x = Z} = LTEZero
lte_xx {x = (S k)} = LTESucc lte_xx

-- Task 5

data GT' : Nat -> Nat -> Type where
  GT'Zero : GT' (S left) Z
  GT'Succ : GT' left right -> GT' (S left) (S right)

-- A
gt_5_3 : GT 5 3
gt_5_3 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

-- B
gt_transitive : GT' x y -> GT' y z -> GT' x z
gt_transitive {x = S x'} a GT'Zero = GT'Zero {left = x'}
gt_transitive (GT'Succ a) (GT'Succ b) = GT'Succ (gt_transitive a b)

-- C
gt_rofl : GT' (x + 1) x
gt_rofl {x = Z} = GT'Zero
gt_rofl {x = (S k)} = GT'Succ gt_rofl

gt_rufl : GT' (S x) x
gt_rufl {x = Z} = GT'Zero
gt_rufl {x = (S k)} = GT'Succ gt_rufl


-- D
gt_add_n' : GT' x y -> GT' (n + x) (n + y)
gt_add_n' {n = Z} prf = prf
gt_add_n' {n = (S k)} prf = GT'Succ (gt_add_n' prf)

gt_add_n : GT' x y -> GT' (x + n) (y + n)
gt_add_n {x} {y} {n} prf =
  rewrite plusCommutative x n in
  rewrite plusCommutative y n in
  gt_add_n' prf

-- E
gt_sqre : GT' x 1 -> GT' (x * x) x
gt_sqre {x = Z} GT'Zero impossible
gt_sqre {x = Z} (GT'Succ _) impossible
gt_sqre {x = (S Z)} (GT'Succ GT'Zero) impossible
gt_sqre {x = (S Z)} (GT'Succ (GT'Succ _)) impossible
gt_sqre {x = (S (S x))} _ =
  rewrite plusCommutative (S (S x)) (S x * S (S x)) in
  gt_add_n {n = S (S x)} (the (GT' (S x * S (S x)) Z) GT'Zero)

-- F
gt_bunt : GT' x 2 -> GT' (x * x) (x + x)
gt_bunt {x = Z} GT'Zero impossible
gt_bunt {x = Z} (GT'Succ _) impossible
gt_bunt {x = (S Z)} (GT'Succ GT'Zero) impossible
gt_bunt {x = (S Z)} (GT'Succ (GT'Succ _)) impossible
gt_bunt {x = (S (S Z))} (GT'Succ (GT'Succ GT'Zero)) impossible
gt_bunt {x = (S (S Z))} (GT'Succ (GT'Succ (GT'Succ _))) impossible
gt_bunt {x = (S (S (S x)))} _ =
  rewrite type_lemma (S (S (S x))) (S (S (S x))) (S x * S (S (S x))) in
    gt_add_n {n = S (S (S x))}
             (gt_add_n {n = S (S (S x))}
                       (the (GT' (S x * S (S (S x))) Z) GT'Zero))
  where
    type_lemma : (a: Nat) -> (b: Nat) -> (c: Nat) -> a + (b + c) = (c + b) + a
    type_lemma a b c =
      rewrite plusCommutative a (b + c) in
      rewrite plusCommutative b c in
      Refl

-- act -- (S x * (S S S x) + (S S S x)) + (S S S x)
-- exp -- (S S S x) + ((S S S x) + (S x) * (S S S x))

-- G
roole : Either (LTE x y) (GT' x y)
roole {x = Z} {y = Z} = Left LTEZero
roole {x = Z} {y = (S k)} = Left LTEZero
roole {x = (S k)} {y = Z} = Right GT'Zero
roole {x = (S k)} {y = (S j)} =
  case roole {x = k} {y = j} of
    Left lte => Left (LTESucc lte)
    Right gt => Right (GT'Succ gt)

-- Task 6

sub : Nat -> Nat -> Nat
sub Z y = Z
sub x Z = x
sub (S x) (S y) = sub x y

-- A
lte_to_sub : LTE x y -> sub x y = 0
lte_to_sub LTEZero = Refl
lte_to_sub (LTESucc prf) = rewrite lte_to_sub prf in Refl

-- B
sub_to_lte : sub x y = 0 -> LTE x y
sub_to_lte {x = Z} prf = LTEZero
sub_to_lte {x = (S k)} {y = Z} Refl impossible
sub_to_lte {x = (S k)} {y = (S j)} prf =
  let pred = sub_to_lte $ trans Refl prf in LTESucc pred

-- C
eqq : (x: Nat) -> sub x Z = x
eqq Z = Refl
eqq (S k) = Refl

lte_kek_sub : LTE y x -> y + (sub x y) = x
lte_kek_sub {x} LTEZero = rewrite eqq x in Refl
lte_kek_sub (LTESucc x) = rewrite lte_kek_sub x in Refl
