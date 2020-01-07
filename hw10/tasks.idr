import Data.Fin
import Data.Vect

-- Task 2

-- Task 5

-- A
plus_fin : Fin a -> Fin b -> Fin (a + b)
plus_fin {a = S a'} {b = S b'} FZ fy =  rotatePlus (weakenN (S a') fy)
  where
    rotatePlus : Fin (b + a) -> Fin (a + b)
    rotatePlus {a} {b} x = rewrite plusCommutative a b in x
plus_fin {a = S a'} {b = S b'} (FS x) fy = FS (plus_fin x fy)

-- check
-- plus_fin (FS (FS (FZ { k = 3}))) (FS (FS (FZ { k = 4})))

-- B
mul_fin : Fin a -> Fin b -> Fin (a * b)
mul_fin {a = S a'} {b = S b'} FZ fb = FZ
mul_fin {a = S a'} {b = S b'} (FS x) fb = plus_fin fb $ mul_fin x fb


-- Task 6

-- min
total nat_min : Nat -> Nat -> Nat
nat_min Z Z = Z
nat_min Z (S k) = Z
nat_min (S k) Z = Z
nat_min (S k) (S j) = S (nat_min k j)

total fin_min : Fin (S a) -> Fin (S b) -> Fin (S (nat_min a b))
fin_min {a = Z} {b = Z} x y = FZ
fin_min {a = Z} {b = (S k)} x y = x
fin_min {a = (S k)} {b = Z} x y = y
fin_min {a = (S k)} {b = (S j)} FZ FZ = FZ
fin_min {a = (S k)} {b = (S j)} FZ (FS x) = FZ
fin_min {a = (S k)} {b = (S j)} (FS x) FZ = FZ
fin_min {a = (S k)} {b = (S j)} (FS x) (FS y) = FS (fin_min x y)

-- map2
total map2 : {x: Type} -> {y: Type} -> {z: Type} ->
             (x -> y -> z) -> Vect a x -> Vect b y -> Vect (nat_min a b) z
map2 {a = Z}     {b = Z}     f [] ys               = []
map2 {a = Z}     {b = (S k)} f [] ys               = []
map2 {a = Z}     {b = Z}     f xy []               = []
map2 {a = (S k)} {b = Z}     f xy []               = []
map2 {a = (S k)} {b = (S j)} f (x :: xs) (y :: ys) = (f x y) :: (map2 f xs ys)

-- index2
up_bound_a : Fin (S (nat_min a b)) -> Fin (S a)
up_bound_a {a = Z} {b = Z} x = x
up_bound_a {a = Z} {b = (S b')} x = x
up_bound_a {a = (S a')} {b = Z} x = FZ
up_bound_a {a = (S a')} {b = (S b')} FZ = FZ
up_bound_a {a = (S a')} {b = (S b')} (FS x) = FS (up_bound_a x)

up_bound_b : Fin (S (nat_min a b)) -> Fin (S b)
up_bound_b {a = Z} {b = Z} x = x
up_bound_b {a = Z} {b = (S b')} x = FZ
up_bound_b {a = (S a')} {b = Z} x = x
up_bound_b {a = (S a')} {b = (S b')} FZ = FZ
up_bound_b {a = (S a')} {b = (S b')} (FS x) = FS (up_bound_b x)


total index2 : {x: Type} -> {y: Type} ->
               Fin (nat_min a b) -> Vect a x -> Vect b y -> (x, y)
index2 {a = Z} {b = Z} _ _ _ impossible
index2 {a = Z} {b = (S _)} _ _ _ impossible
index2 {a = (S _)} {b = Z} _ _ _ impossible
index2 {a = (S a')} {b = (S b')} fin_i xs ys =
  (index (up_bound_a fin_i) xs, index (up_bound_b fin_i) ys)
