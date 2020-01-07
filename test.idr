lte_transitivity : LTE n m -> LTE m p -> LTE n p
lte_transitivity LTEZero     y           = LTEZero
lte_transitivity (LTESucc x) (LTESucc y) = LTESucc (lte_transitivity x y)

--
lte_plusL : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE (c + a) (c + b))
lte_plusL Z p = p
lte_plusL (S k) p = LTESucc (lte_plusL k p)


lte_plusR : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE (a + c) (b + c))
lte_plusR {a} {b} c p =
  rewrite (plusCommutative a c) in
  rewrite (plusCommutative b c) in
  (lte_plusL c p)
 
