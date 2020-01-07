%default total

mult2_is_twice_n : (n: Nat) -> 2 * n = n + n
mult2_is_twice_n n = rewrite plusCommutative n 0 in Refl

pow_2_is_twice_n : (n: Nat) -> pow n 2 = n * n
pow_2_is_twice_n n =
  rewrite multCommutative n 1 in
  rewrite plusCommutative n 0 in
  Refl

mult_out_out_S : (a: Nat) -> (1 + a) * (1 + a) = 1 + a + a + a * a
mult_out_out_S a =
  rewrite multCommutative a (S a) in
  rewrite plusAssociative a a (a * a) in
  Refl

mult_midl_out_S : (a: Nat) -> (b: Nat) -> 2 * (S a) * b = 2 * b + 2 * a * b
mult_midl_out_S a b =
  rewrite sym $ plusSuccRightSucc a (a + 0) in
  rewrite plusCommutative b 0 in
  rewrite plusAssociative b b ((a + (a + 0))* b) in
  Refl

lemma_1 : (a: Nat) -> (b: Nat) ->
          (S a + b) * (S a + b) = 1 + (a + b) + (a + b) + (a + b) * (a + b)
lemma_1 a b = mult_out_out_S (a + b)

lemma_2 : (a: Nat) -> (b: Nat) -> (c: Nat) -> (d: Nat) -> (e: Nat) ->
            a + b + (c + d) + e = a + c + b + d + e
lemma_2 a b c d e =
  rewrite plusAssociative (a + b) c d in
  rewrite sym $ plusAssociative a b c in
  rewrite plusCommutative b c in
  rewrite plusAssociative a c b in
  Refl


lemma_3 : (a: Nat) -> (b: Nat) ->
          (S a) * (S a) + 2 * (S a) * b + b * b =
             1 + a + a + b + b + (a * a + 2 * a * b + b * b)
lemma_3 a b =
  rewrite multCommutative a (S a) in
  rewrite plusAssociative a a (a * a) in
  rewrite mult_midl_out_S a b in
  rewrite lemma_2 (1 + a + a) (a * a) (2 * b) (2 * a * b) (b * b) in
  rewrite mult2_is_twice_n b in
  rewrite plusAssociative (a + a) b b in
  rewrite sym $ plusAssociative (1 + a + a + b + b + a * a) (2 * a * b) (b * b) in
  rewrite sym $ plusAssociative (1 + a + a + b + b) (a * a) (2 * a * b + b * b) in
  rewrite plusAssociative (a * a) (2 * a * b) (b * b) in
  Refl

-- TODO!
lemma_4 : (a: Nat) -> (b: Nat) ->  1 + (a + b) + (a + b) = 1 + a + a + b + b
lemma_4 a b =
  rewrite plusAssociative (a + b) a b in
  rewrite plusCommutative a b in
  rewrite sym $ plusAssociative (b + a) a b in
  rewrite plusCommutative (b + a) (a + b) in
  rewrite plusAssociative (a + b) b a in
  rewrite plusCommutative (a + b + b) a in
  rewrite plusAssociative a (a + b) b in
  rewrite plusAssociative a a b in
  Refl

step_lemma : {a: Nat} -> a=c -> b=d -> a + b = c + d
step_lemma prf_a_c prf_b_d =
  rewrite prf_a_c in
  rewrite prf_b_d in
  Refl

sqre_of_summ_lemma : (a: Nat) -> (b: Nat) ->
                     (a + b) * (a + b) = a * a + 2 * a * b + b * b
sqre_of_summ_lemma Z b = Refl
sqre_of_summ_lemma (S k) b =
  let step = step_lemma (lemma_4 k b) (sqre_of_summ_lemma k b) in
      trans (trans (lemma_1 k b) step) (sym $ lemma_3 k b)

sqre_of_summ : (a: Nat) -> (b: Nat) ->
               pow (a + b) 2 = pow a 2 + 2 * a * b + pow b 2
sqre_of_summ a b =
  rewrite pow_2_is_twice_n (a + b) in
  rewrite pow_2_is_twice_n a in
  rewrite pow_2_is_twice_n b in
  sqre_of_summ_lemma a b

expr_proof: (n: Nat) -> pow (n + 2) 2 = pow n 2 + 4 * n + 4
expr_proof n = rewrite lemma n in sqre_of_summ n 2
  where
    lemma : (n: Nat) -> 4 * n = 2 * n * 2
    lemma n =
      rewrite sym $ multAssociative 2 n 2 in
      rewrite multCommutative n 2 in
      rewrite multAssociative 2 2 n in
      Refl
