(set-option :produce-proofs true)
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-fun observe ((Array Int Int)) Int)
(assert
  (distinct
    (observe (store a i (select a i)))
    (observe a)))
(check-sat)
(get-proof)
