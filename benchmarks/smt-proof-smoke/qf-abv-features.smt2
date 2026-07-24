(set-option :produce-proofs true)
(set-option :global-declarations true)
(set-logic QF_ABV)
(define-sort Table () (Array (_ BitVec 1) (_ BitVec 2)))
(declare-const a Table)
(declare-const condition Bool)
(push 1)
(assert condition)
(check-sat)
(pop 1)
(reset-assertions)
(assert condition)
(assert
  (distinct
    (select (ite condition a (store a #b0 #b11)) #b1)
    (select a #b1)))
(assert
  (distinct
    (select
      (store
        ((as const (Array (_ BitVec 1) (_ BitVec 2))) #b01)
        #b0
        #b10)
      #b0)
    #b10))
(check-sat)
(get-proof)
