(set-logic ALL_SUPPORTED)
;; BEGIN: smt_of_spec counter

(define-fun states_equal
  ( (contents Int)
    (contents_new Int) )
  Bool
  (= contents contents_new)
 )

(define-fun increment_pre_condition
  ( (contents Int) )
  Bool
  (>= contents 0)
 )

(define-fun increment_post_condition
  ( (contents Int)
    (contents_new Int)
    (result Bool) )
  Bool
  (and (= contents_new (+ contents 1)) (= result true))
 )

(define-fun decrement_pre_condition
  ( (contents Int) )
  Bool
  (>= contents 1)
 )

(define-fun decrement_post_condition
  ( (contents Int)
    (contents_new Int)
    (result Bool) )
  Bool
  (and (= contents_new (- contents 1)) (= result true))
 )

(define-fun reset_pre_condition
  ( (contents Int) )
  Bool
  (>= contents 0)
 )

(define-fun reset_post_condition
  ( (contents Int)
    (contents_new Int)
    (result Bool) )
  Bool
  (and (= contents_new 0) (= result true))
 )

(define-fun zero_pre_condition
  ( (contents Int) )
  Bool
  (>= contents 0)
 )

(define-fun zero_post_condition
  ( (contents Int)
    (contents_new Int)
    (result Bool) )
  Bool
  (and (= contents_new contents) (= result (= contents 0)))
 )

;; END: smt_of_spec counter
(declare-fun contents () Int)
(declare-fun contents1 () Int)
(declare-fun contents2 () Int)
(declare-fun contents12 () Int)
(declare-fun contents21 () Int)
(declare-fun result_0_1 () Bool)
(declare-fun result_0_21 () Bool)
(declare-fun result_0_2 () Bool)
(declare-fun result_0_12 () Bool)
(define-fun oper () Bool (and 
  (increment_pre_condition contents)
  (increment_post_condition contents contents1 result_0_1)
  (increment_pre_condition contents2)
  (increment_post_condition contents2 contents21 result_0_21)
  (decrement_pre_condition contents)
  (decrement_post_condition contents contents2 result_0_2)
  (decrement_pre_condition contents1)
  (decrement_post_condition contents1 contents12 result_0_12)
))
(define-fun bowtie () Bool (and  
   (= result_0_1 result_0_21)
   (= result_0_2 result_0_12)
      (states_equal contents12 contents21)
))
(assert (not (=> (or (and (> contents 0))) bowtie)))
(check-sat)
