(set-logic ALL_SUPPORTED)
;; BEGIN: smt_of_spec counter

(define-fun states_equal
  ( contents Int
    contents_new Int )
  Bool
  (= contents contents_new)
 )

(define-fun increment_pre_condition
  ( contents Int )
  Bool
  (>= contents 0)
 )

(define-fun increment_post_condition
  ( contents Int
    contents_new Int )
  Bool
  (and (= contents_new (+ contents 1)) (= result true))
 )

(define-fun decrement_pre_condition
  ( contents Int )
  Bool
  (>= contents 1)
 )

(define-fun decrement_post_condition
  ( contents Int
    contents_new Int )
  Bool
  (and (= contents_new (- contents 1)) (= result true))
 )

(define-fun reset_pre_condition
  ( contents Int )
  Bool
  (>= contents 0)
 )

(define-fun reset_post_condition
  ( contents Int
    contents_new Int )
  Bool
  (and (= contents_new 0) (= result true))
 )

(define-fun zero_pre_condition
  ( contents Int )
  Bool
  (>= contents 0)
 )

(define-fun zero_post_condition
  ( contents Int
    contents_new Int )
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
  (increment_pre_condition result1 contents contents1)
  (increment_pre_condition contents2)
  (increment_pre_condition result21 contents2 contents21)
  (decrement_pre_condition contents)
  (decrement_pre_condition result2 contents contents2)
  (decrement_pre_condition contents1)
  (decrement_pre_condition result12 contents1 contents12)
))
(define-fun bowtie () Bool (and ( 
   (= result_1_1 result_121)
   (= result_1_2 result_112)
      (states_equal contents12 contents21)
))
(assert (not (=> (or false) bowtie)))
(check-sat)