;;; valid((=> (and oper (not (= (mod (+ x y) n) n)) (= n y) (= (mod (+ x y) n) 2) (not (= (mod (+ x y) n) (* 2 x))) (not (= (mod (+ x y) n) y)) (= (mod (+ x y) n) x) (not (= n (mod (+ x y) n))) (not (= n (+ x y))) (not (= n 2)) (= n (* 2 x))) bowtie)):
(set-logic ALL)
;; BEGIN: specToSmtDef( test )

(define-fun states_equal
  ( (n_1 Int)
    (y_1 Int)
    (x_1 Int)
    (err_1 Bool)
    (n_2 Int)
    (y_2 Int)
    (x_2 Int)
    (err_2 Bool) )
  Bool
  (or (and err_1 err_2) (and (not err_1) (not err_2)
  (and ( = n_1 n_2)( = y_1 y_2)( = x_1 x_2))
  
  ))
 )

(define-fun dummyMethod_1_pre_condition
  ( (n Int)
    (y Int)
    (x Int)
    (err Bool) )
  Bool
  true
 )

(define-fun dummyMethod_1_post_condition
  ( (n Int)
    (y Int)
    (x Int)
    (err Bool)
    (n_new Int)
    (y_new Int)
    (x_new Int)
    (err_new Bool)
    (result Bool) )
  Bool
  (or (and err err_new)
      (and (not err) (not err_new) true
   (and (let (( x_1 ( mod ( + x y ) n )))( = x_new x_1 ))(= result true))
  )
      (and (not err) err_new (not true
  )))
 )

(define-fun dummyMethod_2_pre_condition
  ( (n Int)
    (y Int)
    (x Int)
    (err Bool) )
  Bool
  true
 )

(define-fun dummyMethod_2_post_condition
  ( (n Int)
    (y Int)
    (x Int)
    (err Bool)
    (n_new Int)
    (y_new Int)
    (x_new Int)
    (err_new Bool)
    (result Bool) )
  Bool
  (or (and err err_new)
      (and (not err) (not err_new) 
  true
   
  (and (let (( x_1 ( * 2 x )))( = x_new x_1 ))(= result true))
  )
      (and (not err) err_new (not 
  true
  )))
 )

;; END: specToSmtDef( test )
(declare-fun n () Int)
(declare-fun n1 () Int)
(declare-fun n2 () Int)
(declare-fun n12 () Int)
(declare-fun n21 () Int)
(declare-fun y () Int)
(declare-fun y1 () Int)
(declare-fun y2 () Int)
(declare-fun y12 () Int)
(declare-fun y21 () Int)
(declare-fun x () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x12 () Int)
(declare-fun x21 () Int)
(declare-fun err () Bool)
(declare-fun err1 () Bool)
(declare-fun err2 () Bool)
(declare-fun err12 () Bool)
(declare-fun err21 () Bool)
(declare-fun result1 () Bool)
(declare-fun result21 () Bool)
(declare-fun result2 () Bool)
(declare-fun result12 () Bool)
(define-fun oper () Bool (and 
  (dummyMethod_1_pre_condition n y x err)
  (dummyMethod_1_post_condition n y x err n1 y1 x1 err1 result1)
  (dummyMethod_1_pre_condition n2 y2 x2 err2)
  (dummyMethod_1_post_condition n2 y2 x2 err2 n21 y21 x21 err21 result21)
  (dummyMethod_2_pre_condition n y x err)
  (dummyMethod_2_post_condition n y x err n2 y2 x2 err2 result2)
  (dummyMethod_2_pre_condition n1 y1 x1 err1)
  (dummyMethod_2_post_condition n1 y1 x1 err1 n12 y12 x12 err12 result12)
  (or (not err12) (not err21))))
(define-fun bowtie () Bool (and 
   (= result1 result21)
   (= result2 result12)
      (states_equal n12 y12 x12 err12 n21 y21 x21 err21)
))
(assert (not (=> (and oper (not (= (mod (+ x y) n) n)) (= n y) (= (mod (+ x y) n) 2) (not (= (mod (+ x y) n) (* 2 x))) (not (= (mod (+ x y) n) y)) (= (mod (+ x y) n) x) (not (= n (mod (+ x y) n))) (not (= n (+ x y))) (not (= n 2)) (= n (* 2 x))) bowtie)))
(check-sat)
(get-model)
(get-value ((= (mod (+ x y) n) (+ x y)) (= n x) (= (+ x y) (mod (+ x y) n)) (= (+ x y) n) (= (+ x y) 2) (= (+ x y) (* 2 x)) (= (+ x y) y) (= (+ x y) x) (= 2 (mod (+ x y) n)) (= 2 n) (= 2 (+ x y)) (= 2 (* 2 x)) (= 2 y) (= 2 x) (= (* 2 x) (mod (+ x y) n)) (= (* 2 x) n) (= (* 2 x) (+ x y)) (= (* 2 x) 2) (= (* 2 x) y) (= (* 2 x) x) (= y (mod (+ x y) n)) (= y n) (= y (+ x y)) (= y 2) (= y (* 2 x)) (= y x) (= x (mod (+ x y) n)) (= x n) (= x (+ x y)) (= x 2) (= x (* 2 x)) (= x y)))
