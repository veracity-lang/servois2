(set-logic ALL)
;; BEGIN: smt_of_spec stack_test

(declare-datatypes ((list 0))
  (((cons (head Int) (tail list)) (nil))))

(define-fun states_equal
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list) )
  Bool
  (or err (ite (= size 0) (= list_memory nil) (ite (= size 1) (and (= x0 (head list_memory)) (= (tail list_memory) nil)) (ite (= size 2) (and (= x0 (head list_memory)) (= x1 (head (tail list_memory))) (= (tail (tail list_memory)) nil)) (and (= x0 (head list_memory)) (= x1 (head (tail list_memory))) (= x2 (head (tail (tail list_memory)))) (= (tail (tail (tail list_memory))) nil))))))
)

(define-fun pop_pre_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list) )
  Bool
  true
)

(define-fun pop_post_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list)
    (err_new Bool)
    (x0_new Int)
    (x1_new Int)
    (x2_new Int)
    (size_new Int)
    (list_memory_new list)
    (val Int) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (> size 0) (and (= size_new (- size 1)) (= list_memory_new list_memory) (ite (= size 1) (and (= val x0) (= x0_new x0) (= x1_new x1) (= x2_new x2)) (ite (= size 2) (and (= val x1) (= x0_new x0) (= x1_new x1) (= x2_new x2)) (ite (= size 3) (and (= val x2) (= x0_new x0) (= x1_new x1) (= x2_new x2)) true))))) (and (not err) err_new (not (> size 0))))
)

(define-fun pop_list_impl_pre_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list) )
  Bool
  true
)

(define-fun pop_list_impl_post_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list)
    (err_new Bool)
    (x0_new Int)
    (x1_new Int)
    (x2_new Int)
    (size_new Int)
    (list_memory_new list)
    (val Int) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (not (= list_memory nil)) (and (= val (head list_memory)) (= list_memory_new (tail list_memory)) (= x0_new x0) (= x1_new x1) (= x2_new x2) (= size_new size))) (and (not err) err_new (not (not (= list_memory nil)))))
)

;; END: smt_of_spec stack_test
(declare-fun err_l0 () Bool)
(declare-fun err_l1 () Bool)
(declare-fun err_l2 () Bool)
(declare-fun x0_l0 () Int)
(declare-fun x0_l1 () Int)
(declare-fun x0_l2 () Int)
(declare-fun x1_l0 () Int)
(declare-fun x1_l1 () Int)
(declare-fun x1_l2 () Int)
(declare-fun x2_l0 () Int)
(declare-fun x2_l1 () Int)
(declare-fun x2_l2 () Int)
(declare-fun size_l0 () Int)
(declare-fun size_l1 () Int)
(declare-fun size_l2 () Int)
(declare-fun list_memory_l0 () list)
(declare-fun list_memory_l1 () list)
(declare-fun list_memory_l2 () list)
(declare-fun result_0_l1 () Int)
(declare-fun result_0_l2 () Int)

(define-fun oper () Bool (and 
  (= err_l0 false)
  (pop_pre_condition err_l0 x0_l0 x1_l0 x2_l0 size_l0 list_memory_l0)
  (pop_post_condition err_l0 x0_l0 x1_l0 x2_l0 size_l0 list_memory_l0 err_l1 x0_l1 x1_l1 x2_l1 size_l1 list_memory_l1 result_0_l1)
  (pop_list_impl_pre_condition err_l1 x0_l1 x1_l1 x2_l1 size_l1 list_memory_l1)
  (pop_list_impl_post_condition err_l1 x0_l1 x1_l1 x2_l1 size_l1 list_memory_l1 err_l2 x0_l2 x1_l2 x2_l2 size_l2 list_memory_l2 result_0_l2)
))

(define-fun bowtie () Bool (and
   (states_equal err_l1 x0_l1 x1_l1 x2_l1 size_l1 list_memory_l1)
))

(assert (not (=> (and oper true) (not bowtie))))
(check-sat)
(get-model)
