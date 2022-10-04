
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
    (list_memory list)
    (get_return Int)
    (err_new Bool)
    (x0_new Int)
    (x1_new Int)
    (x2_new Int)
    (size_new Int)
    (list_memory_new list)
    (get_return_new Int) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (ite (= size 0) (= list_memory_new nil) (ite (= size 1) (and (= x0 (head list_memory_new)) (= (tail list_memory_new) nil)) (ite (= size 2) (and (= x1 (head list_memory_new)) (= x0 (head (tail list_memory_new))) (= (tail (tail list_memory_new)) nil)) (and (= x2 (head list_memory_new)) (= x1 (head (tail list_memory_new))) (= x0 (head (tail (tail list_memory_new)))) (= (tail (tail (tail list_memory_new))) nil)))))))
)

(define-fun pop_pre_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list)
    (get_return Int) )
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
    (get_return Int)
    (err_new Bool)
    (x0_new Int)
    (x1_new Int)
    (x2_new Int)
    (size_new Int)
    (list_memory_new list)
    (get_return_new Int)
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
    (list_memory list)
    (get_return Int) )
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
    (get_return Int)
    (err_new Bool)
    (x0_new Int)
    (x1_new Int)
    (x2_new Int)
    (size_new Int)
    (list_memory_new list)
    (get_return_new Int)
    (val Int) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (not (= list_memory nil)) (and (= val (head list_memory)) (= list_memory_new (tail list_memory)) (= x0_new x0) (= x1_new x1) (= x2_new x2) (= size_new size))) (and (not err) err_new (not (not (= list_memory nil)))))
)

(define-fun get_pre_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list)
    (get_return Int)
    (index Int) )
  Bool
  true
)

(define-fun get_post_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list)
    (get_return Int)
    (index Int)
    (err_new Bool)
    (x0_new Int)
    (x1_new Int)
    (x2_new Int)
    (size_new Int)
    (list_memory_new list)
    (get_return_new Int)
    (val Int) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (and (< index size) (>= index 0)) (and (= size_new size) (= list_memory_new list_memory) (= x0_new x0) (= x1_new x1) (= x2_new x2) (ite (= index 0) (= get_return x0) (ite (= index 1) (= get_return x1) (ite (= index 2) (= get_return x2) true))))) (and (not err) err_new (not (and (< index size) (>= index 0)))))
)

(define-fun get_impl_pre_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list)
    (get_return Int)
    (index Int) )
  Bool
  true
)

(define-fun get_impl_post_condition
  ( (err Bool)
    (x0 Int)
    (x1 Int)
    (x2 Int)
    (size Int)
    (list_memory list)
    (get_return Int)
    (index Int)
    (err_new Bool)
    (x0_new Int)
    (x1_new Int)
    (x2_new Int)
    (size_new Int)
    (list_memory_new list)
    (get_return_new Int)
    (val Int) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (and (< index size) (>= index 0)) (and (= size_new size) (= list_memory_new list_memory) (= x0_new x0) (= x1_new x1) (= x2_new x2) (ite (= index 0) (= get_return (head list_memory)) (ite (= index 1) (= get_return (head (tail list_memory))) (ite (= index 2) (= get_return (head (tail (tail list_memory)))) true))))) (and (not err) err_new (not (and (< index size) (>= index 0)))))
)

;; END: smt_of_spec stack_test
(declare-fun m1_index () Int)
(declare-fun m2_index () Int)
(declare-fun err_l0 () Bool)
(declare-fun err_r0 () Bool)
(declare-fun err_l1 () Bool)
(declare-fun err_r1 () Bool)
(declare-fun x0_l0 () Int)
(declare-fun x0_r0 () Int)
(declare-fun x0_l1 () Int)
(declare-fun x0_r1 () Int)
(declare-fun x1_l0 () Int)
(declare-fun x1_r0 () Int)
(declare-fun x1_l1 () Int)
(declare-fun x1_r1 () Int)
(declare-fun x2_l0 () Int)
(declare-fun x2_r0 () Int)
(declare-fun x2_l1 () Int)
(declare-fun x2_r1 () Int)
(declare-fun size_l0 () Int)
(declare-fun size_r0 () Int)
(declare-fun size_l1 () Int)
(declare-fun size_r1 () Int)
(declare-fun list_memory_l0 () list)
(declare-fun list_memory_r0 () list)
(declare-fun list_memory_l1 () list)
(declare-fun list_memory_r1 () list)
(declare-fun get_return_l0 () Int)
(declare-fun get_return_r0 () Int)
(declare-fun get_return_l1 () Int)
(declare-fun get_return_r1 () Int)
(declare-fun result_0_l1 () Int)
(declare-fun result_0_r1 () Int)

(define-fun oper () Bool (and 
  (get_pre_condition err_l0 x0_l0 x1_l0 x2_l0 size_l0 list_memory_l0 get_return_l0 m1_index)
  (get_post_condition err_l0 x0_l0 x1_l0 x2_l0 size_l0 list_memory_l0 get_return_l0 m1_index err_l1 x0_l1 x1_l1 x2_l1 size_l1 list_memory_l1 get_return_l1 result_0_l1)
  (get_impl_pre_condition err_r0 x0_r0 x1_r0 x2_r0 size_r0 list_memory_r0 get_return_r0 m2_index)
  (get_impl_post_condition err_r0 x0_r0 x1_r0 x2_r0 size_r0 list_memory_r0 get_return_r0 m2_index err_r1 x0_r1 x1_r1 x2_r1 size_r1 list_memory_r1 get_return_r1 result_0_r1)
  (and (not err_l0) (not err_r0))
  (or (not err_l1) (not err_r1))
(= err_l0 err_r0)
))

(define-fun bowtie () Bool (and
   (states_equal err_l1 x0_l1 x1_l1 x2_l1 size_l1 list_memory_l1 get_return_l1 err_r1 x0_r1 x1_r1 x2_r1 size_r1 list_memory_r1 get_return_r1)
))

(assert (not (=> (and oper (and true (and (= m1_index m2_index) (<= size_l0 3) (>= size_l0 0) (ite (= size_l0 0) (= list_memory_r0 nil) (ite (= size_l0 1) (and (= x0_l0 (head list_memory_r0)) (not (= list_memory_r0 nil)) (= (tail list_memory_r0) nil)) (ite (= size_l0 2) (and (not (= list_memory_r0 nil)) (not (= (tail list_memory_r0) nil)) (= x1_l0 (head list_memory_r0)) (= x0_l0 (head (tail list_memory_r0))) (= (tail (tail list_memory_r0)) nil)) (and (not (= list_memory_r0 nil)) (not (= (tail list_memory_r0) nil)) (not (= (tail (tail list_memory_r0)) nil)) (= x2_l0 (head list_memory_r0)) (= x1_l0 (head (tail list_memory_r0))) (= x0_l0 (head (tail (tail list_memory_r0)))) (= (tail (tail (tail list_memory_r0))) nil)))))))) bowtie)))
(check-sat)

(get-model)
