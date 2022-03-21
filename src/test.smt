(set-logic ALL)
;; BEGIN: smt_of_spec HashTable

(declare-sort E 0)
(declare-sort F 0)

(define-fun postcondition
  ( (err Bool)
    (keys (Set E))
    (H (Array E F))
    (size Int)
    (rd_param E)
    (rd_return F)
    (err_new Bool)
    (keys_new (Set E))
    (H_new (Array E F))
    (size_new Int)
    (rd_param_new E)
    (rd_return_new F) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (and (= rd_param rd_param_new) (= rd_return rd_return_new))))
)

(define-fun get_pre_condition
  ( (err Bool)
    (keys (Set E))
    (H (Array E F))
    (size Int)
    (rd_param E)
    (rd_return F) )
  Bool
  true
)

(define-fun get_post_condition
  ( (err Bool)
    (keys (Set E))
    (H (Array E F))
    (size Int)
    (rd_param E)
    (rd_return F)
    (err_new Bool)
    (keys_new (Set E))
    (H_new (Array E F))
    (size_new Int)
    (rd_param_new E)
    (rd_return_new F)
    (result F) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (member rd_param keys) (and (= keys_new keys) (= H_new H) (= size_new size) (= (select H rd_param) result) (= result rd_return))) (and (not err) err_new (not (member rd_param keys))))
)

;; END: smt_of_spec HashTable
(declare-fun err_l0 () Bool)
(declare-fun err_r0 () Bool)
(declare-fun err_l1 () Bool)
(declare-fun err_r1 () Bool)
(declare-fun keys_l0 () (Set E))
(declare-fun keys_r0 () (Set E))
(declare-fun keys_l1 () (Set E))
(declare-fun keys_r1 () (Set E))
(declare-fun H_l0 () (Array E F))
(declare-fun H_r0 () (Array E F))
(declare-fun H_l1 () (Array E F))
(declare-fun H_r1 () (Array E F))
(declare-fun size_l0 () Int)
(declare-fun size_r0 () Int)
(declare-fun size_l1 () Int)
(declare-fun size_r1 () Int)
(declare-fun beta_pre () (Set E))
(declare-fun beta_post () (Set E))
(declare-fun rd_param_l0 () E)
(declare-fun rd_param_r0 () E)
(declare-fun rd_param_l1 () E)
(declare-fun rd_param_r1 () E)
(declare-fun rd_return_l0 () F)
(declare-fun rd_return_r0 () F)
(declare-fun rd_return_l1 () F)
(declare-fun rd_return_r1 () F)
(declare-fun result_0_l1 () F)
(declare-fun result_0_r1 () F)

(define-fun oper () Bool (and
  (get_pre_condition err_l0 keys_l0 H_l0 size_l0 rd_param_l0 rd_return_l0)
  (get_post_condition err_l0 keys_l0 H_l0 size_l0 rd_param_l0 rd_return_l0 err_l1 keys_l1 H_l1 size_l1 rd_param_l1 rd_return_l1 result_0_l1)
  (get_pre_condition err_r0 keys_r0 H_r0 size_r0 rd_param_r0 rd_return_r0)
  (get_post_condition err_r0 keys_r0 H_r0 size_r0 rd_param_r0 rd_return_r0 err_r1 keys_r1 H_r1 size_r1 rd_param_r1 rd_return_r1 result_0_r1)
  (and (not err_l0) (not err_r0))
  (or (not err_l1) (not err_r1))
))

(define-fun beta_coherence ((beta (Set E)) (H_l (Array E F)) (H_r (Array E F))) Bool 
    (forall ((e E)) 
        (ite (member e beta) 
            true
            (= (select H_l e) (select H_r e))
        )
    )
)

(define-fun postcondition_inst () Bool (and
   (postcondition err_l1 keys_l1 H_l1 size_l1 rd_param_l1 rd_return_l1 err_r1 keys_r1 H_r1 size_r1 rd_param_r1 rd_return_r1)
   (beta_coherence beta_post H_l1 H_r1)
))

(define-fun precondition () Bool 
    (and 
        (= rd_param_l0 rd_param_r0)
        ;; (= rd_return_l0 rd_return_r0)
        (not (member rd_param_l0 beta_pre))
        (beta_coherence beta_pre H_l0 H_r0)
    )
)

(assert (not (=> (and oper precondition) postcondition_inst)))
(check-sat)
