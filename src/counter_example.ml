open Spec
(*
# Counter data structure's abstract definition

name: counter

state:
  - name: contents
    type: Int

# states_equal:
#   definition: (= contents_1 contents_2)

methods:
  - name: increment
    args: []
    return:
      - name: result
        type: Bool
    requires: |
      (>= contents 0)
    ensures: |
      (and (= contents_new (+ contents 1))
           (= result true))
    terms:
      Int: [contents, 1, (+ contents 1)]
  - name: decrement
    args: []
    return:
      - name: result
        type: Bool
    requires: |
      (>= contents 1)
    ensures: |
      (and (= contents_new (- contents 1))
           (= result true))
    terms:
      Int: [contents, 1, (- contents 1), 0]
  - name: reset
    args: []
    return:
      - name: result
        type: Bool
    requires: |
      (>= contents 0)
    ensures: |
      (and (= contents_new 0)
           (= result true))
    terms:
      Int: [contents, 0]
  - name: zero
    args: []
    return:
      - name: result
        type: Bool
    requires: |
      (>= contents 0)
    ensures: |
      (and (= contents_new contents)
           (= result (= contents 0)))
    terms:
      Int: [contents, 0]

predicates:
  - name: "="
    type: [Int, Int] 
*)

let spec : spec =
  {name = "counter"; preds = [PredSig ("=", [TInt; TInt])];
  preamble = None;
 state_eq =
  EBop (Eq, EVar (Var "contents"),
   EVar (VarPost "contents"));
 precond = (EBop (Gte, EVar (Var "contents"), EConst (CInt 0)));
 state = [(Var "contents", TInt)];
 methods =
  [{Spec.name = "increment"; args = [];
    ret = [(Var "result", TBool)];
    pre = EBop (Gte, EVar (Var "contents"), EConst (CInt 0));
    post =
     ELop (And,
      [EBop (Eq, EVar (VarPost "contents"),
        ELop (Add, [EVar (Var "contents"); EConst (CInt 1)]));
       EBop (Eq, EVar (Var "result"), EConst (CBool true))]);
    terms =
     [(TInt,
       [EVar (Var "contents"); EConst (CInt 1);
        ELop (Add, [EVar (Var "contents"); EConst (CInt 1)])])]};
   {Spec.name = "decrement"; args = [];
    ret = [(Var "result", TBool)];
    pre = EBop (Gte, EVar (Var "contents"), EConst (CInt 1));
    post =
     ELop (And,
      [EBop (Eq, EVar (VarPost "contents"),
        EBop (Sub, EVar (Var "contents"), EConst (CInt 1)));
       EBop (Eq, EVar (Var "result"), EConst (CBool true))]);
    terms =
     [(TInt,
       [EVar (Var "contents"); EConst (CInt 1);
        EBop (Sub, EVar (Var "contents"), EConst (CInt 1));
        EConst (CInt 0)])]};
   {Spec.name = "reset"; args = []; ret = [(Var "result", TBool)];
    pre = EBop (Gte, EVar (Var "contents"), EConst (CInt 0));
    post =
     ELop (And,
      [EBop (Eq, EVar (VarPost "contents"), EConst (CInt 0));
       EBop (Eq, EVar (Var "result"), EConst (CBool true))]);
    terms = [(TInt, [EVar (Var "contents"); EConst (CInt 0)])]};
   {Spec.name = "zero"; args = []; ret = [(Var "result", TBool)];
    pre = EBop (Gte, EVar (Var "contents"), EConst (CInt 0));
    post =
     ELop (And,
      [EBop (Eq, EVar (VarPost "contents"),
        EVar (Var "contents"));
       EBop (Eq, EVar (Var "result"),
        EBop (Eq, EVar (Var "contents"), EConst (CInt 0)))]);
    terms = [(TInt, [EVar (Var "contents"); EConst (CInt 0)])]}
  ]}

