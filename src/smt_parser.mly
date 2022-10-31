%{
  open Smt
%}

%token <string> STR
%token <string> SYMBOL
%token <string> SYMBOL_NEW
%token <string> SYMBOL_M1
%token <string> SYMBOL_M2
%token <int> ARG
%token <int> LITERAL

%token EOF
%token LP RP UNDERSCORE
%token INT BOOL ARRAY SET STRING BITVEC
%token TRUE FALSE
%token SUB MUL MOD DIV ABS
%token IMP EQ
%token LT GT LTE GTE
%token NOT
%token ADD AND OR
%token LET ITE
%token FORALL EXISTS

%start <ty> ty_top
%start <exp> exp_top
%start <(exp * exp) list> values_top
%start <unit> eof_top

%%

exp_top: e=exp { e }
ty_top:  t=ty { t }
values_top: LP l=list(value_pair) RP { l }
eof_top: EOF { () }

value_pair: LP e1=exp e2=exp RP { (e1, e2) }

ty:
  | INT  { TInt }
  | BOOL { TBool }
  | s=SYMBOL { TGeneric s }
  | STRING { TString }
  | LP ARRAY k=ty v=ty RP { TArray (k, v) }
  | LP SET k=ty RP { TSet k }
  | LP UNDERSCORE BITVEC w=lit RP { TBitVector w }

lit:
  | d=LITERAL { d }

exp:
  | LP b=bop e1=exp e2=exp RP { EBop (b, e1, e2) }
  | LP u=uop e=exp RP { EUop (u, e) }
  | LP l=lop el=nonempty_list(exp) RP { ELop (l, el) }
  | LP SUB el=nonempty_list(exp) RP { match el with [e1] -> EUop(Neg, e1) | [e1; e2] -> EBop(Sub, e1, e2) | _ -> failwith "Too many arguments with sub" }
  | LP f=SYMBOL el=nonempty_list(exp) RP { EFunc (f, el) }
  | LP FORALL LP bl=nonempty_list(tybinding) RP e=exp RP { EForall(bl, e) }
  | LP EXISTS LP bl=nonempty_list(tybinding) RP e=exp RP { EExists(bl, e) }

  | v=SYMBOL { EVar (Var v) }
  | v=SYMBOL_NEW { EVar (VarPost v) }
  | v=SYMBOL_M1 { EVar (VarM (true, v)) }
  | v=SYMBOL_M2 { EVar (VarM (false, v)) }

  | n=LITERAL  { EConst (CInt n) }
  | n=ARG { EArg n }
  | TRUE  { EConst (CBool true) }
  | FALSE { EConst (CBool false) }
  | s=STR { EConst (CString s) }
  | LP LET LP bl=nonempty_list(binding) RP e=exp RP { ELet (bl, e) }
  | LP ITE e1=exp e2=exp e3=exp RP { EITE (e1, e2, e3) }

bop:
  | MUL { Mul }
  | MOD { Mod }
  | DIV { Div }
  | ABS { Abs }
  | IMP { Imp }
  | EQ  { Eq }
  | LT  { Lt }
  | GT  { Gt }
  | LTE { Lte }
  | GTE { Gte }

uop:
  | NOT { Not }

lop:
  | ADD { Add }
  | AND { And }
  | OR  { Or }

binding:
  LP v=SYMBOL e=exp RP { (Var v, e) }

tybinding:
  LP v=SYMBOL t=ty RP { (Var v, t) }
