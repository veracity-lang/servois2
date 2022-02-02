%{
  open Smt
%}

%token <float> FLOAT
%token <string> SYMBOL
%token <string> SYMBOL_NEW

%token EOF
%token LP RP
%token INT BOOL ARRAY SET
%token TRUE FALSE
%token SUB MUL MOD DIV ABS
%token IMP EQ
%token LT GT LTE GTE
%token NOT
%token ADD AND OR
%token LET ITE

%start <ty> ty_top
%start <exp> exp_top
%start <(exp * exp) list> values_top

%%

exp_top: e=exp EOF { e }
ty_top:  t=ty EOF  { t }
values_top: LP l=list(value_pair) RP { l }

value_pair: LP e1=exp e2=exp RP { (e1, e2) }

ty:
  | INT  { TInt }
  | BOOL { TBool }
  | s=SYMBOL { TGeneric s }
  | LP ARRAY k=ty v=ty RP { TArray (k, v) }
  | LP SET k=ty RP { TSet k }

exp:
  | LP b=bop e1=exp e2=exp RP { EBop (b, e1, e2) }
  | LP u=uop e=exp RP { EUop (u, e) }
  | LP l=lop el=nonempty_list(exp) RP { ELop (l, el) }
  | LP f=SYMBOL el=nonempty_list(exp) RP { EFunc (f, el) }
  | v=SYMBOL { EVar (Var v) }
  | v=SYMBOL_NEW { EVar (VarPost v) }
  | n=FLOAT  { EConst (CInt (int_of_float n)) }
  | TRUE  { EConst (CBool true) }
  | FALSE { EConst (CBool false) }
  | LP LET LP bl=nonempty_list(binding) RP e=exp RP { ELet (bl, e) }
  | LP ITE e1=exp e2=exp e3=exp { EITE (e1, e2, e3) }

bop:
  | SUB { Sub }
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