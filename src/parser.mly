%{
  open Error
  open Tabs

  let pos i =
    Parsing.rhs_start_pos i
%}

%token ARRAY OF
%token NIL BREAK
%token COLON COMMA
%token VAR FUNCTION TYPE
%token COLONEQ
%token LAND LOR
%token EQ NE LE LT GE GT
%token FOR WHILE TO DO
%token PLUS MINUS TIMES SLASH
%token SEMI
%token DOT
%token LET IN END
%token IF THEN ELSE
%token LCURLY RCURLY
%token LBRACK RBRACK
%token LPAREN RPAREN
%token <int32> INT32
%token <string> IDENT
%token <string> STRING
%token EOF

%type <Tabs.exp> program
%start program

%left THEN
%left ELSE
%nonassoc COLONEQ
%left OF DO
%left LOR
%left LAND
%nonassoc LE GE EQ NE GT LT
%left PLUS MINUS
%left TIMES SLASH
%right unary_op

%%

program:
  exp EOF
  { $1 }
  | error
  { raise (Error (Parsing.symbol_start_pos (), "parse error")) }
  ;

expseq:
  /* empty */
  { Eunit (Parsing.symbol_start_pos ()) }
  | expseq_tail
  { $1 }
  ;

expseq_tail:
  exp
  { $1 }
  | exp SEMI expseq_tail
  { Eseq (pos 1, $1, $3) }
  ;

pos_ident:
  IDENT
  { { s = $1; p = pos 1 } }
  ;

record_field_list:
  /* empty */
  { [] }
  | record_field_list_tail
  { $1 }
  ;

record_field_list_tail:
  pos_ident EQ exp
  { [($1, $3)] }
  | pos_ident EQ exp COMMA record_field_list_tail
  { ($1, $3) :: $5 }
  ;

exp:
    INT32
  { Eint (pos 1, $1) }
  | STRING
  { Estring (pos 1, $1) }
  | NIL
  { Enil (pos 1) }
  | var
  { Evar (pos 1, $1) }
  | MINUS exp %prec unary_op
  { Ebinop (pos 1, Eint (pos 1, 0l), Op_sub, $2) }
  | exp LAND exp
  { Eif (pos 2, $1, $3, Eint (pos 3, 0l)) }
  | exp LOR exp
  { Eif (pos 2, $1, Eint (pos 3, 1l), $3) }
  | exp PLUS exp
  { Ebinop (pos 2, $1, Op_add, $3) }
  | exp TIMES exp
  { Ebinop (pos 2, $1, Op_mul, $3) }
  | exp MINUS exp
  { Ebinop (pos 2, $1, Op_sub, $3) }
  | exp SLASH exp
  { Ebinop (pos 2, $1, Op_div, $3) }
  | exp EQ exp
  { Ebinop (pos 2, $1, Op_cmp Ceq, $3) }
  | exp NE exp
  { Ebinop (pos 2, $1, Op_cmp Cne, $3) }
  | exp LE exp
  { Ebinop (pos 2, $1, Op_cmp Cle, $3) }
  | exp LT exp
  { Ebinop (pos 2, $1, Op_cmp Clt, $3) }
  | exp GE exp
  { Ebinop (pos 2, $1, Op_cmp Cge, $3) }
  | exp GT exp
  { Ebinop (pos 2, $1, Op_cmp Cgt, $3) }
  | var COLONEQ exp
  { Eassign (pos 2, $1, $3) }
  | pos_ident LPAREN exp_comma_list RPAREN
  { Ecall (pos 1, $1, $3) }
  | LPAREN expseq RPAREN
  { $2 }
  | pos_ident LCURLY record_field_list RCURLY
  { Emakerecord (pos 1, $1, $3) }
  | var LBRACK exp RBRACK OF exp
  { match $1 with
    | Vsimple x -> Emakearray (pos 1, x, $3, $6)
    | _ -> raise Parse_error }
  | IF exp THEN exp
  { Eif (pos 1, $2, $4, Eunit (Parsing.symbol_end_pos ())) }
  | IF exp THEN exp ELSE exp
  { Eif (pos 1, $2, $4, $6) }
  | WHILE exp DO exp
  { Ewhile (pos 1, $2, $4) }
  | FOR pos_ident COLONEQ exp TO exp DO exp
  { Efor (pos 1, $2, $4, $6, $8) }
  | BREAK
  { Ebreak (pos 1) }
  | LET decs IN expseq END
  { List.fold_right (fun (p, d) e -> Elet (p, d, e)) $2 $4 }
  ;

exp_comma_list:
  /* empty */
  { [] }
| exp_comma_list_tail
  { $1 }
;

exp_comma_list_tail:
  exp
  { [$1] }
| exp COMMA exp_comma_list_tail
  { $1 :: $3 }
;

var:
    pos_ident
  { Vsimple $1 }
  | var LBRACK exp RBRACK
  { Vsubscript (pos 2, $1, $3) }
  | var DOT pos_ident
  { Vfield (pos 2, $1, $3) }
  ;

decs:
    vardec decs_vtf
  { let (x, y, e) = $1 in (pos 1, Dvar (x, y, e)) :: $2 }
  | typdecs decs_vf
  { (pos 1, Dtypes $1) :: $2 }
  | fundec_list decs_vt
  { (pos 1, Dfuns $1) :: $2 }
  ;

decs_vtf:
    /* empty */
  { [] }
  | vardec decs_vtf
  { let (x, y, e) = $1 in (pos 1, Dvar (x, y, e)) :: $2 }
  | typdecs decs_vf
  { (pos 1, Dtypes $1) :: $2 }
  | fundec_list decs_vt
  { (pos 1, Dfuns $1) :: $2 }
  ;

decs_vf:
    /* empty */
  { [] }
  | vardec decs_vtf
  { let (x, y, e) = $1 in (pos 1, Dvar (x, y, e)) :: $2 }
  | fundec_list decs_vt
  { (pos 1, Dfuns $1) :: $2 }
  ;

decs_vt:
    /* empty */
  { [] }
  | vardec decs_vtf
  { let (x, y, e) = $1 in (pos 1, Dvar (x, y, e)) :: $2 }
  | typdecs decs_vf
  { (pos 1, Dtypes $1) :: $2 }
  ;

vardec:
  VAR pos_ident optional_var_type COLONEQ exp
  { ($2, $3, $5) }
  ;

optional_var_type:
  /* empty */
  { None }
  | COLON pos_ident
  { Some $2 }
  ;

typdecs:
  TYPE pos_ident EQ typ
  { [($2, $4)] }
  | TYPE pos_ident EQ typ typdecs
  { ($2, $4) :: $5 }
  ;

type_field_list:
  /* empty */
  { [] }
  | type_field_list_tail
  { $1 }
  ;

type_field_list_tail:
  pos_ident COLON pos_ident
  { [($1, $3)] }
  | pos_ident COLON pos_ident COMMA type_field_list_tail
  { ($1, $3) :: $5 }
  ;

typ:
    pos_ident
  { Tname $1 }
  | ARRAY OF pos_ident
  { Tarray $3 }
  | LCURLY type_field_list RCURLY
  { Trecord ($2) }
  ;

fundec_list:
  fundec
    { [$1] }
|  fundec fundec_list
{ $1 :: $2 }
;

fundec:
  FUNCTION pos_ident LPAREN type_field_list RPAREN
    optional_rtyp_name EQ exp
  {
    { fn_name = $2; fn_args = $4;
      fn_rtyp = $6; fn_body = $8 }
  }
  ;

optional_rtyp_name:
  /* empty */
  { None }
  | COLON pos_ident
  { Some $2 }
  ;
