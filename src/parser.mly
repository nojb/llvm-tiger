%{
open Error
open Tabs

let pos i =
  Parsing.rhs_start_pos i

let mkexp d i =
  {
    edesc = d;
    epos = pos i;
  }

let mkvar d i =
  {
    vdesc = d;
    vpos = pos i;
  }

let mkid s i =
  {
    idesc = s;
    ipos = pos i;
  }
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
%token <int> INT
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
  { {edesc = Eunit; epos = Parsing.symbol_start_pos ()} }
  | expseq_tail
  { $1 }
  ;

expseq_tail:
  exp
  { $1 }
  | exp SEMI expseq_tail
  { mkexp (Eseq ($1, $3)) 1 }
  ;

pos_ident:
  IDENT
  { mkid $1 1 }
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

exp
: INT
    { mkexp (Eint $1) 1 }
  | STRING
    { mkexp (Estring $1) 1 }
  | NIL
    { mkexp Enil 1 }
  | var
    { mkexp (Evar $1) 1 }
  | MINUS exp %prec unary_op
    { mkexp (Ebinop (mkexp (Eint 0) 1, Op_sub, $2)) 1 }
  | exp LAND exp
    { mkexp (Eif ($1, $3, mkexp (Eint 0) 3)) 2 }
  | exp LOR exp
    { mkexp (Eif ($1, mkexp (Eint 1) 3, $3)) 2 }
  | exp PLUS exp
    { mkexp (Ebinop ($1, Op_add, $3)) 2 }
  | exp TIMES exp
    { mkexp (Ebinop ($1, Op_mul, $3)) 2 }
  | exp MINUS exp
    { mkexp (Ebinop ($1, Op_sub, $3)) 2 }
  | exp SLASH exp
    { mkexp (Ebinop ($1, Op_div, $3)) 2 }
  | exp EQ exp
    { mkexp (Ebinop ($1, Op_cmp Ceq, $3)) 2 }
  | exp NE exp
    { mkexp (Ebinop ($1, Op_cmp Cne, $3)) 2 }
  | exp LE exp
    { mkexp (Ebinop ($1, Op_cmp Cle, $3)) 2 }
  | exp LT exp
    { mkexp (Ebinop ($1, Op_cmp Clt, $3)) 2 }
  | exp GE exp
    { mkexp (Ebinop ($1, Op_cmp Cge, $3)) 2 }
  | exp GT exp
    { mkexp (Ebinop ($1, Op_cmp Cgt, $3)) 2 }
  | var COLONEQ exp
    { mkexp (Eassign ($1, $3)) 2 }
  | pos_ident LPAREN exp_comma_list RPAREN
    { mkexp (Ecall ($1, $3)) 1 }
  | LPAREN expseq RPAREN
    { $2 }
  | pos_ident LCURLY record_field_list RCURLY
    { mkexp (Emakerecord ($1, $3)) 1 }
  | var LBRACK exp RBRACK OF exp
    {
      match $1.vdesc with
      | Vsimple x -> mkexp (Emakearray (x, $3, $6)) 1
      | _ -> raise Parse_error
    }
  | IF exp THEN exp
    { mkexp (Eif ($2, $4, {edesc = Eunit; epos = Parsing.symbol_end_pos ()})) 1 }
  | IF exp THEN exp ELSE exp
    { mkexp (Eif ($2, $4, $6)) 1 }
  | WHILE exp DO exp
    { mkexp (Ewhile ($2, $4)) 1 }
  | FOR pos_ident COLONEQ exp TO exp DO exp
    { mkexp (Efor ($2, $4, $6, $8)) 1 }
  | BREAK
    { mkexp Ebreak 1 }
  | LET decs IN expseq END
    { List.fold_right (fun (p, d) e -> {edesc = Elet (d, e); epos = p}) $2 $4 }
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
      { mkvar (Vsimple $1) 1 }
  | var LBRACK exp RBRACK
    { mkvar (Vsubscript ($1, $3)) 2 }
  | var DOT pos_ident
    { mkvar (Vfield ($1, $3)) 2 }
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

optional_var_type
  : /* empty */
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
    {
      fname = $2;
      fargs = $4;
      frety = $6;
      fbody = $8
    }
  }
  ;

optional_rtyp_name:
  /* empty */
  { None }
  | COLON pos_ident
  { Some $2 }
  ;
