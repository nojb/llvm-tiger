%{
  open Globals
  open Parsetree

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
%token <int> INT
%token <string> IDENT
%token <string> STRING
%token EOF

%type <Parsetree.exp> program
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
  ;

expseq:
  /* empty */
  | expseq_tail
  { $1 }
  ;

expseq_tail:
  exp
  { [$1] }
  | exp SEMI expseq_tail
  { $1 :: $3 }
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
    INT
  { Pint (pos 1, $1) }
  | STRING
  { Pstring (pos 1, $1) }
  | NIL
  { Pnil (pos 1) }
  | var
  { Pvar (pos 1, $1) }
  | MINUS exp %prec unary_op
  { Pbinop (pos 1, Pint (pos 1, 0), Op_sub, $2) }
  | exp LAND exp
  { Pif (pos 2, $1, $3, Some (Pint (pos 3, 0))) }
  | exp LOR exp
  { Pif (pos 2, $1, Pint (pos 3, 1), Some $3) }
  | exp PLUS exp
  { Pbinop (pos 2, $1, Op_add, $3) }
  | exp TIMES exp
  { Pbinop (pos 2, $1, Op_mul, $3) }
  | exp MINUS exp
  { Pbinop (pos 2, $1, Op_sub, $3) }
  | exp SLASH exp
  { Pbinop (pos 2, $1, Op_div, $3) }
  | exp EQ exp
  { Pbinop (pos 2, $1, Op_cmp Ceq, $3) }
  | exp NE exp
  { Pbinop (pos 2, $1, Op_cmp Cne, $3) }
  | exp LE exp
  { Pbinop (pos 2, $1, Op_cmp Cle, $3) }
  | exp LT exp
  { Pbinop (pos 2, $1, Op_cmp Clt, $3) }
  | exp GE exp
  { Pbinop (pos 2, $1, Op_cmp Cge, $3) }
  | exp GT exp
  { Pbinop (pos 2, $1, Op_cmp Cgt, $3) }
  | var COLONEQ exp
  { Passign (pos 2, $1, $3) }
  | pos_ident LPAREN exp_comma_list RPAREN
  { Pcall (pos 1, $1, $3) }
  | LPAREN expseq RPAREN
  { Pseq (pos 1, $2) }
  | pos_ident LCURLY record_field_list RCURLY
  { Pmakerecord (pos 1, $1, $3) }
  | var LBRACK exp RBRACK OF exp
  { match $1 with
    | PVsimple x -> Pmakearray (pos 1, x, $3, $6)
    | _ -> raise Parse_error }
  | IF exp THEN exp
  { Pif (pos 1, $2, $4, None) }
  | IF exp THEN exp ELSE exp
  { Pif (pos 1, $2, $4, Some $6) }
  | WHILE exp DO exp
  { Pwhile (pos 1, $2, $4) }
  | FOR pos_ident COLONEQ exp TO exp DO exp
  { Pfor (pos 1, $2, $4, $6, $8) }
  | BREAK
  { Pbreak (pos 1) }
  | LET letexp
  { $2 }
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
  { PVsimple $1 }
  | var LBRACK exp RBRACK
  { PVsubscript (pos 2, $1, $3) }
  | var DOT pos_ident
  { PVfield (pos 2, $1, $3) }
  ;

letexp:
    vardec letexp2
  { let (x, y, e) = $1 in Pletvar (pos 1, x, y, e, $2) }
  | typdecs letexp2
  { Plettype (pos 1, $1, $2) }
  | fundec_list letexp2
  { Pletfuns (pos 1, $1, $2) }
  ;

letexp2:
    letexp
  { $1 }
  | IN expseq END
  { Pseq (pos 2, $2) }
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
  TYPE IDENT EQ typ
  { [($2, $4)] }
  | TYPE IDENT EQ typ typdecs
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
  { PTname $1 }
  | ARRAY OF pos_ident
  { PTarray $3 }
  | LCURLY type_field_list RCURLY
  { PTrecord ($2) } 
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
