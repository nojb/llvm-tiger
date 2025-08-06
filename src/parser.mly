%{
open Tabs
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
%token <int64> INT
%token <string> IDENT
%token <string> STRING
%token EOF

%start <Tabs.program> program

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

program: exp EOF { {name = ""; body = $1} }
;

%inline ident: loc(IDENT) { $1 }
;

%inline binary_operation:
| PLUS  { Op_add }
| TIMES { Op_mul }
| MINUS { Op_sub }
| SLASH { Op_div }
| EQ    { Op_cmp Ceq }
| NE    { Op_cmp Cne }
| LE    { Op_cmp Cle }
| LT    { Op_cmp Clt }
| GE    { Op_cmp Cge }
| GT    { Op_cmp Cgt }
;

%inline loc(X): X { {desc = $1; loc = $symbolstartpos} }
;

%inline exp: loc(exp_) { $1 }
;

exp_:
| INT                                                 { Eint $1 }
| STRING                                              { Estring $1 }
| NIL                                                 { Enil }
| MINUS exp %prec unary_op                            { Ebinop ({desc = Eint 0L; loc = $2.loc}, Op_sub, $2) }
| exp LAND exp                                        { Eif ($1, $3, Some {desc = Eint 0L; loc = $1.loc}) }
| exp LOR exp                                         { Eif ($1, {desc = Eint 1L; loc = $1.loc}, Some $3) }
| exp binary_operation exp                            { Ebinop ($1, $2, $3) }
| ident LPAREN separated_list(COMMA, exp) RPAREN      { Ecall ($1, $3) }
| LPAREN separated_list(SEMI, exp) RPAREN             { Eseq $2 }
| ident LCURLY separated_list(COMMA, separated_pair(ident, EQ, exp)) RCURLY
  { Erecord ($1, $3) }
| var                                                 { Evar $1 }
| var COLONEQ exp                                     { Eassign ($1, $3) }
| var LBRACK exp RBRACK OF exp
  { match $1.desc with
    | Vsimple x -> Earray (x, $3, $6)
    | _ -> assert false
  }
| IF exp THEN exp ioption(preceded(ELSE, exp))        { Eif ($2, $4, $5) }
| WHILE exp DO exp                                    { Ewhile ($2, $4) }
| FOR ident COLONEQ exp TO exp DO exp                 { Efor ($2, $4, $6, $8) }
| BREAK                                               { Ebreak }
| LET nonempty_list(dec) IN loc(separated_list(SEMI, exp)) END { Elet ($2, {$4 with desc = Eseq $4.desc}) }
;

%inline var: loc(var_) { $1 }
;

var_:
| ident                 { Vsimple $1 }
| var LBRACK exp RBRACK { Vsubscript ($1, $3) }
| var DOT ident         { Vfield ($1, $3) }
;

dec:
| VAR ident option(preceded(COLON, ident)) COLONEQ exp { Dvar ($2, $3, $5) }
| TYPE ident EQ typ                                    { Dtype ($2, $4) }
| FUNCTION ident
  LPAREN separated_list(COMMA, separated_pair(ident, COLON, ident)) RPAREN
  option(preceded(COLON, ident)) EQ exp
  { Dfun {fn_name = $2; fn_args = $4; fn_rtyp = $6; fn_body = $8} }
;

typ:
| ident                                                                    { Tname $1 }
| ARRAY OF ident                                                           { Tarray $3 }
| LCURLY separated_list(COMMA, separated_pair(ident, COLON, ident)) RCURLY { Trecord $2 }
;

