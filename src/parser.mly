%{
open Error
open Tabs

let pos i =
  Parsing.rhs_start_pos i

let mkexp i d =
  {edesc = d; epos = Parsing.rhs_start_pos i}

let mkvar i d =
  {vdesc = d; vpos = Parsing.rhs_start_pos i}
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

%type <Tabs.program> program
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
  exp EOF { {name = ""; body = $1} }
| error   { raise (Error (Parsing.symbol_start_pos (), "parse error")) }
;

expseq:
  /* empty */ { mkexp 1 Eunit }
| expseq_tail { $1 }
;

expseq_tail:
  exp                  { $1 }
| exp SEMI expseq_tail { mkexp 1 (Eseq ($1, $3)) }
;

ident:
  IDENT { {s = $1; p = pos 1} }
;

%inline binary_operation:
  PLUS  { Op_add }
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

exp:
  INT32                    { mkexp 1 (Eint $1) }
| STRING                   { mkexp 1 (Estring $1) }
| NIL                      { mkexp 1 Enil }
| MINUS exp %prec unary_op { mkexp 1 (Ebinop (mkexp 1 (Eint 0l), Op_sub, $2)) }
| exp LAND exp             { mkexp 2 (Eif ($1, $3, mkexp 3 (Eint 0l))) }
| exp LOR exp              { mkexp 2 (Eif ($1, mkexp 3 (Eint 1l), $3)) }
| exp binary_operation exp { mkexp 2 (Ebinop ($1, $2, $3)) }
| ident LPAREN separated_list(COMMA, exp) RPAREN
  { mkexp 1 (Ecall ($1, $3)) }
| LPAREN expseq RPAREN     { $2 }
| ident LCURLY separated_list(COMMA, separated_pair(ident, EQ, exp)) RCURLY
  { mkexp 1 (Emakerecord ($1, $3)) }
| var                                 { mkexp 1 (Evar $1) }
| var COLONEQ exp                     { mkexp 2 (Eassign ($1, $3)) }
| var LBRACK exp RBRACK OF exp
  { match $1.vdesc with
    | Vsimple x -> mkexp 1 (Emakearray (x, $3, $6))
    | _ -> assert false
  }
| IF exp THEN exp                     { mkexp 1 (Eif ($2, $4, {edesc = Eunit; epos = Parsing.symbol_end_pos ()})) }
| IF exp THEN exp ELSE exp            { mkexp 1 (Eif ($2, $4, $6)) }
| WHILE exp DO exp                    { mkexp 1 (Ewhile ($2, $4)) }
| FOR ident COLONEQ exp TO exp DO exp { mkexp 1 (Efor ($2, $4, $6, $8)) }
| BREAK                               { mkexp 1 Ebreak }
| LET list(dec) IN expseq END         { mkexp 1 (Elet ($2, $4)) }
;

var:
  ident                 { mkvar 1 (Vsimple $1) }
| var LBRACK exp RBRACK { mkvar 2 (Vsubscript ($1, $3)) }
| var DOT ident         { mkvar 2 (Vfield ($1, $3)) }
;

dec:
  VAR ident option(preceded(COLON, ident)) COLONEQ exp { Dvar ($2, $3, $5) }
| TYPE ident EQ typ                                    { Dtype ($2, $4) }
| FUNCTION ident
  LPAREN separated_list(COMMA, separated_pair(ident, COLON, ident)) RPAREN
  option(preceded(COLON, ident)) EQ exp
  { Dfun {fn_name = $2; fn_args = $4; fn_rtyp = $6; fn_body = $8} }
;

typ:
  ident          { Tname $1 }
| ARRAY OF ident { Tarray $3 }
| LCURLY separated_list(COMMA, separated_pair(ident, COLON, ident)) RCURLY { Trecord $2 }
;

