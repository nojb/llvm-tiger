{
  open Parser

  exception Error of Lexing.position * string

  let str_buf = Buffer.create 20;;
  let keywords = Hashtbl.create 10;;

  List.iter (fun (x, y) -> Hashtbl.add keywords x y)
    [ "if", IF;
      "then", THEN;
      "else", ELSE;
      "var", VAR;
      "end", END;
      "let", LET;
      "for", FOR;
      "while", WHILE;
      "do", DO;
      "to", TO;
      "in", IN;
      "nil", NIL;
      "break", BREAK;
      "array", ARRAY;
      "of", OF;
      "function", FUNCTION;
      "type", TYPE ]
}

rule token = parse
  | '\n'
  { Lexing.new_line lexbuf;
    token lexbuf }
  | ['A'-'Z''a'-'z''_']['a'-'z''A'-'Z''0'-'9''_']* as id
  { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | ['0'-'9']+ as int
  { INT (Int64.of_string int) }
  | '+'
  { PLUS }
  | '*'
  { TIMES }
  | '-'
  { MINUS }
  | '/'
  { SLASH }
  | '&'
  { LAND }
  | '|'
  { LOR }
  | ":="
  { COLONEQ }
  | ':'
  { COLON }
  | ','
  { COMMA }
  | '='
  { EQ }
  | "<>"
  { NE }
  | "<="
  { LE }
  | '<'
  { LT }
  | ">="
  { GE }
  | '>'
  { GT }
  | '.'
  { DOT }
  | ';'
  { SEMI }
  | '{'
  { LCURLY }
  | '}'
  { RCURLY }
  | '['
  { LBRACK }
  | ']'
  { RBRACK }
  | '('
  { LPAREN }
  | ')'
  { RPAREN }
  | [' ' '\t']+
  { token lexbuf }
  | "/*"
  { comment 0 lexbuf }
  | '"'
  { string lexbuf }
  | eof
  { EOF }
  | _
  { raise (Error (lexbuf.Lexing.lex_curr_p, "lexer error")) }

and string = parse
  | '"'
  { let s = Buffer.contents str_buf in
    Buffer.clear str_buf;
    STRING s }
  | '\n'
  { Lexing.new_line lexbuf;
    Buffer.add_char str_buf '\n';
    string lexbuf }
  | "\\n"
  { Buffer.add_char str_buf '\n';
    string lexbuf }
  | "\\t"
  { Buffer.add_char str_buf '\t';
    string lexbuf }
  | "\\\""
  { Buffer.add_char str_buf '"';
    string lexbuf }
  | "\\" ((['0'-'9']['0'-'9']['0'-'9']) as lxm)
  { Buffer.add_char str_buf (char_of_int (int_of_string lxm));
    string lexbuf }
  | "\\\\"
  { Buffer.add_char str_buf '\\';
    string lexbuf }
  | '\\' [' ' '\t']
  { skip_whitespace lexbuf }
  (* | '\\' '\n'
  { Lexing.new_line lexbuf; (* incr_linenum lexbuf; *)
    skip_whitespace lexbuf } *)
  | eof
  { EOF }
  | _ as c
  { Buffer.add_char str_buf c;
    string lexbuf }

and skip_whitespace = parse
  | '\\'
  { string lexbuf }
  | '\n'
  { Lexing.new_line lexbuf;
    skip_whitespace lexbuf }
  | [' ' '\t']+
  { skip_whitespace lexbuf }
  | eof
  { EOF }

and comment lvl = parse
  | "*/" { if lvl = 0 then token lexbuf else comment (lvl-1) lexbuf }
  | "/*" { comment (lvl+1) lexbuf }
  | _ { comment lvl lexbuf }
  | eof
  { EOF }
