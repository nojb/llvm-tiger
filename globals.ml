type ('a, 'b, 'c) fundef = {
  fn_name : 'a;
  fn_rtyp : 'b option;
  fn_args : ('a * 'b) list;
  fn_body : 'c
}
