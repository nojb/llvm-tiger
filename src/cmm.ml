type memory_chunk =
  | Byte_unsigned
  | Byte_signed
  | Sixteen_unsigned
  | Sixteen_signed
  | Thirtytwo_unsigned
  | Thirtytwo_signed
  | Word

type operation =
  | Capply of machtype
  | Cextcall of string * machtype * bool * label option
  | Cload of memory_chunk
  | Calloc
  | Cstore of memory_chunk
  | Caddi | Csubi | Cmuli | Cmulhi | Cdivi | Cmodi
  | Cand | Cor | Cxor | Clsl | Clsr | Casr
  | Ccmpi of comparison
  | Cadd
  | Ccmpa of comparison
  | Ccheckbound

type expression =
  | Cconst_int of nativeint
  | Cconst_symbol of string
  | Cvar of Ident.t
  | Clet of Ident.t * expression * expression
  | Cassign of Ident.t * expression
  | Ctuple of expression list
  | Cop of operation * expression list
  | Csequence of expression * expression
  | Cifthenelse of expression * expression * expression
  | Cswitch of expression * int array * expression array
  | Cloop of expression
  | Cexit of int * expression list

type fundecl =
  {
    fun_name: string;
    fun_args: (Ident.t * machtype) list;
    fun_body: expression;
    fun_fast: bool;
  }

type data_item =
  | Cdefine_symbol of string
  | Cglobal_symbol of string
  | Cint8 of int
  | Cint16 of int
  | Cint32 of nativeint
  | Cint of nativeint
  | Csymbol_address of string
  | Cstring of string
  | Cskip of int
  | Calign of int

type phrase =
  | Cfunction of fundecl
  | Cdata of data_item list
