type t = {
  name : string;
  stamp : int
}

let dummy = {
  name = "<dummy>";
  stamp = -1
}

let equal id1 id2 =
  if id1.stamp = 0 && id2.stamp = 0 then id1.name = id2.name
  else id1.stamp = id2.stamp
  
let compare id1 id2 =
  if id1.stamp = 0 && id2.stamp = 0 then compare id1.name id2.name
  else compare id1.stamp id2.stamp

let laststamp = ref 0

let make name =
  incr laststamp;
  { name = name; stamp = !laststamp }

let makeglobal name =
  {name=name; stamp=0}

let genid () =
  make "tmp"

let to_string id =
  if id.stamp = 0 then id.name
  else Printf.sprintf "%s_%d" id.name id.stamp

open Format

let pp fmt id =
  fprintf fmt "%s" (to_string id)
