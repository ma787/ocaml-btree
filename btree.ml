type keys = int list;;
type pl = int;;
type root = bool;;
type node = Lf of int | Il of keys * pl * node list * bool | None;;

exception MalformedTree of string
exception NotFound of string

(* searches for a node with key k and returns node along with index *)
let rec search tree k i = match tree with
| Il (v::next, pl, c::cn, r) -> 
  if (i == 0 && not r) then raise (MalformedTree "")
  else if v==k then (Il (v::next, pl, cn, r), i)
  else if v<k then search c k (i+1)
  else if next=[] then match cn with
    | rc::[] -> search rc k (i+1)
    | _ -> raise (MalformedTree "incorrect tree structure")
  else search (Il (next, pl, c::cn, r)) k (i+1)
| _ -> raise (NotFound "not found");;