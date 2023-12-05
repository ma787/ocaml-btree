type keys = int list;;
type pl = int;;
type root = bool;;
type t = int
type node = Lf of root * t | Il of keys * pl list * node list * root * t;;

exception MalformedTree of string
exception NotFound of string

(* searches for a node with key k and returns node along with index *)
let rec search tree k i = match tree with
| Il (v::next, pl, c::cn, r, t) -> 
  if (i == 0 && not r) then raise (MalformedTree "index 0 not at root")
  else if v==k then (Il (v::next, pl, cn, r, t), i)
  else if v<k then search c k (i+1)
  else if next=[] then match cn with
    | rc::[] -> search rc k (i+1)
    | _ -> raise (MalformedTree "incorrect tree structure")
  else search (Il (next, pl, c::cn, r, t)) k (i+1)
| _ -> raise (NotFound "not found");;

let rec get_left l m = match l with
| c::cs -> if c==m then [] else c::(get_left cs m)
| [] -> [];;

let rec get_right l m = match l with
| c1::c2::cs -> 
  if c1==m then c2::(get_right (c2::cs) c2)
  else get_right (c2::cs) m
| c::[] -> []
| [] -> [];;

let rec add_key ks k = match ks with
| c::cs ->
  if k < c then k::ks
  else if k==c then ks
  else c::(add_key cs k)
| [] -> k::[]

(* splits a internal node into two on the median key *)
(* unless it is a root, in which case the node is split into three *)
(* resulting in a new root and increasing the tree depth by 1 *)
let rec split tree = match tree with
| Il (ks, pls, c::cn, true, t) -> 
  let mk, mp, mc = List.nth ks (t-1), List.nth pls (t-1), List.nth cn (t-2) in
  let tl = Il (get_left ks mk, get_left pls mp, c::(get_left cn mc), false, t) in
  let tr = Il (get_right ks mk, get_right pls mp, mc::(get_right cn mc), false, t) in
  Il (mk::[], mp::[], tl::tr::[], true, t)
| Lf (r, t) -> Lf (r, t);;

(* inserts a given key and payload into the tree *)
let rec insert tree (k, p) = match tree with
| Lf (true, t) -> Il (k::[], p::[], (Lf (false, t))::(Lf (false, t))::[], true, t)
| Il (v::next, pl, c::cn, r, t) -> 
  if (List.length(next)+1) == 2*t-1 then insert (split tree) (k, p)
  else raise (MalformedTree "incorrect tree structure")
| _ -> raise (MalformedTree "incorrect tree structure");;