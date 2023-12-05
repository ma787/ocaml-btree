type keys = int list;;
type pl = int;;
type root = bool;;
type t = int
type node = Lf of keys * pl list * root * t | Il of keys * pl list * node list * root * t;;

exception MalformedTree of string
exception NotFound of string
exception NullTree of string

(* searches for a node with key k and returns node along with index *)
let rec search tree k i = match tree with
| Il (v::next, pls, c::cn, r, t) -> 
  if (i == 0 && not r) then raise (MalformedTree "index 0 not at root")
  else if v==k then (Il (v::next, pls, cn, r, t), i)
  else if v<k then search c k (i+1)
  else if next=[] then match cn with
    | rc::[] -> search rc k (i+1)
    | _ -> raise (MalformedTree "incorrect tree structure")
  else search (Il (next, pls, c::cn, r, t)) k (i+1)
| Lf (v::next, pls, r, t) ->
  if (i == 0 && not r) then raise (MalformedTree "index 0 not at root")
  else if v==k then (Lf (v::next, pls, r, t), i)
  else if v>k then
    if next =[] then raise (NotFound "key not found")
    else search (Lf (next, pls, r, t)) k (i+1)
  else raise (NotFound "key not found")
| _ -> raise (NotFound "key not found");;

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

let rec update_node tree k p c1 c2 = match tree with
| Lf (v::next, pl::pls, r, t) ->
  if k>v then update_node (Lf (next, pls, r, t)) k p c1 c2
  else if k<v then update_node (Lf (k::v::next, p::pl::pls, r, t)) k p c1 c2
  else raise (MalformedTree "")
| Il (v::next, pl::pls, cn, r, t) ->
  if k>v then
    if next=[] then Il (v::k::next, List.append pls [p], List.append cn (c1::c2::[]), r, t)
    else update_node (Il (next, pls, cn, r, t)) k p c1 c2
  else if k<v then Il (k::v::next, p::pl::pls, c1::c2::cn, r, t)
  else raise (MalformedTree "")
| _ -> raise (MalformedTree "");;

(* splits a internal node into two on the median key *)
(* unless it is a root, in which case the node is split into three *)
(* resulting in a new root and increasing the tree depth by 1 *)
let rec split_root tree = match tree with
| Il (ks, pls, c::cn, true, t) -> 
  let mk, mp, mc = List.nth ks (t-1), List.nth pls (t-1), List.nth cn (t-2) in
  let tl = Il (get_left ks mk, get_left pls mp, c::(get_left cn mc), false, t) in
  let tr = Il (get_right ks mk, get_right pls mp, mc::(get_right cn mc), false, t) in
  Il (mk::[], mp::[], tl::tr::[], true, t)
| Lf (ks, pls, r, t) -> let mk, mp = List.nth ks (t-1), List.nth pls (t-1) in
let tl = Lf (get_left ks mk, get_left pls mp, false, t) in
let tr = Lf (get_right ks mk, get_right pls mp, false, t) in
Il (mk::[], mp::[], tl::tr::[], true, t)
| _ -> raise (NullTree "");;

let rec split tree parent = match tree, parent with
| Il (ks, pls, c::cn, r, t), Il (ks1, pl1, cn1, r1, t1) ->
  let mk, mp, mc = List.nth ks (t-1), List.nth pls t-1, List.nth cn (t-2) in
  let tl = Il (get_left ks mk, get_left pls mp, c::(get_left cn mc), false, t) in
  let tr = Il (get_right ks mk, get_right pls mp, mc::(get_right cn mc), false, t) in
  update_node parent mk mp tl tr
| Il (ks, pls, cn, r, t), Lf (ks1, pl1, r1, t1) -> raise (NullTree "")
| _ , Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| _ -> raise (MalformedTree "");;

(* inserts a given key and payload into the tree *)
let rec insert tree (k, p) = match tree with
| Lf (v::next, pl::pls, true, t) ->
  if (List.length(next)+1) == 2*t then insert (split_root tree) (k, p)
  else if k<v then Lf (k::v::next, p::pl::pls, true, t)
  else if k==v then Lf (v::next, p::pls, true, t) (* update payload *)
  else insert (Lf (next, pls, true, t)) (k, p)
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> (* every non-leaf node must have at least 2 children *)
  if (List.length(next)+1) == 2*t-1 then 
    if r then insert (split_root tree) (k, p) (* root is full *)
    else if k < v then match c1 with
      | Il (k1s, p1::pl1, cn1, r1, t) -> 
        if List.length cn1 == 2*t - 1 then insert (split c1 tree) (k, p)
        else insert c1 (k, p)
      | Lf (v1::next1, p1::pl1, r1, t) -> 
        if (List.length(next1)+1) == 2*t then insert (split c1 tree) (k, p)
        else insert c1 (k, p)
      | _ -> raise (MalformedTree "incorrect tree structure")
    else if k == v then Il (v::next, p::pls, c1::c2::cn, r, t)
    else insert (Il (next, pls, c1::c2::cn, r, t)) (k, p)
  else raise (MalformedTree "incorrect tree structure")
| _ -> raise (MalformedTree "incorrect tree structure");;