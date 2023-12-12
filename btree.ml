type keys = int list
type pl = int
type root = bool
type t = int
type node = Lf of keys * pl list * root * t | Il of keys * pl list * node list * root * t

exception MalformedTree of string
exception NotFound of string
exception NullTree of string
exception TreeCapacityNotMet of string

(* searches for a node with key k and returns node along with index *)
let rec search tree k i = match tree with
| Il (v::next, pls, c::cn, r, t) -> 
  if (i == 0 && not r) then raise (MalformedTree "index 0 not at root")
  else if v=k then (Il (v::next, pls, cn, r, t), i)
  else if v<k then search c k (i+1)
  else if next=[] then match cn with
    | rc::[] -> search rc k (i+1)
    | _ -> raise (MalformedTree "final key must have right child")
  else search (Il (next, pls, c::cn, r, t)) k (i+1)
| Lf (v::next, pls, r, t) ->
  if (i == 0 && not r) then raise (MalformedTree "index 0 not at root")
  else if v=k then (Lf (v::next, pls, r, t), i)
  else if v>k then
    if next =[] then raise (NotFound "key not found")
    else search (Lf (next, pls, r, t)) k (i+1)
  else raise (NotFound "key not found")
| _ -> raise (NotFound "key not found")

let rec get_left l m = match l with
| c::cs -> if c=m then [] else c::(get_left cs m)
| [] -> []

let rec get_right l m = match l with
| c1::c2::cs -> 
  if c1=m then c2::(get_right (c2::cs) c2)
  else get_right (c2::cs) m
| c::[] -> []
| [] -> []

(* adds a key, payload and child to a node *)
(* key must not already be in the node *)
let rec update_node tree k p c1 c2 = match tree with
| Il (v::next, pl::pls, ca::cb::cn, r, t) ->
  if k>v then
    if next=[] then
      if c1=cb then Il (v::k::next, pl::p::pls, ca::cb::c2::cn, r, t)
      else raise (MalformedTree "child mismatch")
    else update_node (Il (next, pls, (cb::cn), r, t)) k p c1 c2
  else if k<v then 
    if c2=ca then Il (k::v::next, p::pl::pls, c1::ca::cb::cn, r, t)
    else raise (MalformedTree "child mismatch")
  else raise (MalformedTree "key already in node")
| _ -> raise (NullTree "")

(* splits a root node into three *)
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
| _ -> raise (NullTree "")

(* splits a node in two on a given key index *)
(* migrates key to parent node and returns parent, which may now be full *)
let rec split tree parent m = match tree, parent with
| Il (ks, pls, c::cn, r, t), Il (ks1, pl1, cn1, r1, t1) ->
  let mk, mp, mc = List.nth ks m, List.nth pls m, List.nth cn m in
  let tl = Il (get_left ks mk, get_left pls mp, c::(get_left cn mc), false, t) in
  let tr = Il (get_right ks mk, get_right pls mp, mc::(get_right cn mc), false, t) in
  update_node parent mk mp tl tr
| Lf (ks, pls, r, t), Il (ks1, pls1, cn1, r1, t1) ->
  let mk, mp = List.nth ks m, List.nth pls m in
  let tl = Lf (get_left ks mk, get_left pls mp, false, t) in
  let tr = Lf (get_right ks mk, get_right pls mp, false, t) in
  update_node parent mk mp tl tr
| _ , Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| _ -> raise (NullTree "")

(* inserts a given key and payload into the tree *)
let rec insert tree (k, p) = match tree with
| Lf (v::next, pl::pls, true, t) ->
  if List.length(v::next) == 2*t-1 then insert (split_root tree) (k, p)
  else if k<v then Lf (k::v::next, p::pl::pls, true, t)
  else if k=v then Lf (v::next, p::pls, true, t) (* update payload *)
  else if next=[] then Lf (v::k::next, pl::p::pls, true, t)
  else insert (Lf (next, pls, true, t)) (k, p)
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> (* every non-leaf node must have at least 2 children *)
  if List.length(v::next) == 2*t-1 then
    if r then insert (split_root tree) (k, p) (* root is full *)
    else raise (MalformedTree "parent node cannot be full")
  else if k<v then match c1 with
    | Il (k1s, p1::pl1, cn1, r1, t) -> 
      if List.length k1s == 2*t-1 then insert (split c1 tree (t-1)) (k, p)
      else insert c1 (k, p)
    | Lf (v1::next1, p1::pl1, r1, t) -> 
      if List.length(v1::next1) == 2*t-1 then insert (split c1 tree (t-1)) (k, p)
      else insert c1 (k, p)
    | _ -> raise (MalformedTree "internal node must have >1 child")
  else if k=v then Il (v::next, p::pls, c1::c2::cn, r, t) (* update payload *)
  else if next=[] then match c2 with (* rightmost child *)
    | Il (k2s, p2::pl2, cn2, r2, t) ->
      if List.length k2s == 2*t-1 then insert (split c2 tree (t-1)) (k, p)
      else insert c2 (k, p)
    | Lf (v2::next2, p2::pl2, r2, t) ->
      if List.length(v2::next2) == 2*t-1 then insert (split c2 tree (t-1)) (k, p)
      else insert c2 (k, p)
    | _ -> raise (MalformedTree "internal node must have >1 child")
  else insert (Il (next, pls, c1::c2::cn, r, t)) (k, p)
| _ -> raise (MalformedTree "internal node cannot be empty or without children")

let rec restore tree k p c = match tree with
| Lf ([], [], r, t) -> Lf (k::[], p::[], r, t)
| Lf (v::next, pl::pls, r, t) -> Lf(k::v::next, p::pl::pls, r, t)
| Il ([], [], cn, r, t) -> Il(k::[], p::[], c::cn, r, t)
| Il (v::next, pl::pls, cn, r, t) -> Il (k::v::next, p::pl::pls, c::cn, r, t)
| _ -> raise (MalformedTree "keys/payloads/children mismatch")

let rec merge parent s1 s2 ignore = match parent with
| Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> 
  if (c1=s1 && c2=s2) then match s1, s2 with
    | Lf _, Il _ -> raise (MalformedTree "nodes must be at same level")
    | Il _, Lf _ -> raise (MalformedTree "nodes must be at same level")
    | Lf (k1s, p1s, false, t1), Lf (k2s, p2s, false, t2) ->
      let km, pm = k1s @ (v::k2s), p1s @ (pl::p2s) in (* TODO: concatenate lists without @ *)
      let l = List.length(km) in 
      if ((l < t-1 || l > 2*t-1) && not ignore) then raise (TreeCapacityNotMet "")
      else let s = Lf (km, pm, false, t) in
      Il (next, pls, s::cn, r, t)
    | Il (k1s, p1s, cn1, false, t1), Il (k2s, p2s, cn2, false, t2) ->
      let km, pm, cm = k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2 in
      let l = List.length(k1s) in
      if (l < t-1 || l > 2*t-1) then raise (TreeCapacityNotMet "")
      else let s = Il (km, pm, cm, false, t) in
      Il (next, pls, s::cn, r, t)
    | _, _ -> raise (MalformedTree "child nodes cannot be empty")
  else restore (merge (Il (next, pls, (c2::cn), r, t)) s1 s2 ignore) v pl c1
| _ -> raise (NotFound "could not find sibling nodes") (* occurs if s1 and s2 are not children of parent *)