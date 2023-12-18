type keys = int list
type pl = int
type root = bool
type t = int
type node = Lf of keys * pl list * root * t | Il of keys * pl list * node list * root * t

exception MalformedTree of string
exception NotFound of string
exception NullTree of string
exception TreeCapacityNotMet of string

let rec to_string tree = let ks, ps, cs, root, tval = match tree with
| Il (k, p, c, r, t) -> k, p, c, r, t
| Lf (k, p, r, t) -> k, p, [], r, t in
let string_of_int_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ string_of_int x ^ ",") "" l) ^ "]" in
let string_of_tree_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ (to_string x) ^ ",") "" l) ^ "]" in
"(" ^ (string_of_int_list ks) ^ ", " ^ (string_of_int_list ps) ^ ", " ^ (if List.length cs > 0 then ((string_of_tree_list cs) ^ ", ") else "") ^ (string_of_bool root) ^ ", " ^ (string_of_int tval) ^ ")"

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

let rec get_left l i m = match l with
| c::cs -> if i=m then [] else c::(get_left cs (i+1) m)
| [] -> []

let rec get_right l i m = match l with
| c::cs -> 
  if m=(-1) then c::(get_right cs i m)
  else if i=m then get_right cs i (-1)
  else get_right cs (i+1) m
| [] -> []

let rec restore tree k p c = match tree with
| Lf ([], [], r, t) -> Lf (k::[], p::[], r, t)
| Lf (v::next, pl::pls, r, t) -> Lf(k::v::next, p::pl::pls, r, t)
| Il ([], [], cn, r, t) -> Il(k::[], p::[], c::cn, r, t)
| Il (v::next, pl::pls, cn, r, t) -> Il (k::v::next, p::pl::pls, c::cn, r, t)
| _ -> raise (MalformedTree "keys/payloads/children mismatch")

(* adds a key, payload and child to a node *)
(* key must not already be in the node *)
let rec update_node tree k p c1 c2 = match tree with
| Il (v::next, pl::pls, c::cn, r, t) -> (match c1, c with
  | Lf (k1::k1s, p1::p1s, r1, t1), Lf (k3::k3s, p3::p3s, r3, t3) ->
    if (k1=k3 && p1=p3) then Il (k::v::next, p::pl::pls, c1::c2::cn, r, t)
    else restore (update_node (Il (next, pls, cn, r, t)) k p c1 c2) v pl c
  | Il (k1::k1s, p1::p1s, c1::cn1, r1, t1), Il (k3::k3s, p3::p3s, c3::cn3, r3, t3) ->
    if (k1=k3 && p1=p3) then Il (k::v::next, p::pl::pls, c1::c2::cn, r, t)
    else restore (update_node (Il (next, pls, cn, r, t)) k p c1 c2) v pl c
  | _ -> raise (MalformedTree "child type mismatch"))
| Il ([], [], c::[], r, t) -> (match c1, c with (* right-most node *)
  | Lf (k1::k1s, p1::p1s, r1, t1), Lf (k3::k3s, p3::p3s, r3, t3) ->
    if (k1=k3 && p1=p3) then Il (k::[], p::[], c1::c2::[], r, t)
    else raise (MalformedTree "child node to split not found")
  | Il (k1::k1s, p1::p1s, c1::cn1, r1, t1), Il (k3::k3s, p3::p3s, c3::cn3, r3, t3) ->
    if (k1=k3 && p1=p3) then Il (k::[], p::[], c1::c2::[], r, t)
    else raise (MalformedTree "child node to split not found")
  | _ -> raise (MalformedTree "child type mismatch"))
| _ -> raise (MalformedTree "must be internal node with >1 child")

(* splits a root node into three *)
(* resulting in a new root and increasing the tree depth by 1 *)
let rec split_root tree = match tree with
| Il (ks, pls, c::cn, true, t) -> 
  let mk, mp = List.nth ks (t-1), List.nth pls (t-1) in
  let tl = Il (get_left ks 0 (t-1), get_left pls 0 (t-1), c::(get_left cn 0 (t-1)), false, t) in
  let tr = Il (get_right ks 0 (t-1), get_right pls 0 (t-1), get_right (c::cn) 0 (t-1), false, t) in
  Il (mk::[], mp::[], tl::tr::[], true, t)
| Lf (ks, pls, r, t) -> let mk, mp = List.nth ks (t-1), List.nth pls (t-1) in
let tl = Lf (get_left ks 0 (t-1), get_left pls 0 (t-1), false, t) in
let tr = Lf (get_right ks 0 (t-1), get_right pls 0 (t-1), false, t) in
Il (mk::[], mp::[], tl::tr::[], true, t)
| _ -> raise (NullTree "")

(* splits a node in two on a given key index *)
(* migrates key to parent node and returns parent, which may now be full *)
let rec split tree parent m = match tree, parent with
| Il (ks, pls, c::cn, r, t), Il (ks1, pl1, cn1, r1, t1) ->
  let mk, mp, mc = List.nth ks m, List.nth pls m, List.nth cn m in
  let tl = Il (get_left ks 0 m, get_left pls 0 m, c::(get_left cn 0 m), false, t) in
  let tr = Il (get_right ks 0 m, get_right pls 0 m, mc::(get_right cn 0 m), false, t) in
  update_node parent mk mp tl tr
| Lf (ks, pls, r, t), Il (ks1, pls1, cn1, r1, t1) ->
  let mk, mp = List.nth ks m, List.nth pls m in
  let tl = Lf (get_left ks 0 m, get_left pls 0 m, false, t) in
  let tr = Lf (get_right ks 0 m, get_right pls 0 m, false, t) in
  update_node parent mk mp tl tr
| _ , Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| _ -> raise (NullTree "")

(* inserts a given key and payload into the tree *)
let rec insert tree k p i = match tree with
| Lf (v::next, pl::pls, r, t) ->
  let l = (List.length (v::next) == 2*t-1) in
  if (l && r && not i) then insert (split_root tree) k p false
  else if (l && not r) then raise (MalformedTree "full node not split ahead of time")
  else if k<v then Lf (k::v::next, p::pl::pls, r, t)
  else if k=v then Lf (v::next, p::pls, r, t) (* update payload *)
  else if next=[] then Lf (v::k::next, pl::p::pls, r, t)
  else restore (insert (Lf (next, pls, r, t)) k p false) v pl (Lf ([], [], false, 0)) (* TODO: find a way to restore keys that have been skipped *)
| Lf ([], [], true, t) -> Lf (k::[], p::[], true, t)
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> (* every non-leaf node must have at least 2 children *)
  let l = (List.length(v::next) == 2*t-1) in
  if (l && r && not i) then insert (split_root tree) k p false (* root is full *)
  else if (l && not r) then raise (MalformedTree "parent node cannot be full")
  else if k<v then match c1 with
    | Il (k1s, pl1, cn1, r1, t) -> 
      if List.length k1s == 2*t-1 then insert (split c1 tree (t-1)) k p true
      else let c  = insert c1 k p false in Il (v::next, pl::pls, c::c2::cn, r, t)
    | Lf (k1s, pl1, r1, t) -> 
      if List.length k1s == 2*t-1 then insert (split c1 tree (t-1)) k p true
      else let c  = insert c1 k p false in Il (v::next, pl::pls, c::c2::cn, r, t)
  else if k=v then Il (v::next, p::pls, c1::c2::cn, r, t) (* update payload *)
  else if next=[] then match c2 with (* rightmost child *)
    | Il (k2s, pl2, cn2, r2, t) ->
      if List.length k2s == 2*t-1 then insert (split c2 tree (t-1)) k p true
      else let c  = insert c2 k p false in Il (v::next, pl::pls, c1::c::cn, r, t)
    | Lf (k2s, pl2, r2, t) ->
      if List.length k2s == 2*t-1 then insert (split c2 tree (t-1)) k p true
      else let c  = insert c2 k p false in Il (v::next, pl::pls, c1::c::cn, r, t)
  else restore (insert (Il (next, pls, c2::cn, r, t)) k p false) v pl c1
| _ -> raise (MalformedTree "internal node cannot be empty or without children")

let rec merge parent s1 s2 ignore = match parent with
| Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> 
  if (c1=s1 && c2=s2) then match s1, s2 with
    | Lf _, Il _ -> raise (MalformedTree "nodes must be at same level")
    | Il _, Lf _ -> raise (MalformedTree "nodes must be at same level")
    | Lf (k1s, p1s, false, t1), Lf (k2s, p2s, false, t2) ->
      let km, pm = k1s @ (v::k2s), p1s @ (pl::p2s) in (* TODO: concatenate lists without @ *)
      let l = List.length km in 
      if ((l < t-1 || l > 2*t-1) && not ignore) then raise (TreeCapacityNotMet "")
      else let s = Lf (km, pm, false, t) in
      Il (next, pls, s::cn, r, t)
    | Il (k1s, p1s, cn1, false, t1), Il (k2s, p2s, cn2, false, t2) ->
      let km, pm, cm = k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2 in
      let l = List.length k1s in
      if (l < t-1 || l > 2*t-1) then raise (TreeCapacityNotMet "")
      else let s = Il (km, pm, cm, false, t) in
      Il (next, pls, s::cn, r, t)
    | _, _ -> raise (MalformedTree "child nodes cannot be empty")
  else restore (merge (Il (next, pls, (c2::cn), r, t)) s1 s2 ignore) v pl c1
| _ -> raise (NotFound "could not find sibling nodes") (* occurs if s1 and s2 are not children of parent *)

let rec redistribute tree parent = match parent with
| Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Il (v::next, pl::pls, c1::c2::cn, r, t) ->
  if c1=tree then match c2 with
    | Lf (ks, pls, r, t) -> 
      let l = List.length ks in
      if l > t-1 then split (merge parent tree c2 true) parent (l-1)
      else raise (NullTree "")
    | Il (ks, pls, cn, r, t) ->
      let l = List.length ks in
      if l > t-1 then split (merge parent tree c2 true) parent (l-1)
      else raise (NullTree "")
  else if c2=tree then match c1 with
    | Lf (ks, pls, r, t) -> 
      let l = List.length ks in
      if l > t-1 then split (merge parent c1 tree true) parent (l-1)
      else raise (NullTree "")
    | Il (ks, pls, cn, r, t) ->
      let l = List.length ks in
      if l > t-1 then split (merge parent c1 tree true) parent (l-1)
      else raise (NullTree "")
  else restore (redistribute tree (Il (next, pls, cn, r, t))) v pl c1
| _ -> raise (MalformedTree "")

let rec refill tree parent = try redistribute tree parent with (NullTree "") ->
  match parent with
  | Lf _ -> raise (MalformedTree "leaf node cannot be parent")
  | Il (v::next, pl::pls, c1::c2::cn, r, t) ->
    if c1=tree then merge parent tree c2 false
    else if c2=tree then merge parent c1 tree false
    else raise (MalformedTree "")
  | _ -> raise (MalformedTree "")

  let rec replace_child parent old newc = match old, parent with
  | _, Lf _ -> raise (MalformedTree "leaf node cannot be parent")
  | _, Il (_, _, [], _, _) -> raise (NotFound "child not found")
  | Lf (v::next, pl::pls, r, t), Il (k::k1s, p::p1s, c::cn, r1, t1) ->
    if old=c then Il (k::k1s, p::p1s, newc::cn, r1, t1) 
    else restore (replace_child (Il (k1s, p1s, cn, r1, t1)) old newc) k p c

let rec delete tree parent k = match tree, parent with
| _, Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Lf (v::next, pl::pls, r, t), _ ->
  if k=v then
    if List.length (v::next) > t-2 then replace_child parent tree (Lf (next, pls, r, t))
    else let l = refill tree parent in match l with
    | Lf (v::next, pl::pls, r, t) -> Lf (next, pls, r, t)
    | _ -> raise (MalformedTree "can only delete from leaf")
  else if k<v then raise (NotFound "key not found")
  else restore (delete (Lf (next, pls, r, t)) parent k) v pl (Lf ([], [], false, 0))
| _, Il (ks, pls, c1::c2::cn, r, t) -> match c2 with
  | Il (k1s, p1s, c::cn1, r, t) -> match c with
    | Lf _ -> delete c c2 k
    | _ -> raise (MalformedTree "inorder successor not leaf")
  | _ -> raise (MalformedTree "inorder successor not leaf")
| _ -> raise (NullTree "")
