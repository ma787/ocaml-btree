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

let rec restore tree k p c = match tree with
| Lf ([], [], r, t) -> Lf (k::[], p::[], r, t)
| Lf (v::next, pl::pls, r, t) -> Lf(k::v::next, p::pl::pls, r, t)
| Il ([], [], cn, r, t) -> Il(k::[], p::[], c::cn, r, t)
| Il (v::next, pl::pls, cn, r, t) -> Il (k::v::next, p::pl::pls, c::cn, r, t)
| _ -> raise (MalformedTree "keys/payloads/children mismatch")

(* searches for a node with key k and returns node *)
let rec search tree k = let eq a b = a=b in
let search_next tnode nk nv npl nc  = let tnext = search tnode k in (match tnext with
| Il ([], [], c::[], r, t) -> restore tnext nv npl nc
| Il (v::next, pl::pls, c::cn, r, t) -> 
  if List.exists (eq nk) (v::next) then restore tnext nv npl nc else tnext
| _ -> tnext) in
match tree with
| Il (v::next, pl::pls, c::cn, r, t) -> 
  if k=v then tree
  else if k<v then search c k
  else search_next (Il (next, pls, cn, r, t)) k v pl c
| Il ([], [], c::[], r, t) -> search c k
| Lf (v::next, pl::pls, r, t) ->
  if k=v then tree
  else if k>v then
    if next=[] then raise (NotFound "key not found")
    else restore (search (Lf (next, pls, r, t)) k) v pl (Lf ([], [], false, 0))
  else raise (NotFound ("key not found"))
| _ -> raise (NotFound ("key not found"))

let rec get_left l i m = match l with
| c::cs -> if i=m then [] else c::(get_left cs (i+1) m)
| [] -> []

let rec get_right l i m = match l with
| c::cs -> 
  if m=(-1) then c::(get_right cs i m)
  else if i=m then get_right cs i (-1)
  else get_right cs (i+1) m
| [] -> []

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

(* takes two child nodes and their separating key and merges them into one node *)
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

(* adds keys from a sibling node to B if possible *)
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
| _ -> raise (NotFound "child not found")

(* attempts to redistribute keys between B and its sibling nodes*)
(* otherwise merges B with a sibling to make sure it has enough children*)
let rec refill tree parent = try redistribute tree parent with (NullTree "") ->
  match parent with
  | Lf _ -> raise (MalformedTree "leaf node cannot be parent")
  | Il (v::next, pl::pls, c1::c2::cn, r, t) ->
    if c1=tree then merge parent tree c2 false
    else if c2=tree then merge parent c1 tree false
    else raise (MalformedTree "")
  | _ -> raise (MalformedTree "")

let rec replace_child parent old newc = match parent with
| Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Il ([], [], _, r, t) -> raise (NotFound "child not found")
| Il (v::next, pl::pls, c::cn, r, t) ->
  if c=old then Il (v::next, pl::pls, newc::cn, r, t)
  else restore (replace_child (Il (next, pls, cn, r, t)) old newc) v pl c
| _ -> raise (NullTree "")

(* returns the key that is the inorder successor of k in tree, along with payload *)
let rec find_successor tree k p i = match tree with
| Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> let m = k=v in
  if (m && not i) then match c2 with
    | Lf (k1::k1s, p1::p1s, r, t) -> k1, p1
    | Il (v1::next1, p1::p1s, ca::cb::cn1, r, t) -> find_successor c2 v1 p1 true
    | _ -> raise (MalformedTree "child node cannot be empty")
  else if m then match c1 with
    | Lf (k1::k1s, p1::p1s, r, t) -> k1, p1
    | Il (v1::next1, p1::p1s, ca::cb::cn1, r, t) -> find_successor c1 v1 p1 true
    | _ -> raise (MalformedTree "child node cannot be empty")
  else find_successor (Il (next, pls, (c2::cn), r, t)) k p i
| Il _ -> raise (NotFound "key not found")

let rec swap_successor tree k1 p1 k2 p2 i = match tree with
| Lf (v::next, pl::pls, r, t) -> let m = k1=v in
  if (m && i) then Lf (k2::next, p2::pls, r, t)
  else if m then restore (swap_successor (Lf (next, pls, r, t)) k1 p1 k2 p2 i) v pl (Lf ([], [], false, 0))
  else Lf (k2::next, p2::pls, r, t)
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> let m = k1=v in
  if (m && not i) then Il (k2::next, p2::pls, c1::(swap_successor c2 k2 p2 k1 p1 true)::cn, r, t)
  else if m then Il (v::next, pl::pls, (swap_successor c1 k1 p1 k2 p2 i)::c2::cn, r, t)
  else restore (swap_successor (Il (next, pls, (c2::cn), r, t)) k1 p1 k2 p2 i) v pl c1
| _ -> raise (NotFound "at least one key to swap not found")

let rec delete tree k =
  let eq a b = a=b in 
  let rec delete_aux tree parent k l =
    let del_next tnode nk nv npl nc  = 
      let res tree = restore tree nv npl nc in
      let p, oldt, tnext = delete_aux tnode parent k (l+1) in (match tnext with
      | Il ([], [], c::[], r, t) -> p, res oldt, res tnext
      | Il (v::next, pl::pls, c::cn, r, t) -> if List.exists (eq nk) (v::next) then p, res oldt, res tnext else p, res oldt, tnext
      | Lf ([], [], r, t) -> p, res oldt, res tnext
      | Lf (v::next, pl::pls, r, t) -> if List.exists (eq nk) (v::next) then p, res oldt, (restore tnext nv npl nc) else p, res oldt, tnext
      | _ -> raise (MalformedTree "no match found")) in 
    match tree, parent with
    | _, Lf _ ->
      if tree=parent then (match parent with
        | Lf (v::next, pl::pls, true, t) ->
          let tnext = Lf (next, pls, true, t) in
          if k=v then tnext, parent, tnext
          else if k>v then 
            let a, b, c = delete_aux tnext tnext k (l+1) in
            let newt = restore a v pl (Lf ([], [], false, 0)) in newt, parent, newt
          else raise (NotFound "key not found")
        | Il (v::next, pl::pls, c::cn, true, t) -> 
          if k=v then
          let swapt = (let k1, p1 = (find_successor tree v pl false) in swap_successor tree v pl k1 p1 false) in delete_aux swapt (replace_child parent tree swapt) k 0
          else if k>v then 
            let tnext = Il (next, pls, cn, true, t) in
            let a, b, c = delete_aux tnext tnext k (l+1) in
            let newt = restore a v pl c in newt, parent, newt
          else raise (NotFound "key not found")
        | _ -> raise (NotFound "key not found"))
        else raise (MalformedTree "leaf node cannot be parent")
    | Lf ([], [], r, t), _ -> raise (NotFound "key not found")
    | Lf (v::next, pl::pls, r, t), _ ->
      if k<v then raise (NotFound "key not found")
      else if k=v then
        if l + (List.length (v::next)) < t then
          let newp = refill tree parent in
          let newc = search newp k in delete_aux newc newp k 0
        else parent, tree, (Lf (next, pls, r, t))
      else del_next (Lf (next, pls, r, t)) k v pl (Lf ([], [], false, 0))
    | Il (_, _, c::[], r, t), _ -> raise (NotFound "key not found")
    | Il (v::next, pl::pls, c1::c2::cn, r, t), _ ->
      if k<v then let p, oldt, newc = delete_aux c1 tree k 0 in p, oldt, (Il (v::next, pl::pls, newc::c2::cn, r, t))
      else if k>v then del_next (Il (next, pls, (c2::cn), r, t)) k v pl c1
      else 
        let swapt = let k1, p1 = find_successor tree v pl false in swap_successor tree v pl k1 p1 false in delete_aux swapt (replace_child parent tree swapt) k 0
    | _, _ -> raise (NullTree "") in
  let delete_final tree parent k l = 
    let p, oldt, newt = delete_aux tree parent k 0 in
    if p=newt then p else replace_child p oldt newt in
  let tdel = search tree k in
  if tree=tdel then match tree with
    | Lf (_, _, true, t) -> delete_final tree tdel k 0
    | Il (_, _, _, true, t) -> delete_final tree tdel k 0
    | _ -> raise (MalformedTree "tree and parent required for deletion if not root")
  else match tree with
    | Il (v::next, pl::pls, c::cn, r, t) ->
      if c=tdel then delete_final tdel tree k 0 else match c with
      | Lf _ -> restore (delete (Il (next, pls, cn, r, t)) k) v pl c
      | Il (k1::k1s, p1::p1s, c1::cn1, r1, t) -> 
        if k<k1 then Il (v::next, pl::pls, (delete c k)::cn, r, t)
        else if k>k1 then restore (delete (Il (next, pls, cn, r, t)) k) v pl c
        else raise (NullTree "")
    | Il ([], [], c::[], r, t) -> if c=tdel then delete_final tdel tree k 0 else raise (NotFound "key not found")