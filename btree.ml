type keys = int list
type pl = int
type node = Lf of keys * pl list * bool * int | Il of keys * pl list * node list * bool * int

exception MalformedTree of string
exception NotFound of string
exception InvalidOperation of string

let null_tree = Lf ([], [], false, 0)

module Attrs = struct
  let rec to_string tree = let ks, ps, cs, root, tval = match tree with
  | Il (k, p, c, r, t) -> k, p, c, r, t
  | Lf (k, p, r, t) -> k, p, [], r, t in
  let string_of_int_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ string_of_int x ^ ",") "" l) ^ "]" in
  let string_of_tree_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ (to_string x) ^ ",") "" l) ^ "]" in
  "(" ^ (string_of_int_list ks) ^ ", " ^ (string_of_int_list ps) ^ ", " ^ (if List.length cs > 0 then ((string_of_tree_list cs) ^ ", ") else "") ^ (string_of_bool root) ^ ", " ^ (string_of_int tval) ^ ")"

  let n_keys tree = match tree with
  | Il (ks, _, _, _, _) -> List.length ks
  | Lf (ks, _, _, _) -> List.length ks

  let get_hd tree = match tree with
  | Il (ks, _, _, _, _) -> List.hd ks
  | Lf (ks, _, _, _) -> List.hd ks

  let is_leaf tree = match tree with
  | Il _ -> false
  | Lf _ -> true

  let get_all tree = match tree with
  | Il (ks, pls, cn, r, t) -> ks, pls, cn, r, t
  | Lf (ks, pls, r, t) -> ks, pls, [], r, t

  let rec split_ks n ks newks i = match ks with
  | c::cs -> if i=n then [c], (List.rev newks), cs else split_ks n cs (c::newks) (i+1)
  | [] -> [], List.rev newks, ks;;

  let rec split_cn n cn newcn i = match cn with
  | c::cs -> if i=n then (List.rev newcn), cn else split_cn n cs (c::newcn) (i+1)
  | [] -> List.rev newcn, cn

  let rec get_index l v i = match l with
  | [] -> raise (Failure "not in list")
  | c::cs -> if c=v then i else get_index cs v (i+1)
  end

module Tree_ops = struct
  (* appends key k, payload p and child c to the head of each associated list *)
  let restore tree k p c = match tree with
  | Lf ([], [], r, t) -> Lf (k::[], p::[], r, t)
  | Lf (v::next, pl::pls, r, t) -> Lf (k::v::next, p::pl::pls, r, t)
  | Il ([], [], cn, r, t) -> Il (k::[], p::[], c::cn, r, t)
  | Il (v::next, pl::pls, cn, r, t) -> Il (k::v::next, p::pl::pls, c::cn, r, t)
  | _ -> raise (MalformedTree "invalid tree structure")

  (* returns [next key] or [] if k is the rightmost key in the node *)
  let rec get_next tree k = match tree with
  | Il (v::next, _::pls, _::cn, r, t) ->
    if v=k then try [List.hd next] with Failure _ -> []
    else get_next (Il (next, pls, cn, r, t)) k
  | Il ([], _, _, _, _) -> []
  | Lf (v::next, _::pls, r, t) ->
    if v=k then try [List.hd next] with Failure _ -> []
    else get_next (Lf (next, pls, r, t)) k
  | _ -> raise (MalformedTree "invalid tree structure")

  let rec get_pl_from_key tree k = match tree with
  | Il (v::next, pl::pls, _::cn, r, t) -> 
    if v=k then pl else get_pl_from_key (Il (next, pls, cn, r, t)) k
  | Lf (v::next, pl::pls, r, t) ->
    if v=k then pl else get_pl_from_key (Lf (next, pls, r, t)) k
  | _ -> raise (NotFound "payload associated with key not found")

  (* returns either the left child of key in kl or the rightmost child if kl=[] *)
  let rec get_child tree kl =
    if Attrs.is_leaf tree then null_tree
    else match kl with
    | [] -> (match tree with
      | Il (_::next, _::pls, _::cn, r, t) -> get_child (Il (next, pls, cn, r, t)) kl
      | Il ([], [], c::[], _, _) -> c
      | _ -> raise (MalformedTree "invalid tree structure"))
    | k::_ -> (match tree with
      | Il (v::next, _::pls, c::cn, r, t) ->
        if v=k then c else get_child (Il (next, pls, cn, r, t)) kl
      | Il ([], [], _::[], _, _) -> raise (NotFound "child node not found")
      | _ -> raise (MalformedTree "invalid tree structure"))

  (* replaces the child node associated with kl with newc *)
  let rec replace_child tree kl newc =
    if Attrs.is_leaf tree then null_tree
    else match kl with
    | [] -> (match tree with
      | Il (v::next, pl::pls, c::cn, r, t) -> 
      restore (replace_child (Il (next, pls, cn, r, t)) kl newc) v pl c
      | Il ([], [], _::[], r, t) -> Il ([], [], newc::[], r, t)
      | _ -> raise (MalformedTree "invalid tree structure"))
    | k::_ -> (match tree with
      | Il (v::next, pl::pls, c::cn, r, t) ->
        if v=k then (Il (v::next, pl::pls, newc::cn, r, t))
        else restore (replace_child (Il (next, pls, cn, r, t)) kl newc) v pl c
      | Il ([], [], _::[], _, _) -> raise (NotFound "child node not found")
    | _ -> raise (MalformedTree "invalid tree structure"))

  let rec insert_key_and_pl tree k p = match tree with
  | Lf (v::next, pl::pls, r, t) ->
    if k<v then Lf (k::v::next, p::pl::pls, r, t)
    else restore (insert_key_and_pl (Lf (next, pls, r, t)) k p) v pl null_tree
  | Lf ([], [], r, t) -> Lf (k::[], p::[], r, t)
  | _ -> raise (InvalidOperation "cannot insert key in internal node")

  let rec remove_key tree k = match tree with
  | Lf (v::next, pl::pls, r, t) ->
    if v=k then Lf (next, pls, r, t)
    else restore (remove_key (Lf (next, pls, r, t)) k) v pl null_tree
  | _ -> raise (InvalidOperation "cannot remove key from internal node")

  (* replaces the child nodes of the key in kl with newc *)
  let rec replace_and_remove tree kl newc =
    match kl with
    | [] -> raise (NotFound "merge key not given")
    | k::_ -> (match tree with
      | Il (v::next, pl::pls, c1::c2::cn, r, t) ->
        if v=k then (Il (next, pls, newc::cn, r, t)) 
        else restore (replace_and_remove (Il (next, pls, (c2::cn), r, t)) kl newc) v pl c1
      | _ -> raise (NotFound "merge key to remove not found"))

  (* adds a key, payload and child to a node *)
  (* key must not already be in the node *)
  let rec update_node tree k p c1 c2 = match tree with
  | Il (v::next, pl::pls, c::cn, r, t) -> 
    if Attrs.is_leaf c1 != Attrs.is_leaf c then
      raise (MalformedTree "child node type mismatch")
    else if Attrs.get_hd c1 = Attrs.get_hd c then
      Il (k::v::next, p::pl::pls, c1::c2::cn, r, t)
    else restore (update_node (Il (next, pls, cn, r, t)) k p c1 c2) v pl c
  | Il ([], [], c::cn, r, t) -> (* right-most node *)
    if Attrs.is_leaf c1 != Attrs.is_leaf c then 
      raise (MalformedTree "child node type mismatch")
    else if Attrs.get_hd c1 = Attrs.get_hd c then 
      Il (k::[], p::[], c1::c2::cn, r, t)
    else raise (NotFound "child node to replace not found")
  | _ -> raise (MalformedTree "invalid tree structure")
  end

open Attrs
open Tree_ops

(* searches for and returns a node in the tree containing key k *)
let rec search tree k = let eq a b = a=b in
let search_next tnode ks nv npl nc  = let tnext = search tnode k in (match tnext with
| Il ([], [], _::[], _, _) -> restore tnext nv npl nc
| Il (v::_, _::_, _::_, _, _) -> 
  if List.exists (eq v) ks then restore tnext nv npl nc else tnext
| _ -> tnext) in
match tree with
| Il (v::next, pl::pls, c::cn, r, t) -> 
  if k=v then tree
  else if k<v then search c k
  else search_next (Il (next, pls, cn, r, t)) (v::next) v pl c
| Il ([], [], c::[], _, _) -> search c k
| Lf (v::next, pl::pls, r, t) ->
  if k=v then tree
  else if k>v then
    if next=[] then raise (NotFound ("key not found"))
    else restore (search (Lf (next, pls, r, t)) k) v pl (Lf ([], [], false, 0))
  else raise (NotFound "key not found")
| _ -> raise (NotFound "key not found")

(* splits a node in two on a given key index *)
(* migrates key to parent node and returns parent, which may now be full *)
(* if the node is a root, this can increase the depth of the tree by 1 *)
let split tree parent m ignore =
  let split_node left leaf tree =
    let ks, pls, cn, _, t = get_all tree in
    let mk, lks, rks = split_ks m ks [] 0 in
    let mp, lpls, rpls = split_ks m pls [] 0 in
    let lcn, rcn = split_cn (m+1) cn [] 0 in
    let tr = (if leaf then if left then Lf (lks, lpls, false, t) else Lf (rks, rpls, false, t)
    else if left then Il (lks, lpls, lcn, false, t) else Il (rks, rpls, rcn, false, t)) in
    mk, mp, tr in
  let _, _, _, root, t = get_all tree in
  let root_split = 
    if ignore then false else (root && Int.equal (get_hd parent) (get_hd tree)) in
  if is_leaf parent && not root_split then raise (InvalidOperation "cannot split with leaf node as parent")
  else let cleaf = is_leaf tree in
  let mk, mp, t_left = split_node true cleaf tree in
  let _, _, t_right = split_node false cleaf tree in
  if root_split then Il (List.hd mk::[], List.hd mp::[], t_left::t_right::[], true, t)
  else update_node parent (List.hd mk) (List.hd mp) t_left t_right

let rec insert tree k p ckey ignore =
  let _, _, _, root, t = get_all tree in
  let lim = 2*t-1 in
  let empty, full = ckey < 0, n_keys tree = lim in
  if (full && root && not ignore) then
    let tr = split tree tree (t-1) false in insert tr k p (get_hd tr) false
  else if (full && not root && not ignore) then raise (MalformedTree "full node not split ahead of time")
  else if (empty && root) then insert_key_and_pl tree k p
  else if empty then raise (MalformedTree "empty non-root node")
  else if k=ckey then tree
  else let next = get_next tree ckey in
    if (k>ckey && next != []) then insert tree k p (List.hd next) ignore
    else let pkey = if k<ckey then [ckey] else [] in
    if (is_leaf tree) then insert_key_and_pl tree k p
    else let c = get_child tree pkey in
      if (n_keys c) = lim then 
        let tr = split c tree (t-1) false in insert tr k p (Attrs.get_hd tr) true
      else let newc = insert c k p (Attrs.get_hd c) false in replace_child tree pkey newc
    
(* takes two child nodes and merges them into one node, taking a key from the parent node *)
(* if the node is a root, this can decrease the depth by 1 *)
let rec merge parent v s1 s2 ignore iroot =
  let check_length l t = 
    if ((l < t-1 || l > 2*t-1) && not ignore) then 
      raise (InvalidOperation "merge will result in an invalid node") else () in
  let _, _, _, root, t = get_all parent in
  let one_key, next = n_keys parent = 1, get_next parent v in
  let s1_leaf, s2_leaf = is_leaf s1, is_leaf s2 in
  if ((s1_leaf && not s2_leaf) || (s2_leaf && not s1_leaf)) then
    raise (MalformedTree "internal node and leaf node at same level")
  else if (is_leaf parent) then raise (InvalidOperation "cannot merge with leaf node as parent")
  else
    let m1, m2 = get_child parent [v] = s1, get_child parent next = s2 in
    if m1 && m2 then
      let k1s, p1s, cn1, _, _ = get_all s1 in
      let k2s, p2s, cn2, _, _ = get_all s2 in
      let _ = check_length (List.length k1s + List.length k2s + 1 ) t in
      let merged_cn = cn1 @ cn2 in
      if (root && one_key && not iroot) then
        let ks, pls, _, _, _ = get_all parent in
        let mk, mp = List.hd ks, List.hd pls in
        if s1_leaf then Lf (k1s @ (mk::k2s), p1s @ (mp::p2s), true, t)
        else Il (k1s @ (mk::k2s), p1s @ (mp::p2s), merged_cn, true, t)
      else
        let merged_ks = k1s @ (v::k2s) in
        let merged_pls = let p = get_pl_from_key parent v in p1s @ (p::p2s) in
        let s = 
          if s1_leaf then (Lf (merged_ks, merged_pls, false, t))
          else (Il (merged_ks, merged_pls, merged_cn, false, t)) in
        replace_and_remove parent [v] s
    else if next=[] then raise (NotFound "could not find sibling nodes")
    else merge parent (List.hd next) s1 s2 ignore iroot

let rec find_predecessor tree k i = match tree with
| Lf (v::next, pl::pls, r, t) ->
  if i then
    if next=[] then (v, pl)
    else find_predecessor (Lf (next, pls, r, t)) k i (* find largest key in leaf node *)
  else
    if k=v then raise (NotFound "") (* the predecessor is higher in the tree **)
    else if next=[] then raise (NotFound "key not found")
    else if List.hd next = k then (v, pl)
    else find_predecessor (Lf (next, pls, r, t)) k i
| Il (v::next, pl::pls, c1::c2::cn, r, t) ->
  if not i then
    if k=v then find_predecessor c1 k true
    else if k<v then find_predecessor c1 k i
    else if (next=[] || k < List.hd next) then 
      (try find_predecessor c2 k i 
      with (NotFound "") -> (v, pl))
    else find_predecessor (Il (next, pls, (c2::cn), r, t)) k i
  else
    if cn=[] then find_predecessor c2 k true
    else find_predecessor (Il (next, pls, (c2::cn), r, t)) k i
| _ -> raise (NotFound "key or predecessor not found")

let rec find_successor tree k i = match tree with
| Lf (v::next, pl::pls, r, t) ->
  if i then (v, pl)
  else if r then
    if next=[] then raise (NotFound "key or successor not found")
    else if k=v then find_successor (Lf (next, pls, r, t)) k true
    else find_successor (Lf (next, pls, r, t)) k i
  else
    if next=[] then 
      if k=v then raise (NotFound "") (* the successor is higher in the tree *)
      else raise (NotFound "key not found")
    else if k=v then find_successor (Lf (next, pls, r, t)) k true
    else find_successor (Lf (next, pls, r, t)) k i
| Il (v::next, pl::pls, c1::c2::cn, r, t) -> 
  if not i then
    if k=v then find_successor c2 k true
    else if k<v then 
      (try find_successor c1 k i 
      with (NotFound "") -> (v, pl))
    else if next=[] then find_successor c2 k i
    else find_successor (Il (next, pls, (c2::cn), r, t)) k i
  else
    find_successor c1 k i
| _ -> raise (NotFound "key or predecessor not found")

(* swaps the positions of (oldkey, oldpl) and (newkey, newpl) in a tree *)
(* newkey must be either the predecessor or successor of oldkey and must be at a lower depth *)
let rec swap tree oldpair newpair ckey found index =
  let swap_child tree kl f = 
    let c = get_child tree kl in let newc = swap c oldpair newpair (get_hd c) f 0 in
    replace_child tree kl newc in
  let swap_next tree kl f = swap tree oldpair newpair (List.hd kl) f (index+1) in
  let replace_in_list l n = List.mapi (fun i a -> if i=index then n else a) l in
  let ks, pls, cn, r, t = get_all tree in
  let leaf, next = is_leaf tree, get_next tree ckey in
  let ok, nk = fst oldpair, fst newpair in
  let op, np = snd oldpair, snd newpair in
  let successor = nk>ok in
  if ckey=nk then
    if (not found || not leaf) then raise (MalformedTree "order violation")
    else Lf (replace_in_list ks ok, replace_in_list pls op, r, t)
  else if (ckey=ok || found) then
    let newt = if ckey!=ok then tree else
      if leaf then Lf (replace_in_list ks nk, replace_in_list pls nk, r, t)
      else Il (replace_in_list ks nk, replace_in_list pls np, cn, r, t) in
    if (next=[] && leaf) then raise (NotFound "at least one key in swap not found")
    (* either key and successor are both in this leaf, or predecessor is the rightmost key *)
    else if leaf then swap_next newt next true
    else if not found then let kl = if successor then next else [nk] in 
      swap_child newt kl true (* pick edge to go down *)
    else (* find smallest key in subtree if successor *)
      if successor then swap_child newt [ckey] true
      else if next=[] then swap_child newt next true
      else swap_next newt next true (* and largest key in subtree if predecessor*)
  else if ckey>ok then
    if next=[] then swap_child tree next false
    else swap_next tree next false
  else swap_child tree [ckey] false

let steal tree ckey morec =
  let _, _, _, root, t = get_all tree in
  let next = get_next tree ckey in
  let ca, cb = get_child tree [ckey], get_child tree next in
  let mt = merge tree ckey ca cb true root in
  let mc = get_child mt next in
  let lim = (if ca=morec then (n_keys ca - 1) else if cb=morec then t else -1) in
  if lim = -1 then raise (NotFound "child node not found")
  else split mc mt lim true

let rec deletev tree k ckey swapped =
  if ckey<0 then tree
  else 
    let ks, _, _, _, t = get_all tree in
    let leaf, next = is_leaf tree, get_next tree ckey in
    let ca, cb = 
    if not leaf then get_child tree [ckey], get_child tree next 
    else null_tree, null_tree in
    let l1, l2 = n_keys ca, n_keys cb in
    let pair = (ckey, get_pl_from_key tree ckey) in
    let left, right, lempty, rempty = k<ckey, (k>ckey && next=[]), l1<t, l2<t in
    let leftc, rightc = 
    if swapped then not left, left else left, right in (* swapping causes an inversion *)
    if k=ckey then
      if leaf then remove_key tree k
      else if not (lempty && rempty) then (* swap with inorder predecessor/successor *)
        let key_to_swap = 
          if lempty then find_successor tree ckey false 
          else find_predecessor tree ckey false in
        let tr = swap tree pair key_to_swap ckey false (get_index ks ckey 0) in 
        deletev tr k (fst key_to_swap) true
        (* merge around key to delete if neither child node has enough keys *)
      else let tr = merge tree ckey ca cb false false in deletev tr k (get_hd tr) false
    else if not (leftc || rightc) then deletev tree k (List.hd next) swapped
    else if not leaf then
      let c = if lempty || (rightc && not rempty) then cb else ca in
      let ok = (leftc && not lempty) || (rightc && not rempty) in
      if ok then let c_del = deletev c k (get_hd c) false in (* subtree containing k is ok *)
        replace_child tree (if leftc then [ckey] else next) c_del
      else if lempty && rempty then (* merge needed as neither child node has enough keys *)
        let tr = merge tree ckey ca cb false false in deletev tr k (get_hd tr) false
        (* steal a key from the left or right sibling of the subtree containing k *)
      else let tr = steal tree ckey c in deletev tr k (get_hd tr) false
    else if left || right then raise (NotFound "key to delete not found")
    else deletev tree k (List.hd next) false (* continue searching this leaf *)

let delete tree k = deletev tree k (try get_hd tree with Failure _ -> -1) false

let rec insert_list tree items = match items with
| (k, pl)::its -> insert_list (insert tree k pl (try get_hd tree with Failure _ -> -1) false) its
| [] -> tree

let rec delete_list tree keys = match keys with
| k::ks -> delete_list (delete tree k) ks
| [] -> tree

let create_btree t = Lf ([], [], true, t)
