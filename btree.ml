type keys = int32 list
type node = 
| Lf of keys * bool * int * int
| Il of keys * node list * bool * int * int

exception MalformedTree of string
exception NotFound of string
exception InvalidOperation of string
exception NoSpace

module IdSet = Set.Make(Int)

let sizeof_pointer = 4
let null_tree = Lf ([], false, 0, -1)
let null_pointer = Int32.max_int

module Attrs = struct
  let n_keys tree = match tree with
  | Il (ks, _, _, _, _) -> List.length ks
  | Lf (ks, _, _, _) -> List.length ks

  let get_hd tree = match tree with
  | Il (ks, _, _, _, _) -> List.hd ks
  | Lf (ks, _, _, _) -> List.hd ks

  let is_leaf tree = match tree with
  | Il _ -> false
  | Lf _ -> true

  let get_id tree = match tree with
  | Il (_, _, _, _, id) -> id
  | Lf (_, _, _, id) -> id

  let get_all tree = match tree with
  | Il (ks, cn, r, t, id) -> ks, cn, r, t, id
  | Lf (ks, r, t, id) -> ks, [], r, t, id

  let get_child_ids tree = match tree with
  | Il (_, cn, _, _, _) -> 
    List.map (fun tr -> let _, _, _, _, id = get_all tr in id) cn
  | Lf _ -> []

  let get_all_ids tree = 
  let rec get_id_list tree = match tree with
  | Il (_, cn, true, _, id) -> id::(get_child_ids tree) @ (List.flatten (List.map get_id_list cn))
  | Il (_, cn, _, _, _) -> (get_child_ids tree) @ (List.flatten (List.map get_id_list cn))
  | Lf (_, true, _, id) -> [id]
  | Lf _ -> [] in
  List.sort_uniq Int.compare (get_id_list tree)

  let get_all_keys tree = 
    let rec get_key_list tree = match tree with
    | Il (ks, cn, _, _, _) -> ks @ (List.flatten (List.map get_key_list cn))
    | Lf (ks, _, _, _) -> ks in
    List.sort_uniq Int32.compare (get_key_list tree)

  let split_ks n ks = 
    let rec splitv ks newks i = match ks with
    | c::cs -> 
      if i=n then [c], List.rev newks, cs else splitv cs (c::newks) (i+1)
    | [] -> [], List.rev newks, ks
  in splitv ks [] 0

  let split_cn n cn = 
    let rec splitv cn newcn i = match cn with
    | c::cs -> if i=n then List.rev newcn, cn else splitv cs (c::newcn) (i+1)
    | [] -> List.rev newcn, cn
  in splitv cn [] 0

  let rec get_index l v i = match l with
  | [] -> raise (Failure "not in list")
  | c::cs -> if c=v then i else get_index cs v (i+1)

  let rec to_string tree = 
  let ks, cn, r, t, id = get_all tree in
  let string_of_int32_list l = 
    "{" ^ (List.fold_left (fun acc x -> 
      acc ^ Int32.to_string x ^ ",") "" l) ^ "}" in
  let string_of_tree_list l = 
    let s = (List.fold_left (fun acc x -> acc ^ (to_string x) ^ ",") "" l) in 
    if s = "" then s else "[" ^ s ^ "], " in 
  "(" ^ (string_of_int32_list ks) ^ ", " ^ (string_of_tree_list cn) ^ (string_of_bool r) ^ ", " ^ (string_of_int t) ^ ", " ^ (string_of_int id) ^ ")"
  end

module Storage = struct
  let plen = 2000
  let pointers = ref (List.map Int32.of_int (List.init plen (fun i -> i)))
  let storage = ref []

  let take_rev_pointer _ =
    if !pointers=[] then raise NoSpace
    else let rev_pointers = List.rev !pointers in
    let p = List.hd rev_pointers in
    let newp = List.rev (List.tl rev_pointers) in
    pointers := newp; p

  let take_node_pointers _ =
    let hpointer = take_rev_pointer () in
    let cblockpointer = take_rev_pointer () in
    hpointer, cblockpointer

  let take_spec_pointer p =
    if not (List.mem p !pointers) then raise NoSpace
    else let newp = List.filter (fun i -> not (Int32.equal i p)) !pointers in
    pointers := newp

  let deallocate pointer =
    let newp = pointer::(!pointers) in
    pointers := List.sort_uniq Int32.compare newp
  
  let read pointer =
    List.assoc pointer !storage
  
  let write (pointer, cs) =
    let olds = !storage in
    let news = List.filter (fun (p, _) -> not (Int32.equal pointer p)) olds in
    storage := (pointer, cs)::news
end

module Ids = struct
  let ids = ref []

  let store_id (id, (hpointer, cblockpointer)) =
    let current = !ids in
    let newi = List.filter ((fun (i, _) -> id != i)) current in
    ids := (id, (hpointer, cblockpointer))::newi

  let find_first_free_id _ =
    let ilist, _ = List.split !ids in
    let s = IdSet.of_list ilist in
    let max_id = IdSet.max_elt s in
    let free_ids set max = IdSet.(diff (of_list (List.init max (fun i -> (i+1)))) set) in
    let free = free_ids s max_id in
    if IdSet.is_empty free then (max_id+1)
    else IdSet.find_first (fun i -> i=i) free

  let get_node_pointers_from_id id = List.assoc id !ids
    
  let free_id id =
    let remove_id id =
      let current = !ids in
      let newi = List.filter (fun (i, _) -> id != i) current in
      ids := newi in
    try
    let hpointer, cblockpointer = get_node_pointers_from_id id in
    Storage.deallocate hpointer;
    if not (Int32.equal cblockpointer null_pointer) then Storage.deallocate cblockpointer;
    remove_id id
    with Not_found -> () (* id is not stored so do nothing *)
  end

module Serial = struct
  let rec read_pointers cs acc n lim =
    if n<lim then acc
    else let p = Cstruct.LE.get_uint32 cs (n*sizeof_pointer) in
    read_pointers cs (p::acc) (n-1) lim
  
  let head_block_into_cstruct ~block_size tree cblockpointer =
    let nk = Attrs.n_keys tree in
    let cs = Cstruct.create block_size in
    let ks, _, _, _, id = Attrs.get_all tree in
    (* id of this node *)
    Cstruct.LE.set_uint32 cs 0 (Int32.of_int id);
    (* pointer to block containing child node pointers *)
    Cstruct.LE.set_uint32 cs sizeof_pointer cblockpointer;
    (* number of keys in this node*)
    Cstruct.LE.set_uint32 cs (2*sizeof_pointer) (Int32.of_int nk);
    for n=0 to nk-1 do
      Cstruct.LE.set_uint32 cs ((n+3)*sizeof_pointer) (List.nth ks n);
    done;
    cs
  
  let data_block_into_cstruct ~block_size pl =
    let cs = Cstruct.create block_size in
    Cstruct.blit_from_string pl 0 cs 0 (String.length pl);
    cs
  
  let of_data_block_cstruct pointer = 
    Cstruct.to_string (Storage.read pointer)

  let child_block_into_cstruct ~block_size cpointers =
    let cs = Cstruct.create block_size in
    for n=0 to (List.length cpointers - 1) do
      Cstruct.LE.set_uint32 cs (n*sizeof_pointer) (List.nth cpointers n);
    done;
    cs
  
  let of_child_block_cstruct pointer n =
    let cs = Storage.read pointer in
    read_pointers cs [] n 0
  
  let rec of_cstruct t pointer =
    let hdblock = Storage.read pointer in
    let id = Int32.to_int (Cstruct.LE.get_uint32 hdblock 0) in
    let cblockpointer = Cstruct.LE.get_uint32 hdblock sizeof_pointer in
    let nk = Int32.to_int (Cstruct.LE.get_uint32 hdblock (2*sizeof_pointer)) in
    let keys = List.sort Int32.compare (read_pointers hdblock [] (nk+2) 3) in
    let r = id = 1 in (* root node has id 1 *)
    if Int32.equal cblockpointer null_pointer then Lf (keys, r, t, id)
    else let cpointers = of_child_block_cstruct cblockpointer nk in
    let cn = List.sort (fun tr1 tr2 -> 
      Int32.compare (Attrs.get_hd tr1) (Attrs.get_hd tr2)) 
      (List.map (of_cstruct t) cpointers) in Il (keys, cn, r, t, id)
  end

module Block_ops = struct
  let store_pl ~block_size k p =
    let cs = Serial.data_block_into_cstruct ~block_size p in
    Storage.take_spec_pointer k;
    Storage.write (k, cs)
  
  let add_key_to_head_block hpointer k =
    let hblock = Storage.read hpointer in
    let nk = Int32.to_int (Cstruct.LE.get_uint32 hblock (2*sizeof_pointer)) in
    Cstruct.LE.set_uint32 hblock (2*sizeof_pointer) (Int32.of_int (nk+1));
    Cstruct.LE.set_uint32 hblock ((nk+3)*sizeof_pointer) k;
    Storage.write (hpointer, hblock)

  let replace_key_in_head_block hpointer k newk =
    let hblock = Storage.read hpointer in
    let nk = Int32.to_int (Cstruct.LE.get_uint32 hblock (2*sizeof_pointer)) in
    let ks = 
      List.sort Int32.compare (Serial.read_pointers hblock [] (nk+2) 3) in
    let newks = List.filter (fun i -> not (Int32.equal k i)) ks in
    Cstruct.LE.set_uint32 hblock ((nk+2)*sizeof_pointer) newk;
    for n=0 to (nk-2) do
      Cstruct.LE.set_uint32 hblock ((n+3)*sizeof_pointer) (List.nth newks n);
    done;
    (if Int32.(equal newk zero) then
      Cstruct.LE.set_uint32 hblock (2*sizeof_pointer) (Int32.of_int (nk-1)));
    Storage.write (hpointer, hblock)
  
  let add_cpointer_to_child_block cblockpointer cpointer nk =
    let cblock = Storage.read cblockpointer in
    let _cpointers = Serial.read_pointers cblock [] nk 0 in
    Cstruct.LE.set_uint32 cblock ((nk+1)*sizeof_pointer) cpointer;
    Storage.write (cblockpointer, cblock)

  let remove_cpointer_from_child_block cblockpointer cpointer nk =
    let cblock = Storage.read cblockpointer in
    let cpointers = Serial.read_pointers cblock [] nk 0 in
    let new_cpointers = 
      List.filter (fun i -> not (Int32.equal cpointer i)) cpointers in
    for n=0 to nk-1 do
      Cstruct.LE.set_uint32 cblock (n*sizeof_pointer) (List.nth new_cpointers n);
    done;
    Storage.write (cblockpointer, cblock)
  end

module Node_writes = struct
  let get_cpointers cn =
    let cn_ids = List.map Attrs.get_id cn in
    let cn_pointer_pairs = List.map Ids.get_node_pointers_from_id cn_ids in
    let hpointers, _cpointers = List.split cn_pointer_pairs in hpointers

  let write_node ~block_size tree =
    let confirm_write hpointer cblockpointer id cn =
      Storage.write (hpointer, Serial.head_block_into_cstruct ~block_size tree cblockpointer);
      if not (Attrs.is_leaf tree) then begin
        let cpointers = get_cpointers cn in
        Storage.write (cblockpointer, Serial.child_block_into_cstruct ~block_size cpointers);
        Ids.store_id (id, (hpointer, cblockpointer)) 
      end else Ids.store_id (id, (hpointer, null_pointer)) in
    let (_, cn, r, _, id), leaf = Attrs.get_all tree, Attrs.is_leaf tree in
    let hpointer, cblockpointer = try Ids.get_node_pointers_from_id id
    with Not_found -> 
      if leaf then Storage.take_rev_pointer (), null_pointer
      else Storage.take_node_pointers () in
    let new_cbpointer = 
      let nullp = Int32.equal cblockpointer null_pointer in
      if r && not leaf && nullp then
        Storage.take_rev_pointer ()
      else if r && leaf && not nullp then
        (Storage.deallocate cblockpointer; null_pointer)
      else cblockpointer in
    confirm_write hpointer new_cbpointer id cn
  
  let write_node_split_update id nk k cpointer =
    let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
    Block_ops.add_cpointer_to_child_block cblockpointer cpointer nk;
    Block_ops.add_key_to_head_block hpointer k;
  end

module Tree_ops = struct
  (* adds key k, payload p and child c to each associated list *)
  let restore tree k c = match tree with
  | Lf ([], r, t, id) -> Lf (k::[], r, t, id)
  | Lf (v::next, r, t, id) -> Lf (k::v::next, r, t, id)
  | Il ([], cn, r, t, id) -> Il (k::[], c::cn, r, t, id)
  | Il (v::next, cn, r, t, id) -> Il (k::v::next, c::cn, r, t, id)

  (* returns [next key] or [] if k is the rightmost key in the node *)
  let rec get_next tree k = match tree with
  | Il (v::next, _::cn, r, t, id) ->
    if v=k then try [List.hd next] with Failure _ -> []
    else get_next (Il (next, cn, r, t, id)) k
  | Il ([], _, _, _, _) -> []
  | Lf (v::next, r, t, id) ->
    if v=k then try [List.hd next] with Failure _ -> []
    else get_next (Lf (next, r, t, id)) k
  | _ -> raise (MalformedTree "invalid tree structure")

  (* returns either the left child of key in kl/rightmost child if kl=[] *)
  let rec get_child tree kl =
    if Attrs.is_leaf tree then null_tree
    else match kl with
    | [] -> (match tree with
      | Il (_::next, _::cn, r, t, id) -> 
        get_child (Il (next, cn, r, t, id)) kl
      | Il ([], c::[], _, _, _) -> c
      | _ -> raise (MalformedTree "invalid tree structure"))
    | k::_ -> (match tree with
      | Il (v::next, c::cn, r, t, id) ->
        if v=k then c else get_child (Il (next, cn, r, t, id)) kl
      | Il ([], _::[], _, _, _) -> raise (NotFound "child node not found")
      | _ -> raise (MalformedTree "invalid tree structure"))

  (* replaces the child node associated with kl with newc *)
  let rec replace_child tree kl newc =
    if Attrs.is_leaf tree then null_tree
    else match kl with
    | [] -> (match tree with
      | Il (v::next, c::cn, r, t, id) -> 
      restore (replace_child (Il (next, cn, r, t, id)) kl newc) v c
      | Il ([], _::[], r, t, id) -> Il ([], newc::[], r, t, id)
      | _ -> raise (MalformedTree "invalid tree structure"))
    | k::_ -> (match tree with
      | Il (v::next, c::cn, r, t, id) ->
        if v=k then (Il (v::next, newc::cn, r, t, id))
        else restore (replace_child (Il (next, cn, r, t, id)) kl newc) v c
      | Il ([], _::[], _, _, _) -> raise (NotFound "child node not found")
    | _ -> raise (MalformedTree "invalid tree structure"))

  let rec insert_key tree k = match tree with
  | Lf (v::next, r, t, id) ->
    if k<v then Lf (k::v::next, r, t, id)
    else if k=v then Lf (k::next, r, t, id)
    else restore (insert_key (Lf (next, r, t, id)) k) v null_tree
  | Lf ([], r, t, id) -> Lf (k::[], r, t, id)
  | _ -> raise (InvalidOperation "cannot insert key in internal node")

  let rec remove_key tree k = match tree with
  | Lf (v::next, r, t, id) ->
    if v=k then Lf (next, r, t, id)
    else restore (remove_key (Lf (next, r, t, id)) k) v null_tree
  | _ -> raise (InvalidOperation "cannot remove key from internal node")

  (* replaces the child nodes of the key in kl with newc *)
  let rec replace_and_remove tree kl newc =
    match kl with
    | [] -> raise (NotFound "merge key not given")
    | k::_ -> (match tree with
      | Il (v::next, c1::c2::cn, r, t, id) ->
        if v=k then (Il (next, newc::cn, r, t, id)) 
        else 
          let tr = replace_and_remove (Il (next, (c2::cn), r, t, id)) kl newc
          in restore tr v c1
      | _ -> raise (NotFound "merge key to remove not found"))

  (* adds a key, payload and child to a node
   * key must not already be in the node *)
  let rec update_node tree k c1 c2 = match tree with
  | Il (v::next, c::cn, r, t, id) -> 
    if Attrs.is_leaf c1 != Attrs.is_leaf c then
      raise (MalformedTree "child node type mismatch")
    else if Attrs.get_hd c1 = Attrs.get_hd c then
      Il (k::v::next, c1::c2::cn, r, t, id)
    else restore (update_node (Il (next, cn, r, t, id)) k c1 c2) v c
  | Il ([], c::cn, r, t, id) -> (* right-most node *)
    if Attrs.is_leaf c1 != Attrs.is_leaf c then 
      raise (MalformedTree "child node type mismatch")
    else if Attrs.get_hd c1 = Attrs.get_hd c then 
      Il (k::[], c1::c2::cn, r, t, id)
    else raise (NotFound "child node to replace not found")
  | _ -> raise (MalformedTree "invalid tree structure")
  end

open Attrs
open Tree_ops

(* searches for and returns a node in the tree containing key k *)
let rec search tree k = let eq a b = a=b in
  let search_next tnode ks nv nc  = 
    let tnext = search tnode k in (match tnext with
    | Il ([], _::[], _, _, _) -> restore tnext nv nc
    | Il (v::_, _::_, _, _, _) -> 
      if List.exists (eq v) ks then restore tnext nv nc else tnext
    | _ -> tnext) in
  match tree with
  | Il (v::next, c::cn, r, t, id) -> 
    if k=v then tree
    else if k<v then search c k
    else search_next (Il (next, cn, r, t, id)) (v::next) v c
  | Il ([], c::[], _, _, _) -> search c k
  | Lf (v::next, r, t, id) ->
    if k=v then tree
    else if k>v then
      if next=[] then raise (NotFound ("key not found"))
      else restore (search (Lf (next, r, t, id)) k) v null_tree
    else raise (NotFound "key not found")
  | _ -> raise (NotFound "key not found")

(* splits a node in two on a given key index
 * migrates key to parent node and returns parent, which may now be full
 * if the node is a root, this can increase the depth of the tree by 1 *)
let split ~block_size tree parent m ignore =
  let split_node tree lid rid =
    let ks, cn, _, t, _ = get_all tree in
    let mk, lks, rks = split_ks m ks in
    let lcn, rcn = split_cn (m+1) cn in
    let tl, tr = 
      if (is_leaf tree) then Lf (lks, false, t, lid), Lf (rks, false, t, rid)
      else Il (lks, lcn, false, t, lid), Il (rks, rcn, false, t, rid) in 
    List.hd mk, tl, tr in
  let (_, _, root, t, cid), pid = get_all tree, get_id parent in
  let root_split = 
    if fst ignore then false else (root && (get_hd parent) = (get_hd tree)) in
  if is_leaf parent && not root_split then 
    raise (InvalidOperation "cannot split with leaf node as parent")
  else let lid, rid = 
    if fst ignore then snd ignore
    else if root_split then let i = Ids.find_first_free_id () in i, i+1
    else cid, Ids.find_first_free_id () in
    let mk, t_left, t_right = split_node tree lid rid in
    let newt = if root_split then Il (mk::[], t_left::t_right::[], true, t, pid)
    else update_node parent mk t_left t_right in
    if fst ignore then newt else begin
      Node_writes.write_node ~block_size t_left; 
      Node_writes.write_node ~block_size t_right;
      begin 
      if root_split then Node_writes.write_node ~block_size newt
      else
        let cpointer, _ = Ids.get_node_pointers_from_id rid in
        Node_writes.write_node_split_update pid (n_keys parent) mk cpointer
      end; newt
    end

let rec insertv ~block_size tree k p ckey ignore =
  let no_split = false, (-1, -1) in
  let continue = insertv ~block_size in
  let confirm_insert key id =
    Block_ops.store_pl ~block_size key p;
    let hpointer, _ = Ids.get_node_pointers_from_id id in
    Block_ops.add_key_to_head_block hpointer k;
    insert_key tree k in
  let _, _, root, t, id = get_all tree in
  let lim = 2*t-1 in
  let empty, full = (ckey < Int32.zero), n_keys tree = lim in
  if (full && root && not ignore) then
    let tr = split ~block_size tree tree (t-1) no_split in continue tr k p (get_hd tr) false
  else if (full && not root && not ignore) then 
    raise (MalformedTree "full node not split ahead of time")
  else if (empty && root) then confirm_insert k id
  else if empty then raise (MalformedTree "empty non-root node")
  else if k=ckey then (Block_ops.store_pl ~block_size k p; tree)
  else let next = get_next tree ckey in
    if (k>ckey && next != []) then continue tree k p (List.hd next) ignore
    else let pkey = if k<ckey then [ckey] else [] in
    if (is_leaf tree) then confirm_insert k id
    else let c = get_child tree pkey in
      if (n_keys c) = lim then 
        let tr = split ~block_size c tree (t-1) no_split in 
        continue tr k p (Attrs.get_hd tr) true
      else 
        let newc = continue c k p (Attrs.get_hd c) false in 
        replace_child tree pkey newc
  
let insert ~block_size tree k p = 
  let _, _, root, _, _ = get_all tree in
  if not root then 
    raise (InvalidOperation "insert can only be called on a root node")
  else insertv ~block_size tree k p (try get_hd tree with Failure _ -> Int32.minus_one) false
    
(* takes two child nodes and merges them into one node 
 * the parent node loses a key in the process
 * if the node is a root, this can decrease the depth by 1 *)
let rec merge ~block_size parent ckey s1 s2 ignore =
  let check_length l t = 
    if ((l < t-1 || l > 2*t-1) && not ignore) then 
      raise (InvalidOperation "merge will result in an invalid node") 
    else () in
  let _, _, root, t, pid = get_all parent in
  let one_key, next = n_keys parent = 1, get_next parent ckey in
  let s1_leaf, s2_leaf = is_leaf s1, is_leaf s2 in
  if ((s1_leaf && not s2_leaf) || (s2_leaf && not s1_leaf)) then
    raise (MalformedTree "internal node and leaf node at same level")
  else if (is_leaf parent) then 
    raise (InvalidOperation "cannot merge with leaf node as parent")
  else
    let m1, m2 = get_child parent [ckey] = s1, get_child parent next = s2 in
    if m1 && m2 then
      let k1s, cn1, _, _, lid = get_all s1 in
      let k2s, cn2, _, _, rid = get_all s2 in
      let _ = check_length (List.length k1s + List.length k2s + 1) t in
      let merged_ks, merged_cn = k1s @ (ckey::k2s), cn1 @ cn2 in
      let reduce = root && one_key && not ignore in
      let mid = if reduce then pid else lid in
      let s = if s1_leaf then Lf (merged_ks, reduce, t, mid)
      else Il (merged_ks, merged_cn, reduce, t, mid) in
      if reduce then begin
        Ids.free_id lid; Ids.free_id rid;
        Node_writes.write_node ~block_size s; s 
      end else begin
        let tr = replace_and_remove parent [ckey] s in
        if ignore then tr else begin
          Node_writes.write_node ~block_size s;
          let hpointer, cblockpointer = Ids.get_node_pointers_from_id pid in
          let cpointer, _ = Ids.get_node_pointers_from_id rid in
          Block_ops.remove_cpointer_from_child_block cblockpointer cpointer (n_keys parent);
          Block_ops.replace_key_in_head_block hpointer ckey Int32.zero;
          Ids.free_id rid; tr
          end
      end
    else if next=[] then raise (NotFound "could not find sibling nodes")
    else merge ~block_size parent (List.hd next) s1 s2 ignore

let rec find_predecessor tree k = 
  let rec get_largest tree =
    let rec last l = match l with
    | c::cs -> if cs=[] then c else last cs 
    | [] -> raise (Failure "empty list") in
    if is_leaf tree then
      let ks, _, _, _, _ = get_all tree in last ks
    else let c2 = get_child tree [] in get_largest c2 
  in match tree with
  | Lf (v::next, r, t, id) ->
    if next=[] then raise (NotFound "key not found")
    else if List.hd next=k then v
    else find_predecessor (Lf (next, r, t, id)) k
  | Il (v::next, c1::c2::cn, r, t, id) ->
    if k=v then get_largest c1
    else if k<v then find_predecessor c1 k
    else if next=[] then find_predecessor c2 k 
    else find_predecessor (Il (next, c2::cn, r, t, id)) k
  | _ -> raise (MalformedTree "tree structure invalid")

let rec find_successor tree k = 
  let rec get_smallest tree =
    if is_leaf tree then get_hd tree
    else let c1 = get_child tree [get_hd tree] in get_smallest c1
  in match tree with
  | Lf (v::next, r, t, id) ->
    if next=[] then raise (NotFound "key not found")
    else if v=k then List.hd next
    else find_successor (Lf (next, r, t, id)) k
  | Il (v::next, c1::c2::cn, r, t, id) ->
    if k=v then get_smallest c2
    else if k<v then find_successor c1 k
    else if next=[] then find_successor c2 k 
    else find_successor (Il (next, c2::cn, r, t, id)) k
  | _ -> raise (MalformedTree "tree structure invalid")

(* swaps the positions of (oldkey, oldpl) and (newkey, newpl) in a tree
 * newkey must be either the predecessor or successor of oldkey 
 * it must also be at a lower depth than oldkey
 * found = 0 - not found
 * found = 1 - found in this node 
 * found = 2 - found higher in the tree *)
let rec swap tree ok nk ckey found index =
  let replace id k1 k2 =
    let hpointer, _ = Ids.get_node_pointers_from_id id in
    Block_ops.replace_key_in_head_block hpointer k1 k2 in
  let swap_child tree kl f = 
    let c = get_child tree kl in 
    let newc = swap c ok nk (get_hd c) f 0 in
    replace_child tree kl newc in
  let swap_next tree kl f = 
    swap tree ok nk (List.hd kl) f (index+1) in
  let replace_in_list l n = 
    List.mapi (fun i a -> if i=index then n else a) l in
  let ks, cn, r, t, id = get_all tree in
  let leaf, next = is_leaf tree, get_next tree ckey in
  let successor = nk>ok in
  if ckey=nk then
    if (found=0 || not leaf) then raise (MalformedTree "order violation")
    else let tr = Lf (replace_in_list ks ok, r, t, id) in
    if found=1 then tr else (replace id nk ok; tr)
  else if (ckey=ok || found>0) then
    let newt = if ckey!=ok then tree else begin
      replace id ok nk;
      if leaf then Lf (replace_in_list ks nk, r, t, id)
      else Il (replace_in_list ks nk, cn, r, t, id) 
    end in
    if (next=[] && leaf) then 
      raise (NotFound "at least one key in swap not found")
    (* either key and successor are both in this leaf 
       or predecessor is the rightmost key *)
    else if leaf then swap_next newt next (max 1 found)
    else if found=0 then let kl = if successor then next else [nk] in 
      swap_child newt kl 2 (* pick edge to go down *)
    else (* find smallest key in subtree if successor *)
      if successor then swap_child newt [ckey] 2
      else if next=[] then swap_child newt next 2
      else swap_next newt next (max 1 found) (* and largest key if predecessor *)
  else if ckey>ok then
    if next=[] then swap_child tree next 0
    else swap_next tree next 0
  else swap_child tree [ckey] 0

(* redistributes a key from morec to its immediate sibling node *)
let steal ~block_size tree ckey morec =
  let _, _, _, t, pid = get_all tree in
  let next = get_next tree ckey in
  let ca, cb = get_child tree [ckey], get_child tree next in
  let ca_id, cb_id = get_id ca, get_id cb in
  let mt = merge ~block_size tree ckey ca cb true in
  let merged_child = get_child mt next in
  let lim = (if ca=morec then (n_keys ca)-1 else if cb=morec then t else -1) in
  if lim = -1 then raise (NotFound "child node not found")
  else let tr = split ~block_size merged_child mt lim (true, (ca_id, cb_id)) in
  let new_sp = let ks, _, _, _, _ = get_all merged_child in List.nth ks lim in
  let lessc = if ca=morec then cb else ca in
  let lid, mid = get_id lessc, get_id morec in
  let hpointer, _ = Ids.get_node_pointers_from_id pid in 
  let lpointer, lcpointer = Ids.get_node_pointers_from_id lid in
  let mpointer, mcpointer = Ids.get_node_pointers_from_id mid in
  Block_ops.replace_key_in_head_block hpointer ckey new_sp;
  Block_ops.replace_key_in_head_block mpointer new_sp Int32.zero;
  Block_ops.add_key_to_head_block lpointer ckey;
  let moved_child_key = if morec=cb then [get_hd morec] else [] in
  if is_leaf morec then tr else begin
    let moved_cpointer, _ = 
      Ids.get_node_pointers_from_id (get_id (get_child morec moved_child_key)) in
    Block_ops.remove_cpointer_from_child_block mcpointer moved_cpointer (n_keys morec);
    Block_ops.add_cpointer_to_child_block lcpointer moved_cpointer (n_keys lessc); tr
  end

let rec deletev ~block_size tree k ckey swapped =
  let continue = deletev ~block_size in
  if ckey<Int32.zero then tree
  else 
    let ks, _, _, t, id = get_all tree in
    let leaf, next = is_leaf tree, get_next tree ckey in
    let ca, cb = 
    if not leaf then get_child tree [ckey], get_child tree next 
    else null_tree, null_tree in
    let l1, l2 = n_keys ca, n_keys cb in
    let left, right, lempty, rempty = k<ckey, k>ckey && next=[], l1<t, l2<t in
    (* swapping causes an inversion *)
    let leftc, rightc = if swapped then not left, left else left, right in
    if k=ckey then
      if leaf then begin
        let hpointer, _ = Ids.get_node_pointers_from_id id in
        Block_ops.replace_key_in_head_block hpointer k Int32.zero;
        Storage.deallocate k;
        remove_key tree k
      end else if not (lempty && rempty) then
        let key_to_swap = (* swap with inorder predecessor/successor *)
          (if lempty then find_successor else find_predecessor) tree ckey in
        let tr = swap tree ckey key_to_swap ckey 0 (get_index ks ckey 0) in 
        continue tr k key_to_swap true
        (* merge around key to delete if neither child node has enough keys *)
      else 
        let tr = merge ~block_size tree ckey ca cb false in continue tr k (get_hd tr) false
    else if not (leftc || rightc) then continue tree k (List.hd next) false
    else if not leaf then
      let c = if lempty || (rightc && not rempty) then cb else ca in
      let ok = (leftc && not lempty) || (rightc && not rempty) in
      if ok then (* k is in subtree which can lose a key *)
        let c_del = continue c k (get_hd c) false in
        replace_child tree (if leftc then [ckey] else next) c_del
      else if lempty && rempty then (* merge needed *)
        let tr = merge ~block_size tree ckey ca cb false in continue tr k (get_hd tr) false
        (* steal a key a sibling of the subtree containing k *)
      else let tr = steal ~block_size tree ckey c in continue tr k (get_hd tr) false
    else if left || right then raise (NotFound "key to delete not found")
    else continue tree k (List.hd next) false (* continue searching this leaf *)

let delete tree k = 
  let _, _, root, _, _ = get_all tree in
  if not root then 
    raise (InvalidOperation "delete can only be called on a root node")
  else deletev tree k (try get_hd tree with Failure _ -> Int32.minus_one) false

let rec insert_list ~block_size tree items = 
  match items with
| (k, pl)::its ->
  insert_list ~block_size (insert ~block_size tree k pl) its
| [] -> tree

let rec delete_list ~block_size tree keys = match keys with
| k::ks -> delete_list ~block_size (delete ~block_size tree k) ks
| [] -> tree

let create_btree ~block_size t = 
  let tr = Lf ([], true, t, 1) in
  Storage.pointers := List.map Int32.of_int (List.init Storage.plen (fun i -> i));
  Storage.storage := [];
  Ids.ids := [];
  Node_writes.write_node ~block_size tr; tr
