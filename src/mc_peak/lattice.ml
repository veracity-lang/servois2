open Util

module type ORDERED = 
sig
  type t
  val lte : t -> t -> bool
  val string_of: t -> string
  val v_of_string: string -> t
end

module type LATTICE = functor(Elem: ORDERED) ->
sig
  type v = Elem.t                    (*  *)
  type 'a el
  type 'a t

  val join: v el -> v el -> v el t -> v el 
  val meet: v el -> v el -> v el t -> v el
  val lte: v -> v -> v el t -> bool option

  val top: v el t -> v el option
  val bottom: v el t -> v el option

  val construct: v list -> v el t

  val save: v el t -> out_channel -> unit
  val load: in_channel -> v el t

  val list_of: v el t -> v list

  val length: v el t -> int

  val find_opt: (v -> bool) -> v el t -> v option

  (* val add: v -> v el t -> v el t *)

  val remove: int -> v el t -> v el t

  val remove_v: v -> v el t -> v el t

  val remove_upperset: v -> v el t -> v el t

  val chains_of: v el t -> v list list

  val coveredbyset: v -> v el t -> v list
  
  val coveringset: v -> v el t -> v list

  val upperset: int -> v el t -> (int * v el) list
  val upperset_of_v: v -> v el t -> v list

  val lowerset: int -> v el t -> (int * v el) list

  val string_of_el: v el -> string
  val string_of: v el t -> string
end 

module Lattice : LATTICE = functor (Elem: ORDERED) -> 
struct
  module StoreM = Map.Make(struct type t = int let compare x y = x - y end)

  type v = Elem.t
  type 'a el = Bottom of { covered_by: int list }
          | Top of {covering: int list }
          | Element of { value: 'a; covering: int list; covered_by: int list } 
  type 'a t = 'a StoreM.t

  (* let join = failwith "Lattice join is undefined"
   * let meet = failwith "Lattice meet is undefined" *)

   let string_of_el: v el -> string = 
    fun el -> 
    let string_of_keys ks = List.map string_of_int ks
                            |> String.concat " ; "
    in
    match el with
    | Bottom {covered_by} -> sp "Bottom, Covered_By: [%s]" (string_of_keys covered_by) 
    | Top  {covering} -> sp "Top, Covering: [%s]" (string_of_keys covering)
    | Element {value = p; covered_by; covering} -> 
      (sp "Elem: %s, Covered_By: [%s], Covering: [%s]" 
         (Elem.string_of p) (string_of_keys covered_by) (string_of_keys covering))  

  let string_of: v el t -> string = 
    fun l ->
    String.concat "\n" 
      (List.map (fun (idk, el) -> sp "%d:%s" idk (string_of_el el)) (StoreM.bindings l))

  let id_bottom: int = 0
  let id_top: int = 1
  let id_next: unit -> int = 
    let gen = ref 1 in
    fun () -> gen := !gen + 1; !gen

  let find_binding_opt: (v -> bool) -> v el t -> (int * v el) option = 
    fun f l -> 
    StoreM.choose_opt @@ StoreM.filter (
        fun _ el -> 
          match el with 
          | Element {value = a; _} -> f a 
          | (Top _ | Bottom _) -> false 
      ) l
  
  let find_opt: (v -> bool) -> v el t -> v option = 
    fun f l ->
    let maybe_binding = find_binding_opt f l in 
    Option.bind maybe_binding (
      fun (_, el) ->
        match el with
        | Element {value = a; _} -> Some a
        | (Top _ | Bottom _) -> None)
        

  let construct : v list -> v el t = 
    fun els -> 
    let l = List.fold_left (fun l el_val -> 
        StoreM.add (id_next ()) (Element {value = el_val; covering = []; covered_by = []}) l
      ) StoreM.empty els
    in
    let l = StoreM.mapi (fun idk el ->
        match el with
        | (Bottom _ | Top _) -> el
        | Element {value = p; _} -> ( 
          let downset, upset, _ = StoreM.fold (fun idk' el' (downset, upset, l) ->
              match el' with
              | (Bottom _ | Top _) -> (downset, upset, l)
              | Element {value = p'; _} ->
                if Elem.lte p p' then (downset, idk'::upset, l)
                else if Elem.lte p' p then (idk'::downset, upset, l)
                else (downset, upset, l)) l ([], [], l) 
          in
          let covering = List.map (fun idk1 -> List.filter ((!=) idk1) downset
                                               |> List.map (fun idk2 -> (idk1, idk2))) downset
                         |> List.flatten
                         |> List.fold_left (fun acc (idk1, idk2) -> 
                             match (StoreM.find idk1 l), (StoreM.find idk2 l) with 
                             | Element {value = p1; _}, Element {value = p2; _} ->
                               if Elem.lte p1 p2 then List.filter ((!=) idk1) acc
                               else acc
                             | _, _ -> acc
                           ) downset
                       
          in
          let covering = match covering with
            | [] -> [id_bottom]
            | _ -> covering 
          in
          let covered_by = List.map (fun idk1 -> List.filter ((!=) idk1) upset
                                               |> List.map (fun idk2 -> (idk1, idk2))) upset
                         |> List.flatten
                         |> List.fold_left (fun acc (idk1, idk2) -> 
                             match (StoreM.find idk1 l), (StoreM.find idk2 l) with 
                             | Element {value = p1; _}, Element {value = p2; _} ->
                               if Elem.lte p1 p2 then List.filter ((!=) idk2) acc
                               else acc
                             | _, _ -> acc
                           ) upset
                       
          in
          let covered_by = match covered_by with
            | [] -> [id_top]
            | _ -> covered_by 
          in
          Element {value= p; covering= covering; covered_by= covered_by } )
      ) l
    in
    let bottom_covered_by, top_covering = StoreM.fold (fun idk el (bced_by, tcing) -> 
        match el with
        | (Bottom _ | Top _) -> (bced_by, tcing) 
        | Element {covering; covered_by; _} ->
          (if List.exists ((=) id_bottom) covering then (idk::bced_by) else bced_by),
          (if List.exists ((=) id_top) covered_by then (idk::tcing) else tcing)
     
      ) l ([], [])
    in
     StoreM.add id_bottom (Bottom {covered_by = bottom_covered_by}) l
     |> StoreM.add id_top (Top {covering = top_covering })
   
  let save l oc = 
    let encode_el = function
      | Top {covering} -> sp "[%s]" (String.concat ";" (List.map string_of_int covering))
      | Element {value; covering; covered_by} -> 
        sp "%s,[%s],[%s]" (Elem.string_of value)
          (String.concat ";" (List.map string_of_int covering))
          (String.concat ";" (List.map string_of_int covered_by))
      | Bottom {covered_by} -> sp "[%s]" (String.concat ";" (List.map string_of_int covered_by))
    in
    let snapshot_of l = String.concat "\n" @@ 
      List.map (fun (id, el) -> sp "%d,%s" id (encode_el el)) (StoreM.bindings l)
    in 
    Printf.fprintf oc "%s" (snapshot_of l)  
 
  let load ic = 
    let parse_el_top s = 
      let s_length = String.length s in     
      let covering_s = String.sub s 1 (s_length - 2) in 
      let covering = List.map int_of_string (String.split_on_char ';' covering_s) in
      Top {covering = covering}
    in
    let parse_el_bottom s = 
      let s_length = String.length s in     
      let covered_by_s = String.sub s 1 (s_length - 2) in 
      let covered_by = List.map int_of_string (String.split_on_char ';' covered_by_s) in
      Bottom {covered_by = covered_by}
    in
    let parse_el s = 
      let s_length = String.length s in
      let v_delim = String.index_from s 0 ',' in
      let v_s = String.sub s 0 v_delim in
      let v = Elem.v_of_string v_s in 
      let cing_delim = String.index_from s (v_delim + 1) ',' in
      let covering_s = String.sub s (v_delim + 2) (cing_delim - v_delim - 3) in
      let covering = List.map int_of_string (String.split_on_char ';' covering_s) in
      let covered_by_s = String.sub s (cing_delim + 2) (s_length - cing_delim - 3) in
      let covered_by = List.map int_of_string (String.split_on_char ';' covered_by_s) in
      Element {value = v; covering = covering; covered_by = covered_by}
    in
    let parse_el_binding s = 
      let id_el_split = String.index_from s 0 ',' in
      let id = int_of_string (String.sub s 0 id_el_split) in
      let el_s = String.sub s (id_el_split + 1) ((String.length s) - id_el_split - 1) in
      if id = id_bottom then (id_bottom, (parse_el_bottom el_s)) 
      else if id = id_top then (id_top, (parse_el_top el_s))
      else (id, (parse_el el_s))
    in
    let rec add_el inc l = 
      try
        let line = input_line inc in
        let id, el = parse_el_binding line in
        add_el inc (StoreM.add id el l)
      with End_of_file ->
        l
    in add_el ic StoreM.empty

  let list_of: v el t -> v list  =
    fun l -> 
    List.flatten @@ List.map (fun (_, el) ->
        match el with
        | Element {value = p; _} -> [p]
        | (Bottom _ | Top _) -> []) (StoreM.bindings l)

  let bottom: v el t -> v el option = fun l -> StoreM.find_opt id_bottom l
  let top: v el t -> v el option = fun l -> StoreM.find_opt id_top l     

  let length: v el t -> int = 
    fun l -> 
    let sz = StoreM.cardinal l in
    match bottom l, top l with
    | Some _, Some _ -> sz - 2
    | (Some _, None | None, Some _) -> sz - 1
    | None, None -> sz 

  let coveredbyset: v -> v el t -> v list = 
    fun a l -> 
    match find_binding_opt (fun a' -> a' = a) l with
    | None -> []
    | Some (_, Top _) -> []
    | (Some (_, Element {covered_by; _}) | Some (_, Bottom {covered_by})) ->
      List.fold_right (
        fun idk acc ->
          match StoreM.find idk l with
            | Top _ -> acc
            | Element { value = a_; _} -> a_::acc
            | Bottom _ -> acc
      ) covered_by []

  let coveringset: v -> v el t -> v list = 
    fun a l -> 
    match find_binding_opt (fun a' -> a' = a) l with
    | None -> []
    | Some (_, Bottom _) -> []
    | (Some (_, Element {covering; _}) | Some (_, Top {covering})) ->
      List.fold_right (
        fun idk acc ->
          match StoreM.find idk l with
            | Top _ -> acc
            | Element { value = a_; _} -> a_::acc
            | Bottom _ -> acc
      ) covering []

  let upperset: int -> v el t -> (int * v el) list = 
    fun idk l ->
    let rec ups l covered_by acc = 
      match covered_by with
      | [] -> acc
      | idk'::ids -> 
        match List.find_opt (fun (id_, _) -> id_ = idk') acc with
        | None ->
          begin match StoreM.find idk' l with
            | (Top _) as el' -> (idk', el')::acc
            | (Element {covered_by = covered_by'; _}) as el' ->
              ups l covered_by' ((idk', el')::acc) |> ups l ids  
            | Bottom _ -> acc
          end
        | Some _ -> ups l ids acc
    in
    match StoreM.find_opt idk l with
    | None -> [] 
    | Some Top _ -> []
    | Some (Element {covered_by; _} as el) -> ups l covered_by [(idk, el)]
    | Some (Bottom {covered_by} as el) -> ups l covered_by [(idk, el)] 
              
  let upperset_of_v: v -> v el t -> v list = 
    fun a l -> 
    match find_binding_opt (fun a' -> a' = a) l with
    | None -> []
    | Some (_, Top _) -> []
    | Some (idk, Element _) ->
      List.fold_right (fun (idk_, el_) acc ->
          begin match el_ with
            | (Top _ | Bottom _) -> acc
            | Element { value = a_; _} -> a_::acc 
          end
        ) (upperset idk l) []
    | Some (_, Bottom _) -> list_of l
  
  let lowerset: int -> v el t -> (int * v el) list = 
    fun idk l ->
    let rec lows l covering acc = 
      match covering with
      | [] -> acc
      | idk'::ids -> 
        match List.find_opt (fun (id_, _) -> id_ = idk') acc with
        | None ->
          begin match StoreM.find idk' l with
            | Top _  -> acc
            | (Element {covering = covering'; _}) as el' ->
              lows l covering' ((idk', el')::acc) |> lows l ids
            | (Bottom _) as el'  -> (idk', el')::acc
          end
        | Some _ -> lows l ids acc
    in
    match StoreM.find_opt idk l with
    | None -> []
    | Some (Top {covering} as el) -> lows l covering [(idk, el)]
    | Some (Element {covering; _} as el) -> lows l covering [(idk, el)]
    | Some Bottom _ -> []

  let meet a b l = 
    (* compute the lowerset of b and then, 
       starting with "a" by breadth-first-searching the graph
       for an element that is in the lowerset of b. 
       The first element found is the meet *)
    let rec find_meet las lowb =   
      match las with
      | [] -> raise @@ Failure "Unreachable state. Bottom should have been found"
      | la::las' ->
        if (List.exists ((=) la) lowb) then StoreM.find la l
        else begin
          match StoreM.find la l with
          | Top _ -> raise @@ Failure "Top should not appear in covering set"
          | Element {covering; _} -> find_meet (las @ covering) lowb
          | (Bottom _) as bottom -> bottom 
        end 
    in
    if (a = b) then a 
    else begin
      let b_key, _ = StoreM.choose @@ StoreM.filter (fun _ el -> el = b) l in
      let lowb = List.map fst (lowerset b_key l) |> List.filter ((!=) b_key) in
      match a with
      | Top _ -> b
      | Element {covering; _} -> find_meet covering lowb
      | Bottom _ -> a 
    end

  let join a b l = 
    (* compute the upperset of b and then, 
       starting with "a" by breadth-first-searching the graph
       for an element that is in the upperset of b. 
       The first element found is the join *)
    let rec find_join uas upb =   
      match uas with
      | [] -> raise @@ Failure "Unreachable state. Top should have been found"
      | ua::uas' ->
        if (List.exists ((=) ua) upb) then StoreM.find ua l
        else begin
          match StoreM.find ua l with
          | (Top _) as top -> top
          | Element {covered_by; _} -> find_join (uas @ covered_by) upb
          | Bottom _ -> raise @@ Failure "Bottom should not appear in covering set" 
        end 
    in
    if (a = b) then a
    else begin
      let b_key, _ = StoreM.choose @@ StoreM.filter (fun _ el -> el = b) l in
      let upb = List.map fst (upperset b_key l) |> List.filter ((!=) b_key) in
      match a with
      | Top _ -> a
      | Element {covered_by; _} -> find_join covered_by upb
      | Bottom _ -> b 
    end
    
  let lte va vb l = 
    match (find_binding_opt ((=) va) l), (find_binding_opt ((=) vb) l) with
    | None, _ -> None
    | _ , None -> None
    | Some (_, Top _), _ -> Some false
    | Some (_, Bottom _), _ -> Some true
    | _, Some (_, Top _) -> Some true
    | _, Some (_, Bottom _) -> Some false
    | Some (_, a), Some (_, b) -> 
      let meet_ab = meet a b l in
      if a = meet_ab then Some true else Some false

  let el_covering_update: int -> int list -> v el t -> v el t = 
    fun idk new_covering l -> 
    StoreM.update idk (Option.map (
        fun el ->
          match el with
          | Top elc -> Top { covering=new_covering } 
          | Element elc -> Element {elc with covering = new_covering}
          | Bottom _ -> el   
      )) l   
 
  let el_covering_append: int -> int list -> v el t -> v el t = 
    fun idk idks_to_append l -> 
    StoreM.update idk (Option.map (
        fun el ->
          match el with
          | Top {covering} -> Top { covering=covering @ idks_to_append } 
          | Element ({covering;_} as elc) -> 
            Element {elc with covering = covering @ idks_to_append }
          | Bottom _ -> el   
      )) l
  
  let el_covered_by_update: int -> int list -> v el t -> v el t = 
    fun idk new_covered_by l -> 
    StoreM.update idk (Option.map (
        fun el ->
          match el with
          | Top _ -> el 
          | Element elc -> Element {elc with covered_by = new_covered_by}
          | Bottom elc -> Bottom {covered_by = new_covered_by}   
      )) l 

  let el_covered_by_append: int -> int list -> v el t -> v el t = 
    fun idk idks_to_append l -> 
    StoreM.update idk (Option.map (
        fun el ->
          match el with
          | Top _ -> el 
          | Element ({covered_by;_} as elc) -> 
            Element {elc with covered_by = covered_by @ idks_to_append}
          | Bottom {covered_by} -> Bottom {covered_by = covered_by @ idks_to_append}   
      )) l

  (* let add: v -> v el t -> v el t = 
   *   failwith "Add element to lattice is undefined" *)
    
  let remove: int -> v el t -> v el t = 
    fun idk l ->
    let reconnect_covering x_idk x_cby_idks y_idk l = 
       match StoreM.find_opt y_idk l with
         | None -> l 
         | Some Top _ -> l
         | (Some Element {covered_by; _} | Some Bottom {covered_by}) ->
           let covered_by' = List.filter ((!=) x_idk) covered_by in
           let l = el_covered_by_update y_idk covered_by' l in 
           let us = upperset y_idk l in  
           let idks_us = List.map fst us in 
           let new_to_covered_by = 
             List.filter (fun id_ -> not @@ List.exists ((=) id_) idks_us) x_cby_idks 
           in
           let l = List.fold_right 
               (fun idk_ l_ -> el_covering_append idk_ [y_idk] l_) new_to_covered_by l 
           in        
           el_covered_by_update y_idk (covered_by' @ new_to_covered_by) l             
    in
    let reconnect_covered_by x_idk x_cing_idks y_idk l = 
      match StoreM.find_opt y_idk l with
      | None -> l
      | (Some Top {covering} | Some Element {covering;_})-> 
        let covering' = List.filter ((!=) x_idk) covering in
        let l = el_covering_update y_idk covering' l in
        let ls = lowerset y_idk l in
        let idks_ls = List.map fst ls in
        let new_to_covering = 
          List.filter (fun id_ -> not @@ List.exists ((=) id_) idks_ls) x_cing_idks 
        in
        let l = List.fold_right 
            (fun idk_ l_ -> el_covered_by_append idk_ [y_idk] l_) new_to_covering l
        in
        el_covering_update y_idk (covering' @ new_to_covering) l
      | Some Bottom _ -> l 
    in
    let reconnect_nodes x_idk x_cing_idks x_cby_idks l = 
      List.fold_right 
          (fun idk_ l_ -> 
            reconnect_covering x_idk x_cby_idks idk_ l_ 
          ) x_cing_idks l 
      |> List.fold_right 
          (fun idk_ l_ ->
            reconnect_covered_by x_idk x_cing_idks idk_ l_
          ) x_cby_idks
    in
    match StoreM.find_opt idk l with
    | None -> l
    | Some Top _ -> failwith "Lattice.remove : Top is not removable"   
    | Some Element {covered_by; covering; _} ->
      reconnect_nodes idk covering covered_by l |> StoreM.remove idk
    | Some Bottom _ -> failwith "Lattice.remove : Bottom is not removable"

  let remove_v: v -> v el t -> v el t = 
    fun a l -> 
    match find_binding_opt ((=) a) l with
    | None -> l
    | Some (_, Top _) -> failwith "Lattice.remove : Top is not removable"   
    | Some (idk, Element _) -> remove idk l
    | Some (_, Bottom _) -> failwith "Lattice.remove : Bottom is not removable"

  let remove_upperset: v -> v el t -> v el t = 
    fun a l -> 
    let rec rm els l_ = 
      match els with
      | [] -> l_
      | (idk, el)::els' -> 
        begin match el with 
          | ( Top _ | Bottom _ )  -> rm els' l_
          | Element _ -> rm els' (remove idk l_)
        end
    in
    match find_binding_opt (fun a' -> a' = a) l with
    | None -> l
    | Some (_, Top _) -> failwith "Lattive.remove_upperset : Top is not removable"
    | Some (idk, Element _) -> rm (upperset idk l) l
    | Some (_, Bottom _) -> failwith "Lattice.remove_upperset : Bottom is not removable"

  let chains_of: v el t -> v list list = 
    fun l -> 
    let rec to_chains wl cs = 
      match wl with
      | [] -> cs
      | (idk, chain_prefix)::wl' -> 
        match StoreM.find_opt idk l with
        | None -> to_chains wl' cs 
        | Some (Element {value = p; covered_by; _}) ->
          begin match covered_by with
            | ([] | [1]) -> to_chains wl' ((p::chain_prefix)::cs)        (* 1 is id_top*)
            | _ -> 
              let new_wl' = List.fold_right (fun idk acc -> (idk, p::chain_prefix)::acc) 
                  covered_by wl' in
              to_chains new_wl' cs
          end          
        | Some _ -> to_chains wl' cs 
    in
    match bottom l with
    | None -> []
    | Some (Bottom {covered_by}) -> 
      let wl = List.map (fun idk -> (idk, [])) covered_by in
      to_chains wl [] |> List.map List.rev
    | Some _ -> []

end 
