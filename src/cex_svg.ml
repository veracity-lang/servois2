(* SVG heap diagram for commutativity counterexamples.
 *
 * Shows the heap structure at up to three points in a failing commutation:
 *   Init  |  After M1  |  After M1;M2
 *
 * Each panel shows:
 *  - Named pointer variables (globals + thread-local snapshots) with arrows
 *    into the allocated heap cells
 *  - Heap cells as boxes with val/next fields; next-pointer arrows between cells
 *
 * No external dependencies: SVG is produced as a plain OCaml string.
 *
 * Entry point: [render] returns the SVG string.
 *)

open Smt

(* ------------------------------------------------------------------ *)
(* Layout constants                                                    *)
(* ------------------------------------------------------------------ *)

let pad        = 16   (* outer top/left/right/bottom padding *)
let title_h    = 28   (* height reserved for state title bar *)
let ptr_h      = 22   (* height per pointer-label row *)
let ptr_col_w  = 100  (* width of the pointer-labels column within a panel *)
let cell_left  = 150  (* X offset from panel origin to cell-box left edge *)
let cell_w     = 148  (* cell box width *)
let cell_h     = 54   (* cell box height (two halves of 27) *)
let cell_hh    = 27   (* half cell height *)
let cell_gap   = 10   (* vertical gap between cell boxes *)
let panel_w    = cell_left + cell_w + 28  (* total panel width *)
let panel_gap  = 26   (* horizontal gap between adjacent panels *)

(* ------------------------------------------------------------------ *)
(* Model extraction helpers                                            *)
(* ------------------------------------------------------------------ *)

let int_of_exp = function
  | EConst (CInt n)             -> Some n
  | EUop (Neg, EConst (CInt n)) -> Some (-n)
  | _                           -> None

let find model key =
  Option.bind (List.assoc_opt key model) int_of_exp

(* ------------------------------------------------------------------ *)
(* Heap state                                                          *)
(* ------------------------------------------------------------------ *)

type heap_cell = {
  value : int;
  next  : int;   (* -1 = null *)
}

type named_ptr = {
  label : string;
  cell  : int;   (* index into [cells]; -1 = null *)
}

type named_val = {
  val_label : string;
  val_int   : int;
}

type heap_state = {
  title    : string;
  alloc    : int;
  cells    : heap_cell array;
  ptrs     : named_ptr list;
  int_vars : named_val list;
}

(* Build heap_state from model values at the given state suffix.
   [local_arr_names]  — TLoc arrays shown as pointer arrows.
   [int_arr_names]    — int arrays shown as plain values.
   [global_int_names] — plain scalar integer globals shown as plain values. *)
let parse_state ?(global_int_names=[]) model sfx title global_names local_arr_names int_arr_names thread_var =
  let key_var name = EVar (Var (name ^ sfx)) in
  let key_sel arr idx_exp =
    EFunc ("select", [EVar (Var (arr ^ sfx)); idx_exp]) in

  let alloc =
    find model (key_var "heap_alloc") |> Option.value ~default:0 in
  let alloc = max 0 (min alloc 32) in

  let cells = Array.init alloc (fun i ->
    let ci = EConst (CInt i) in
    let value = find model (key_sel "heap_value" ci) |> Option.value ~default:0 in
    let next  = find model (key_sel "heap_next"  ci) |> Option.value ~default:(-1) in
    { value; next })
  in

  let global_ptrs = List.filter_map (fun name ->
    find model (key_var name)
    |> Option.map (fun c -> { label = name; cell = c }))
    global_names
  in

  let thread_idx_exp = key_var thread_var in
  let local_ptrs = List.filter_map (fun arr ->
    find model (key_sel arr thread_idx_exp)
    |> Option.map (fun c ->
        { label = Printf.sprintf "%s[%s]" arr thread_var; cell = c }))
    local_arr_names
  in

  let int_var_list = List.filter_map (fun arr ->
    find model (key_sel arr thread_idx_exp)
    |> Option.map (fun v ->
        { val_label = Printf.sprintf "%s[%s]" arr thread_var; val_int = v }))
    int_arr_names
  in

  let scalar_int_vars = List.filter_map (fun name ->
    find model (key_var name)
    |> Option.map (fun v -> { val_label = name; val_int = v }))
    global_int_names
  in

  (* For every TLoc pointer we display, also show its ->next field as a
     pointer row immediately below it. The value comes from the already-
     extracted cells array, so no extra SMT queries are needed. *)
  let ptr_with_next p =
    let nxt_row =
      if p.cell >= 0 && p.cell < Array.length cells then
        [ { label = p.label ^ "->next"; cell = cells.(p.cell).next } ]
      else []
    in
    p :: nxt_row
  in
  let all_ptrs = List.concat_map ptr_with_next (global_ptrs @ local_ptrs) in

  { title; alloc; cells; ptrs = all_ptrs; int_vars = scalar_int_vars @ int_var_list }

(* ------------------------------------------------------------------ *)
(* SVG helpers                                                         *)
(* ------------------------------------------------------------------ *)

let sp = Printf.sprintf

(* Escape XML special characters. *)
let xe s =
  let b = Buffer.create (String.length s + 4) in
  String.iter (function
    | '<' -> Buffer.add_string b "&lt;"
    | '>' -> Buffer.add_string b "&gt;"
    | '&' -> Buffer.add_string b "&amp;"
    | '"' -> Buffer.add_string b "&quot;"
    | c   -> Buffer.add_char b c) s;
  Buffer.contents b

let svg_rect ?(rx=4) ?(fill="#fff") ?(stroke="#555") ?(sw=1) x y w h =
  sp {|<rect x="%d" y="%d" width="%d" height="%d" rx="%d" fill="%s" stroke="%s" stroke-width="%d"/>|}
    x y w h rx fill stroke sw

let svg_line ?(stroke="#777") ?(sw=1) x1 y1 x2 y2 =
  sp {|<line x1="%d" y1="%d" x2="%d" y2="%d" stroke="%s" stroke-width="%d"/>|}
    x1 y1 x2 y2 stroke sw

(* Text anchored at (x,y); anchor = "start" | "middle" | "end". *)
let svg_text ?(anchor="start") ?(fill="#ddd") ?(fw="normal") ?(fs=11) x y txt =
  sp {|<text x="%d" y="%d" text-anchor="%s" fill="%s" font-weight="%s" font-size="%d">%s</text>|}
    x y anchor fill fw fs (xe txt)

(* Cubic bezier path with arrowhead marker. *)
let svg_bezier ?(stroke="#888") x1 y1 cx1 cy1 cx2 cy2 x2 y2 =
  sp {|<path d="M %d %d C %d %d %d %d %d %d" stroke="%s" stroke-width="1.5" fill="none" marker-end="url(#arr)"/>|}
    x1 y1 cx1 cy1 cx2 cy2 x2 y2 stroke

(* Straight line with arrowhead. *)
let svg_arrow_line ?(stroke="#888") x1 y1 x2 y2 =
  sp {|<line x1="%d" y1="%d" x2="%d" y2="%d" stroke="%s" stroke-width="1.5" marker-end="url(#arr)"/>|}
    x1 y1 x2 y2 stroke

(* Null pointer: short stub ending with ⊥ tick marks. *)
let svg_null x y =
  let xend = x + 18 in
  String.concat "\n"
    [ svg_line ~stroke:"#da4343" x y xend y
    ; svg_line ~stroke:"#da4343" xend (y-5) xend (y+5)
    ; svg_line ~stroke:"#da4343" (xend+4) (y-3) (xend+4) (y+3)
    ]

(* ------------------------------------------------------------------ *)
(* Per-panel SVG generation                                            *)
(* ------------------------------------------------------------------ *)

(* Total label rows = pointer rows + int-value rows. *)
let n_label_rows st = List.length st.ptrs + List.length st.int_vars

(* Compute where cell [i] begins vertically, relative to panel origin.
   Cells are laid out starting at the same Y as the first pointer-label row. *)
let cell_top i =
  pad + title_h + 8 + i * (cell_h + cell_gap)

(* Render one panel (state) at origin (0,0); caller wraps in <g translate>. *)
let render_panel st max_alloc =
  let n_rows   = n_label_rows st in
  let buf      = Buffer.create 2048 in
  let put s    = Buffer.add_string buf s; Buffer.add_char buf '\n' in

  (* ---- Title ---- *)
  put (svg_rect ~rx:0 ~fill:"#2a3a4a" ~stroke:"none" ~sw:0
         0 0 panel_w (pad + title_h));
  put (svg_text ~anchor:"middle" ~fill:"#7ec8e3" ~fw:"bold" ~fs:12
         (panel_w/2) (pad + title_h/2 + 4) st.title);

  (* ---- Background for body ---- *)
  let body_top = pad + title_h in
  let body_h   = 8
                 + max (n_rows * ptr_h) (max_alloc * (cell_h + cell_gap))
                 + pad in
  put (svg_rect ~rx:0 ~fill:"#1e2d3d" ~stroke:"none" ~sw:0
         0 body_top panel_w body_h);

  (* ---- Pointer label rows (TLoc arrays: drawn as arrows) ---- *)
  let n_ptrs = List.length st.ptrs in
  List.iteri (fun k p ->
    let ly = pad + title_h + 6 + k * ptr_h + ptr_h / 2 + 4 in
    put (svg_text ~fill:"#b5d0e8" ~fs:10 6 ly (p.label ^ ":"));
    if p.cell >= 0 && p.cell < st.alloc then begin
      let cy = cell_top p.cell + cell_hh in
      let bx = ptr_col_w - 6 in
      put (svg_bezier ~stroke:"#6ab" bx ly (bx+12) ly (cell_left-10) cy cell_left cy)
    end else
      put (svg_null (ptr_col_w - 2) ly)
  ) st.ptrs;

  (* ---- Integer value rows (int arrays: shown as plain values) ---- *)
  List.iteri (fun k iv ->
    let row = n_ptrs + k in
    let ly  = pad + title_h + 6 + row * ptr_h + ptr_h / 2 + 4 in
    put (svg_text ~fill:"#c8b8e8" ~fs:10 6 ly (iv.val_label ^ ":"));
    let txt = if iv.val_int = -1 then "null" else string_of_int iv.val_int in
    put (svg_text ~fill:"#e8d8a8" ~fw:"bold" ~fs:10 (ptr_col_w + 4) ly txt)
  ) st.int_vars;

  (* ---- Cell boxes ---- *)
  for i = 0 to max_alloc - 1 do
    let cy   = cell_top i in
    let live = i < st.alloc in
    let fill = if live then "#283848" else "#1a2530" in
    let sc   = if live then "#4a6a7a" else "#2a3a4a" in
    put (svg_rect ~rx:3 ~fill ~stroke:sc ~sw:1 cell_left cy cell_w cell_h);
    (* Divider *)
    if live then
      put (svg_line ~stroke:"#3a5060" cell_left (cy + cell_hh)
             (cell_left + cell_w) (cy + cell_hh));
    if live then begin
      (* Top half: cell index + value *)
      put (svg_text ~fill:"#aaa" ~fs:9 (cell_left + 3) (cy + 10)
             (sp "cell %d" i));
      put (svg_text ~fill:"#e8d8a8" ~fw:"bold" ~fs:11
             (cell_left + 50) (cy + cell_hh - 6)
             (sp "val = %d" st.cells.(i).value));
      (* Bottom half: next pointer *)
      let next_y = cy + cell_hh + 18 in
      put (svg_text ~fill:"#aaa" ~fs:10 (cell_left + 4) next_y "next:");
      let nx = st.cells.(i).next in
      if nx < 0 then
        (* null *)
        put (svg_null (cell_left + 42) next_y)
      else begin
        (* Arrow exiting right side, curving to target cell left *)
        let sx  = cell_left + cell_w in
        let sy  = cy + cell_h * 3 / 4 in
        let j   = nx in   (* target cell index *)
        if j < max_alloc then begin
          let ty = cell_top j + cell_hh in
          let cx = sx + 30 in
          put (svg_bezier ~stroke:"#6ab" sx sy cx sy cx ty cell_left ty)
        end else begin
          (* target outside visible range — draw as a dangling arrow right *)
          put (svg_arrow_line ~stroke:"#c66" sx sy (sx + 28) sy)
        end
      end
    end else begin
      put (svg_text ~fill:"#3a5060" ~fs:10
             (cell_left + cell_w/2) (cy + cell_h/2 + 4)
             "—")
    end
  done;

  (* ---- Right border ---- *)
  let total_h = pad + title_h + body_h in
  put (svg_line ~stroke:"#2a3a4a" ~sw:2 panel_w 0 panel_w total_h);

  Buffer.contents buf

(* ------------------------------------------------------------------ *)
(* Top-level render                                                    *)
(* ------------------------------------------------------------------ *)

(** [render ~suffixes ~titles ~global_names ~local_arr_names ~int_arr_names ~global_int_names ~thread_var model]
    returns an SVG string showing the heap diagram for each state in [suffixes].
    [local_arr_names]  — TLoc arrays shown as pointer arrows.
    [int_arr_names]    — int arrays shown as plain values.
    [global_int_names] — plain scalar integer globals shown as plain values. *)
let render ~suffixes ~titles ~global_names ~local_arr_names ?(int_arr_names=[]) ?(global_int_names=[]) ~thread_var model =
  let states = List.map2 (fun sfx title ->
    parse_state ~global_int_names model sfx title global_names local_arr_names int_arr_names thread_var
  ) suffixes titles in

  let n_panels  = List.length states in
  let max_rows  = List.fold_left (fun acc st -> max acc (n_label_rows st)) 0 states in
  let max_alloc = List.fold_left (fun acc st -> max acc st.alloc) 0 states in
  let max_alloc = max max_alloc 1 in  (* always show at least one cell row *)

  let total_w = pad + n_panels * panel_w + (n_panels - 1) * panel_gap + pad in
  let total_h = pad + title_h + 8
                + max (max_rows * ptr_h) (max_alloc * (cell_h + cell_gap)) + pad in

  let buf = Buffer.create 8192 in
  let put s = Buffer.add_string buf s; Buffer.add_char buf '\n' in

  put (sp {|<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 %d %d" width="100%%"|}
         total_w total_h);
  put {|  style="font-family: 'Courier New', Courier, monospace; background:#162030;">|};

  (* Arrow marker definition *)
  put {|<defs>|};
  put {|  <marker id="arr" markerWidth="7" markerHeight="5" refX="7" refY="2.5" orient="auto">|};
  put {|    <polygon points="0 0, 7 2.5, 0 5" fill="#6ab"/>|};
  put {|  </marker>|};
  put {|</defs>|};

  (* Background *)
  put (svg_rect ~rx:0 ~fill:"#162030" ~stroke:"none" 0 0 total_w total_h);

  (* Panels *)
  List.iteri (fun col st ->
    let px = pad + col * (panel_w + panel_gap) in
    put (sp {|<g transform="translate(%d, %d)">|} px pad);
    put (render_panel st max_alloc);
    put {|</g>|};
  ) states;

  (* Column separators *)
  for col = 1 to n_panels - 1 do
    let sx = pad + col * (panel_w + panel_gap) - panel_gap / 2 in
    put (svg_line ~stroke:"#0d1820" ~sw:panel_gap sx 0 sx total_h)
  done;

  put {|</svg>|};
  Buffer.contents buf

(** Write the SVG to [path]. Does nothing if model is empty.
    [local_arr_names]  — TLoc arrays shown as arrows.
    [int_arr_names]    — int arrays shown as plain values (default []).
    [global_int_names] — plain scalar integer globals shown as plain values (default []). *)
let write_svg path ~suffixes ~titles ~global_names ~local_arr_names ?(int_arr_names=[]) ?(global_int_names=[]) ~thread_var model =
  if model = [] then ()
  else begin
    let svg = render ~suffixes ~titles ~global_names ~local_arr_names ~int_arr_names ~global_int_names ~thread_var model in
    let oc = open_out path in
    output_string oc svg;
    close_out oc
  end

(* ------------------------------------------------------------------ *)
(* HTML variable table                                                 *)
(* ------------------------------------------------------------------ *)

(** [render_table_html] returns an HTML <table> fragment showing all state
    variables in three columns: Init (""), After M1 ("1"), After M1;M2 ("12").
    Variable names are in the first column; values come from [model].
    Uses the same lookup key construction as [parse_state]. *)
let render_table_html ~suffixes ~titles ~global_names ~local_arr_names ?(int_arr_names=[]) ?(global_int_names=[]) ~thread_var model =
  let val_str v = if v = -1 then "null" else string_of_int v in
  let look key = Option.fold ~none:"—" ~some:val_str (find model key) in

  let per_sfx sfx =
    let kv name = EVar (Var (name ^ sfx)) in
    let tidx    = kv thread_var in
    let ks arr  = EFunc ("select", [EVar (Var (arr ^ sfx)); tidx]) in
    (kv, ks)
  in
  let sfx_fns = List.map per_sfx suffixes in

  (* rows: (display_name, [val_at_sfx0; ...]) *)
  let rows =
    List.map (fun n ->
      (n, List.map (fun (kv, _) -> look (kv n)) sfx_fns))
      global_names
    @ (let vs = List.map (fun (kv, _) -> look (kv "heap_alloc")) sfx_fns in
       if List.for_all (( = ) "—") vs then [] else [("heap_alloc", vs)])
    @ List.map (fun n ->
        (n, List.map (fun (kv, _) -> look (kv n)) sfx_fns))
        global_int_names
    @ List.map (fun arr ->
        let lbl = Printf.sprintf "%s[%s]" arr thread_var in
        (lbl, List.map (fun (_, ks) -> look (ks arr)) sfx_fns))
        local_arr_names
    @ List.map (fun arr ->
        let lbl = Printf.sprintf "%s[%s]" arr thread_var in
        (lbl, List.map (fun (_, ks) -> look (ks arr)) sfx_fns))
        int_arr_names
  in
  let rows = List.filter (fun (_, vs) -> not (List.for_all (( = ) "—") vs)) rows in

  if rows = [] then ""
  else begin
    let buf = Buffer.create 2048 in
    let put = Buffer.add_string buf in
    put {|<table style="border-collapse:collapse;font-family:'Courier New',Courier,monospace;|};
    put {|font-size:12px;margin-top:10px;width:100%">|};
    put "\n";
    (* header row *)
    put {|<tr style="background:#1e3a50">|};
    put {|<th style="padding:5px 10px;text-align:left;color:#7ec8e3;border:1px solid #2a4a60">Variable</th>|};
    List.iter (fun title ->
      put (sp {|<th style="padding:5px 10px;text-align:right;color:#7ec8e3;border:1px solid #2a4a60">%s</th>|}
               (xe title))
    ) titles;
    put "</tr>\n";
    (* data rows *)
    List.iteri (fun ri (name, vs) ->
      let bg = if ri mod 2 = 0 then "#162030" else "#1a2a3a" in
      put (sp {|<tr style="background:%s">|} bg);
      put (sp {|<td style="padding:4px 10px;color:#b5d0e8;border:1px solid #2a4a60">%s</td>|}
               (xe name));
      List.iter (fun v ->
        let color = if v = "null" then "#da8080"
                    else if v = "—"   then "#555"
                    else "#e8d8a8" in
        put (sp {|<td style="padding:4px 10px;text-align:right;color:%s;border:1px solid #2a4a60">%s</td>|}
                 color (xe v))
      ) vs;
      put "</tr>\n"
    ) rows;
    put "</table>\n";
    Buffer.contents buf
  end

(** Write the HTML variable table to [path].
    Name the file "heap_table.html" so it sorts after "heap_diagram.svg"
    and is displayed below the SVG in the panel. *)
let write_table path ~suffixes ~titles ~global_names ~local_arr_names ?(int_arr_names=[]) ?(global_int_names=[]) ~thread_var model =
  if model = [] then ()
  else begin
    let tbl = render_table_html ~suffixes ~titles ~global_names ~local_arr_names
                ~int_arr_names ~global_int_names ~thread_var model in
    if tbl = "" then ()
    else begin
      let oc = open_out path in
      output_string oc tbl;
      close_out oc
    end
  end
