(*

Copyright (c) 2012 Radek Micek

Permission is hereby granted, free of charge, to any person
obtaining a copy of this software and associated documentation
files (the "Software"), to deal in the Software without
restriction, including without limitation the rights to use,
copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.

*)

open BatPervasives

(* ************************************** *)
(* Additional functions for arrays        *)

let array_swap arr i j =
  if i <> j then begin
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  end

let array_rfindi pred arr =
  let rec loop i =
    if i >= 0 then
      if pred arr.(i) then i else loop (i-1)
    else
      raise Not_found
  in

  loop (Array.length arr - 1)

let array_uniq arr =
  let h = Hashtbl.create (Array.length arr / 2 + 1) in
  let not_seen lit =
    if Hashtbl.mem h lit then
      false
    else begin
      Hashtbl.add h lit ();
      true
    end in
  BatArray.filter not_seen arr

let dyn_array_findi pred arr =
  let rec loop i =
    if i < BatDynArray.length arr then
      if pred (BatDynArray.get arr i) then
        i
      else
        loop (i+1)
    else
      raise Not_found
  in

  loop 0

let dyn_array_enum_rev arr =
  let n = BatDynArray.length arr in
  BatEnum.init n (fun i -> BatDynArray.get arr (n-i-1))

(* ************************************** *)
(* Sat solver                             *)

type var = int

(* true - positive, false - negative.  *)
type sign = bool

type lit = Lit of sign * var

(* Literals will be reordered, first 2 literals are watched. *)
type clause = {
  lits : lit array;
  resolution_proof : (clause * clause) option;
}

type xbool =
  | XTrue
  | XFalse
  | XUndef

type reason =
  | Decided
  | Implied of clause

type problem = {
  clauses : clause BatDynArray.t;

  (* Indexed by variables *)
  assignment : xbool BatDynArray.t;
  decision_levels : int BatDynArray.t;

  trace : (var * reason) BatDynArray.t;
  mutable dlevel : int;
}

let lit_var (Lit(_, var)) = var

let lit_ass (prob : problem) (Lit(sign, var)) =
  match sign, BatDynArray.get prob.assignment var with
    | true, XTrue | false, XFalse -> XTrue
    | true, XFalse | false, XTrue -> XFalse
    | _, XUndef -> XUndef

let bool_to_xbool = function
  | true -> XTrue
  | false -> XFalse

let satisfy_lit prob (Lit(sign, var)) cl =
  BatDynArray.set prob.assignment var (bool_to_xbool sign);
  BatDynArray.set prob.decision_levels var prob.dlevel;
  BatDynArray.add prob.trace (var, Implied cl)

exception Propagation
exception Conflict of clause

(* Full unit propagation. Returns conflict clause if any. *)
let propagate prob =
  let ass = lit_ass prob in

  let is_true_lit lit = ass lit = XTrue in
  let is_undef_lit lit = ass lit = XUndef in

  let update_watched_lits lits =
    try
      let i = BatArray.findi is_true_lit lits in
      array_swap lits 0 i
    with
      | Not_found ->
          try
            let i = BatArray.findi is_undef_lit lits in
            array_swap lits 0 i;
            let j = array_rfindi is_undef_lit lits in
            array_swap lits 1 j
          with
            | Not_found -> ()
  in

  let prop cl =
    match cl.lits with
      | [| |] -> raise (Conflict cl)
      | [| x |] ->
          begin match ass x with
            | XTrue -> ()
            | XFalse -> raise (Conflict cl)
            | XUndef ->
                satisfy_lit prob x cl;
                raise Propagation
          end
      | _ ->
          update_watched_lits cl.lits;

          begin match ass cl.lits.(0), ass cl.lits.(1) with
            | XTrue, _ | _, XTrue | XUndef, XUndef -> ()
            | XFalse, XFalse -> raise (Conflict cl)
            | XUndef, XFalse ->
                satisfy_lit prob cl.lits.(0) cl;
                raise Propagation
            | XFalse, XUndef ->
                satisfy_lit prob cl.lits.(1) cl;
                raise Propagation
          end
  in

  let rec loop () =
    try
      BatDynArray.iter prop prob.clauses;
      None
    with
      | Propagation -> loop ()
      | Conflict cl -> Some cl
  in

  loop ()

(* Resolution on x. *)
let resolve a b x =
  let lits =
    Array.append a.lits b.lits
    |> array_uniq
    |> BatArray.filter (fun (Lit(_, var)) -> var <> x)
  in

  { lits; resolution_proof = Some(a, b) }

let resolve_until pred prob conflict =
  let trace = dyn_array_enum_rev prob.trace in

  let rec loop cl =
    if pred prob cl then
      cl
    else begin
      let rec pop_trace_until_var_in_clause () =
        let var, reason = trace |> BatEnum.get |> BatOption.get in

        if cl.lits |> BatArray.exists (fun lit -> lit_var lit = var) then
          var, reason
        else
          pop_trace_until_var_in_clause ()
      in

      let var, reason = pop_trace_until_var_in_clause () in
      match reason with
        | Implied ante -> loop (resolve cl ante var)
        | Decided -> failwith "UIP not found"
    end
  in

  loop conflict


let is_uip prob cl =

  let dlevel = prob.dlevel in
  let lits = cl.lits in

  (* Returns false if the number of literals from current decision level
     is 2 or more. *)
  let rec count_cur_level i cnt =
    if i < Array.length lits then
      if BatDynArray.get prob.decision_levels (lit_var lits.(i)) = dlevel then
        cnt < 1 && count_cur_level (i+1) (cnt+1)
      else
        count_cur_level (i+1) cnt
    else
      true
  in

  count_cur_level 0 0

(* Computes first UIP by resolution. *)
let compute_uip = resolve_until is_uip

let backtrack prob level =
  let rec loop () =
    if BatDynArray.empty prob.trace ||
      (prob.trace
       |> BatDynArray.last
       |> fst
       |> BatDynArray.get prob.decision_levels = level)
    then
      prob.dlevel <- level
    else begin
      let var = prob.trace |> BatDynArray.last |> fst in
      BatDynArray.delete_last prob.trace;
      BatDynArray.set prob.assignment var XUndef;
      BatDynArray.set prob.decision_levels var ~-1;
      loop ()
    end in

  loop ()

(* First undecided variable is assigned 0. *)
let decide prob =
  try
    let var =  prob.assignment |> dyn_array_findi (fun a -> a = XUndef) in
    prob.dlevel <- prob.dlevel + 1;
    BatDynArray.add prob.trace (var, Decided);
    BatDynArray.set prob.assignment var XFalse;
    BatDynArray.set prob.decision_levels var prob.dlevel
  with
    | Not_found -> failwith "No unassigned variable."

let watched_literals_sat prob cl =
  match cl.lits with
    | [| |] -> false
    | [| x |] -> lit_ass prob x = XTrue
    | _ ->
        match lit_ass prob cl.lits.(0), lit_ass prob cl.lits.(1) with
          | XTrue, _ | _, XTrue -> true
          | _, _ -> false

type result =
  (* Found satisfying assignment. *)
  | Sat
  (* Derived empty clause at decision level 0. *)
  | Empty of clause
  | Unknown

let rec do_propagation prob =
  match propagate prob with
    | Some conflict ->
        let learned_cl = compute_uip prob conflict in
        BatDynArray.add prob.clauses learned_cl;

        if prob.dlevel = 0 then begin
          (* If the clause is not empty, we have to resolve out all literals. *)
          let cl = resolve_until (fun _ cl -> Array.length cl.lits = 0) prob learned_cl in
          Empty cl
        end else begin
          assert (Array.length learned_cl.lits > 0);

          let nlevel =
            learned_cl.lits
            |> BatArray.enum
            |> BatEnum.map (fun lit -> BatDynArray.get prob.decision_levels (lit_var lit))
            |> BatEnum.filter (fun dl -> dl < prob.dlevel)
            |> BatEnum.fold max 0
          in

          backtrack prob nlevel;
          do_propagation prob
        end

    | None ->
        (* Check if satisfied - we can use watched literals. *)
        if prob.clauses
           |> BatDynArray.enum
           |> BatEnum.for_all (watched_literals_sat prob)
        then
          Sat
        else
          Unknown

(* Returns empty clause with proof by resolution.  *)
let rec solve prob =
  let rec loop () =
    match do_propagation prob with
      | Unknown ->
          decide prob;
          loop ()
      | Sat-> None
      | Empty cl -> Some cl
  in

  loop ()

let new_problem () = {
  clauses = BatDynArray.create ();
  assignment = BatDynArray.create ();
  decision_levels = BatDynArray.create ();
  trace = BatDynArray.create ();
  dlevel = 0
}

let new_var prob =
  let var = BatDynArray.length prob.assignment in
  BatDynArray.add prob.assignment XUndef;
  BatDynArray.add prob.decision_levels ~-1;
  var

(* ************************************** *)
(* Sample problems                        *)

let simple_problem () =
  let prob = new_problem () in
  let nvars = 6 in
  let vars = Array.init nvars (fun _ -> new_var prob) in
  let x = Array.init nvars (fun i -> Lit(true, vars.(i))) in
  let x' = Array.init nvars (fun i -> Lit(false, vars.(i))) in

  let clauses = [
    [| x.(4); x'.(0); x.(2) |];
    [| x'.(2); x.(3) |];
    [| x'.(4); x.(0) |];
    [| x.(5); x.(0) |];
    [| x'.(0); x.(1) |];
    [| x'.(2); x'.(3) |];
    [| x'.(4); x'.(5) |];
    [| x.(2); x'.(3) |];
    [| x.(2); x.(4) |];
  ] in

  List.iter (fun lits -> BatDynArray.add prob.clauses { lits; resolution_proof = None }) clauses;

  prob

let php_problem npigeons nholes =
  let prob = new_problem () in
  let v = Array.init npigeons (fun _ -> Array.init nholes (fun _ -> new_var prob)) in

  (* No pigeon is in two holes at once. *)
  for p = 0 to npigeons-1 do
    for h = 0 to nholes-1 do
      for h2 = h+1 to nholes-1 do
        let lits = [| Lit(false, v.(p).(h)); Lit(false, v.(p).(h2)) |] in
        BatDynArray.add prob.clauses { lits; resolution_proof = None }
      done
    done
  done;

  (* Every pigeon is in one hole. *)
  for p = 0 to npigeons-1 do
    let lits = Array.init nholes (fun h -> Lit(true, v.(p).(h))) in
    BatDynArray.add prob.clauses { lits; resolution_proof = None }
  done;

  (* No two pigeons are in the same hole. *)
  for p = 0 to npigeons-1 do
    for p2 = p+1 to npigeons-1 do
      for h = 0 to nholes-1 do
        let lits = [| Lit(false, v.(p).(h)); Lit(false, v.(p2).(h)) |] in
        BatDynArray.add prob.clauses { lits; resolution_proof = None }
      done
    done
  done;

  prob

let selected_problem = simple_problem

let _ =
  let prob = selected_problem () in
  match solve prob with
    | None -> print_string "sat\n"
    | Some _ -> print_string "unsat\n"
