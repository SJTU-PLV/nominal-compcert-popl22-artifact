(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Parse dependencies generated by ocamldep and produce a linking order *)

open Printf

type status = Todo | Inprogress | Done

type node = {
  deps: string list;
  result: string;
  mutable status: status
}

(* Parsing *)

let re_continuation_line = Str.regexp "\\(.*\\)\\\\[ \t]*$"

let re_depend_line = Str.regexp "\\([^:]*\\):\\(.*\\)$"

let re_whitespace = Str.regexp "[ \t\n]+"

let parse_dependencies depfile =
  let deps = (Hashtbl.create 63 : (string, node) Hashtbl.t) in
  let ic = open_in depfile in

  let rec read_line () =
    let l = input_line ic in
    if Str.string_match re_continuation_line l 0 then begin
      let l' = Str.matched_group 1 l in
      l' ^ read_line ()
    end else
      l in

  let enter_line l =
    if not (Str.string_match re_depend_line l 0) then begin
      eprintf "Warning: ill-formed dependency line '%s'\n" l
    end else begin
      let lhs = Str.matched_group 1 l
      and rhs = Str.matched_group 2 l in
      let lhs = Str.split re_whitespace lhs
      and rhs = Str.split re_whitespace rhs in
      List.iter (fun lhs -> let node = {
          deps = rhs;
          result = lhs;
          status = Todo
        } in
          Hashtbl.add deps lhs node) lhs
    end in

  begin try
    while true do enter_line (read_line ()) done
  with End_of_file ->
    ()
  end;
  close_in ic;
  deps

(* Suffix of a file name *)

let re_suffix = Str.regexp "\\.[a-zA-Z]+$"

let filename_suffix s =
  try
    ignore (Str.search_forward re_suffix s 0); Str.matched_string s
  with Not_found ->
    ""

(* Topological sorting *)

let emit_dependencies deps targets =

  let rec dsort target suff =
    match Hashtbl.find_opt deps target with
    | None -> ()
    | Some node ->
        match node.status with
        | Done -> ()
        | Inprogress ->
            eprintf "Warning: cyclic dependency on '%s', ignored\n" target
        | Todo ->
            node.status <- Inprogress;
            List.iter
              (fun dep ->
                  if Filename.check_suffix dep suff then dsort dep suff)
              node.deps;
            printf "%s " target;
            node.status <- Done
  in
    Array.iter (fun t -> dsort t (filename_suffix t)) targets

let _ =
  if Array.length Sys.argv < 3 then begin
    eprintf "Usage: modorder <dependency file> <target>...\n";
    exit 2
  end;
  emit_dependencies
    (parse_dependencies Sys.argv.(1))
    (Array.sub Sys.argv 2 (Array.length Sys.argv - 2));
  print_newline()
