open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;

(*The interactive loop and the file demand different line-merging methods to produce the same expression*)
let rec join_lines line acc= 
if line="" then
  join_lines (read_line ()) acc
else
  match String.get line ((String.length line)-1) with
    |';'-> String.concat " " (acc::[line])
    |_ -> join_lines (read_line ()) (String.concat " " (acc::[line]));;

let join_file_lines channel = 
let rec aux acc= try
  let l= input_line channel in 
    aux (l::acc)
  with End_of_file->String.concat "" (List.rev acc)
in
aux [];;

(*The find function returns the index of a given token within a list*)
let find token l =
  let rec aux str l acc = match l with
      | a::b -> if (a=str) then acc else aux str b (acc+1)
      | [] -> raise (Not_found)
      in
        try aux token l 0
        with Not_found->(-1)
;;

let remove_last list=
  let rec aux l acc= match l with
  |a::[]-> List.rev acc
  |a::b-> aux b (a::acc)
in aux list [];;

let process_expression expression ctx nctx debug=
    try
      let inst = s token (from_string expression) (*parsing of the expression into an instruction*)
      in execute_instruction ctx nctx debug inst  (*this returns the variable context*)
    with
       Lexical_error ->
         print_endline "lexical error"; nctx
     | Parse_error ->
         print_endline "syntax error"; nctx
     | Type_error e ->
         print_endline ("type error: " ^ e); nctx
     | End_of_file ->
         print_endline "...bye!!!"; nctx;;



let rec eval_expressions acc ctx nctx debug=
  match acc with
    |a::[]-> 
      process_expression a ctx nctx debug
    |a::b -> 
      (*the variable context is maintained across the different evaluations to keep track of assigned variables*)
      eval_expressions b ctx (process_expression a ctx nctx debug) debug

(*interactive loop*)
let top_level_loop debug =
  let rec loop ctx nctx =
    print_string ">> ";
    flush stdout;
    let newnctx=eval_expressions (remove_last(String.split_on_char ';' (join_lines (read_line ()) ""))) ctx nctx debug 
    in loop ctx newnctx
  in
    print_endline "Evaluator of lambda expressions...";
    loop emptyctx emptynctx
  ;;

(*the debug and file flags are checked at the start of the program*)
let debug=find "-d" (Array.to_list Sys.argv) in
  if debug=(-1) then
    let fileidx=find "-f" (Array.to_list Sys.argv) in
      if fileidx=(-1) then top_level_loop false
      else
          (let channel=open_in Sys.argv.(fileidx+1)
          (*file expression set processing*)
          in eval_expressions (remove_last(String.split_on_char ';' (join_file_lines channel))) emptyctx emptynctx false)
  else
    let fileidx=find "-f" (Array.to_list Sys.argv) in
      if fileidx=(-1) then top_level_loop true
      else
          (let channel=open_in Sys.argv.(fileidx+1)
          (*file expression set processing*)
          in eval_expressions (remove_last(String.split_on_char ';' (join_file_lines channel))) emptyctx emptynctx true)