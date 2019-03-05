module Cmd

open ExprTypes
open System

let progs : (string * string * bool * (int -> int * GExpr)) list ref = ref []
let cmds  : (string * string * (int * GExpr -> unit)) list ref       = ref []

let registerProg name descr param f = 
  progs := !progs @ [(name, descr, param, f)]

let registerCmd name descr f = 
  cmds  := !cmds @ [(name, descr, f)]

let printProgs () =
  let f (name, descr, param, f) = 
    if param then printf "%s" ("  " + name + " n -- " + descr + "\n")
    else          printf "%s" ("  " + name + " -- " + descr + "\n")
  printf "Available programs: \n"
  List.iter f !progs
  printf "\n"

let printCmds () =
  let f (name, descr, f) =
    printf "%s" ("  " ^ name ^ " -- " ^ descr + "\n")
  printf "Commands: \n"
  List.iter f !cmds
  printf "\n"

let printHelp () = 
  printProgs ()
  printCmds ()

let isCmd x = List.exists (fun (s, _, _) -> s = x) !cmds

let parseCmd x =
  let (name, descr, f) = List.find (fun (s, _, _) -> s = x) !cmds
  f

let parseParam (xs : string list) = match xs with
  | [] -> None
  | x::xs -> 
      let mutable n = 0
      if Int32.TryParse(x, &n) then Some n
      else None

let parseProg xs = match xs with
  | [] -> None
  | x::xs -> begin
      if List.exists (fun (s, _, _, _) -> s = x) !progs then
        let (name, descr, param, f) = List.find (fun (s, _, _, _) -> s = x) !progs
        if param then
          match parseParam xs with
            | None -> None
            | Some n -> Some (f n)
        else
          Some (f 0)
      else
        printf "Specify a program\n"
        None
    end

let parseLine (s:string) =
  match Array.toList (s.Split([|' '|])) with
    | [] | ("help")::_ | ("-h")::_ | ("--help")::_ -> printHelp ()
    | x::xs -> 
        if (isCmd x) then
          let cmd = parseCmd x
          match parseProg xs with
            | None -> printHelp ()
            | Some p -> cmd p
        else
          let cmd = parseCmd "compile"
          match parseProg (x::xs) with
            | None -> printHelp ()
            | Some p -> cmd p
