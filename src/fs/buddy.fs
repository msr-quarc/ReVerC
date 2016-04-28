module Buddy

open System
open System.Runtime.InteropServices
open Microsoft.FSharp.NativeInterop

type BDD = int

//let path = @"/home/meamy/Programming/ReVer/bdd"

// Imports
[<DllImport(@"bdd", EntryPoint="bdd_init")>]
extern int bdd_init(int,int);

[<DllImport(@"bdd", EntryPoint="bdd_true")>]
extern BDD bdd_true();

[<DllImport(@"bdd", EntryPoint="bdd_false")>]
extern BDD bdd_false();

[<DllImport(@"bdd", EntryPoint="bdd_ithvar")>]
extern BDD bdd_ithvar(int);

[<DllImport(@"bdd", EntryPoint="bdd_nithvar")>]
extern BDD bdd_nithvar(int);

[<DllImport(@"bdd", EntryPoint="bdd_var")>]
extern int bdd_var(BDD);

[<DllImport(@"bdd", EntryPoint="bdd_low")>]
extern BDD bdd_low(BDD);

[<DllImport(@"bdd", EntryPoint="bdd_high")>]
extern BDD bdd_high(BDD);

[<DllImport(@"bdd", EntryPoint="bdd_printall")>]
extern void bdd_printall();

[<DllImport(@"bdd", EntryPoint="bdd_printtable")>]
extern void bdd_printtable(BDD);

[<DllImport(@"bdd", EntryPoint="bdd_and")>]
extern BDD bdd_and(BDD, BDD);

[<DllImport(@"bdd", EntryPoint="bdd_xor")>]
extern BDD bdd_xor(BDD, BDD);

[<DllImport(@"bdd", EntryPoint="bdd_biimp")>]
extern BDD bdd_biimp(BDD, BDD);

[<DllImport(@"bdd", EntryPoint="bdd_or")>]
extern BDD bdd_or(BDD, BDD);

[<DllImport(@"bdd", EntryPoint="bdd_imp")>]
extern BDD bdd_imp(BDD, BDD);

[<DllImport(@"bdd", EntryPoint="bdd_not")>]
extern BDD bdd_not(BDD);

[<DllImport(@"bdd", EntryPoint="bdd_ite")>]
extern BDD bdd_ite(BDD, BDD);

[<DllImport(@"bdd", EntryPoint="bdd_setvarnum")>]
extern int bdd_setvarnum(int);

[<DllImport(@"bdd", EntryPoint="bdd_addref")>]
extern BDD bdd_addref(BDD);

[<DllImport(@"bdd", EntryPoint="bdd_setmaxincrease")>]
extern int bdd_setmaxincrease(int);

[<DllImport(@"bdd", EntryPoint="bdd_fnprintdot")>]
extern int bdd_fnprintdot(nativeint, BDD)

[<DllImport(@"bdd", EntryPoint="bdd_printdotprogHack")>]
extern int bdd_printdotprogHack(int, BDD)

[<DllImport(@"bdd", EntryPoint="bdd_printdotcircHack")>]
extern int bdd_printdotcircHack(int, BDD)

[<DllImport(@"bdd", EntryPoint="bdd_setcacheratio")>]
extern int bdd_setcacheratio(int)

// F# interface to match MLBDD
type t = BDD

let init op = 
    let tmp = match op with
        | None -> bdd_init(1000000, 1000)
        | Some n -> bdd_init(n, 100);
    if tmp < 0 
    then failwith "Could not initialize bdd"
    else ignore <| bdd_setvarnum(256);
         ignore <| bdd_setcacheratio(10);
         bdd_setmaxincrease(4000000)
let dtrue  _ = bdd_true()
let dfalse _ = bdd_false()
let ithvar _ i = bdd_ithvar(i)
let dnot b = bdd_not(b)
let dand b b' = bdd_addref <| bdd_and(b, b')
let xor b b' = bdd_addref <| bdd_xor(b, b')
let eq b b' = bdd_addref <| bdd_biimp(b, b')

let rec allsat b = match b with
    | 0 -> []
    | 1 -> [[]]
    | _ -> 
        let var = bdd_var(b)
        let low = bdd_low(b)
        let high = bdd_high(b)
        List.map (fun sat -> (false, var)::sat) (allsat low) @ 
        List.map (fun sat -> (true, var)::sat) (allsat high)

let equal b b' = b = b'
let print b = bdd_printtable(b)

let print_dot (fname:string) b = 
    let byteArr = Array.init fname.Length (fun i -> Convert.ToByte fname.[i])
    let gch = GCHandle.Alloc(byteArr,GCHandleType.Pinned)
    try ignore <| bdd_fnprintdot((gch.AddrOfPinnedObject()), b)
    finally gch.Free()
