module CopyConstPropFold


(*
    (* An optimisation takes a program and returns a new program. *)
    val optimiseProgram : Fasto.KnownTypes.Prog -> Fasto.KnownTypes.Prog
*)

open AbSyn

(* A propagatee is something that we can propagate - either a variable
   name or a constant value. *)
type Propagatee =
    ConstProp of Value
  | VarProp   of string

type VarTable = SymTab.SymTab<Propagatee>

// helper function to check if its safe to optimize a variable
let rec isFreeIn (name : string) (e : TypedExp) : bool =
    match e with 
    | Var (vname, pos) -> vname = name
    | Plus (e1, e2, _) | Minus (e1, e2, _) | Times (e1, e2, _)
    | Divide (e1, e2, _) | And (e1, e2, _) | Or (e1, e2, _)
    | Equal (e1, e2, _) | Less (e1, e2, _) -> isFreeIn name e1 || isFreeIn name e2
    | Let (Dec (vname, ed, decpos), body, _) -> isFreeIn name ed || (vname <> name && isFreeIn name body)
    | Not (e, _) | Negate (e, _) | Iota (e, _)
    | Length (e, _, _) | Write (e, _, _) -> isFreeIn name e
    | Apply (_, args, _) -> List.exists (isFreeIn name) args
    | If (e1, e2, e3, _) -> isFreeIn name e1 || isFreeIn name e2 || isFreeIn name e3
    | _ -> false

let removeStaleVarProps (name : string) (vtable : VarTable) : VarTable =
    SymTab.fromList (List.filter (fun (_, prop) -> prop <> VarProp name) (SymTab.toList vtable))

    
let rec copyConstPropFoldExp (vtable : VarTable)
                             (e      : TypedExp) =
    match e with
        (* Copy propagation is handled entirely in the following three
        cases for variables, array indexing, and let-bindings. *)
        | Var (name, pos) ->
            match SymTab.lookup name vtable with
            | Some (VarProp v)   -> Var (v, pos)        // let y = x in ... y ...; replace y with x
            | Some (ConstProp c) -> Constant (c, pos)   // let y = 5 in ... y ...; replace y with 5
            | None               -> Var (name, pos)     // leave it alone

        | Index (name, ei, t, pos) ->
            let ei' = copyConstPropFoldExp vtable ei

            match SymTab.lookup name vtable with
            | Some (VarProp v)      -> Index (v, ei', t, pos)
            | Some (ConstProp (_))  -> Index (name, ei', t, pos)
            | None                  -> Index (name, ei', t, pos)
            
            
        | Let (Dec (name, ed, decpos), body, pos) ->
            let ed' = copyConstPropFoldExp vtable ed
            match ed' with
                | Var (vname, _) ->
                    let vtable' = removeStaleVarProps name (SymTab.bind name (VarProp vname) vtable)   // let x = y in; return just y for future lookups
                    let body' = copyConstPropFoldExp vtable' body
                    Let (Dec (name, ed', decpos), body', pos)
                    
                | Constant (cname, _) ->
                    let vtable' = removeStaleVarProps name (SymTab.bind name (ConstProp cname) vtable) // let x = 5 in; return just 5 
                    let body' = copyConstPropFoldExp vtable' body
                    Let (Dec (name, ed', decpos), body', pos)
                    
                | Let (Dec (iname, ied, idecpos), ibody_inner, ipos) ->
                    let inner = Let (Dec (name, ibody_inner, decpos), body, pos)
                    let restructured = Let (Dec (iname, ied, idecpos), inner, ipos)

                    if not (isFreeIn iname body) then
                        copyConstPropFoldExp vtable restructured
                    else 
                        let body' = copyConstPropFoldExp vtable body
                        Let (Dec (name, ed', decpos), body', pos)


                | _ -> (* Fallthrough - for everything else, just optimize body *)
                    let vtable' = removeStaleVarProps name vtable
                    let body' = copyConstPropFoldExp vtable' body
                    Let (Dec (name, ed', decpos), body', pos)
                      (* Or maybe rename the inner bound variable
                         to some fresh identifier, to avoid inadvertently
                         shadowing any bindings using `name` in vtable? *)

        | Times (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with 
            | (Constant (IntVal 1, _), _) -> e2'
            | (_, Constant (IntVal 1, _)) -> e1'
            | (Constant (IntVal 0, _), _) -> Constant (IntVal 0, pos)
            | (_, Constant (IntVal 0, _)) -> Constant (IntVal 0, pos)
            | (Constant (IntVal x, _), Constant (IntVal y, _)) -> Constant (IntVal (x * y), pos)
            | _ -> Times (e1', e2', pos)
            
        | And (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1 
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
            | (Constant (BoolVal a,_), Constant (BoolVal b,_)) ->
                Constant (BoolVal (a && b), pos)
            | (Constant (BoolVal false, _), _) -> Constant (BoolVal false, pos)
            | (_, Constant (BoolVal false, _)) -> Constant (BoolVal false, pos)
            | (Constant (BoolVal true, _), _) -> e2'
            | (_, Constant (BoolVal true, _)) -> e1'
            | _ -> And (e1', e2', pos)
        | Constant (x,pos) -> Constant (x,pos)
        | StringLit (x,pos) -> StringLit (x,pos)
        | ArrayLit (es, t, pos) ->
            ArrayLit (List.map (copyConstPropFoldExp vtable) es, t, pos)
        | Plus (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal x, _), Constant (IntVal y, _)) ->
                    Constant (IntVal (x + y), pos)
                | (Constant (IntVal 0, _), _) -> e2'
                | (_, Constant (IntVal 0, _)) -> e1'
                | _ -> Plus (e1', e2', pos)
        | Minus (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal x, _), Constant (IntVal y, _)) ->
                    Constant (IntVal (x - y), pos)
                | (_, Constant (IntVal 0, _)) -> e1'
                | _ -> Minus (e1', e2', pos)
        | Equal (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal v1, _), Constant (IntVal v2, _)) ->
                    Constant (BoolVal (v1 = v2), pos)
                | _ ->
                    if false (* e1' = e2' *)  (* <- this would be unsafe! (why?) *)
                    then Constant (BoolVal true, pos)
                    else Equal (e1', e2', pos)
        | Less (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal v1, _), Constant (IntVal v2, _)) ->
                    Constant (BoolVal (v1 < v2), pos)
                | _ ->
                    if false (* e1' = e2' *)  (* <- as above *)
                    then Constant (BoolVal false, pos)
                    else Less (e1', e2', pos)
        | If (e1, e2, e3, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            match e1' with
                | Constant (BoolVal b, _) ->
                    if b
                    then copyConstPropFoldExp vtable e2
                    else copyConstPropFoldExp vtable e3
                | _ ->
                    If (e1',
                        copyConstPropFoldExp vtable e2,
                        copyConstPropFoldExp vtable e3,
                        pos)
        | Apply (fname, es, pos) ->
            Apply (fname, List.map (copyConstPropFoldExp vtable) es, pos)
        | Iota (en, pos) ->
            Iota (copyConstPropFoldExp vtable en, pos)
        | Length (ea, t, pos) ->
            Length (copyConstPropFoldExp vtable ea, t, pos)
        | Replicate (en, ev, t, pos) ->
            Replicate (copyConstPropFoldExp vtable en,
                       copyConstPropFoldExp vtable ev,
                       t, pos)
        | Map (farg, el, t1, t2, pos) ->
            Map (copyConstPropFoldFunArg vtable farg,
                 copyConstPropFoldExp vtable el,
                 t1, t2, pos)
        | Filter (farg, el, t1, pos) ->
            Filter (copyConstPropFoldFunArg vtable farg,
                    copyConstPropFoldExp vtable el,
                    t1, pos)
        | Reduce (farg, e0, el, t, pos) ->
            Reduce (copyConstPropFoldFunArg vtable farg,
                    copyConstPropFoldExp vtable e0,
                    copyConstPropFoldExp vtable el,
                    t, pos)
        | Scan (farg, e0, el, t, pos) ->
            Scan (copyConstPropFoldFunArg vtable farg,
                  copyConstPropFoldExp vtable e0,
                  copyConstPropFoldExp vtable el,
                  t, pos)
        | Divide (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
            | (Constant (IntVal x, _), Constant (IntVal y, _)) when y <> 0 ->
                Constant (IntVal (x / y), pos)
            | _ -> Divide (e1', e2', pos)
        | Or (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (BoolVal a, _), Constant (BoolVal b, _)) ->
                    Constant (BoolVal (a || b), pos)
                | _ -> Or (e1', e2', pos)
        | Not (e0, pos) ->
            let e0' = copyConstPropFoldExp vtable e0
            match e0' with
                | Constant (BoolVal a, _) -> Constant (BoolVal (not a), pos)
                | _ -> Not (e0', pos)
        | Negate (e0, pos) ->
            let e0' = copyConstPropFoldExp vtable e0
            match e0' with
                | Constant (IntVal x, _) -> Constant (IntVal (-x), pos)
                | _ -> Negate (e0', pos)
        | Read (t, pos) -> Read (t, pos)
        | Write (e0, t, pos) -> Write (copyConstPropFoldExp vtable e0, t, pos)

and copyConstPropFoldFunArg (vtable : VarTable)
                            (farg   : TypedFunArg) =
    match farg with
        | FunName fname -> FunName fname
        | Lambda (rettype, paramls, body, pos) ->
            (* Remove any bindings with the same names as the parameters. *)
            let paramNames = (List.map (fun (Param (name, _)) -> name) paramls)
            let vtable'    = SymTab.removeMany paramNames vtable
            Lambda (rettype, paramls, copyConstPropFoldExp vtable' body, pos)

let copyConstPropFoldFunDec = function
    | FunDec (fname, rettype, paramls, body, loc) ->
        let body' = copyConstPropFoldExp (SymTab.empty ()) body
        FunDec (fname, rettype, paramls, body', loc)

let optimiseProgram (prog : TypedProg) =
    List.map copyConstPropFoldFunDec prog
