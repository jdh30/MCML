module MCML.Interpreter

open MCML.Collections
open MCML.AST
open MCML.Errors

type Value =
  | VInt of int
  | VChar of char
  | VString of string
  | VTuple of Value list
  | VUnion of string * Value option
  | VClosure of VariableBindings * (Patt * Expr) list1
  | VPanic
  | VPrint
and Scope<'a> =
  { Nested: Map<string, Scope<'a>>
    Local: 'a }
and VariableBindings = Scope<(string * (Pos * Value ref)) list>

let VTuple = function [v] -> v | vs -> VTuple vs

let vTrue = VUnion("True", None)
let vFalse = VUnion("False", None)

// Scopes are:
//   built by the exec function
//   consumed by the interpreter
// Also need to be locally "open"ed in a module or expression.
module Scope =
  let empty =
    { Nested = Map.empty
      Local = [] }

  let rec find mdls vars =
    match mdls with
    | [] -> vars.Local
    | (mdl, _)::mdls ->
        match Map.tryFind mdl vars.Nested with
        | None -> failwithf "Internal error: Unknown module %s" mdl
        | Some vars -> find mdls vars

let (>>=) = Result.(>>=)

let rec stringOfValue value =
  match value with
  | VInt n -> string n
  | VChar c -> sprintf "'%c'" c
  | VString s -> sprintf "%A" s
  | VTuple vs -> sprintf "(%s)" (String.concat ", " (List.map stringOfValue vs))
  | VUnion(name, None) -> name
  | VUnion(name, Some arg) -> sprintf "%s(%s)" name (stringOfValue arg)
  | VClosure(_, (case, cases)) ->
      let cases = [for p, e in case::cases -> stringOfPatt p + " -> " + stringOfExpr e]
      sprintf "[%s]" (String.concat " | " cases)
  | VPanic -> "panic"
  | VPrint -> "print"

/// Try to match a value against a pattern accumulating bound variables vars.
let rec tryBind assign (vars: VariableBindings) (value, patt) =
  match value, patt with
  | _, (PAny _, _) -> Some vars
  | VInt m, (PInt n, _) -> if m = n then Some vars else None
  | VString s1, (PString s2, _) -> if s1 = s2 then Some vars else None
  | VTuple [], (PTuple [], _) -> Some vars
  | VTuple(v::vs), (PTuple(p::ps), pos) ->
      match tryBind assign vars (v, p) with
      | None -> None
      | Some vars -> tryBind assign vars (VTuple vs, (PTuple ps, pos))
  | VUnion(name1, value), (PUnion((_, (name2, _)), patt), _) ->
      if name1 <> name2 then None else
        match value, patt with
        | Some value, Some patt -> tryBind assign vars (value, patt)
        | None, None -> Some vars
        | _ -> failwith "Internal error: tryBind"
  | value, (PAs(patt, (name, pos)), _) ->
      match tryBind assign vars (value, patt) with
      | None -> None
      | Some vars -> Some(assign name (pos, value) vars)
  | value, (POr(patt1, patt2), _) ->
      match tryBind assign vars (value, patt1) with
      | None -> tryBind assign vars (value, patt2)
      | r -> r
  | value, (PVar var, pos) -> Some(assign var (pos, value) vars)
  | _ -> None

/// Match a value to a pattern or throw a match failure exception.
let bind assign vars (value, (_, pos as patt)) =
  match tryBind assign vars (value, patt) with
  | None -> Error(Unmatched(stringOfValue value), pos)
  | Some vars -> Ok vars

/// Match a value against a sequence of match cases, returning the
/// bound variables and expression matched.
let rec binds assign pos vars value = function
  | [] -> Error(Unmatched(stringOfValue value), pos)
  | (patt, expr)::actions ->
      match tryBind assign vars (value, patt) with
      | None -> binds assign pos vars value actions
      | Some vars -> Ok(vars, expr)

let findLocal (name, _) vars =
  match List.tryFind (fun (k, _) -> k=name) vars with
  | None -> failwithf "Internal error: Unknown variable %s" name
  | Some(_, v) -> v

/// Find a variable in the environment.
let find (mdls, var) vars =
  findLocal var (Scope.find mdls vars)

/// Create a new variable binding name to value.
let assignNew var (pos, value) vars =
  { vars with Local = (var, (pos, ref value))::vars.Local }

/// Find an existing variable binding and update its value.
let assignExisting pos var (_, value) vars =
  let _, r = findLocal (var, pos) vars.Local
  r := value
  vars

let rec pVarsIn bs patt =
  match patt with
  | (PAny | PInt _ | PString _ | PUnion(_, None)), _ -> bs
  | PVar x, pos -> Map.add x pos bs
  | PTuple patts, _ -> pVarsIns bs patts
  | (PUnion(_, Some patt) | PAs(patt, _)), _ -> pVarsIn bs patt
  | POr(patt1, patt2), _ -> pVarsIns bs [patt1; patt2]
and pVarsIns bs patts = List.fold pVarsIn bs patts

let rec map f xs =
  tramp { match xs with
          | [] -> return Ok []
          | x::xs ->
              let! x = f x
              let! xs = map f xs
              return Ok(x::xs) }

let map1 f (x, xs) =
  tramp { let! x = f x
          let! xs = map f xs
          return Ok(x::xs) }

let rec fold f a xs =
  tramp { match xs with
          | [] -> return Ok a
          | x::xs ->
              let! a = f a x
              return! fold f a xs }

let fold1 f a (x, xs) =
  tramp { let! a = f a x
          return! fold f a xs }

let rec eval (vars: VariableBindings) (expr, pos) =
  tramp { match expr with
          | EInt n -> return(Ok(VInt n))
          | EChar c -> return(Ok(VChar c))
          | EString s -> return(Ok(VString s))
          | EUnOp(Num1 Neg, n) ->
              let! v = eval vars n
              match v with
              | VInt n -> return(Ok(VInt -n))
              | v -> return failwithf "Internal error: ~-%A" v
          | EBinOp(f, Num2 op, g) ->
              let op = match op with Add -> (+) | Sub -> (-) | Mul -> (*) | Div -> (/) | Mod -> (%)
              return! evalIntOp vars f op g
          | EBinOp(f, Bool2 op, g) -> return! evalBoolOp vars f op g
          | EBinOp(f, Compare, g) ->
              let! f = eval vars f
              let! g = eval vars g
              return(Ok(VInt(compare f g |> sign)))
          | EVar var -> return(Ok !(find var vars |> snd))
          | ETuple es ->
              let! vs = map (eval vars) es
              return(Ok(VTuple vs))
          | EApply(f, arg)
          | EBinOp(arg, PipeLine, f) ->
              let! f = eval vars f
              let! arg = eval vars arg
              match f, arg with
              | VClosure(vars2, (case, cases)), arg ->
                  let! vars2, expr = tramp { return binds assignNew pos vars2 arg (case::cases) }
                  return! eval vars2 expr
              | VUnion(name, None), arg ->
                  return(Ok(VUnion(name, Some arg)))
              | VPanic, VString msg -> return(Error(Panic msg, pos))
              | VPanic, v -> return failwithf "Internal error: panic %A" v
              | VPrint, v ->
                  //printfn "%s" (stringOfValue v)
                  return(Ok(VTuple []))
              | f, arg ->
                  return
                    failwithf "Internal error: Application of %A(%A)"
                      (stringOfValue f) (stringOfValue arg)
          | EFunction cases -> return(Ok(VClosure(vars, cases)))
          | ELetIn(rc, bindings, rest) ->
              let! vars = evalLet rc vars bindings
              return! eval vars rest
          | EPanic -> return(Ok VPanic)
          | EPrint -> return(Ok VPrint) }
and evalIntOp vars f op g =
  tramp { let! m = eval vars f
          let! n = eval vars g
          match m, n with
          | VInt m, VInt n -> return(Ok(VInt(op m n)))
          | _ -> return failwithf "Internal error: (%A) %A %A" op m n }
and evalBoolOp vars f op g =
  tramp { let! b1 = eval vars f
          match op, b1=vTrue with
          | And, false | Or, true -> return(Ok b1)
          | _ -> return! eval vars g }
and evalLet rc vars bindings =
  tramp { match rc with
          | NotRec ->
              let f vars (patt, body) =
                tramp { let! value = eval vars body
                        return(bind assignNew vars (value, patt)) }
              return! fold1 f vars bindings
          | Rec ->
              let f vars ((_, pos as patt), body) =
                tramp { let! value = eval vars body
                        return bind (assignExisting pos) vars (value, patt) }
              let patt, patts = List1.map fst bindings
              let pVars = pVarsIns Map.empty (patt::patts)
              let make vars x pos = { vars with Local=(x, (pos, ref(VTuple[])))::vars.Local }
              let vars = Map.fold make vars pVars
              return! fold1 f vars bindings }

let rec exec prefix vars (defn, _) =
  tramp { match defn with
          | SLet(rc, bindings) ->
              return! evalLet rc vars bindings
          | SUnion(_, _, cases) ->
              let addCase vars ((name, pos), _) =
                let value = VUnion(name, None)
                { vars with Local = (name, (pos, ref value))::vars.Local }
              return Ok(List1.fold addCase vars cases)
          | SModule((name, _), defns) ->
              let! vars2 = fold (exec (prefix @ [name])) vars defns
              return
                Ok { Nested = Map.add name vars2 vars.Nested
                     Local = vars.Local } }

module Env = TypeInference.Env

let parseAndRun str =
  let typeOfPos = dictionary[]
  let result =
    Parser.parse str >>= fun (tokens, stmts) ->
    TypeInference.infer typeOfPos Env.empty stmts >>= fun _ ->
    let exec = fold (exec []) Scope.empty stmts
    let _, result = Trampoline.runTram 0 exec
    result >>= fun vars ->
    Ok(tokens, vars, stmts, typeOfPos)
  match result with
  | Ok x -> Ok x
  | Error(msg, pos) -> Error(msg, pos, typeOfPos)
