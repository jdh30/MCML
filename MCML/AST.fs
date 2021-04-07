/// Abstract syntax trees.
module MCML.AST

open MCML.Collections

type Pos = { Start: int; End: int }

type Ident = string * Pos

type Path = Ident list * Ident

let stringOfPath (mdls, name) =
  String.concat "." (List.map fst (mdls @ [name]))

type Rec = Rec | NotRec

type NumberUnOp = Neg
type NumberBinOp = Add | Sub | Mul | Div | Mod
type BooleanBinOp = And | Or
type UnOp = Num1 of NumberUnOp
type BinOp = Num2 of NumberBinOp | Bool2 of BooleanBinOp | Compare | PipeLine

type TypeVariable = TypeVariable of int

type Type =
  | TVar of TypeVariable
  | TInt
  | TChar
  | TString
  | TRef of Ident * Type list
  | TTuple of Type list
  | TArrow of Type * Type

let TTuple = function [ty] -> ty | tys -> TTuple tys

let noPos = {Start=0; End=0}
let tyBool = TRef(("Bool", {Start=5; End=9}), [])
let tyCompare = TRef(("Comparison", noPos), [])

type TypeExprAux =
  | TEParam of string
  | TEInt
  | TEString
  | TERef of Path * TypeExpr list
  | TETuple of TypeExpr list
  | TEArrow of TypeExpr * TypeExpr
and TypeExpr = TypeExprAux * Pos

let TETuple = function [te, _] -> te | tes -> TETuple tes

type TypeDefinitionAux =
  | TUnion of (Ident * Type option) list
and TypeDefinition = TypeDefinitionAux * Pos

/// Untyped abstract syntax trees with the position of every node.
type PattAux =
  | PAny
  | PInt of int
  | PString of string
  | PVar of string
  | PTuple of Patt list
  | PUnion of Path * Patt option
  | PAs of Patt * Ident
  | POr of Patt * Patt
and Patt = PattAux * Pos

let PTuple = function [p, _] -> p | ps -> PTuple ps

type ExprAux =
  | EInt of int
  | EChar of char
  | EString of string
  | EUnOp of UnOp * Expr
  | EBinOp of Expr * BinOp * Expr
  | EVar of Path
  | ETuple of Expr list
  | EApply of Expr * Expr
  | EFunction of (Patt * Expr) list1
  | ELetIn of Rec * (Patt * Expr) list1 * Expr
  | EPanic
  | EPrint
and Expr = ExprAux * Pos

let ETuple = function [e, _] -> e | es -> ETuple es

type StatementAux =
  | SLet of Rec * (Patt * Expr) list1
  | SUnion of Rec * (Ident * Ident list) * (Ident * TypeExpr option) list1
  | SModule of Ident * Statement list
and Statement = StatementAux * Pos

//let arrow = "->"
let arrow = "→"

let rec stringOfName (prefix, name) =
  String.concat "." (prefix @ [name] |> List.map fst)

let rec stringOfPatt (patt, _) = stringOfPattAux patt
and stringOfPattAux patt =
  match patt with
  | PAny -> "_"
  | PInt n -> string n
  | PString s -> sprintf "%A" s
  | PVar s -> s
  | PTuple ps -> sprintf "(%s)" (String.concat ", " (Seq.map stringOfPatt ps))
  | PUnion(name, None) -> stringOfName name
  | PUnion(name, Some arg) -> sprintf "(%s %s)" (stringOfName name) (stringOfPatt arg)
  | PAs(patt, (name, _)) -> sprintf "(%s as %s)" (stringOfPatt patt) name
  | POr(patt1, patt2) -> sprintf "(%s | %s)" (stringOfPatt patt1) (stringOfPatt patt2)

let rec stringOfExpr (expr, _) = stringOfExprAux expr
and stringOfExprAux expr =
  match expr with
  | EInt n -> string n
  | EChar c -> sprintf "'%c'" c // FIXME: Emit non-ASCII as '\065' etc.?
  | EString s -> sprintf "%A" s
  | EUnOp(Num1 Neg, x) -> sprintf "-(%s)" (stringOfExpr x)
  | EBinOp(x, Num2 op, y) ->
      let op = match op with Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
      sprintf "(%s) %s (%s)" (stringOfExpr x) op (stringOfExpr y)
  | EBinOp(x, Bool2 op, y) ->
      let op = match op with And -> "&&" | Or -> "||"
      sprintf "(%s) %s (%s)" (stringOfExpr x) op (stringOfExpr y)
  | EBinOp(x, Compare, y) -> sprintf "$compare (%s) (%s)" (stringOfExpr x) (stringOfExpr y)
  | EBinOp(x, PipeLine, y) -> sprintf "(%s |> %s)" (stringOfExpr x) (stringOfExpr y)
  | EVar name -> stringOfName name
  | ETuple fs -> sprintf "(%s)" (String.concat ", " (Seq.map stringOfExpr fs))
  | EApply(f, x) -> sprintf "(%s %s)" (stringOfExpr f) (stringOfExpr x)
  | EFunction cases -> sprintf "[%s]" (stringOfCases cases)
  | ELetIn(rc, bindings, rest) ->
      let rc = match rc with NotRec -> "" | Rec -> " rec"
      sprintf "let%s %s in %s" rc (stringOfBindings bindings) (stringOfExpr rest)
  | EPanic -> "panic"
  | EPrint -> "print"
and stringOfCases (case, cases) =
  [ for p, e in case::cases -> sprintf "%s -> %s" (stringOfPatt p) (stringOfExpr e) ]
  |> String.concat " | "
and stringOfBindings (defn, defns) =
  [ for p, e in defn::defns -> sprintf "%s = %s" (stringOfPatt p) (stringOfExpr e) ]
  |> String.concat " and "

module Type =
  let prec = function
    | TInt | TChar | TString | TVar _ -> 9
    | TRef _ -> 8
    | TTuple _ -> 6
    | TArrow _ -> 4

  let rec stringOfTypeAux outer (ns: Map<_, _>) ty =
    let inner = prec ty
    let s, ns =
      match ty with
      | TInt -> "Int", ns
      | TChar -> "Char", ns
      | TString -> "String", ns
      | TVar(TypeVariable n) ->
          let f i = string(char(int 'α' + i))
          match Map.tryFind n ns with
          | None ->
              let i = Map.count ns
              f i, Map.add n i ns
          | Some i -> f i, ns
      | TRef((name, _), []) -> name, ns
      | TRef((name, _), args) ->
          let ss, ns = List.mapFold (stringOfTypeAux 8) ns args
          String.concat " " (name::ss), ns
      | TTuple [] -> "()", ns
      | TTuple tys ->
          let tys, ns = List.mapFold (stringOfTypeAux (inner+1)) ns tys
          String.concat ", " tys, ns
      | TArrow(ty1, ty2) ->
          let s1, ns = stringOfTypeAux (inner+1) ns ty1
          let s2, ns = stringOfTypeAux inner ns ty2
          sprintf "%s %s %s" s1 arrow s2, ns
    (if outer > inner then sprintf "(%s)" s else s), ns

  /// Pretty print a type as a string.
  let toString ty =
    let s, _ = stringOfTypeAux -1 Map.empty ty
    s

  /// Pretty print a pair of types as strings.
  let toString2 ty1 ty2 =
    let s1, m = stringOfTypeAux -1 Map.empty ty1
    let s2, _ = stringOfTypeAux -1 m ty2
    s1, s2
