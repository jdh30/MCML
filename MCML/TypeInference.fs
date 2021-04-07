/// Use the Damas-Milner type inference algorithm to annotate
/// an abstract syntax tree (AST) with types.
module MCML.TypeInference

open MCML.Collections
open MCML.AST
open MCML.Errors

let (>>=) = Result.(>>=)

let mutable currTyVar = 0

module Env =
  type Binding =
    | Var of string * Type
    | UnionType of string * (string list * Pos)
    | Constr of string * (Type option * Type)
    | Module of string * Binding list

  type Env = Env of Binding list list1

  let empty = Env([], [])

  let rec tryFindUnionType (mdls, (name1, _ as ident)) (Env(bs, bss)) =
    match mdls, bs, bss with
    | _, [], [] -> None
    | [], UnionType(name2, pos)::_, _ when name1 = name2 -> Some pos
    | [], _::bs, bss -> tryFindUnionType (mdls, ident) (Env(bs, bss))
    | (mdl1, _)::mdln as mdls, Module(mdl2, bs2)::bs3, bss when mdl1=mdl2 ->
        match tryFindUnionType (mdln, ident) (Env(bs2, [])) with
        | None -> tryFindUnionType (mdls, ident) (Env(bs3, bss))
        | result -> result
    | mdls, [], bs::bss -> tryFindUnionType (mdls, ident) (Env(bs, bss))
    | mdls, _::bs, bss -> tryFindUnionType (mdls, ident) (Env(bs, bss))

  let rec tryFindConstructor (mdls, (name1, _ as ident) as path) (Env(bs, bss)) =
    match mdls, bs, bss with
    | _, [], [] -> Error(UnknownConstructor(stringOfPath path), Parser.unions1 ident mdls)
    | [], Constr(name2, (argType, retTypeName))::_, _ when name1 = name2 ->
        Ok(argType, retTypeName)
    | [], _::bs, bss -> tryFindConstructor (mdls, ident) (Env(bs, bss))
    | (mdl1, _)::mdln as mdls, Module(mdl2, bs2)::bs3, bss when mdl1=mdl2 ->
        match tryFindConstructor (mdln, ident) (Env(bs2, [])) with
        | Error(UnknownConstructor _, _) -> tryFindConstructor (mdls, ident) (Env(bs3, bss))
        | result -> result
    | mdls, [], bs::bss -> tryFindConstructor (mdls, ident) (Env(bs, bss))
    | mdls, _::bs, bss -> tryFindConstructor (mdls, ident) (Env(bs, bss))

  let rec tryFindVar (mdls, (name1, _ as ident)) (Env(bs, bss)) =
    match mdls, bs, bss with
    | _, [], [] -> None
    | [], Var(name2, ty)::_, _ when name1 = name2 -> Some ty
    | [], _::bs, bss -> tryFindVar (mdls, ident) (Env(bs, bss))
    | (mdl1, _)::mdln as mdls, Module(mdl2, bs2)::bs3, bss when mdl1=mdl2 ->
        match tryFindVar (mdln, ident) (Env(bs2, [])) with
        | None -> tryFindVar (mdls, ident) (Env(bs3, bss))
        | result -> result
    | mdls, [], bs::bss -> tryFindVar (mdls, ident) (Env(bs, bss))
    | mdls, _::bs, bss -> tryFindVar (mdls, ident) (Env(bs, bss))

  let addVar x v (Env(bs, bss)) =
    Env(Var(x, v)::bs, bss)

  let addVars (bindings: Map<string, Type>) (Env(bs, bss)) =
    Env(Map.fold (fun bs name ty -> Var(name, ty)::bs) bs bindings, bss)

  let addConstructor (constr, pos) argTy retTy (Env(bs, bss)) =
    Env(Constr(constr, (argTy, retTy))::bs, bss)

  let addType (name, args) (Env(bs, bss)) =
    Env(UnionType(fst name, (List.map fst args, Parser.unions1 name args))::bs, bss)

  let startModule (Env(bs, bss)) = Env([], bs::bss)

  let endModule (name, _) (Env(bs, bss)) =
    match bs, bss with
    | _, [] -> failwith "Internal error: module end in outer scope"
    | bs1, bs2::bss -> Env((Module(name, bs1)::bs2), bss)

let rec typeOfTypeExpr env tyVars pos (te, _) =
  match te with
  | TEArrow(te1, te2) ->
      typeOfTypeExpr env tyVars pos te1 >>= fun te1 ->
      typeOfTypeExpr env tyVars pos te2 >>= fun te2 ->
      Ok(TArrow(te1, te2))
  | TEInt -> Ok TInt
  | TERef((_, (name, _) as path), args) ->
      match Env.tryFindUnionType path env with
      | None ->
          Error(UnknownType name, pos)
      | Some(_, tyPos) ->
          Result.List.map (typeOfTypeExpr env tyVars pos) args >>= fun args ->
          Ok(TRef((name, tyPos), args))
  | TEString -> Ok TString
  | TETuple tes ->
      Result.List.map (typeOfTypeExpr env tyVars pos) tes >>= fun tys ->
      Ok(TTuple tys)
  | TEParam u ->
      match Dictionary.tryFind u tyVars with
      | None -> Error(UnknownTypeVariable, pos)
      | Some ty -> Ok ty

/// Bind variable name "x" at position "pos" to a new type variable.
let bind b (x, pos) ty =
  match Dictionary.tryFind x b with
  | Some _ -> Error(DuplicatePatternName x, pos)
  | None ->
      b.Add(x, ty)
      Ok()

let posOf (_, pos, _) = pos

let typeOf (_, _, ty) = ty

let rec inferTuple f xs =
  Result.List.map f xs >>= fun tys ->
  Ok(TTuple tys)

let stringOfPath ((mdls, name): Path) =
  String.concat "." [for s, _ in mdls@[name] -> s]

let infer (typeOfPos: Dictionary<_, _>) env stmts =
  /// Substitutions represented as a dictionary mapping type variable to type.
  let s = dictionary[]

  /// The set of generalized type variables.
  let g = hashSet[]

  let mutable level = 0

  /// Level of a type variable.
  let levelOf = dictionary[]

  /// Generate a new type variable name.
  let newTypeVariable () =
    currTyVar <- currTyVar + 1
    let tv = TypeVariable currTyVar
    levelOf.[tv] <- level
    TVar tv

  let typeOfTypeName (tyName, tyArgs) =
    let pos = Parser.unions1 tyName tyArgs
    let tyVars = dictionary[]
    for arg, _ in tyArgs do
      tyVars.[arg] <- newTypeVariable()
    tyVars, Type.TRef((fst tyName, pos), [for arg, _ in tyArgs -> tyVars.[arg]])

  /// If the type is a type variable then apply any substitutions to it until we
  /// get a non-variable (but the resulting type may still contain variables
  /// that require further substitution).
  let rec subst1 ty =
    match ty with
    | TVar u ->
        match Dictionary.tryFind u s with
        | None -> ty
        | Some ty -> subst1 ty
    | ty -> ty

  let rec subst ty =
    match subst1 ty with
    | TVar _
    | TInt
    | TChar
    | TString as ty -> ty
    | TRef(path, args) -> TRef(path, List.map subst args)
    | TTuple tys -> TTuple(List.map subst tys)
    | TArrow(ty1, ty2) -> TArrow(subst ty1, subst ty2)

  /// Check if the type variable u appears in the type ty.
  let rec contains u ty =
    match subst1 ty with
    | TVar v ->
        levelOf.[v] <- min levelOf.[u] levelOf.[v]
        u=v
    | TInt | TChar | TString -> false
    | TArrow(t1, t2) -> contains u t1 || contains u t2
    | TTuple tys
    | TRef(_, tys) -> List.exists (contains u) tys

  /// Constrain the type variable u to be of the type ty.
  let rec constrain (u: TypeVariable) ty pos =
    match subst1 ty with
    | TVar v when u=v -> Ok()
    | ty ->
        if contains u ty then
          Error(CyclicType(TVar u, ty), pos)
        else
          Dictionary.add u ty s
          Ok()

  /// Unify type ty1 with type ty2 by adding substitutions to s.
  let rec unify pos ty1 ty2 =
    match subst1 ty1, subst1 ty2 with
    | TArrow(ty11, ty12), TArrow(ty21, ty22) ->
        unifys pos [ty11; ty12] [ty21; ty22]
    | TVar u, ty
    | ty, TVar u -> constrain u ty pos
    | TInt, TInt
    | TString, TString -> Ok()
    | TTuple tys1, TTuple tys2 ->
        if tys1.Length <> tys2.Length then
          printfn "%A" (TupleLengthsDiffer(ty1, ty2), pos)
          Error(TupleLengthsDiffer(ty1, ty2), pos)
        else unifys pos tys1 tys2
    | TRef(t1, tyArgs1), TRef(t2, tyArgs2) ->
        if t1 = t2 then
          unifys pos tyArgs1 tyArgs2
        else
          Error(TypeMismatch(ty1, ty2), pos)
    | ty1, ty2 -> Error(TypeMismatch(ty1, ty2), pos)
  and unifys pos tys1 tys2 =
    match tys1, tys2 with
    | [], [] -> Ok()
    | ty1::tys1, ty2::tys2 ->
        unify pos ty1 ty2 >>= fun () -> unifys pos tys1 tys2
    | _ -> failwith "Internal error: TypeInference.unifys"

  /// Given two sets of bindings combine them into one set returning an
  /// error if any duplicates are found.
  let andBindings pos b1 b2 =
    Result.Seq.fold (fun b1 (x, v) ->
      match Map.tryFind x b1 with
      | Some _ -> Error(DuplicatePatternName x, pos)
      | None -> Ok(Map.add x v b1)) b1 (Map.toSeq b2)

  /// Given two sets of bindings check that they bind the same sets of
  /// variables, unifying their types, returning an error if the sets
  /// of bound variables differ.
  let orBindings pos b1 b2 =
    Result.Seq.fold (fun b1 (x, ty1) ->
      match Map.tryFind x b1 with
      | Some ty2 ->
          unify pos ty1 ty2 >>= fun () ->
          Ok(Map.remove x b1)
      | None -> Error(MissingPatternName x, pos)) b1 (Map.toSeq b2) >>= fun diff ->
    match Seq.tryHead (Map.toSeq diff) with
    | None -> Ok b1
    | Some(x, _) -> Error(MissingPatternName x, pos)

  let rec refresh vs ty =
    match subst1 ty with
    | TVar u as ty ->
        match HashSet.contains u g, Dictionary.tryFind u vs with
        | true, None ->
            let v = newTypeVariable()
            vs.[u] <- v
            v
        | true, Some v -> v
        | false, _ -> ty
    | TInt | TChar | TString as ty -> ty
    | TRef(p, tys) -> TRef(p, List.map (refresh vs) tys)
    | TTuple tys -> TTuple(List.map (refresh vs) tys)
    | TArrow(ty1, ty2) -> TArrow(refresh vs ty1, refresh vs ty2)

  /// Infer the type of a pattern adding the position and type of all
  /// new bound variables to the dictionary "b".
  let rec inferPatt env (patt, pos) =
    let add(ty, b) =
      typeOfPos.[pos] <- ty
      Ok(ty, b)
    match patt with
    | PAny -> add(newTypeVariable(), Map.empty)
    | PInt _ -> add(TInt, Map.empty)
    | PString _ -> add(TString, Map.empty)
    | PVar x ->
        let ty = newTypeVariable()
        add(ty, Map[x, ty])
    | PTuple ps ->
        let f b1 p =
          inferPatt env p >>= fun (ty, b2) ->
          andBindings pos b1 b2 >>= fun b ->
          Ok(ty, b)
        Result.List.mapFold f Map.empty ps >>= fun (tys, b) ->
        add(TTuple tys, b)
    | PUnion(path, patt) ->
        Env.tryFindConstructor path env >>= fun (argTy, retTy) ->
        let argTy, retTy =
          let refresh = refresh (dictionary[])
          Option.map refresh argTy, refresh retTy
        Result.Option.map (inferPatt env) patt >>= fun p ->
        match p, argTy with
        | None, None -> add(retTy, Map.empty)
        | Some(pattTy, b), Some argTy ->
            unify pos pattTy argTy >>= fun () ->
            add(retTy, b)
        | None, Some argTy -> Error(ConstructorRequiresArgument argTy, pos)
        | Some _, None -> Error(ConstructorDoesNotRequireArgument, pos)
    | PAs(p, (name, pos)) ->
        inferPatt env p >>= fun (pattTy, b) ->
        andBindings pos b (Map[name, pattTy]) >>= fun b ->
        add(pattTy, b)
    | POr(p1, p2) ->
        inferPatt env p1 >>= fun (pattTy1, b1) ->
        inferPatt env p2 >>= fun (pattTy2, b2) ->
        orBindings pos b1 b2 >>= fun b ->
        unify pos pattTy1 pattTy2 >>= fun () ->
        add(pattTy1, b)

  let rec generalise ty =
    match subst1 ty with
    | TVar tv ->
        if levelOf.[tv] > level then
          ignore(g.Add tv)
    | TInt | TChar | TString -> ()
    | TRef(_, tys)
    | TTuple tys -> List.iter generalise tys
    | TArrow(ty1, ty2) -> List.iter generalise [ty1; ty2]

  /// Infer the type of an expression.
  let rec inferExpr env (expr, pos) =
    let add ty =
      typeOfPos.[pos] <- ty
      Ok ty
    match expr with
    | EVar path ->
        match Env.tryFindVar path env with
        | None -> Error(UnknownVariable(stringOfPath path), pos)
        | Some ty -> add(refresh (dictionary[]) ty)
    | EInt _ -> add TInt
    | EChar _ -> add TChar
    | EString _ -> add TString
    | EUnOp(Num1 Neg, f) ->
        inferExpr env f >>= fun fTy ->
        unify pos TInt fTy >>= fun () ->
        add TInt
    | EBinOp(f, Num2 _, g) ->
        inferExpr env f >>= fun fTy ->
        unify pos TInt fTy >>= fun () ->
        inferExpr env g >>= fun gTy ->
        unify pos TInt gTy >>= fun () ->
        add TInt
    | EBinOp(f, Bool2 _, g) ->
        inferExpr env f >>= fun fTy ->
        unify pos tyBool fTy >>= fun () ->
        inferExpr env g >>= fun gTy ->
        unify pos tyBool gTy >>= fun () ->
        add tyBool
    | EBinOp(f, Compare, g) ->
        inferExpr env f >>= fun fTy ->
        inferExpr env g >>= fun gTy ->
        unify pos fTy gTy >>= fun () ->
        add TInt
    | ETuple es -> inferTuple (inferExpr env) es >>= add
    | EBinOp(arg, PipeLine, (_, fnPos as fn)) ->
        inferExpr env arg >>= fun argTy ->
        inferExpr env fn >>= fun fnTy ->
        inferApply fnPos fnTy argTy add
    | EApply(fn, (_, argPos as arg)) ->
        inferExpr env fn >>= fun fnTy ->
        inferExpr env arg >>= fun argTy ->
        inferApply argPos fnTy argTy add
    | EFunction((patt1, expr1), cases) ->
        inferCase env (patt1, expr1) >>= fun (patt1Ty, expr1Ty) ->
        let inferCase case =
          inferCase env case >>= fun (pattTy, exprTy) ->
          unify pos patt1Ty pattTy >>= fun () ->
          unify pos expr1Ty exprTy
        Result.List.iter inferCase cases >>= fun () ->
        add(TArrow(patt1Ty, expr1Ty))
    | ELetIn(rc, defns, rest) ->
        inferLet env rc defns >>= fun env ->
        inferExpr env rest >>= fun restTy ->
        add restTy
    | EPanic -> add(TArrow(TString, newTypeVariable()))
    | EPrint -> add(TArrow(newTypeVariable(), TTuple[]))
  and inferApply pos fnTy argTy add =
    let retTy = newTypeVariable()
    unify pos (TArrow(argTy, retTy)) fnTy >>= fun () ->
    add retTy

  /// Infer the type of the pattern that binds variables used in the expression.
  and inferCase env (patt, expr) =
    inferPatt env patt >>= fun (pattTy, b) ->
    let env = Env.addVars b env
    inferExpr env expr >>= fun exprTy ->
    Ok(pattTy, exprTy)

  and inferLet env rc defns =
    let f1 b1 (patt, (_, exprPos as expr)) =
      inferPatt env patt >>= fun (pattTy, b2) ->
      andBindings exprPos b1 b2 >>= fun b ->
      Ok((pattTy, expr), b)
    let f2 env (pattTy, (_, exprPos as expr)) =
      inferExpr env expr >>= fun exprTy ->
      unify exprPos pattTy exprTy
    level <- level + 1
    Result.List1.mapFold f1 Map.empty defns >>= fun (defns, b) ->
    let result =
      match rc with
      | NotRec ->
          Result.List1.iter (f2 env) defns >>= fun () ->
          Ok(Env.addVars b env)
      | Rec ->
          let env = Env.addVars b env
          Result.List1.iter (f2 env) defns >>= fun () ->
          Ok env
    level <- level - 1
    result >>= fun env ->
    for _, ty in Map.toSeq b do
      generalise ty
    Ok env

  let rec inferStatement env stmt =
    match stmt with
    | SLet(rc, defns) ->
        inferLet env rc defns >>= fun env ->
        Ok env
    | SUnion(rc, retTypeName, constructors) ->
        let f env ((constrName, pos as constr), argTy) =
          let tyVars, retTy = typeOfTypeName retTypeName
          Result.Option.map (typeOfTypeExpr env tyVars pos) argTy >>= fun argTy ->
          level <- level - 1
          Option.iter generalise argTy
          generalise retTy
          level <- level + 1
          let env = Env.addConstructor constr argTy retTy env
          let ty =
            match argTy with
            | None -> retTy
            | Some argTy -> TArrow(argTy, retTy)
          typeOfPos.[pos] <- ty
          Ok(Env.addVar constrName ty env)
        match rc with
        | NotRec ->
            Result.List1.fold f env constructors >>= fun env ->
            Ok(Env.addType retTypeName env)
        | Rec ->
            let env = Env.addType retTypeName env
            Result.List1.fold f env constructors >>= Ok
    | SModule(name, stmts) ->
        let env = Env.startModule env
        inferStatements env stmts >>= fun env ->
        Ok(Env.endModule name env)
  and inferStatements env stmts =
    match stmts with
    | [] -> Ok env
    | (stmt, _)::stmts ->
        inferStatement env stmt >>= fun env ->
        inferStatements env stmts

  let result = inferStatements env stmts
  for pos, ty in [for KeyValue(pos, ty) in typeOfPos -> pos, subst ty] do
    typeOfPos.[pos] <- subst ty
  result
