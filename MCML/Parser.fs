module MCML.Parser

open MCML.Collections
open MCML.AST
open MCML.Errors

type Token =
  | INT of int
  | CHAR of char
  | STRING of string
  | BUILTIN of string
  | LIDENT of string
  | UIDENT of string
  | DOT | COMMA
  | OPEN | CLOSE
  | SQOPEN | SQCLOSE
  | COPEN | CCLOSE | ARROW
  | LT | LE | EQ | NE | GE | GT
  | ADD | SUB | MUL | DIV | MOD
  | NOT | AMPAMP | PIPEPIPE | PIPELINE
  | ANY | AS | PIPE
  | LET | REC | AND | IN
  | TYPE | MODULE
  | PANIC
  | COMMENTSTART | COMMENTEND

let (>>=) = Result.(>>=)

let symbols =
  [ COMMA, ","; DOT, ".";
    OPEN, "("; CLOSE, ")";
    SQOPEN, "["; SQCLOSE, "]";
    COPEN, "{"; CCLOSE, "}";
    LT, "<"; LE, "<="; EQ, "="; NE, "<>"; GE, ">="; GT, ">";
    ADD, "+"; SUB, "-"; MUL, "*"; DIV, "/"; MOD, "%";
    NOT, "¬"; AMPAMP, "&&"; PIPEPIPE, "||"; PIPELINE, "|>";
    ANY, "_";
    ARROW, "->";
    PIPE, "|";
    COMMENTSTART, "(*"; COMMENTEND, "*)" ]
  |> List.sortBy (fun (_, s) -> -s.Length)

let keywords =
  [ AS, "as";
    LET, "let"; REC, "rec"; AND, "and"; IN, "in";
    TYPE, "type";
    MODULE, "module";
    PANIC, "panic" ]

let stringOfToken =
  let d = dict(symbols @ keywords)
  fun token ->
    match token with
    | INT n -> string n
    | CHAR c -> string c
    | LIDENT s | UIDENT s -> s
    | token -> d.[token]

let lower = set['a'..'z']
let upper = set['A'..'Z']
let digit = set['0'..'9']
let alphanum = lower + upper + digit
let ws = set[' '; '\r'; '\n'; '\t']

let next (s: string, i) =
  if i >= s.Length then None else
    Some(s.[i], (s, i+1))

let substring (s: string, i) (_, j) = s.[i..j-1]

let startsWith (s: string, i) (prefix: string) =
  i + prefix.Length <= s.Length &&
    s.Substring(i, prefix.Length) = prefix

let rec skipWhile (alphabet: Set<char>) it =
  match next it with
  | Some(c, it) when alphabet.Contains c -> skipWhile alphabet it
  | _ -> it

let rec skipUntil (prefix: string) (s: string, i as it) =
  if i + prefix.Length > s.Length then None
  elif startsWith it prefix then Some(s, i + prefix.Length) else
    skipUntil prefix (s, i+1)

/// If a result is successful then apply the continuation k to it.
let apply f k it =
  match f it with
  | Ok(v, s) -> k v s
  | Error x -> Error x

/// If a lowercase identifier is a keyword then return its token
/// otherwise return it as an LIDENT.
let tokenOfLident s =
  let picker (k, ks) = if s=ks then Some k else None
  match Seq.tryPick picker keywords with
  | Some token -> token
  | None -> LIDENT s

/// Lex a string and start index into either a list of tokens and their positions
/// in the string or the position of a lexical error.
let rec lex it1 : Result<(Token * Pos) list * _, _> =
  match next it1 with
  | None -> Ok([], it1)
  | Some(c, it) when ws.Contains c -> lex it
  | Some(''', it) ->
      match next it with
      | Some(c, it) ->
          match next it with
          | Some(''', it2) -> emit (CHAR(c)) it1 it2
          | _ -> Error(UnexpectedInput, it)
      | _ -> Error(UnexpectedInput, it)
  | Some(c, it2) when digit.Contains c ->
      let it2 = skipWhile digit it2
      emit (INT(int(substring it1 it2))) it1 it2
  | Some(c, it2) when upper.Contains c ->
      let it2 = skipWhile alphanum it2
      emit (UIDENT(substring it1 it2)) it1 it2
  | Some('$', it2) ->
      let it2 = skipWhile alphanum it2
      emit (BUILTIN(substring it1 it2)) it1 it2
  | Some(c, it2) when lower.Contains c || c='$' ->
      let it2 = skipWhile alphanum it2
      emit (tokenOfLident(substring it1 it2)) it1 it2
  | Some('"', it2) -> lexString it2 it2
  | _ ->
      match Seq.tryFind (snd >> startsWith it1) symbols with
      | None -> Error(UnexpectedInput, it1)
      | Some(COMMENTSTART, str) ->
          lexComment 1 (fst it1, snd it1 + str.Length)
      | Some(token, str) ->
          let it2 = fst it1, snd it1 + str.Length
          emit token it1 it2
/// Lex a string literal.
and lexString it1 it2 =
  match next it2 with
  | None -> Error(EndOfInputInsideString, it2)
  | Some('"', it3) -> emit (STRING(substring it1 it2)) it1 it3
  | Some('\\', it2) ->
      match next it2 with
      | None -> Error(EndOfInputInsideString, it2)
      | Some(_, it2) -> lexString it1 it2
  | Some(_, it2) -> lexString it1 it2
and lexComment depth it1 =
  match Seq.tryFind (snd >> startsWith it1) symbols, next it1 with
  | Some(COMMENTSTART, str), _ ->
      let it2 = fst it1, snd it1 + str.Length
      lexComment (depth+1) it2
  | Some(COMMENTEND, str), _ ->
      (fst it1, snd it1 + str.Length)
      |> if depth=1 then lex else lexComment (depth-1)
  | None, None -> Error(EndOfInputInsideComment, it1)
  | None, Some(_, it1) -> lexComment depth it1
  | Some(_, str), _ -> lexComment depth (fst it1, snd it1 + str.Length)

/// Emit a token between positions it1 and it2.
and emit t it1 it2 =
  apply lex (fun ts s ->
    Ok((t, { Start=snd it1; End=snd it2 })::ts, s)) it2

/// Expect the given token, returning a failure result if it is not present.
let expect token ts =
  match ts with
  | (t, _ as h)::ts when t=token -> Ok(h, ts)
  | ts -> Error(Expected(stringOfToken token), ts)

/// Calculate a range of input spanning the two given positions.
let union (_, p1) (_, p2) =
  { Start = min p1.Start p2.Start; End = max p1.End p2.End }

/// Calculate a range of input spanning the given list of ranges.
let unions1 (_, p) fs =
  List.fold (fun p f -> union ((), p) f) p fs

/// Apply parser p1 and then parser p2 returning success only if
/// both parsers succeed.
let bind p1 p2 =
  apply p1 (fun v1 ->
    apply p2 (fun v2 ts ->
      Ok((v1, v2), ts)))

/// Parse with p1 and then p2 and then apply the continuation k to
/// the two results.
let apply2 p1 p2 k =
  apply (bind p1 p2) (fun (v1, v2) -> k (v1, v2))

let apply3 p1 p2 p3 k =
  apply (bind p1 (bind p2 p3)) (fun (v1, (v2, v3)) -> k (v1, v2, v3))

let apply4 p1 p2 p3 p4 k =
  apply (bind (bind p1 p2) (bind p3 p4)) (fun ((v1, v2), (v3, v4)) ->
    k (v1, v2, v3, v4))

let rec starAux p ts =
  match p ts with
  | Ok(x, ts) ->
      let xs, ts = starAux p ts
      x::xs, ts
  | Error _ -> [], ts

/// Kleene star: match zero or more repetitions of parser p.
let star p ts = Ok(starAux p ts)

let rec starThen p tok ts =
  match p ts, ts with
  | Ok(x, ts), _ ->
      apply (starThen p tok) (fun (xs, last) ts ->
        Ok((x::xs, last), ts)) ts
  | Error _, (tok2, _ as last)::ts when tok=tok2 -> Ok(([], last), ts)
  | Error(msg, ts), _ -> Error(msg, ts)

/// Match one or more repetitions of parser p returning a pair of the
/// first value and list of subsequent values.
let plus p = bind p (star p)

let rec list0 p sep ts =
  match p ts with
  | Ok(x, ts) ->
      apply (star (bind (expect sep) p)) (fun cxs ts ->
        Ok(x::List.map snd cxs, ts)) ts
  | Error _ -> Ok([], ts)

/// Parse a list using parser p to parse each element and expecting
/// the token sep between consecutive elements.
let list1 p sep =
  apply2 p (star (bind (expect sep) p)) (fun (x, xs) ts ->
    Ok((x, List.map snd xs), ts))

/// Given a map from tokens to strings, parse any of the tokens and
/// return its associated string with the position of the token.
// This function is always wrapped in a star so the error never escapes.
let parseMap ops ts =
  match ts with
  | (token, p)::ts ->
      match Map.tryFind token ops with
      | None -> Error(Dummy, ts)
      | Some v -> Ok((v, p), ts)
  | ts -> Error(Dummy, ts)

/// Parse with parser "parse" a sequence of left associative operators
/// given in the Map "ops".
let pLeftAssoc parse ops fn =
  apply2 parse (star (bind (parseMap (Map ops)) parse)) (fun (f, opgs) ts ->
    Ok(List.fold fn f opgs, ts))

let pLeftAssocBuiltIn parse ops =
  pLeftAssoc parse ops (fun f ((op, _), g) -> EBinOp(f, op, g), union f g)

let pLeftAssocFn parse ops =
  let fn f ((op, pop), g) =
    let op = EVar([], (op, pop)), pop      
    EApply((EApply(op, f), union f op), g), union f g
  pLeftAssoc parse ops fn

/// Parse an optional "rec" keyword.
let parseRec ts =
  match ts with
  | (REC, _)::ts -> Ok(Rec, ts)
  | ts -> Ok(NotRec, ts)

/// Parse an identifier.
let parseIdent ts =
  match ts with
  | ((LIDENT x | UIDENT x), p)::ts -> Ok((x, p), ts)
  | ts -> Error(Expected "identifier", ts)

/// Parse a lowercase identifier.
let parseLIdent ts =
  match ts with
  | (LIDENT s, p)::ts -> Ok((s, p), ts)
  | ts -> Error(Expected "lowercase identifier", ts)

/// Parse an uppercase identifier.
let parseUIdent ts =
  match ts with
  | (UIDENT s, p)::ts -> Ok((s, p), ts)
  | ts -> Error(Expected "uppercase identifier", ts)

/// Parse a sequence of zero or more uppercase identifiers followed by
/// dots.
let parsePathPrefix ts =
  apply (star (bind parseUIdent (expect DOT))) (fun prefix ts ->
    Ok(List.map fst prefix, ts)) ts

/// Desugar "fun x y z -> e" into "fun x -> fun y -> fun z -> e".
let rec desugarBinding patts body =
  match patts with
  | [] -> body
  | patt::patts -> EFunction((patt, desugarBinding patts body), []), union patt body

/// Parse a comma-separated list.
let parseCSL parse f =
  apply (list1 parse COMMA) (fun (e, es) ts ->
    Ok((match es with [] -> e | es -> f (e::es), unions1 e es), ts))

/// Parse literals, identifiers, bracketed expressions, let-bindings, lambda
/// functions and match expressions.
let rec parseAtom ts =
  match ts with
  | (INT n, p)::ts -> Ok((EInt n, p), ts)
  | (CHAR c, p)::ts -> Ok((EChar c, p), ts)
  | (STRING s, p)::ts -> Ok((EString s, p), ts)
  | (LIDENT "panic", p)::ts -> Ok((EPanic, p), ts)
  | (LIDENT "print", p)::ts -> Ok((EPrint, p), ts)
  | (BUILTIN "$compare", p)::ts ->
      apply2 parseAtom parseAtom (fun (f, g) ts ->
        Ok((EBinOp(f, Compare, g), p), ts)) ts
  | ((LIDENT _ | UIDENT _), _)::_ as ts ->
      apply2 parsePathPrefix parseIdent (fun (path, var) ts ->
        Ok((EVar(path, var), unions1 var path), ts)) ts
  | (SQOPEN, _ as t1)::ts ->
      apply2 parseMatchCases (expect SQCLOSE) (fun (cases, tn) ts ->
        Ok((EFunction cases, union t1 tn), ts)) ts
  | (OPEN, _ as t1)::(CLOSE, _ as t2)::ts -> Ok((ETuple[], union t1 t2), ts)
  | (OPEN, _)::ts ->
      apply2 parseExpr (expect CLOSE) (fun (f, _) ts -> Ok(f, ts)) ts
  | (LET, _ as tLet)::ts ->
      apply4 parseRec parseLetBindings (expect IN) parseExpr
        (fun (rc, bindings, _, rest) ts ->
          Ok((ELetIn(rc, bindings, rest), union tLet rest), ts)) ts
  | ts -> Error(Expected "expression", ts)
/// Parse whitespace-separated expressions as function application.
and parseApply =
  apply (plus parseAtom) (fun (f, gs) ts ->
    Ok(List.fold (fun f g -> EApply(f, g), union f g) f gs, ts))
/// Parse the unary negation operator.
and parseNegate ts =
  match ts with
  | (SUB, _ as token)::ts ->
      apply parseNegate (fun f ts ->
        Ok((EUnOp(Num1 Neg, f), union token f), ts)) ts
  | ts -> parseApply ts
/// Parse a sequence of one or more factors separated by multiplication,
/// division or modulus operators.
and parseFactor = pLeftAssocBuiltIn parseNegate [MUL, Num2 Mul; DIV, Num2 Div; MOD, Num2 Mod]
/// Parse a sequence of one or more terms separated by addition or
/// subtraction operators.
and parseTerm = pLeftAssocBuiltIn parseFactor [ADD, Num2 Add; SUB, Num2 Sub]
/// Parse a sequence of one or more terms separated by comparison operators.
and parseCmp =
  pLeftAssocFn parseTerm [LT, "<"; LE, "<="; EQ, "="; NE, "<>"; GE, ">="; GT, ">"]
and parseNot ts =
  match ts with
  | (NOT, pop as token)::ts ->
      apply parseNot (fun f ts ->
        let op = EVar([], ("¬", pop)), pop
        Ok((EApply(op, f), union token f), ts)) ts
  | ts -> parseCmp ts
/// Parse a sequence of one or more terms separated by logical operators.
and parseLogic = pLeftAssocBuiltIn parseNot [AMPAMP, Bool2 And; PIPEPIPE, Bool2 Or]
and parsePipeline ts =
  apply (list1 parseLogic PIPELINE) (fun (f, fs) ts ->
    Ok(List.fold (fun f g -> EBinOp(f, PipeLine, g), union f g) f fs, ts)) ts
/// Parse a sequence of one or more comma separated expressions.
and parseTuple = parseCSL parsePipeline ETuple
/// Parse an expression.
and parseExpr = parseTuple
/// Parse the remainder of a let-binding after the "let" and "rec" tokens,
/// such as "f x = x".
and parseLetBinding ts = (* f x = x, x *)
  apply3 (plus parsePattTuple) (expect EQ) parseExpr
    (fun ((patt, patts), _, body) ts -> Ok((patt, desugarBinding patts body), ts)) ts
/// Parse a sequence of let bindings separated by the "and" keyword.
and parseLetBindings = (* f x = x, x and g x = f x *)
  apply (list1 parseLetBinding AND) (fun bs ts -> Ok(bs, ts))
/// Parse literal, variable and tuple patterns.
and parsePattAtom ts =
  match ts with
  | (INT n, p)::ts -> Ok((PInt n, p), ts)
  | (SUB, _ as tok1)::(INT n, _ as tok2)::ts -> Ok((PInt -n, union tok1 tok2), ts)
  | (STRING s, p)::ts -> Ok((PString s, p), ts)
  | (ANY, p)::ts -> Ok((PAny, p), ts)
  | (LIDENT s, p)::ts -> Ok((PVar s, p), ts)
  | (OPEN, _ as t1)::(LT|LE|EQ|NE|GE|GT|NOT as op, _)::(CLOSE, _ as t3)::ts ->
      Ok((PVar(stringOfToken op), union t1 t3), ts)
  | (OPEN, _ as t1)::(CLOSE, _ as t2)::ts -> Ok((PTuple[], union t1 t2), ts)
  | (OPEN, _)::ts ->
      apply2 parsePatt (expect CLOSE) (fun (f, _) ts -> Ok(f, ts)) ts
  | ts -> Error(Expected "pattern", ts)
/// Parse whitespace-separated patterns as union type constructors.
and parsePattApply ts =
  match bind parsePathPrefix parseUIdent ts with
  | Ok((mdls, (_, p as name) as caseName), ts) ->
      match parsePattAtom ts with
      | Ok(arg, ts) -> Ok((PUnion(caseName, Some arg), unions1 arg (name::mdls)), ts)
      | Error _ -> Ok((PUnion(caseName, None), p), ts)
  | Error _ -> parsePattAtom ts
/// Parse comma-separated patterns as a tuple.
and parsePattTuple = parseCSL parsePattApply PTuple
/// Parse pipe-separated patterns as or-patterns.
and parsePattOrs =
  apply (list1 parsePattTuple PIPE) (fun (p, ps) ts ->
    Ok((List.fold (fun p1 p2 -> POr(p1, p2), union p1 p2) p ps), ts))
/// Parse an as-pattern.
and parsePattAs =
  apply parsePattOrs (fun patt ts ->
    match ts with
    | (AS, _)::(LIDENT name, p)::ts ->
        let name = name, p
        Ok((PAs(patt, name), union patt name), ts)
    | ts -> Ok(patt, ts))
/// Parse a pattern.
and parsePatt = parsePattAs
/// Parse a match case of the form "pattern -> expression".
and parseMatchCase =
  apply3 parsePatt (expect ARROW) parseExpr
    (fun (patt, _, action) ts -> Ok((patt, action), ts))
/// Parse a sequence of pipe-separated match cases.
and parseMatchCases ts =
  apply (list1 parseMatchCase PIPE) (fun x ts -> Ok(x, ts)) ts

/// Parse an atomic type expression.
let rec parseTypeAtom ts =
  match ts with
  | (LIDENT x, pos)::ts -> Ok((TEParam x, pos), ts)
  | (OPEN, _ as tok1)::(CLOSE, _ as tok2)::ts -> Ok((TETuple[], union tok1 tok2), ts)
  | (OPEN, _)::ts ->
      apply2 parseTypeExpr (expect CLOSE) (fun (ty, _) ts -> Ok(ty, ts)) ts
  | ts -> Error(Expected "type expression", ts)
and parseTypeApply ts =
  match ts with
  | (LIDENT x, pos)::ts -> Ok((TEParam x, pos), ts)
  | (UIDENT _, _ as first)::_ as ts ->
      apply3 parsePathPrefix parseUIdent (star parseTypeAtom) (fun (path, name, args) ts ->
        let (_, last), None | _, Some(_, last) = name, List.tryLast args
        match path, name with
        | [], ("Int", pos) -> Ok((TEInt, pos), ts)
        | [], ("String", pos) -> Ok((TEString, pos), ts)
        | _ -> Ok((TERef((path, name), args), union first ((), last)), ts)) ts
  | ts -> parseTypeAtom ts
/// Parse a sequence of comma-separated type expressions as a tuple type.
and parseTypeTuple =
  apply (list1 parseTypeApply COMMA) (fun (ty, tys) ts ->
    Ok((TETuple(ty::tys), unions1 ty tys), ts))
/// Parse "a -> b" as a function type.
and parseTypeArrow ts =
  apply parseTypeTuple (fun ty1 ts ->
    match ts with
    | (ARROW, _)::ts ->
        apply parseTypeArrow (fun ty2 ts ->
          Ok((TEArrow(ty1, ty2), union ty1 ty2), ts)) ts
    | ts -> Ok(ty1, ts)) ts
/// Parse a type expression.
and parseTypeExpr = parseTypeArrow

/// Parse a let, type or module definition.
let rec parseStatement ts =
  match ts with
  | (LET, _ as token)::ts ->
      apply2 parseRec parseLetBindings (fun (rc, bindings) ts ->
        let _, expr = List1.last bindings
        Ok((SLet(rc, bindings), union token expr), ts)) ts
  | (TYPE, _ as first)::ts ->
      let rc, ts =
        match ts with
        | (REC, _)::ts -> Rec, ts
        | ts -> NotRec, ts
      apply4 parseUIdent (star parseLIdent) (expect EQ) (list1 parseUnionCaseTypeDefinition PIPE)
        (fun (name, args, _, cases) ts ->
          let ((_, last), None | _, Some(_, last)) = List1.last cases
          Ok((SUnion(rc, (name, args), cases), union first ((), last)), ts)) ts
  | (MODULE, _ as first)::(UIDENT name, pName)::(COPEN, _)::ts ->
      apply (starThen parseStatement CCLOSE) (fun (stmts, last) ts ->
        Ok((SModule((name, pName), stmts), union first last), ts)) ts
  | ts -> Error(Expected "let, type or module", ts)
/// Parse the definition of a union case, e.g. "Some a".
and parseUnionCaseTypeDefinition ts =
  match ts with
  | (UIDENT name, p0)::ts ->
      match parseTypeExpr ts with
      | Ok(arg, ts) -> Ok(((name, p0), Some arg), ts)
      | Error _ -> Ok(((name, p0), None), ts)
  | ts -> Error(Expected "algebraic type definition", ts)

/// Parse a sequence of zero or more top-level definitions.
let parseStatements ts =
  apply (star parseStatement) (fun defns ts -> Ok(defns, ts)) ts

/// Parse a whole string into an abstract syntax tree returning
/// either a list of top-level definitions or an error message and
/// location.
let parse s =
  match lex (s, 0) with
  | Error(err, (_, i)) -> Error(err, {Start=i; End=i})
  | Ok(tokens, (s, i)) ->
      if i < s.Length then
        failwithf "Internal error: unparsed input"
      match parseStatements tokens with
      | Ok(_, (_::_ as ts)) ->
          match parseStatement ts with
          | Ok _ -> failwithf "Internal error: parse"
          | Error(msg, (_, p)::_) -> Error(msg, p)
          | Error(msg, []) ->
              let i = s.Length
              Error(msg, {Start=i; End=i})
      | Ok(stmts, []) -> Ok(tokens, stmts)
      | Error(msg, (_, p)::_) -> Error(msg, p)
      | Error(msg, []) ->
          let i = s.Length
          Error(msg, {Start=i; End=i})
