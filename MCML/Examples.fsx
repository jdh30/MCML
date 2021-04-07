type Bool = True | False
type Comparison = Less | Equal | Greater
type Option a = None | Some a
type Result a b = Ok a | Error b

let bitwiseAnd _ _ = 0
let bitwiseXor _ _ = 0
let id x = x
let (¬) = [True -> False | False -> True]
let compare f g = $compare f g |> [-1 -> Less | 0 -> Equal | 1 -> Greater]
let (<) f g = compare f g |> [Less -> True | _ -> False]
let (<=) f g = compare f g |> [Less | Equal -> True | _ -> False]
let (=) f g = compare f g |> [Equal -> True | _ -> False]
let (<>) f g = ¬f=g
let (>=) f g = ¬f<g
let (>) f g = ¬f<=g
let if p t f = p |> [True -> t | False -> f]
let min a b = if (a <= b) a b
let max a b = if (a >= b) a b
let minBy p a b = if (p a <= p b) a b
let maxBy p a b = if (p a >= p b) a b

module Generic {
  (* Generic init in terms of fold. *)
  let init unfold n f =
    unfold [i -> i<n |> [True -> Some(f i, i+1) | False -> None]] 0

  (* Generic iter in terms of fold. *)
  let iter fold f xs = fold [() -> [x -> f x]] () xs
}

(* On-demand sequences. *)
module Seq {
  type rec SeqAux a = Empty | More(a, (() -> SeqAux a))
  type Seq a = Seq(() -> SeqAux a)

  let empty = Seq[() -> Empty]

  let apply onEmpty onMore xs =
    xs() |>
    [ Empty -> onEmpty()
    | More(x, xs) -> onMore(x, xs) ]

  let tryDecapitate (Seq xs) =
    apply [() -> None] [x, xs -> Some(x, Seq xs)] xs

  let prepend x (Seq xs) = Seq[() -> More(x, xs)]

  let singleton x = prepend x empty

  let rec concatAux xs0 xs1 () =
    apply xs1 [x0, xs0 -> More(x0, concatAux xs0 xs1)] xs0

  let concat (Seq xs0) (Seq xs1) = Seq(concatAux xs0 xs1)

  let rec unfoldAux f a () =
    f a |>
    [ None -> Empty
    | Some(x, a) -> More(x, unfoldAux f a) ]

  let unfold f a = Seq(unfoldAux f a)

  let init = Generic.init unfold

  let rec mapAux f xs () =
    apply [() -> Empty] [x, xs -> More(f x, mapAux f xs)] xs

  let map f (Seq xs) = Seq(mapAux f xs)

  let rec foldAux f a xs =
    apply [() -> a] [x, xs -> foldAux f (f a x) xs] xs

  let fold f a (Seq xs) = foldAux f a xs

  let rec fold2Aux f a xs ys =
    (xs(), ys()) |>
    [ Empty, _ | _, Empty -> a
    | More(x, xs), More(y, ys) -> fold2Aux f (f a x y) xs ys ]

  let fold2 f a (Seq xs) (Seq ys) = fold2Aux f a xs ys

  let rec truncateAux n xs () =
    n |>
    [ 0 -> Empty
    | n -> apply [() -> Empty] [x, xs -> More(x, truncateAux (n-1) xs)] xs ]

  let truncate n (Seq xs) = Seq(truncateAux n xs)

  let rec filterAux p xs =
    let f (x, xs) = p x |> [ True -> More(x, xs) | False -> filterAux p xs ] in
    apply [() -> Empty] f xs

  let filter p (Seq xs) = Seq[() -> filterAux p xs]
}

(* Linked list. *)
module List {
  type rec List a = Nil | Cons(a, List a)

  let empty = Nil
    
  let tryHeadTail = [Nil -> None | Cons(x, xs) -> Some(x, xs)]

  let rec unfold f a =
    f a |>
    [ None -> Nil
    | Some(x, a) -> Cons(x, unfold f a) ]

  let init = Generic.init unfold

  let rec map f =
    [ Nil -> Nil
    | Cons(x, xs) -> Cons(f x, map f xs) ]

  let rec fold f a =
    [ Nil -> a
    | Cons(x, xs) -> fold f (f a x) xs ]

  let toSeq = Seq.unfold tryHeadTail
      
  let rec ofSeqAux xs =
    xs() |>
    [ Seq.Empty -> Nil
    | Seq.More(x, xs) -> Cons(x, ofSeqAux xs) ]

  let ofSeq (Seq.Seq xs) = ofSeqAux xs
}

(* Weight-balanced binary tree. *)
(* TODO:

Can we make Map.keys take O(1)?
*)
module BBT {
  type rec BBT a = L | B(Int, BBT a, a, BBT a)

  let empty = L

  let count = [L -> 0 | B(n, _, _, _) -> n]

  let rec tryFind cmpk =
    [ L -> None
    | B(_, l, v, r) ->
        cmpk v |>
        [ Less -> tryFind cmpk l
        | Equal -> Some v
        | Greater -> tryFind cmpk r ] ]

  let rotateRight b =
    [ L, v, r -> b(L, v, r)
    | B(_, ll, lv, L), v, r -> b(ll, lv, b(L, v, r))
    | B(_, ll, lv, B(_, lrl, lrv, lrr)), v, r -> b(b(ll, lv, lrl), lrv, b(lrr, v, r)) ]

  let rotateLeft b =
    [ l, v, L -> b(l, v, L)
    | l, v, B(_, L, rv, rr) -> b(b(l, v, L), rv, rr)
    | l, v, B(_, B(_, rll, rlv, rlr), rv, rr) -> b(b(l, v, rll), rlv, b(rlr, rv, rr)) ]

  let rec b(l, v, r) =
    let ln, rn = count l, count r in
    (2*ln+1 < rn, ln > 2*rn+1) |>
    [ True, _ -> rotateLeft b (l, v, r)
    | _, True -> rotateRight b (l, v, r) 
    | _ -> B(ln+1+rn, l, v, r) ]

  let rec apply cmpx onEmpty onFound =
    [ L -> onEmpty()
    | B(_, l, v, r) ->
        cmpx v |>
        [ Less -> b(apply cmpx onEmpty onFound l, v, r)
        | Equal -> onFound (l, v, r)
        | Greater -> b(l, v, apply cmpx onEmpty onFound r) ] ]

  let insert cmp x = apply cmp [() -> b(L, x, L)] b

  let rec merge =
    [ L, t | t, L -> t
    | (B(ln, ll, lv, lr) as l), (B(rn, rl, rv, rr) as r) ->
        ln > rn |>
        [ True -> b(ll, lv, merge(lr, r))
        | False -> b(merge(l, rl), rv, rr) ] ]

  let delete cmp = apply cmp [() -> L] [(l, _, r) -> merge (l, r)]

  let rec fold f a =
    [ L -> a
    | B(_, l, v, r) -> fold f (f (fold f a l) v) r ]

  let rec up =
    [ L -> Seq.empty
    | B(_, l, v, r) -> Seq.concat (up l) (Seq.prepend v (up r)) ]

  let rec down =
    [ L -> Seq.empty
    | B(_, l, v, r) -> Seq.concat (down r) (Seq.prepend v (down l)) ]

  let rec split cmp x =
    [ L -> L, None, L
    | B(_, l, v, r) ->
        cmp x v |>
        [ Less -> split cmp x l |> [ ll, lv, lr -> ll, lv, b(lr, v, r) ]
        | Equal -> l, Some v, r
        | Greater -> split cmp x r |> [ rl, rv, rr -> b(l, v, rl), rv, rr ] ] ]

  let rec union cmp s1 s2 =
    let add x = insert (cmp x) x in
    let rec union =
      [ L, s | s, L -> s
      | B(_, L, v, L), s | s, B(_, L, v, L) -> add v s
      | (B(ln, ll, lv, lr) as l), (B(rn, rl, rv, rr) as r) ->
          compare ln rn |>
          [ Less ->
              split cmp lv r |>
              [ rl, _, rr -> b(union(ll, rl), lv, union(lr, rr)) ]
          | _ ->
              split cmp rv l |>
              [ ll, _, lr -> b(union(ll, rl), rv, union(lr, rr)) ] ] ] in
    union(s1, s2)

  let rec intersection cmp s1 s2 =
    let add x = insert (cmp x) x in
    let rec i =
      [ L, _ | _, L -> L
      | (B(ln, ll, lv, lr) as l), (B(rn, rl, rv, rr) as r) ->
          compare ln rn |>
          [ Less ->
              split cmp lv r |>
              [ rl, None, rr -> union cmp (i(ll, rl)) (i(lr, rr))
              | rl, Some _, rr -> b(i(ll, rl), lv, i(lr, rr)) ]
          | _ ->
              split cmp rv l |>
              [ ll, None, lr -> union cmp (i(ll, rl)) (i(lr, rr))
              | ll, Some _, lr -> b(i(ll, rl), rv, i(lr, rr)) ] ] ] in
    i(s1, s2)
}

module Set {
  type Set a = Set BBT.BBT a
  let empty = Set BBT.empty
  let count (Set s) = BBT.count s
  let add x (Set s) = Set(BBT.insert (compare x) x s)
  let remove x (Set s) = Set(BBT.delete (compare x) s)
  let contains x (Set s) =
    BBT.tryFind (compare x) s |> [None -> False | Some _ -> True]
  let fold f a (Set s) = BBT.fold f a s
  let up (Set s) = BBT.up s
  let down (Set s) = BBT.down s
  let split x (Set s) = BBT.split compare x s |> [l, v, r -> Set l, v, Set r]
  let union (Set s1) (Set s2) = Set(BBT.union compare s1 s2)
  let intersection (Set s1) (Set s2) = Set(BBT.intersection compare s1 s2)
  let iter = Generic.iter fold
  let ofSeq xs = Seq.fold [s -> [x -> add x s]] empty xs
  let singleton x = add x empty
}

module Map {
  type Map k v = Map BBT.BBT (k, v)
  let empty = Map BBT.empty
  let add k v (Map d) = Map(BBT.insert [k2, _ -> compare k k2] (k, v) d)
  let remove k (Map d) = Map(BBT.delete [k2, _ -> compare k k2] d)
  let tryFind k (Map d) =
    BBT.tryFind [k2, _ -> compare k k2] d |>
    [None -> None | Some(_, v) -> Some v]
  let fold f a (Map d) = BBT.fold [a -> [k, v -> f a k v]] a d
  let iter = Generic.iter fold
  let ofSeq xs = Seq.fold [s -> [k, v -> add k v s]] empty xs
  let up (Map s) = BBT.up s
  let down (Map s) = BBT.down s
}

module ComputationalGeometry {
  let sub (x0, y0) (x1, y1) = x0-x1, y0-y1

  let cross (x0, y0) (x1, y1) =
    x0*y1 - y0*x1

  let rec hsplit ps p1 p2 =
    let dist p = cross (sub p1 p) (sub p2 p) in
    let ps = Seq.filter [p -> dist p > 0] ps in
    Seq.tryDecapitate ps |>
    [ None -> Seq.singleton p1
    | Some(p, ps2) ->
        let pm = Seq.fold (maxBy dist) p ps2 in
        Seq.concat (hsplit ps p1 pm) (hsplit ps pm p2) ]

  let quickHull points =
    Seq.tryDecapitate points |>
    [ None -> Seq.empty
    | Some(p, ps) ->
        let x (x, _) = x in
        let minx = Seq.fold (minBy x) p points in
        let maxx = Seq.fold (maxBy x) p points in
        Seq.concat (hsplit points minx maxx) (hsplit points maxx minx) ]
}

let fibs =
  Seq.unfold [a, b -> Some(a, (b, a+b))] (0, 1)
  |> Seq.truncate 10
  |> Seq.fold [t -> [x -> Set.add x t]] Set.empty

let lower = Seq.init 5 [x -> x] |> Set.ofSeq
let upper = Seq.init 5 [x -> x+2] |> Set.ofSeq
let both = Set.union lower upper |> Set.up |> List.ofSeq

let ps =
  Seq.init 10 [x -> x%5, x]
  |> ComputationalGeometry.quickHull
  |> List.ofSeq

let rec nth nn i =
  [ 0 -> Set.singleton i
  | 1 -> nn i
  | n ->
      let s0 = nth nn i (n-2) in
      let s1 = nth nn i (n-1) in
      let s2 = Set.fold [s -> [i -> Set.union s (nn i)]] Set.empty s1 in
      s2 ]

let manhattan (x, y) =
  Set.empty
  |> Set.add (x-1, y)
  |> Set.add (x+1, y)
  |> Set.add (x, y-1)
  |> Set.add (x, y+1)

let ps = nth manhattan (0, 0) 4

module PATRICIA {
  type rec T =
      Leaf Int
    | Branch(Int, Int, (T, T))

  let empty = None

  let isEmpty = [None -> True | Some _ -> False]

  let singleton k = Some(Leaf k)

  let zeroBit k m =
    bitwiseAnd k m = 0

  let zeroBitPick k m l r =
    zeroBit k m |>
    [ True -> l | False -> r ]

  let zeroBitApply k m f t0 t1 =
    zeroBit k m |>
    [ True -> f t0, t1
    | False -> t0, f t1 ]

  let rec containsAux k =
    [ Leaf j -> k = j
    | Branch (_, m, (l, r)) -> containsAux k (zeroBitPick k m l r) ]

  let containsAuxPick k s t f =
    containsAux k s |>
    [ True -> t | False -> f ]

  let contains k =
    [ None -> False
    | Some t -> containsAux k t ]

  let lowestBit x = bitwiseAnd x (-x)

  let branchingBit p0 p1 = lowestBit (bitwiseXor p0 p1)

  let mask p m = bitwiseAnd p (m - 1)

  let join (p0, t0, p1, t1) =
    let m = branchingBit p0 p1 in
    Branch(mask p0 m, m, zeroBitPick p0 m (t0, t1) (t1, t0))

  let matchPrefix k p m =
    mask k m = p

  let rec addAux k =
    [ Leaf j as t ->
        j = k |>
        [ True -> t
        | False -> join(k, Leaf k, j, t) ]
    | Branch(p, m, (t0, t1)) as t ->
        matchPrefix k p m |>
        [ True -> Branch (p, m, zeroBitApply k m (addAux k) t0 t1)
        | False -> join (k, Leaf k, p, t) ] ]

  let add k =
    [ None -> Leaf k
    | Some t -> addAux k t ]
    |> Some

  let rec removeAux k =
    [ Leaf j as t -> k = j |> [True -> None | False -> Some t]
    | Branch(p, m, (t0, t1)) as t ->
        matchPrefix k p m |>
        [ True ->
            zeroBit k m |>
            [ True ->
                removeAux k t0 |>
                [ None -> t1
                | Some t0 -> Branch(p, m, (t0, t1)) ]
            | False ->
                removeAux k t1 |>
                [ None -> t0
                | Some t1 -> Branch(p, m, (t0, t1)) ] ]
        | False -> t ]
        |> Some ]

  let remove k =
    [ None -> None
    | Some t -> removeAux k t ]

  type Overlap = Lower | Same | Upper | Distinct

  let overlapOf p1 p2 m1 m2 =
    (compare m1 m2, p1=p2, matchPrefix p2 p1 m1, matchPrefix p1 p2 m2) |>
    [ Less, _, True, _ -> Lower
    | Equal, True, _, _ -> Same
    | Greater, _, _, True -> Upper
    | _ -> Distinct ]

  let rec unionAux =
    [ Leaf k, t | t, Leaf k -> addAux k t
    | (Branch(p, m, (s0, s1)) as s), (Branch(q, n, (t0, t1)) as t) ->
        overlapOf p q m n |>
        [ Lower -> Branch(p, m, zeroBitApply q m [s -> unionAux(s, t)] s0 s1)
        | Same -> Branch(p, m, (unionAux(s0, t0), unionAux(s1, t1)))
        | Upper -> Branch(q, n, zeroBitApply p n [t -> unionAux(s, t)] t0 t1)
        | Distinct -> join(p, s, q, t) ] ]

  let union s t =
    (s, t) |>
    [ None, s
    | s, None -> s
    | Some s, Some t -> Some(unionAux(s, t)) ]

  let rec isSubsetAux =
    [ Leaf k, s -> containsAux k s
    | Branch _, Leaf _ -> False
    | Branch(p1, m1, (l1, r1)), Branch(p2, m2, (l2, r2)) ->
        overlapOf p1 p2 m1 m2 |>
        [ Lower | Distinct -> False
        | Same -> isSubsetAux(l1, l2) && isSubsetAux(r1, r2)
        | Upper ->
            let lr2 = zeroBitPick p1 m2 l2 r2 in
            isSubsetAux(l1, lr2) && isSubsetAux(r1, lr2) ] ]

  let isSubset s1 s2 =
    (s1, s2) |>
    [ None, _ -> True
    | _, None -> False
    | Some s1, Some s2 -> isSubsetAux(s1, s2) ]

  let rec intersectAux =
    [ Leaf k, s
    | s, Leaf k -> containsAuxPick k s (singleton k) None
    | (Branch(p1, m1, (l1, r1)) as s1), (Branch(p2, m2, (l2, r2)) as s2) ->
        overlapOf p1 p2 m1 m2 |>
        [ Lower -> intersectAux(zeroBitPick p2 m1 l1 r1, s2)
        | Same -> union (intersectAux(l1, l2)) (intersectAux(r1, r2))
        | Upper -> intersectAux(s1, zeroBitPick p1 m2 l2 r2)
        | Distinct -> None ] ]

  let intersect s1 s2 =
    (s1, s2) |>
    [ _, None
    | None, _ -> None
    | Some s1, Some s2 -> intersectAux(s1, s2) ]

  let differenceAux(a, b) = [() -> a | _ -> b] ()
  let differenceAux =
    [ (Leaf k1 as s1), s2 -> containsAuxPick k1 s2 None (Some s1)
    | s1, Leaf k2 -> removeAux k2 s1
    | (Branch(p1, m1, (l1, r1)) as s1), (Branch(p2, m2, (l2, r2)) as s2) ->
        overlapOf p1 p2 m1 m2 |>
        [ Lower -> unionAux(zeroBitApply p2 m1 [s1 -> differenceAux(s1, s2)] l1 r1)
        | Same -> unionAux(differenceAux(l1, l2), differenceAux(r1, r2))
        | Upper -> differenceAux(s1, zeroBitPick p1 m2 l2 r2)
        | Distinct -> s1 ]
        |> Some ]

  let difference s1 s2 =
    (s1, s2) |>
    [ None, _ -> None
    | s1, None -> s1
    | Some s1, Some s2 -> differenceAux(s1, s2) ]

  let rec countAux =
    [ Leaf _ -> 1
    | Branch(_, _, (t0, t1)) -> countAux t0 + countAux t1 ]

  let count =
    [ None -> 0
    | Some s -> countAux s ]

  let rec foldAux f a =
    [ Leaf n -> f a n
    | Branch(_, _, (s1, s2)) -> foldAux f (foldAux f a s1) s2 ]

  let fold f a =
    [ None -> a
    | Some t -> foldAux f a t ]

  let iter = Generic.iter fold
}
