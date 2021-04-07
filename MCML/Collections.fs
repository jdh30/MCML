/// Core collections used by our interpreter.
module MCML.Collections

type 'a list1 = 'a * 'a list

module List1 =
  let singleton x = x, []

  let prepend x0 (x1, xs) = x0, x1::xs

  let last (x, xs) =
    List.tryLast xs
    |> Option.defaultValue x

  let tryPick f (x, xs) =
    match f x with
    | None -> List.tryPick f xs
    | result -> result

  let map f (x, xs) = f x, List.map f xs

  let fold f a (x, xs) = List.fold f (f a x) xs

  let iter f (x, xs) =
    f x
    List.iter f xs

type Dictionary<'K, 'V when 'K: equality> = System.Collections.Generic.Dictionary<'K, 'V>
type HashSet<'T when 'T: equality> = System.Collections.Generic.HashSet<'T>

let dictionary kvs =
  let d = Dictionary HashIdentity.Structural
  for k, v in kvs do
    d.[k] <- v
  d

let hashSet xs =
  let s = HashSet HashIdentity.Structural
  for x in xs do
    ignore(s.Add x)
  s

module HashSet =
  let contains x (s: HashSet<_>) = s.Contains x

module Dictionary =
  let tryFind key (d: Dictionary<_,_>) =
    let mutable value = Unchecked.defaultof<_>
    if d.TryGetValue(key, &value) then Some value else None

  let fold f a d = Seq.fold (fun a (KeyValue(k, v)) -> f a k v) a d

  let add k v (d: Dictionary<_,_>) =
    d.[k] <- v

  let map f (d: Dictionary<_,_>) =
    let d2 = dictionary[]
    for KeyValue(k, v) in d do
      d2.[k] <- f k v
    d2

module Result =
  let (>>=) x k =
    match x with
    | Ok ok -> k ok
    | Error err -> Error err

  module Option =
    let map f o =
      match o with
      | None -> Ok None
      | Some x -> f x >>= (Some >> Ok)

  module Seq =
    let fold f a (xs: seq<_>) =
      use e = xs.GetEnumerator()
      let rec loop a =
        if e.MoveNext() then
          let x = e.Current
          f a x >>= loop
        else Ok a
      loop a

    let rec iter f xs = fold (fun () -> f) () xs

  module List =
    let rec fold f a xs =
      match xs with
      | [] -> Ok a
      | x::xs -> f a x >>= fun a -> fold f a xs

    let rec iter f xs = fold (fun () -> f) () xs

    let rec map f xs =
      match xs with
      | [] -> Ok[]
      | x::xs -> f x >>= fun x -> map f xs >>= fun xs -> Ok(x::xs)

    let rec mapFold f a xs =
      match xs with
      | [] -> Ok([], a)
      | x::xs ->
          f a x >>= fun (x, a) ->
          mapFold f a xs >>= fun (xs, a) ->
          Ok(x::xs, a)

  module List1 =
    let map f (x, xs) = f x >>= fun x -> List.map f xs >>= fun xs -> Ok(x, xs)

    let fold f a (x, xs) =
      f a x >>= fun a -> List.fold f a xs

    let rec iter f xs = fold (fun () -> f) () xs

    let mapFold f a (x, xs) =
      f a x >>= fun (x, a) ->
      List.mapFold f a xs >>= fun (xs, a) ->
      Ok((x, xs), a)

// By Benjamin Hodgson from https://stackoverflow.com/a/49681264/11210638
module rec Trampoline =
  type ICall<'a, 'e> =
    abstract member Rebind<'b> : ('a -> Tram<'b,'e>) -> Tram<'b,'e>
    abstract member Next : unit -> Tram<'a,'e>

  and Tram<'a, 'e> =
    | Done of Result<'a,'e>
    | Call of ICall<'a, 'e>

  type TramMonad() =
    member _.Return x = Done x
    member _.ReturnFrom x = x
    member tramp.Bind(ma, f) =
      match ma with
      | Call c -> c.Rebind f
      | Done _ -> bind ma f

  let tramp = new TramMonad()

  let rec bind<'a, 'x, 'e> (mx : Tram<'x,'e>) (f : 'x -> Tram<'a,'e>) : Tram<'a,'e> =
    { new ICall<'a, 'e> with
        member this.Rebind<'b>(g : 'a -> Tram<'b,'e>) : Tram<'b,'e> =
          bind<'b, 'x, 'e> mx (fun x -> tramp.Bind(f x, g) : Tram<'b,'e>)
        member this.Next() =
          match mx with
          | Done(Ok x) -> f x
          | Done(Error e) -> Done(Error e)
          | Call c -> c.Rebind f }
    |> Call

  let rec runTram n t =
    match t with
    | Done x -> n, x
    | Call c -> runTram (n+1) (c.Next())

let tramp = Trampoline.tramp
