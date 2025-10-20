signature EITHER = sig
    datatype ('a, 'b) t = Left of 'a | Right of 'b
    val either: ('a -> 'c) -> ('b -> 'c) -> ('a, 'b) t -> 'c
    val mapL: ('a -> 'c) -> ('a, 'b) t -> ('c, 'b) t
    val mapR: ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
    val bindR: ('b -> ('a, 'c) t) -> ('a, 'b) t -> ('a, 'c) t
    val >>= :  ('a, 'b) t * ('b -> ('a, 'c) t) -> ('a, 'c) t
    val bindL: ('a -> ('c, 'b) t) -> ('a, 'b) t -> ('c, 'b) t

    val >=> : ('a -> ('b, 'c) t) * ('c -> ('b, 'd) t) -> ('a -> ('b, 'd) t)
    val join: ('a, ('a, 'b) t) t -> ('a, 'b) t


    (* Throw Exception *)
    val the_right: ('a, 'b) t -> 'b
    (* Throw Exception *)
    val the_left: ('a, 'b) t -> 'a
    val same: ('a -> 'a -> 'c) -> ('b -> 'b -> 'c) -> ('a -> 'b -> 'd) -> ('a, 'b) t -> ('a, 'b) t -> ('d, 'c) t
    val from_option: 'a -> 'b option -> ('a, 'b) t
    val succeed: 'a -> ('b, 'a) t
    val fail: 'a -> ('a, 'b) t
    val combine: ('a -> 'a -> 'a) -> ('b -> 'b -> 'c) -> ('a, 'b) t -> ('a, 'b) t -> ('a, 'c) t
    val combine_map: ('a -> ('b list, 'c) t) -> 'a list -> ('b list, 'c list) t
    val <|> : ('a list, 'b) t * ('a list, 'c) t -> ('a list, 'b * 'c) t
end

infix >>= >=>
infix 2 <|>
structure Either : EITHER = struct
datatype ('a, 'b) t = Left of 'a | Right of 'b
fun either f _ (Left x) = f x
  | either _ g (Right x) = g x
fun mapL f (Left x) = Left (f x)
  | mapL _ (Right x) = (Right x)
fun mapR f (Right x) = Right (f x)
  | mapR _ (Left x) = Left x
fun bindR f (Right x) = f x
  | bindR _ (Left x) = Left x
fun bindL f (Left x) = f x
  | bindL _ (Right x) = (Right x)

fun join x = bindR (fn y => y) x

fun switch sw1 sw2 x =
    case sw1 x of
            (Right s) => sw2 s
      | (Left f) => Left f
fun (sw1 >=> sw2) = switch sw1 sw2

fun (a >>= b) = bindR b a

fun combine onL onR l r =
    case (l, r) of
        (Left e, Left e') => Left (onL e e')  |
        (Left e, Right _) => Left e |
        (Right _, Left e) => Left e |
        (Right a, Right b) => Right (onR a b);
fun comb_app l r = combine append pair l r
fun (l <|> r) = comb_app l r

fun combine' ls  =
    case ls of
        [] => Right []
     | (x::xs) => combine append (fn (y : 'b) => fn (ys : 'b list) => (y::ys))
                         x (combine' xs)

fun combine_map f = List.map f #> combine'

fun same onL onR notsame l r =
    case (l, r) of
            (Left e, Left e') => Right (onL e e')  |
            (Left e, Right e') => Left (notsame e e') |
            (Right e, Left e') => Left (notsame e' e) |
            (Right e, Right e') => Right (onR e e');

fun fail x = Left x
fun succeed x = Right x
fun the_right (Right x) = x
  | the_right _ = Exn.error "Not an Right"
fun the_left (Left x) = x
  | the_left _ = Exn.error "Not a Left"
fun from_option err x =
    case x of
            NONE => fail err |
            SOME x => succeed x
end
