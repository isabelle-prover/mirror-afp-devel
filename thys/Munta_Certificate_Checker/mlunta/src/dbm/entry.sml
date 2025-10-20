structure Entry : DBM_ENTRY = struct
type t = IntRep.t
type from = t
type to = Word8Vector.vector
open IntRep

fun from_int x = id x
fun =< x = from_int (LT x)
fun ==< x = from_int (LTE x)

fun mod_lsb b x =
    case x of
        (LT x') => if b then (LTE x') else x |
        (LTE x') => if b then (LT x') else x |
        Inf => Inf

val inf = Inf
val zero = (LTE 0)


fun get_int (LT x) = x |
    get_int (LTE x) = x

fun add x y =
    case (x, y) of
        (Inf, _) => Inf |
        (_, Inf) => Inf |
        (LTE m, LTE n) => LTE (n + m) |
        (m, n) => LT ((get_int m) + (get_int n))

fun (x |+| y) = add x y

fun (x |<| y) =
    case (x, y) of
        (Inf, Inf) => false |
        (Inf, _) => false |
        (_, Inf) => true |
        (LT m, LT n) => m < n |
        (LTE m, LTE n) => m < n |
        (LT m, LTE n) => m <= n |
        (LTE m, LT n) =>  m < n

fun (x |<=| y) =
    case (x, y) of
        (Inf, Inf) => true |
        (Inf, _) => false |
        (_, Inf) => true |
        (LT m, LT n) => m <= n |
        (LTE m, LTE n) => m <= n |
        (LTE m, LT n) => m < n |
        (LT m, LTE n) => m <= n

fun (x |>| y) = (x |<=| y) |> not

fun min x y = if x |<=| y then x else y
fun max x y = if x |<=| y then y else x

fun max_ceil c c' =
    case (c, c') of
        (Inf, _) => c' |
        (_, Inf) => c |
        _ => max c c'

fun to_string x =
    case x of
        Inf => "oo" |
        (LT x) => "(" ^ Int.toString x ^ ", < )" |
        (LTE x) => "(" ^ Int.toString x ^ ", <=)"

fun |~| x =
    case x of
        Inf => Inf |
        (LT x) => ~ x |> LT |
        (LTE x) => ~ x |> LTE

fun not_bound x =
    case x of
        Inf => Inf |
        (LT x) => LTE (~x) |
        (LTE x) => LT (~x)

fun (x == y) = x = y
fun cmp x y =
    if x |<| y then Lt
    else if x == y then Eq
    else Gt

fun check_neg x =
    case x of
        Inf => false |
        (LTE x) => x < 0 |
        (LT x) => x <= 0

fun serialize x = x |> Entry64Bit.from_int |> Entry64Bit.serialize
end
