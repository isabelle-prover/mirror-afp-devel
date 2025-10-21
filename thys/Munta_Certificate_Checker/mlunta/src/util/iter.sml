(* This is taken from the mlton page at: mlton.org/ProductType *)
infix 7 &
datatype ('a, 'b) product = & of 'a * 'b
infix &

(* This is taken from the mlton page at: http://mlton.org/ForLoops *)
signature ITER =
  sig
    type 'a t = ('a -> unit) -> unit

    val return: 'a -> 'a t
    val >>= : 'a t * ('a -> 'b t) -> 'b t
    val <$> : 'a t * ('a -> 'b) -> 'b t

    val none: 'a t

    val to: int * int -> int t
    val to_n: int -> int t
    val downto: int * int -> int t

    val inList: 'a list -> 'a t
    val inVector: 'a vector -> 'a t
    val inArray: 'a array -> 'a t

    val using: ('a, 'b) StringCvt.reader -> 'b -> 'a t

    val when: 'a t * ('a -> bool) -> 'a t
    val by: 'a t * ('a -> 'b) -> 'b t
    val @@ : 'a t * 'a t -> 'a t
    val ** : 'a t * 'b t -> ('a, 'b) product t
    val <*> : 'a t * 'b t -> ('a * 'b) t
    val for: 'a -> 'a
  end

infix 2 to downto
infix 1 @@ when by
infix 0 >>= <$> <*> **

fun const x _ = x
fun opt fno fso = fn NONE => fno () | SOME x => fso x
fun pass x f = f x

structure Iter :> ITER =
struct
type 'a t = ('a -> unit) -> unit
    val return = pass
    fun (iA >>= a2iB) f = iA (flip a2iB f)
    fun (i <$> i') = i >>= (i' #> return)

    val none = ignore

    fun (l to u) f = let fun `l = if l<u then (f l; `(l+1)) else () in `l end
    fun to_n n = 0 to n
    fun (u downto l) f =
        let
            fun `u = if u>l then (f (u-1); `(u-1)) else ()
        in `u
        end

    fun inList x = flip List.app x
    fun inVector x = flip Vector.app x
    fun inArray x = flip Array.app x

    fun using get s f =
        let
            fun `s = opt (const ()) (fn (x, s) => (f x; `s)) (get s)
        in `s
        end

    fun (iA when p) f = iA (fn a => if p a then f a else ())
    fun (iA by g) f = iA (f o g)
    fun (iA @@ iB) f = (iA f : unit; iB f)
    fun (iA ** iB) f = iA (fn a => iB (fn b => f (a & b)))
    fun (i <*> i') = i ** i' <$> (fn x & y => (x, y))
    val for = id
end
