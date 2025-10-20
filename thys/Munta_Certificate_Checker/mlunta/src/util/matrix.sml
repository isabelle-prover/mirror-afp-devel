signature MATRIX = sig
    type dim = int
    type 'a matrix

    val dim: 'a matrix -> dim
    val create: int -> 'a -> 'a matrix
    val copy: 'a matrix -> 'a matrix
    val fromList: 'a list list -> 'a matrix
    val sub: int -> int -> 'a matrix -> 'a
    val update: int -> int -> 'a -> 'a matrix -> unit
    val foldl: ('a * 'b -> 'b) -> 'b -> 'a matrix -> 'b
    val foldli: (int * 'a * 'b -> 'b) -> 'b -> 'a matrix -> 'b
    val appij: (int * int * 'a -> unit) -> 'a matrix -> unit
    val cmp: ('a * 'a -> bool) -> 'a matrix -> 'a matrix -> bool
end
