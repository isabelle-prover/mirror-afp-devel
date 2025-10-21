signature DICT = sig
    type key = int
    type 'a t
    val fromList : 'a list -> 'a t
    val find : key -> 'a t -> 'a
    val map : ('a -> 'b) -> 'a t -> 'b t
    val update: key -> 'a -> 'a t -> 'a t
    val foldli: (int * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b
    val foldl: ('a * 'b -> 'b) -> 'b -> 'a t -> 'b
    val size: 'a t -> int
end
