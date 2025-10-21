signature SP_GRAPH = sig
  structure M : MATRIX
  structure W : WEIGHT
  type graph
  type node = int
  val nodes: graph -> int
  val init: int -> graph
  val add_edge: node -> node -> W.t -> graph -> graph
  val edge: node -> node -> graph -> W.t option
  val shortest_path: graph -> graph
  val k: graph -> W.t Vector.vector
  val show: (int -> string) -> graph -> unit
end

functor GraphWeightToSPGraph(structure M : MATRIX
                             structure GW : GRAPH_WEIGHT)
        : SP_GRAPH =
struct
structure M = M
structure W = GW.W
type node = int
type graph = GW.t M.matrix
fun init n = M.create n GW.unbound
fun edge i j G = let val G_ij = M.sub i j G in
                   if G_ij |> GW.is_unbound then NONE
                   else G_ij |> GW.back |> SOME
                 end

fun edge' i j G = M.sub i j G

fun nodes G = M.dim G

fun add_edge i j x G =
    let
      val upd = flip (M.update i j) G
      val G_ij = edge' i j G
    in
      (
        G_ij |> GW.update x |> upd;
        G
      )
    end

fun adj G = G

local
  structure SP = SPIter(M)
  open Iter
in
fun shortest_path' G =
    let
      fun sub i j = edge' i j G
      fun upd i j x = M.update i j x G
    in
      for (SP.close G)
          (fn (k, i, j, D_ij) =>
              let
                val D_ij' = GW.add (sub i k) (sub k j)
                val max = GW.max D_ij D_ij'
              in
                upd i j max
              end
          )
    end
end

fun shortest_path G = tap shortest_path' G

fun init_ceil max_0 =
    if max_0 |> GW.is_unbound then GW.W.zero
    else max_0 |> GW.back

fun k G =
    Vector.tabulate (nodes G, fn max => init_ceil (edge' max 0 G))

fun show name_at G =
    let
      fun string_weight e =
          if GW.is_unbound e then "  inf  "
          else "   " ^ (e |> GW.show) ^ "   "
      fun string_edge (j, i, e) =
          (if i = 0 then "\n| " ^ name_at j ^ " |" else "")
          ^ string_weight e ^ "|"
    in
      (G |> adj |> M.appij (string_edge #> print); print "\n")
    end

end

functor SPGraphFn(
  structure M : MATRIX
  structure W : WEIGHT
) : SP_GRAPH = struct

structure SPGraph = GraphWeightToSPGraph(structure M = M
                                         structure GW = GraphWeightFn(W))
open SPGraph
end

structure IntGraph =
  SPGraphFn(
    structure M = LnLayoutMatrix
    structure W = IntWeight
  )

structure UpperGraph =
SPGraphFn(
  structure M = LnLayoutMatrix
  structure W = UpperBound
)

structure LowerGraph =
SPGraphFn(
  structure M = LnLayoutMatrix
  structure W = LowerBound
)
