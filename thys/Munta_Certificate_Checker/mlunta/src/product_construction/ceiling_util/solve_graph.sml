signature SOLVE_GRAPH = sig
  structure Graph : GRAPH
  val shortest_path: Graph.graph -> Graph.graph
end

functor SolveGraph(Graph : GRAPH) : SP_GRAPH =
struct
structure Graph = Graph
local
  structure SP = FloydWarshallIter(Graph.M)
  open Iter
in
fun shortest_path' G =
    let
      val adj = Graph.adj G
      fun sub i j = Graph.M.sub i j adj
      fun upd i j x = Graph.M.update i j x adj
    in
      for (SP.close adj)
          (fn (k, i, j, D_ij) =>
              let
                val D_ij' = Graph.W.add (sub i k) (sub k j)
                val max = Graph.W.max D_ij D_ij'
              in
                upd i j max
              end
          )
    end
end

fun shortest_path G = tap shortest_path' G
end
