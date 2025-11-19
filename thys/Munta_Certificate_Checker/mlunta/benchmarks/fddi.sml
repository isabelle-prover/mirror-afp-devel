structure FddiBenchR = struct
fun run n =
    let
      open Benchmark
      val input = FddiGen.string true n
      val name = "FddiR" ^ (Int.toString n)
     in
       Mlunta.checking name input
       |> (K ())
    end
end
structure FddiBenchL = struct
fun run n =
    let
      open Benchmark
      val input = FddiGen.string false n
      val name = "FddiL" ^ (Int.toString n)
    in
      Mlunta.checking name input
      |> (K ())
    end
end
