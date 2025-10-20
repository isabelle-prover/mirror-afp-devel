structure FischerBenchR = struct
fun run n =
    let
      open Benchmark
      val input = FischerGen.string true n
      val name = "FischerR" ^ (Int.toString n)
     in
       Mlunta.checking name input
       |> (K ())
    end
end

structure FischerBenchL = struct
fun run n =
    let
      open Benchmark
      val input = FischerGen.string false n
      val name = "FischerL" ^ (Int.toString n)
     in
       Mlunta.checking name input
       |> (K ())
    end
end
