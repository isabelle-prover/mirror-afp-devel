structure CSMABenchL = struct
fun run n =
    let
      open Benchmark
      val input = CsmaGen.string false n
      val name = "CsmaL" ^ (Int.toString n)
     in
       Mlunta.checking name input
       |> (K ())
    end
end

structure CSMABenchR = struct
fun run n =
    let
      open Benchmark
      val input = CsmaGen.string true n
      val name = "CsmaR" ^ (Int.toString n)
      val _ =  "Benchmark " ^ name ^ ":\n"
     in
       Mlunta.checking name input
       |> (K ())
    end
end
