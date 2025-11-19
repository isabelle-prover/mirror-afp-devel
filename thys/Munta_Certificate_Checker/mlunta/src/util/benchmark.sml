structure Benchmark = struct
type 'a benchmark =
     {
       result: 'a,
       time : Time.time
     }

fun time_it f x =
    let
      val start = Timer.startRealTimer ()
      val result = f x
      val time = Timer.checkRealTimer start
    in
      {
        result = result,
        time = time
      }
    end

fun to_string time =
    let
      val headersep = "****************************************\n"
      val total_str = "Total Time: " ^ (time |> Time.toString)
    in
      headersep ^
      total_str ^
      "\n" ^
      headersep ^
      "\n"
    end

fun add_time f ({result, time} : 'a benchmark) =
    f (time, result)

fun run_and_print f x : 'a benchmark =
    time_it f x
    |> add_time (apfst to_string)
    |> apfst print
    |> snd

fun time (b : 'a benchmark) =
    #time b

fun result (b : 'a benchmark) =
    #result b
end
