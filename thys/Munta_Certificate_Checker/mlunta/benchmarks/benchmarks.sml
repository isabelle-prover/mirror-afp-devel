fun main () =
    (
      FischerBenchR.run 5;
      FischerBenchL.run 5;
      FischerBenchL.run 6;

      FddiBenchR.run 8;
      FddiBenchR.run 10;
      FddiBenchL.run 6;
      FddiBenchL.run 7;

      CSMABenchR.run 5;
      CSMABenchR.run 6;
      CSMABenchL.run 6
    ) handle _ => print "There was an Unhandled Exception !!!!"

val _ = main ()
