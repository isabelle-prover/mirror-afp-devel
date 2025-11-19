(* XXX: what about dataguard test *)
Build.subdir "test/construction/"
             [
               "rewrite_gi_test", "renaming_test", "constraint_test"(* , "dataguard_test" *)
             ]
