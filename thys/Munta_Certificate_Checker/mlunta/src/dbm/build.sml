(* XXX: own directory for custom iteration combinators *)
Build.subdir "src/dbm/"
             [
               "matrix_iter", "sp_iter", "dbm_iter", "signed_word", "dbm_entry",
               "word_entry", "entry", "dbm"
             ]
