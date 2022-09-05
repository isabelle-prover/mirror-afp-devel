theory Renaming_Auto
  imports
    Utils
    Renaming
keywords
  "rename" :: thy_decl % "ML"
and
  "simple_rename" :: thy_decl % "ML"
and
  "src"
and
  "tgt"
abbrevs
  "simple_rename" = ""

begin

hide_const (open) Order.pred

lemmas nat_succI = nat_succ_iff[THEN iffD2]
ML_file\<open>Renaming_ML.ml\<close>

end