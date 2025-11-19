\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Linked Zippers\<close>
theory ML_Linked_Zippers
  imports
    ML_Zippers
begin

ML\<open>
  val mk_name = ML_Gen.mk_name
\<close>

ML_gen_file\<open>linked_zipper_morphs.ML\<close>
ML_gen_file\<open>linked_zipper.ML\<close>

end