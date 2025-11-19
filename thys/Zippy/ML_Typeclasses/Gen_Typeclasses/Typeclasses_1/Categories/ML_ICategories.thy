\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Indexed Categories\<close>
theory ML_ICategories
  imports
    ML_Categories
    ML_ITypeclasses_Base
begin

ML_gen_file\<open>icategory.ML\<close>
ML_gen_file\<open>icategory_instance.ML\<close>

ML_gen_file\<open>icategory_util.ML\<close>

end