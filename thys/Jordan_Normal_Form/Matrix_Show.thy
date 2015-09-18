(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Converting Matrices to Strings\<close>

text \<open>We just instantiate matrices in the show-class by printing them as lists of lists.\<close>

theory Matrix_Show
imports
  "../Show/Show"
  Matrix
begin

definition shows_mat :: "'a :: show mat \<Rightarrow> shows" where
  "shows_mat A \<equiv> shows (mat_to_list A)"

instantiation mat :: ("show") "show"
begin

definition "shows_prec p (A :: 'a mat) \<equiv> shows_mat A"
definition "shows_list (As :: 'a mat list) \<equiv> shows_sep shows_mat (shows '', '') As"

instance 
  by standard (simp_all add: shows_mat_def show_law_simps shows_prec_mat_def shows_list_mat_def)

end

end