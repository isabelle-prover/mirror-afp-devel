subsection \<open>Class Instances for Multivariate Polynomials and Containers\<close>


theory MPoly_Container
  imports 
    "Polynomials.MPoly_Type_Class"
    "Containers.Set_Impl"
begin

text \<open>Basic setup for using multivariate polynomials in combination with container framework.\<close>
 
derive (eq) ceq poly_mapping
derive (dlist) set_impl poly_mapping (* difference list *)
derive (no) ccompare poly_mapping (* no order on poly-mapping *)

end