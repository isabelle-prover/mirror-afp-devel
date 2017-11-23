(*  Title:      Cars.thy
    Author:     Sven Linker

A countably infinite type to denote cars in the model of HMLSL.
*)

section\<open>Cars\<close>

text {* 
We define a type to refer to cars. For simplicity, we assume that (countably)
infinite cars exist.
*}

theory Cars
  imports Main
begin

text {*
The type of cars consists of the natural numbers. However, we do not
define or prove any additional structure about it.
*}

typedef cars = "{n. (is_nat n)} " 
  using Nat_Transfer.transfer_int_nat_function_closures(9) by auto

locale cars 
begin

text {*
For the construction of possible counterexamples, it is beneficial to 
prove that at least two cars exist. Furthermore, we show that there indeed
exist infinitely many cars.
*}

lemma at_least_two_cars_exists:"\<exists>c d ::cars . c\<noteq>d" 
proof -
  have "(0::int) \<noteq> 1" by simp
  then have "Abs_cars (0::int) \<noteq> Abs_cars(1) " 
    by (metis Abs_cars_inverse Nat_Transfer.transfer_int_nat_function_closures(9)
        Nat_Transfer.transfer_nat_int_function_closures(6) int_nat_eq mem_Collect_eq)
  thus ?thesis by blast
qed

lemma infinite_cars:"infinite {c::cars . True}" 
proof -
  have "infinite {n. is_nat(n)}" 
    by (metis Nat_Transfer.transfer_int_nat_set_function_closures(5)
        Nat_Transfer.transfer_int_nat_set_function_closures(6) infinite_UNIV_char_0
        infinite_super mem_Collect_eq subsetI transfer_nat_int_set_relations(1))
  then show ?thesis 
    by (metis UNIV_def finite_imageI type_definition.Rep_range type_definition_cars)
qed

end
end