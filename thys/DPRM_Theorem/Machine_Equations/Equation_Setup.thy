subsection \<open>Arithmetizing equations are Diophantine\<close>

theory Equation_Setup imports "../Register_Machine/RegisterMachineSpecification"
          "../Diophantine/Diophantine_Relations"

begin

locale register_machine = 
  fixes p :: program
    and n :: nat
  assumes p_nonempty: "length p > 0"
      and valid_program: "program_register_check p n"
  assumes n_gt_0: "n > 0"

begin

  definition m :: "nat" where
    "m \<equiv> length p - 1"

  lemma modifies_yields_valid_register:
    assumes "k < length p"
    shows "modifies (p!k) < n"
  proof - 
    have "instruction_register_check n (p!k)"
      using valid_program assms list_all_length program_register_check.simps by auto

    thus ?thesis by (cases "p!k", auto simp: n_gt_0) 
  qed

end

locale rm_eq_fixes = register_machine + 
  fixes a b c d e f :: "nat"
    and q :: nat
    and r z :: "register \<Rightarrow> nat"
    and s :: "state \<Rightarrow> nat"

end