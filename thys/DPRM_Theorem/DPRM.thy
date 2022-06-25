section \<open>Proof of the DPRM theorem\<close>

theory DPRM
  imports "Machine_Equations/Machine_Equation_Equivalence"
begin

definition is_recenum :: "nat set \<Rightarrow> bool" where
  "is_recenum A =
    (\<exists> p :: program.
     \<exists> n :: nat.
     \<forall> a :: nat. \<exists> ic. ic = initial_config n a \<and> is_valid_initial ic p a \<and>
    (a \<in> A) = (\<exists> q::nat. terminates ic p q))"

theorem DPRM: "is_recenum A \<Longrightarrow> is_dioph_set A"
proof -
  assume "is_recenum A"
  hence "(\<exists> p :: program. 
          \<exists> n :: nat. \<forall> a :: nat. 
          \<exists> ic. ic = initial_config n a \<and> is_valid_initial ic p a \<and>
            (a \<in> A) = (\<exists> q::nat. terminates ic p q))" using is_recenum_def by auto
  then obtain p n where p: 
         "\<forall> a :: nat. 
          \<exists> ic. ic = initial_config n a \<and> is_valid_initial ic p a \<and>
            (a \<in> A) = (\<exists> q::nat. terminates ic p q)" by auto

  interpret rm: register_machine p "Suc n" apply (unfold_locales)
  proof -
    from p have 
      "\<exists> ic. ic = initial_config n 0 \<and> is_valid_initial ic p 0 \<and>
            (0 \<in> A) = (\<exists> q::nat. terminates ic p q)" by auto
    then obtain ic where ic: "ic = initial_config n 0" and is_val: "is_valid_initial ic p 0" by auto 

    show "length p > 0"
      using is_val unfolding is_valid_initial_def is_valid_def by auto

    have "length (snd ic) = Suc n"
      unfolding ic initial_config_def by auto 

    moreover have "snd ic \<noteq> []"
      using is_val unfolding is_valid_initial_def is_valid_def tape_check_initial.simps by auto

    ultimately show "Suc n > 0"
      by auto
      
    show "program_register_check p (Suc n)"
      using is_val unfolding is_valid_initial_def is_valid_def using \<open>length (snd ic) = Suc n\<close>
      by auto
  qed
      

  have equiv: "a \<in> A \<longleftrightarrow> register_machine.rm_equations p (Suc n) a" for a 
    proof -
      from p have "\<exists> ic. ic = initial_config n a \<and> is_valid_initial ic p a \<and>
      (a \<in> A) = (\<exists> q::nat. terminates ic p q)" by auto
      then obtain ic where ic: "ic = initial_config n a \<and> is_valid_initial ic p a \<and>
      (a \<in> A) = (\<exists> q::nat. terminates ic p q)" by blast

      have ic_def: "ic = initial_config n a" using ic by auto
      hence n_is_length: "Suc n = length (snd ic)" using initial_config_def[of "n" "a"] by auto
      have is_val: "is_valid_initial ic p a" using ic by auto
      have "(a \<in> A) = (\<exists>q. terminates ic p q)" using ic by auto
      moreover have "(\<exists>q. terminates ic p q) = register_machine.rm_equations p (Suc n) a"
        using is_val n_is_length rm.conclusion_4_5
        by auto 

      ultimately show ?thesis by auto  
   qed

  hence A_characterization: "A = {a::nat. register_machine.rm_equations p (Suc n) a}" by auto

  have eq_dioph: "\<exists>P\<^sub>1 P\<^sub>2. \<forall>a. register_machine.rm_equations p (Suc n) (peval A a) 
                    = (\<exists>v. ppeval P\<^sub>1 a v = ppeval P\<^sub>2 a v)" for A
    using rm.rm_dioph[of A] using is_dioph_rel_def[of "rm.rm_equations_relation A"] 
    unfolding rm.rm_equations_relation_def by(auto simp: unary_eval)

  have "\<exists>P\<^sub>1 P\<^sub>2. \<forall>b. register_machine.rm_equations p (Suc n) (peval (Param 0) (\<lambda>x. b)) 
         = (\<exists>v. ppeval P\<^sub>1 (\<lambda>x. b) v = ppeval P\<^sub>2 (\<lambda>x. b) v)"
    using eq_dioph[of "Param 0"] by blast

  hence "\<exists>P1 P2. \<forall>a. register_machine.rm_equations p (Suc n) a 
                    = (\<exists>v. ppeval P1 (\<lambda>x. a) v = ppeval P2 (\<lambda>x. a) v)"
    by auto

  thus ?thesis 
    unfolding A_characterization is_dioph_set_def by simp
qed

end
