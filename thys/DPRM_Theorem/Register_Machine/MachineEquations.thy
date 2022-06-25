section \<open>Arithmetization of Register Machines\<close>

subsection \<open>A first definition of the arithmetizing equations\<close>

theory MachineEquations
  imports MultipleStepRegister MultipleStepState MachineMasking
begin
 
definition mask_equations :: "nat \<Rightarrow> (register \<Rightarrow> nat) \<Rightarrow> (register \<Rightarrow> nat)
                              \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" (* 4.15, 4.17 and 4.20 *)
  where "(mask_equations n r z c d e f) = ((\<forall>l<n. (r l) \<preceq> d)
                                           \<and> (\<forall>l<n. (z l) \<preceq> e)
                                           \<and> (\<forall>l<n. 2^c * (z l) = (r l + d) && f))"

(* REGISTER EQUATIONS *)
definition reg_equations :: "program \<Rightarrow> (register \<Rightarrow> nat) \<Rightarrow> (register \<Rightarrow> nat) \<Rightarrow> (state \<Rightarrow> nat)
                             \<Rightarrow>  nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "(reg_equations p r z s b a n q) = (
    \<comment> \<open>4.22\<close> (\<forall>l>0. l < n \<longrightarrow> r l =     b*r l + b*\<Sum>R+ p l (\<lambda>k. s k) - b*\<Sum>R- p l (\<lambda>k. s k && z l))
  \<and> \<comment> \<open>4.23\<close> (      r 0 = a + b*r 0 + b*\<Sum>R+ p 0 (\<lambda>k. s k) - b*\<Sum>R- p 0 (\<lambda>k. s k && z 0))
  \<and> (\<forall>l<n. r l < b ^ q)) \<comment> \<open>Extra equation not in Matiyasevich's book.
                                      Needed to show that all registers are empty at time q\<close>"

(* STATE EQUATIONS -- todo from here on *)
definition state_equations :: "program \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> (register \<Rightarrow> nat) \<Rightarrow> 
                              nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "state_equations p s z b e q m = (
\<comment> \<open>4.24\<close> (\<forall>d>0. d\<le>m \<longrightarrow> s d =     b*\<Sum>S+ p d (\<lambda>k. s k) + b*\<Sum>S- p d (\<lambda>k. s k && z (modifies (p!k)))
                                                 + b*\<Sum>S0 p d (\<lambda>k. s k && (e - z (modifies (p!k)))))
     \<and> \<comment> \<open>4.25\<close> (       s 0 = 1 + b*\<Sum>S+ p 0 (\<lambda>k. s k) + b*\<Sum>S- p 0 (\<lambda>k. s k && z (modifies (p!k)))
                                                 + b*\<Sum>S0 p 0 (\<lambda>k. s k && (e - z (modifies (p!k)))))
     \<and> \<comment> \<open>4.27\<close> (s m = b^q)
     \<and> (\<forall>k\<le>m. s k \<preceq> e) \<and>  (\<forall>k<m. s k < b ^ q) \<comment> \<open>these equations are not from the book\<close>
     \<and> (\<forall>M\<le>m. (\<Sum>k\<le>M. s k) \<preceq> e) \<comment> \<open>this equation is added, too\<close> )"

(* The following two equations do not appear in Matiyasevich's book, this duplicated definition
   (note that they are also included just above) is, for now, only a reminder. *)
definition state_unique_equations :: "program \<Rightarrow> (state\<Rightarrow>nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>bool" where
  "state_unique_equations p s m e = ((\<Sum>k=0..m. s k) \<preceq> e \<and> (\<forall>k\<le>m. s k \<preceq> e))"


(* RM CONSTANTS FOR DEFINITION AND CLARIFY OF EQUATIONS *)
definition rm_constants :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "rm_constants q c b d e f a = (
       \<comment> \<open>4.14\<close> (b = B c)
     \<and> \<comment> \<open>4.16\<close> (d = D q c b)
     \<and> \<comment> \<open>4.18\<close> (e = E q b) \<comment> \<open>4.19 left out (compare book)\<close>
     \<and> \<comment> \<open>4.21\<close> (f = F q c b)
     \<and> \<comment> \<open>extra equation not in the book\<close> c > 0
     \<and> \<comment> \<open>4.26\<close> (a < 2^c) \<and> (q>0))"

definition rm_equations_old :: "program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "rm_equations_old p q a n = (
    \<exists> b c d e f :: nat.
    \<exists> r z :: register \<Rightarrow> nat.
    \<exists> s :: state \<Rightarrow> nat.
     mask_equations n r z c d e f
     \<and> reg_equations p r z s b a n q 
     \<and> state_equations p s z b e q (length p - 1)
     \<and> rm_constants q c b d e f a)"

end
