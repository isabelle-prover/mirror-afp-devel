(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish
   Last modified: 11 Aug, 2025
  *)

(*<*)
theory SyntaxAndSemantics
imports Main HOL.List
begin
(*>*)

datatype 'b formula = 
    FF                                      (\<open>\<bottom>.\<close>)
  | TT                                      (\<open>\<top>.\<close>)
  | atom 'b                
  | Negation "'b formula"                   (\<open>\<not>.(_)\<close> [110] 110)
  | Conjunction "'b formula" "'b formula"   (infixl \<open>\<and>.\<close>  109)
  | Disjunction "'b formula" "'b formula"   (infixl \<open>\<or>.\<close>  108)
  | Implication "'b formula" "'b formula"   (infixl \<open>\<rightarrow>.\<close> 100)


primrec t_v_evaluation :: "('b \<Rightarrow>  bool) \<Rightarrow> 'b formula  \<Rightarrow> bool"
where
   "t_v_evaluation I \<bottom>. = False"
|  "t_v_evaluation I \<top>. = True"
|  "t_v_evaluation I (atom p) = I p"
|  "t_v_evaluation I (\<not>. F) = (\<not> (t_v_evaluation I F))"
|  "t_v_evaluation I (F \<and>. G) = ( (t_v_evaluation I F) \<and> (t_v_evaluation I G))"
|  "t_v_evaluation I (F \<or>. G) = ( (t_v_evaluation I F) \<or> (t_v_evaluation I G))"
|  "t_v_evaluation I (F \<rightarrow>. G) = ( (t_v_evaluation I F) \<longrightarrow> (t_v_evaluation I G))"  

lemma eval_false_implication:
  assumes "\<not> t_v_evaluation I (F \<rightarrow>.G)"
  shows "t_v_evaluation I F \<and> \<not> t_v_evaluation I G "
  by (meson assms t_v_evaluation.simps(7))

(*>*)

definition model :: "('b \<Rightarrow> bool) \<Rightarrow> 'b formula set \<Rightarrow> bool" (\<open>_ model _\<close> [80,80] 80) where
 "I model S \<equiv> (\<forall>F \<in> S. t_v_evaluation I F)"

definition satisfiable :: "'b formula set \<Rightarrow> bool" where
 "satisfiable S \<equiv> (\<exists>v. v model S)"

(*<*)

lemma satisfiable_subset:
  assumes "satisfiable S" and "H\<subseteq>S"
  shows "satisfiable H"
  by (meson assms(1,2) model_def satisfiable_def subset_iff)
(*>*)

definition consequence :: "'b formula set \<Rightarrow> 'b formula \<Rightarrow> bool" (\<open>_ \<Turnstile> _\<close> [80,80] 80) where
 "S \<Turnstile> F \<equiv> (\<forall>I. I model S \<longrightarrow> t_v_evaluation I F)"

(*<*)

lemma ConsSat:
  assumes "S \<Turnstile> F"
  shows "\<not> satisfiable (S \<union> {\<not>. F})"
proof(rule notI)
  assume "satisfiable (S \<union> {\<not>. F})"
  hence 1: "\<exists>I. I model (S \<union> {\<not>. F})" by (auto simp add: satisfiable_def) 
  obtain I where I: "I model (S \<union> {\<not>. F})" using 1 by auto
  hence 2: "\<forall>G\<in>(S \<union> {\<not>. F}). t_v_evaluation I G" 
    by (auto simp add: model_def)
  hence "\<forall>G\<in>S. t_v_evaluation I G" by blast
  moreover
   have 3: "t_v_evaluation I (\<not>. F)" using 2 by simp
   hence "\<not>t_v_evaluation I F" by auto 
  ultimately 
  show "False" using assms 
    by (simp add: consequence_def, simp add: model_def)
qed

lemma SatCons:
  assumes "\<not> satisfiable (S \<union> {\<not>. F})"
  shows "S \<Turnstile> F"
proof (rule contrapos_np)
  assume hip: "\<not> S \<Turnstile> F"
  show "satisfiable (S \<union> {\<not>. F})"
  proof -
    have 1: "\<exists>I. I model S \<and> \<not>(t_v_evaluation I F)"  
      using hip by (simp add: consequence_def)
    obtain I where I: "I model S \<and> \<not>(t_v_evaluation I F = True)" using 1 by auto
    hence  "I model S" by simp
    hence 2: "\<forall>G\<in>S. t_v_evaluation I G" by (simp add: model_def) 
    have "\<not>t_v_evaluation I F" using I by simp
    hence 3: "t_v_evaluation I (\<not>. F)" by simp
    have  "\<forall>G\<in>(S \<union> {\<not>. F}). t_v_evaluation I G" 
    proof (rule ballI) 
      fix G 
      assume hip2: "G\<in>(S \<union> {\<not>. F})"    
      show "t_v_evaluation I G"
      proof (cases)
        assume "G\<in>S"
        thus ?thesis using 2 by simp
        next
        assume "\<not>G\<in>S"
        hence "G = (\<not>. F)"using hip2 by simp
        thus ?thesis using 3 by simp
      qed
    qed
    hence "I model (S \<union> {\<not>. F})" by (simp add: model_def)   
    thus ?thesis by (auto simp add: satisfiable_def)
  qed
  next
  show "\<not> satisfiable (S \<union> {\<not>. F})" using assms by simp
qed 
(*>*)

theorem EquiConsSat: 
  shows  "S \<Turnstile> F = (\<not> satisfiable (S \<union> {\<not>. F}))"
(*<*)
using SatCons ConsSat by blast
(*>*)

definition tautology :: "'b formula \<Rightarrow> bool" where
  "tautology F \<equiv> (\<forall>I. ((t_v_evaluation I F)))"

lemma "tautology (F  \<rightarrow>. (G \<rightarrow>. F))"
  by (simp add: tautology_def)

lemma empty_model: "\<forall>(I::'b \<Rightarrow> bool). I model {}"
proof - 
  fix I
  have "\<forall>F\<in> {}. t_v_evaluation (I::'b \<Rightarrow> bool) F" by simp
  thus "\<forall>I. I model {}" by (simp add: model_def)
qed
(*>*)

theorem CNS_tautology: "tautology F = ({} \<Turnstile> F)"
(*<*)
by(simp add: tautology_def consequence_def empty_model)
(*>*)

theorem TautSatis:
  shows "tautology (F \<rightarrow>. G) = (\<not> satisfiable{F, \<not>.G})"
(*<*)
proof -
 { assume h1: "\<not> tautology (F \<rightarrow>. G)"
   have "satisfiable{F, \<not>.G}"
   proof -
     have "\<exists> I. \<not> t_v_evaluation I (F \<rightarrow>. G)" 
       using h1 by (unfold tautology_def, auto) 
    then obtain I where "\<not> t_v_evaluation I (F \<rightarrow>. G)" by auto 
    hence a: "\<not> t_v_evaluation I (F \<rightarrow>. G)"  by auto
    hence "t_v_evaluation I F  \<and> \<not>t_v_evaluation I G" 
    proof -             
     { assume "\<not> t_v_evaluation I F \<or> t_v_evaluation I G"
       hence "False"
       proof(rule disjE)
         assume "\<not>t_v_evaluation I F"
         hence " \<not>t_v_evaluation I F" by auto
         hence "t_v_evaluation I (F \<rightarrow>. G)" 
           by simp
         thus "False" using a by auto
       next
         assume "t_v_evaluation I G"
         hence "t_v_evaluation I G" by auto
         hence "t_v_evaluation I (F \<rightarrow>. G)" by simp
         thus "False" using a by auto
       qed}  
     thus "t_v_evaluation I F \<and> \<not> t_v_evaluation I G" by auto
   qed
   hence "t_v_evaluation I F = True \<and> t_v_evaluation I (\<not>.G)" 
     by simp
   hence "\<exists> I. I model {F, \<not>.G}" by (auto simp add: model_def)  
   thus "satisfiable {F, \<not>.G}" by(simp add: satisfiable_def)
 qed}
moreover
{ assume h2: "satisfiable {F, \<not>.G}" 
  have "\<not> tautology (F \<rightarrow>. G)" 
  proof -  
    have "\<exists> I. I model {F, \<not>.G}" using h2 by (simp add: satisfiable_def)  
    hence "\<exists> I. t_v_evaluation I F \<and> t_v_evaluation I (\<not>.G)" 
      by(simp add: model_def)
    then obtain I where I1: "t_v_evaluation I F" and I2: "t_v_evaluation I (\<not>.G)"
      by auto
    have "\<not> t_v_evaluation I G" using I2  by auto   
    hence "\<not>t_v_evaluation I (F \<rightarrow>. G)" using I1 
      by simp
    thus "\<not> tautology (F \<rightarrow>. G)" by (auto, unfold tautology_def, auto)
  qed}
  ultimately
  show ?thesis by auto
qed
 
definition equivalent:: "'b formula  \<Rightarrow> 'b formula \<Rightarrow> bool" where
  "equivalent F G \<equiv> (\<forall> I. (t_v_evaluation I F) = (t_v_evaluation I G))"

primrec disjunction_atomic :: "'b list \<Rightarrow>'a \<Rightarrow> ('a \<times> 'b)formula"  where
 "disjunction_atomic [] i = \<bottom>."   
| "disjunction_atomic (x#D) i = (atom (i, x)) \<or>. (disjunction_atomic D i)"

lemma t_v_evaluation_disjunctions1:
  assumes "t_v_evaluation I (disjunction_atomic (a # l) i)"
  shows "t_v_evaluation I (atom (i,a)) \<or> t_v_evaluation I (disjunction_atomic l i)"
  using assms by auto

lemma t_v_evaluation_atom:
  assumes "t_v_evaluation I (disjunction_atomic l i)"
  shows "\<exists>x. x \<in> set l \<and> (t_v_evaluation I (atom (i,x)))"
proof-
  have "t_v_evaluation I (disjunction_atomic l i) \<Longrightarrow>
  \<exists>x. x \<in> set l \<and> (t_v_evaluation I (atom (i,x)))"
  proof(induct l)
    case Nil
    then show ?case by auto
  next   
    case (Cons a l)  
    show  "\<exists>x. x \<in> set (a # l) \<and> t_v_evaluation I (atom (i,x))"  
    proof-
      have
      "(t_v_evaluation I (atom (i,a))) \<or> t_v_evaluation I (disjunction_atomic l i)" 
        using Cons(2) t_v_evaluation_disjunctions1[of I] by auto      
      thus ?thesis
    proof(rule disjE)
      assume "t_v_evaluation I (atom (i,a))"
      thus ?thesis by auto
    next
      assume "t_v_evaluation I (disjunction_atomic l i)" 
      thus ?thesis using Cons by auto    
    qed
  qed
qed
  thus ?thesis using assms by auto
qed 

definition set_to_list ::  "'a set \<Rightarrow> 'a list" 
  where "set_to_list s = (SOME l. set l = s)"

lemma  finiteness_set_to_list:
   "finite s \<equiv> (set (set_to_list s) = s)"
  unfolding set_to_list_def using List.finite_set finite_list tfl_some
  by (smt (verit, del_insts)) 

end
