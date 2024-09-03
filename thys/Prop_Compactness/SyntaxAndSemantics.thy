(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory SyntaxAndSemantics
imports Main  
begin
(*>*)

datatype 'b formula = 
    FF
  | TT
  | atom 'b                 (* ("P_" [1000]) *)
  | Negation "'b formula"                   ("\<not>.(_)" [110] 110)
  | Conjunction "'b formula" "'b formula"     (infixl "\<and>."  109)
  | Disjunction "'b formula" "'b formula"     (infixl "\<or>."  108)
  | Implication "'b formula" "'b formula"   (infixl "\<rightarrow>." 100)


lemma "(\<not>.\<not>. Atom P \<rightarrow>. Atom Q  \<rightarrow>. Atom R) = 
       (((\<not>. (\<not>. Atom P)) \<rightarrow>. Atom Q) \<rightarrow>. Atom R)"
by simp


datatype v_truth = Ttrue | Ffalse 


definition v_negation :: "v_truth \<Rightarrow> v_truth" where
 "v_negation x \<equiv> (if x = Ttrue then Ffalse else Ttrue)"

definition v_conjunction ::  "v_truth \<Rightarrow> v_truth \<Rightarrow> v_truth" where
 "v_conjunction x y \<equiv> (if x = Ffalse then Ffalse else y)"

definition v_disjunction ::  "v_truth \<Rightarrow> v_truth \<Rightarrow> v_truth" where
 "v_disjunction x y \<equiv> (if x = Ttrue then Ttrue else y)"

definition v_implication :: "v_truth \<Rightarrow> v_truth \<Rightarrow> v_truth" where
 "v_implication x y \<equiv> (if x = Ffalse then Ttrue else y)"


primrec t_v_evaluation :: "('b \<Rightarrow>  v_truth) \<Rightarrow> 'b formula  \<Rightarrow> v_truth"
where
   "t_v_evaluation I FF = Ffalse"
|  "t_v_evaluation I TT = Ttrue"
|  "t_v_evaluation I (atom p) = I p"
|  "t_v_evaluation I (\<not>. F) = (v_negation (t_v_evaluation I F))"
|  "t_v_evaluation I (F \<and>. G) = (v_conjunction (t_v_evaluation I F) (t_v_evaluation I G))"
|  "t_v_evaluation I (F \<or>. G) = (v_disjunction (t_v_evaluation I F) (t_v_evaluation I G))"
|  "t_v_evaluation I (F \<rightarrow>. G) = (v_implication (t_v_evaluation I F) (t_v_evaluation I G))"  


lemma Bivaluation:
shows "t_v_evaluation I F = Ttrue \<or>  t_v_evaluation I F = Ffalse"
(*<*)
proof(cases "t_v_evaluation I F")
  assume "t_v_evaluation I F = Ttrue" thus ?thesis by simp
  next  
  assume hip: "t_v_evaluation I F = Ffalse" thus ?thesis by simp
qed
(*>*)


lemma NegationValues1:
assumes "t_v_evaluation I (\<not>.F) = Ffalse"
shows "t_v_evaluation I F = Ttrue"
(*<*)
proof -
  { assume "t_v_evaluation I F \<noteq> Ttrue"
    hence "t_v_evaluation I F = Ffalse"  using Bivaluation by auto
    hence "t_v_evaluation I (\<not>.F) = Ttrue" by(simp add:v_negation_def)
    hence "False"
      using assms by auto}
  thus "t_v_evaluation I F = Ttrue" by auto
qed
(*>*)


lemma NegationValues2:
assumes "t_v_evaluation I (\<not>.F) = Ttrue"
shows "t_v_evaluation I F = Ffalse"
(*<*)
proof -
  { assume "t_v_evaluation I F \<noteq> Ffalse"
    hence "t_v_evaluation I F = Ttrue"  using Bivaluation by auto
    hence "t_v_evaluation I (\<not>.F) = Ffalse" by(simp add:v_negation_def)
    hence "False" using assms by auto}
  thus "t_v_evaluation I F = Ffalse" by auto
qed
(*>*)

lemma  non_Ttrue:
  assumes "t_v_evaluation I F \<noteq>  Ttrue" shows "t_v_evaluation I F = Ffalse"
(*<*)
proof(rule ccontr)
  assume "t_v_evaluation I F \<noteq> Ffalse"
  thus False using assms Bivaluation by auto
qed
(*>*)


lemma ConjunctionValues: 
  assumes "t_v_evaluation I (F \<and>. G) = Ttrue" 
  shows "t_v_evaluation I F = Ttrue \<and> t_v_evaluation I G = Ttrue"
(*<*)
proof - 
 { assume "\<not>(t_v_evaluation I  F = Ttrue \<and> t_v_evaluation I  G = Ttrue)" 
   hence "t_v_evaluation I  F \<noteq> Ttrue \<or> t_v_evaluation I G \<noteq> Ttrue" by simp
   hence "t_v_evaluation I  F = Ffalse \<or> t_v_evaluation I G = Ffalse" using Bivaluation by auto
   hence "t_v_evaluation I (F \<and>. G) = Ffalse" by(auto simp add: v_conjunction_def)
   hence "False" using assms by simp}    
 thus "t_v_evaluation I F = Ttrue \<and> t_v_evaluation I G = Ttrue" by auto
qed
(*>*)


lemma DisjunctionValues:
  assumes "t_v_evaluation I (F \<or>. G ) = Ttrue"
  shows "t_v_evaluation I  F = Ttrue \<or> t_v_evaluation I G = Ttrue" 
(*<*)
proof - 
 { assume "\<not>(t_v_evaluation I  F = Ttrue \<or> t_v_evaluation I G  = Ttrue)" 
   hence "t_v_evaluation I F  \<noteq> Ttrue \<and> t_v_evaluation I G \<noteq> Ttrue" by simp
   hence "t_v_evaluation I  F = Ffalse \<and> t_v_evaluation I G = Ffalse" using Bivaluation by auto
   hence "t_v_evaluation I (F \<or>. G) = Ffalse" by(simp add: v_disjunction_def)
   hence "False" using assms by simp}    
 thus "t_v_evaluation I F = Ttrue \<or> t_v_evaluation I G = Ttrue" by auto
qed
(*>*)


lemma ImplicationValues:
  assumes "t_v_evaluation I (F \<rightarrow>. G) = Ttrue"
  shows "t_v_evaluation I F = Ttrue \<longrightarrow> t_v_evaluation I G = Ttrue"
(*<*) 
proof - 
 { assume "\<not>(t_v_evaluation I F = Ttrue \<longrightarrow> t_v_evaluation I G = Ttrue)" 
   hence "t_v_evaluation I F =  Ttrue \<and> t_v_evaluation I G \<noteq> Ttrue" by simp
   hence "t_v_evaluation I F = Ttrue \<and> t_v_evaluation I G = Ffalse" using Bivaluation by auto
   hence "t_v_evaluation I (F \<rightarrow>. G) = Ffalse" by(simp add: v_implication_def)
   hence "False" using assms by simp}    
 thus "t_v_evaluation I F = Ttrue \<longrightarrow> t_v_evaluation I G = Ttrue" by auto
qed

lemma eval_false_implication:
  assumes "t_v_evaluation I (F \<rightarrow>.G) = Ffalse"
  shows "t_v_evaluation I F = Ttrue \<and> t_v_evaluation I G = Ffalse"
proof(rule ccontr) 
  assume "\<not> (t_v_evaluation I F = Ttrue \<and> t_v_evaluation I G = Ffalse)"
  hence "t_v_evaluation I F = Ffalse \<or> t_v_evaluation I G = Ttrue"
    using Bivaluation by auto 
  hence "t_v_evaluation I (F \<rightarrow>.G) = Ttrue"
    by(unfold t_v_evaluation_def, unfold v_implication_def, auto) 
  thus False using assms by auto
qed

(*>*)


definition model :: "('b \<Rightarrow> v_truth) \<Rightarrow> 'b formula set \<Rightarrow> bool" ("_ model _" [80,80] 80) where
 "I model S \<equiv> (\<forall>F \<in> S. t_v_evaluation I F = Ttrue)"


definition satisfiable :: "'b formula set \<Rightarrow> bool" where
 "satisfiable S \<equiv> (\<exists>v. v model S)"

(*<*)

lemma satisfiable_subset:
  assumes "satisfiable S" and "H\<subseteq>S"
  shows "satisfiable H"
proof(unfold satisfiable_def)
  show "\<exists>v. v model H"
  proof-
    have "\<exists>v. v model S" using assms(1) by(unfold satisfiable_def)
    then obtain v where v: "v model S" by auto
    have "v model H"
    proof(unfold model_def)
      show  "\<forall>F\<in>H. t_v_evaluation v F = Ttrue"
      proof
        fix F
        assume "F\<in>H"
        thus "t_v_evaluation v F = Ttrue" using assms(2) v by(unfold model_def, auto)
      qed
    qed
    thus ?thesis by auto
  qed
qed

(*>*)

  
definition consequence :: "'b formula set \<Rightarrow> 'b formula \<Rightarrow> bool" ("_ \<Turnstile> _" [80,80] 80) where
 "S \<Turnstile> F \<equiv> (\<forall>I. I model S \<longrightarrow> t_v_evaluation I F = Ttrue)"


(*<*)

lemma ConsSat:
  assumes "S \<Turnstile> F"
  shows "\<not> satisfiable (S \<union> {\<not>. F})"
proof(rule notI)
  assume "satisfiable (S \<union> {\<not>. F})"
  hence 1: "\<exists>I. I model (S \<union> {\<not>. F})" by (auto simp add: satisfiable_def) 
  obtain I where I: "I model (S \<union> {\<not>. F})" using 1 by auto
  hence 2: "\<forall>G\<in>(S \<union> {\<not>. F}). t_v_evaluation I G = Ttrue" 
    by (auto simp add: model_def)
  hence "\<forall>G\<in>S. t_v_evaluation I G = Ttrue" by blast
  moreover
  have 3: "t_v_evaluation I (\<not>. F) = Ttrue" using 2 by simp
  hence "t_v_evaluation I F = Ffalse" 
    proof (cases "t_v_evaluation I F")
      assume "t_v_evaluation I F = Ttrue" 
      thus ?thesis using 3 by(simp add:v_negation_def)
      next
      assume "t_v_evaluation I F = Ffalse" 
      thus ?thesis by simp
    qed
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
    have 1: "\<exists>I. I model S \<and> \<not>(t_v_evaluation I F = Ttrue)"  
      using hip by (simp add: consequence_def)
    obtain I where I: "I model S \<and> \<not>(t_v_evaluation I F = Ttrue)" using 1 by auto
    hence  "I model S" by simp
    hence 2: "\<forall>G\<in>S. t_v_evaluation I G = Ttrue" by (simp add: model_def) 
    have "\<not>(t_v_evaluation I F = Ttrue)" using I by simp
    hence 3: "t_v_evaluation I (\<not>. F) = Ttrue" by (simp add:v_negation_def)
    have  "\<forall>G\<in>(S \<union> {\<not>. F}). t_v_evaluation I G = Ttrue" 
    proof (rule ballI) 
      fix G 
      assume hip2: "G\<in>(S \<union> {\<not>. F})"    
      show "t_v_evaluation I G = Ttrue"
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
  "tautology F \<equiv> (\<forall>I. ((t_v_evaluation I F) = Ttrue))"

lemma "tautology (F  \<rightarrow>. (G \<rightarrow>. F))" 
proof - 
  have "\<forall>I. t_v_evaluation I (F \<rightarrow>. (G \<rightarrow>. F)) = Ttrue"
  proof 
    fix I
    show "t_v_evaluation I (F \<rightarrow>. (G \<rightarrow>. F)) = Ttrue"
    proof (cases "t_v_evaluation I F")
      text\<open> Caso 1: \<close>    
    { assume "t_v_evaluation I F = Ttrue"        
      thus ?thesis by (simp add: v_implication_def) }               
      next 
      text\<open> Caso 2: \<close> 
    { assume "t_v_evaluation I F = Ffalse"    
      thus ?thesis by(simp add: v_implication_def) }     
    qed 
  qed  
  thus ?thesis by (simp add: tautology_def)
qed



(*<*)


lemma empty_model: "\<forall>(I::'b \<Rightarrow> v_truth). I model {}"
proof - 
  have "\<forall>F\<in> {}. t_v_evaluation (I::'b \<Rightarrow> v_truth) F = Ttrue" by simp
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
     have "\<exists> I. t_v_evaluation I (F \<rightarrow>. G) \<noteq> Ttrue" 
       using h1 by (unfold tautology_def, auto) 
    then obtain I where "t_v_evaluation I (F \<rightarrow>. G) \<noteq> Ttrue" by auto 
    hence a: "t_v_evaluation I (F \<rightarrow>. G) = Ffalse" using Bivaluation by blast
    hence "t_v_evaluation I F = Ttrue \<and> t_v_evaluation I G = Ffalse" 
    proof -
     { assume "t_v_evaluation I F \<noteq> Ttrue \<or> t_v_evaluation I G \<noteq> Ffalse"
       hence "False"
       proof(rule disjE)
         assume "t_v_evaluation I F \<noteq> Ttrue"
         hence "t_v_evaluation I F = Ffalse" using Bivaluation by auto
         hence "t_v_evaluation I (F \<rightarrow>. G) = Ttrue" 
           by (auto simp add: v_implication_def)
         thus "False" using a by auto
       next
         assume "t_v_evaluation I G \<noteq> Ffalse"
         hence "t_v_evaluation I G = Ttrue" using Bivaluation by auto
         hence "t_v_evaluation I (F \<rightarrow>. G) = Ttrue" by( simp add: v_implication_def)
         thus "False" using a by auto
       qed}  
     thus "t_v_evaluation I F = Ttrue \<and> t_v_evaluation I G = Ffalse" by auto
   qed
   hence "t_v_evaluation I F = Ttrue \<and> t_v_evaluation I (\<not>.G) = Ttrue" 
     by (simp add:v_negation_def)
   hence "\<exists> I. I model {F, \<not>.G}" by (auto simp add: model_def)  
   thus "satisfiable {F, \<not>.G}" by(simp add: satisfiable_def)
 qed}
moreover
{ assume h2: "satisfiable {F, \<not>.G}" 
  have "\<not> tautology (F \<rightarrow>. G)" 
  proof -  
    have "\<exists> I. I model {F, \<not>.G}" using h2 by (simp add: satisfiable_def)  
    hence "\<exists> I. t_v_evaluation I F = Ttrue \<and> t_v_evaluation I (\<not>.G) = Ttrue" 
      by(simp add: model_def)
    then obtain I where I1: "t_v_evaluation I F = Ttrue" and I2: "t_v_evaluation I (\<not>.G) = Ttrue"
      by auto
    have "t_v_evaluation I G = Ffalse" using I2 NegationValues2 by auto   
    hence "t_v_evaluation I (F \<rightarrow>. G) = Ffalse" using I1 
      by (simp add: v_implication_def)
    thus "\<not> tautology (F \<rightarrow>. G)" by (auto, unfold tautology_def, auto)
  qed}
  ultimately
  show ?thesis by auto
qed

  
definition equivalent:: "'b formula  \<Rightarrow> 'b formula \<Rightarrow> bool" where
  "equivalent F G \<equiv> (\<forall> I. (t_v_evaluation I F) = (t_v_evaluation I G))"

primrec disjunction_atomic :: "'b list \<Rightarrow>'a \<Rightarrow> ('a \<times> 'b)formula"  where
 "disjunction_atomic [] i = FF"   
| "disjunction_atomic (x#D) i = (atom (i, x)) \<or>. (disjunction_atomic D i)"

lemma t_v_evaluation_disjunctions1:
  assumes "t_v_evaluation I (disjunction_atomic (a # l) i) = Ttrue"
  shows "t_v_evaluation I (atom (i,a)) = Ttrue \<or> t_v_evaluation I (disjunction_atomic l i) = Ttrue" 
proof-
  have
  "(disjunction_atomic (a # l) i) = (atom (i,a)) \<or>. (disjunction_atomic l i)"
    by auto
  hence "t_v_evaluation I ((atom (i ,a)) \<or>. (disjunction_atomic l i)) = Ttrue" 
    using assms by auto
  thus ?thesis using DisjunctionValues by blast
qed

lemma t_v_evaluation_atom:
  assumes "t_v_evaluation I (disjunction_atomic l i) = Ttrue"
  shows "\<exists>x. x \<in> set l \<and> (t_v_evaluation I (atom (i,x)) = Ttrue)"
proof-
  have "t_v_evaluation I (disjunction_atomic l i) = Ttrue \<Longrightarrow>
  \<exists>x. x \<in> set l \<and> (t_v_evaluation I (atom (i,x)) = Ttrue)"
  proof(induct l)
    case Nil
    then show ?case by auto
  next   
    case (Cons a l)  
    show  "\<exists>x. x \<in> set (a # l) \<and> t_v_evaluation I (atom (i,x)) = Ttrue"  
    proof-
      have
      "(t_v_evaluation I (atom (i,a)) = Ttrue) \<or> t_v_evaluation I (disjunction_atomic l i)=Ttrue" 
        using Cons(2) t_v_evaluation_disjunctions1[of I] by auto      
      thus ?thesis
    proof(rule disjE)
      assume "t_v_evaluation I (atom (i,a)) = Ttrue"
      thus ?thesis by auto
    next
      assume "t_v_evaluation I (disjunction_atomic l i) = Ttrue" 
      thus ?thesis using Cons by auto    
    qed
  qed
qed
  thus ?thesis using assms by auto
qed 

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s =  (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)


(*>*)
     
(*<*)
end
(*>*)