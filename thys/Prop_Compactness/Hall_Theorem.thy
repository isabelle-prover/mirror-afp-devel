(* Hall Theorem for countable families of finite sets
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiáis 
   Mauricio Ayala-Rincón           Universidade de Brasília
*) 
theory Hall_Theorem
  imports  
   "PropCompactness"
   "Marriage.Marriage" 
begin

section \<open> Hall Theorem for countable (infinite) families of sets \<close> 

text \<open>Hall's Theorem for countable families of sets is proved as a consequence of compactness theorem for propositional calculus (\cite{SARdL2022}). The theory imports Marriage theory from the AFP, which proves marriage theorem for the finite case. The proof also uses an updated version of Serrano's formalization of the compactness theorem for propositional logic. \<close> 

 definition system_representatives :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"system_representatives S I R  \<equiv> (\<forall>i\<in>I. (R i) \<in> (S i)) \<and> (inj_on R I)"

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s =  (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)

lemma list_to_set:
  assumes "finite (S i)"
  shows "set (set_to_list (S i)) = (S i)" 
  using assms  set_set_to_list  by auto

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

definition \<F> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> (('a \<times> 'b)formula) set"  where
   "\<F> S I  \<equiv> (\<Union>i\<in>I. { disjunction_atomic (set_to_list (S i)) i })"

definition \<G> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b)formula set"  where
   " \<G> S I \<equiv> {\<not>.(atom (i,x) \<and>. atom(i,y))
                         |x y i . x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I}"

definition \<H> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow>('a \<times> 'b)formula set"  where
   "\<H> S I \<equiv> {\<not>.(atom (i,x) \<and>. atom(j,x))
                         | x i j. x \<in> (S i) \<inter> (S j) \<and> (i\<in>I \<and> j\<in>I \<and> i\<noteq>j)}"

definition \<T> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b)formula set"  where
   "\<T> S I  \<equiv> (\<F> S I) \<union> (\<G> S I) \<union> (\<H> S I)" 

primrec indices_formula :: "('a \<times> 'b)formula  \<Rightarrow> 'a set" where
  "indices_formula FF = {}"
| "indices_formula TT = {}"
| "indices_formula (atom P) =  {fst P}"
| "indices_formula (\<not>. F) = indices_formula F"
| "indices_formula (F \<and>. G) = indices_formula F \<union> indices_formula G"
| "indices_formula (F \<or>. G) = indices_formula F \<union> indices_formula G"
| "indices_formula (F \<rightarrow>. G) = indices_formula F \<union> indices_formula G"

definition  indices_set_formulas :: "('a \<times> 'b)formula set  \<Rightarrow> 'a set" where
"indices_set_formulas S = (\<Union>F\<in> S. indices_formula F)"

lemma finite_indices_formulas:
  shows "finite (indices_formula F)"
  by(induct F, auto)

lemma finite_set_indices:
  assumes  "finite S"
  shows "finite (indices_set_formulas S)" 
 using `finite S` finite_indices_formulas 
  by(unfold indices_set_formulas_def, auto)

lemma indices_disjunction:
  assumes "F = disjunction_atomic L  i" and "L \<noteq> []"
  shows "indices_formula F = {i}" 
proof-
  have  "(F = disjunction_atomic L  i  \<and>  L \<noteq> []) \<Longrightarrow> indices_formula F = {i}"
  proof(induct L arbitrary: F)
    case Nil hence False using assms by auto
    thus ?case by auto
  next
    case(Cons a L)
    assume "F = disjunction_atomic (a # L) i \<and> a # L \<noteq> []" 
    thus ?case
    proof(cases L)
      assume "L = []"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
      thus "indices_formula F = {i}" using Cons(2) by auto
    next
      show
  "\<And>b list. F = disjunction_atomic (a # L) i \<and> a # L \<noteq> [] \<Longrightarrow> L = b # list \<Longrightarrow> 
            indices_formula F = {i}" 
        using Cons(1-2) by auto
    qed
  qed 
  thus ?thesis using assms  by auto
qed    

lemma nonempty_set_list:
  assumes "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)"     
  shows "\<forall>i\<in>I. set_to_list (S i)\<noteq>[]"  
proof(rule ccontr)
  assume "\<not> (\<forall>i\<in>I. set_to_list (S i) \<noteq> [])" 
  hence "\<exists>i\<in>I. set_to_list (S i) = []" by auto 
  hence "\<exists>i\<in>I. set(set_to_list (S i)) = {}" by auto
  then obtain i where i: "i\<in>I" and  "set (set_to_list (S i)) = {}" by auto
  thus False using list_to_set[of S i]  assms by auto
qed

lemma  at_least_subset_indices:
  assumes "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)"  
  shows  "indices_set_formulas (\<F> S I) \<subseteq> I" 
proof
  fix i
  assume hip: "i \<in> indices_set_formulas (\<F> S I)" show  "i \<in> I"
  proof-  
    have "i \<in> (\<Union>F\<in>(\<F> S I). indices_formula F)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "\<exists>F \<in> (\<F> S I). i \<in> indices_formula F" by auto
    then obtain F where "F\<in>(\<F> S I)" and i: "i \<in> indices_formula F" by auto
    hence "\<exists> k\<in>I. F = disjunction_atomic (set_to_list (S k)) k"
      by (unfold \<F>_def, auto) 
    then obtain k where
    k: "k\<in>I" and "F = disjunction_atomic (set_to_list (S k)) k" by auto
    hence "indices_formula F = {k}"
      using assms  nonempty_set_list[of I S] 
      indices_disjunction[OF `F = disjunction_atomic (set_to_list (S k))  k`]
      by auto
    hence "k = i" using i by auto
    thus ?thesis using k by auto
  qed
qed

lemma at_most_subset_indices:
  shows "indices_set_formulas (\<G> S I) \<subseteq> I"
proof
  fix i
  assume hip: "i \<in> indices_set_formulas (\<G> S I)" show  "i \<in> I"
  proof-
    have "i \<in> (\<Union>F\<in>(\<G> S I). indices_formula F)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "\<exists>F\<in>(\<G> S I). i \<in> indices_formula F" by auto
    then obtain F where "F\<in>(\<G> S I)" and i: "i \<in> indices_formula F"
      by auto
    hence "\<exists>x y j. x\<in>(S j) \<and> y\<in>(S j) \<and> x\<noteq>y \<and> j\<in>I \<and> F = 
           \<not>.(atom (j, x) \<and>. atom(j,y))"
      by (unfold \<G>_def, auto)
    then obtain x y j where "x\<in>(S j) \<and> y\<in>(S j) \<and> x\<noteq>y \<and> j\<in>I"
      and "F = \<not>.(atom (j, x) \<and>. atom(j,y))"
      by auto
    hence "indices_formula F = {j} \<and> j\<in>I" by auto
    thus "i \<in> I" using i by auto
  qed
qed

lemma  different_subset_indices:
  shows "indices_set_formulas (\<H> S I) \<subseteq> I" 
proof
  fix i
  assume hip: "i \<in> indices_set_formulas (\<H> S I)" show "i \<in> I"
  proof-
    have "i \<in> (\<Union>F\<in>(\<H> S I). indices_formula F)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "\<exists>F\<in>(\<H> S I) . i \<in> indices_formula F" by auto
    then obtain F where "F\<in>(\<H> S I)" and i: "i \<in> indices_formula F"
      by auto
    hence "\<exists> x j k. x \<in> (S j) \<inter> (S k) \<and> (j\<in>I \<and> k\<in>I \<and> j\<noteq>k) \<and> F =
           \<not>.(atom (j,x) \<and>. atom(k,x))"
      by (unfold \<H>_def, auto)
    then obtain x j k
      where "(j\<in>I \<and> k\<in>I \<and> j\<noteq>k) \<and> F = \<not>.(atom (j, x) \<and>. atom(k,x))"
      by auto
    hence u: "j\<in>I" and v: "k\<in>I" and "indices_formula F = {j,k}"
      by auto
    hence "i=j \<or> i=k"  using i by auto
    thus "i \<in> I" using u v  by auto
  qed
qed

lemma indices_union_sets:
  shows "indices_set_formulas(A \<union> B) = (indices_set_formulas A) \<union> (indices_set_formulas B)"
   by(unfold  indices_set_formulas_def, auto)

lemma at_least_subset_subset_indices1:
  assumes "F\<in>(\<F> S I)"
  shows "(indices_formula F) \<subseteq> (indices_set_formulas (\<F> S I))"
proof
  fix i 
  assume hip: "i \<in> indices_formula F"
  show  "i \<in> indices_set_formulas (\<F> S I)"
  proof-
    have "\<exists>F. F\<in>(\<F> S I) \<and> i \<in> indices_formula F" using assms hip by auto
    thus  ?thesis by(unfold indices_set_formulas_def, auto)
  qed
qed 

lemma at_most_subset_subset_indices1:
  assumes  "F\<in>(\<G> S I)"
  shows "(indices_formula F) \<subseteq> (indices_set_formulas (\<G> S I))" 
proof
  fix i 
  assume hip: "i \<in> indices_formula F"
  show  "i \<in> indices_set_formulas (\<G> S I)"
  proof-
    have "\<exists>F. F\<in>(\<G> S I) \<and> i \<in> indices_formula F" using assms hip by auto
    thus ?thesis by(unfold indices_set_formulas_def, auto)
  qed
qed

lemma different_subset_indices1:
  assumes  "F\<in>(\<H> S I)"
  shows "(indices_formula F) \<subseteq> (indices_set_formulas (\<H> S I))" 
proof
  fix i 
  assume hip: "i \<in> indices_formula F"
  show  "i \<in> indices_set_formulas (\<H> S I)"
  proof-
    have "\<exists>F. F\<in>(\<H> S I) \<and> i \<in> indices_formula F" using assms hip by auto
    thus ?thesis by(unfold indices_set_formulas_def, auto)
  qed
qed

lemma all_subset_indices:
  assumes  "\<forall>i\<in>I.(S i)\<noteq>{}" and "\<forall>i\<in>I. finite(S i)"
  shows "indices_set_formulas (\<T> S I) \<subseteq> I"
proof
  fix i
  assume hip: "i \<in> indices_set_formulas (\<T> S I)" show "i \<in> I"
  proof-
    have  "i \<in> indices_set_formulas ((\<F> S I) \<union> (\<G> S I)  \<union> (\<H> S I))"
      using hip by (unfold \<T>_def,auto)
    hence "i \<in> indices_set_formulas ((\<F> S I) \<union> (\<G> S I)) \<union>
    indices_set_formulas(\<H> S I)"
      using indices_union_sets[of "(\<F> S I) \<union> (\<G> S I)"] by auto
    hence "i \<in> indices_set_formulas ((\<F> S I) \<union> (\<G> S I)) \<or> 
    i \<in> indices_set_formulas(\<H> S I)"
      by auto
    thus ?thesis
    proof(rule disjE)        
      assume hip: "i \<in> indices_set_formulas (\<F> S I \<union> \<G> S I)"       
      hence "i \<in> (\<Union>F\<in> (\<F> S I) \<union> (\<G> S I). indices_formula F)"
        by(unfold  indices_set_formulas_def, auto)
      then obtain F
      where F: "F\<in>(\<F> S I) \<union> (\<G> S I)" and i: "i \<in> indices_formula F" by auto 
      from F have  "(indices_formula F) \<subseteq> (indices_set_formulas (\<F> S I))
      \<or> indices_formula F \<subseteq> (indices_set_formulas (\<G> S I))"
        using at_least_subset_subset_indices1 at_most_subset_subset_indices1 by blast
      hence "i \<in> indices_set_formulas (\<F> S I) \<or>
               i \<in> indices_set_formulas (\<G> S I)"
        using i by auto
      thus "i \<in> I" 
        using assms at_least_subset_indices[of I S] at_most_subset_indices[of S I] by auto
      next
      assume "i \<in> indices_set_formulas (\<H> S I)" 
      hence
      "i \<in> (\<Union>F\<in>(\<H> S I). indices_formula F)" 
        by(unfold  indices_set_formulas_def, auto)
      then obtain F where F:  "F\<in>(\<H> S I)" and i: "i \<in> indices_formula F"
        by auto
      from F have "(indices_formula F) \<subseteq> (indices_set_formulas (\<H> S I))"
        using different_subset_indices1 by blast
      hence "i \<in> indices_set_formulas (\<H> S I)" using i by auto
      thus "i \<in> I" using different_subset_indices[of S I]
        by auto
    qed
  qed
qed

lemma inclusion_indices:
  assumes "S \<subseteq> H" 
  shows  "indices_set_formulas S \<subseteq> indices_set_formulas H" 
proof
  fix i
  assume "i \<in> indices_set_formulas S"
  hence "\<exists>F. F \<in> S \<and> i \<in> indices_formula F"
    by(unfold indices_set_formulas_def, auto) 
  hence "\<exists>F. F \<in> H \<and> i \<in> indices_formula F" using assms by auto
  thus  "i \<in> indices_set_formulas H" 
    by(unfold indices_set_formulas_def, auto)
qed

lemma indices_subset_formulas:
  assumes  "\<forall>i\<in>I.(S i)\<noteq>{}" and "\<forall>i\<in>I. finite(S i)" and "A \<subseteq> (\<T> S I)" 
  shows "(indices_set_formulas A) \<subseteq> I" 
proof-
  have "(indices_set_formulas A) \<subseteq> (indices_set_formulas (\<T> S I))"
    using assms(3) inclusion_indices by auto
  thus ?thesis using assms(1-2) all_subset_indices[of I S] by auto
qed

lemma To_subset_all_its_indices:
  assumes  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and  "To \<subseteq> (\<T> S I)"
  shows "To \<subseteq> (\<T> S (indices_set_formulas To))"
proof
  fix F
  assume hip: "F \<in> To" 
  hence "F \<in> (\<T> S I)" using assms(3) by auto
  hence "F \<in> (\<F> S I) \<union> (\<G> S I) \<union> (\<H> S I)" by(unfold \<T>_def,auto)
  hence "F \<in> (\<F> S I) \<or> F \<in> (\<G> S I) \<or> F \<in> (\<H> S I)" by auto
  thus "F\<in>(\<T> S (indices_set_formulas To))"  
  proof(rule disjE)
    assume "F \<in> (\<F> S I)"
    hence "\<exists>i\<in>I. F =  disjunction_atomic (set_to_list (S i)) i" 
      by(unfold \<F>_def,auto)
    then obtain i
      where i: "i\<in>I" and F: "F =  disjunction_atomic (set_to_list (S i)) i"
      by auto
    hence "indices_formula F = {i}"
      using 
      assms(1-2) nonempty_set_list[of I S] indices_disjunction[of F "(set_to_list (S i))" i ]
      by auto
    hence "i\<in>(indices_set_formulas To)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "F\<in>(\<F> S (indices_set_formulas To))" 
      using F by(unfold \<F>_def,auto)
    thus "F\<in>(\<T> S (indices_set_formulas To))"
      by(unfold \<T>_def,auto)
  next
    assume "F \<in> (\<G> S I) \<or> F \<in> (\<H> S I)"
    thus ?thesis
    proof(rule disjE)
      assume "F \<in> (\<G> S I)" 
      hence "\<exists>x.\<exists>y.\<exists>i. F = \<not>.(atom (i,x) \<and>. atom(i,y)) \<and> x\<in>(S i) \<and>
               y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I"
        by(unfold \<G>_def, auto)
      then obtain x y i
        where F1: "F = \<not>.(atom (i,x) \<and>. atom(i,y))" and
                F2: "x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I"
        by auto
      hence "indices_formula F = {i}" by auto
      hence "i\<in>(indices_set_formulas To)" using hip
        by(unfold indices_set_formulas_def,auto)
      hence "F\<in>(\<G> S (indices_set_formulas To))"
        using F1 F2 by(unfold \<G>_def,auto)
      thus "F\<in>(\<T> S (indices_set_formulas To))"  by(unfold \<T>_def,auto)
    next
      assume "F \<in> (\<H> S I)"
      hence "\<exists>x.\<exists>i.\<exists>j. F = \<not>.(atom (i,x) \<and>. atom(j,x)) \<and> 
              x \<in> (S i) \<inter> (S j) \<and> (i\<in>I \<and> j\<in>I \<and> i\<noteq>j)" 
        by(unfold  \<H>_def, auto)
      then obtain x i j
        where F3: "F = \<not>.(atom (i,x) \<and>. atom(j,x))" and 
                F4: " x \<in> (S i) \<inter> (S j) \<and> (i\<in>I \<and> j\<in>I \<and> i\<noteq>j)" 
        by auto 
      hence "indices_formula F = {i,j}" by auto
      hence "i\<in>(indices_set_formulas To) \<and> j\<in>(indices_set_formulas To)" 
        using hip by(unfold indices_set_formulas_def,auto)
      hence "F\<in>(\<H> S (indices_set_formulas To))"
        using F3 F4 by(unfold \<H>_def,auto)
      thus "F\<in>(\<T> S (indices_set_formulas To))"  by(unfold \<T>_def,auto)
    qed
  qed
qed

lemma all_nonempty_sets:
  assumes  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "A \<subseteq> (\<T> S I)" 
  shows   "\<forall>i\<in>(indices_set_formulas A). (S i)\<noteq>{}"
proof-
  have "(indices_set_formulas A)\<subseteq>I" 
    using assms(1-3) indices_subset_formulas[of I S A] by auto
  thus ?thesis using assms(1) by auto
qed

lemma all_finite_sets:
  assumes  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "A \<subseteq> (\<T> S I)" 
shows  "\<forall>i\<in>(indices_set_formulas A). finite (S i)"
proof-
  have  "(indices_set_formulas A)\<subseteq>I" 
    using assms(1-3) indices_subset_formulas[of I S A] by auto
  thus  "\<forall>i\<in>(indices_set_formulas A). finite (S i)" using assms(2) by auto
qed

lemma all_nonempty_sets1:
  assumes  "\<forall>J\<subseteq>I. finite J \<longrightarrow>  card J \<le> card (\<Union> (S ` J))"
  shows "\<forall>i\<in>I. (S i)\<noteq>{}" using assms by auto

lemma system_distinct_representatives_finite:
  assumes
  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "To \<subseteq> (\<T> S I)"  and "finite To" 
   and "\<forall>J\<subseteq>(indices_set_formulas To). card J \<le> card (\<Union> (S ` J))"
 shows  "\<exists>R. system_representatives S (indices_set_formulas To) R" 
proof- 
  have 1: "finite (indices_set_formulas To)"
    using assms(4) finite_set_indices by auto
  have  "\<forall>i\<in>(indices_set_formulas To). finite (S i)"
    using all_finite_sets assms(1-3) by auto
  hence  "\<exists>R. (\<forall>i\<in>(indices_set_formulas To). R i \<in> S i) \<and> 
              inj_on R (indices_set_formulas To)" 
    using 1 assms(5) marriage_HV[of "(indices_set_formulas To)" S] by auto
  then obtain R 
    where R: "(\<forall>i\<in>(indices_set_formulas To). R i \<in> S i) \<and> 
              inj_on R (indices_set_formulas To)" by auto 
  thus ?thesis by(unfold system_representatives_def, auto)
qed

fun Hall_interpretation :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (('a \<times> 'b) \<Rightarrow> v_truth)"  where
"Hall_interpretation A \<I> R = (\<lambda>(i,x).(if  i \<in> \<I> \<and> x \<in> (A i) \<and> (R i) = x  then Ttrue else Ffalse))"

lemma t_v_evaluation_index:
  assumes  "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ttrue"
  shows  "(R i) = x"
proof(rule ccontr)
  assume  "(R i) \<noteq> x" hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) \<noteq> Ttrue" 
    by auto
  hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ffalse" 
  using non_Ttrue[of "Hall_interpretation S I R" "atom (i,x)"] by auto 
  thus False using assms by simp
qed

lemma distinct_elements_distinct_indices:
  assumes "F = \<not>.(atom (i,x) \<and>. atom(i,y))" and "x\<noteq>y"  
  shows "t_v_evaluation (Hall_interpretation S I R) F = Ttrue"
proof(rule ccontr)
  assume "t_v_evaluation (Hall_interpretation S I R) F \<noteq> Ttrue"
  hence
  "t_v_evaluation (Hall_interpretation S I R) (\<not>.(atom (i,x) \<and>. atom (i, y))) \<noteq> Ttrue" 
    using assms(1) by auto
  hence
  "t_v_evaluation (Hall_interpretation S I R) (\<not>.(atom (i,x) \<and>. atom (i, y))) = Ffalse"
    using
  non_Ttrue[of "Hall_interpretation S I R" "\<not>.(atom (i,x) \<and>. atom (i, y))"]
    by auto     
  hence  "t_v_evaluation (Hall_interpretation S I R) ((atom (i,x) \<and>. atom (i, y))) = Ttrue" 
    using
  NegationValues1[of "Hall_interpretation S I R" "(atom (i,x) \<and>. atom (i, y))"]
    by auto
  hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ttrue" and
  "t_v_evaluation (Hall_interpretation S I R) (atom (i, y)) = Ttrue"
    using
 ConjunctionValues[of "Hall_interpretation S I R" "atom (i,x)" "atom (i, y)"]
    by auto
  hence "(R i)= x" and "(R i)= y" using t_v_evaluation_index by auto
  hence "x=y" by auto
  thus False using assms(2) by auto
qed

lemma same_element_same_index:
  assumes
  "F = \<not>.(atom (i,x) \<and>. atom(j,x))"  and "i\<in>I \<and> j\<in>I" and "i\<noteq>j" and "inj_on R I"
  shows "t_v_evaluation (Hall_interpretation S I R) F = Ttrue"
proof(rule ccontr)
  assume "t_v_evaluation (Hall_interpretation S I R) F \<noteq> Ttrue"
  hence  "t_v_evaluation (Hall_interpretation S I R) (\<not>.(atom (i,x) \<and>. atom (j,x))) \<noteq> Ttrue"
    using assms(1) by auto
  hence
  "t_v_evaluation (Hall_interpretation S I R) (\<not>.(atom (i,x) \<and>. atom (j, x))) = Ffalse" using
  non_Ttrue[of "Hall_interpretation S I R" "\<not>.(atom (i,x) \<and>. atom (j, x))" ]
    by auto
  hence  "t_v_evaluation (Hall_interpretation S I R) ((atom (i,x) \<and>. atom (j, x))) = Ttrue" 
    using 
 NegationValues1[of "Hall_interpretation S I R" "(atom (i,x) \<and>. atom (j, x))"] 
    by auto
  hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ttrue" and
  "t_v_evaluation (Hall_interpretation S I R) (atom (j, x)) = Ttrue"
    using ConjunctionValues[of "Hall_interpretation S I R" "atom (i,x)" "atom (j,x)"]
    by auto
  hence  "(R i)= x"  and  "(R j)= x" using t_v_evaluation_index by auto
  hence "(R i) = (R j)" by auto
  hence "i=j" using  `i\<in>I \<and> j\<in>I` `inj_on R I` by(unfold inj_on_def, auto)
  thus False using  `i\<noteq>j`  by auto
qed

lemma disjunctor_Ttrue_in_atomic_disjunctions:
  assumes "x \<in> set l" and "t_v_evaluation I (atom (i,x)) = Ttrue"
  shows "t_v_evaluation I (disjunction_atomic l i) = Ttrue"
proof-
  have "x \<in> set l \<Longrightarrow> t_v_evaluation I (atom (i,x)) = Ttrue \<Longrightarrow>
  t_v_evaluation I (disjunction_atomic l i) = Ttrue" 
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    then show  "t_v_evaluation I (disjunction_atomic (a # l) i) = Ttrue"
    proof-
      have "x = a \<or> x\<noteq>a" by auto
      thus  "t_v_evaluation I (disjunction_atomic (a # l) i) = Ttrue"
      proof(rule disjE)
        assume "x = a"
          hence
          1:"(disjunction_atomic (a#l) i) = 
             (atom (i,x)) \<or>. (disjunction_atomic l i)"
          by auto 
        have "t_v_evaluation I ((atom (i,x)) \<or>. (disjunction_atomic l i)) = Ttrue"  
          using Cons(3)  by(unfold t_v_evaluation_def,unfold v_disjunction_def, auto)
        thus ?thesis using 1  by auto
      next
        assume "x \<noteq> a"
        hence "x\<in> set l" using Cons(2) by auto
        hence "t_v_evaluation I (disjunction_atomic l i ) = Ttrue"
          using Cons(1) Cons(3) by auto
        thus ?thesis
          by(unfold t_v_evaluation_def,unfold v_disjunction_def, auto)
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma t_v_evaluation_disjunctions:
  assumes  "finite (S i)"
  and  "x \<in> (S i)  \<and>  t_v_evaluation I (atom (i,x)) = Ttrue" 
  and  "F = disjunction_atomic (set_to_list (S i)) i " 
  shows "t_v_evaluation I F = Ttrue"
proof- 
  have "set (set_to_list (S i)) = (S i)" 
  using  set_set_to_list assms(1) by auto
  hence "x \<in> set (set_to_list (S i))"
    using assms(2) by auto
  thus "t_v_evaluation I F = Ttrue"
    using assms(2-3) disjunctor_Ttrue_in_atomic_disjunctions by auto
qed

theorem SDR_satisfiable:
  assumes "\<forall>i\<in>\<I>. (A i) \<noteq> {}"  and  "\<forall>i\<in>\<I>. finite (A i)" and  "X \<subseteq> (\<T> A \<I>)"
  and  "system_representatives A \<I> R"  
shows "satisfiable X"
proof- 
  have "satisfiable (\<T> A \<I>)"
  proof-
    have "inj_on R \<I>" using assms(4) system_representatives_def[of A \<I> R] by auto
    have "(Hall_interpretation A \<I> R) model (\<T> A \<I>)"
    proof(unfold model_def) 
      show "\<forall>F \<in> (\<T> A \<I>). t_v_evaluation (Hall_interpretation A \<I> R) F = Ttrue"
      proof 
        fix F assume "F \<in> (\<T> A \<I>)"
        show  "t_v_evaluation (Hall_interpretation A \<I> R) F  = Ttrue"
        proof-
          have "F \<in> (\<F> A \<I>) \<union> (\<G> A \<I>) \<union> (\<H> A \<I>)" 
            using  `F \<in> (\<T> A \<I>)` assms(3)  by(unfold \<T>_def,auto) 
          hence  "F \<in> (\<F> A \<I>) \<or> F \<in> (\<G> A \<I>) \<or> F \<in> (\<H> A \<I>)" by auto  
          thus ?thesis
          proof(rule disjE) 
            assume "F \<in> (\<F> A \<I>)"
            hence "\<exists>i\<in>\<I>. F =  disjunction_atomic (set_to_list (A i)) i" 
              by(unfold \<F>_def,auto)
            then obtain i
              where i: "i\<in>\<I>" and F: "F =  disjunction_atomic (set_to_list (A i)) i"
              by auto
            have 1: "finite (A i)" using i  assms(2) by auto
            have 2: " i \<in> \<I> \<and> (R i) \<in> (A i)" 
              using i assms(4) by (unfold system_representatives_def, auto)
            hence "t_v_evaluation (Hall_interpretation A \<I> R) (atom (i,(R i))) = Ttrue"
              by auto 
            thus "t_v_evaluation (Hall_interpretation A \<I> R) F  = Ttrue"
              using 1 2 assms(4) F           
            t_v_evaluation_disjunctions
            [of A i "(R i)" "(Hall_interpretation A \<I> R)" F]
              by auto
          next
            assume "F \<in> (\<G> A \<I>) \<or> F \<in> (\<H> A \<I>)"
            thus ?thesis
            proof(rule disjE)
              assume "F \<in> (\<G> A \<I>)"
              hence
            "\<exists>x.\<exists>y.\<exists>i. F = \<not>.(atom (i,x) \<and>. atom(i,y)) \<and> x\<in>(A i) \<and>
              y\<in>(A i) \<and>  x\<noteq>y \<and> i\<in>\<I>"
                by(unfold \<G>_def, auto)
              then obtain x y i
                where F: "F = \<not>.(atom (i,x) \<and>. atom(i,y))" 
            and "x\<in>(A i) \<and> y\<in>(A i) \<and>  x\<noteq>y \<and> i\<in>\<I>"
                by auto
          thus "t_v_evaluation (Hall_interpretation A \<I> R) F  = Ttrue"
            using `inj_on R \<I>` distinct_elements_distinct_indices[of F i x y A \<I> R] by auto
          next
              assume "F \<in> (\<H> A \<I>)"
              hence "\<exists>x.\<exists>i.\<exists>j. F = \<not>.(atom (i,x) \<and>. atom(j,x)) \<and>
                   x \<in> (A i) \<inter> (A j) \<and> (i\<in>\<I> \<and> j\<in>\<I> \<and> i\<noteq>j)" 
                 by(unfold  \<H>_def, auto)
              then obtain x i j
              where "F = \<not>.(atom (i,x) \<and>. atom(j,x))"  and "(i\<in>\<I> \<and> j\<in>\<I> \<and> i\<noteq>j)" 
                 by auto
              thus "t_v_evaluation (Hall_interpretation A \<I> R) F  = Ttrue" using `inj_on R \<I>`
              same_element_same_index[of F i x j \<I> ]  by auto             
            qed
          qed
        qed
      qed
    qed
    thus "satisfiable (\<T> A \<I>)" by(unfold satisfiable_def, auto)
  qed 
  thus "satisfiable X" using satisfiable_subset assms(3) by auto
qed 

lemma finite_is_satisfiable:
  assumes
  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "To \<subseteq> (\<T> S I)"  and  "finite To"
  and "\<forall>J\<subseteq>(indices_set_formulas To). card J \<le> card (\<Union> (S ` J))"
shows  "satisfiable To"
proof- 
  have 0: "\<exists>R. system_representatives S (indices_set_formulas To) R" 
    using assms system_distinct_representatives_finite[of I S To] by auto
  then obtain R
    where R: "system_representatives S (indices_set_formulas To) R" by auto
  have 1: "\<forall>i\<in>(indices_set_formulas To). (S i)\<noteq>{}" 
    using assms(1-3) all_nonempty_sets  by blast
  have 2: "\<forall>i\<in>(indices_set_formulas To). finite (S i)" 
    using assms(1-3) all_finite_sets by blast
  have 3: "To\<subseteq>(\<T> S (indices_set_formulas To))"
    using assms(1-3) To_subset_all_its_indices[of I S To] by auto 
  thus  "satisfiable To"
    using  1 2 3 0 SDR_satisfiable by auto
qed

lemma diag_nat:
  shows "\<forall>y z.\<exists>x. (y,z) = diag x" 
  using enumeration_natxnat by(unfold enumeration_def,auto)

lemma EnumFormulasHall:
  assumes "\<exists>g. enumeration (g:: nat \<Rightarrow>'a)" and "\<exists>h. enumeration (h:: nat \<Rightarrow>'b)"
  shows "\<exists>f. enumeration (f:: nat \<Rightarrow>('a \<times>'b )formula)"
proof-
  from assms(1) obtain g where e1: "enumeration (g:: nat \<Rightarrow>'a)" by auto  
  from assms(2) obtain h where e2: "enumeration (h:: nat \<Rightarrow>'b)" by auto  
  have "enumeration ((\<lambda>m.(g(fst(diag m)),(h(snd(diag m))))):: nat \<Rightarrow>('a \<times>'b))"
  proof(unfold enumeration_def) 
    show  "\<forall>y::('a \<times> 'b). \<exists>m. y = (g (fst (diag m)), h (snd (diag m)))"  
    proof
      fix y::"('a \<times>'b )" 
      show "\<exists>m. y = (g (fst (diag m)), h (snd (diag m)))"
      proof-
        have  "y = ((fst y), (snd y))" by auto
        from e1 have  "\<forall>w::'a. \<exists>n1. w = (g n1)" by(unfold enumeration_def, auto)
        hence "\<exists>n1. (fst y) = (g n1)" by auto
        then obtain n1 where n1: "(fst y) = (g n1)" by auto 
        from e2 have  "\<forall>w::'b. \<exists>n2. w = (h n2)" by(unfold enumeration_def, auto)
        hence "\<exists>n2. (snd y) = (h n2)" by auto
        then obtain n2 where n2: "(snd y) = (h n2)" by auto
        have "\<exists>m. (n1, n2) = diag m" using diag_nat by auto
        hence "\<exists>m. (n1, n2) = (fst (diag m), snd (diag m))" by simp
        hence "\<exists>m.((fst y), (snd y)) = (g(fst (diag m)), h(snd (diag m)))"
          using n1 n2 by blast
        thus "\<exists>m. y = (g (fst (diag m)), h(snd (diag m)))" by auto
      qed
    qed
  qed
  thus "\<exists>f. enumeration (f:: nat \<Rightarrow>('a \<times>'b )formula)" 
    using EnumerationFormulasP1 by auto 
qed

theorem all_formulas_satisfiable:
  fixes S :: "('a::countable \<Rightarrow> 'b::countable set)" and I :: "'a set"
  assumes "\<forall>i\<in>(I::'a set). finite (S i)" and "\<forall>J\<subseteq>I. finite J \<longrightarrow>  card J \<le> card (\<Union> (S ` J))"
  shows "satisfiable (\<T> S I)"
proof-
  have "\<forall> A. A \<subseteq> (\<T> S I) \<and> (finite A) \<longrightarrow> satisfiable A"
  proof(rule allI, rule impI) 
    fix A assume "A \<subseteq> (\<T> S I) \<and> (finite A)"
    hence hip1:  "A \<subseteq> (\<T> S I)" and  hip2: "finite A" by auto
    show "satisfiable A"
    proof -
      have 0: "\<forall>i\<in>I. (S i)\<noteq>{}" using assms(2) all_nonempty_sets1 by auto
      hence 1: "(indices_set_formulas A)\<subseteq>I"  
        using assms(1) hip1 indices_subset_formulas[of I S A] by auto
      have 2: "finite (indices_set_formulas A)" 
        using hip2 finite_set_indices by auto
      have 3: "card (indices_set_formulas A) \<le> card(\<Union> (S `(indices_set_formulas A)))"
        using 1 2 assms(2) by auto
      have "\<forall>J\<subseteq>(indices_set_formulas A). card J \<le> card(\<Union> (S ` J))"
      proof(rule allI)
        fix J
        show "J \<subseteq> indices_set_formulas A \<longrightarrow> card J \<le> card (\<Union> (S ` J)) "
        proof(rule impI)
          assume hip: "J\<subseteq>(indices_set_formulas A)"              
          hence 4: "finite J" 
            using 2  rev_finite_subset by auto 
          have "J\<subseteq>I" using hip 1 by auto
          thus "card J \<le> card (\<Union> (S ` J))" using 4  assms(2) by auto      
        qed
      qed
      thus "satisfiable A"
        using 0 assms(1) hip1 hip2 finite_is_satisfiable[of I S A]  by auto
    qed
  qed
  thus "satisfiable (\<T> S I)" 
    using Compactness_Theorem by auto
qed

fun SDR ::  "(('a \<times> 'b) \<Rightarrow> v_truth) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow>'b )"
  where
"SDR M S I = (\<lambda>i. (THE x. (t_v_evaluation M (atom (i,x)) = Ttrue) \<and> x\<in>(S i)))"

lemma existence_representants:
 assumes "i \<in> I" and "M model (\<F> S I)" and "finite(S i)"  
  shows "\<exists>x. (t_v_evaluation M (atom (i,x)) = Ttrue) \<and>  x \<in> (S i)" 
proof- 
  from  `i \<in> I`  
  have  "(disjunction_atomic (set_to_list (S i)) i) \<in> (\<F> S I)" 
    by(unfold \<F>_def,auto)
  hence "t_v_evaluation M (disjunction_atomic(set_to_list (S i)) i) = Ttrue"
    using assms(2) model_def[of M "\<F> S I"] by auto 
  hence 1: "\<exists>x. x \<in> set (set_to_list (S i)) \<and> (t_v_evaluation M (atom (i,x)) = Ttrue)"
    using t_v_evaluation_atom[of M "(set_to_list (S i))" i] by auto
  thus  "\<exists>x. (t_v_evaluation M (atom (i,x)) = Ttrue) \<and>  x \<in> (S i)" 
    using   `finite(S i)` set_set_to_list[of "(S i)"] by auto
qed

lemma unicity_representants:
  shows  "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow>
          (\<not>.(atom (i,x) \<and>. atom(i,y))\<in> (\<G> S I))"
proof(rule allI) 
  fix y
  show "x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I \<longrightarrow> 
       (\<not>.(atom (i,x) \<and>. atom(i,y))\<in> (\<G> S I))"
  proof(rule impI)
    assume "x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I"
    thus  "\<not>.(atom (i,x) \<and>. atom(i,y)) \<in> (\<G> S I)"
   by(unfold \<G>_def, auto)
  qed
qed

lemma unicity_selection_representants:
 assumes "i \<in> I" and "M model (\<G> S I)" 
  shows  "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(i,y))) = Ttrue)"
proof-
  have   "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (\<not>.(atom (i,x) \<and>. atom(i,y))\<in> (\<G> S I))"
    using unicity_representants[of x S i] by auto
  thus  "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(i,y))) = Ttrue)"
    using assms(2)  model_def[of M "\<G> S I"] by blast
qed

lemma uniqueness_satisfaction:
  assumes "t_v_evaluation M (atom (i,x)) = Ttrue \<and> x\<in>(S i)" and
  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y  \<longrightarrow>  t_v_evaluation M (atom (i, y)) = Ffalse"  
shows "\<forall>z. t_v_evaluation M (atom (i, z)) = Ttrue \<and> z\<in>(S i) \<longrightarrow> z = x"
proof(rule allI)
  fix z 
  show "t_v_evaluation M (atom (i, z)) = Ttrue \<and> z \<in> S i  \<longrightarrow> z = x" 
  proof(rule impI)
    assume hip: "t_v_evaluation M (atom (i, z)) = Ttrue \<and> z \<in> (S i)"  
    show "z = x"
    proof(rule ccontr)
      assume 1: "z \<noteq> x"
      have   2: "z \<in> (S i)" using hip by auto
      hence  "t_v_evaluation M (atom(i,z)) =  Ffalse" using 1 assms(2) by auto
      thus False using hip by auto
    qed
  qed
qed

lemma uniqueness_satisfaction_in_Si:
  assumes "t_v_evaluation M (atom (i,x)) = Ttrue \<and> x\<in>(S i)" and
  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y \<longrightarrow> (t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(i,y))) = Ttrue)"
  shows "\<forall>y. y \<in> (S i)  \<and> x\<noteq>y  \<longrightarrow>  t_v_evaluation M (atom (i, y)) = Ffalse"
proof(rule allI, rule impI)
  fix y
  assume hip: "y \<in> S i \<and> x \<noteq> y"
  show "t_v_evaluation M (atom (i, y)) = Ffalse"
  proof(rule ccontr)
    assume "t_v_evaluation M (atom (i, y)) \<noteq> Ffalse" 
    hence "t_v_evaluation M (atom (i, y)) = Ttrue" using  Bivaluation by blast
    hence 1: "t_v_evaluation M (atom (i,x) \<and>. atom(i,y))  = Ttrue"
      using assms(1) v_conjunction_def by auto
    have "t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(i,y))) = Ttrue"
      using hip assms(2) by auto
    hence "t_v_evaluation M (atom (i,x) \<and>. atom(i,y)) = Ffalse" 
      using NegationValues2  by blast
    thus False using 1  by auto
  qed      
qed

lemma uniqueness_aux1:
  assumes  "t_v_evaluation M (atom (i,x)) = Ttrue \<and> x\<in>(S i)"
  and  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y \<longrightarrow> (t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(i,y))) = Ttrue)"
shows "\<forall>z. t_v_evaluation M (atom (i, z)) = Ttrue \<and> z\<in>(S i) \<longrightarrow> z = x" 
  using assms uniqueness_satisfaction_in_Si[of M i x ]  uniqueness_satisfaction[of M i x] by blast 

lemma uniqueness_aux2:
  assumes "t_v_evaluation M (atom (i,x)) = Ttrue \<and> x\<in>(S i)" and
  "(\<And>z.(t_v_evaluation M (atom (i, z)) = Ttrue \<and> z\<in>(S i))  \<Longrightarrow> z = x)"
shows "(THE a. (t_v_evaluation M (atom (i,a)) = Ttrue) \<and> a\<in>(S i)) = x" 
  using assms by(rule the_equality)

lemma uniqueness_aux:
  assumes  "t_v_evaluation M (atom (i,x)) = Ttrue \<and> x\<in>(S i)" and
  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y \<longrightarrow> (t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(i,y))) = Ttrue)"
shows  "(THE a. (t_v_evaluation M (atom (i,a)) = Ttrue) \<and> a\<in>(S i)) = x" 
  using assms  uniqueness_aux1[of M i x ] uniqueness_aux2[of M i x] by blast

lemma function_SDR:
  assumes "i \<in> I" and "M model (\<F> S I)" and "M model (\<G> S I)" and "finite(S i)"
shows "\<exists>!x. (t_v_evaluation M (atom (i,x)) = Ttrue) \<and>  x \<in> (S i) \<and> (SDR  M S I i) = x" 
proof- 
  have  "\<exists>x. (t_v_evaluation M (atom (i,x)) = Ttrue) \<and>  x \<in> (S i)" 
    using assms(1-2,4) existence_representants by auto 
  then obtain x where x: "(t_v_evaluation M (atom (i,x)) = Ttrue) \<and>  x \<in> (S i)"
    by auto
  moreover
  have "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(i,y))) = Ttrue)" 
    using assms(1,3) unicity_selection_representants[of i I M S]  by auto
  hence "(THE a. (t_v_evaluation M (atom (i,a)) = Ttrue) \<and> a\<in>(S i)) = x"
   using x  `i \<in> I`  uniqueness_aux[of M i x] by auto 
  hence "SDR M S I i = x"  by auto
  hence "(t_v_evaluation M (atom (i,x)) = Ttrue \<and> x \<in> (S i)) \<and>  SDR M S I i = x"
    using x by auto
  thus ?thesis  by auto
qed

lemma aux_for_\<H>_formulas:
  assumes
  "(t_v_evaluation M (atom (i,a)) = Ttrue) \<and> a \<in> (S i)"
  and "(t_v_evaluation M (atom (j,b)) = Ttrue) \<and> b \<in> (S j)" 
  and  "i\<in>I \<and> j\<in>I \<and> i\<noteq>j" 
  and "(a \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j \<longrightarrow>
  (t_v_evaluation M (\<not>.(atom (i,a) \<and>. atom(j,a))) = Ttrue))"
  shows  "a \<noteq> b"
proof(rule ccontr)
  assume  "\<not> a \<noteq> b" 
  hence hip: "a=b" by auto
  hence "t_v_evaluation M (atom (i, a)) = Ttrue" and  "t_v_evaluation M (atom (j, a)) = Ttrue"
    using assms by auto
  hence "t_v_evaluation M (atom (i, a) \<and>. atom(j,a)) = Ttrue" using v_conjunction_def
    by auto
  hence "t_v_evaluation M (\<not>.(atom (i, a) \<and>. atom(j,a))) = Ffalse" 
    using v_negation_def by auto
  moreover
  have  "a \<in> (S i) \<inter> (S j)" using hip assms(1-2) by auto
  hence "t_v_evaluation M (\<not>.(atom (i, a) \<and>. atom(j, a))) = Ttrue" 
    using assms(3-4) by auto
  ultimately show False by auto
qed

lemma model_of_all:
  assumes  "M model (\<T> S I)"
  shows  "M model (\<F> S I)" and  "M model (\<G> S I)" and  "M model (\<H> S I)" 
proof(unfold model_def)
  show "\<forall>F\<in>\<F> S I. t_v_evaluation M F = Ttrue"
  proof
    fix F
    assume "F\<in> (\<F> S I)" hence "F\<in>(\<T> S I)" by(unfold \<T>_def, auto) 
    thus "t_v_evaluation M F = Ttrue" using assms by(unfold model_def, auto)
  qed
next
  show "\<forall>F\<in>(\<G> S I). t_v_evaluation M F = Ttrue"
  proof
    fix F
    assume "F\<in>(\<G> S I)" hence "F\<in>(\<T> S I)" by(unfold \<T>_def, auto) 
    thus "t_v_evaluation M F = Ttrue" using assms by(unfold model_def, auto)
  qed
next
  show "\<forall>F\<in>(\<H> S I). t_v_evaluation M F = Ttrue"
  proof
    fix F
    assume "F\<in>(\<H> S I)" hence "F\<in>(\<T> S I)" by(unfold \<T>_def, auto) 
    thus "t_v_evaluation M F = Ttrue" using assms by(unfold model_def, auto)
  qed
qed

lemma sets_have_distinct_representants:
  assumes
  hip1: "i\<in>I" and  hip2: "j\<in>I" and  hip3: "i\<noteq>j" and  hip4: "M model (\<T> S I)"
  and hip5: "finite(S i)" and  hip6: "finite(S j)"
  shows " SDR M S I i  \<noteq>  SDR M S I j" 
proof-
  have 1: "M model \<F> S I" and 2:  "M model \<G> S I"
    using hip4 model_of_all by auto
  hence "\<exists>!x. (t_v_evaluation M (atom (i,x)) = Ttrue) \<and> x \<in> (S i) \<and>  SDR M S I i = x"
    using  hip1  hip4  hip5 function_SDR[of i I M S] by auto  
  then obtain x where
  x1: "(t_v_evaluation M (atom (i,x)) = Ttrue) \<and> x \<in> (S i)" and x2: "SDR M S I i = x"
    by auto 
  have "\<exists>!y. (t_v_evaluation M (atom (j,y)) = Ttrue) \<and> y \<in> (S j) \<and> SDR M S I j = y"
  using 1 2  hip2  hip4  hip6 function_SDR[of j I M S] by auto   
  then obtain y where
  y1: "(t_v_evaluation M (atom (j,y)) = Ttrue) \<and> y \<in> (S j)" and y2: "SDR M S I j = y"
    by auto
  have "(x \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j) \<longrightarrow>
  (\<not>.(atom (i,x) \<and>. atom(j,x))\<in> (\<H> S I))"
    by(unfold  \<H>_def, auto)
  hence "(x \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j) \<longrightarrow>
  (\<not>.(atom (i,x) \<and>. atom(j,x)) \<in> (\<T> S I))"
    by(unfold  \<T>_def, auto)
  hence "(x \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j) \<longrightarrow>
  (t_v_evaluation M (\<not>.(atom (i,x) \<and>. atom(j,x))) = Ttrue)" 
    using hip4 model_def[of M "\<T> S I"] by auto
  hence "x \<noteq> y" using x1 y1 assms(1-3) aux_for_\<H>_formulas[of M i x  S  j y I] 
    by auto
  thus ?thesis using x2 y2 by auto
qed  

lemma satisfiable_representant:
  assumes "satisfiable (\<T> S I)" and "\<forall>i\<in>I. finite (S i)"
  shows "\<exists>R. system_representatives S I R"
proof-
  from assms have "\<exists>M. M model (\<T> S I)"  by(unfold satisfiable_def)
  then obtain M where M: "M model (\<T> S I)" by auto 
  hence  "system_representatives S I (SDR M S I)" 
  proof(unfold system_representatives_def) 
    show "(\<forall>i\<in>I. (SDR M S I i) \<in> (S i)) \<and> inj_on (SDR M S I) I" 
    proof(rule conjI)
      show "\<forall>i\<in>I. (SDR M S I i) \<in> (S i)"
      proof 
        fix i
        assume i: "i \<in> I"
        have "M model \<F> S I" and 2: "M model \<G> S I" using M model_of_all
          by auto
        thus "(SDR M S I i) \<in> (S i)"
          using i M assms(2) model_of_all[of M S I]
                  function_SDR[of i I M S ] by auto 
      qed
    next
      show "inj_on (SDR M S I) I"
      proof(unfold  inj_on_def)
        show "\<forall>i\<in>I. \<forall>j\<in>I. SDR M S I i = SDR M S I j \<longrightarrow> i = j"
        proof 
          fix i 
          assume 1:  "i \<in> I"
          show "\<forall>j\<in>I. SDR M S I i = SDR M S I j \<longrightarrow> i = j"
          proof 
            fix j
            assume 2:  "j \<in> I"
            show "SDR M S I i = SDR M S I j \<longrightarrow> i = j"
            proof(rule ccontr)
              assume  "\<not> (SDR M S I i = SDR M S I j \<longrightarrow> i = j)"
              hence 5:  "SDR M S I i = SDR M S I j" and 6:  "i\<noteq> j" by auto
              have  3: "finite(S i)" and 4: "finite(S j)" using 1 2  assms(2) by auto
              have "SDR M S I i \<noteq> SDR M S I j"
                using 1 2 3 4 6 M sets_have_distinct_representants[of i I j M S] by auto
              thus False  using 5 by auto
            qed
          qed 
        qed
      qed
    qed
  qed
  thus  "\<exists>R. system_representatives S I R" by auto
qed

theorem Hall:
  fixes S :: "('a::countable \<Rightarrow> 'b::countable set)" and I :: "'a set"
  assumes Finite: "\<forall>i\<in>I. finite (S i)"
  and Marriage: "\<forall>J\<subseteq>I. finite J \<longrightarrow>  card J \<le> card (\<Union> (S ` J))"
 shows "\<exists>R. system_representatives S I R"
proof-  
  have "satisfiable (\<T> S I)" using assms all_formulas_satisfiable[of I] by auto
  thus ?thesis using Finite Marriage satisfiable_representant[of S I] by auto
qed

theorem marriage_necessity:
  fixes A :: "'a \<Rightarrow> 'b set" and I :: "'a set"
  assumes "\<forall> i\<in>I. finite (A i)"
  and "\<exists>R. (\<forall>i\<in>I. R i \<in> A i) \<and> inj_on R I" (is "\<exists>R. ?R R A & ?inj R A")
  shows "\<forall>J\<subseteq>I. finite J \<longrightarrow> card J \<le> card (\<Union>(A ` J))"
proof clarify
  fix J
  assume "J \<subseteq> I" and 1: "finite J"
  show "card J \<le> card (\<Union>(A ` J))"
  proof-
    from assms(2) obtain R where "?R R A" and "?inj R A" by auto
    have "inj_on R J" by(rule subset_inj_on[OF \<open>?inj R A\<close> \<open>J\<subseteq>I\<close>])
    moreover have "(R ` J) \<subseteq> (\<Union>(A ` J))" using \<open>J\<subseteq>I\<close> \<open>?R R A\<close> by auto
    moreover have "finite (\<Union>(A ` J))" using \<open>J\<subseteq>I\<close> 1 assms
      by auto
    ultimately show ?thesis by (rule card_inj_on_le)
  qed
qed

end
