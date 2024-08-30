(*  Formalization of König Lemma
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiáis 
   Mauricio Ayala-Rincón           Universidade de Brasília
*)

(*<*)
theory KoenigLemma
 imports PropCompactness  
begin
(*>*)

section \<open>König Lemma\<close>

text\<open>This section formalizes König Lemma from the compactness theorem for propositional logic directly. \<close>


type_synonym 'a rel = "('a \<times> 'a) set"

definition irreflexive_on ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
 where "irreflexive_on A r \<equiv>  (\<forall>x\<in>A. (x, x) \<notin> r)"

definition transitive_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "transitive_on A r \<equiv>
 (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"

definition total_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "total_on A r \<equiv> (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"

definition minimum ::  "'a set \<Rightarrow> 'a \<Rightarrow>'a rel \<Rightarrow> bool"
  where "minimum A a r \<equiv>  (a\<in>A \<and> (\<forall>x\<in>A. x \<noteq> a  \<longrightarrow> (a,x) \<in> r))"

definition predecessors :: "'a set \<Rightarrow>'a \<Rightarrow>'a rel  \<Rightarrow> 'a set"
  where "predecessors A a r \<equiv> {x\<in>A.(x, a) \<in> r}"

definition height ::  "'a set \<Rightarrow>'a \<Rightarrow> 'a rel \<Rightarrow> nat"
  where "height A a r   \<equiv>  card (predecessors A a r)"

definition level ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow>'a set"
  where "level A r n \<equiv> {x\<in>A. height A x r = n}"

definition imm_successors ::  "'a set \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a set"
  where "imm_successors A a r \<equiv> 
 {x\<in>A. (a,x)\<in> r \<and> height A x r = (height A a r)+1}" 

definition strict_part_order ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where  "strict_part_order A r \<equiv> irreflexive_on A r \<and> transitive_on A r"

lemma minimum_element:
  assumes  "strict_part_order A r" and "minimum A a r" and "r={}"
  shows "A={a}"
proof(rule ccontr)
  assume hip: "A \<noteq> {a}" show False
  proof(cases)
    assume  hip1: "A={}"
    have "a\<in>A" using `minimum A a r` by(unfold minimum_def, auto) 
    thus False using hip1 by auto
  next
    assume  "A \<noteq> {}"
    hence "\<exists>x. x\<noteq>a \<and> x\<in>A" using hip by auto
    then obtain x where  "x\<noteq>a \<and> x\<in>A" by auto
    hence "(a,x)\<in>r"  using `minimum A a r` by(unfold minimum_def, auto)
    hence "r \<noteq> {}" by auto
    thus False using `r={}` by auto
  qed
qed

lemma spo_uniqueness_min:
  assumes  "strict_part_order A r" and  "minimum A a r" and "minimum A b r" 
  shows "a=b"
proof(rule ccontr)
  assume hip: "a \<noteq> b"
  have "a\<in>A"and "b\<in>A" using assms(2-3) by(unfold minimum_def, auto)
  show False
  proof(cases)
    assume "r = {}"
    hence  "A={a} \<and> A={b}"  using assms(1-3) minimum_element[of A r] by auto
    thus False using hip by auto
  next
    assume "r\<noteq>{}"
    hence 1: "(a,b)\<in>r \<and> (b,a)\<in>r" using hip assms(2-3)
      by(unfold minimum_def, auto)    
    have  irr: "irreflexive_on A r" and tran: "transitive_on A r"     
    using assms(1) by(unfold strict_part_order_def, auto)
    have  "(a,a)\<in>r" using  `a\<in>A`  `b\<in>A` 1 tran by(unfold transitive_on_def, blast)
    thus False using  `a\<in>A`  irr  by(unfold irreflexive_on_def, blast)
  qed
qed

lemma emptyness_pred_min_spo:
  assumes  "minimum A a r" and "strict_part_order A r"
  shows  "predecessors A a r = {}"
proof(rule ccontr)
  have  irr:  "irreflexive_on A r" and tran: "transitive_on A r" using assms(2)
  by(unfold strict_part_order_def, auto)
  assume 1: "predecessors A a r \<noteq> {}" show False
  proof-
    have "\<exists>x\<in>A. (x,a)\<in> r" using 1  by(unfold predecessors_def, auto)
    then obtain x where "x\<in>A" and "(x,a)\<in> r" by auto
    hence "x\<noteq>a" using irr by (unfold irreflexive_on_def, auto)
    hence "(a,x)\<in>r" using  `x\<in>A` `minimum A a r` by(unfold minimum_def, auto)
    have  "a\<in>A" using  `minimum A a r` by(unfold minimum_def, auto)
    hence "(a,a)\<in>r" using `(a,x)\<in>r`  `(x,a)\<in> r`  `x\<in>A`  tran 
      by(unfold transitive_on_def, blast)
    thus False using `(a,a)\<in>r` `a\<in>A` irr  irreflexive_on_def
      by (unfold irreflexive_on_def, auto)
  qed
qed

lemma  emptyness_pred_min_spo2:
  assumes  "strict_part_order A r" and  "minimum A a r" 
  shows "\<forall>x\<in>A.(predecessors A x r = {}) \<longleftrightarrow> (x=a)" 
proof
  fix x
  assume  "x \<in> A" 
  show "(predecessors A x r = {}) \<longleftrightarrow> (x = a)"
  proof-
    have 1: "a \<in> A" using  `minimum A a r`  by(unfold minimum_def, auto)
    have 2: "(predecessors A x r = {})\<longrightarrow> (x=a)"
    proof(rule impI)
      assume h: "predecessors A x r = {}"  show "x=a"
      proof(rule ccontr)
      assume  "x \<noteq> a" 
      hence  "(a,x)\<in> r" using  `x \<in> A` `minimum A a r`
        by(unfold minimum_def, auto)     
      hence  "a \<in> predecessors A x r"
        using 1 by(unfold  predecessors_def,auto)
      thus False using h by auto 
    qed
  qed
  have 3: "x=a \<longrightarrow> (predecessors A x r = {})"
  proof(rule impI)
    assume "x=a"
    thus "predecessors A x r = {}" 
      using assms emptyness_pred_min_spo[of A a]  by auto
  qed
  show ?thesis using 2 3 by auto
   qed
qed

lemma height_minimum:
  assumes  "strict_part_order A r" and  "minimum A a r"
  shows "height  A a r = 0"
proof-
  have  "a\<in>A" using  `minimum A a r` by(unfold minimum_def, auto)
  hence "predecessors A a r = {}"
    using assms emptyness_pred_min_spo2[of A r]  by auto
  thus "height  A a r = 0" by(unfold height_def, auto) 
qed

lemma zero_level:
  assumes  "strict_part_order A r" 
  and "minimum A a r"  and  "\<forall>x\<in>A. finite (predecessors A x r)"  
  shows "(level A r 0) = {a}"
proof-
  have "\<forall>x\<in>A.(card (predecessors A x r) = 0) \<longleftrightarrow> (x=a)"
  using  assms emptyness_pred_min_spo2[of A r a] card_eq_0_iff by auto
  hence 1:  "\<forall>x\<in>A.(height A x r = 0) \<longleftrightarrow> (x=a)"
    by(unfold height_def, auto)
  have "a\<in>A" using  `minimum A a r` by(unfold minimum_def, auto)
  thus ?thesis using assms 1  level_def[of A r 0] by auto
qed

lemma min_predecessor:
  assumes  "minimum A a r"
  shows  "\<forall>x\<in>A. x\<noteq>a \<longrightarrow> a\<in>predecessors A x r"
proof
  fix x
  assume "x\<in>A"
  show "x \<noteq> a \<longrightarrow> a \<in> predecessors A x r"
  proof(rule impI)
    assume  "x \<noteq> a"
    show "a \<in> predecessors A x r"
    proof-
      have "(a,x)\<in>r" using `x\<in>A` `x \<noteq> a` `minimum A a r` 
        by(unfold minimum_def, auto)
      hence "a\<in>A"  using  `minimum A a r` by(unfold minimum_def, auto)
      thus "a\<in>predecessors A x r" using `(a,x)\<in>r` 
        by(unfold predecessors_def, auto)
    qed
  qed
qed

lemma spo_subset_preservation: 
  assumes "strict_part_order A r" and "B\<subseteq>A" 
  shows "strict_part_order B r" 
proof-  
  have  "irreflexive_on A r" and "transitive_on A r" 
    using  `strict_part_order A r` 
    by(unfold strict_part_order_def, auto)
  have 1: "irreflexive_on B r"
  proof(unfold irreflexive_on_def)
    show "\<forall>x\<in>B. (x, x) \<notin> r"
    proof
      fix x
      assume "x\<in>B" 
      hence "x\<in>A" using  `B\<subseteq>A` by auto
      thus "(x,x)\<notin>r" using  `irreflexive_on A r`
        by (unfold irreflexive_on_def, auto)
    qed
  qed
  have 2:  "transitive_on B r"
  proof(unfold transitive_on_def)
    show "\<forall>x\<in>B. \<forall>y\<in>B. \<forall>z\<in>B. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
    proof
      fix x assume "x\<in>B"
      show "\<forall>y\<in>B. \<forall>z\<in>B. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
      proof
        fix y  assume "y\<in>B"
        show "\<forall>z\<in>B. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
        proof 
          fix z  assume "z\<in>B"
          show "(x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
          proof(rule impI)
            assume hip: "(x, y) \<in> r \<and> (y, z) \<in> r" 
            show "(x, z) \<in> r"
          proof-
            have "x\<in>A" and  "y\<in>A" and  "z\<in>A" using `x\<in>B` `y\<in>B` `z\<in>B` `B\<subseteq>A`
              by auto
            thus "(x, z) \<in> r" using hip `transitive_on A  r` by(unfold transitive_on_def, blast)
            qed
          qed
        qed
      qed
    qed
  qed
  thus "strict_part_order B r"
    using 1 2  by(unfold strict_part_order_def, auto)   
qed

lemma total_ord_subset_preservation:
  assumes "total_on A r" and  "B\<subseteq>A"
  shows "total_on B r"
proof(unfold total_on_def)
  show  "\<forall>x\<in>B. \<forall>y\<in>B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
  proof
    fix x
    assume "x\<in>B" show " \<forall>y\<in>B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
    proof 
      fix y
      assume "y\<in>B" 
      show  "x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"  
      proof(rule impI)
        assume  "x \<noteq> y"
        show "(x, y) \<in> r \<or> (y, x) \<in> r"
        proof-
          have "x\<in>A \<and> y\<in>A" using  `x\<in>B`  `y\<in>B` `B\<subseteq>A` by auto
          thus  "(x, y) \<in> r \<or> (y, x) \<in> r" 
            using  `x \<noteq> y` `total_on A r` by(unfold total_on_def, auto) 
        qed
      qed
    qed
  qed
qed

definition maximum ::  "'a set \<Rightarrow> 'a \<Rightarrow>'a rel \<Rightarrow> bool"
  where "maximum A a r \<equiv>  (a\<in>A \<and> (\<forall>x\<in>A. x \<noteq> a \<longrightarrow> (x,a) \<in> r))"

lemma maximum_strict_part_order:
  assumes "strict_part_order A r" and "A\<noteq>{}" and "total_on A r" 
  and "finite A"
  shows "(\<exists>a. maximum A a r)" 
proof-
  have "strict_part_order A r \<Longrightarrow> A\<noteq>{} \<Longrightarrow> total_on A r \<Longrightarrow> finite A
  \<Longrightarrow> (\<exists>a. maximum A a r)"  using assms(4)
  proof(induct A rule:finite_induct)
    case empty
    then show ?case by auto
  next
    case (insert x A)  
    show "(\<exists>a. maximum (insert x A) a r)"
  proof(cases "A={}")
    case True
    hence "insert x A ={x}" by simp
    hence  "maximum (insert x A) x r" by(unfold maximum_def, auto)
    then show ?thesis by auto
  next
    case False
    assume "A \<noteq> {}"
    show "\<exists>a. maximum (insert x A) a r"
    proof-
      have 1: "strict_part_order A r" 
        using insert(4) spo_subset_preservation by auto
      have 2: "total_on A r" using insert(6) total_ord_subset_preservation by auto
      have "\<exists>a. maximum A a r" using 1  `A\<noteq>{}`  insert(1) 2 insert(3) by auto
      then obtain a where a: "maximum A a r" by auto
      hence  "a\<in>A" and "\<forall>y\<in>A. y \<noteq> a  \<longrightarrow> (y,a) \<in> r" by(unfold maximum_def, auto)
      have 3: "a\<in>(insert x A)" using `a\<in>A`  by auto
      have 4: "a\<noteq>x" using `a\<in>A` and  `x \<notin> A` by auto
      have  "x\<in>(insert x A)" by auto
      hence "(a,x)\<in>r \<or> (x,a)\<in>r" using 3 4 `total_on (insert x A) r`
        by(unfold total_on_def, auto)
      thus "\<exists>a. maximum (insert x A) a r"
      proof(rule disjE)
        have  "transitive_on (insert x A) r" using  insert(4) 
          by(unfold strict_part_order_def, auto) 
        assume casoa: "(a, x) \<in> r"  
        have  "\<forall>z\<in>(insert x A). z \<noteq> x  \<longrightarrow> (z,x) \<in> r"
        proof
          fix z
          assume hip1: "z \<in> (insert x A)"
          show "z \<noteq> x \<longrightarrow> (z, x) \<in> r"
          proof(rule impI)
            assume "z \<noteq> x"
            hence hip2:  "z\<in>A" using `z \<in> (insert x A)` by auto 
            thus "(z, x) \<in> r" 
            proof(cases)
              assume "z=a" 
              thus "(z, x) \<in> r" using `(a, x) \<in> r` by auto 
            next
              assume "z\<noteq>a"
              hence "(z,a) \<in> r" using  `z\<in>A` `\<forall>y\<in>A. y \<noteq> a  \<longrightarrow> (y,a) \<in> r` by auto
              have "a\<in>(insert x A)" and "z\<in>(insert x A)" and  "x\<in>(insert x A)"
                using  `a\<in>A` `z\<in>A` by auto            
              thus  "(z, x) \<in> r"
                using  `(z,a) \<in> r` `(a, x) \<in> r`  `transitive_on (insert x A) r`
                by(unfold transitive_on_def, blast) 
            qed
          qed
        qed
        thus "\<exists>a. maximum (insert x A) a r"
          using  `x\<in>(insert x A)` by(unfold maximum_def, auto)
      next
        assume casob: "(x, a) \<in> r"
        have  "\<forall>z\<in>(insert x A). z \<noteq> a  \<longrightarrow> (z,a) \<in> r"
        proof
          fix z
          assume hip1: "z \<in> (insert x A)"
          show "z \<noteq> a \<longrightarrow> (z, a) \<in> r"
          proof(rule impI)
            assume "z \<noteq> a" show  "(z, a) \<in> r"
            proof- 
              have "z\<in>A \<or> z=x" using `z \<in> (insert x A)` by auto
              thus  "(z, a) \<in> r"
              proof(rule disjE)
                assume  "z \<in> A"
                thus  "(z, a) \<in> r" 
                  using  `z \<noteq> a` `\<forall>y\<in>A. y \<noteq> a  \<longrightarrow> (y,a) \<in> r` by auto
              next
                assume "z = x" 
                thus  "(z, a) \<in> r" using `(x, a) \<in> r` by auto
              qed
            qed
          qed
        qed
        thus "\<exists>a. maximum (insert x A) a r" 
          using `a\<in>(insert x A)`  by(unfold maximum_def, auto)      
      qed
    qed
  qed
qed
  thus ?thesis using assms by auto
qed

lemma finiteness_union_finite_sets:
  fixes S :: "'a  \<Rightarrow>  'a set" 
  assumes "\<forall>x. finite (S x)" and "finite A"
  shows "finite (\<Union>a\<in>A. (S a))" using assms by auto

lemma uniqueness_level_aux:
  assumes "k>0"
  shows "(level A r n) \<inter> (level A r (n+k)) = {}" 
proof(rule ccontr)
  assume  "level A r n \<inter> level A r (n + k) \<noteq> {}" 
  hence  "\<exists>x. x\<in>(level A r n) \<inter> level A r (n + k)" by auto
  then obtain x where "x\<in>(level A r n) \<inter> level A r (n + k)" by auto
  hence "x\<in>A \<and> height A x r = n" and "x\<in>A \<and> height A x r = n+k"
    by(unfold level_def, auto)
  thus False using `k>0` by auto
qed

lemma uniqueness_level:
  assumes "n\<noteq>m" 
  shows "(level A r n) \<inter> (level A r m) = {}"
proof-
  have "n < m \<or> m < n" using assms by auto
  thus ?thesis
  proof(rule disjE)
    assume "n < m"
    hence "\<exists>k. k>0 \<and> m=n+k" by arith
    thus ?thesis using uniqueness_level_aux[of _ A r] by auto
  next
    assume "m < n"
    hence "\<exists>k. k>0 \<and> n=m+k" by arith
    thus ?thesis using  uniqueness_level_aux[of _ A r] by auto
  qed
qed
 
definition tree ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "tree A r  \<equiv>
 r \<subseteq> A \<times> A \<and> r\<noteq>{} \<and> (strict_part_order A r)  \<and>  (\<exists>a. minimum A a r) \<and>
 (\<forall>a\<in>A. finite (predecessors A a r) \<and> (total_on (predecessors A  a r) r))"

definition finite_tree::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where
"finite_tree A r  \<equiv> tree A r \<and> finite A"

abbreviation  infinite_tree::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" 
  where
"infinite_tree A r  \<equiv>  tree A r \<and> \<not> finite A"

definition enumerable_tree :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"  where
 "enumerable_tree A r \<equiv> \<exists>g. enumeration (g:: nat \<Rightarrow>'a)"

definition finitely_branching ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where  "finitely_branching  A r \<equiv> (\<forall>x\<in>A. finite (imm_successors A x r))"

definition sub_linear_order :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "sub_linear_order B A r  \<equiv>  B\<subseteq>A \<and> (strict_part_order A r) \<and> (total_on B r)"

definition path ::  "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "path  B A r  \<equiv>
 (sub_linear_order B A r) \<and>
 (\<forall>C. B \<subseteq> C \<and> sub_linear_order C A r \<longrightarrow> B = C)"

definition finite_path:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "finite_path B A r \<equiv>  path  B A r \<and> finite B"

definition infinite_path:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "infinite_path B A r \<equiv>  path  B A r \<and>  \<not> finite B"

lemma tree: 
  assumes "tree A r"
  shows
  "r \<subseteq> A \<times> A" and "r\<noteq>{}" 
  and  "strict_part_order A r"
  and  "\<exists>a. minimum A a r" 
  and  "(\<forall>a\<in>A. finite (predecessors A a r) \<and> (total_on (predecessors A  a r) r))"
  using `tree A r` by(unfold tree_def, auto)

lemma non_empty: 
  assumes "tree A r" shows "A\<noteq>{}"
proof-
  have "\<exists>a. minimum A a r" using  `tree A r` tree[of A r] by auto
  hence "\<exists>a. a\<in>A"  by(unfold minimum_def, auto)
  thus  "A\<noteq>{}" by auto
qed

lemma predecessors_spo:
  assumes "tree A r" 
  shows  "\<forall>x\<in>A. strict_part_order (predecessors A x r) r"
proof- 
  have "irreflexive_on A r" and "transitive_on A r"  using `tree A r`
    by(unfold tree_def,unfold strict_part_order_def,auto) 
  thus ?thesis
proof(unfold strict_part_order_def)
  show "\<forall>x\<in>A. irreflexive_on (predecessors A x r) r \<and>
        transitive_on (predecessors A x r) r"
  proof
    fix x
    assume "x\<in>A"
    show "irreflexive_on (predecessors A x r) r \<and> transitive_on (predecessors A x r) r"
    proof-
      have 1: "irreflexive_on (predecessors A x r) r"
      proof(unfold irreflexive_on_def)
        show "\<forall>y\<in>(predecessors A x r). (y, y) \<notin> r"
        proof
          fix y
          assume "y\<in>(predecessors A x r)"
          hence "y\<in>A" by(unfold predecessors_def,auto)
          thus "(y, y) \<notin> r" using `irreflexive_on A r` by(unfold irreflexive_on_def,auto)
        qed
      qed
      have 2: "transitive_on (predecessors A x r) r"
      proof(unfold transitive_on_def)
        let ?B= "(predecessors A x r)"
        show "\<forall>w\<in>?B. \<forall>y\<in>?B. \<forall>z\<in>?B. (w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
        proof
          fix w assume "w\<in>?B"
         show "\<forall>y\<in>?B. \<forall>z\<in>?B. (w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
         proof
           fix y assume "y\<in>?B"
           show "\<forall>z\<in>?B. (w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
           proof 
             fix z  assume "z\<in>?B"
             show "(w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
             proof(rule impI)
               assume hip: "(w, y) \<in> r \<and> (y, z) \<in> r" 
               show "(w, z) \<in> r"
               proof-
                 have  "w\<in>A" and  "y\<in>A" and  "z\<in>A" using `w\<in>?B` `y\<in>?B` `z\<in>?B`
                   by(unfold predecessors_def,auto)
                 thus "(w, z) \<in> r"
                   using hip `transitive_on A  r` by(unfold transitive_on_def, blast)
                 qed
               qed
             qed
           qed
         qed
       qed
       show
        "irreflexive_on (predecessors A x r) r \<and> transitive_on (predecessors A x r) r"
       using 1 2 by auto
       qed
     qed
  qed
qed
       
lemma predecessors_maximum:
  assumes "tree A r" and  "minimum A a r"
  shows "\<forall>x\<in>A. x\<noteq>a \<longrightarrow> (\<exists>b. maximum (predecessors A x r) b r)"
proof
  fix x
  assume "x\<in>A"
  show "x\<noteq>a \<longrightarrow> (\<exists>b. maximum (predecessors A x r) b r)"
  proof(rule impI)
    assume "x\<noteq>a"
    show "(\<exists>b. maximum (predecessors A x r) b r)" 
    proof-
      have 1: "strict_part_order (predecessors A x r) r" 
        using  `tree A r` `x\<in>A`  predecessors_spo by auto
      have 2: "total_on (predecessors A x r) r" and 
           3: "finite (predecessors A x r)" and  "r \<subseteq> A \<times> A"
        using  `tree A r` `x\<in>A` by(unfold tree_def, auto)
      have 4:  "(predecessors A x r)\<noteq>{}" 
        using  `r \<subseteq> A \<times> A`  `minimum A a r`  `x\<in>A`  `x\<noteq>a` 
              min_predecessor[of A a] by auto
      have 5: "A\<noteq>{}" using `tree A r` non_empty by auto
      show "(\<exists>b. maximum (predecessors A x r) b r)" 
        using 1 2 3 4 5  maximum_strict_part_order by auto
    qed
  qed
qed

lemma non_empty_preds_in_tree: 
  assumes  "tree A r"  and  "card (predecessors A x r) = n+1"
  shows  "x\<in>A"
proof- 
  have  "r \<subseteq> A \<times> A"  using `tree A r` by(unfold tree_def, auto)
  have "(predecessors A x r) \<noteq> {}" using assms(2) by auto
  hence "\<exists>y\<in>A. (y,x)\<in>r" by (unfold predecessors_def,auto)
  thus  "x\<in>A" using  `r \<subseteq> A \<times> A` by auto
qed

lemma imm_predecessor:
  assumes  "tree A r"   
  and  "card (predecessors A x r) = n+1" and
  "maximum (predecessors A x r) b r"
  shows "height A b r = n"
proof- 
  have "transitive_on A r" and  "r \<subseteq> A \<times> A" and  "irreflexive_on A r"
    using `tree A r`
    by (unfold tree_def, unfold strict_part_order_def, auto)
  have  "x\<in>A" using  assms(1) assms(2)  non_empty_preds_in_tree by auto
  have "strict_part_order (predecessors A x r) r"
    using `x\<in>A` `tree A r` predecessors_spo[of A r] by auto
  hence  "irreflexive_on (predecessors A x r) r" and
         "transitive_on (predecessors A x r) r"
    by(unfold strict_part_order_def, auto) 
  have "b\<in>(predecessors A x r)" 
    using `maximum (predecessors A x r) b r` by(unfold maximum_def, auto)
  have "total_on (predecessors A x r) r"
    using `x\<in>A` `tree A r` by(unfold tree_def, auto)
  have "card (predecessors A x r)>0 " using assms(2) by auto
  hence 1: "finite (predecessors A x r)"  using card_gt_0_iff by blast
  have  2: "b\<in>(predecessors A x r)" 
    using assms(3) by (unfold maximum_def,auto)
  hence "card ((predecessors A x r)-{b}) = n" 
    using 1  `card (predecessors A x r) = n+1`
    card_Diff_singleton[of b "(predecessors A x r)" ] by auto
  have "(predecessors A b r) = ((predecessors A x r)-{b})"
  proof(rule equalityI)
    show "(predecessors A b r) \<subseteq> (predecessors A x r - {b})" 
    proof
      fix y
      assume  "y\<in> (predecessors A b r)"
      hence "y\<in>A" and  "(y,b)\<in> r" by (unfold predecessors_def,auto)
      hence "y\<noteq>b" using `irreflexive_on A r` by(unfold irreflexive_on_def,auto)
      have "(b,x)\<in>r" using 2 by (unfold predecessors_def,auto)
      hence "b\<in>A"  using `r \<subseteq> A \<times> A` by auto
      have "(y,x)\<in> r" using `x\<in>A` `y\<in>A` `b\<in>A`  `(y,b)\<in> r`  `(b,x)\<in>r` `transitive_on A r`
        by(unfold transitive_on_def, blast)    
      show "y\<in>(predecessors A x r - {b})" 
        using `y\<in>A` `(y,x)\<in> r` `y\<noteq>b` by(unfold predecessors_def, auto)
    qed
  next
    show "(predecessors A x r - {b}) \<subseteq> (predecessors A b r)"
    proof
      fix y
      assume hip: "y\<in>(predecessors A x r - {b})" 
      hence "y\<noteq>b" and  "y\<in>A" by(unfold predecessors_def, auto)
      have "(y,b)\<in> r" using hip `maximum (predecessors A x r) b r`
        by(unfold maximum_def,auto)
      thus "y\<in> (predecessors A b r)" using `y\<in>A`
        by(unfold predecessors_def, auto)
    qed
  qed
  hence 3:  "card (predecessors A b r) = card (predecessors A x r - {b})" 
    by auto
  have "finite (predecessors A x r)" using `x\<in>A` `tree A r` by(unfold tree_def,auto)
  hence "card (predecessors A x r - {b}) = card (predecessors A x r)-1 " 
    using 2  card_Suc_Diff1 by auto
  hence "card (predecessors A b r) = n"
    using 3  `card (predecessors A x r) = n+1` by auto
  thus "height A b r = n" by (unfold height_def, auto)
qed
 
lemma height:
  assumes  "tree A r" and "height A x r = n+1"  
  shows "\<exists>y. (y,x)\<in>r \<and> height A y r = n"
proof -
  have 1: "card (predecessors A x r) = n+1" 
    using assms(2) by (unfold height_def, auto)
  have "\<exists>a. minimum A a r" using `tree A r` by(unfold tree_def, auto) 
  then obtain a where a: "minimum A a r"  by auto
  have  "strict_part_order A r" using  `tree A r` tree[of A r]  by auto
  hence  "height  A a r = 0" using a  height_minimum[of A r] by auto
  hence "x \<noteq> a" using assms(2) by auto
  have "x\<in>A"  using `tree A r`  1  non_empty_preds_in_tree by auto 
  hence "(\<exists>b. maximum (predecessors A x r) b r)" 
    using `x \<noteq> a` `tree A r` a predecessors_maximum[of A r a] by auto
  then obtain b where b: "(maximum (predecessors A x r) b r)" by auto
  hence "(b,x)\<in>r" by(unfold maximum_def, unfold predecessors_def,auto)
  thus "\<exists>y. (y,x)\<in>r \<and> height A y r = n"
    using  `tree A r` 1 b imm_predecessor[of A r] by auto 
qed

lemma level:
  assumes  "tree A r" and "x \<in> (level A r (n+1))"  
  shows "\<exists>y. (y,x)\<in>r \<and> y \<in> (level A r n)"
proof-
  have "height A x r = n+1"
    using `x\<in> (level A r (n+1))` by (unfold level_def, auto)
  hence "\<exists>y. (y,x)\<in>r \<and> height A y r = n" 
    using `tree A r` height[of A r] by auto 
  then obtain y where y:  "(y,x)\<in>r \<and> height A y r = n" by auto
  have  "r \<subseteq> A \<times> A"  using `tree A r` by(unfold tree_def,auto) 
  hence "y\<in>A" using y by auto
  hence "(y,x)\<in>r \<and> y \<in> (level A r n)" using y by(unfold level_def, auto)
  thus ?thesis by auto
qed
(*Para demostrar que en un árbol de ramificación los leveles son finites, se define
la siguiente función. *)
primrec set_nodes_at_level ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow>'a set" where
"set_nodes_at_level A r 0 = {a. (minimum A a r)}"
| "set_nodes_at_level A r (Suc n)  = (\<Union>a\<in> (set_nodes_at_level A r n). imm_successors A a r)"

lemma set_nodes_at_level_zero_spo:
  assumes  "strict_part_order A r" and  "minimum A a r"
  shows "(set_nodes_at_level A r 0) = {a}"
proof-
  have "a\<in>(set_nodes_at_level A r 0)" using `minimum A a r` by auto
  hence 1: "{a} \<subseteq> (set_nodes_at_level A r 0)" by auto
  have 2:  "(set_nodes_at_level A r 0) \<subseteq> {a}"
  proof
    {fix x
    assume "x\<in>(set_nodes_at_level A r 0)"
    hence "minimum A x r" by auto
    hence "x=a" using assms  spo_uniqueness_min[of A r] by auto
    thus "x\<in>{a}" by auto}
  qed
  thus "(set_nodes_at_level A r 0) = {a}" using 1 2 by auto
qed

lemma height_level:
  assumes "strict_part_order A r"  and  "minimum A a r"
  and "x \<in> set_nodes_at_level A r n"
  shows "height A x r = n"
proof-
  have
 "\<lbrakk>strict_part_order A r; minimum A a r; x \<in> set_nodes_at_level A r n\<rbrakk> \<Longrightarrow> 
  height A x r = n" 
  proof(induct n arbitrary: x)
    case 0
    then show "height A x r = 0"
    proof-
      have "minimum A x r"  using `x \<in> set_nodes_at_level A r 0` by auto
      thus "height A x r = 0"
        using `strict_part_order A r`  height_minimum[of A r]
        by auto
    qed
  next
    case (Suc n)
    then show ?case 
    proof-
      have  "x\<in> (\<Union>a \<in> (set_nodes_at_level A r n). (imm_successors A a r))"
        using Suc(4) by auto
      then  obtain a
        where hip1:  "a \<in> (set_nodes_at_level A r n)" and hip2: "x\<in> (imm_successors A a r)" 
        by auto
      hence 1: "height A a r = n" using  Suc(1-3) by auto
      have "height A x r = (height A a r)+1" 
        using hip2 by(unfold imm_successors_def, auto)
      thus "height A x r = Suc n" using 1 by auto
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma level_func_vs_level_def: 
  assumes  "tree A r"
  shows "set_nodes_at_level A r n = level A r n"   
proof(induct n)
  have 1: "strict_part_order A r" and
       2: "\<forall>x\<in>A. finite (predecessors A x r)"
    using  `tree A r` tree[of A r] by auto 
  have "\<exists>a. minimum A a r" using `tree A r` by(unfold tree_def, auto)
  then obtain a where a: "minimum A a r"  by auto
  case 0
  then show  "set_nodes_at_level A r 0 = level A r 0" 
  proof- 
    have "set_nodes_at_level A r 0 = {a}" using 1 a  set_nodes_at_level_zero_spo[of A r] by auto
    moreover 
    have "level A r 0 = {a}" using 1 2  a  zero_level[of A r] by auto
    ultimately
    show "set_nodes_at_level A r 0 = level A r 0" by auto
  qed
  next
    case (Suc n)
    assume  "set_nodes_at_level A r n = level A r n"
    show "set_nodes_at_level A r (Suc n) = level A r (Suc n)"
    proof(rule equalityI)
      show "set_nodes_at_level A r (Suc n) \<subseteq> level A r (Suc n)"
      proof(rule subsetI)
        fix x
        assume hip:  "x \<in> set_nodes_at_level A r (Suc n)" show "x \<in> level A r (Suc n)"
        proof- 
          have
          "set_nodes_at_level A r (Suc n) = (\<Union>a \<in> (set_nodes_at_level A r n). (imm_successors A a r))"
            by simp
          hence "x\<in> (\<Union>a \<in> (set_nodes_at_level A r n). (imm_successors A a r))"
            using hip by auto 
          then obtain a where hip1: "a \<in> (set_nodes_at_level A r n)" and
            hip2:"x\<in> (imm_successors A a r)" by auto
          have "(a,x)\<in>r \<and>  height A x r = (height A a r)+1" 
            using hip2 by(unfold imm_successors_def, auto)
          moreover
          have "\<exists>b. minimum A b r" using `tree A r` by(unfold tree_def, auto)
         then obtain b where b: "minimum A b r"  by auto
         have 1:  "r \<subseteq> A \<times> A" and  "strict_part_order A r"
           using `tree A r` by(unfold tree_def, auto)     
         hence "height A a r = n" using b hip1  height_level[of A r] by auto
         ultimately
         have "(a,x)\<in>r \<and> height A x r = n+1" by auto
         hence "x\<in>A \<and> height A x r = n+1" using `r \<subseteq> A \<times> A` by auto
         thus "x \<in> level A r (Suc n)" by(unfold level_def, auto)
       qed
     qed
  next
    show "level A r (Suc n) \<subseteq> set_nodes_at_level A r (Suc n)"
    proof(rule subsetI)
      fix x
      assume hip: "x \<in> level A r (Suc n)" show "x \<in> set_nodes_at_level A r (Suc n)"
      proof-
        have  1: "x\<in>A \<and> height A x r = n+1" using hip by(unfold level_def,auto)
        hence  "\<exists>y. (y,x)\<in>r \<and> height A y r = n" 
        using assms height[of A r] by auto
        then obtain y where y1: "(y,x)\<in>r"  and y2: "height A y r = n" by auto
        hence "x \<in> (imm_successors A y r)" 
          using 1 by(unfold imm_successors_def, auto)
        moreover
        have  "r \<subseteq> A \<times> A"  using `tree A r` by(unfold tree_def, auto)
        have "y\<in>A" using y1  `r \<subseteq> A \<times> A` by auto
        hence "y\<in> level A r n" using y2 by(unfold level_def, auto)
        hence "y\<in> set_nodes_at_level A r n" using Suc by auto 
        ultimately
        show "x \<in> set_nodes_at_level A r (Suc n)" by auto
      qed
    qed
  qed
qed

lemma pertenece_level:
  assumes "x \<in> set_nodes_at_level A r n" 
  shows "x\<in>A" 
proof-
  have "x \<in> set_nodes_at_level A r n \<Longrightarrow> x\<in>A"
  proof(induct n) 
    case 0
    show  "x \<in> A"  using  `x \<in> set_nodes_at_level A r 0` minimum_def[of A x r] by auto
  next
    case (Suc n)
    then show "x \<in> A"
    proof- 
      have "\<exists>a \<in> (set_nodes_at_level A r n). x\<in> imm_successors A a r"  
        using `x \<in> set_nodes_at_level A r (Suc n)` by auto  
      then obtain a  where  a1:  "a \<in> (set_nodes_at_level A r n)" and
        a2: "x\<in> imm_successors A a r" by auto
      show "x \<in> A" using a2 imm_successors_def[of A a r] by auto   
    qed
  qed
  thus "x \<in> A" using assms by auto
qed

lemma finiteness_set_nodes_at_levela:
  assumes  "\<forall>x\<in>A. finite (imm_successors A x r)" and "finite (set_nodes_at_level A r n)"
  shows "finite (\<Union>a\<in> (set_nodes_at_level A r n). imm_successors A a r)"
proof  
  show "finite (set_nodes_at_level A r n)" using assms(2) by simp
next
  fix x
  assume hip:  "x \<in> set_nodes_at_level A r n" show  "finite (imm_successors A x r)"
  proof-  
    have "x\<in>A" using hip  pertenece_level[of x A r]  by auto 
    thus  "finite (imm_successors A x r)"  using assms(1) by auto 
  qed
qed

lemma finiteness_set_nodes_at_level:
  assumes "finite (set_nodes_at_level A r 0)" and  "finitely_branching A r"
  shows  "finite (set_nodes_at_level A r n)"
proof(induct n)
  case 0
  show "finite (set_nodes_at_level A r 0)" using assms  by auto
next
  case (Suc n)
  then show ?case
  proof -   
    have 1: "\<forall>x\<in>A. finite (imm_successors A x r)"
      using assms by (unfold finitely_branching_def, auto)
    hence  "finite (\<Union>a\<in> (set_nodes_at_level A r n). imm_successors A a r)"
      using Suc(1) finiteness_set_nodes_at_levela[of A r] by auto 
    thus "finite (set_nodes_at_level A r (Suc n))" by auto
  qed
qed

lemma finite_level:
  assumes  "tree A r" and "finitely_branching  A r" 
  shows  "finite (level A r n)" 
proof-
  have 1: "strict_part_order A r"  using `tree A r` tree[of A r] by auto
  have  "\<exists>a. minimum A a r"  using `tree A r` tree[of A r] by auto
  then obtain a where "minimum A a r" by auto
  hence "finite (set_nodes_at_level A r 0)" 
    using 1  set_nodes_at_level_zero_spo[of A r] by auto
  hence "finite (set_nodes_at_level A r n)"
    using `finitely_branching  A r` finiteness_set_nodes_at_level[of A r] by auto
  thus  ?thesis using `tree A r` level_func_vs_level_def[of A r n] by auto
qed

lemma  finite_level_a:
  assumes "tree A r" and "\<forall>n. finite (level A r n)"
  shows "finitely_branching A r"
proof(unfold finitely_branching_def)
  show  "\<forall>x\<in>A. finite (imm_successors A x r)"
  proof
  fix x
  assume "x\<in>A"
  show "finite (imm_successors A x r)" using finitely_branching_def
  proof-
    let ?n = "(height A x r)"
    have "(imm_successors A x r) \<subseteq> (level A r (?n+1))"
      using imm_successors_def[of A x r] level_def[of A r "?n+1"] by auto 
    thus "finite (imm_successors A x r)"  using assms(2) by(simp add: finite_subset)   
  qed
qed
qed

lemma empty_predec: 
  assumes "\<forall>x\<in>A. (x,y)\<notin>r"  
  shows "predecessors A y r ={}" 
    using assms by(unfold predecessors_def, auto)

lemma level_element:
 "\<forall>x\<in>A.\<exists>n. x\<in> level A r n"
proof
  fix x
  assume hip: "x\<in>A" show "\<exists>n. x \<in> level A r n"
  proof-
    let ?n = "height A x r"
    have "x\<in>level A r ?n" using `x\<in>A`  by (unfold level_def, auto)
    thus "\<exists>n. x \<in> level A r n" by auto 
  qed
qed

lemma union_levels:
  shows "A =(\<Union>n. level A r n)"
proof(rule equalityI)
  show "A \<subseteq> (\<Union>n. level A r n)"
  proof(rule subsetI)
    fix x
    assume hip: "x\<in>A" show "x\<in>(\<Union>n. level A r n)"
    proof-
      have "\<exists>n. x\<in> level A r n"  
        using hip level_element[of A] by auto
      then obtain n where  "x\<in> level A r n" by auto
    thus ?thesis by auto 
  qed
qed
next
  show  "(\<Union>n. level A r n) \<subseteq> A"
  proof(rule subsetI)
    fix x
    assume hip:  "x \<in> (\<Union>n. level A r n)" show "x \<in> A"
    proof-
      obtain n where  "x\<in> level A r n" using hip by auto 
      thus "x \<in> A" by(unfold level_def, auto)
    qed
  qed
qed

lemma path_to_node:
  assumes  "tree A r"  and  "x \<in> (level A r (n+1))" 
  shows "\<forall>k.(0\<le>k \<and> k\<le>n)\<longrightarrow> (\<exists>y. (y,x)\<in>r \<and> y \<in> (level A r k))"
proof- 
  have "tree A r \<Longrightarrow> x \<in> (level A r (n+1)) \<Longrightarrow>  
  \<forall>k.(0\<le>k \<and> k\<le>n)\<longrightarrow> (\<exists>y. (y,x)\<in>r \<and> y \<in> (level A r k))"
  proof(induction n arbitrary: x)
    have "r \<subseteq> A \<times> A" and 1:  "strict_part_order A r" 
    and "\<exists>a. minimum A a r"
    and 2: "\<forall>x\<in>A. finite (predecessors A x r)"  
      using `tree A r` tree[of A r] by auto
    case 0
    show  "\<forall>k. 0 \<le> k \<and> k \<le> 0 \<longrightarrow> (\<exists>y. (y, x) \<in> r \<and> y \<in> level A r k)"
    proof
      fix k
      show "0 \<le> k \<and> k \<le> 0 \<longrightarrow> (\<exists>y. (y, x) \<in> r \<and> y \<in> level A r k)"
      proof(rule impI)
        assume hip:  "0 \<le> k \<and> k \<le> 0"
        show "(\<exists>y. (y, x) \<in> r \<and> y \<in> level A r k)" 
        proof-
          have "k=0" using hip  by auto
          thus "(\<exists>y. (y, x) \<in> r \<and> y \<in> level A r k)"
            using `tree A r`  `x \<in> (level A r (0 + 1))` level[of A r ]  by auto
        qed      
      qed
    qed
    next
      case (Suc n)
      show "\<forall>k. 0 \<le> k \<and> k \<le> Suc n \<longrightarrow> (\<exists>y. (y, x) \<in> r \<and> y \<in> level A r k)"
  proof(rule allI, rule impI)
    fix k 
    assume hip:  "0 \<le> k \<and> k \<le> Suc n"
    show  "(\<exists>y. (y, x) \<in> r \<and> y \<in> level A r k)"
    proof-
      have "(0 \<le> k \<and> k \<le> n) \<or> k = Suc n"  using hip by auto
      thus ?thesis
      proof(rule disjE)
        assume hip1:  "0 \<le> k \<and> k \<le> n"
        have "\<exists>y. (y,x)\<in>r \<and> y \<in> (level A r (n+1))" 
        using `tree A r` level  `x \<in> level A r (Suc n + 1)` by auto
        then obtain y where y1: "(y,x)\<in>r" and y2: "y \<in> (level A r (n+1))" 
          by auto    
        have "\<forall>k. 0 \<le> k \<and> k \<le> n \<longrightarrow> (\<exists>z. (z, y) \<in> r \<and> z \<in> level A r k)" 
          using y2  Suc(1-3) by auto 
        hence "(\<exists>z. (z, y) \<in> r \<and> z \<in> level A r k)" 
          using hip1 by auto
        then obtain z where  z1: "(z, y) \<in> r" and z2: "z \<in> (level A r k)" by auto
        have  "r \<subseteq> A \<times> A" and "strict_part_order A r" 
          using  `tree A r` tree by auto
        hence "z\<in>A" and  "y\<in>A" and "x\<in>A"
          using `r \<subseteq> A \<times> A` `(z, y) \<in> r` `(y,x)\<in>r` by auto
        have "transitive_on A r" using `strict_part_order A r`
          by(unfold strict_part_order_def, auto)
        hence "(z, x) \<in> r" using `z\<in>A` `y\<in>A` and `x\<in>A` `(z, y) \<in> r` `(y,x)\<in>r`
          by(unfold transitive_on_def, blast)
        thus "(\<exists>y. (y, x) \<in> r \<and> y \<in> level A r k)"
          using z2 by auto
      next
        assume  "k = Suc n"
        thus  "\<exists>y. (y,x)\<in>r \<and> y \<in> (level A r k)"
          using `tree A r` level `x \<in> level A r (Suc n + 1)` by auto
        qed
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma set_nodes_at_level:  
  assumes "tree A r"  
  shows "(level A r (n+1))\<noteq> {} \<longrightarrow> (\<forall>k.(0\<le>k \<and> k\<le>n) \<longrightarrow> (level A r k)\<noteq> {})"
proof(rule impI) 
  assume hip:  "(level A r (n+1))\<noteq> {}"
    show  "(\<forall>k.(0\<le>k \<and> k\<le>n) \<longrightarrow> (level A r k)\<noteq> {})"
    proof-      
      have  "\<exists>x. x\<in>(level A r (n+1))" using hip by auto  
      then obtain x where x: "x\<in>(level A r (n+1))" by auto
      thus ?thesis using assms path_to_node[of A r] by blast
    qed
  qed

lemma emptyness_below_height:
  assumes  "tree A r"  
  shows  "((level A r (n+1)) = {}) \<longrightarrow> (\<forall>k. k>(n+1) \<longrightarrow> (level A r k) = {})"
proof(rule ccontr)
  assume hip: "\<not> (level A r (n+1) = {} \<longrightarrow> (\<forall>k>(n+1). level A r k = {}))"
  show False
  proof-
    have "((level A r (n+1)) = {}) \<and> \<not>(\<forall>k>(n+1). level A r k = {})" 
      using hip by auto
    hence 1: "(level A r (n+1)) = {}" and 2: "\<exists>k>(n+1). (level A r k) \<noteq> {}"
      by auto
    obtain z where z1: "z>(n+1)" and z2: "(level A r z) \<noteq> {}"
      using 2 by auto
    have "z>0" using  `z>(n+1)` by auto 
    hence "(level A r ((z-1)+1)) \<noteq> {}"
      using z2 by simp
    hence "\<forall>k.(0\<le>k \<and> k\<le>(z-1)) \<longrightarrow> (level A r k)\<noteq> {}" 
      using  z2 `tree A r` set_nodes_at_level[of A r "z-1"]
      by auto
    hence  "(level A r (n+1)) \<noteq> {}"
      using `z>(n+1)` by auto
    thus False using 1 by auto
  qed
qed

lemma characterization_nodes_tree_finite_height:
  assumes "tree A r" and "\<forall>k. k>m \<longrightarrow> (level A r k) = {}"
  shows "A = (\<Union>n\<in>{0..m}. level A r n)"
proof- 
  have a: "A = (\<Union>n. level A r n)" using  union_levels[of A r] by auto
  have "(\<Union>n. level A r n) = (\<Union>n\<in>{0..m}. level A r n)"
  proof(rule equalityI)
    show "(\<Union>n. level A r n) \<subseteq> (\<Union>n\<in>{0..m}.  level A r n)"
    proof(rule subsetI)
      fix x
      assume hip: "x\<in>(\<Union>n. level A r n)" 
      show "x\<in>(\<Union>n\<in>{0..m}. level A r n)"
      proof-
        have "\<exists>n. x\<in> level A r n"  
        using hip level_element[of A] by auto
        then obtain n where n: "x\<in> level A r n" by auto
        have "n\<in>{0..m}"
        proof(rule ccontr)
          assume 1: "n \<notin> {0..m}"
          show False
          proof-
            have "n > m" using 1 by auto
            thus False using assms(2) n by auto
          qed
        qed
        thus "x\<in>(\<Union>n\<in>{0..m}. level A r n)" using n by auto
      qed
    qed
  next
    show  "(\<Union>n\<in>{0..m}. level A r n) \<subseteq> (\<Union>n. level A r n)" by auto
  qed
  thus  "A = (\<Union>n\<in>{0..m}. level A r n)" using a by auto
qed

lemma finite_tree_if_fin_branches_and_fin_height:
  assumes "tree A r"  and  "finitely_branching  A r"
  and "\<exists>n. (\<forall>k. k>n \<longrightarrow> (level A r k) = {})"
  shows "finite A"
proof-
  obtain m where m: "(\<forall>k. k>m \<longrightarrow> (level A r k) = {})" 
    using assms(3) by auto 
  hence 1: "A =(\<Union>n\<in>{0..m}. level A r n)"
    using  assms(1) assms(3) characterization_nodes_tree_finite_height[of A r m] by auto
  have "\<forall>n. finite (level A r n)" 
    using assms(1-2) finite_level by auto
  hence "\<forall>n\<in>{0..m}. finite (level A r n)" by auto
  hence "finite (\<Union>n\<in>{0..m}. level A r n)" by auto
  thus "finite A" using 1 by auto
qed

lemma all_levels_non_empty:
  assumes  "infinite_tree A r" and  "finitely_branching A r"
  shows "\<forall>n. level A r n \<noteq> {}"
proof(rule ccontr)
  assume hip: "\<not> (\<forall>n. level A r n \<noteq> {})"
  show False
  proof-
    have "tree A r" using `infinite_tree A r` by auto
    have "(\<exists>n. level A r n = {})" using hip by auto
    then obtain n where n: "level A r n = {}" by auto 
    thus False
    proof(cases n)
      case 0
      then show False
      proof-
        have "\<exists>a. minimum A a r" using `tree A r` tree[of A r] by auto
        then obtain a where a:  "minimum A a r" by auto
        have " strict_part_order A r" 
        and "\<forall>x\<in>A. finite (predecessors A x r)" 
          using  `tree A r` tree[of A r] by auto
        hence "level A r n = {a}" 
          using a `n=0` zero_level[of A r a] by auto
        thus False using `level A r n = {}` by auto
      qed
      next
        case (Suc nat)
        fix m
        assume hip: "n = Suc m" show False
        proof-
          have 1:  "level A r (Suc m) = {}"  
            using hip  n by auto
        have "(\<forall>k. k>(m+1) \<longrightarrow> (level A r k) = {})" 
          using `tree A r` 1  emptyness_below_height[of A r m] by auto
        hence 1: "(\<exists>n. \<forall>k. k>n \<longrightarrow> (level A r k) = {})" by auto
        hence 2: "finite A" 
          using `tree A r` 1 `finitely_branching  A r` finite_tree_if_fin_branches_and_fin_height[of A r] by auto
        have 3:  "\<not> finite A" using `infinite_tree A r` by auto
        show False using 2 3 by auto
      qed
    qed
  qed
qed

lemma simple_cyclefree:
  assumes "tree A r" and "(x,z)\<in>r" and "(y,z)\<in>r" and "x\<noteq>y" 
  shows "(x,y)\<in>r \<or> (y,x)\<in>r"
proof-
  have "r \<subseteq> A \<times> A" using `tree A r` by(unfold tree_def, auto)
  hence "x\<in>A" and  "y\<in>A" and  "z\<in>A" using  `(x,z)\<in>r` and `(y,z)\<in>r` by auto 
  hence 1: "x \<in> predecessors A z r" and 2: "y \<in> predecessors A z r"
    using assms by(unfold predecessors_def, auto)
  have "(total_on (predecessors A  z r) r)"
    using `tree A r` `z\<in>A` by(unfold tree_def, auto)
  thus ?thesis using 1 2 `x\<noteq>y`  total_on_def[of "predecessors A z r" r] by auto 
qed

lemma inclusion_predecessors:
  assumes  "r \<subseteq> A \<times> A" and "strict_part_order A r" and "(x,y)\<in>r"
  shows "(predecessors A x r) \<subset> (predecessors A y r)"
proof-
  have "irreflexive_on A r" and "transitive_on A r" 
    using assms(2) by (unfold strict_part_order_def, auto) 
  have 1: "(predecessors A x r)\<subseteq> (predecessors A y r)"
  proof(rule subsetI)
    fix z
    assume "z\<in>predecessors A x r"
    hence "z\<in>A" and "(z,x)\<in>r" by(unfold predecessors_def, auto)
    have "x\<in>A" and "y\<in>A"  using `(x,y)\<in>r` `r \<subseteq> A \<times> A` by auto
    hence "(z,y)\<in>r"
      using `z\<in>A` `y\<in>A` `x\<in>A` `(z,x)\<in>r` `(x,y)\<in>r` `transitive_on A r` 
      by (unfold transitive_on_def, blast) 
    thus "z\<in>predecessors A y r" 
      using `z\<in>A` by(unfold predecessors_def, auto)
  qed
  have 2: "x\<in>predecessors A y r" 
    using `r \<subseteq> A \<times> A` `(x,y)\<in>r` by(unfold predecessors_def, auto)
  have 3:  "x\<notin>predecessors A x r"
  proof(rule ccontr)
    assume "\<not> x \<notin> predecessors A x r"
    hence "x \<in> predecessors A x r" by auto
    hence "x\<in>A \<and> (x,x)\<in>r"
      by(unfold predecessors_def, auto)
    thus False using `irreflexive_on A r`
      by (unfold irreflexive_on_def, auto)
  qed
  have "(predecessors A x r) \<noteq> (predecessors A y r)"
    using 2 3 by auto
  thus ?thesis using 1 by auto
qed

lemma different_height_finite_pred:
  assumes  "r \<subseteq> A \<times> A" and "strict_part_order A r" and "(x,y)\<in>r" 
  and  "finite (predecessors A y r)"
  shows "height A x r < height A y r" 
proof- 
  have "card(predecessors A x r) < card(predecessors A y r)" 
    using assms  inclusion_predecessors[of r A x y] psubset_card_mono by auto
  thus ?thesis by(unfold height_def, auto)
qed

lemma different_levels_finite_pred:
  assumes  "r \<subseteq> A \<times> A" and "strict_part_order A r" and "(x,y)\<in>r"
  and "x \<in> (level A r n)"  and  "y \<in> (level A r m)" 
  and  "finite (predecessors A y r)"
  shows "level A r n \<noteq> level A r m"
proof(rule ccontr)
  assume "\<not> level A r n \<noteq> level A r m"
  hence "level A r n = level A r m"  by auto
  hence "x \<in> (level A r m)"  using `x \<in> (level A r n)` by auto
  hence 1:  "height A x r= m"  by(unfold level_def, auto)
  have "height A y r= m" using `y \<in> (level A r m)` by(unfold level_def, auto)
  hence "height A x r = height A y r" using 1 by auto
  thus False 
    using assms different_height_finite_pred[of r A x y] by (unfold level_def, auto)
qed

lemma less_level_pred_in_fin_pred: 
  assumes  "r \<subseteq> A \<times> A" and "strict_part_order A r" 
  and "x \<in> predecessors A y r"  and "y \<in> (level A r n)"
  and  "x \<in> (level A r m)" 
  and "finite (predecessors A y r)"
  shows "m<n" 
proof-
  have "(x,y)\<in>r" using `(x \<in> predecessors A y r)`
    by (unfold predecessors_def, auto)
  thus ?thesis 
    using assms  different_height_finite_pred[of r A x y] by(unfold level_def, auto)
qed

lemma emptyness_inter_diff_levels_aux:
  assumes "tree A r" and "x\<in>(predecessors A z r)" 
  and "y\<in>(predecessors A z r)"
  and  "x\<noteq>y" and "x \<in> (level A r n)" and "y \<in> (level A r m)" 
  shows "level A r n \<inter> level A r m = {}" 
proof-   
  have "(x,y)\<in>r \<or> (y,x)\<in>r"     
    using assms simple_cyclefree[of A] by(unfold predecessors_def, auto)
  thus "level A r n \<inter> level A r m ={}"
  proof(rule disjE)
    assume  "(x, y) \<in> r" 
    have "r\<subseteq> A \<times> A" and 1: "strict_part_order A r"
      using  `tree A r` by(unfold tree_def,auto)
    hence "x\<in>A" and "y\<in>A"  and  2: "x\<in>(predecessors A y r)"
      using `(x, y) \<in> r`  by(unfold predecessors_def, auto)
    have 3: "finite (predecessors A y r)"
      using `y\<in>A`  `tree A r` by(unfold tree_def, auto) 
    hence  "n<m"
      using assms `r\<subseteq> A \<times> A` 1 2 3 less_level_pred_in_fin_pred[of r A x y m n]
      by auto
    hence "\<exists>k>0. m=n+k" by arith
    then obtain k where k: "k>0" and m: "m=n+k" by auto
    thus ?thesis using uniqueness_level_aux[OF k, of A ]
      by auto
  next
    assume  "(y, x) \<in> r" 
    have "r\<subseteq> A \<times> A" and 1: "strict_part_order A r"
      using  `tree A r` by(unfold tree_def,auto)
    hence "x\<in>A" and "y\<in>A" and 2: "y\<in>(predecessors A x r)"
      using `(y, x) \<in> r`
      by(unfold predecessors_def, auto)
    have 3: "finite (predecessors A x r)" 
      using `x\<in>A` `tree A r`
      by(unfold tree_def, auto) 
    hence  "m<n" 
      using assms `r\<subseteq> A \<times> A` 1 2 3 less_level_pred_in_fin_pred[of r A y x n m]
      by auto
    hence "\<exists>k>0. n=m+k" by arith
    then obtain k where k: "k>0" and m: "n=m+k" by auto
    thus ?thesis using  uniqueness_level_aux[OF k, of A] by auto
  qed
qed

lemma emptyness_inter_diff_levels:
  assumes "tree A r" and "(x,z)\<in> r" and "(y,z)\<in> r"
  and  "x\<noteq>y" and  "x \<in> (level A r n)" and "y \<in> (level A r m)" 
shows "level A r n \<inter> level A r m = {}" 
proof-
  have "r \<subseteq> A \<times> A"  using  `tree A r` tree by auto
  hence "x\<in>A" and  "y\<in>A"  using  `r \<subseteq> A \<times> A`  `(x,z) \<in> r`  `(y,z)\<in>r` by auto
  hence "x\<in>(predecessors A z r)" and "y\<in>(predecessors A z r)" 
    using  `(x,z)\<in> r` and `(y,z)\<in> r` by(unfold predecessors_def, auto)
  thus ?thesis
    using assms  emptyness_inter_diff_levels_aux[of A r] by blast
qed

primrec disjunction_nodes :: "'a list  \<Rightarrow> 'a formula"  where
 "disjunction_nodes [] = FF"   
| "disjunction_nodes (v#D) = (atom v) \<or>. (disjunction_nodes D)"

lemma truth_value_disjunction_nodes:
  assumes "v\<in> set l" and "t_v_evaluation I (atom v) = Ttrue"
  shows "t_v_evaluation I (disjunction_nodes l) = Ttrue"
proof-
  have "v\<in> set l \<Longrightarrow>  t_v_evaluation I (atom v) = Ttrue \<Longrightarrow>
  t_v_evaluation I (disjunction_nodes l) = Ttrue" 
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    then show  "t_v_evaluation I (disjunction_nodes (a # l)) = Ttrue"
    proof-
      have "v = a \<or> v\<noteq>a" by auto
      thus  "t_v_evaluation I (disjunction_nodes (a # l)) = Ttrue"
      proof(rule disjE)
        assume "v = a"
        hence 1: "disjunction_nodes (a#l) = (atom v) \<or>. (disjunction_nodes l)"
          by auto 
        have "t_v_evaluation I ((atom v) \<or>. (disjunction_nodes l)) = Ttrue"  
          using Cons(3)  by(unfold t_v_evaluation_def,unfold v_disjunction_def, auto)
        thus ?thesis using 1  by auto
      next
        assume "v \<noteq> a"
        hence "v\<in> set l" using Cons(2) by auto
        hence "t_v_evaluation I (disjunction_nodes l) = Ttrue"
          using Cons(1) Cons(3) by auto
        thus ?thesis
          by(unfold t_v_evaluation_def,unfold v_disjunction_def, auto)
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma set_set_to_list1:
  assumes "tree A r" and  "finitely_branching A r" 
  shows "set (set_to_list (level A r n)) = (level A r n)"
  using assms finite_level[of A r n]  set_set_to_list by auto

lemma truth_value_disjunction_formulas:
  assumes  "tree A r" and  "finitely_branching A r"
  and  "v\<in>(level A r n) \<and> t_v_evaluation I (atom v) = Ttrue" 
  and  "F = disjunction_nodes(set_to_list (level A r n))" 
  shows "t_v_evaluation I  F = Ttrue"
proof- 
  have "set (set_to_list (level A r n)) = (level A r n)" 
    using set_set_to_list1 assms(1-2) by auto
  hence "v\<in> set (set_to_list (level A r n))"
    using assms(3) by auto
  thus "t_v_evaluation I F = Ttrue"
    using assms(3-4) truth_value_disjunction_nodes by auto
qed

definition \<F> :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
   "\<F> A r  \<equiv> (\<Union>n. {disjunction_nodes(set_to_list (level A r n))})"

definition \<G> ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
   "\<G> A r \<equiv> {(atom u) \<rightarrow>. (atom v) |u v. u\<in>A \<and> v\<in>A \<and> (v,u)\<in> r}" 

definition \<H>n :: "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> ('a formula) set"  where
   "\<H>n A r n \<equiv> {\<not>.((atom u) \<and>. (atom v))
                         |u v . u\<in>(level A r n) \<and> v\<in>(level A r n) \<and> u\<noteq>v }"
definition \<H>  :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
 "\<H> A r  \<equiv> \<Union>n. \<H>n A r n"

definition \<T> :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
   "\<T> A r  \<equiv> (\<F> A r) \<union> (\<G> A r) \<union> (\<H> A r)" 

primrec nodes_formula :: "'v formula  \<Rightarrow> 'v set" where
  "nodes_formula FF = {}"
| "nodes_formula TT = {}"
| "nodes_formula (atom P) =  {P}"
| "nodes_formula (\<not>. F) = nodes_formula F"
| "nodes_formula (F \<and>. G) = nodes_formula F \<union> nodes_formula G"
| "nodes_formula (F \<or>. G) = nodes_formula F \<union> nodes_formula G"
| "nodes_formula (F \<rightarrow>.G) = nodes_formula F \<union> nodes_formula G"

definition nodes_set_formulas :: "'v formula set  \<Rightarrow> 'v set"  where
"nodes_set_formulas S = (\<Union>F\<in> S. nodes_formula F)"

definition maximum_height:: "'v set \<Rightarrow>'v rel \<Rightarrow> 'v  formula  set  \<Rightarrow>  nat"  where
 "maximum_height A r S =  Max (\<Union>x\<in>nodes_set_formulas S. {height A x r})"

lemma node_formula:
  assumes "v \<in> set l" 
  shows "v \<in> nodes_formula (disjunction_nodes l)" 
proof-
  have "v \<in> set l \<Longrightarrow> v \<in> nodes_formula (disjunction_nodes l)" 
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)  
    show "v \<in> nodes_formula (disjunction_nodes (a # l))"  
   proof-
     have "v = a \<or> v\<noteq>a" by auto
     thus "v \<in> nodes_formula (disjunction_nodes (a # l))"
     proof(rule disjE)
       assume "v = a"
       hence 1: "disjunction_nodes (a#l) = (atom v) \<or>. (disjunction_nodes l)"
         by auto 
       have "v \<in> nodes_formula ((atom v) \<or>. (disjunction_nodes l))" by auto 
       thus ?thesis using 1  by auto
     next
       assume "v \<noteq> a"
       hence "v\<in> set l" using Cons(2) by auto
       hence "v \<in> nodes_formula (disjunction_nodes l)"
         using Cons(1) Cons(2) by auto
       thus ?thesis by auto
     qed
   qed
 qed
  thus ?thesis using assms by auto
qed 

lemma node_disjunction_formulas:
  assumes  "tree A r" and  "finitely_branching A r" and "v\<in>(level A r n)" 
  and  "F = disjunction_nodes(set_to_list (level A r n))" 
  shows  "v \<in> nodes_formula F"
proof- 
  have "set (set_to_list (level A r n)) = (level A r n)" 
    using set_set_to_list1 assms(1-2) by auto
  hence "v\<in> set (set_to_list (level A r n))" 
    using assms(3) by auto
  thus "v \<in> nodes_formula F"
    using assms(3-4)  node_formula  by auto
qed

fun node_sig_level_max:: "'v set \<Rightarrow> 'v rel \<Rightarrow> 'v formula set  \<Rightarrow> 'v" 
  where "node_sig_level_max A r S = 
  (SOME u. u \<in> (level A r ((maximum_height A r S)+1)))"

lemma node_level_maximum:  
  assumes "infinite_tree A r" and  "finitely_branching A r"
  shows "(node_sig_level_max A r S) \<in>  (level A r ((maximum_height A r S)+1))" 
proof-
  have  "\<exists>u. u \<in> (level A r ((maximum_height A r S)+1))"
    using assms  all_levels_non_empty[of A r] by (unfold level_def, auto)
  then obtain u where u: "u \<in> (level A r (( maximum_height A r S)+1))" by auto
  hence "(SOME u. u \<in> (level A r ((maximum_height A r S)+1))) \<in> (level A r ((maximum_height A r S)+1))" 
    using someI by auto
  thus ?thesis by auto 
qed

fun path_interpretation :: "'v set \<Rightarrow>'v rel \<Rightarrow> 'v \<Rightarrow> ('v  \<Rightarrow>  v_truth)"  where
"path_interpretation A r u = (\<lambda>v. (if (v,u)\<in>r  then Ttrue else Ffalse))"

lemma finiteness_nodes_formula:
 "finite (nodes_formula F)" by(induct F, auto)

lemma finiteness_set_nodes:
  assumes "finite S" 
  shows  "finite (nodes_set_formulas S)" 
  using assms finiteness_nodes_formula 
  by (unfold nodes_set_formulas_def, auto)

lemma maximum1:
  assumes  "finite S" and "u \<in> nodes_set_formulas S"
  shows "(height A u r)  \<le> (maximum_height A r S)" 
proof-  
  have "(height A u r) \<in> ( \<Union>x\<in>nodes_set_formulas S. {height A x r})" 
    using assms(2) by auto
  thus "(height A u r)  \<le> (maximum_height A r S)"
    using `finite S` finiteness_set_nodes[of S] 
    by(unfold maximum_height_def, auto) 
qed

lemma value_path_interpretation:
  assumes "t_v_evaluation (path_interpretation A r v) (atom u) = Ttrue"
  shows "(u,v)\<in>r"
proof(rule ccontr)
  assume "(u, v) \<notin> r"
  hence "t_v_evaluation (path_interpretation A r v) (atom u) = Ffalse"
    by(unfold t_v_evaluation_def, auto) 
  thus False using assms by auto
qed

lemma satisfiable_path:
  assumes "infinite_tree A r"
  and  "finitely_branching A r" and  "S \<subseteq> (\<T> A r)" 
  and "finite S" 
shows  "satisfiable S"
proof-
  let ?m = "(maximum_height A r S)+1"
  let ?level = "level A r ?m"
  let ?u = "node_sig_level_max A r S" 
  have 1: "tree A r" using `infinite_tree A r` by auto
  have  "r \<subseteq> A \<times> A" and "strict_part_order A r" 
    using  `tree A r` tree by auto
  have "transitive_on A r" 
    using `strict_part_order A r`
    by(unfold strict_part_order_def, auto) 
  have "\<exists>u. u \<in>?level" 
    using assms(1-2) node_level_maximum by auto
  then obtain u where u: "u \<in> ?level"  by auto
  hence levelu:  "?u \<in> ?level"
    using someI by auto
  hence "?u\<in>A" by(unfold level_def, auto)
  have "(path_interpretation A r ?u) model S"
  proof(unfold model_def)
    show "\<forall>F\<in>S. t_v_evaluation (path_interpretation A r ?u) F = Ttrue"
    proof 
      fix F assume "F \<in> S"
      show  "t_v_evaluation (path_interpretation A r ?u) F  = Ttrue"
      proof-        
        have "F \<in> (\<F> A r) \<union> (\<G> A r) \<union> (\<H> A r)" 
        using `S \<subseteq>  \<T> A r` `F \<in> S` assms(2)  by(unfold \<T>_def,auto) 
        hence  "F \<in> (\<F> A r) \<or> F \<in> (\<G> A r) \<or> F \<in> (\<H> A r)" by auto 
        thus ?thesis
        proof(rule disjE)
          assume "F \<in> (\<F> A r)"
          hence "\<exists>n. F = disjunction_nodes(set_to_list (level A r n))" 
            by(unfold \<F>_def,auto)
          then obtain n
            where n: "F = disjunction_nodes(set_to_list (level A r n))" 
            by auto
          have "\<exists>v. v\<in>(level A r n)" 
            using  assms(1-2) all_levels_non_empty[of A r] by auto 
          then obtain v where v: "v \<in> (level A r n)" by auto      
          hence  "v \<in> nodes_formula F" 
            using n node_disjunction_formulas[OF 1 assms(2) v, of F ]
            by auto
          hence a: "v \<in> nodes_set_formulas S" 
            using `F \<in> S`  by(unfold nodes_set_formulas_def, blast)
          hence b: "(height A v r) \<le> (maximum_height A r S)" 
            using `finite S`  maximum1[of S v] by auto
          have "(height A v r) = n" 
            using v by(unfold level_def, auto) 
          hence  "n < ?m" 
            using `finite S` a   maximum1[of S v A r]
            by(unfold maximum_height_def, auto)         
          hence "(\<exists>y. (y,?u)\<in>r \<and> y \<in> (level A r n))" 
            using levelu `tree A r` path_to_node[of A r]
            by auto
          then obtain y where y1: "(y,?u)\<in>r" and y2: "y \<in> (level A r n)"
            by auto
          hence "t_v_evaluation (path_interpretation A r ?u) (atom y) = Ttrue" 
            by auto
          thus "t_v_evaluation (path_interpretation A r ?u) F = Ttrue"
            using 1 assms(2) y2 n  truth_value_disjunction_formulas[of A r y]
            by auto
        next
          assume  "F \<in> \<G> A r \<or> F \<in> \<H> A r"
          thus "t_v_evaluation (path_interpretation A r ?u) F = Ttrue"
          proof(rule disjE)
            assume  "F \<in> \<G> A r"
            hence "\<exists>u. \<exists>v. u\<in>A \<and> v\<in>A  \<and> (v,u)\<in> r  \<and>
                  (F = (atom u) \<rightarrow>. (atom v))"
              by (unfold  \<G>_def, auto)
            then obtain u v where "u\<in>A" and "v\<in>A" and "(v,u)\<in> r" 
            and F: "(F = (atom u) \<rightarrow>. (atom v))" by auto
            show "t_v_evaluation (path_interpretation A r ?u) F = Ttrue"  
            proof(rule ccontr)
              assume "\<not>(t_v_evaluation (path_interpretation A r ?u) F = Ttrue)" 
              hence "t_v_evaluation (path_interpretation A r ?u) F = Ffalse"
                using Bivaluation by auto
              hence "t_v_evaluation (path_interpretation A r ?u) (atom u) =  Ttrue \<and>
              t_v_evaluation (path_interpretation A r ?u) (atom v) =  Ffalse" 
                using F  eval_false_implication by blast
              hence 1: "t_v_evaluation (path_interpretation A r ?u) (atom u) =  Ttrue"
              and   2: "t_v_evaluation (path_interpretation A r ?u) (atom v) =  Ffalse"
                by auto
              have "(u,?u)\<in>r" using 1 value_path_interpretation by auto
              hence "(v,?u)\<in> r" 
                using  `u\<in>A` `v\<in>A` `?u\<in>A` `(v,u)\<in> r` `transitive_on A r` 
                by(unfold transitive_on_def, blast)
              hence "t_v_evaluation (path_interpretation A r ?u) (atom v) =  Ttrue" 
                by auto
              thus False using 2 by auto
            qed
          next
            assume  "F \<in> \<H> A r" 
            hence "\<exists>n. F \<in> \<H>n A r n" by(unfold  \<H>_def, auto)
            then obtain n where  "F \<in> \<H>n A r n" by auto
            hence
            "\<exists>u. \<exists>v. F = \<not>.((atom u) \<and>. (atom v)) \<and> u\<in>(level A r n) \<and>
             v\<in>(level A r n) \<and> u\<noteq>v"
              by(unfold \<H>n_def, auto)  
            then obtain u v where F: "F = \<not>.((atom u) \<and>. (atom v))" 
            and "u\<in>(level A r n)" and "v\<in>(level A r n)" and "u\<noteq>v"
              by auto
            show "t_v_evaluation (path_interpretation A r ?u) F = Ttrue"  
            proof(rule ccontr)
              assume "t_v_evaluation (path_interpretation A r ?u) F \<noteq> Ttrue"
              hence "t_v_evaluation (path_interpretation A r ?u) F = Ffalse"
                using Bivaluation by auto
              hence
              "t_v_evaluation (path_interpretation A r ?u)((atom u) \<and>.
               (atom v)) = Ttrue" 
                using F  NegationValues1 by blast
              hence "t_v_evaluation (path_interpretation A r ?u)(atom u) = Ttrue \<and>
              t_v_evaluation (path_interpretation A r ?u)(atom v) = Ttrue"
                using ConjunctionValues by blast
              hence "(u,?u)\<in>r" and  "(v,?u)\<in>r"
                using  value_path_interpretation by auto
              hence a: "(level A r n) \<inter> (level A r n) = {}"
                using `tree A r`  `u\<in>(level A r n)`  `v\<in>(level A r n)`  `u\<noteq>v`
                emptyness_inter_diff_levels[of A r]
                by blast
              have "(level A r n) \<noteq> {}" 
                using  `v\<in>(level A r n)` by auto           
              thus False using a by auto 
            qed
          qed
        qed
      qed
    qed
  qed
  thus "satisfiable S" by(unfold satisfiable_def, auto)
qed

definition \<B>:: "'a set \<Rightarrow> ('a  \<Rightarrow> v_truth) \<Rightarrow> 'a set" where
"\<B> A I  \<equiv> {u|u. u\<in>A \<and> t_v_evaluation I (atom u) = Ttrue}"

lemma value_disjunction_list1:
  assumes "t_v_evaluation I (disjunction_nodes (a # l)) = Ttrue"
  shows "t_v_evaluation I (atom a) = Ttrue \<or> t_v_evaluation I (disjunction_nodes l) = Ttrue" 
proof-
  have "disjunction_nodes (a # l) = (atom a) \<or>. (disjunction_nodes l)"
    by auto
  hence "t_v_evaluation I ((atom a) \<or>. (disjunction_nodes l)) = Ttrue" 
    using assms by auto
  thus ?thesis using DisjunctionValues by blast
qed

lemma value_disjunction_list:
  assumes "t_v_evaluation I (disjunction_nodes l) = Ttrue"
  shows "\<exists>x. x \<in> set l \<and> t_v_evaluation I (atom x) = Ttrue" 
proof-
  have "t_v_evaluation I (disjunction_nodes l) = Ttrue \<Longrightarrow>
  \<exists>x. x \<in> set l \<and>  t_v_evaluation I (atom x) = Ttrue" 
  proof(induct l)
    case Nil
    then show ?case by auto
  next   
    case (Cons a l)  
    show  "\<exists>x. x \<in> set (a # l) \<and> t_v_evaluation I (atom x) = Ttrue"  
    proof-
      have "t_v_evaluation I (atom a) = Ttrue \<or> t_v_evaluation I (disjunction_nodes l)=Ttrue" 
        using Cons(2) value_disjunction_list1[of I] by auto      
      thus ?thesis
    proof(rule disjE)
      assume "t_v_evaluation I (atom a) = Ttrue"
      thus ?thesis by auto
    next
      assume "t_v_evaluation I (disjunction_nodes l) = Ttrue" 
      thus ?thesis
        using Cons by auto    
    qed
  qed
qed
  thus ?thesis using assms by auto
qed 

lemma intersection_branch_set_nodes_at_level:
  assumes "infinite_tree A r" and "finitely_branching A r" 
  and I: "\<forall>F \<in> (\<F> A r). t_v_evaluation I F = Ttrue"
shows "\<forall>n. \<exists>x. x \<in> level A r n \<and> x \<in> (\<B> A I)" using all_levels_non_empty
proof- 
  fix n 
  have "\<forall>n. t_v_evaluation I (disjunction_nodes(set_to_list (level A r n))) = Ttrue"
    using I by (unfold \<F>_def, auto)
  hence 1:
  "\<forall>n. \<exists>x. x \<in> set (set_to_list (level A r n)) \<and> t_v_evaluation I (atom x) = Ttrue"
    using value_disjunction_list by auto
  have "tree A r" 
    using `infinite_tree A r`by auto
  hence "\<forall>n. set (set_to_list (level A r n)) = level A r n" 
    using assms(1-2)  set_set_to_list1 by auto
  hence  "\<forall>n. \<exists>x. x \<in> level A r n \<and>  t_v_evaluation I (atom x) = Ttrue"
    using 1  by auto
  hence  "\<forall>n. \<exists>x. x \<in> level A r n \<and> x\<in>A \<and> t_v_evaluation I (atom x) = Ttrue" 
    by(unfold level_def, auto)
  thus ?thesis using \<B>_def[of A I] by auto
qed

lemma intersection_branch_emptyness_below_height:
  assumes I:  "\<forall>F \<in> (\<H> A r). t_v_evaluation I F = Ttrue" 
  and "x\<in>(\<B> A I)"  and  "y\<in>(\<B> A I)"  and  "x \<noteq> y" and  n: "x \<in> level A r n"
  and m: "y \<in> level A r m" 
shows  "n \<noteq> m"
proof(rule ccontr)
  assume "\<not> n \<noteq> m"
  hence "n=m" by auto
  have "x\<in>A" and  "y\<in>A" and v1: "t_v_evaluation I (atom x) = Ttrue" 
  and v2: "t_v_evaluation I (atom y) = Ttrue" 
    using  `x\<in>(\<B> A I)` `y\<in>(\<B> A I)`  by(unfold \<B>_def, auto) 
  have "\<not>.((atom x) \<and>. (atom y)) \<in> (\<H>n A r n)" 
    using `x\<in>A`   `y\<in>A`  `x \<noteq> y` n m `n=m`
    by(unfold \<H>n_def, auto)             
  hence "\<not>.((atom x) \<and>. (atom y)) \<in> (\<H> A r)"
    by(unfold \<H>_def, auto)                   
  hence "t_v_evaluation I (\<not>.((atom x) \<and>. (atom y))) = Ttrue"
    using I by auto
  moreover                  
  have "t_v_evaluation I ((atom x) \<and>. (atom y)) = Ttrue"
    using v1 v2 v_conjunction_def by auto
  hence "t_v_evaluation I (\<not>.((atom x) \<and>. (atom y))) = Ffalse" 
    using v_negation_def by auto 
  ultimately
  show False by auto
qed

lemma intersection_branch_level: 
  assumes  "infinite_tree A r" and "finitely_branching A r" 
  and I: "\<forall>F \<in> (\<F> A r) \<union> (\<H> A r). t_v_evaluation I F = Ttrue"
shows "\<forall>n. \<exists>u. (\<B> A I) \<inter>  level A r n = {u}"
proof
  fix n 
  show "\<exists>u. (\<B> A I) \<inter> level A r n = {u}" 
  proof-
    have "\<exists>u. u \<in> level A r n \<and> u \<in> (\<B> A I)" 
      using assms intersection_branch_set_nodes_at_level[of A r I] by auto
    then obtain u where u: "u \<in> level A r n \<and> u\<in>(\<B> A I)" by auto
    hence 1:  "{u} \<subseteq> (\<B> A I) \<inter> level A r n" by blast
    have 2:  "(\<B> A I) \<inter> level A r n \<subseteq> {u}"
    proof(rule subsetI)
      fix x
      assume  "x\<in>(\<B> A I) \<inter> level A r n"
      hence 2: "x\<in>(\<B> A I) \<and> x\<in> level A r n"  by auto
      have "u = x"
      proof(rule ccontr)
        assume "u \<noteq> x"
        hence "n\<noteq>n" 
          using u 2 I intersection_branch_emptyness_below_height[of A r] by blast
        thus False by auto
      qed
      thus "x\<in>{u}" by auto
    qed
    have "(\<B> A I) \<inter> level A r n = {u}"
      using 1 2 by auto
    thus "\<exists>u.(\<B> A I) \<inter>  level A r n = {u}"  by auto
  qed
qed

lemma predecessor_in_branch:
  assumes I:  "\<forall>F \<in> (\<G> A r). t_v_evaluation I F = Ttrue" 
  and "y\<in>(\<B> A I)"  and  "(x,y)\<in> r" and "x\<in>A" and "y\<in>A"
shows "x\<in>(\<B> A I)"
proof- 
  have "(atom y) \<rightarrow>. (atom x)\<in> \<G> A r" 
    using `x\<in>A`  `y\<in>A`  `(x, y)\<in>r` by (unfold  \<G>_def, auto)
  hence "t_v_evaluation I ((atom y) \<rightarrow>. (atom x)) = Ttrue"
    using I by auto
  moreover
  have "t_v_evaluation I (atom y) = Ttrue" 
    using  `y\<in>(\<B> A I)` by(unfold \<B>_def, auto)
  ultimately
  have "t_v_evaluation I (atom x) = Ttrue"
    using v_implication_def by  auto
  thus  "x\<in>(\<B> A I)" using  `x\<in>A`  by(unfold \<B>_def, auto) 
qed

lemma is_path: 
  assumes  "infinite_tree A r" and "finitely_branching A r" 
  and I: "\<forall>F \<in> (\<T> A r). t_v_evaluation I F = Ttrue" 
shows "path (\<B> A I) A r"
proof(unfold path_def)
  let ?B = "(\<B> A I)" 
  have "tree A r" 
  using  `infinite_tree A r` by auto
  have "\<forall>F \<in> (\<F> A r) \<union> (\<G> A r) \<union> (\<H> A r). t_v_evaluation I F = Ttrue"
    using I by(unfold \<T>_def)
  hence I1:  "\<forall>F \<in> (\<F> A r). t_v_evaluation I F = Ttrue" 
  and   I2:  "\<forall>F \<in> (\<G> A r). t_v_evaluation I F = Ttrue"
  and   I3:  "\<forall>F \<in> (\<H> A r). t_v_evaluation I F = Ttrue" 
    by auto 
  have 0: "sub_linear_order ?B A r"
  proof(unfold sub_linear_order_def)
    have 1: "?B \<subseteq> A"  by(unfold \<B>_def, auto)
    have 2: "strict_part_order A r" 
      using `tree A r` tree[of A r] by auto
    have "total_on ?B r"
    proof(unfold total_on_def)
      show "\<forall>x\<in>?B. \<forall>y\<in>?B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
      proof
        fix x
        assume "x\<in>?B" 
        show "\<forall>y\<in>?B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
        proof              
          fix y
          assume "y\<in>?B"
          show "x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r" 
          proof(rule impI)
            assume "x \<noteq> y" 
            have "x\<in>A" and "y\<in>A" and v1: "t_v_evaluation I (atom x) = Ttrue" 
            and v2: "t_v_evaluation I (atom y) = Ttrue" 
              using `x\<in>?B` `y\<in>?B`  by(unfold \<B>_def, auto)
            have "(\<exists>n. x \<in> level A r n)" and "(\<exists>m. y \<in> level A r m)" 
              using `x\<in>A` and `y\<in>A` level_element[of A r]
              by auto
            then obtain n m
            where n: "x \<in> level A r n" and m: "y \<in> level A r m"
              by auto             
            have "n\<noteq>m"
              using I3 `x\<in>?B` `y\<in>?B` `x \<noteq> y` n m 
                    intersection_branch_emptyness_below_height[of A r]
              by auto                
            hence "n<m \<or> m<n" by auto
            thus "(x, y) \<in> r \<or> (y, x) \<in> r" 
            proof(rule disjE)
              assume  "n < m"  
              have "(x, y) \<in> r"
              proof(rule ccontr)
                assume "(x, y) \<notin> r"
                have "\<exists>z. (z, y)\<in>r \<and> z \<in> level A r n" 
                  using `tree A r` `y \<in> level A r m` `n < m`
                         path_to_node[of A r y "m-1"]
                  by auto 
                then obtain z where z1: "(z, y)\<in>r" and z2: "z \<in> level A r n"
                  by auto 
                have "z\<in>A" using  `tree A r` tree z1 by auto
                hence "z\<in>(\<B> A I)" 
                  using I2 `y\<in>A` `y\<in>?B` `(z, y)\<in>r` predecessor_in_branch[of A r I y z]
                  by auto
                have "x\<noteq>z" using `(x, y) \<notin> r` `(z, y)\<in>r` by auto  
                hence "n\<noteq>n"
                  using I3 `x\<in>?B` `z\<in>?B` n z2  intersection_branch_emptyness_below_height[of A r]
                  by blast  
                thus False by auto 
              qed
              thus "(x, y) \<in> r \<or> (y, x) \<in> r" by auto
            next
              assume "m < n"
              have "(y, x) \<in> r"
              proof(rule ccontr)
                assume "(y, x) \<notin> r"
                have "\<exists>z. (z, x)\<in>r \<and> z \<in> level A r m" 
                  using `tree A r`  `x \<in> level A r n`  `m < n`
                         path_to_node[of A r x "n-1"]
                  by auto 
                  then obtain z where z1: "(z, x)\<in>r" and z2: "z \<in> level A r m"
                  by auto 
                have "z\<in>A" using  `tree A r` tree z1 by auto
                hence  "z\<in>(\<B> A I)" 
                  using I2 `x\<in>A` `x\<in>?B` `(z, x)\<in>r` predecessor_in_branch[of A r I x z]
                  by auto
                have "y\<noteq>z" using `(y, x) \<notin> r` `(z, x)\<in>r` by auto  
                hence "m\<noteq>m"
                  using I3 `y\<in>?B` `z\<in>?B` m z2 intersection_branch_emptyness_below_height[of A r ]
                  by blast
                thus False by auto 
              qed
              thus "(x, y) \<in> r \<or> (y, x) \<in> r" by auto
            qed
          qed
        qed
      qed
    qed
    thus 3: "?B \<subseteq> A \<and> strict_part_order A r \<and> total_on ?B r"
      using 1 2 by auto             
  qed             
  have 4: "(\<forall>C. ?B \<subseteq> C \<and> sub_linear_order C A r \<longrightarrow> ?B = C)"               
  proof
    fix C
    show "?B \<subseteq> C \<and> sub_linear_order C A r \<longrightarrow> ?B = C"
    proof(rule impI)
      assume "?B \<subseteq> C \<and> sub_linear_order C A r"
      hence "?B \<subseteq> C" and  "sub_linear_order C A r" by auto
      have "C \<subseteq> ?B"           
      proof(rule subsetI)
          fix x
          assume "x\<in> C"
        have "C \<subseteq> A"
          using `sub_linear_order C A r`
         by(unfold sub_linear_order_def, auto)
        hence "x\<in>A" using `x\<in>C` by auto
        have "\<exists>n. x\<in>level A r n" 
          using `x\<in>A` level_element[of A] by auto
        then obtain n where n: "x\<in>level A r n" by auto
        have "\<exists>u. (\<B> A I) \<inter> level A r n = {u}"
          using assms(1,2) I1 I3 intersection_branch_level[of A r]
          by blast
        then obtain u where i: "(\<B> A I) \<inter> level A r n = {u}" 
          by auto
        hence "u\<in>A" and u: "u \<in> level A r n"
         by(unfold level_def, auto)
        have "x=u" 
        proof(rule ccontr)               
          assume hip: "x\<noteq>u" 
          have "u\<in>(\<B> A I)" using i by auto
          hence "u\<in>C" using `?B \<subseteq> C` by auto
          have "total_on C r"
            using `sub_linear_order C A r` sub_linear_order_def[of C A r]
            by blast         
          hence "(x,u)\<in>r \<or> (u,x)\<in>r" 
            using hip `x\<in>C` `u\<in>C` `sub_linear_order C A r`
            by(unfold total_on_def,auto)
          thus False
          proof(rule disjE)
            assume "(x,u)\<in>r"               
            have "r \<subseteq> A \<times> A" and "strict_part_order A r" 
            and "finite (predecessors A u r)"
              using `u\<in>A` `tree A r` tree[of A r] by auto
            hence  "(level A r n) \<noteq> (level A r n)" 
              using `(x,u)\<in>r` `x \<in> level A r n` `u \<in> level A r n` 
                    different_levels_finite_pred[of r A ] by blast
            thus False by auto
          next
            assume "(u,x)\<in>r"               
            have "r \<subseteq> A \<times> A" and "strict_part_order A r" 
            and "finite (predecessors A x r)"
              using `x\<in>A` `tree A r` tree[of A r]  by auto
            hence "(level A r n) \<noteq> (level A r n)" 
              using `(u,x)\<in>r` `u \<in> level A r n` `x \<in> level A r n`
                    different_levels_finite_pred[of r A ] by blast
            thus False by auto
          qed
        qed          
        thus "x \<in> ?B" using i by auto
      qed
      thus  "?B = C"  using `?B \<subseteq> C` by blast
    qed
  qed
  thus "sub_linear_order (\<B> A I) A r \<and>
          (\<forall>C. \<B> A I \<subseteq> C \<and> sub_linear_order C A r \<longrightarrow> \<B> A I = C)"
    using `sub_linear_order (\<B> A I) A r` by auto
qed

lemma surjective_infinite:
  assumes  "\<exists>f:: 'a \<Rightarrow> nat. \<forall>n. \<exists>x\<in>A. n = f(x)"
  shows "infinite A"
proof(rule ccontr)
  assume "\<not> infinite A"
  hence "finite A" by auto
  hence "\<exists>n. \<exists>g. A = g ` {i::nat. i < n}"
    using finite_imp_nat_seg_image_inj_on[of A] by auto 
  then obtain n g where g: "A = g ` {i::nat. i < n}" by auto
  obtain f where  "(\<forall>n. \<exists>x\<in>A. n = (f:: 'a \<Rightarrow>  nat)(x))" 
    using assms by auto
  hence "\<forall>m. \<exists>k\<in>{i::nat. i < n}. m =(f \<circ> g)(k)"
    using g  by auto
  hence  "(UNIV :: nat set)  = (f \<circ> g) ` {i::nat. i < n}"
    by blast
  hence  "finite (UNIV :: nat set)" 
    using nat_seg_image_imp_finite by blast 
  thus False by auto
qed

lemma family_intersection_infinita:
  fixes P :: " nat \<Rightarrow> 'a set"
  assumes "\<forall>n. \<forall>m. n \<noteq> m \<longrightarrow> P n \<inter> P m = {}" 
  and  "\<forall>n. (A \<inter> (P n)) \<noteq> {}"
  shows "infinite (\<Union>n. (A \<inter> (P n)))" 
proof-
  let ?f = "\<lambda>x. SOME n. x\<in>(A \<inter> (P n))"
  have "\<forall>n. \<exists>x\<in>(\<Union>n. (A \<inter> (P n))). n = ?f(x)"
  proof
    fix n
    obtain a where a:  "a \<in> (A \<inter> (P n))" using assms(2) by auto
    {fix m
    have  "a \<in> (A \<inter> (P m)) \<longrightarrow> m=n" 
    proof(rule impI)
      assume hip: "a \<in> A \<inter> P m" show "m =n"
      proof(rule ccontr)
        assume "m \<noteq> n"
        hence "P m \<inter> P n = {}" using assms(1) by auto
        thus False using a hip by auto
      qed
    qed}
    hence "\<And>m. a \<in> A \<inter> P m \<Longrightarrow> m = n" by auto
    hence 1: "?f(a) = n"  using a  some_equality by auto
    have "a\<in>(\<Union>n. (A \<inter> (P n)))" using a by auto
    thus "\<exists>x\<in>\<Union>n. A \<inter> P n. n = (SOME n. x \<in> A \<inter> P n)" using 1 by auto
  qed
  hence  "\<exists>f:: 'a \<Rightarrow>  nat. \<forall>n. \<exists>x\<in>((\<Union>n. (A \<inter> (P n)))). n = f(x)" 
    using exI  by auto
  thus ?thesis using surjective_infinite by auto
qed

lemma infinite_path:
  assumes  "infinite_tree A r" and  "finitely_branching A r"
  and  I: "\<forall>F \<in> (\<F> A r). t_v_evaluation I F = Ttrue"
shows "infinite (\<B> A I)"
proof-
  have a: "\<forall>n. \<forall>m.  n \<noteq> m \<longrightarrow> level A r n \<inter> level A r m = {}"
    using uniqueness_level[of _ _ A r] by auto 
  have  "\<forall>n. \<B> A I \<inter> level A r n \<noteq> {}"
    using `infinite_tree A r`
          `finitely_branching A r` I  intersection_branch_set_nodes_at_level[of A r]
    by blast  
  hence  "infinite (\<Union>n. (\<B> A I) \<inter>  level A r n)"
    using family_intersection_infinita  a  by auto
  thus "infinite (\<B> A I)"by auto 
qed

theorem Koenig_Lemma:
  assumes  "infinite_tree (A::'nodes:: countable set) r" 
  and "finitely_branching A r" 
  shows  "\<exists>B. infinite_path B A r"
proof-
  have  "satisfiable (\<T> A r)" 
  proof- 
    have "\<forall> S. S \<subseteq> (\<T> A r) \<and> (finite S) \<longrightarrow> satisfiable S" 
      using `infinite_tree A r` `finitely_branching A r` satisfiable_path
      by auto   
    thus "satisfiable (\<T> A r)"
      using Compactness_Theorem[of "(\<T> A r)"] by auto
  qed
  hence "\<exists>I. (\<forall>F \<in> (\<T> A r). t_v_evaluation I F = Ttrue)" 
    by(unfold satisfiable_def, unfold model_def, auto) 
  then obtain I where I:  "\<forall>F \<in> (\<T> A r). t_v_evaluation I F = Ttrue"  
    by auto
  hence "\<forall>F \<in> (\<F> A r) \<union> (\<G> A r) \<union> (\<H> A r). t_v_evaluation I F = Ttrue"
    by(unfold \<T>_def)
  hence I1:  "\<forall>F \<in> (\<F> A r). t_v_evaluation I F = Ttrue" 
  and   I2:  "\<forall>F \<in> (\<G> A r). t_v_evaluation I F = Ttrue"
  and   I3:  "\<forall>F \<in> (\<H> A r). t_v_evaluation I F = Ttrue" 
    by auto 
  let ?B = "(\<B> A I)"
  have "infinite_path ?B A r"
  proof(unfold infinite_path_def)
    show "path ?B A r \<and> infinite ?B" 
    proof(rule conjI)
      show "path ?B A r"
        using  `infinite_tree A r` `finitely_branching A r` I is_path[of A r]
        by auto   
      show "infinite (\<B> A I)"
        using `infinite_tree A r` `finitely_branching A r` I1 infinite_path
      by auto     
    qed
  qed
  thus "\<exists>B. infinite_path B A r" by auto
qed
           
end
