header "Base"

theory Base = Main + PermutationLemmas:

subsection "Integrate with Isabelle libraries?"

    --  "Misc"

  -- "FIXME added by tjr, forms basis of a lot of proofs of existence of inf sets"
  -- "something like this should be in FiniteSet, asserting nats are not finite"
lemma natset_finite_max: assumes a: "finite A"
  shows "Suc (Max A) \<notin> A"
proof (cases "A = {}")
  case True
  thus ?thesis by auto
next
  case False
  hence "Max A \<in> A \<and> (\<forall>s \<in> A. s \<le> Max A)" by(simp!)
  thus ?thesis by auto
qed

    -- "not used"
lemma not_finite_univ: "~ finite (UNIV::nat set)"
  apply rule
  apply(drule_tac natset_finite_max)
  by force

  -- "FIXME should be in main lib"
lemma LeastI_ex: "(\<exists> x. P (x::'a::wellorder)) \<Longrightarrow> P (LEAST x. P x)"
  by(blast intro: LeastI)


subsection "Summation"

consts summation :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
primrec 
  "summation f 0 = f 0"
  "summation f (Suc n) = f (Suc n) + summation f n"


subsection "Termination Measure"

consts exp :: "[nat,nat] \<Rightarrow> nat"
primrec 
  "exp x 0       = 1"
  "exp x (Suc m) = x * exp x m"

consts sumList     :: "nat list \<Rightarrow> nat"
primrec 
  "sumList []     = 0"
  "sumList (x#xs) = x + sumList xs"


subsection "Functions"

constdefs
  preImage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set"
  "preImage f A \<equiv> { x . f x \<in> A}"

  pre      :: "('a \<Rightarrow> 'b) => 'b \<Rightarrow> 'a set"
  "pre f a \<equiv> { x . f x = a}"

  equalOn  :: "['a set,'a => 'b,'a => 'b] => bool"
  "equalOn A f g \<equiv> (!x:A. f x = g x)"    

lemma preImage_insert: "preImage f (insert a A) = pre f a Un preImage f A"
  by(auto simp add: preImage_def pre_def)

lemma preImageI: "f x : A ==> x : preImage f A"
  apply(simp add: preImage_def) done
    
lemma preImageE: "x : preImage f A ==> f x : A"
  apply(simp add: preImage_def) done

lemma equalOn_Un:  "equalOn (A \<union> B) f g = (equalOn A f g \<and> equalOn B f g)"
  by(auto simp add: equalOn_def) 

lemma equalOnD: "equalOn A f g \<Longrightarrow> (\<forall> x \<in> A . f x = g x)"
  by(simp add: equalOn_def)

lemma equalOnI:"(\<forall> x \<in> A . f x = g x) \<Longrightarrow> equalOn A f g"
  by(simp add: equalOn_def)

lemma equalOn_UnD: "equalOn (A Un B) f g ==> equalOn A f g & equalOn B f g"
  apply(auto simp: equalOn_def) done 


    -- "FIXME move following elsewhere?"
lemma inj_inv_singleton[simp]: "\<lbrakk> inj f; f z = y \<rbrakk> \<Longrightarrow> {x. f x = y} = {z}"
  apply rule
  apply(auto simp: inj_on_def) done

lemma finite_pre[simp]: "inj f \<Longrightarrow> finite (pre f x)"
  apply(simp add: pre_def) 
  apply (cases "\<exists> y. f y = x", auto) done

lemma finite_preImage[simp]: "\<lbrakk> finite A; inj f \<rbrakk> \<Longrightarrow> finite (preImage f A)"
  apply(induct A rule: finite_induct) 
  apply(simp add: preImage_def)
  apply(simp add: preImage_insert) done


end
