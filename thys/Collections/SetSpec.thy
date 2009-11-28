(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "Specification of Sets"
theory SetSpec
imports Main
begin
text_raw{*\label{thy:SetSpec}*}

text {*
  This theory specifies set operations by means of a mapping to
  HOL's standard sets.
*}

(* Drop some notation that gets in the way here*)
(*no_notation member (infixl "mem" 55)*)
notation insert ("set'_ins")

locale set =
  -- "Abstraction to set"
  fixes \<alpha> :: "'s \<Rightarrow> 'x set"
  -- "Invariant"
  fixes invar :: "'s \<Rightarrow> bool"

subsection "Basic Set Functions"

subsubsection "Empty set"

locale set_empty = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes empty :: "'s"
  assumes empty_correct:
    "\<alpha> empty = {}"
    "invar empty"

subsubsection "Membership Query"

locale set_memb = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes memb :: "'x \<Rightarrow> 's \<Rightarrow> bool"
  assumes memb_correct:
    "invar s \<Longrightarrow> memb x s \<longleftrightarrow> x \<in> \<alpha> s"

subsubsection "Insertion of Element"

locale set_ins = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes ins :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes ins_correct:
    "invar s \<Longrightarrow> \<alpha> (ins x s) = set_ins x (\<alpha> s)"
    "invar s \<Longrightarrow> invar (ins x s)"

subsubsection "Disjoint Insert"

locale set_ins_dj = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes ins_dj :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes ins_dj_correct:
    "\<lbrakk>invar s; x\<notin>\<alpha> s\<rbrakk> \<Longrightarrow> \<alpha> (ins_dj x s) = set_ins x (\<alpha> s)"
    "\<lbrakk>invar s; x\<notin>\<alpha> s\<rbrakk> \<Longrightarrow> invar (ins_dj x s)"

subsubsection "Deletion of Single Element"

locale set_delete = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes delete :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes delete_correct:
    "invar s \<Longrightarrow> \<alpha> (delete x s) = \<alpha> s - {x}"
    "invar s \<Longrightarrow> invar (delete x s)"

subsubsection "Emptiness Check"

locale set_isEmpty = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct:
    "invar s \<Longrightarrow> isEmpty s \<longleftrightarrow> \<alpha> s = {}"

subsubsection "Bounded Quantifiers"

locale set_ball = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes ball :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> bool"
  assumes ball_correct: "invar S \<Longrightarrow> ball S P \<longleftrightarrow> (\<forall>x\<in>\<alpha> S. P x)"

subsubsection "Finite Set"
locale finite_set = set +
  assumes finite[simp, intro!]: "invar s \<Longrightarrow> finite (\<alpha> s)"

subsubsection "Size"

locale set_size = finite_set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes size :: "'s \<Rightarrow> nat"
  assumes size_correct: 
    "invar s \<Longrightarrow> size s = card (\<alpha> s)"
  
subsection "Iterators"
text {*
  An iterator applies a
  function to a state and all the elements of the set.
  The function is applied in any order. Proofs over the iteration are
  done by establishing invariants over the iteration.
  *}
types
  ('s,'a,'\<sigma>) iterator = "('a \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 's \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"


locale set_iterate = finite_set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes iterate :: "('s,'x,'\<sigma>) iterator"
  -- "The iterator is specified by its invariant proof rule"
  assumes iterate_rule: "\<lbrakk> 
    invar S; 
    I (\<alpha> S) \<sigma>0; 
    !!x it \<sigma>. \<lbrakk> x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>)
  \<rbrakk> \<Longrightarrow> I {} (iterate f S \<sigma>0)"
begin

  lemma iterate_rule_P:
    assumes A: 
      "invar S" 
      "I (\<alpha> S) \<sigma>0"
      "!!x it \<sigma>. \<lbrakk> x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>)"
    assumes C: 
      "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows 
      "P (iterate f S \<sigma>0)"
    using C[OF iterate_rule[OF A(1), of I, OF A(2,3)]]
    by force

end

text {*
  Iterators may have a break-condition, that interrupts the iteration before
  the last element has been visited.
*}
types
  ('s,'a,'\<sigma>) iteratori = "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 's \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"


locale set_iteratei = finite_set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes iteratei :: "('s,'x,'\<sigma>) iteratori"

  assumes iteratei_rule: "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>)
    \<rbrakk> \<Longrightarrow> 
        I {} (iteratei c f S \<sigma>0) \<or> 
        (\<exists>it. it \<subseteq> \<alpha> S \<and> it \<noteq> {} \<and> 
              \<not> (c (iteratei c f S \<sigma>0)) \<and> 
              I it (iteratei c f S \<sigma>0))"

begin
  lemma iteratei_rule_P':
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      \<lbrakk> I {} (iteratei c f S \<sigma>0) \<rbrakk> \<Longrightarrow> P;
      !!it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> {}; 
              \<not> (c (iteratei c f S \<sigma>0)); 
              I it (iteratei c f S \<sigma>0)
            \<rbrakk> \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P"
    using iteratei_rule[of S I \<sigma>0 c f]
    by blast

  lemma iteratei_rule_P:
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei c f S \<sigma>0)"
    by (rule iteratei_rule_P')

end


subsection "More Set Operations"

subsubsection "Union"


locale set_union = set \<alpha>1 invar1 + set \<alpha>2 invar2 + set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'a set" and invar3
  +
  fixes union :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  assumes union_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> \<alpha>3 (union s1 s2) = \<alpha>1 s1 \<union> \<alpha>2 s2"
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> invar3 (union s1 s2)"


locale set_union_dj = set \<alpha>1 invar1 + set \<alpha>2 invar2 + set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'a set" and invar3
  +
  fixes union_dj :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  assumes union_dj_correct:
    "\<lbrakk>invar1 s1; invar2 s2; \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}\<rbrakk> \<Longrightarrow> \<alpha>3 (union_dj s1 s2) = \<alpha>1 s1 \<union> \<alpha>2 s2"
    "\<lbrakk>invar1 s1; invar2 s2; \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}\<rbrakk> \<Longrightarrow> invar3 (union_dj s1 s2)"

subsubsection "Intersection"

locale set_inter = set \<alpha>1 invar1 + set \<alpha>2 invar2 + set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'a set" and invar3
  +
  fixes inter :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  assumes inter_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> \<alpha>3 (inter s1 s2) = \<alpha>1 s1 \<inter> \<alpha>2 s2"
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> invar3 (inter s1 s2)"

subsubsection "Subset"

locale set_subset = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes subset :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes subset_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> subset s1 s2 \<longleftrightarrow> \<alpha>1 s1 \<subseteq> \<alpha>2 s2"

subsubsection "Equal"

locale set_equal = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes equal :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes equal_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> equal s1 s2 \<longleftrightarrow> \<alpha>1 s1 = \<alpha>2 s2"


subsubsection "Image and Filter"

locale set_image_filter = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes image_filter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes image_filter_correct_aux:
    "invar1 s \<Longrightarrow> \<alpha>2 (image_filter f s) = { b . \<exists>a\<in>\<alpha>1 s. f a = Some b }"
    "invar1 s \<Longrightarrow> invar2 (image_filter f s)"
begin
  -- "This special form will be checked first by the simplifier: "
  lemma image_filter_correct_aux2: 
    "invar1 s \<Longrightarrow> 
    \<alpha>2 (image_filter (\<lambda>x. if P x then (Some (f x)) else None) s) 
    = f ` {x\<in>\<alpha>1 s. P x}"
    by (auto simp add: image_filter_correct_aux)

  lemmas image_filter_correct = 
    image_filter_correct_aux2 image_filter_correct_aux

end

locale set_inj_image_filter = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes inj_image_filter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes inj_image_filter_correct:
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s \<inter> dom f)\<rbrakk> \<Longrightarrow> \<alpha>2 (inj_image_filter f s) = { b . \<exists>a\<in>\<alpha>1 s. f a = Some b }"
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s \<inter> dom f)\<rbrakk> \<Longrightarrow> invar2 (inj_image_filter f s)"

subsubsection "Image"

locale set_image = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes image :: "('a \<Rightarrow> 'b) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes image_correct:
    "invar1 s \<Longrightarrow> \<alpha>2 (image f s) = f`\<alpha>1 s"
    "invar1 s \<Longrightarrow> invar2 (image f s)"


locale set_inj_image = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes inj_image :: "('a \<Rightarrow> 'b) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes inj_image_correct:
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s)\<rbrakk> \<Longrightarrow> \<alpha>2 (inj_image f s) = f`\<alpha>1 s"
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s)\<rbrakk> \<Longrightarrow> invar2 (inj_image f s)"

subsubsection "Union of Set of Sets"

locale set_Union_image = set \<alpha>1 invar1 + set \<alpha>2 invar2 + set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'b set" and invar3
  +
  fixes Union_image :: "('a \<Rightarrow> 's2) \<Rightarrow> 's1 \<Rightarrow> 's3"
  assumes Union_image_correct: 
    "\<lbrakk> invar1 s; !!x. x\<in>\<alpha>1 s \<Longrightarrow> invar2 (f x) \<rbrakk> \<Longrightarrow> \<alpha>3 (Union_image f s) = \<Union>\<alpha>2`f`\<alpha>1 s"
    "\<lbrakk> invar1 s; !!x. x\<in>\<alpha>1 s \<Longrightarrow> invar2 (f x) \<rbrakk> \<Longrightarrow> invar3 (Union_image f s)"


subsubsection "Disjointness Check"

locale set_disjoint = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes disjoint :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes disjoint_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> disjoint s1 s2 \<longleftrightarrow> \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}"

subsubsection "Disjointness Check With Witness"

locale set_disjoint_witness = set \<alpha>1 invar1 + set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes disjoint_witness :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 'a option"
  assumes disjoint_witness_correct:
    "\<lbrakk>invar1 s1; invar2 s2\<rbrakk> 
      \<Longrightarrow> disjoint_witness s1 s2 = None \<Longrightarrow> \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}"
    "\<lbrakk>invar1 s1; invar2 s2; disjoint_witness s1 s2 = Some a\<rbrakk> 
      \<Longrightarrow> a\<in>\<alpha>1 s1 \<inter> \<alpha>2 s2"
begin
  lemma disjoint_witness_None: "\<lbrakk>invar1 s1; invar2 s2\<rbrakk> 
    \<Longrightarrow> disjoint_witness s1 s2 = None \<longleftrightarrow> \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}"
    by (case_tac "disjoint_witness s1 s2")
       (auto dest: disjoint_witness_correct)
    
  lemma disjoint_witnessI: "\<lbrakk>
    invar1 s1; 
    invar2 s2; 
    \<alpha>1 s1 \<inter> \<alpha>2 s2 \<noteq> {}; 
    !!a. \<lbrakk>disjoint_witness s1 s2 = Some a\<rbrakk> \<Longrightarrow> P 
                            \<rbrakk> \<Longrightarrow> P"
    by (case_tac "disjoint_witness s1 s2")
       (auto dest: disjoint_witness_correct)

end

subsubsection "Selection of Element"

locale set_sel = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes sel :: "'s \<Rightarrow> ('x \<Rightarrow> 'r option) \<Rightarrow> 'r option"
  assumes selE: 
    "\<lbrakk> invar s; x\<in>\<alpha> s; f x = Some r; 
       !!x r. \<lbrakk>sel s f = Some r; x\<in>\<alpha> s; f x = Some r \<rbrakk> \<Longrightarrow> Q 
     \<rbrakk> \<Longrightarrow> Q"
  assumes selI: "\<lbrakk>invar s; \<forall>x\<in>\<alpha> s. f x = None \<rbrakk> \<Longrightarrow> sel s f = None"
begin

  lemma sel_someD:
    "\<lbrakk> invar s; sel s f = Some r; !!x. \<lbrakk>x\<in>\<alpha> s; f x = Some r\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    apply (cases "\<exists>x\<in>\<alpha> s. \<exists>r. f x = Some r")
    apply (safe)
    apply (erule_tac f=f and x=x in selE)
    apply auto
    apply (drule (1) selI)
    apply simp
    done

  lemma sel_noneD: 
    "\<lbrakk> invar s; sel s f = None; x\<in>\<alpha> s \<rbrakk> \<Longrightarrow> f x = None"
    apply (cases "\<exists>x\<in>\<alpha> s. \<exists>r. f x = Some r")
    apply (safe)
    apply (erule_tac f=f and x=xa in selE)
    apply auto
    done
end

subsubsection "Conversion of Set to List"

locale set_to_list = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes to_list :: "'s \<Rightarrow> 'x list"
  assumes to_list_correct: 
    "invar s \<Longrightarrow> set (to_list s) = \<alpha> s"
    "invar s \<Longrightarrow> distinct (to_list s)"

subsubsection "Conversion of List to Set"

locale list_to_set = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes to_set :: "'x list \<Rightarrow> 's"
  assumes to_set_correct:
    "\<alpha> (to_set l) = set l"
    "invar (to_set l)"


no_notation insert ("set'_ins")
(*notation member (infixl "mem" 55)*)




end
