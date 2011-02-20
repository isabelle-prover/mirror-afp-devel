
header {*  Generalization of Deutsch-Schorr-Waite Algorithm  *}

theory LinkMark
imports StackMark
begin

text {*
In the third step the stack diagram is refined to a diagram where no extra 
memory is used. The relation $next$  is replaced by two new variables $link$ and $label$. 
The variable $\mathit{label}:\mathit{node}\to \mathit{index}$ associates a label to every node and the variable
$\mathit{link}: \mathit{index}\to \mathit{node}\to \mathit{node}$ is a collection of pointer functions indexed by the set  
$\mathit{index}$ of labels. For $x\in \mathit{node}$, $\mathit{link} \ i \ x$ is the successor node of $x$  along 
the function $\mathit{link} \ i$. In this context a node $x$ is reachable if there exists a path 
from the root to $x$  along the links $\mathit{link} \ i$  such that all nodes in this path are 
not $\mathit{nil}$ and they are labeled by a special label $\mathit{none}\in \mathit{index}$.

The stack variable $S$ is replaced by two new variables $p$ and $t$ ranging over nodes. Variable $p$ 
stores the head of $S$,  $t$ stores the head of the tail of $S$, and the rest of $S$ 
is stored by temporarily modifying the variables $\mathit{link}$ and $\mathit{label}$.

This algorithm is a generalization of the Deutsch-Schorr-Waite graph marking algorithm because
we have a collection of pointer functions instead of left and right only.
*}

locale pointer = node +
  fixes none :: "'index"
  fixes link0::"'index \<Rightarrow> 'node \<Rightarrow> 'node"
  fixes label0 :: "'node \<Rightarrow> 'index"
  (* next assume is used to bind the type variable 'node introduced in this locale to the type variable 'node introduced in the locale node. *)
  assumes "(nil::'node) = nil"
begin
  definition "next =  {(a, b) . (\<exists> i . link0 i a = b) \<and> a \<noteq> nil \<and> b \<noteq> nil \<and> label0 a = none}"
end;

sublocale  pointer \<subseteq> graph "nil" "root" "next"
  apply unfold_locales;
  apply (unfold next_def);
  by auto;

text{*
The locale pointer fixes the initial values for the variables $ \mathit{link}$ and $ \mathit{label}$ and
it defines the relation next as the union of all $ \mathit{link} \ i$ functions, excluding
the mappings to $ \mathit{nil}$, the mappings from $ \mathit{nil}$ as well as the mappings from elements which
are not labeled by $ \mathit{none}$.
*}

text{*
The next two recursive functions, $ \mathit{label}\_0$, $ \mathit{link}\_0$ are used to compute
the initial values of the variables $ \mathit{label}$ and $ \mathit{link}$ from their current
values.
*}

context pointer
begin
primrec
  label_0:: "('node \<Rightarrow> 'index) \<Rightarrow> ('node list) \<Rightarrow> ('node \<Rightarrow> 'index)" where 
   "label_0 lbl []      = lbl" |
   "label_0 lbl (x # l) = label_0 (lbl(x := none)) l";

lemma label_cong [cong]: "f = g \<Longrightarrow> xs = ys \<Longrightarrow> pointer.label_0 n f xs = pointer.label_0 n g ys"
by simp

primrec
  link_0:: "('index \<Rightarrow> 'node \<Rightarrow> 'node) \<Rightarrow> ('node \<Rightarrow> 'index) \<Rightarrow> 'node \<Rightarrow> ('node list) \<Rightarrow> ('index \<Rightarrow> 'node \<Rightarrow> 'node)" where
  "link_0 lnk lbl p []       = lnk" |
  "link_0 lnk lbl p (x # l)  = link_0 (lnk((lbl x) := ((lnk (lbl x))(x := p)))) lbl x l";

text{*
The function $ \mathit{stack}$ defined bellow is the main data refinement relation connecting
the stack from the abstract algorithm to its concrete representation by temporarily
modifying the variable $ \mathit{link}$ and $ \mathit{label}$.
*}

primrec
  stack:: "('index \<Rightarrow> 'node \<Rightarrow> 'node) \<Rightarrow> ('node \<Rightarrow> 'index) \<Rightarrow> 'node \<Rightarrow> ('node list) \<Rightarrow> bool" where
  "stack lnk lbl x []       = (x = nil)" |
  "stack lnk lbl x (y # l)  = 
      (x \<noteq> nil \<and> x = y \<and> \<not> x \<in> set l \<and> stack lnk lbl (lnk (lbl x) x) l)";


lemma label_out_range0 [simp]:
  "\<not> x \<in> set S \<Longrightarrow> label_0 lbl S x = lbl x";
  apply (rule_tac P="\<forall> label . \<not> x \<in> set S \<longrightarrow> label_0 label S x = label x" in mp);
  by (simp, induct_tac S, auto);

lemma link_out_range0 [simp]:
  "\<not> x \<in> set S \<Longrightarrow> link_0 link label p S i x = link i x";
  apply (rule_tac P="\<forall> link p . \<not> x \<in> set S \<longrightarrow> link_0 link label p S i x = link i x" in mp);
  by (simp, induct_tac S, auto);


lemma link_out_range [simp]: "\<not> x \<in> set S \<Longrightarrow> link_0 link (label(x := y)) p S = link_0 link label p S";
  apply (rule_tac P="\<forall> link p . \<not> x \<in> set S \<longrightarrow> link_0 link (label(x := y)) p S = link_0 link label p S" in mp);
  by (simp, induct_tac S, auto);

lemma empty_stack [simp]: "stack link label nil S = (S = [])";
  by (case_tac S, simp_all);

lemma stack_out_link_range [simp]: "\<not> p \<in> set S \<Longrightarrow> stack (link(i := (link i)(p := q))) label x S = stack link label x S";
  apply (rule_tac P = "\<forall> link x . \<not> p \<in> set S \<longrightarrow> stack (link(i := (link i)(p := q))) label x S = stack link label x S" in mp);
  by (simp, induct_tac S, auto);

lemma stack_out_label_range [simp]: "\<not> p \<in> set S \<Longrightarrow> stack link (label(p := q)) x S = stack link label x S";
  apply (rule_tac P = "\<forall> link x . \<not> p \<in> set S \<longrightarrow> stack link (label(p := q)) x S = stack link label x S" in mp);
  by (simp, induct_tac S, auto);

definition
  "g mrk lbl ptr x \<equiv> ptr x \<noteq> nil \<and> ptr x \<notin> mrk \<and> lbl x = none"

lemma g_cong [cong]: "mrk = mrk1 \<Longrightarrow> lbl = lbl1 \<Longrightarrow> ptr = ptr1 \<Longrightarrow> x = x1 ==> 
       pointer.g n m mrk lbl ptr x = pointer.g n m mrk1 lbl1 ptr1 x1"
by simp

subsection {* Transitions *}

definition
  "Q1'' s \<equiv> let (p, t, lnk, lbl, mrk) = s in { (p', t', lnk', lbl', mrk') .
      root = nil \<and> p' = nil \<and> t' = nil \<and> lnk' = lnk \<and> lbl' = lbl \<and> mrk' = mrk}";


definition
  "Q2'' s \<equiv> let (p, t, lnk, lbl, mrk) = s in { (p', t', lnk', lbl', mrk') .
      root \<noteq> nil \<and> p' = root \<and> t' = nil \<and> lnk' = lnk \<and> lbl' = lbl \<and> mrk' = mrk \<union> {root}}";

definition
  "Q3'' s \<equiv> let (p, t, lnk, lbl, mrk) = s in { (p', t', lnk', lbl', mrk') .
         p \<noteq> nil \<and> 
         (\<exists> i . g mrk lbl (lnk i) p \<and> 
            p' = lnk i p \<and> t' =  p \<and> lnk' =  lnk(i := (lnk i)(p := t)) \<and> lbl' = lbl(p := i) \<and>
            mrk' = mrk \<union> {lnk i p})}";

definition
  "Q4'' s  \<equiv> let (p, t, lnk, lbl, mrk) = s in { (p', t', lnk', lbl', mrk') .
          p \<noteq> nil \<and> 
          (\<forall> i . \<not> g mrk lbl (lnk i) p) \<and> t \<noteq> nil \<and> 
          p' = t \<and> t' = lnk (lbl t) t \<and> lnk' = lnk(lbl t := (lnk (lbl t))(t := p)) \<and> lbl' = lbl(t := none) \<and> 
          mrk' = mrk}"

definition
  "Q5'' s \<equiv> let (p, t, lnk, lbl, mrk) = s in { (p', t', lnk', lbl', mrk') .
           p \<noteq> nil \<and> 
          (\<forall> i . \<not> g mrk lbl (lnk i) p) \<and> t = nil \<and>
           p' = nil \<and> t' = t \<and> lnk' =  lnk \<and> lbl' = lbl \<and> mrk' = mrk}";

definition
  "Q6'' s \<equiv> let (p, t, lnk, lbl, mrk) = s in {(p', t', lnk', lbl', mrk') . p = nil \<and>  
         p' = p \<and> t' = t \<and> lnk' = lnk \<and> lbl' =  lbl \<and> mrk' = mrk}";

subsection {* Invariants *}

definition
  "Init'' \<equiv> { (p, t, lnk, lbl, mrk) . lnk = link0 \<and> lbl = label0}";

definition
  "Loop'' \<equiv> UNIV";

definition
  "Final'' \<equiv> Init''";

subsection {* Data refinement relations *}

definition 
  "R1' \<equiv> (\<lambda> (p, t, lnk, lbl, mrk) . {(stk, mrk') . (p, t, lnk, lbl, mrk) \<in> Init'' \<and> mrk' = mrk})";

definition  
  "R2' \<equiv> (\<lambda> (p, t, lnk, lbl, mrk) . {(stk, mrk') .  
       p = head stk \<and>  
       t = head (tail stk) \<and>  
       stack lnk lbl t (tail stk) \<and> 
       link0 = link_0 lnk lbl p (tail stk) \<and> 
       label0 = label_0 lbl (tail stk) \<and>
       \<not> nil \<in> set stk \<and> 
       mrk' = mrk})";

definition [simp]:
  "R' i = (case i of
      I.init  \<Rightarrow> R1' |
      I.loop  \<Rightarrow> R2' |
      I.final \<Rightarrow> R1')";

subsection{* Diagram *}

definition
  "LinkMark_rel = (\<lambda> (i, j) . (case (i, j) of
      (I.init, I.loop)  \<Rightarrow> Q1'' \<squnion> Q2'' |
      (I.loop, I.loop)  \<Rightarrow> Q3'' \<squnion> (Q4'' \<squnion> Q5'') |
      (I.loop, I.final) \<Rightarrow> Q6'' |
       _ \<Rightarrow> \<bottom>))";

definition [simp]:
  "LinkMarkInv i = (case i of
      I.init  \<Rightarrow> Init'' |
      I.loop  \<Rightarrow> Loop'' |
      I.final \<Rightarrow> Final'')";

subsection {* Data refinement of the transitions *}

theorem init1 [simp]:
  "DataRefinement Init' Q1' R1' R2' (demonic Q1'')";
  by (simp add: DataRefinement_def hoare_demonic Q1''_def Init'_def Init''_def 
       Loop''_def R1'_def R2'_def Q1'_def tail_def head_def angelic_def subset_eq);

theorem init2 [simp]:
  "DataRefinement Init' Q2' R1' R2' (demonic Q2'')";
  by (simp add: DataRefinement_def hoare_demonic Q2''_def Init'_def Init''_def 
       Loop''_def R1'_def R2'_def Q2'_def tail_def head_def angelic_def subset_eq);

theorem step1 [simp]:
  "DataRefinement Loop' Q3' R2' R2' (demonic Q3'')";
  apply (simp add: DataRefinement_def hoare_demonic Q3''_def Init'_def Init''_def 
       Loop'_def R1'_def Q3'_def tail_def head_def angelic_def subset_eq);
  apply (simp add: simp_eq_emptyset);
  apply auto;
  apply (unfold next_def);
  apply (unfold R2'_def);
  apply (simp add: simp_eq_emptyset);
  apply safe;
  apply simp;
  apply (rule_tac x = "ac i (hd a) # a" in exI);
  apply safe;
  apply simp_all;
  apply (simp add: g_def  neq_Nil_conv);
  apply clarify;
  apply (simp add: g_def  neq_Nil_conv);
  apply (case_tac a);
  apply (simp_all add: g_def  neq_Nil_conv);
  apply (case_tac a);
  apply simp_all;
  apply (case_tac a);
  by auto;

lemma neqif [simp]: "x \<noteq> y \<Longrightarrow> (if y = x then a else b) = b"
  apply (case_tac "y \<noteq> x");
  apply simp_all;
  done;

theorem step2 [simp]:
  "DataRefinement Loop' Q4' R2' R2' (demonic Q4'')";
  apply (simp add: DataRefinement_def hoare_demonic Q4''_def Init'_def Init''_def 
       Loop'_def Q4'_def angelic_def subset_eq);
  apply (simp add: simp_eq_emptyset);
  apply safe;
  apply (unfold next_def);
  apply (unfold R2'_def);
  apply (simp_all add: neq_Nil_conv);
  apply auto [1];
  apply (case_tac ysa);
  apply (simp add: head_def);
  apply (simp add: head_def);
  apply (case_tac a);
  apply simp;
  apply simp;
  apply (unfold g_def);
  by auto;

lemma setsimp: "a = c \<Longrightarrow> (x \<in> a) = (x \<in> c)"; 
  apply simp;
  done;

theorem step3 [simp]:
  "DataRefinement Loop' Q4' R2' R2' (demonic Q5'')";
  apply (simp add: DataRefinement_def hoare_demonic Q5''_def Init'_def Init''_def 
       Loop'_def Q4'_def angelic_def subset_eq);
  apply (unfold R2'_def);
  apply (unfold next_def);
  apply (simp add: simp_eq_emptyset);
  apply (unfold g_def);
  apply safe; 
  apply (simp_all add: head_def tail_def);
  by auto;

theorem final [simp]:
  "DataRefinement Loop' Q5' R2' R1' (demonic Q6'')";
   apply (simp add: DataRefinement_def hoare_demonic Q6''_def Init'_def Init''_def 
       Loop'_def R2'_def R1'_def Q5'_def angelic_def subset_eq neq_Nil_conv tail_def head_def);
  apply (simp add: simp_eq_emptyset);
   apply safe;
   by simp_all;

subsection {* Diagram data refinement *}

theorem LinkMark_DataRefinement [simp]:
 "DgrDataRefinement (dangelic R SetMarkInv) StackMark_rel R' (dgr_demonic LinkMark_rel)";
  apply (rule_tac P = "StackMarkInv" in DgrDataRefinement_mono);
  apply (simp add: le_fun_def dangelic_def SetMarkInv_def angelic_def R1_def R2_def Init'_def Final'_def mem_def le_bool_def);
  apply auto;
  apply (unfold simp_set_function);
  apply auto;
  apply (simp add: DgrDataRefinement_def dgr_demonic_def LinkMark_rel_def StackMark_rel_def demonic_sup_inf data_refinement_choice2);
  apply (rule data_refinement_choice2);
  apply auto;
  apply (rule data_refinement_choice);
  by auto;

subsection {* Diagram correctness *}

theorem LinkMark_correct:
  "Hoare_dgr (dangelic R' (dangelic R SetMarkInv)) (dgr_demonic LinkMark_rel) ((dangelic R' (dangelic R SetMarkInv)) \<sqinter> (- grd (step ((dgr_demonic LinkMark_rel)))))";
  apply (rule_tac T="StackMark_rel" in Diagram_DataRefinement);
  apply auto;
  by (rule StackMark_correct);


end;

end;