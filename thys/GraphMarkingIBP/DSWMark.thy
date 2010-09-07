header {* Deutsch-Schorr-Waite Marking Algorithm *}

theory DSWMark

imports LinkMark

begin

text{*
Finally, we construct the Deutsch-Schorr-Waite marking algorithm by assuming that there 
are only two pointers ($\mathit{left}$, $\mathit{right}$) from every node. There is also a new variable,
$\mathit{atom}: \mathit{node} \to  \mathit{bool}$ which associates to every node a Boolean value.
The data invariant of this refinement step requires that $\mathit{index}$ has exactly two distinct 
elements $none$  and $\mathit{some}$, $\mathit{left} = \mathit{link}\ \mathit{none}$, 
$\mathit{right}=\mathit{link}\  \mathit{some}$, and $\mathit{atom}\ x$ is true 
if and only if $\mathit{label}\ x = \mathit{some}$.

We use a new locale which fixes the iniatial values of the variables $\mathit{left}$, $\mathit{right}$, and 
$\mathit{atom}$ in $\mathit{left0}$, $\mathit{right0}$, and $\mathit{atom0}$ respectively.
*}

datatype Index = none | some;

locale classical = node +
  fixes left0  :: "'node \<Rightarrow> 'node"
  fixes right0 :: "'node \<Rightarrow> 'node"
  fixes atom0  :: "'node \<Rightarrow> bool"
  assumes "(nil::'node) = nil"
  begin
    definition
      "link0 i = (if i = (none::Index) then left0 else right0)"

    definition
      "label0 x = (if atom0 x then (some::Index) else none)"
  end;

sublocale classical \<subseteq> pointer "nil" "root" "none::Index" "link0" "label0"
proof; qed auto;

context classical
begin

lemma [simp]:
  "(label0 = (\<lambda> x . if atom x then some else none)) = (atom0 = atom)";
  apply (simp add: ext_iff label0_def);
  by auto;

definition
  "gg mrk atom ptr x \<equiv> ptr x \<noteq> nil \<and> ptr x \<notin> mrk \<and> \<not> atom x";

subsection {* Transitions *}

definition
  "QQ1 \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
         root = nil \<and>  p' = nil \<and> t' = nil \<and> mrk' = mrk \<and> left' = left \<and> right' = right \<and> atom' = atom}";
  
definition
  "QQ2 \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
         root \<noteq> nil \<and>  p' = root \<and> t' = nil \<and> mrk' = mrk \<union> {root} \<and> left' = left \<and> right' = right \<and> atom' = atom}";

definition
  "QQ3 \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
      p \<noteq> nil \<and> gg mrk atom left p \<and>
      p' = left p \<and> t' = p \<and> mrk' = mrk \<union> {left p} \<and> 
      left' = left(p := t) \<and> right' = right \<and> atom' = atom}";

definition
  "QQ4 \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
      p \<noteq> nil \<and> gg mrk atom right p \<and>
      p' = right p \<and> t' = p \<and> mrk' = mrk \<union> {right p} \<and> 
      left' = left \<and> right' = right(p := t) \<and> atom' = atom(p := True)}";

definition
  "QQ5 \<equiv>  \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
      p \<noteq> nil \<and> (*not needed in the proof*)
      \<not> gg mrk atom left p \<and> \<not> gg mrk atom right p \<and>
      t \<noteq> nil \<and> \<not> atom t \<and>
      p' = t \<and> t' = left t \<and> mrk' = mrk \<and> 
      left' = left(t := p) \<and> right' = right \<and> atom' = atom}";


definition
  "QQ6 \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
      p \<noteq> nil \<and> (*not needed in the proof*)
      \<not> gg mrk atom left p \<and> \<not> gg mrk atom right p \<and>
      t \<noteq> nil \<and> atom t \<and>
      p' = t \<and> t' = right t \<and> mrk' = mrk \<and> 
      left' = left \<and> right' = right(t := p) \<and> atom' = atom(t := False)}";

definition
  "QQ7 \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
      p \<noteq> nil \<and>
      \<not> gg mrk atom left p \<and> \<not> gg mrk atom right p \<and>
      t = nil \<and>
      p' = nil \<and> t' = t \<and> mrk' = mrk \<and> 
      left' = left \<and> right' = right \<and> atom' = atom}";


definition
  "QQ8 \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', left', right', atom', mrk') . 
     p = nil \<and> p' = p \<and> t' = t \<and> mrk' = mrk \<and> left' = left \<and> right' = right \<and> atom' = atom}";

section {* Data refinement relation *}

definition
  "RR \<equiv> \<lambda> (p, t, left, right, atom, mrk) . {(p', t', lnk, lbl, mrk') .
          lnk none = left \<and> lnk some = right \<and>
          lbl = (\<lambda> x . if atom x then some else none) \<and>
          p' = p \<and> t' = t \<and> mrk' = mrk}";

definition [simp]:
  "R'' i = RR"

definition
  "ClassicMark_rel = (\<lambda> (i, j) . (case (i, j) of
      (I.init, I.loop)  \<Rightarrow> QQ1 \<squnion> QQ2 |
      (I.loop, I.loop)  \<Rightarrow> (QQ3 \<squnion> QQ4) \<squnion> ((QQ5 \<squnion> QQ6) \<squnion> QQ7) |
      (I.loop, I.final) \<Rightarrow> QQ8 |
       _ \<Rightarrow> \<bottom>))";

subsection {* Data refinement of the transitions *}

theorem init1 [simp]:
  "DataRefinement Init'' Q1'' RR RR (demonic QQ1)";
  by (simp add: DataRefinement_def hoare_demonic angelic_def QQ1_def Q1''_def RR_def
       Init''_def subset_eq);

theorem init2 [simp]:
  "DataRefinement Init'' Q2'' RR RR (demonic QQ2)";
  by (simp add: DataRefinement_def hoare_demonic angelic_def QQ2_def Q2''_def RR_def
       Init''_def subset_eq);

lemma index_simp: 
  "(u = v) = (u none = v none \<and> u some = v some)"
  by (safe, rule ext, case_tac "x", auto);


theorem step1 [simp]:
  "DataRefinement Loop'' Q3'' RR RR (demonic QQ3)";
  apply (simp add: DataRefinement_def hoare_demonic angelic_def QQ3_def  Q3''_def RR_def
       Loop''_def subset_eq g_def gg_def simp_eq_emptyset);
  apply safe;
  apply (rule_tac x="\<lambda> x . if x = some then ab some else (ab none)(a := aa)" in exI);
  apply simp;
  apply (rule_tac x="none" in exI);
  apply (simp add: index_simp);
  done;

theorem step2 [simp]:
  "DataRefinement Loop'' Q3'' RR RR (demonic QQ4)";
  apply (simp add: DataRefinement_def hoare_demonic angelic_def QQ4_def Q3''_def RR_def
       Loop''_def subset_eq g_def gg_def simp_eq_emptyset);
  apply safe;
  apply (rule_tac x="\<lambda> x . if x = none then ab none else (ab some)(a := aa)" in exI);
  apply simp;
  apply (rule_tac x="some" in exI);
  apply (simp add: index_simp);
  apply (rule ext);
  apply auto;
  done;


theorem step3 [simp]:
  "DataRefinement Loop'' Q4'' RR RR (demonic QQ5)";
  apply (simp add: DataRefinement_def hoare_demonic angelic_def QQ5_def Q4''_def RR_def
       Loop''_def subset_eq g_def gg_def simp_eq_emptyset);
  apply clarify;
  apply (case_tac "i");
  apply auto;
  done

lemma if_set_elim: "(x \<in> (if b then A else B)) = ((b \<and> x \<in> A) \<or> (\<not> b \<and> x \<in> B))";
  by auto;

theorem step4 [simp]:
  "DataRefinement Loop'' Q4'' RR RR (demonic QQ6)";
  apply (simp add: DataRefinement_def hoare_demonic angelic_def  QQ6_def Q4''_def
       Loop''_def subset_eq simp_eq_emptyset);

  apply safe;
  apply (simp add: RR_def);
  apply auto;
  apply (rule ext);
  apply (simp_all);
  apply (simp_all add: RR_def g_def gg_def if_set_elim);
  apply (case_tac "i");
  by auto;

theorem step5 [simp]:
  "DataRefinement Loop'' Q5'' RR RR (demonic QQ7)";
  apply (simp add: DataRefinement_def hoare_demonic angelic_def Q5''_def QQ7_def 
       Loop''_def subset_eq RR_def simp_eq_emptyset);
  apply safe;
  apply (simp_all add: g_def gg_def);
  apply (case_tac "i");
  by auto;


theorem final_step [simp]:
  "DataRefinement Loop'' Q6'' RR RR (demonic QQ8)";
  by (simp add: DataRefinement_def hoare_demonic angelic_def Q6''_def QQ8_def 
       Loop''_def subset_eq RR_def simp_eq_emptyset);

subsection {* Diagram data refinement *}

theorem ClassicMark_DataRefinement [simp]:
 "DgrDataRefinement (dangelic R' (dangelic R SetMarkInv)) LinkMark_rel R'' (dgr_demonic ClassicMark_rel)";
  apply (rule_tac P = "LinkMarkInv" in DgrDataRefinement_mono);
  apply (simp add: le_fun_def dangelic_def SetMarkInv_def angelic_def R1'_def R2'_def Init''_def Loop''_def Final''_def mem_def le_bool_def);
  apply auto;
  apply (unfold simp_set_function);
  apply auto;
  apply (simp add: DgrDataRefinement_def dgr_demonic_def ClassicMark_rel_def LinkMark_rel_def demonic_sup_inf data_refinement_choice2);
  apply (rule data_refinement_choice2);
  apply auto;
  apply (rule data_refinement_choice);
  apply auto;
  apply (rule data_refinement_choice2);
  apply auto;
  apply (rule data_refinement_choice);
  by auto;

subsection {* Diagram corectness *}

theorem ClassicMark_correct [simp]:
  "Hoare_dgr  (dangelic R'' (dangelic R' (dangelic R SetMarkInv))) (dgr_demonic ClassicMark_rel) 
   ((dangelic R'' (dangelic R' (dangelic R SetMarkInv))) \<sqinter> (- grd (step ((dgr_demonic ClassicMark_rel)))))";
  apply (rule_tac T="LinkMark_rel" in Diagram_DataRefinement);
  apply auto;
  by (rule LinkMark_correct);

text {*
We have proved the correctness of the final algorithm, but the pre and the post conditions
involve the angelic choice operator and they depend on all data refinement steps we 
have used to prove the final diagram. We simplify these conditions and we show that
we obtained indead the corectness of the marking algorithm. 

The predicate $\mathit{ClassicInit}$ which is true for the $\mathit{init}$ situation states that initially 
the variables $\mathit{left}$, $\mathit{right}$, and $\mathit{atom}$ are equal to their initial values and also 
that no node is marked.

The predicate $\mathit{ClassicFinal}$ which is true for the $final$ situation states that at the end
the values of the variables $\mathit{left}$, $\mathit{right}$, and $\mathit{atom}$ are again equal to their initial values
and the variable $mrk$ records all reachable nodes. The reachable nodes are defined using our initial 
$\mathit{next}$ relation, however if we unfold all locale interpretations and definitions we see easeily
that a node $x$ is reachable if there is a path from $root$ to $x$ along $\mathit{left}$ and $\mathit{right}$ functions,
and all nodes in this path have the atom bit false.
*}

definition 
  "ClassicInit = {(p, t, left, right, atom, mrk) .
      atom = atom0 \<and> left = left0 \<and> right = right0 \<and> 
      finite (- mrk) \<and> mrk = {}}";

definition 
  "ClassicFinal = {(p, t, left, right, atom, mrk) . 
       atom = atom0 \<and> left = left0 \<and> right = right0 \<and> 
       mrk = reach root}";

theorem [simp]:
  "ClassicInit \<subseteq> (angelic RR (angelic R1' (angelic R1 (SetMarkInv init))))";
  apply (simp add: SetMarkInv_def);
  apply (simp add: ClassicInit_def angelic_def RR_def R1'_def R1_def Init_def Init''_def);
  apply (simp add: mem_def simp_eq_emptyset inf_fun_eq inf_bool_eq); 
  apply clarify;
  apply (simp add: simp_set_function);
  apply (simp_all add: ext_iff link0_def label0_def simp_set_function);
  done;

theorem [simp]:
  "ClassicInit \<subseteq> (angelic (R'' init) (angelic (R' init) (angelic (R init) (SetMarkInv init))))";
  by (simp add: R''_def R'_def R_def);

theorem [simp]:
  "(angelic RR (angelic R1' (angelic R1 (SetMarkInv final)))) \<le> ClassicFinal";
  apply (simp add: SetMarkInv_def);
  apply (simp add: ClassicFinal_def angelic_def RR_def R1'_def R1_def Final_def Final''_def Init''_def label0_def link0_def);
  apply (simp add: mem_def simp_eq_emptyset inf_fun_eq inf_bool_eq);
  apply (simp_all add: simp_set_function link0_def);
  apply safe;
  apply (simp_all add: simp_set_function);
  apply (simp_all add: link0_def);
  by auto;

theorem [simp]:
  "(angelic (R'' final) (angelic (R' final) (angelic (R final) (SetMarkInv final)))) \<le> ClassicFinal";
  by (simp add: R''_def R'_def R_def);

text{*
The indexed predicate $\mathit{ClassicPre}$ is the precondition of the diagram, and since we are only interested
in starting the marking diagram in the $init$ situation we set 
$\mathit{ClassicPre} \ loop = \mathit{ClassicPre} \ \mathit{final} = \emptyset$. 
*}

definition [simp]:
  "ClassicPre i =  (case i of
      I.init  \<Rightarrow> ClassicInit |
      I.loop  \<Rightarrow> {} |
      I.final \<Rightarrow> {})";

text{*
We are interested on the other hand that the marking diagram terminates only in the $\mathit{final}$ situation. In order to
achieve this we define the postcondition of the diagram as the indexed predicate $\mathit{ClassicPost}$ which is empty
on every situation except $final$. 
*}

definition [simp]:
  "ClassicPost i =  (case i of
      I.init  \<Rightarrow> {} |
      I.loop  \<Rightarrow> {} |
      I.final \<Rightarrow> ClassicFinal)";

definition [simp]:
  "ClassicMark = dgr_demonic ClassicMark_rel";

lemma exists_or:
  "(\<exists> x . p x \<or> q x) = ((\<exists> x . p x) \<or> (\<exists> x . q x))"
  by auto;


lemma [simp]:
  "(- grd (step (dgr_demonic ClassicMark_rel))) init = {}";
  apply (unfold ext_iff);
  apply (unfold fun_Compl_def);
  apply simp;
  apply (unfold dgr_demonic_def);
  apply safe;
  apply (unfold grd_demonic);
  apply auto;
  apply (unfold ClassicMark_rel_def);
  apply auto;
  apply (rule_tac x = loop in exI);
  apply auto;
  apply (simp add: QQ1_def QQ2_def sup_fun_eq sup_bool_eq);
  by (simp add: mem_def simp_set_function exists_or);

lemma [simp]:
  "(- grd (step (dgr_demonic ClassicMark_rel))) loop = {}";
  apply (unfold ext_iff);
  apply (unfold fun_Compl_def);
  apply simp;
  apply (unfold dgr_demonic_def);
  apply safe;
  apply (unfold grd_demonic);
  apply auto;
  apply (unfold ClassicMark_rel_def);
  apply auto;
  apply (simp add: bot_fun_eq bot_bool_eq);
  apply (simp add: QQ3_def QQ4_def QQ5_def QQ6_def QQ7_def QQ8_def sup_fun_eq sup_bool_eq);
  apply (simp add: mem_def simp_set_function);
  apply (case_tac "a \<noteq> nil");
  apply auto;
  apply (rule_tac x = loop in exI);
  apply auto;
  apply (simp add: exists_or);
  apply (unfold gg_def);
  by auto;

text {*
The final theorem states the correctness of the marking diagram with respect to the precondition
$\mathit{ClassicPre}$ and the postcondition $\mathit{ClassicPost}$, that is, if the diagram starts in the initial 
situation, then it will terminate in the final situation, and it will mark all reachable nodes.
*}

theorem "\<Turnstile> ClassicPre {| pt ClassicMark |} ClassicPost";
  apply (rule_tac P="(dangelic R'' (dangelic R' (dangelic R SetMarkInv)))" in hoare_pre);
  apply (subst le_fun_def)
  apply (simp add: dangelic_def);
  apply (rule_tac Q = "((dangelic R'' (dangelic R' (dangelic R SetMarkInv))) \<sqinter> (- grd (step ((dgr_demonic ClassicMark_rel)))))" in hoare_mono);
  apply simp;
  apply (rule le_funI)
  apply (case_tac x);
  apply (rule le_funI)
  apply (simp add: inf_fun_eq mem_def);
  apply (rule le_funI)
  apply (simp add: inf_fun_eq mem_def);
  apply (subst inf_fun_eq)
  apply (simp_all add: dangelic_def);
  apply (rule_tac y = "angelic RR (angelic R1' (angelic R1 (SetMarkInv final)))" in order_trans)
  apply auto [1];
  by (simp_all add: hoare_dgr_correctness);
end;

end;