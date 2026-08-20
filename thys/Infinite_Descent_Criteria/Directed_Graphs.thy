(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

section "Infinite Descent in Sloped Graphs"

text \<open>We follow the formulation given in \cite{InfiniteDescent}, in terms of sloped graphs.\<close>
theory Directed_Graphs
imports Preliminaries
begin

subsection "Directed Graphs"
(* DIRECTED GRAPHS *)

locale Graph = 
fixes Node :: "'node set"
and edge :: "'node \<Rightarrow> 'node \<Rightarrow> bool"
begin

inductive pathG :: "'node list \<Rightarrow> bool" 
where 
 Base: "{nd,nd'} \<subseteq> Node \<Longrightarrow> edge nd nd' \<Longrightarrow> pathG [nd,nd']"
|Step: "nd \<in> Node \<Longrightarrow> pathG ndl \<Longrightarrow> edge (last ndl) nd \<Longrightarrow> pathG (ndl @ [nd])"

lemma path_length_ge2: assumes "pathG ndl" shows "length ndl \<ge> 2"
using assms by (induct, auto)

lemma path_set: 
assumes "pathG ndl" shows "set ndl \<subseteq> Node" 
using assms by (induct, auto)  

lemma path_nth_'node: 
"pathG ndl \<Longrightarrow> i < length ndl \<Longrightarrow> ndl!i \<in> Node"
  using path_set nth_mem by blast


lemma pathG_butlast:"2 < length c \<Longrightarrow> pathG c \<Longrightarrow> pathG (butlast c)"  using pathG.cases by fastforce


lemma path_nth_edge: 
assumes "pathG ndl" "Suc i < length ndl" shows "edge (ndl!i) (ndl!(Suc i))"
using assms apply(induct arbitrary: i) apply simp_all
by (metis Suc_lessI append_Nil2 append_eq_conv_conj butlast_snoc hd_drop_conv_nth last_snoc nth_append_length nth_butlast take_hd_drop)

lemma path_iff_set_nth: 
"pathG ndl \<longleftrightarrow> 
 length ndl \<ge> 2 \<and> set ndl \<subseteq> Node \<and> (\<forall>i. Suc i < length ndl \<longrightarrow> edge (ndl!i) (ndl!(Suc i)))"
apply safe
  subgoal by (simp add: path_length_ge2)
  subgoal using path_set by blast
  subgoal by (simp add: path_nth_edge)
  subgoal proof(induction ndl rule: rev_induct) 
    case Nil thus ?case by auto
  next
    case (snoc nd ndl)
    show ?case
    proof(cases "length ndl = 1")
      case True then obtain nd' where ndl: "ndl = [nd']" by (cases ndl, auto)
      show ?thesis unfolding ndl 
      apply (simp, rule pathG.Base) using snoc by (auto simp: ndl)
    next
      case False
      show ?thesis apply (rule pathG.Step) 
        subgoal using snoc by auto
        subgoal apply (rule snoc.IH) using snoc False by auto (metis Suc_lessD nth_append)
        subgoal using snoc
        by simp (metis Suc_le_length_iff append_butlast_last_id length_append_singleton lessI 
                   list.simps(3) nth_append nth_append_length) .
     qed 
   qed .

lemma path_iff_nth: 
"pathG ndl \<longleftrightarrow> 
 length ndl \<ge> 2 \<and> (\<forall>i<length ndl. ndl!i \<in> Node) \<and> (\<forall>i. Suc i < length ndl \<longrightarrow> edge (ndl!i) (ndl!(Suc i)))"
unfolding path_iff_set_nth apply safe 
  subgoal by auto
  by (auto simp: in_set_conv_nth)

lemma Graph_pathG_restrict:
  "Graph.pathG N e ndl \<longleftrightarrow> Graph.pathG N (\<lambda>x y. e x y \<and> x \<in> N \<and> y \<in> N) ndl"
  unfolding Graph.path_iff_nth by auto

lemma path_appendL:
"pathG (ndl1 @ ndl2) \<Longrightarrow> length ndl1 \<ge> 2 \<Longrightarrow> pathG ndl1" 
unfolding path_iff_set_nth by simp (metis Suc_lessD nth_append trans_less_add1)

lemma path_appendR:
"pathG (ndl1 @ ndl2) \<Longrightarrow> length ndl2 \<ge> 2 \<Longrightarrow> pathG ndl2" 
unfolding path_iff_set_nth by simp (metis add_Suc_right nat_add_left_cancel_less nth_append_length_plus)

lemma path_appendM:
"pathG (ndl1 @ ndl2 @ ndl3) \<Longrightarrow> length ndl2 \<ge> 2 \<Longrightarrow> pathG ndl2" 
  by (smt append_Nil2 dual_order.trans path_appendL 
    path_appendR le_add_same_cancel1 length_append length_greater_0_conv less_le)

lemma ls_app:"[a, b, c] = [a,b] @ [c]" by auto

lemma notPathG_within:"\<not>pathG [a,b] \<Longrightarrow> \<not>pathG (ls @ [a,b] @ ls')" using path_appendL[of "ls @ [a,b]" ls'] path_appendR[of ls "[a,b]"] by auto

lemma notPathG_within':"\<not>pathG [a,b] \<Longrightarrow> \<not>pathG (ls # a # b # ls')" using path_appendL[of "[ls,a,b]" ls'] path_appendR[of "[ls]"] by auto

lemma pathG_tl:"2 \<le> length xs \<Longrightarrow> pathG (x#xs) \<Longrightarrow> pathG xs"  using pathG.cases 
  by (metis Graph.path_appendR append_Cons append_Nil)


lemma path_append_hd:
assumes "pathG (ndl1 @ [hd ndl2])" and "pathG ndl2" 
shows "pathG (ndl1 @ ndl2)"
proof-
  have 1: "\<And>ndl1 nd2 nd2'. ndl1 @ [nd2, nd2'] = (ndl1 @ [nd2]) @ [nd2']" by simp
  show ?thesis using assms(2,1) apply (induction arbitrary: ndl1)
    subgoal for nd2 nd2' ndl1 unfolding 1 apply (rule pathG.Step) by auto 
    subgoal for nd2 ndl2 ndl1 unfolding append_assoc[symmetric] apply (rule pathG.Step) 
      subgoal by auto
      subgoal by (metis Nil_is_append_conv pathG.cases hd_append2 list.distinct(1)) 
      subgoal by (metis Nil_is_append_conv pathG.cases last_appendR list.distinct(1)) . . 
  qed

lemma path_append_last:
assumes "pathG ndl1" and "pathG (last ndl1 # ndl2)" 
shows "pathG (ndl1 @ ndl2)"
proof-
  have [simp]: "ndl1 \<noteq> []" using assms(1) pathG.cases by auto
  hence 1: "ndl1 @ ndl2 = (butlast ndl1) @ (hd (last ndl1 # ndl2) # ndl2)" by simp
  show ?thesis unfolding 1 apply(rule path_append_hd) using assms by auto
qed

lemma path_Cons: 
assumes "nd \<in> Node" "edge nd (hd ndl)" "pathG ndl"
shows "pathG (nd # ndl)"
using assms(3,1,2) apply induction 
  subgoal by simp (metis Base append.left_neutral append_Cons bot_least path_append_last 
     insert_subset snoc_eq_iff_butlast)
  subgoal by simp (metis butlast.simps(2) pathG.simps hd_append2 last.simps list.distinct(1) 
     snoc_eq_iff_butlast) . 

lemma not_path_Nil[simp]: "\<not> pathG []"
using pathG.cases by blast

lemma not_path_singl[simp]: "\<not> pathG [nd]"
using path_length_ge2 by fastforce

lemma not_path_emp: "Node = {} \<Longrightarrow> \<not> pathG ndl"
by (metis bot.extremum_uniqueI empty_iff pathG.simps insert_not_empty)

lemma path_singl_in: 
assumes "edge nd nd" "n \<ge> 2" "nd \<in> Node"
shows "pathG (replicate n nd)"
using assms apply(induct n)
  subgoal by auto  
  subgoal using Base path_Cons le_Suc_eq by auto .

lemma path_singl_set: 
assumes "set ndl \<subseteq> {nd}" "nd \<in> Node"
shows "pathG ndl \<longleftrightarrow> (edge nd nd \<and> (\<exists>n\<ge>2. ndl = replicate n nd))"
proof-
  {assume "pathG ndl"
   hence "edge nd nd \<and> (\<exists>n\<ge>2. ndl = replicate n nd)"
   using assms apply(induction)  
   subgoal by simp (metis dual_order.refl empty_replicate numeral_2_eq_2 replicate_Suc) 
   subgoal by simp (metis linear not_less_eq_eq replicate_Suc replicate_append_same) .
  }
  thus ?thesis using path_singl_in by (auto simp: assms(2))
qed

lemma path_two_incl: 
assumes "edge nd nd'" "{nd,nd'} \<subseteq> Node"
shows "pathG [nd,nd']"
using assms unfolding path_iff_set_nth by simp

lemma path_two_concat_incl: 
assumes "edge nd nd'" "edge nd' nd" "n > 0"  "{nd,nd'} \<subseteq> Node"
shows "pathG (concat (replicate n [nd,nd']))"
using assms(1-3) apply(induct n)
  subgoal by auto
  subgoal by simp (smt pathG.Base assms(4) concat.simps(1) concat.simps(2) concat_append 
    path_Cons hd_append2 insert_subset list.distinct(1) list.sel(1) neq0_conv replicate_0 
    replicate_append_same) .


lemma pathG_butlast_not_nil:"pathG n \<Longrightarrow> butlast n \<noteq> []" by (metis Graph.not_path_Nil Graph.not_path_singl append_butlast_last_id
      self_append_conv2)

(* Path-connected nodes: *)
(* NB: We don't have empty paths, so a node is not always connected to itself. *)

definition pathCon where 
"pathCon nd nd' \<equiv> \<exists>ndl. pathG ndl \<and> hd ndl = nd \<and> last ndl = nd'"

lemma pathCon_trans: 
"pathCon nd nd' \<Longrightarrow> pathCon nd' nd'' \<Longrightarrow> pathCon nd nd''"
unfolding pathCon_def  
by (metis path_append_last hd_Cons_tl hd_append2 last.simps last_appendR not_path_Nil)

lemma not_pathCon_emp: "Node = {} \<Longrightarrow> \<not> pathCon nd1 nd2"
unfolding pathCon_def by (simp add: Graph.not_path_emp)

lemma pathCon_singl: "Node = {nd} \<Longrightarrow> pathCon nd1 nd2 \<longleftrightarrow> nd1 = nd \<and> nd2 = nd \<and> edge nd1 nd2"
unfolding pathCon_def 
by (metis empty_iff path_nth_'node path_set path_singl_set path_two_incl hd_conv_nth 
      insert_iff last.simps last_appendR 
   length_greater_0_conv not_path_Nil replicate_append_same subsetI)

lemma path_nth_pathCon: 
assumes fp: "pathG ndl" and ij: "i < j" "j < length ndl"
shows "pathCon (ndl!i) (ndl!j)"
proof-
  obtain ndl1 ndl2 ndl3 where "ndl = ndl1 @ (ndl!i) # ndl2 @ (ndl!j) # ndl3"
  using ij using list_split2 by blast
  hence ndl: "pathG (ndl1 @ ((ndl!i) # ndl2 @ [ndl!j]) @ ndl3)" using assms by auto 
  have "pathG ((ndl!i) # ndl2 @ [ndl!j])" 
  using path_appendM[OF ndl] by simp
  thus ?thesis unfolding pathCon_def by auto
qed

lemma path_set_pathCon: 
assumes fp: "pathG ndl" and nd: "{nd,nd'} \<subseteq> set ndl" "nd \<noteq> nd'"
shows "pathCon nd nd' \<or> pathCon nd' nd"
using path_nth_pathCon[OF fp] nd unfolding set_conv_nth 
using not_less_iff_gr_or_eq 
  by (smt (verit) insert_subset linorder_neqE_nat mem_Collect_eq)

(* Cycles *)

definition cycleG where 
"cycleG ndl \<equiv> pathG ndl \<and> hd ndl = last ndl"

lemma cycleG_not_nil:"cycleG c \<Longrightarrow> c \<noteq>[]" unfolding cycleG_def by auto
lemma cycleG_length_ge:"cycleG c \<Longrightarrow> length c \<ge> 2" unfolding cycleG_def using path_length_ge2 by auto


lemma cycleG_path_drop: "cycleG c \<Longrightarrow> j < length (butlast c) \<Longrightarrow> pathG (drop j c)"
  unfolding cycleG_def by(rule path_appendR[of "take j c"], auto)

definition cycleFrom where 
"cycleFrom nd ndl \<equiv> cycleG ndl \<and> hd ndl = nd"

lemma cycle_rotate1:
"cycleG (ndl @ [nd,nd']) \<Longrightarrow> cycleG (nd # ndl @ [nd])" 
unfolding cycleG_def path_iff_set_nth apply safe
  subgoal by auto
  subgoal by auto
  subgoal for i apply (cases i) 
    subgoal by simp (metis append.assoc append.left_neutral append_Cons length_append_singleton 
      lessI list.sel(1) neq_Nil_conv nth_Cons_0 nth_append_length)
    subgoal by simp (metis Suc_lessI less_SucI nth_append nth_append_length) . 
    subgoal by simp .

lemma cycle_rotate:
assumes "cycleG (ndl1 @ ndl2 @ [nd'])" "ndl2 \<noteq> []" 
shows "cycleG (ndl2 @ ndl1 @ [hd ndl2])" 
using assms proof(induction ndl2 arbitrary: ndl1 nd' rule: rev_induct) 
  case Nil thus ?case by auto
next 
  case (snoc nd2 ndl2 ndl1 nd')
  show ?case
  proof(cases "ndl2 = []")
    case True 
    show ?thesis unfolding True apply simp
    apply(rule cycle_rotate1) using snoc True by auto
  next
    case False   
    hence 1: "ndl2 @ nd2 # ndl1 @ [hd ndl2] = hd ndl2 # (tl ndl2 @ nd2 # ndl1) @ [hd ndl2]" by auto
    have 2: "(tl ndl2 @ nd2 # ndl1) @ [hd ndl2, hd (tl ndl2 @ [nd2])] = 
             (tl ndl2 @ [nd2]) @ (ndl1 @ [hd ndl2]) @ [hd (tl ndl2 @ [nd2])]"
    by auto
    show ?thesis using False apply simp unfolding append_Cons[symmetric]
    apply(rule snoc.IH[where nd' = nd2])
      subgoal unfolding append_Cons unfolding append_assoc[symmetric] apply(rule cycle_rotate1)
      using snoc by auto 
      subgoal by auto . 
  qed
qed

lemma cycle_rotate_butlast: 
assumes "cycleG (ndl1 @ nd # ndl2)" "ndl1 \<noteq> []" "ndl2 \<noteq> []"
shows "cycleG (nd # butlast ndl2 @ ndl1 @ [nd])" 
using assms cycle_rotate[where nd' = "last (nd # ndl2)"  
    and ?ndl2.0 = "butlast (nd # ndl2)" and ?ndl1.0 = ndl1] using assms by simp

lemma cycle_rotate_set: 
assumes "cycleG ndl" "nd \<in> set ndl"
shows "\<exists>ndl'. set ndl' = set ndl \<and> cycleG ndl' \<and> hd ndl' = nd \<and> last ndl' = nd \<and> length ndl' = length ndl"
proof(cases "hd ndl = nd \<or> last ndl = nd")
  case True thus ?thesis apply(intro exI[of _ ndl])
  using assms unfolding cycleG_def by auto
next
  case False then obtain ndl1 ndl2 where ndl: "ndl = ndl1 @ nd # ndl2" "ndl1 \<noteq> []" "ndl2 \<noteq> []"
  by (metis assms(2) hd_append last_ConsL last_append list.sel(1) list.simps(3) split_list)
  thus ?thesis using cycle_rotate_butlast[OF assms(1)[unfolded ndl(1)] ndl(2,3)] 
  apply(intro exI[of _ "nd # butlast ndl2 @ ndl1 @ [nd]"]) using assms ndl
  apply safe
    subgoal using in_set_butlastD by force
    subgoal by (smt Un_iff append_butlast_last_id hd_append2 hd_conv_nth in_set_conv_nth insert_iff 
      last.simps last_appendR length_greater_0_conv list.set(2) cycleG_def set_append)
    by auto 
qed
 
lemma cycle_set_pathCon: 
assumes cy: "cycleG ndl" and nd: "{nd,nd'} \<subseteq> set ndl" 
shows "pathCon nd nd'"
proof-
  obtain ndl' where ndl': "cycleG ndl'" "set ndl' = set ndl" "hd ndl' = nd" "last ndl' = nd"
  by (meson cy cycle_rotate_set insert_subset nd)
  show ?thesis proof(cases "nd = nd'")
    case True thus ?thesis using cycleG_def ndl'(1) ndl'(3) pathCon_def by auto
  next
    case False then obtain ndl1 ndl2 where 1: "ndl1 \<noteq> []" "ndl' = ndl1 @ nd' # ndl2" 
    by (metis append_Nil insert_iff list.sel(1) nd ndl'(2) ndl'(3) split_list subset_eq)
    hence "ndl' = ndl1 @ [nd'] @ ndl2" by simp
    hence "pathG (ndl1 @ [nd'])" using ndl'(1) unfolding cycleG_def  
      by (metis "1"(1) append.assoc eq_iff path_appendL length_append_singleton length_greater_0_conv 
        less_le not_less_eq_eq numeral_2_eq_2)
    thus ?thesis unfolding pathCon_def using "1"(1) "1"(2) ndl'(3) by auto
  qed
qed

lemma cycle_iff_nth: 
"cycleG ndl \<longleftrightarrow> 
 length ndl \<ge> 2 \<and> ndl!0 = ndl!(length ndl - 1) \<and> 
 (\<forall>i<length ndl. ndl!i \<in> Node) \<and> (\<forall>i. Suc i < length ndl \<longrightarrow> edge (ndl!i) (ndl!(Suc i)))"
unfolding cycleG_def path_iff_nth 
by (metis One_nat_def hd_conv_nth last_conv_nth list.size(3) not_less pos2)

lemma cycleG_shape: "cycleG nds \<Longrightarrow> (\<exists>x. nds = [x,x] \<or> (\<exists>xs. length xs > 0 \<and> nds = [x] @ xs @ [x]))"
  unfolding cycleG_def 
  apply(rule exI[of _ "hd nds"])
  apply(cases "butlast (tl nds)")
  subgoal apply(rule disjI1) 
    by (metis append.simps(1) append_butlast_last_id
        butlast.simps(1,2) list.exhaust_sel
        pathG_butlast_not_nil tl_last')
  apply(rule disjI2) 
  apply(rule exI[of _ "butlast (tl nds)"]) 
    by (metis append.simps(1,2) append_butlast_last_id
        bot_nat_0.not_eq_extremum butlast.simps(1)
        hd_Cons_tl last_tl length_0_conv list.sel(2)
        list.simps(3)) 
(* Strongly connected graph *)

definition scg :: "bool" where 
"scg \<equiv> \<forall>nd nd'. {nd,nd'} \<subseteq> Node \<longrightarrow> pathCon nd nd'"

lemma scg_emp: "Node = {} \<Longrightarrow> scg" unfolding scg_def by auto 

lemma scg_two: 
assumes "Node = {nd,nd'}"
shows "scg \<longleftrightarrow> edge nd nd' \<and> edge nd' nd"  
proof safe
  assume scg: scg
  {fix nd nd' assume Node: "Node = {nd,nd'}" 
   with scg obtain ndl where "pathG ndl" "nd = hd ndl" "nd' = last ndl"
   unfolding scg_def pathCon_def by auto
   hence "edge nd nd'" apply(induction)
     subgoal by simp
     subgoal by (metis Graph.path_set Node hd_append2 insert_absorb insert_iff 
       last_in_set last_snoc not_path_Nil singleton_insert_inj_eq' subsetD) .
  } 
  thus "edge nd nd'" "edge nd' nd" using assms by auto
next
  assume 0: "edge nd nd'" "edge nd' nd"
  show scg
  unfolding scg_def proof safe
    fix ndd ndd' assume 1: "{ndd, ndd'} \<subseteq> Node"
    show "pathCon ndd ndd'"
    proof(cases "{ndd, ndd'} = {nd, nd'}")
      case True
      show ?thesis unfolding pathCon_def
      apply(rule exI[of _ "[ndd, ndd']"])
      apply safe 
        apply (metis 0(1) 0(2) 1 pathG.Base True doubleton_eq_iff)
        by simp_all 
    next
      case False hence e: "ndd = ndd'" and or: "ndd = nd \<or> ndd = nd'" using 1 assms by auto
      show ?thesis using or apply standard
        subgoal unfolding pathCon_def apply(rule exI[of _ "[ndd, nd', nd]"])
        unfolding pathCon_def using 0 1 e assms path_Cons path_two_incl by auto
        subgoal unfolding pathCon_def apply(rule exI[of _ "[ndd, nd, nd']"])
        using 0 1 e pathG.Base assms path_Cons by auto .
    qed
  qed   
qed

lemma scg_singl: "Node = {nd} \<Longrightarrow> scg \<longleftrightarrow> edge nd nd" 
by (metis insert_absorb2 scg_two)

lemma scg_iff_two: 
assumes "\<exists>nd nd'. nd \<noteq> nd' \<and> {nd,nd'} \<subseteq> Node"
shows "scg \<longleftrightarrow> (\<forall>nd nd'. {nd,nd'} \<subseteq> Node \<and> nd \<noteq> nd' \<longrightarrow> pathCon nd nd')" 
(is "_ \<longleftrightarrow> ?K")
proof safe
  assume 1: ?K
  show "scg" unfolding scg_def proof safe
    fix nd nd' assume 2: "{nd, nd'} \<subseteq> Node"
    show "pathCon nd nd'"
    proof(cases "nd = nd'")
      case False thus ?thesis using 1 2 by auto
    next
      case True
      then obtain nd'' where nd'': "nd'' \<in> Node" "nd'' \<noteq> nd" "nd'' \<noteq> nd'" using assms 2 by auto
      have "pathCon nd nd''" using 1 2 nd'' by auto
      moreover have "pathCon nd'' nd'" using 1 2 nd'' by auto
      ultimately show ?thesis using pathCon_trans by blast
    qed
  qed
qed (simp add: scg_def)

lemma scg_ex_path:
assumes "scg" and "finite Node" and "Node \<noteq> {}"
shows "\<exists>ndl. pathG ndl \<and> set ndl = Node"
proof-
  {fix S2 nd assume "finite S2" and "S2 \<subseteq> Node"
   hence "\<exists>ndl. pathG ndl \<and> S2 \<subseteq> set ndl"
   proof(induction)
     case empty thus ?case using assms pathCon_def scg_def by auto
   next
     case (insert nd S2)
     then obtain ndl where ndl: "pathG ndl" "S2 \<subseteq> set ndl" by auto
     obtain ndl' where ndl': "pathG ndl'" "hd ndl' = last ndl" "last ndl' = nd"
     using insert assms(1) unfolding scg_def pathCon_def  
     by simp (metis path_set last_in_set ndl(1) not_path_Nil subset_eq)
     
     show ?case apply(rule exI[of _ "ndl @ tl ndl'"]) 
     apply safe
        subgoal by (metis path_append_last hd_Cons_tl ndl'(1) ndl'(2) ndl(1) not_path_Nil)
        subgoal by simp (metis hd_Cons_tl last_in_set last_tl ndl'(1) ndl'(3) not_path_Nil 
           not_path_singl)
        subgoal using ndl(2) by auto . 
   qed
  }
  thus ?thesis using assms by (meson eq_iff path_set)
qed

lemma scg_ex_cycle:
assumes "scg" and "finite Node" and "Node \<noteq> {}"
shows "\<exists>ndl. cycleG ndl \<and> set ndl = Node"
proof-
  obtain ndl where ndl: "pathG ndl \<and> set ndl = Node" using scg_ex_path[OF assms] by auto
  obtain ndl' where ndl': "pathG ndl'" "hd ndl' = last ndl" "last ndl' = hd ndl"
  using insert assms(1) unfolding scg_def pathCon_def  
  by simp (smt last_in_set list.set_sel(1) ndl not_path_Nil)
  have 1: "pathG (ndl @ tl ndl')" 
  by (metis append_Nil2 path_append_last hd_Cons_tl ndl ndl'(1) ndl'(2) tl_Nil)
  show ?thesis apply(rule exI[of _ "ndl @ tl ndl'"]) 
  unfolding cycleG_def apply safe
    subgoal by fact
    subgoal by (metis append_Nil2 append_butlast_last_id hd_Cons_tl 
       hd_append2 last_appendR last_tl ndl ndl'(1) ndl'(2) ndl'(3) not_path_Nil)
    subgoal using 1 path_set by blast 
    subgoal by (simp add: ndl) .
qed

lemma Graph_scg_restrict:
  "Graph.scg N e \<longleftrightarrow> Graph.scg N (\<lambda>x y. e x y \<and> x \<in> N \<and> y \<in> N)"
  unfolding Graph.scg_def Graph.pathCon_def 
  using Graph_pathG_restrict  by fastforce


lemma ex_cycle_scg:
assumes "cycleG ndl" "set ndl = Node"
shows "scg"
using assms cycle_set_pathCon scg_def by auto 

lemma scg_iff_cycle: 
assumes "finite Node" and "Node \<noteq> {}"
shows "scg \<longleftrightarrow> (\<exists>ndl. cycleG ndl \<and> set ndl = Node)"
  using assms ex_cycle_scg scg_ex_cycle by blast

lemma cycle_from_path: 
assumes p: "pathG ndl"
and ij: "j < i" "i < length ndl" "ndl!i = ndl!j"  
shows "cycleG (drop j (take (Suc i) ndl))"
unfolding cycleG_def apply safe
  subgoal using p ij unfolding path_iff_nth by auto
  subgoal 
  by (metis drop_eq_Nil dual_order.strict_trans2 hd_Nil_eq_last 
    hd_drop_conv_nth ij(1) ij(2) ij(3) last_drop last_snoc 
    lessI linorder_not_less nth_take order_less_le take_Suc_conv_app_nth) .

(* Any long enough path contains a cycle: *)
lemma finite_path_containsCycle: 
assumes f: "finite Node" and p: "pathG ndl" and l: "length ndl > card Node"
shows "\<exists>i j. i < length ndl \<and> j < i \<and> cycleG (drop j (take (Suc i) ndl))"
proof-
  have "set ndl \<subseteq> Node" using Graph.path_set p by blast
  hence "card (set ndl) \<le> card Node" by (simp add: card_mono f)
  then obtain i j where 1: "j < i" "i < length ndl" "ndl!i = ndl!j"  using l 
    by (metis distinct_card distinct_conv_nth not_less_iff_gr_or_eq order_le_less)
  hence "cycleG (drop j (take (Suc i) ndl))" 
    using Graph.cycle_from_path p by blast
  thus ?thesis using 1 by auto
qed


(* Infinite paths (ipaths) *)

definition ipath :: "'node stream \<Rightarrow> bool" where
"ipath \<equiv> alw (holdsS Node) aand alw (holds2 edge)"

lemma ipath_iff_snth: "ipath nds \<longleftrightarrow> (\<forall>i. nds!!i \<in> Node \<and> edge (nds!!i) (nds!!(Suc i)))"
by (meson alw_holds2_iff_snth alw_holdsS_iff_snth ipath_def)

lemma ipath_stake_path: 
"ipath nds \<Longrightarrow> n \<ge> 2 \<Longrightarrow> pathG (stake n nds)"
unfolding ipath_iff_snth path_iff_set_nth  
using path_iff_nth path_set by auto  

lemma ipath_iff_stake_path: 
"ipath nds \<longleftrightarrow> (\<forall>n \<ge> 2. pathG (stake n nds))"
apply safe
  subgoal by (simp add: ipath_stake_path)
  subgoal  
    by (metis Suc_le_lessD alw_holds2_iff_snth alw_holdsS_iff_snth 
     ipath_def length_stake nat_le_linear not_less_eq_eq path_iff_nth stake_nth) .

lemma sset_ipath: "ipath nds \<Longrightarrow> sset nds \<subseteq> Node"
by (metis imageE ipath_iff_snth sset_range subsetI)

lemma ipath_sdrop: 
"ipath nds \<Longrightarrow> ipath (sdrop n nds)"
unfolding ipath_iff_snth using path_iff_nth path_set by (auto simp add: sdrop_snth) 


lemma ipath_shift:"local.ipath (v @- srepeat u) \<Longrightarrow> local.ipath (srepeat u)"
  apply(drule ipath_sdrop[of "v @- srepeat u" "length v"])
  using sdrop_shift_length[of v "length v"] by auto

lemma ipath_stl:"ipath r1 \<Longrightarrow> local.ipath (stl r1)" using ipath_sdrop[of _ 1] by auto

lemma ipath_scons:"ipath (r##r') \<Longrightarrow> local.ipath (r')" using ipath_stl by force

lemma ipath_stake_sdrop_path: 
"ipath nds \<Longrightarrow> m \<ge> 2 \<Longrightarrow> pathG (stake m (sdrop n nds))" 
by (auto intro: ipath_sdrop ipath_stake_path)

lemma ipath_stake_sdrop_cycle: 
"ipath nds \<Longrightarrow> m \<ge> 2 \<Longrightarrow> nds!!n = nds!!(n+m-1) \<Longrightarrow> cycleG (stake m (sdrop n nds))" 
by (simp add: hd_conv_nth ipath_stake_sdrop_path last_conv_nth cycleG_def sdrop_snth)

lemma ipath_pathCon: 
assumes nds: "ipath nds" and ij: "i < j"
shows "pathCon (nds!!i) (nds!!j)"
using ipath_stake_sdrop_path[where n = i and m = "Suc(j-i)", OF nds]
unfolding pathCon_def apply(intro exI[of _ "stake (Suc (j - i)) (sdrop i nds)"]) 
using ij not_le apply safe
  subgoal by auto
  subgoal by auto
  subgoal by (metis add_diff_cancel_left' last_snoc less_or_eq_imp_le nat_le_iff_add sdrop_snth stake_Suc) .

lemma ipath_infinitely_often: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "\<exists>nd\<in>Node. \<forall>i. \<exists>j\<ge>i. nds!!j = nd"
proof- 
  let ?f = "(!!)nds"  
  have r: "range ?f \<subseteq> Node" using ipath_iff_snth nds by auto
  hence "finite (range ?f)" using Node finite_subset by auto
  then obtain nd where nd: "nd \<in> Node" and "infinite (?f -` {nd})" 
  by (meson r inf_img_fin_dom infinite_UNIV_char_0 subset_eq)
  hence "\<forall>i. \<exists>j\<ge>i. nds!!j = nd"  
    by (meson finite_nat_set_iff_bounded_le nat_le_linear vimage_singleton_eq)
  thus ?thesis using nd by auto
qed

(* Any cycle produces an ipath (via repettion): *)
lemma cycle_srepeat_ipath: 
assumes "cycleG ndl" shows "ipath (srepeat (butlast ndl))"
proof-
  have ndl: "butlast ndl \<noteq> [] \<and> length ndl \<ge> 2"  
  using assms  not_path_Nil path_length_ge2 unfolding cycleG_def 
  by (metis append_Nil append_butlast_last_id not_path_singl)  
  show ?thesis using assms ndl unfolding cycle_iff_nth ipath_iff_snth apply safe
    subgoal for i apply(cases "i mod (length ndl - Suc 0) = 0")
      subgoal by (simp add: nth_butlast)
      subgoal by simp (metis One_nat_def Suc_le_lessD diff_le_self length_butlast less_le_trans 
         mod_less_divisor nth_butlast numeral_2_eq_2 zero_less_diff) . 
    subgoal for i apply(cases "i mod (length ndl - Suc 0) = 0")
      subgoal by simp (metis One_nat_def Suc_le_lessD length_butlast mod_Suc mod_less_divisor 
           nth_butlast numeral_2_eq_2 zero_less_diff)
      subgoal by simp (smt One_nat_def Suc_le_lessD Suc_less_eq Suc_pred length_butlast less_le_trans 
           mod_Suc mod_less_divisor nth_butlast numeral_2_eq_2 pos2) . . 
  qed

lemma cycle_repeat: 
assumes ndl: "cycleG ndl" and n: "n \<noteq> 0"
shows "cycleG (repeat n (butlast ndl) @ [last ndl])"
proof-
  have "ndl \<noteq> [] \<and> length ndl \<ge> 2"  
  using cycleG_def assms cycle_iff_nth not_path_Nil by blast
  thus ?thesis using assms unfolding cycle_iff_nth apply safe
    subgoal by auto 
    subgoal by simp (smt One_nat_def nth_repeat Suc_le_lessD 
    Suc_pred append_butlast_last_id append_is_Nil_conv hd_append2 hd_conv_nth length_butlast length_greater_0_conv 
     nth_append_length numeral_2_eq_2 repeat_Suc zero_less_diff)
    subgoal for i apply(cases "i < length (repeat n (butlast ndl))")
      subgoal apply(subst nth_append) 
        by simp (metis One_nat_def in_set_butlastD length_butlast nth_mem nth_repeat 
         path_iff_nth path_iff_set_nth set_repeat subset_code(1)) 
      subgoal apply(subst nth_append) by (simp add: last_conv_nth) .
    subgoal for i apply(cases "i < length (repeat n (butlast ndl))")
      subgoal apply(subst nth_append) 
      apply simp apply(subst repeat_nth)
        subgoal by simp
        subgoal apply simp apply(subst nth_append) 
        by simp (metis (no_types, lifting) ipath_iff_snth One_nat_def Suc_le_lessD 
             Suc_mono cycle_srepeat_ipath last_conv_nth length_butlast length_greater_0_conv
             less_Suc_eq mod_mult_self2_is_0 ndl nth_butlast numeral_2_eq_2 
             repeat_nth_eq_srepeat_snth srepeat_snth zero_less_diff) .
      subgoal apply(subst nth_append) by simp . .
qed

(* The subgraph relationship *)

definition subgr where 
"subgr Node1 edge1 Node2 edge2 \<equiv> Node1 \<subseteq> Node2 \<and> (\<forall>nd nd'. edge1 nd nd' \<longrightarrow> edge2 nd nd')"

lemma path_subgr: 
"subgr Node1 edge1 S2 R2 \<Longrightarrow> Graph.pathG Node1 edge1 ndl \<Longrightarrow> Graph.pathG S2 R2 ndl"
unfolding Graph.path_iff_nth Graph.subgr_def by auto 

lemma cycle_subgr: 
"subgr Node1 edge1 S2 R2 \<Longrightarrow> Graph.cycleG Node1 edge1 ndl \<Longrightarrow> Graph.cycleG S2 R2 ndl"
by (simp add: Graph.cycleG_def Graph.path_subgr)

lemma ipath_subgr: 
"subgr Node1 edge1 S2 R2 \<Longrightarrow> Graph.ipath Node1 edge1 nds \<Longrightarrow> Graph.ipath S2 R2 nds"
unfolding Graph.ipath_iff_snth Graph.subgr_def by auto

(* Strongly connected subgraphs *)

fun scsg :: "'node set \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> bool" where 
"scsg Node1 edge1 \<longleftrightarrow> subgr Node1 edge1 Node edge \<and> Graph.scg Node1 edge1"

lemmas scsg_def = scsg.simps[simp del]


lemma scsg_paths:"scsg V' E' \<Longrightarrow> (\<forall>nd nd'.
        {nd, nd'} \<subseteq> V' \<longrightarrow>
        Graph.pathCon V' E' nd nd')"
  unfolding scsg_def Graph.scg_def by auto

(* Maximal strongly connected subgraphs *)
definition maximal_scsg where 
"maximal_scsg Node1 edge1 \<equiv> 
 scsg Node1 edge1 \<and> (\<forall> S2 R2. scsg S2 R2 \<and> subgr Node1 edge1 S2 R2 \<longrightarrow> Node1 = S2 \<and> edge1 = R2)"


(* The limit of an ipath is the graph of all nodes and edges that are always eventually taken 
by the path: *)

definition limitS :: "'node stream \<Rightarrow> 'node set" where 
"limitS nds \<equiv> {nd \<in> Node. alw (ev (holds ((=) nd))) nds}" 

definition limitR :: "'node stream \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool)" where 
"limitR nds \<equiv> \<lambda>nd nd'. alw (ev (holds2 (\<lambda>ndd ndd'. ndd = nd \<and> ndd' = nd'))) nds"

lemma limitS_sset: "limitS nds \<subseteq> sset nds" unfolding limitS_def 
by (smt alwD ev_holds_sset mem_Collect_eq subsetI)


(* An ipath will eventually always be in its limit subgraph: *)
lemma ipath_ev_alw: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "ev (alw (holdsS (limitS nds) aand holds2 (limitR nds))) nds"
proof-
  define P where "P \<equiv> {(nd,nd') | nd nd'. {nd,nd'} \<subseteq> Node \<and>  
     \<not> alw (ev (holds2 (\<lambda>ndd ndd'. ndd = nd \<and> ndd' = nd'))) nds}"

  have "\<forall>p\<in>P. \<exists>m. \<forall>i\<ge>m. (nds!!i, nds!!(Suc i)) \<noteq> p" 
  unfolding P_def alw_ev_holds2_iff_snth by auto
  then obtain f where f: "\<forall>p\<in>P. \<forall>i\<ge>f p. (nds!!i, nds!!(Suc i)) \<noteq> p" 
  using bchoice[of P "\<lambda>p m. \<forall>i\<ge>m. (nds!!i, nds!!(Suc i)) \<noteq> p"] by auto

  have "P \<subseteq> Node \<times> Node" unfolding P_def by auto
  hence fP: "finite (f `P)" using Node finite_subset by blast

  define i0 where "i0 \<equiv> Max (f ` P)"
  have "\<forall>i\<ge>i0. \<forall>p\<in>P. (nds!!i, nds!!(Suc i)) \<noteq> p" 
  by (metis Max_ge f dual_order.trans fP image_eqI i0_def)
  hence 1: "\<forall>i\<ge>i0. limitR nds (nds!!i) (nds!!(Suc i))" 
  unfolding limitR_def P_def by simp (metis Graph.ipath_iff_snth nds snth.simps(2))

  define Q where "Q \<equiv> {nd \<in> Node. \<not> alw (ev (holds ((=)nd))) nds}"

  have "\<forall>q\<in>Q. \<exists>m. \<forall>i\<ge>m. nds!!i \<noteq> q" 
  unfolding Q_def alw_ev_holds_iff_snth by auto
  then obtain g where g: "\<forall>q\<in>Q. \<forall>i\<ge>g q. nds!!i \<noteq> q" 
  using bchoice[of Q "\<lambda>p m. \<forall>i\<ge>m. nds!!i  \<noteq> p"] by auto

  have "Q \<subseteq> Node" unfolding Q_def by auto
  hence gQ: "finite (g `Q)" using Node finite_subset by blast

  define j0 where "j0 \<equiv> Max (g ` Q)"
  have "\<forall>i\<ge>j0. \<forall>q\<in>Q. nds!!i \<noteq> q" 
  by (metis Max_ge g dual_order.trans gQ image_eqI j0_def)
  hence 2: "\<forall>i\<ge>j0. (nds!!i) \<in> limitS nds " 
  unfolding limitS_def Q_def by (metis (mono_tags, lifting) mem_Collect_eq nds snth_sset sset_ipath subsetD)

  show ?thesis
  using 1 2 unfolding ev_alw_holds2_aand_holdsS_iff_snth apply(intro exI[of _ "max j0 i0"]) by auto
qed


lemma limitS_infinite_visits:
  assumes "x \<in> limitS \<pi>"
  shows "\<exists>n \<ge> m. \<pi> !! n = x"
  using assms unfolding limitS_def 
  using infinite_nat_iff_unbounded_le mem_Collect_eq 
  by (metis (mono_tags, lifting) alw_ev_holds_iff_snth)

(* Another way to formulate the above is to say that an 
ipath has a prefix that is an ipath in the limit subgraph: *)
lemma ipath_sdrop_limit: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "\<exists>i. Graph.ipath (limitS nds) (limitR nds) (sdrop i nds)"
using ipath_ev_alw[OF assms] 
unfolding ev_alw_holds2_aand_holdsS_iff_snth Graph.ipath_iff_snth sdrop_snth 
by (metis add_Suc_right le_add1)

lemma limitR_sset: "limitR nds nd nd' \<Longrightarrow> {nd,nd'} \<subseteq> sset nds" 
unfolding limitR_def unfolding alw_ev_holds2_iff_snth  
by (metis empty_subsetI insert_subset snth_sset)

lemma limitR_S: "ipath nds \<Longrightarrow> limitR nds nd nd' \<Longrightarrow> {nd,nd'} \<subseteq> Node" 
using limitR_sset sset_ipath by blast 

(* The limit is a subgraph of the ipath's graph:  *)

lemma limitS_S: "limitS nds \<subseteq> Node" unfolding limitS_def by auto

lemma limitR_R: "ipath nds \<Longrightarrow> limitR nds nd nd' \<Longrightarrow> edge nd nd'" 
unfolding ipath_iff_snth limitR_def alw_ev_holds2_iff_snth by auto

(* ... and is a strongly connected graph: *)

lemma scg_limit: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "Graph.scg (limitS nds) (limitR nds)"
unfolding Graph.scg_def proof safe
  fix nd nd' assume 0: "{nd, nd'} \<subseteq> limitS nds"

  obtain m where nds_m: "Graph.ipath (limitS nds) (limitR nds) (sdrop m nds)"
  using ipath_sdrop_limit[OF assms] by auto

  have 1: "alw (ev (holds ((=)nd))) nds" "alw (ev (holds ((=)nd'))) nds" 
  using 0 unfolding limitS_def by auto

  obtain i where i: "i\<ge>m" and "nd = nds!!i" 
  using 1 unfolding alw_ev_holds_iff_snth by blast 
  hence nd: "nd = (sdrop m nds)!!(i-m)" by (simp add: sdrop_snth)

  obtain j where j: "j > i" and "nd' = nds!!j" 
  using 1 unfolding alw_ev_holds_iff_snth using Suc_le_lessD by blast
  hence nd': "nd' = (sdrop m nds)!!(j-m)" 
  by (metis add_diff_cancel_left' i less_le_trans less_not_refl nat_le_iff_add nat_le_linear sdrop_snth)

  show "Graph.pathCon (limitS nds) (limitR nds) nd nd'"
  unfolding nd nd' apply(rule Graph.ipath_pathCon) using nds_m i j by auto
qed

(* ... hence a strongly connected subgraph: *)
lemma scsg_limit: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "scsg (limitS nds) (limitR nds)"
by (metis (full_types) Graph.subgr_def Node limitR_R limitS_S nds scg_limit scsg.elims(3))


(* NB: The above lemmas form a result that is crucial for the characterisation of ipaths
in cyclic proof systems. For finite graphs, any ipath is eventually swallowed by a strongly 
connected subgraph (namely its limit), in that:
-- eventually the steps will always be in this subgraph, and 
-- *every* edge in this subgraph is always eventually taken.
*)
lemma 
assumes "finite Node" and "ipath nds"
shows "\<exists>Node1 edge1. 
  scsg Node1 edge1 \<and> 
  ev (alw (holdsS Node1 aand holds2 edge1)) nds \<and> 
  (\<forall>nd nd'. edge1 nd nd' \<longrightarrow> alw (ev (holds2 (\<lambda>ndd ndd'. ndd = nd \<and> ndd' = nd'))) nds)"
apply(intro exI[of _ "limitS nds"] exI[of _ "limitR nds"])
apply safe
  subgoal using scsg_limit[OF assms] .
  subgoal using ipath_ev_alw[OF assms] .
  subgoal unfolding limitR_def . .

(* Other properties of the limit *)

lemma finite_limitS: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "finite (limitS nds)"
using Node finite_subset limitS_S by blast

lemma S_ne: 
assumes nds: "ipath nds"
shows "Node \<noteq> {}"
using ipath_iff_snth nds by blast

lemma R_ne: 
assumes nds: "ipath nds"
shows "\<exists>nd nd'. {nd,nd'} \<subseteq> Node \<and>  edge nd nd'"
using ipath_iff_snth nds by blast

lemma limitS_ne: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "limitS nds \<noteq> {}"
using ipath_sdrop_limit[OF assms] Graph.S_ne by blast 

lemma limitR_ne: 
assumes Node: "finite Node" and  nds: "ipath nds"
shows "\<exists>nd nd'. {nd,nd'} \<subseteq> limitS nds \<and> limitR nds nd nd'"
using ipath_sdrop_limit[OF assms] Graph.R_ne by blast 
 
lemma finite_limitR: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "finite {(nd,nd') . limitR nds nd nd'}"
proof-
  have "{(nd,nd') . limitR nds nd nd'} \<subseteq> Node \<times> Node"
  unfolding limitR_def alw_ev_holds2_iff_snth  
  using Graph.ipath_iff_snth nds by blast+
  thus ?thesis using Node infinite_super by blast
qed

lemma ipath_limitR_interval: 
assumes Node: "finite Node" and nds: "ipath nds"
shows "\<exists>j1\<ge>i. \<exists>j2\<ge>j1. 
  \<forall>nd nd'. limitR nds nd nd' \<longrightarrow> 
  (\<exists>j. j1 \<le> j \<and> j < j2 \<and> nds!!j = nd \<and> nds!!(Suc j) = nd')"
proof-
  define P where "P \<equiv> {(nd,nd') . limitR nds nd nd'}"
  have 0: "\<And>nd nd'. limitR nds nd nd' \<longleftrightarrow> (nd,nd') \<in> P" unfolding P_def by simp
  have fP: "finite P" "P\<noteq>{}" unfolding P_def 
  using Node finite_limitR limitR_ne nds by fastforce+
  have "\<forall>p\<in>P. \<exists>j\<ge>i. (nds!!j, nds!!(Suc j)) = p" 
  unfolding P_def by (simp add: Graph.limitR_def alw_ev_holds2_iff_snth)
  then obtain f where f: "\<forall>p\<in>P. f p \<ge> i \<and> (nds!!(f p), nds!!(Suc (f p))) = p" 
  using bchoice[of P "\<lambda>p j. j \<ge> i \<and> (nds!!j, nds!!(Suc j)) = p"] by blast

  define j1 j2 where "j1 \<equiv> Min (f ` P)" and "j2 \<equiv> Suc (Max (f ` P))"
  show ?thesis apply(rule exI[of _ j1], safe)
    subgoal using f fP unfolding j1_def by simp
    subgoal apply(rule exI[of _ j2], safe)
      subgoal using f fP unfolding j1_def j2_def by (simp add: le_SucI)
      subgoal for nd nd' apply(rule exI[of _ "f (nd,nd')"])
        using f fP unfolding j1_def j2_def 0 by (auto simp: le_imp_less_Suc) . .
qed

lemma limitS_sdrop_eq[simp]: "limitS (sdrop n nds) = limitS nds"
unfolding limitS_def alw_ev_holds_iff_snth 
by (metis (no_types, opaque_lifting) sdrop_snth add_leE  less_eqE nat_add_left_cancel_le trans_le_add2)

lemma limitR_sdrop_eq[simp]: "limitR (sdrop n nds) = limitR nds"
unfolding limitR_def alw_ev_holds2_iff_snth sdrop_snth fun_eq_iff apply safe
  using trans_le_add2 apply fastforce
  by (metis add_Suc_right add_leE nat_add_left_cancel_le nat_le_iff_add)

end (* context Graphs  *)




end