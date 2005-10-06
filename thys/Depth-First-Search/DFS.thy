(*  Title:       Depth-First Search
    Author:      Toshiaki Nishihara and Yasuhiko Minamide
    Maintainer:  Yasuhiko Minamide <minamide@cs.tsukuba.ac.jp>
*)

header "Depth-First Search"

theory DFS
imports Main InductiveInvariant
begin

subsection "Definition of Graphs"

typedecl node 
types graph = "(node * node) list"

consts
  nexts :: "[graph, node] \<Rightarrow> node list"
primrec
  "nexts [] n = []"
  "nexts (e#es) n = (if fst e = n then snd e # nexts es n else nexts es n)"

constdefs
  nextss :: "[graph, node list] \<Rightarrow> node set"
  "nextss g xs \<equiv> set g `` set xs"

lemma nexts_set: "y \<in> set (nexts g x) = ((x,y) \<in> set g)"
  by (induct g, auto)

lemma nextss_Cons: "nextss g (x#xs) = set (nexts g x) \<union> nextss g xs" 
  by(unfold nextss_def,auto simp add:Image_def nexts_set)

constdefs
  reachable :: "[graph, node list] \<Rightarrow> node set"
  "reachable g xs \<equiv> (set g)\<^sup>* `` set xs"

subsection "Depth-First Search with Stack" 

constdefs
  nodes_of :: "graph \<Rightarrow> node set" 
  "nodes_of g \<equiv> set (map fst g @ map snd g)"

lemma [rule_format, simp]: "x \<notin> nodes_of g \<longrightarrow> nexts g x = []"
  by (induct g, auto simp add: nodes_of_def)

constdefs
  dfs_rel :: "((graph * node list * node list) * (graph * node list * node list)) set"
  "dfs_rel \<equiv> inv_image (finite_psubset <*lex*> less_than)  
                   (\<lambda>(g,xs,ys). (nodes_of g - set ys, size xs))"

lemma dfs_rel_wf: "wf dfs_rel"
  by (auto simp add: dfs_rel_def wf_finite_psubset)

lemma [simp]: "finite (nodes_of g - set ys)"  
proof(rule finite_subset)
  show "finite (nodes_of g)"
    by (auto simp add: nodes_of_def)
qed (auto)

consts 
  dfs :: "[graph * node list * node list] \<Rightarrow> node list"
recdef (permissive) dfs dfs_rel
  dfs_base[simp]: "dfs (g, [], ys) = ys"
  dfs_inductive: "dfs (g, x#xs, ys) = (if x mem ys then dfs (g, xs, ys) 
                        else dfs (g, nexts g x@xs, x#ys))"
(hints recdef_simp add: dfs_rel_def finite_psubset_def recdef_wf add: dfs_rel_wf)


text {*
  \begin{itemize}
  \item The second argument of \isatext{\isastyle{dfs}} is a stack of nodes that will be
  visited.
  \item The third argument of \isatext{\isastyle{dfs}} is a list of nodes that have
  been visited already.
  \end{itemize}
*}

recdef_tc dfs_tc: dfs
proof (intro allI)
  fix g x ys
  show "\<not> x mem ys \<longrightarrow>
       nodes_of g - insert x (set ys) \<subset> nodes_of g - set ys \<or>
       nodes_of g - insert x (set ys) = nodes_of g - set ys \<and> nexts g x = []"
    by (cases  "x \<in> nodes_of g", auto simp add: mem_iff)
qed

lemmas dfs_induct = dfs.induct[OF dfs_tc]
lemmas dfs_inductive[simp] = dfs_inductive[OF dfs_tc]

subsection "Depeth-First Search with Nested-Recursion"

text {*
  We prove the termination of depth-first search with nested-recursion
  by the method of inductive invariants.
*}

consts 
  dfs2 :: "[graph * node list * node list] \<Rightarrow> node list"
recdef (permissive) dfs2 dfs_rel
  [simp]: "dfs2 (g, [], ys) = ys"
  dfs2_inductive: 
          "dfs2 (g, x#xs, ys) = (if x mem ys then dfs2 (g, xs, ys) 
                                 else dfs2 (g, xs, dfs2 (g, nexts g x, x#ys)))"
(hints recdef_simp add: dfs_rel_def finite_psubset_def recdef_wf add: dfs_rel_wf)


lemma dfs2_inv: "set ys \<subseteq> set (dfs2 (g, xs, ys))"
proof (rule tfl_indinv_wfrec [OF dfs2_def, where x = "(g, xs, ys)" and S = "\<lambda>(g, xs, ys). \<lambda>zs. set ys \<subseteq> set zs",simplified])
  show "wf dfs_rel" 
    by (rule dfs_rel_wf)
next
  show "indinv dfs_rel (\<lambda>(g, xs, ys) zs. set ys \<subseteq> set zs)
     (\<lambda>dfs2.
         prod_case
          (\<lambda>u. prod_case
                (\<lambda>w y. case w of [] \<Rightarrow> y
                       | z # aa \<Rightarrow>
                           if z mem y then dfs2 (u, aa, y)
                           else dfs2 (u, aa, dfs2 (u, nexts u z, z # y)))))"
  proof (auto simp add: indinv_def)
    fix f g xs ys z
    assume H: "\<forall>g' xs' ys'.
          ((g', xs', ys'), g, xs, ys) \<in> dfs_rel \<longrightarrow>
          set ys' \<subseteq> set (f (g', xs', ys'))"
      and "z \<in> set ys"
    show "z \<in> set (case xs of [] \<Rightarrow> ys
                   | x # xs \<Rightarrow>
                       if x mem ys then f (g, xs, ys)
                       else f (g, xs, f (g, nexts g x, x # ys)))"
    proof (cases xs)
      case Nil
      thus ?thesis
	by (auto!)
    next
      case (Cons x xs'')
      show ?thesis
      proof (auto!)
	have "set ys \<subseteq> set (f (g, xs'', ys))"
	proof (rule H[rule_format])
	  show "((g, xs'', ys), g, xs, ys) \<in> dfs_rel"
	    by (auto! simp add: dfs_rel_def inv_image_def lex_prod_def)
	qed
	thus "z \<in> set (f (g, xs'', ys))"
	  by (auto!)
      next
	assume "\<not> x mem ys"
	have F: "set (x#ys) \<subseteq> set (f (g, nexts g x, x # ys))"
	proof (rule H[rule_format])
	  show "((g, nexts g x, x # ys), g, xs, ys) \<in> dfs_rel"
	  proof (cases "x : nodes_of g")
	    case True
	    show ?thesis
	    proof (simp add: dfs_rel_def inv_image_def lex_prod_def finite_psubset_def, rule disjI1)
	      show "nodes_of g - insert x (set ys) \<subset> nodes_of g - set ys"
		by(auto! simp add: mem_iff)
	    qed
	  next
	    case False
	    show ?thesis
	      apply(simp add: dfs_rel_def inv_image_def lex_prod_def)
	      apply(rule disjI2)
	      apply(auto!)
	      done
	  qed
	qed
	also have "\<dots> \<subseteq> set (f (g, xs'', f (g, nexts g x, x # ys)))"
	proof (rule H[rule_format])
	  from F
	  show "((g, xs'', f (g, nexts g x, x # ys)), g, xs, ys) \<in> dfs_rel"
	    by (auto! simp add: dfs_rel_def inv_image_def lex_prod_def finite_psubset_def)
	qed
	finally have "set (x#ys) \<subseteq> \<dots>"
	  by auto
	thus "z \<in> set (f (g, xs'', f (g, nexts g x, x # ys)))"
	  by (auto!)
      qed
    qed
  qed
qed

recdef_tc dfs2_tc: dfs2(1)
proof (intro allI impI)
  fix g x 
  fix xs ys::"node list"
  assume "\<not> x mem ys" 
  show "nodes_of g - insert x (set ys) \<subset> nodes_of g - set ys \<or>
       nodes_of g - insert x (set ys) = nodes_of g - set ys \<and>
       length (nexts g x) < Suc (length xs)"
  proof (cases "x : nodes_of g")
    case False
    show ?thesis
      by (rule disjI2, auto!)
  next
    case True
    show ?thesis
      by(rule disjI1, auto! simp add: mem_iff)
  qed
qed

recdef_tc dfs2_tc2: dfs2(2)
proof (intro allI impI)
  fix g x 
  fix xs ys::"node list"
  assume "\<not> x mem ys" 
  have "set (x#ys) \<subseteq> set (dfs2 (g, nexts g x, x # ys))"
    by (rule dfs2_inv)
  thus "nodes_of g - set (dfs2 (g, nexts g x, x # ys)) \<subset> nodes_of g - set ys \<or>
       nodes_of g - set (dfs2 (g, nexts g x, x # ys)) = nodes_of g - set ys"
    by (auto)
qed

lemma dfs2_induct[induct type]:
  assumes "\<And>g ys. P g [] ys" and
  H: "\<And>g x xs ys.
        \<lbrakk>\<not> x mem ys \<longrightarrow> P g xs (dfs2 (g, nexts g x, x # ys));
         \<not> x mem ys \<longrightarrow> P g (nexts g x) (x # ys); x mem ys \<longrightarrow> P g xs ys\<rbrakk>
         \<Longrightarrow> P g (x # xs) ys"
  shows "P u v w"
proof (induct u v w rule: dfs2.induct[OF dfs2_tc])
  case (2 g x xs ys)
  show ?case
  proof (rule H)
    show "\<not> x mem ys \<longrightarrow> P g xs (dfs2 (g, nexts g x, x # ys))"
    proof 
      assume "\<not> x mem ys"
      have "set (x#ys) \<subseteq> set (dfs2 (g, nexts g x, x # ys))"
	by (rule dfs2_inv)
      thus "P g xs (dfs2 (g, nexts g x, x # ys))"
	by (auto!)
    qed
  qed
qed

lemma dfs2_inductive[simp]:
  "dfs2 (g, x # xs, ys) = (if x mem ys then dfs2 (g, xs, ys)
                           else dfs2 (g, xs, dfs2 (g, nexts g x, x # ys)))"
proof -
  have "set (x#ys) \<subseteq> set (dfs2 (g, nexts g x, x # ys))"
    by (rule dfs2_inv)
  hence "((g, xs, dfs2 (g, nexts g x, x # ys)), g, x # xs, ys) \<in> dfs_rel"
    by (auto simp add: dfs_rel_def inv_image_def lex_prod_def finite_psubset_def)
  with dfs2_inductive[OF dfs2_tc]
  show ?thesis
    by (simp)
qed

lemma dfs_app: "dfs (g, xs@ys, zs) = dfs (g, ys, dfs (g, xs, zs))"
  by (induct g xs zs rule:dfs_induct, auto!)

lemma "dfs2 (g, xs, ys) = dfs (g, xs, ys)" 
  by (induct g xs ys rule:dfs2_induct, auto simp add: dfs_app)

subsection "Basic Properties"

lemma visit_subset_dfs: "set ys \<subseteq> set (dfs (g, xs, ys))"
  by (induct g xs ys rule: dfs_induct, auto simp add: mem_iff)

lemma next_subset_dfs: "set xs \<subseteq> set (dfs (g, xs, ys))"
proof(induct g xs ys rule:dfs_induct)
  case(2 g x xs ys) 
  show ?case
  proof(cases "x \<in> set ys")
    case True
    have "set ys \<subseteq> set (dfs (g, xs, ys))"
      by (rule visit_subset_dfs)
    thus ?thesis
      by (auto! simp add: mem_iff)
  next
    case False
    have "set (x#ys) \<subseteq> set (dfs (g, nexts g x @ xs, x#ys))"
      by(rule visit_subset_dfs)
    thus ?thesis
      by (auto! simp add: mem_iff)
  qed
qed(simp)


lemma nextss_closed_dfs'[rule_format]: 
 "nextss g ys \<subseteq> set xs \<union> set ys \<longrightarrow> nextss g (dfs(g,xs,ys)) \<subseteq> set (dfs(g,xs,ys))"
  by (induct g xs ys rule:dfs_induct, auto simp add:nextss_Cons mem_iff)

lemma nextss_closed_dfs: "nextss g (dfs(g,xs,[])) \<subseteq> set (dfs(g,xs,[]))"
  by (rule nextss_closed_dfs', simp add: nextss_def)

lemma Image_closed_trancl: assumes "r `` X \<subseteq> X" shows "r\<^sup>* `` X = X"
proof
  show "r\<^sup>* `` X \<subseteq> X"
  proof(unfold Image_def, auto)
    fix x y
    assume "y \<in> X"
    assume "(y,x) \<in> r\<^sup>*"
    thus "x \<in> X"
      by (induct, auto! simp add: Image_def)
  qed
qed (auto)

lemma reachable_closed_dfs: "reachable g xs \<subseteq> set(dfs(g,xs,[]))"
proof -
  have "reachable g xs \<subseteq> reachable g (dfs(g,xs,[]))"
    by(unfold reachable_def,rule Image_mono,auto simp add:next_subset_dfs)
  also have "\<dots> = set(dfs(g,xs,[]))"
  proof(unfold reachable_def,rule Image_closed_trancl)
    from nextss_closed_dfs
    show"set g `` set (dfs (g, xs, [])) \<subseteq> set (dfs (g, xs, []))"
      by(simp add: nextss_def)
  qed
  finally show ?thesis .
qed    

lemma reachable_nexts: "reachable g (nexts g x) \<subseteq> reachable g [x]"
  by(unfold reachable_def,auto intro:converse_rtrancl_into_rtrancl simp: nexts_set)

lemma reachable_append: "reachable g (xs @ ys) = reachable g xs Un reachable g ys"
  by (unfold reachable_def, auto)


lemma dfs_subset_reachable_visit_nodes: "set (dfs(g,xs,ys)) \<subseteq> reachable g xs \<union> set ys"
proof(induct g xs ys rule:dfs_induct)
  case (2 g x xs ys)
  show ?case
  proof(cases "x \<in> set ys")
    case True
    show "set (dfs (g, x#xs, ys)) \<subseteq> reachable g (x#xs) \<union> set ys"
      by (auto! simp add:reachable_def mem_iff)
  next
    case False
    have "reachable g (nexts g x) \<subseteq> reachable g [x]" 
      by (rule reachable_nexts)
    hence "reachable g (nexts g x @ xs) \<subseteq> reachable g (x#xs)"
      by(simp add: reachable_append, auto simp add: reachable_def)
    thus "set (dfs (g, x#xs, ys)) \<subseteq> reachable g (x#xs) \<union> set ys"  
      by (auto! simp add:reachable_def mem_iff)
  qed
qed(unfold reachable_def,simp)

subsection "Correctness"
    
theorem dfs_eq_reachable: "set (dfs(g,xs,[])) = reachable g xs"
proof
  have "set (dfs(g,xs,[])) \<subseteq> reachable g xs \<union> set []"
    by (rule dfs_subset_reachable_visit_nodes[of g xs "[]"])
 thus "set (dfs (g, xs, [])) \<subseteq> reachable g xs"
   by simp
qed(rule reachable_closed_dfs)

theorem "y \<in> set (dfs(g,[x],[])) = ((x,y) \<in> (set g)\<^sup>*)"
  by(simp only:dfs_eq_reachable reachable_def, auto)

subsection "Executable Code"

types_code 
  node ("int") 

code_module DFS file "DFS.sml" contains
  dfs = "dfs" dfs2 = "dfs2"

end
