header "Depth-First Search"

theory DFS = Main:

subsection "Definition of Graphs"

typedecl node 
types graph = "(node * node) list"

consts
  Next :: "[graph, node] \<Rightarrow> node list"
primrec
  "Next [] n = []"
  "Next (e#es) n = (if fst e = n then snd e # Next es n else Next es n)"

constdefs
  Nexts :: "[graph, node list] \<Rightarrow> node set"
  "Nexts g xs \<equiv> set g `` set xs"

lemma Next_set: "y \<in> set (Next g x) = ((x,y) \<in> set g)"
  by (induct g, auto)

lemma Nexts_Cons: "Nexts g (x#xs) = set (Next g x) \<union> Nexts g xs" 
  by(unfold Nexts_def,auto simp add:Image_def Next_set)

constdefs
  Reachable :: "[graph, node list] \<Rightarrow> node set"
  "Reachable g xs \<equiv> (set g)\<^sup>* `` set xs"

subsection "Formalization of Depth-First Search" 

constdefs
  nodes_of :: "graph \<Rightarrow> node set" 
  "nodes_of g \<equiv> set (map fst g @ map snd g)"

constdefs
  dfs_rel :: "((graph * node list * node list) * (graph * node list * node list)) set"
  "dfs_rel \<equiv> inv_image (finite_psubset <*lex*> less_than)  
                   (%(g,xs,ys). (nodes_of g - set ys, size xs))"

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
                        else dfs (g, Next g x@xs, x#ys))"
(hints recdef_simp add: dfs_rel_def finite_psubset_def 
       recdef_wf add: dfs_rel_wf)


text {*
  \begin{itemize}
  \item The second argument of \isatext{\isastyle{dfs}} is a stack of nodes that will be
  visited.
  \item The third argument of \isatext{\isastyle{dfs}} is a list of nodes that have
  been visited already.
  \end{itemize}
*}

lemma [rule_format, simp]: "x \<notin> nodes_of g \<longrightarrow> Next g x = []"
  by (induct g, auto simp add: nodes_of_def)

lemma dfs_tc_lem: "x \<notin> set ys \<longrightarrow>
        nodes_of g - insert x (set ys) \<subset> nodes_of g - set ys \<or>
        nodes_of g - insert x (set ys) = nodes_of g - set ys \<and> Next g x = []"
  by (cases  "x \<in> nodes_of g", auto)

recdef_tc dfs_tc: dfs
  by (simp add: dfs_tc_lem mem_iff)

lemmas dfs_induct = dfs.induct[OF dfs_tc]
lemmas dfs_inductive[simp] = dfs_inductive[OF dfs_tc]

subsection "Basic Properties"

declare mem_iff[simp]

lemma visit_subset_dfs: "set ys \<subseteq> set (dfs (g, xs, ys))"
  by (induct g xs ys rule: dfs_induct, auto)

lemma next_subset_dfs: "set xs \<subseteq> set (dfs (g, xs, ys))"
proof(induct g xs ys rule:dfs_induct)
  case(2 g x xs ys) 
  show ?case
  proof(cases "x \<in> set ys")
    case True
    have "set ys \<subseteq> set (dfs (g, xs, ys))"
      by (rule visit_subset_dfs)
    thus ?thesis
      by (auto!)
  next
    case False
    have "set (x#ys) \<subseteq> set (dfs (g, Next g x @ xs, x#ys))"
      by(rule visit_subset_dfs)
    thus ?thesis
      by (auto!)
  qed
qed(simp)

lemma Nexts_closed_dfs'[rule_format]: 
 "Nexts g ys \<subseteq> set xs \<union> set ys \<longrightarrow> Nexts g (dfs(g,xs,ys)) \<subseteq> set (dfs(g,xs,ys))"
  by (induct g xs ys rule:dfs_induct, auto simp add:Nexts_Cons)

lemma Nexts_closed_dfs: "Nexts g (dfs(g,xs,[])) \<subseteq> set (dfs(g,xs,[]))"
  by (rule Nexts_closed_dfs', simp add: Nexts_def)

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

lemma Reachable_closed_dfs: "Reachable g xs \<subseteq> set(dfs(g,xs,[]))"
proof -
  have "Reachable g xs \<subseteq> Reachable g (dfs(g,xs,[]))"
    by(unfold Reachable_def,rule Image_mono,auto simp add:next_subset_dfs)
  also have "\<dots> = set(dfs(g,xs,[]))"
  proof(unfold Reachable_def,rule Image_closed_trancl)
    from Nexts_closed_dfs
    show"set g `` set (dfs (g, xs, [])) \<subseteq> set (dfs (g, xs, []))"
      by(simp add: Nexts_def)
  qed
  finally show ?thesis .
qed    

lemma Reachable_Next: "Reachable g (Next g x) \<subseteq> Reachable g [x]"
  by(unfold Reachable_def,auto intro:converse_rtrancl_into_rtrancl simp: Next_set)

lemma Reachable_append: "Reachable g (xs @ ys) = Reachable g xs Un Reachable g ys"
  by (unfold Reachable_def, auto)


lemma dfs_subset_Reachable_visit_nodes: "set (dfs(g,xs,ys)) \<subseteq> Reachable g xs \<union> set ys"
proof(induct g xs ys rule:dfs_induct)
  case (2 g x xs ys)
  show ?case
  proof(cases "x \<in> set ys")
    case True
    show "set (dfs (g, x#xs, ys)) \<subseteq> Reachable g (x#xs) \<union> set ys"
      by (auto! simp add:Reachable_def)
  next
    case False
    have "Reachable g (Next g x) \<subseteq> Reachable g [x]" 
      by (rule Reachable_Next)
    hence "Reachable g (Next g x @ xs) \<subseteq> Reachable g (x#xs)"
      by(simp add: Reachable_append, auto simp add: Reachable_def)
    thus "set (dfs (g, x#xs, ys)) \<subseteq> Reachable g (x#xs) \<union> set ys"  
      by (auto! simp add:Reachable_def)
  qed
qed(unfold Reachable_def,simp)

subsection "Correctness"
    
theorem dfs_eq_Reachable: "set (dfs(g,xs,[])) = Reachable g xs"
proof
  have "set (dfs(g,xs,[])) \<subseteq> Reachable g xs \<union> set []"
    by (rule dfs_subset_Reachable_visit_nodes[of g xs "[]"])
 thus "set (dfs (g, xs, [])) \<subseteq> Reachable g xs"
   by simp
qed(rule Reachable_closed_dfs)

theorem "y \<in> set (dfs(g,[x],[])) = ((x,y) \<in> (set g)\<^sup>*)"
  by(simp only:dfs_eq_Reachable Reachable_def, auto)

subsection "Executable Code"

types_code 
  node ("int") 

code_module DFS
file "DFS.sml"
contains
  dfs = "dfs"

end
