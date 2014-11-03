section {* Directed Graphs *}
(* Author: Peter Lammich *)
theory Digraph
  imports 
  "CAVA_Base/CAVA_Base"
  "Words"
begin

subsection "Directed Graphs"
text {* Directed graphs are modeled as a relation on nodes *}
type_synonym 'v digraph = "('v\<times>'v) set"

locale digraph = fixes E :: "'v digraph"

subsubsection {* Paths *}
text {* Path are modeled as list of nodes, the last node of a path is not included
  into the list. This formalization allows for nice concatenation and splitting
  of paths. *}
inductive path :: "'v digraph \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" for E where
  path0: "path E u [] u"
| path_prepend: "\<lbrakk> (u,v)\<in>E; path E v l w \<rbrakk> \<Longrightarrow> path E u (u#l) w"

lemma path1: "(u,v)\<in>E \<Longrightarrow> path E u [u] v"
  by (auto intro: path.intros)

lemma path_empty_conv[simp]:
  "path E u [] v \<longleftrightarrow> u=v"
  by (auto intro: path0 elim: path.cases)

inductive_cases path_uncons: "path E u (u'#l) w"
inductive_simps path_cons_conv: "path E u (u'#l) w"

lemma path_no_edges[simp]: "path {} u p v \<longleftrightarrow> (u=v \<and> p=[])"
  by (cases p) (auto simp: path_cons_conv)

lemma path_conc: 
  assumes P1: "path E u la v" 
  assumes P2: "path E v lb w"
  shows "path E u (la@lb) w"
  using P1 P2 apply induct 
  by (auto intro: path.intros)
  
lemma path_append:
  "\<lbrakk> path E u l v; (v,w)\<in>E \<rbrakk> \<Longrightarrow> path E u (l@[v]) w"
  using path_conc[OF _ path1] .

lemma path_unconc:
  assumes "path E u (la@lb) w"
  obtains v where "path E u la v" and "path E v lb w"
  using assms 
  thm path.induct
  apply (induct u "la@lb" w arbitrary: la lb rule: path.induct)
  apply (auto intro: path.intros elim!: list_Cons_eq_append_cases)
  done

lemma path_conc_conv: 
  "path E u (la@lb) w \<longleftrightarrow> (\<exists>v. path E u la v \<and> path E v lb w)"
  by (auto intro: path_conc elim: path_unconc)

lemma (in -) path_append_conv: "path E u (p@[v]) w \<longleftrightarrow> (path E u p v \<and> (v,w)\<in>E)"
  by (simp add: path_cons_conv path_conc_conv)

lemmas path_simps = path_empty_conv path_cons_conv path_conc_conv


lemmas path_trans[trans] = path_prepend path_conc path_append
lemma path_from_edges: "\<lbrakk>(u,v)\<in>E; (v,w)\<in>E\<rbrakk> \<Longrightarrow> path E u [u] v" 
  by (auto simp: path_simps)


lemma path_edge_cases[case_names no_use split]: 
  assumes "path (insert (u,v) E) w p x"
  obtains 
    "path E w p x" 
  | p1 p2 where "path E w p1 u" "path (insert (u,v) E) v p2 x"
  using assms
  apply induction
  apply simp
  apply (clarsimp)
  apply (metis path_simps path_cons_conv)
  done

lemma path_edge_rev_cases[case_names no_use split]: 
  assumes "path (insert (u,v) E) w p x"
  obtains 
    "path E w p x" 
  | p1 p2 where "path (insert (u,v) E) w p1 u" "path E v p2 x"
  using assms
  apply (induction p arbitrary: x rule: rev_induct)
  apply simp
  apply (clarsimp simp: path_cons_conv path_conc_conv)
  apply (metis path_simps path_append_conv)
  done


lemma path_mono: 
  assumes S: "E\<subseteq>E'" 
  assumes P: "path E u p v" 
  shows "path E' u p v"
  using P
  apply induction
  apply simp
  using S
  apply (auto simp: path_cons_conv)
  done

lemma path_is_rtrancl: 
  assumes "path E u l v"
  shows "(u,v)\<in>E\<^sup>*"
  using assms 
  by induct auto

lemma rtrancl_is_path:
  assumes "(u,v)\<in>E\<^sup>*"
  obtains l where "path E u l v"
  using assms 
  by induct (auto intro: path0 path_append)

lemma path_is_trancl: 
  assumes "path E u l v"
  and "l\<noteq>[]"
  shows "(u,v)\<in>E\<^sup>+"
  using assms 
  apply induct
  apply auto []
  apply (case_tac l)
  apply auto
  done

lemma trancl_is_path:
  assumes "(u,v)\<in>E\<^sup>+"
  obtains l where "l\<noteq>[]" and "path E u l v"
  using assms 
  by induct (auto intro: path0 path_append)

lemma path_nth_conv: "path E u p v \<longleftrightarrow> (let p'=p@[v] in
  u=p'!0 \<and>
  (\<forall>i<length p' - 1. (p'!i,p'!Suc i)\<in>E))"
  apply (induct p arbitrary: v rule: rev_induct)
  apply (auto simp: path_conc_conv path_cons_conv nth_append)
  done

lemma path_mapI:
  assumes "path E u p v"
  shows "path (pairself f ` E) (f u) (map f p) (f v)"
  using assms
  apply induction
  apply (simp)
  apply (force simp: path_cons_conv)
  done

lemma path_restrict: 
  assumes "path E u p v" 
  shows "path (E \<inter> set p \<times> insert v (set (tl p))) u p v"
  using assms
proof induction
  print_cases
  case (path_prepend u v p w)
  from path_prepend.IH have "path (E \<inter> set (u#p) \<times> insert w (set p)) v p w"
    apply (rule path_mono[rotated])
    by (cases p) auto
  thus ?case using `(u,v)\<in>E`
    by (cases p) (auto simp add: path_cons_conv)
qed auto

lemma path_restrict_closed:
  assumes CLOSED: "E``D \<subseteq> D"
  assumes I: "v\<in>D" and P: "path E v p v'"
  shows "path (E\<inter>D\<times>D) v p v'"
  using P CLOSED I
  by induction (auto simp: path_cons_conv)


lemma path_set_induct:
  assumes "path E u p v" and "u\<in>I" and "E``I \<subseteq> I"
  shows "set p \<subseteq> I"
  using assms
  by (induction rule: path.induct) auto

lemma path_nodes_reachable: "path E u p v \<Longrightarrow> insert v (set p) \<subseteq> E\<^sup>*``{u}"
  apply (auto simp: in_set_conv_decomp path_cons_conv path_conc_conv)
  apply (auto dest!: path_is_rtrancl)
  done

lemma path_nodes_edges: "path E u p v \<Longrightarrow> set p \<subseteq> fst`E"
  by (induction rule: path.induct) auto

lemma path_tl_nodes_edges: 
  assumes "path E u p v"
  shows "set (tl p) \<subseteq> fst`E \<inter> snd`E"
proof -
  from path_nodes_edges[OF assms] have "set (tl p) \<subseteq> fst`E"
    by (cases p) auto

  moreover have "set (tl p) \<subseteq> snd`E"
    using assms
    apply (cases)
    apply simp
    apply simp
    apply (erule path_set_induct[where I = "snd`E"])
    apply auto
    done
  ultimately show ?thesis
    by auto
qed

lemma path_loop_shift: 
  assumes P: "path E u p u"
  assumes S: "v\<in>set p"
  obtains p' where "set p' = set p" "path E v p' v"
proof -
  from S obtain p1 p2 where [simp]: "p = p1@v#p2" by (auto simp: in_set_conv_decomp)
  from P obtain v' where A: "path E u p1 v" "(v, v') \<in> E" "path E v' p2 u" 
    by (auto simp: path_simps)
  hence "path E v (v#p2@p1) v" by (auto simp: path_simps)
  thus ?thesis using that[of "v#p2@p1"] by auto
qed



subsubsection {* Infinite Paths *}
definition ipath :: "'q digraph \<Rightarrow> 'q word \<Rightarrow> bool"
  -- "Predicate for an infinite path in a digraph"
  where "ipath E r \<equiv> \<forall>i. (r i, r (Suc i))\<in>E"


lemma ipath_conc_conv: 
  "ipath E (u \<frown> v) \<longleftrightarrow> (\<exists>a. path E a u (v 0) \<and> ipath E v)"
  apply (auto simp: conc_def ipath_def path_nth_conv nth_append)
  apply (metis add_Suc_right diff_add_inverse not_add_less1)
  by (metis Suc_diff_Suc diff_Suc_Suc not_less_eq)

lemma ipath_iter_conv:
  assumes "p\<noteq>[]"
  shows "ipath E (p\<^sup>\<omega>) \<longleftrightarrow> (path E (hd p) p (hd p))"
proof (cases p)
  case Nil thus ?thesis using assms by simp
next
  case (Cons u p') hence PLEN: "length p > 0" by simp
  show ?thesis proof 
    assume "ipath E (iter (p))"
    hence "\<forall>i. (iter (p) i, iter (p) (Suc i)) \<in> E"
      unfolding ipath_def by simp
    hence "(\<forall>i<length p. (p!i,(p@[hd p])!Suc i)\<in>E)" 
      apply (simp add: assms)
      apply safe
      apply (drule_tac x=i in spec)
      apply simp
      apply (case_tac "Suc i = length p")
      apply (simp add: Cons)
      apply (simp add: nth_append)
      done
    thus "path E (hd p) p (hd p)"
      by (auto simp: path_nth_conv Cons nth_append nth_Cons')
  next
    assume "path E (hd p) p (hd p)"
    thus "ipath E (iter p)"
      apply (auto simp: path_nth_conv ipath_def assms Let_def)
      apply (drule_tac x="i mod length p" in spec)
      apply (auto simp: nth_append assms split: split_if_asm)
      apply (metis less_not_refl mod_Suc)
      by (metis PLEN diff_self_eq_0 mod_Suc nth_Cons_0 
        semiring_numeral_div_class.pos_mod_bound)
  qed
qed

lemma ipath_to_rtrancl:
  assumes R: "ipath E r"
  assumes I: "i1\<le>i2"
  shows "(r i1,r i2)\<in>E\<^sup>*"
  using I
proof (induction i2)
  case (Suc i2)
  show ?case proof (cases "i1=Suc i2")
    assume "i1\<noteq>Suc i2"
    with Suc have "(r i1,r i2)\<in>E\<^sup>*" by auto
    also from R have "(r i2,r (Suc i2))\<in>E" unfolding ipath_def by auto
    finally show ?thesis .
  qed simp
qed simp
    
lemma ipath_to_trancl:
  assumes R: "ipath E r"
  assumes I: "i1<i2"
  shows "(r i1,r i2)\<in>E\<^sup>+"
proof -
  from R have "(r i1,r (Suc i1))\<in>E"
    by (auto simp: ipath_def)
  also have "(r (Suc i1),r i2)\<in>E\<^sup>*"
    using ipath_to_rtrancl[OF R,of "Suc i1" i2] I by auto
  finally (rtrancl_into_trancl2) show ?thesis .
qed

lemma run_limit_two_connectedI:
  assumes A: "ipath E r" 
  assumes B: "a \<in> limit r" "b\<in>limit r"
  shows "(a,b)\<in>E\<^sup>+"
proof -
  from B have "{a,b} \<subseteq> limit r" by simp
  with A show ?thesis
    by (metis ipath_to_trancl two_in_limit_iff)
qed


lemma ipath_subpath:
  assumes P: "ipath E r"
  assumes LE: "l\<le>u"
  shows "path E (r l) (map r [l..<u]) (r u)"
  using LE
proof (induction "u-l" arbitrary: u l)
  case (Suc n)
  note IH=Suc.hyps(1)
  from `Suc n = u-l` `l\<le>u` obtain u' where [simp]: "u=Suc u'" 
    and A: "n=u'-l" "l \<le> u'" 
    by (cases u) auto
    
  note IH[OF A]
  also from P have "(r u',r u)\<in>E"
    by (auto simp: ipath_def)
  finally show ?case using `l \<le> u'` by (simp add: upt_Suc_append)
qed auto  

lemma ipath_restrict_eq: "ipath (E \<inter> (E\<^sup>*``{r 0} \<times> E\<^sup>*``{r 0})) r \<longleftrightarrow> ipath E r"
  unfolding ipath_def
  by (auto simp: relpow_fun_conv rtrancl_power)
lemma ipath_restrict: "ipath E r \<Longrightarrow> ipath (E \<inter> (E\<^sup>*``{r 0} \<times> E\<^sup>*``{r 0})) r"
  by (simp add: ipath_restrict_eq)


lemma ipathI[intro?]: "\<lbrakk>\<And>i. (r i, r (Suc i)) \<in> E\<rbrakk> \<Longrightarrow> ipath E r"
  unfolding ipath_def by auto

lemma ipathD: "ipath E r \<Longrightarrow> (r i, r (Suc i)) \<in> E"
  unfolding ipath_def by auto

lemma ipath_in_Domain: "ipath E r \<Longrightarrow> r i \<in> Domain E"
  unfolding ipath_def by auto

lemma ipath_in_Range: "\<lbrakk>ipath E r; i\<noteq>0\<rbrakk> \<Longrightarrow> r i \<in> Range E"
  unfolding ipath_def by (cases i) auto

lemma ipath_suffix: "ipath E r \<Longrightarrow> ipath E (suffix i r)"
  unfolding suffix_def ipath_def by auto



subsubsection {* Strongly Connected Components *}

text {* A strongly connected component is a maximal mutually connected set 
  of nodes *}
definition is_scc :: "'q digraph \<Rightarrow> 'q set \<Rightarrow> bool"
  where "is_scc E U \<longleftrightarrow> U\<times>U\<subseteq>E\<^sup>* \<and> (\<forall>V. V\<supset>U \<longrightarrow> \<not> (V\<times>V\<subseteq>E\<^sup>*))"

lemma scc_non_empty[simp]: "\<not>is_scc E {}" unfolding is_scc_def by auto

lemma scc_non_empty'[simp]: "is_scc E U \<Longrightarrow> U\<noteq>{}" unfolding is_scc_def by auto

lemma is_scc_closed: 
  assumes SCC: "is_scc E U"
  assumes MEM: "x\<in>U"
  assumes P: "(x,y)\<in>E\<^sup>*" "(y,x)\<in>E\<^sup>*"
  shows "y\<in>U"
proof -
  from SCC MEM P have "insert y U \<times> insert y U \<subseteq> E\<^sup>*"
    unfolding is_scc_def
    apply clarsimp
    apply rule
    apply clarsimp_all
    apply (erule disjE1)
    apply clarsimp
    apply (metis in_mono mem_Sigma_iff rtrancl_trans)
    apply auto []
    apply (erule disjE1)
    apply clarsimp
    apply (metis in_mono mem_Sigma_iff rtrancl_trans)
    apply auto []
    done
  with SCC show ?thesis unfolding is_scc_def by blast
qed

lemma is_scc_connected:
  assumes SCC: "is_scc E U"
  assumes MEM: "x\<in>U" "y\<in>U"
  shows "(x,y)\<in>E\<^sup>*"
  using assms unfolding is_scc_def by auto

text {* In the following, we play around with alternative characterizations, and
  prove them all equivalent .*}

text {* A common characterization is to define an equivalence relation 
  ,,mutually connected'' on nodes, and characterize the SCCs as its 
  equivalence classes: *}

definition mconn :: "('a\<times>'a) set \<Rightarrow> ('a \<times> 'a) set"
  -- "Mutually connected relation on nodes"
  where "mconn E = E\<^sup>* \<inter> (E\<inverse>)\<^sup>*"

lemma mconn_pointwise:
   "mconn E = {(u,v). (u,v)\<in>E\<^sup>* \<and> (v,u)\<in>E\<^sup>*}"
  by (auto simp add: mconn_def rtrancl_converse)

text {* @{text "mconn"} is an equivalence relation: *}
lemma mconn_refl[simp]: "Id\<subseteq>mconn E"
  by (auto simp add: mconn_def)

lemma mconn_sym: "mconn E = (mconn E)\<inverse>"
  by (auto simp add: mconn_pointwise)

lemma mconn_trans: "mconn E O mconn E = mconn E"
  by (auto simp add: mconn_def)

lemma is_scc_mconn_eqclasses: "is_scc E U \<longleftrightarrow> U \<in> UNIV // mconn E"
  -- "The strongly connected components are the equivalence classes of the 
    mutually-connected relation on nodes"
proof
  assume A: "is_scc E U"
  then obtain x where "x\<in>U" unfolding is_scc_def by auto
  hence "U = mconn E `` {x}" using A
    unfolding mconn_pointwise is_scc_def
    apply clarsimp
    apply rule
    apply auto []
    apply clarsimp
    by (metis A is_scc_closed)
  thus "U \<in> UNIV // mconn E"
    by (auto simp: quotient_def)
next
  assume "U \<in> UNIV // mconn E"
  thus "is_scc E U"
    by (auto simp: is_scc_def mconn_pointwise quotient_def)
qed

(* For presentation in the paper *)
lemma "is_scc E U \<longleftrightarrow> U \<in> UNIV // (E\<^sup>* \<inter> (E\<inverse>)\<^sup>*)"
  unfolding is_scc_mconn_eqclasses mconn_def by simp

text {* We can also restrict the notion of "reachability" to nodes
  inside the SCC
  *}

lemma find_outside_node:
  assumes "(u,v)\<in>E\<^sup>*"
  assumes "(u,v)\<notin>(E\<inter>U\<times>U)\<^sup>*"
  assumes "u\<in>U" "v\<in>U"
  shows "\<exists>u'. u'\<notin>U \<and> (u,u')\<in>E\<^sup>* \<and> (u',v)\<in>E\<^sup>*"
  using assms
  apply (induction)
  apply auto []
  apply clarsimp
  by (metis IntI mem_Sigma_iff rtrancl.simps)

lemma is_scc_restrict1:
  assumes SCC: "is_scc E U"
  shows "U\<times>U\<subseteq>(E\<inter>U\<times>U)\<^sup>*"
  using assms
  unfolding is_scc_def
  apply clarsimp
  apply (rule ccontr)
  apply (drule (2) find_outside_node[rotated])
  apply auto []
  by (metis is_scc_closed[OF SCC] mem_Sigma_iff rtrancl_trans subsetD)

lemma is_scc_restrict2:
  assumes SCC: "is_scc E U"
  assumes "V\<supset>U"
  shows "\<not> (V\<times>V\<subseteq>(E\<inter>V\<times>V)\<^sup>*)"
  using assms
  unfolding is_scc_def
  apply clarsimp
  using rtrancl_mono[of "E \<inter> V \<times> V" "E"]
  apply clarsimp
  apply blast
  done

lemma is_scc_restrict3: 
  assumes SCC: "is_scc E U"
  shows "((E\<^sup>*``((E\<^sup>*``U) - U)) \<inter> U = {})"
  apply auto
  by (metis assms is_scc_closed is_scc_connected rtrancl_trans)
  
lemma is_scc_alt_restrict_path:
  "is_scc E U \<longleftrightarrow> U\<noteq>{} \<and>
    (U\<times>U \<subseteq> (E\<inter>U\<times>U)\<^sup>*) \<and> ((E\<^sup>*``((E\<^sup>*``U) - U)) \<inter> U = {})"
  apply rule
  apply (intro conjI)
  apply simp
  apply (blast dest: is_scc_restrict1)
  apply (blast dest: is_scc_restrict3)
  
  unfolding is_scc_def
  apply rule
  apply clarsimp
  apply (metis (full_types) Int_lower1 in_mono mem_Sigma_iff rtrancl_mono_mp)
  apply blast
  done

lemma is_scc_pointwise:
  "is_scc E U \<longleftrightarrow> 
    U\<noteq>{}
  \<and> (\<forall>u\<in>U. \<forall>v\<in>U. (u,v)\<in>(E\<inter>U\<times>U)\<^sup>*) 
  \<and> (\<forall>u\<in>U. \<forall>v. (v\<notin>U \<and> (u,v)\<in>E\<^sup>*) \<longrightarrow> (\<forall>u'\<in>U. (v,u')\<notin>E\<^sup>*))"
  -- "Alternative, pointwise characterization"
  unfolding is_scc_alt_restrict_path
  by blast  


subsection "Finitely Reachable Graphs"
text {* Finitely reachable graphs are directed graphs with an explicit set 
  of root nodes, such that only finitely many nodes are reachable from
  the set of root nodes *}

record 'v fr_graph_rec = 
  frg_V :: "'v set"
  frg_E :: "'v digraph"  
  frg_V0 :: "'v set"

locale fr_graph = 
  -- "Directed graph with explicit set of root nodes, and 
      finitely many reachable nodes"
  fixes G :: "('v,'more) fr_graph_rec_scheme"
  assumes finite_reachableE_V0[simp, intro!]: "finite ((frg_E G)\<^sup>*``frg_V0 G)"
  assumes V0_ss: "frg_V0 G \<subseteq> (frg_V G)"
  assumes E_ss: "frg_E G \<subseteq> (frg_V G)\<times>(frg_V G)"
begin
  abbreviation "V \<equiv> frg_V G"
  abbreviation "E \<equiv> frg_E G"
  abbreviation "V0 \<equiv> frg_V0 G"

  lemma is_fr_graph: "fr_graph G" by unfold_locales

  lemma finite_V0[simp, intro!]: "finite V0"
    using finite_reachableE_V0
    apply (rule finite_subset[rotated])
    by auto

  definition is_run
    -- "Infinite run, i.e., a rooted infinite path"
    where "is_run r \<equiv> r 0 \<in> V0 \<and> ipath E r"
  
  lemma run_reachable: "is_run r \<Longrightarrow> r i \<in> E\<^sup>*``V0"
    unfolding is_run_def
    using ipath_to_rtrancl[of "frg_E G" r 0 i]
    by auto
  
  lemma 
    assumes "is_run r"
    shows run_ipath: "ipath E r"
    and run_V0: "r 0 \<in> V0"
    using assms unfolding is_run_def by auto


  lemma is_run_finite: "is_run r \<Longrightarrow> finite (range r)"
    apply (rule finite_subset[OF _ finite_reachableE_V0])
    using run_reachable
    by auto

  lemma run_V: "is_run r \<Longrightarrow> range r \<subseteq> V"
    using run_ipath[THEN ipath_in_Domain] E_ss by auto

end

locale fin_fr_graph = fr_graph G 
  for G :: "('v,'more) fr_graph_rec_scheme"
+ assumes finite_V[simp, intro!]: "finite V"
begin
  lemma is_fin_fr_graph: "fin_fr_graph G" by unfold_locales

  lemma finite_E[simp, intro!]: "finite E"
    using finite_subset[OF E_ss] by auto

end


abbreviation "rename_E f E \<equiv> (\<lambda>(u,v). (f u, f v))`E"

definition "fr_rename_ext ecnv f G \<equiv> \<lparr> 
    frg_V = f`(frg_V G),
    frg_E = rename_E f (frg_E G),   
    frg_V0 = (f`frg_V0 G),
    \<dots> = ecnv G
  \<rparr>"

locale fr_rename_precond
  = fr_graph G for G :: "('u,'more) fr_graph_rec_scheme" +
  fixes f :: "'u \<Rightarrow> 'v"
  fixes ecnv :: "('u, 'more) fr_graph_rec_scheme \<Rightarrow> 'more'"
  assumes INJ: "inj_on f V"
begin
  abbreviation "G' \<equiv> fr_rename_ext ecnv f G"

  lemma G'_fields:
    "frg_V G' = f`V"
    "frg_V0 G' = f`V0"
    "frg_E G' = rename_E f E"
    unfolding fr_rename_ext_def by simp_all

  definition "fi \<equiv> the_inv_into V f"

  lemma 
    fi_f: "x\<in>V \<Longrightarrow> fi (f x) = x" and
    f_fi: "y\<in>f`V \<Longrightarrow> f (fi y) = y" and
    fi_f_eq: "\<lbrakk>f x = y; x\<in>V\<rbrakk> \<Longrightarrow> fi y = x"
    unfolding fi_def
    by (auto 
      simp: the_inv_into_f_f f_the_inv_into_f the_inv_into_f_eq INJ)

  lemma E'_to_E: "(u,v) \<in> frg_E G' \<Longrightarrow> (fi u, fi v)\<in>E"
    using E_ss
    by (auto simp: fi_f G'_fields)

  lemma V0'_to_V0: "v\<in>frg_V0 G' \<Longrightarrow> fi v \<in> V0"
    using V0_ss
    by (auto simp: fi_f G'_fields)


  lemma rtrancl_E'_sim:
    assumes "(f u,v')\<in>(frg_E G')\<^sup>*"
    assumes "u\<in>V"
    shows "\<exists>v. v' = f v \<and> v\<in>V \<and> (u,v)\<in>E\<^sup>*"
    using assms
  proof (induction "f u" v' arbitrary: u)
    case (rtrancl_into_rtrancl v' w' u)
    then obtain v w where "v' = f v" "w' = f w" "(v,w)\<in>E"
      by (auto simp: G'_fields)
    hence "v\<in>V" "w\<in>V" using E_ss by auto
    from rtrancl_into_rtrancl obtain vv where "v' = f vv" "vv\<in>V" "(u,vv)\<in>E\<^sup>*"
      by blast
    from `v' = f v` `v\<in>V` `v' = f vv` `vv\<in>V` have [simp]: "vv = v"
      using INJ by (metis inj_on_contraD)

    note `(u,vv)\<in>E\<^sup>*`[simplified]
    also note `(v,w)\<in>E`
    finally show ?case using `w' = f w` `w\<in>V` by blast
  qed auto
    
  lemma rtrancl_E'_to_E: assumes "(u,v)\<in>(frg_E G')\<^sup>*" shows "(fi u, fi v)\<in>E\<^sup>*"
    using assms apply induction
    by (fastforce intro: E'_to_E rtrancl_into_rtrancl)+

  lemma G'_invar: "fr_graph G'"
    apply unfold_locales
  proof -
    have "(frg_E G')\<^sup>* `` frg_V0 G' \<subseteq> f ` (E\<^sup>*``V0)"
      apply (clarsimp_all simp: G'_fields(2))
      apply (drule rtrancl_E'_sim)
      using V0_ss apply auto []
      apply auto
      done
    thus "finite ((frg_E G')\<^sup>* `` frg_V0 G')" 
      by (rule finite_subset) simp
    
    show "frg_V0 G' \<subseteq> frg_V G'"
      using V0_ss by (auto simp: G'_fields) []

    show "frg_E G' \<subseteq> frg_V G' \<times> frg_V G'"
      using E_ss by (auto simp: G'_fields) []
  qed

  sublocale G'!: fr_graph G' using G'_invar .

  lemma V'_to_V: "v \<in> G'.V \<Longrightarrow> fi v \<in> V"
    by (auto simp: fi_f G'_fields)

  lemma ipath_sim1: "ipath E r \<Longrightarrow> ipath G'.E (f o r)"
    unfolding ipath_def by (auto simp: G'_fields)

  lemma ipath_sim2: "ipath G'.E r \<Longrightarrow> ipath E (fi o r)"
    unfolding ipath_def 
    apply (clarsimp simp: G'_fields)
    apply (drule_tac x=i in spec)
    using E_ss
    by (auto simp: fi_f)

  lemma run_sim1: "is_run r \<Longrightarrow> G'.is_run (f o r)"
    unfolding is_run_def G'.is_run_def
    apply (intro conjI)
    apply (auto simp: G'_fields) []
    apply (auto simp: ipath_sim1)
    done

  lemma run_sim2: "G'.is_run r \<Longrightarrow> is_run (fi o r)"
    unfolding is_run_def G'.is_run_def
    by (auto simp: ipath_sim2 V0'_to_V0)

end


end
