(*  Title:      Presburger-Automata/DFS.thy
    Author:     Toshiaki Nishihara and Yasuhiko Minamide
    Author:     Stefan Berghofer and Alex Krauss, TU Muenchen, 2008-2009
    Author:     Peter Gammie (data refinement futz), 2010
*)

header "Generic DFS"

theory DFS
imports Main
begin


(*

We use a generic DFS to construct the transitions and action function
of the implementation of the JKBP. This theory is largely due to
\cite{DBLP:conf/tphol/BerghoferR09}, who based their work on
\cite{Nishihara-Minamide-AFP04}.

All proofs are elided as the details of how we explore the state
space is inessential to the JKBP synthesis algorithm.

*)


definition
  "succsr succs \<equiv> {(x, y). y \<in> set (succs x)}"


partial_function (tailrec)
  gen_dfs
where
  "gen_dfs succs ins memb S wl = (case wl of
     [] \<Rightarrow> S
   | (x # xs) \<Rightarrow>
       if memb x S then gen_dfs succs ins memb S xs
       else gen_dfs succs ins memb (ins x S) (succs x @ xs))"

lemma gen_dfs_simps[simp]:
  "gen_dfs succs ins memb S [] = S"
  "gen_dfs succs ins memb S (x # xs) =
    (if memb x S then gen_dfs succs ins memb S xs
     else gen_dfs succs ins memb (ins x S) (succs x @ xs))"
  by (simp_all add: gen_dfs.simps)

(*

Most of these assumptions are straightforward.

We require that the transition relation respects the data abstraction
function.

*)

locale DFS =
  fixes succs :: "'a \<Rightarrow> 'a list"
  and is_node :: "'a \<Rightarrow> bool"
  and invariant :: "'b \<Rightarrow> bool"
  and ins :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  and memb :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and empt :: 'b
  and node_abs :: "'a \<Rightarrow> 'c"
  assumes ins_eq: "\<And>x y S. \<lbrakk> is_node x; is_node y; invariant S; \<not> memb y S \<rbrakk>
                       \<Longrightarrow> memb x (ins y S) \<longleftrightarrow> ((node_abs x = node_abs y) \<or> memb x S)"
  and succs: "\<And>x y. \<lbrakk> is_node x; is_node y; node_abs x = node_abs y \<rbrakk>
                       \<Longrightarrow> node_abs ` set (succs x) = node_abs ` set (succs y)"
  and empt: "\<And>x. is_node x \<Longrightarrow> \<not> memb x empt"
  and succs_is_node: "\<And>x. is_node x \<Longrightarrow> list_all is_node (succs x)"
  and empt_invariant: "invariant empt"
  and ins_invariant: "\<And>x S. is_node x \<Longrightarrow> invariant S \<Longrightarrow> \<not> memb x S \<Longrightarrow> invariant (ins x S)"
  and graph_finite: "finite (node_abs ` is_node)"
begin


definition rel where
  "rel = inv_image finite_psubset (\<lambda>S. node_abs ` {n \<in> is_node. \<not> memb n S})"

abbreviation
  "dfs \<equiv> gen_dfs succs ins memb"

(* Yuck, something to do with Skolems broke. *)
lemma FIXME_grot:
  "\<lbrakk>invariant S; is_node x; list_all is_node xs; \<not>memb x S\<rbrakk>
     \<Longrightarrow> node_abs ` {n \<in> is_node. \<not> memb n (ins x S)}
       \<subset> node_abs ` {n \<in> is_node. \<not> memb n S}"
  apply rule
   apply (auto simp add: ins_eq mem_def cong: conj_cong)
  apply (subgoal_tac "node_abs x \<in> node_abs ` {n. is_node n \<and> \<not> memb n S}")
   apply (subgoal_tac "node_abs x \<notin> node_abs ` {n. is_node n \<and> node_abs n \<noteq> node_abs x \<and> \<not> memb n S}")
    apply blast
   apply rule
   apply (erule imageE) back
   apply auto[1]
  apply auto[1]
  done

lemma psubsetI2: "\<lbrakk> A \<subseteq> B; x \<in> A; x \<notin> B\<rbrakk> \<Longrightarrow> A \<subset> B"
  by (unfold less_le) blast

lemma dfs_induct[consumes 2, case_names base step]:
  assumes S: "invariant S"
  and xs: "list_all is_node xs"
  and I1: "\<And>S. invariant S \<Longrightarrow> P S []"
  and I2: "\<And>S x xs. invariant S \<Longrightarrow> is_node x \<Longrightarrow> list_all is_node xs \<Longrightarrow>
    (memb x S \<Longrightarrow> P S xs) \<Longrightarrow> (\<not> memb x S \<Longrightarrow> P (ins x S) (succs x @ xs)) \<Longrightarrow> P S (x # xs)"
  shows "P S xs" using I1 I2 S xs
  apply induction_schema
  apply atomize_elim
  apply (case_tac xs, simp+)
  apply atomize_elim
  apply (rule conjI)
  apply (rule ins_invariant, assumption+)
  apply (rule succs_is_node, assumption)
  apply (relation "rel <*lex*> measure length")
  apply (simp add: wf_lex_prod rel_def)
  apply simp
  apply simp
  apply (rule disjI1)
  apply (simp add: rel_def finite_psubset_def)
  apply (rule conjI)
  apply (erule FIXME_grot)
  apply simp_all
  apply (rule finite_subset[OF _ graph_finite])
  apply auto
  done

definition
  "succss xs \<equiv> \<Union>x\<in>xs. set (succs x)"

definition
  "set_of S \<equiv> {x. is_node x \<and> memb x S}"

definition
  "reachable xs \<equiv> {(x, y). y \<in> set (succs x)}\<^sup>* `` xs"

lemma visit_subset_dfs: "invariant S \<Longrightarrow> list_all is_node xs \<Longrightarrow>
  is_node y \<Longrightarrow> memb y S \<Longrightarrow> memb y (dfs S xs)"
  by (induct S xs rule: dfs_induct) (simp_all add: ins_eq)

lemma next_subset_dfs: "invariant S \<Longrightarrow> list_all is_node xs \<Longrightarrow>
  x \<in> set xs \<Longrightarrow> memb x (dfs S xs)"
proof (induct S xs rule: dfs_induct)
  case (step S y xs)
  then show ?case
    by (auto simp add: visit_subset_dfs ins_eq ins_invariant succs_is_node)
qed simp

lemma succss_closed_dfs':
  "invariant ys \<Longrightarrow> list_all is_node xs \<Longrightarrow>
   node_abs ` succss (set_of ys) \<subseteq> node_abs ` (set xs \<union> set_of ys) \<Longrightarrow> node_abs ` succss (set_of (dfs ys xs)) \<subseteq> node_abs ` set_of (dfs ys xs)"
proof(induct ys xs rule: dfs_induct)
  case (base S) thus ?case by simp
next
  case (step S x xs) thus ?case
    apply (auto simp add: succss_def set_of_def cong: conj_cong)
     apply (subgoal_tac "node_abs xa \<in> node_abs ` (\<Union>x\<in>{x. is_node x \<and> memb x (dfs S xs)}. set (succs x))")
      apply blast
     apply blast
    apply (subgoal_tac "node_abs ` (\<Union>x\<in>{xa. is_node xa \<and> memb xa (ins x S)}. set (succs x)) \<subseteq> node_abs ` (set (succs x) \<union> set xs \<union> {xa. is_node xa \<and> memb xa (ins x S)})")
     apply blast
    apply (auto simp add: ins_eq succss_def set_of_def cong: conj_cong)
    apply (subgoal_tac "\<exists>xc'. xc' \<in> set (succs x) \<and> node_abs xc' = node_abs xc")
     apply clarsimp
     apply (rule_tac x=xc' in image_eqI)
      apply simp
     apply simp
    apply (cut_tac x=xd and y=x in succs)
     apply simp_all
    apply (subgoal_tac "node_abs xc \<in> node_abs ` set (succs x)")
     apply auto[1]
    apply auto[1]
   apply (subgoal_tac "node_abs ` set (succs xd) \<subseteq> node_abs ` (\<Union>x\<in>{x. is_node x \<and> memb x S}. set (succs x))")
    defer
    apply auto[1]
   apply (subgoal_tac "node_abs xc \<in> node_abs ` set (succs xd)")
    defer
    apply auto[1]
   apply (subgoal_tac "node_abs xc \<in> insert (node_abs x) (node_abs ` (set xs \<union> {x. is_node x \<and> memb x S}))")
    defer
    apply (erule set_rev_mp)
    apply (erule subset_trans)
    apply blast
   apply auto
   done
qed

lemma succss_closed_dfs: "list_all is_node xs \<Longrightarrow>
  node_abs ` succss (set_of (dfs empt xs)) \<subseteq> node_abs ` set_of (dfs empt xs)"
  apply (rule succss_closed_dfs')
  apply (rule empt_invariant)
  apply assumption
  apply (simp add: succss_def)
  apply (rule subsetI)
  apply clarsimp
  unfolding set_of_def
  using empt
  apply clarsimp
  done

theorem succsr_is_node:
  assumes xy: "(x, y) \<in> (succsr succs)\<^sup>*"
  shows "is_node x \<Longrightarrow> is_node y" using xy
proof induct
  case (step y z)
  then have "is_node y" by simp
  then have "list_all is_node (succs y)"
    by (rule succs_is_node)
  with step show ?case
    by (simp add: succsr_def list_all_iff)
qed

lemma succss_closed:
  assumes inc: "node_abs ` succss X \<subseteq> node_abs ` X"
      and X: "X \<subseteq> is_node"
  shows "node_abs ` reachable X = node_abs ` X"
proof
  show "node_abs ` X \<subseteq> node_abs ` reachable X"
    unfolding reachable_def by auto
next
  show "node_abs ` reachable X \<subseteq> node_abs ` X"
  proof(unfold reachable_def, auto)
    fix x y
    assume y: "y \<in> X"
    assume "(y, x) \<in> {(x, y). y \<in> set (succs x)}\<^sup>*"
    thus "node_abs x \<in> node_abs ` X" using y
    proof induct
      case base thus ?case by simp
    next
      case (step r s)
      from X step have "is_node r"
        using succsr_is_node[where x=y and y=r]
        unfolding succsr_def
        apply -
        apply (auto iff: mem_def)
        done
      with inc step show ?case
        apply clarsimp
        apply (subgoal_tac "is_node x")
         apply (cut_tac x=r and y=x in succs)
         apply auto
         apply (subgoal_tac "node_abs s \<in> node_abs ` set (succs x)")
         apply auto
         unfolding succss_def
         apply auto
         using X
         apply (auto iff: mem_def)
         done
     qed
   qed
qed

lemma dfs_is_node:
  assumes S: "invariant S"
      and xs: "list_all is_node xs"
  shows "set_of (dfs S xs) \<subseteq> is_node"
  using assms
  apply (induct S xs rule: dfs_induct)
  apply auto
  unfolding set_of_def
  apply auto
  apply (auto iff: mem_def)
  done

lemma reachable_closed_dfs:
  assumes xs: "list_all is_node xs"
  shows "node_abs ` reachable (set xs) \<subseteq> node_abs ` set_of (dfs empt xs)"
proof -
  from xs have "reachable (set xs) \<subseteq> reachable (set_of (dfs empt xs))"
    apply (unfold reachable_def)
    apply (rule Image_mono)
    apply (auto simp add: set_of_def next_subset_dfs empt_invariant list_all_iff)
    done
  hence "node_abs ` reachable (set xs) \<subseteq> node_abs ` reachable (set_of (dfs empt xs))"
    by auto
  also from succss_closed_dfs[OF xs] have "\<dots> = node_abs ` set_of (dfs empt xs)"
    apply (rule succss_closed)
    apply (rule dfs_is_node[OF empt_invariant xs])
    done
  finally show ?thesis .
qed

lemma reachable_succs: "reachable (set (succs x)) \<subseteq> reachable {x}"
  by (auto simp add: reachable_def intro: converse_rtrancl_into_rtrancl)

lemma dfs_subset_reachable_visit_nodes:
  "invariant ys \<Longrightarrow> list_all is_node xs \<Longrightarrow>
   node_abs ` set_of (dfs ys xs) \<subseteq> node_abs ` (reachable (set xs) \<union> set_of ys)"
proof(induct ys xs rule: dfs_induct)
  case (step S x xs)
  show ?case
  proof (cases "memb x S")
    case True
    with step show ?thesis
      apply (auto simp add: reachable_def)
      apply (drule subsetD)
       apply blast
      apply blast
      done
  next
    case False
    have "reachable (set (succs x)) \<subseteq> reachable {x}"
      by (rule reachable_succs)
    then have "reachable (set (succs x @ xs)) \<subseteq> reachable (set (x # xs))"
      by (auto simp add: reachable_def)
    then show ?thesis using step
      apply (auto simp add: reachable_def set_of_def cong: conj_cong)
       apply (subgoal_tac "node_abs xa \<in> node_abs `
            ({(x, y). y \<in> set (succs x)}\<^sup>* `` set xs \<union>
             {x. is_node x \<and> memb x S})")
        apply auto[1]
       apply auto[1]
      apply (subgoal_tac "node_abs xa \<in> node_abs `
            ({(x, y). y \<in> set (succs x)}\<^sup>* `` (set (succs x) \<union> set xs) \<union>
             {xa. is_node xa \<and> memb xa (ins x S)})")
       defer
       apply auto[1]
      apply auto[1]
       apply (rule_tac x=xb in image_eqI)
        apply auto[1]
       apply auto[1]
      apply (auto iff: ins_eq)
      done
  qed
qed (simp add: reachable_def)



theorem dfs_imp_reachable:
  assumes y: "is_node y"
      and xs: "list_all is_node xs"
      and m: "memb y (dfs empt xs)"
  shows "\<exists>y'. node_abs y' = node_abs y \<and> y' \<in> reachable (set xs)"
proof -
  from m dfs_subset_reachable_visit_nodes [OF empt_invariant xs] y
  obtain y'
    where "node_abs y' = node_abs y"
      and "y' \<in> reachable (set xs)"
    by (auto simp add: empt set_of_def)
  thus ?thesis by blast
qed

theorem reachable_imp_dfs:
  assumes y: "is_node y"
      and xs: "list_all is_node xs"
      and m: "y \<in> reachable (set xs)"
  shows "\<exists>y'. node_abs y' = node_abs y \<and> memb y' (dfs empt xs)"
  using y m reachable_closed_dfs[OF xs]
  apply (auto simp add: set_of_def)
  apply (drule subsetD[where c="node_abs y"])
   apply simp
  apply auto
  done


theorem dfs_invariant [consumes 2, case_names base step]:
  assumes S: "invariant S"
  and xs: "list_all is_node xs"
  and H: "I S"
  and I: "\<And>S x. \<not> memb x S \<Longrightarrow> is_node x \<Longrightarrow> invariant S \<Longrightarrow> I S \<Longrightarrow> I (ins x S)"
  shows "I (dfs S xs)"
proof -
  from S xs H
  have "I (dfs S xs) \<and> invariant (dfs S xs)"
  proof (induct S xs rule: dfs_induct)
    case (step S x xs)
    show ?case
    proof (cases "memb x S")
      case False
      then show ?thesis
	apply simp
	apply (rule step)
	apply assumption
	apply (rule I)
	apply assumption
	apply (rule step)+
	done
    qed (simp add: step)
  qed simp
  then show ?thesis ..
qed


theorem dfs_invariant': "invariant S \<Longrightarrow> list_all is_node xs \<Longrightarrow> invariant (dfs S xs)"
  by (induct S xs rule: dfs_induct) auto

end


end

