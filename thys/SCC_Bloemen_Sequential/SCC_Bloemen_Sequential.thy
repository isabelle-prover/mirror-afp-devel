section \<open>Overview\<close>

text \<open>
  Computing the maximal strongly connected components (SCCs) of a 
  finite directed graph is a celebrated problem in the
  theory of graph algorithms. Although Tarjan's algorithm~\<^cite>\<open>"tarjan:depth-first"\<close> 
  is perhaps the best-known solution, there are many others. In his PhD 
  thesis, Bloemen~\<^cite>\<open>"bloemen:strong"\<close> presents an algorithm that is itself based
  on earlier algorithms by Munro~\<^cite>\<open>"munro:efficient"\<close> and
  Dijkstra~\<^cite>\<open>"dijkstra:finding"\<close>. Just like these algorithms, Bloemen's
  solution is based on enumerating SCCs in a depth-first traversal of the graph.
  Gabow's algorithm that has already been formalized in Isabelle~\<^cite>\<open>"lammich:gabow"\<close>
  also falls into this category of solutions.
  Nevertheless, Bloemen goes on to present a parallel variant of the algorithm
  suitable for execution on multi-core processors, based on clever data structures
  that minimize locking.

  In the following, we encode the sequential version of the algorithm in the
  proof assistant Isabelle/HOL, and prove its correctness. Bloemen's thesis
  briefly and informally explains why the algorithm is correct. Our proof expands
  on these arguments, making them completely formal. The encoding is based on
  a direct representation of the algorithm as a pair of mutually recursive
  functions; we are not aiming at extracting executable code.
\<close>

theory SCC_Bloemen_Sequential
imports Main
begin

text \<open>
  The record below represents the variables of the
  algorithm. Most variables correspond to those used in
  Bloemen's presentation. Thus, the variable @{text \<S>}
  associates to every node the set of nodes that have
  already been determined to be part of the same SCC. A core
  invariant of the algorithm will be that this mapping represents
  equivalence classes of nodes: for all nodes @{text v} and @{text w},
  we maintain the relationship

  @{text "v \<in> \<S> w \<longleftrightarrow> \<S> v = \<S> w."}

  In an actual implementation of this algorithm, this variable
  could conveniently be represented by a union-find structure.
  Variable @{text stack} holds the list of roots of these 
  (not yet maximal) SCCs, in depth-first order,
  @{text visited} and @{text explored}
  represent the nodes that have already been seen, respectively
  that have been completely explored, by the algorithm, and
  @{text sccs} is the set of maximal SCCs that the algorithm
  has found so far.

  Additionally, the record holds some auxiliary variables that
  are used in the proof of correctness. In particular,
  @{text root} denotes the node on which the algorithm was called,
  @{text cstack} represents the call stack of the recursion of
  function @{text dfs},
  and @{text vsuccs} stores the successors of each node
  that have already been visited by the function @{text dfss}
  that loops over all successors of a given node.
\<close>
record 'v env =
  root :: "'v"
  \<S> :: "'v \<Rightarrow> 'v set"
  explored :: "'v set"
  visited :: "'v set"
  vsuccs :: "'v \<Rightarrow> 'v set"
  sccs :: "'v set set"
  stack :: "'v list"
  cstack :: "'v list"

text \<open>
  The algorithm is initially called with an environment that
  initializes the root node and trivializes all other components.
\<close>
definition init_env where
  "init_env v = \<lparr>
    root = v,
    \<S> = (\<lambda>u. {u}),
    explored = {},
    visited = {},
    vsuccs = (\<lambda>u. {}),
    sccs = {},
    stack = [],
    cstack = []
   \<rparr>"

\<comment> \<open>Make the simplifier expand let-constructions automatically.\<close>
declare Let_def[simp]



section \<open>Auxiliary lemmas about lists\<close>

text \<open>
  We use the precedence order on the elements that appear
  in a list. In particular, stacks are represented as lists,
  and a node @{text x} precedes another node @{text y} on the
  stack if @{text x} was pushed on the stack later
  than @{text y}.
\<close>

definition precedes ("_ \<preceq> _ in _" [100,100,100] 39) where
  "x \<preceq> y in xs \<equiv> \<exists>l r. xs = l @ (x # r) \<and> y \<in> set (x # r)"

lemma precedes_mem:
  assumes "x \<preceq> y in xs"
  shows "x \<in> set xs" "y \<in> set xs"
  using assms unfolding precedes_def by auto

lemma head_precedes:
  assumes "y \<in> set (x # xs)"
  shows "x \<preceq> y in (x # xs)"
  using assms unfolding precedes_def by force

lemma precedes_in_tail:
  assumes "x \<noteq> z"
  shows "x \<preceq> y in (z # zs) \<longleftrightarrow> x \<preceq> y in zs"
  using assms unfolding precedes_def by (auto simp: Cons_eq_append_conv)

lemma tail_not_precedes:
  assumes "y \<preceq> x in (x # xs)" "x \<notin> set xs"
  shows "x = y"
  using assms unfolding precedes_def
  by (metis Cons_eq_append_conv Un_iff list.inject set_append)

lemma split_list_precedes:
  assumes "y \<in> set (ys @ [x])"
  shows "y \<preceq> x in (ys @ x # xs)"
  using assms unfolding precedes_def
  by (metis append_Cons append_assoc in_set_conv_decomp
            rotate1.simps(2) set_ConsD set_rotate1)

lemma precedes_refl [simp]: "(x \<preceq> x in xs) = (x \<in> set xs)"
proof
  assume "x \<preceq> x in xs" thus "x \<in> set xs"
    by (simp add: precedes_mem)
next
  assume "x \<in> set xs"
  from this[THEN split_list] show "x \<preceq> x in xs"
    unfolding precedes_def by auto
qed

lemma precedes_append_left:
  assumes "x \<preceq> y in xs"
  shows "x \<preceq> y in (ys @ xs)"
  using assms unfolding precedes_def by (metis append.assoc)

lemma precedes_append_left_iff:
  assumes "x \<notin> set ys"
  shows "x \<preceq> y in (ys @ xs) \<longleftrightarrow> x \<preceq> y in xs" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  then obtain l r where lr: "ys @ xs = l @ (x # r)" "y \<in> set (x # r)"
    unfolding precedes_def by blast
  then obtain us where
    "(ys = l @ us \<and> us @ xs = x # r) \<or> (ys @ us = l \<and> xs = us @ (x # r))"
    by (auto simp: append_eq_append_conv2)
  thus ?rhs
  proof
    assume us: "ys = l @ us \<and> us @ xs = x # r"
    with assms have "us = []"
      by (metis Cons_eq_append_conv in_set_conv_decomp)
    with us lr show ?rhs
      unfolding precedes_def by auto
  next
    assume us: "ys @ us = l \<and> xs = us @ (x # r)"
    with \<open>y \<in> set (x # r)\<close> show ?rhs
      unfolding precedes_def by blast
  qed
next
  assume "?rhs" thus "?lhs" by (rule precedes_append_left)
qed

lemma precedes_append_right:
  assumes "x \<preceq> y in xs"
  shows "x \<preceq> y in (xs @ ys)"
  using assms unfolding precedes_def by force

lemma precedes_append_right_iff:
  assumes "y \<notin> set ys"
  shows "x \<preceq> y in (xs @ ys) \<longleftrightarrow> x \<preceq> y in xs" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain l r where lr: "xs @ ys = l @ (x # r)" "y \<in> set (x # r)"
    unfolding precedes_def by blast
  then obtain us where
    "(xs = l @ us \<and> us @ ys = x # r) \<or> (xs @ us = l \<and> ys = us @ (x # r))"
    by (auto simp: append_eq_append_conv2)
  thus ?rhs
  proof
    assume us: "xs = l @ us \<and> us @ ys = x # r"
    with \<open>y \<in> set (x # r)\<close> assms show ?rhs
      unfolding precedes_def by (metis Cons_eq_append_conv Un_iff set_append)
  next
    assume us: "xs @ us = l \<and> ys = us @ (x # r)"
    with \<open>y \<in> set (x # r)\<close> assms 
    show ?rhs by auto \<comment> \<open>contradiction\<close>
  qed
next
  assume ?rhs thus ?lhs by (rule precedes_append_right)
qed

text \<open>
  Precedence determines an order on the elements of a list,
  provided elements have unique occurrences. However, consider
  a list such as @{text "[2,3,1,2]"}: then $1$ precedes $2$ and
  $2$ precedes $3$, but $1$ does not precede $3$.
\<close>
lemma precedes_trans:
  assumes "x \<preceq> y in xs" and "y \<preceq> z in xs" and "distinct xs"
  shows "x \<preceq> z in xs"
  using assms unfolding precedes_def
  by (smt Un_iff append.assoc append_Cons_eq_iff distinct_append 
          not_distinct_conv_prefix set_append split_list_last)

lemma precedes_antisym:
  assumes "x \<preceq> y in xs" and "y \<preceq> x in xs" and "distinct xs"
  shows "x = y"
proof -
  from \<open>x \<preceq> y in xs\<close> \<open>distinct xs\<close> obtain as bs where
    1: "xs = as @ (x # bs)" "y \<in> set (x # bs)" "y \<notin> set as"
    unfolding precedes_def by force
  from \<open>y \<preceq> x in xs\<close> \<open>distinct xs\<close> obtain cs ds where
    2: "xs = cs @ (y # ds)" "x \<in> set (y # ds)" "x \<notin> set cs"
    unfolding precedes_def by force
  from 1 2 have "as @ (x # bs) = cs @ (y # ds)"
    by simp
  then obtain zs where
    "(as = cs @ zs \<and> zs @ (x # bs) = y # ds) 
     \<or> (as @ zs = cs \<and> x # bs = zs @ (y # ds))"  (is "?P \<or> ?Q")
    by (auto simp: append_eq_append_conv2)
  then show ?thesis
  proof
    assume "?P" with \<open>y \<notin> set as\<close> show ?thesis 
      by (cases "zs") auto
  next
    assume "?Q" with \<open>x \<notin> set cs\<close> show ?thesis
      by (cases "zs") auto
  qed
qed


section \<open>Finite directed graphs\<close>

text \<open>
  We represent a graph as an Isabelle locale that identifies a finite
  set of vertices (of some base type @{text "'v"}) and associates to
  each vertex its set of successor vertices.
\<close>

locale graph =
  fixes vertices :: "'v set"
    and successors :: "'v \<Rightarrow> 'v set"
  assumes vfin: "finite vertices"
    and sclosed: "\<forall>x \<in> vertices. successors x \<subseteq> vertices"

context graph
begin

abbreviation edge where
  "edge x y \<equiv> y \<in> successors x"

text \<open>
  We inductively define reachability of nodes in the graph.
\<close>
inductive reachable where
  reachable_refl[iff]: "reachable x x"
| reachable_succ[elim]: "\<lbrakk>edge x y; reachable y z\<rbrakk> \<Longrightarrow> reachable x z"

lemma reachable_edge: "edge x y \<Longrightarrow> reachable x y"
  by auto

lemma succ_reachable:
  assumes "reachable x y" and "edge y z"
  shows "reachable x z"
  using assms by induct auto

lemma reachable_trans:
  assumes y: "reachable x y" and z: "reachable y z"
  shows "reachable x z"
  using assms by induct auto

text \<open>
  In order to derive a ``reverse'' induction rule for @{const "reachable"},
  we define an alternative reachability predicate and prove that the two
  coincide.
\<close>
inductive reachable_end where
  re_refl[iff]: "reachable_end x x"
| re_succ: "\<lbrakk>reachable_end x y; edge y z\<rbrakk> \<Longrightarrow> reachable_end x z"

lemma succ_re:
  assumes y: "edge x y" and z: "reachable_end y z"
  shows "reachable_end x z"
  using z y by (induction) (auto intro: re_succ)

lemma reachable_re:
  assumes "reachable x y"
  shows "reachable_end x y"
  using assms by (induction) (auto intro: succ_re)

lemma re_reachable:
  assumes "reachable_end x y"
  shows "reachable x y"
  using assms by (induction) (auto intro: succ_reachable)

lemma reachable_end_induct:
  assumes r: "reachable x y"
      and base: "\<And>x. P x x"
      and step: "\<And>x y z. \<lbrakk>P x y; edge y z\<rbrakk> \<Longrightarrow> P x z"
  shows "P x y"
using r[THEN reachable_re] proof (induction)
  case (re_refl x)
  from base show ?case .
next
  case (re_succ x y z)
  with step show ?case by blast
qed

text \<open>
  We also need the following variant of reachability avoiding
  certain edges. More precisely, @{text y} is reachable from @{text x}
  avoiding a set @{text E} of edges if there exists a path such that
  no edge from @{text E} appears along the path.
\<close>
inductive reachable_avoiding where
  ra_refl[iff]: "reachable_avoiding x x E"
| ra_succ[elim]: "\<lbrakk>reachable_avoiding x y E; edge y z; (y,z) \<notin> E\<rbrakk> \<Longrightarrow> reachable_avoiding x z E"

lemma edge_ra:
  assumes "edge x y" and "(x,y) \<notin> E"
  shows "reachable_avoiding x y E"
  using assms by (meson reachable_avoiding.simps)

lemma ra_trans:
  assumes 1: "reachable_avoiding x y E" and 2: "reachable_avoiding y z E"
  shows "reachable_avoiding x z E"
  using 2 1 by induction auto

lemma ra_cases:
  assumes "reachable_avoiding x y E"
  shows "x=y \<or> (\<exists>z. z \<in> successors x \<and> (x,z) \<notin> E \<and> reachable_avoiding z y E)"
using assms proof (induction)
  case (ra_refl x S)
  then show ?case by simp
next
  case (ra_succ x y S z)
  then show ?case
    by (metis ra_refl reachable_avoiding.ra_succ)
qed

lemma ra_mono: 
  assumes "reachable_avoiding x y E" and "E' \<subseteq> E"
  shows "reachable_avoiding x y E'"
using assms by induction auto

lemma ra_add_edge:
  assumes "reachable_avoiding x y E"
  shows "reachable_avoiding x y (E \<union> {(v,w)})
         \<or> (reachable_avoiding x v (E \<union> {(v,w)}) \<and> reachable_avoiding w y (E \<union> {(v,w)}))"
using assms proof (induction)
  case (ra_refl x E)
  then show ?case by simp
next
  case (ra_succ x y E z)
  then show ?case
    using reachable_avoiding.ra_succ by auto
qed


text \<open>
  Reachability avoiding some edges obviously implies reachability.
  Conversely, reachability implies reachability avoiding the empty set.
\<close>
lemma ra_reachable:
  "reachable_avoiding x y E \<Longrightarrow> reachable x y"
  by (induction rule: reachable_avoiding.induct) (auto intro: succ_reachable)

lemma ra_empty:
  "reachable_avoiding x y {} = reachable x y"
proof
  assume "reachable_avoiding x y {}"
  thus "reachable x y"
    by (rule ra_reachable)
next
  assume "reachable x y"
  hence "reachable_end x y"
    by (rule reachable_re)
  thus "reachable_avoiding x y {}"
    by induction auto
qed


section \<open>Strongly connected components\<close>

text \<open>
  A strongly connected component is a set @{text S} of nodes
  such that any two nodes in @{text S} are reachable from each other.
  This concept is represented by the predicate @{text "is_subscc"} below.
  We are ultimately interested in non-empty, maximal strongly connected
  components, represented by the predicate @{text "is_scc"}.
\<close>

definition is_subscc where
  "is_subscc S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. reachable x y"

definition is_scc where
  "is_scc S \<equiv> S \<noteq> {} \<and> is_subscc S \<and> (\<forall>S'. S \<subseteq> S' \<and> is_subscc S' \<longrightarrow> S' = S)"

lemma subscc_add:
  assumes "is_subscc S" and "x \<in> S"
      and "reachable x y" and "reachable y x"
  shows "is_subscc (insert y S)"
using assms unfolding is_subscc_def by (metis insert_iff reachable_trans)

lemma sccE:
  \<comment> \<open>Two nodes that are reachable from each other are in the same SCC.\<close>
  assumes "is_scc S" and "x \<in> S"
      and "reachable x y" and "reachable y x"
  shows "y \<in> S"
  using assms unfolding is_scc_def 
  by (metis insertI1 subscc_add subset_insertI)

lemma scc_partition:
  \<comment> \<open>Two SCCs that contain a common element are identical.\<close>
  assumes "is_scc S" and "is_scc S'" and "x \<in> S \<inter> S'"
  shows "S = S'"
  using assms unfolding is_scc_def is_subscc_def
  by (metis IntE assms(2) sccE subsetI)


section \<open>Algorithm for computing strongly connected components\<close>

text \<open>
  We now introduce our representation of Bloemen's algorithm in Isabelle/HOL.
  The auxiliary function @{text unite} corresponds to the inner \textsf{while}
  loop in Bloemen's pseudo-code~\<^cite>\<open>\<open>p.32\<close> in "bloemen:strong"\<close>. It is applied to
  two nodes @{text v} and @{text w} (and the environment @{text e} holding the
  current values of the program variables) when a loop is found, i.e.\ when
  @{text w} is a successor of @{text v} in the graph that has already been
  visited in the depth-first search. In that case, the root of the SCC
  of node @{text w} determined so far must appear below the root of
  @{text v}'s SCC in the @{text stack} maintained by the algorithm. 
  The effect of the function is to merge the SCCs of all nodes on the
  top of the stack above (and including) @{text w}. Node @{text w}'s root
  will be the root of the merged SCC.
\<close>

definition unite :: "'v \<Rightarrow> 'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "unite v w e \<equiv>
     let pfx = takeWhile (\<lambda>x. w \<notin> \<S> e x) (stack e);
         sfx = dropWhile (\<lambda>x. w \<notin> \<S> e x) (stack e);
         cc = \<Union> { \<S> e x | x . x \<in> set pfx \<union> {hd sfx} }
     in  e\<lparr>\<S> := \<lambda>x. if x \<in> cc then cc else \<S> e x,
           stack := sfx\<rparr>"

text \<open>
  We now represent the algorithm as two mutually recursive functions @{text dfs} and
  @{text dfss} in Isabelle/HOL. The function @{text dfs} corresponds to Bloemen's
  function \textsf{SetBased}, whereas @{text dfss} corresponds to the \textsf{forall}
  loop over the successors of the node on which @{text dfs} was called. Instead of
  using global program variables in imperative style, our functions explicitly pass
  environments that hold the current values of these variables.

  A technical complication in the development of the algorithm in Isabelle is the
  fact that the functions need not terminate when their pre-conditions (introduced
  below) are violated, for example when @{text dfs} is called for a node that was
  already visited previously. We therefore cannot prove termination at this point, 
  but will later show that the explicitly given pre-conditions ensure termination.
\<close>

function (domintros) dfs :: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" 
and dfss :: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "dfs v e =
  (let e1 = e\<lparr>visited := visited e \<union> {v}, 
              stack := (v # stack e), 
              cstack := (v # cstack e)\<rparr>;
       e' = dfss v e1
   in if v = hd(stack e')
      then e'\<lparr>sccs := sccs e' \<union> {\<S> e' v}, 
              explored := explored e' \<union> (\<S> e' v), 
              stack := tl(stack e'), 
              cstack := tl(cstack e')\<rparr>
      else e'\<lparr>cstack := tl(cstack e')\<rparr>)"
| "dfss v e =
   (let vs = successors v - vsuccs e v
    in  if vs = {} then e
        else let w = SOME x. x \<in> vs;
                 e' = (if w \<in> explored e then e
                       else if w \<notin> visited e
                       then dfs w e
                       else unite v w e);
                 e'' = (e'\<lparr>vsuccs := 
                             (\<lambda>x. if x=v then vsuccs e' v \<union> {w} 
                                  else vsuccs e' x)\<rparr>)
             in  dfss v e'')"
  by pat_completeness (force+)


section \<open>Definition of the predicates used in the correctness proof\<close>

text \<open>
  Environments are partially ordered according to the following definition.
\<close>
definition sub_env where
  "sub_env e e' \<equiv> 
     root e' = root e
   \<and> visited e \<subseteq> visited e'
   \<and> explored e \<subseteq> explored e'
   \<and> (\<forall>v. vsuccs e v \<subseteq> vsuccs e' v)
   \<and> (\<forall> v. \<S> e v \<subseteq> \<S> e' v)
   \<and> (\<Union> {\<S> e v | v . v \<in> set (stack e)})
     \<subseteq> (\<Union> {\<S> e' v | v . v \<in> set (stack e')})
"

lemma sub_env_trans:
  assumes "sub_env e e'" and "sub_env e' e''"
  shows "sub_env e e''"
  using assms unfolding sub_env_def
  by (metis (no_types, lifting) subset_trans)

text \<open>
  The set @{text "unvisited e u"} contains all edges @{text "(a,b)"}
  such that node @{text a} is in the same SCC as
  node @{text u} and the edge has not yet been followed, in the
  sense represented by variable @{text vsuccs}.
\<close>
definition unvisited where
  "unvisited e u \<equiv> 
   {(a,b) | a b. a \<in> \<S> e u \<and> b \<in> successors a - vsuccs e a}"

subsection \<open>Main invariant\<close>

text \<open>
  The following definition characterizes well-formed environments.
  This predicate will be shown to hold throughout the execution
  of the algorithm. In words, it asserts the following facts:
  \begin{itemize}
  \item Only nodes reachable from the root (for which the algorithm
    was originally called) are visited.
  \item The two stacks @{text stack} and @{text cstack} do not
    contain duplicate nodes, and @{text stack} contains a subset
    of the nodes on @{text cstack}, in the same order.
  \item Any node higher on the @{text stack} (i.e., that was pushed
    later) is reachable from nodes lower in the @{text stack}.
    This property also holds for nodes on the call stack,
    but this is not needed for the correctness proof.
  \item Every explored node, and every node on the call stack,
    has been visited.
  \item Nodes reachable from fully explored nodes have 
    themselves been fully explored.
  \item The set @{text "vsuccs e n"}, for any node @{text n},
    is a subset of @{text n}'s successors, and all these nodes
    are in @{text visited}. The set is empty if @{text "n \<notin> visited"},
    and it contains all successors if @{text n} has been fully 
    explored or if @{text n} has been visited, but is no longer
    on the call stack.
  \item The sets @{text "\<S> e n"} represent an equivalence relation.
    The equivalence classes of nodes that have not yet been visited 
    are singletons. Also, equivalence classes for two distinct nodes
    on the @{text stack} are disjoint because the stack only stores
    roots of SCCs, and the union of the equivalence classes for these
    root nodes corresponds to the set of live nodes, i.e. those nodes
    that have already been visited but not yet fully explored.
  \item More precisely, an equivalence class is represented on the
    stack by the oldest node in the sense of the call order: any
    node in the class that is still on the call stack precedes the
    representative on the call stack and was therefore pushed later.
  \item Equivalence classes represent the maximal available
    information about strong connectedness: nodes represented by
    some node @{text n} on the @{text stack} can reach some node
    @{text m} that is lower in the stack only by taking an
    edge from some node in @{text n}'s equivalence class that 
    has not yet been followed. (Remember that @{text m} can reach
    @{text n} by one of the previous conjuncts.)
  \item Equivalence classes represent partial SCCs in the sense
    of the predicate @{text is_subscc}. Variable @{text sccs}
    holds maximal SCCs in the sense of the predicate @{text is_scc},
    and their union corresponds to the set of explored nodes.
  \end{itemize}
\<close>
definition wf_env where
  "wf_env e \<equiv>
    (\<forall>n \<in> visited e. reachable (root e) n)
  \<and> distinct (stack e)
  \<and> distinct (cstack e)
  \<and> (\<forall>n m. n \<preceq> m in stack e \<longrightarrow> n \<preceq> m in cstack e)
  \<and> (\<forall>n m. n \<preceq> m in stack e \<longrightarrow> reachable m n)
  \<and> explored e \<subseteq> visited e
  \<and> set (cstack e) \<subseteq> visited e
  \<and> (\<forall>n \<in> explored e. \<forall>m. reachable n m \<longrightarrow> m \<in> explored e)  
  \<and> (\<forall>n. vsuccs e n \<subseteq> successors n \<inter> visited e)
  \<and> (\<forall>n. n \<notin> visited e \<longrightarrow> vsuccs e n = {})
  \<and> (\<forall>n \<in> explored e. vsuccs e n = successors n)
  \<and> (\<forall>n \<in> visited e - set (cstack e). vsuccs e n = successors n)
  \<and> (\<forall>n m. m \<in> \<S> e n \<longleftrightarrow> (\<S> e n = \<S> e m))
  \<and> (\<forall>n. n \<notin> visited e \<longrightarrow> \<S> e n = {n})
  \<and> (\<forall>n \<in> set (stack e). \<forall>m \<in> set (stack e). n \<noteq> m \<longrightarrow> \<S> e n \<inter> \<S> e m = {})
  \<and> \<Union> {\<S> e n | n. n \<in> set (stack e)} = visited e - explored e
  \<and> (\<forall>n \<in> set (stack e). \<forall>m \<in> \<S> e n. m \<in> set (cstack e) \<longrightarrow> m \<preceq> n in cstack e)
  \<and> (\<forall>n m. n \<preceq> m in stack e \<and> n \<noteq> m \<longrightarrow>
        (\<forall>u \<in> \<S> e n. \<not> reachable_avoiding u m (unvisited e n)))
  \<and> (\<forall>n. is_subscc (\<S> e n))
  \<and> (\<forall>S \<in> sccs e. is_scc S)
  \<and> \<Union> (sccs e) = explored e"

subsection \<open>Consequences of the invariant\<close>

text \<open>
  Since every node on the call stack is an element
  of @{text visited} and every node on the @{text stack}
  also appears on @{text cstack}, all these nodes are
  also in @{text visited}.
\<close>
lemma stack_visited:
  assumes "wf_env e" "n \<in> set (stack e)"
  shows "n \<in> visited e"
  using assms unfolding wf_env_def
  by (meson precedes_refl subset_iff)

text \<open>
  Classes represented on the stack consist of visited nodes
  that have not yet been fully explored.
\<close>
lemma stack_class:
  assumes "wf_env e" "n \<in> set (stack e)" "m \<in> \<S> e n"
  shows "m \<in> visited e - explored e"
  using assms unfolding wf_env_def by blast

text \<open>
  Conversely, every such node belongs to some class
  represented on the stack.
\<close>
lemma visited_unexplored:
  assumes "wf_env e" "m \<in> visited e" "m \<notin> explored e"
  obtains n where "n \<in> set (stack e)" "m \<in> \<S> e n"
  using assms unfolding wf_env_def
  by (smt (verit, ccfv_threshold) Diff_iff Union_iff mem_Collect_eq)

text \<open>
  Every node belongs to its own equivalence class.
\<close>
lemma S_reflexive:
  assumes "wf_env e"
  shows "n \<in> \<S> e n"
  using assms by (auto simp: wf_env_def)

text \<open>
  No node on the stack has been fully explored.
\<close>
lemma stack_unexplored:
  assumes 1: "wf_env e"
      and 2: "n \<in> set (stack e)"
      and 3: "n \<in> explored e"
  shows "P"
  using stack_class[OF 1 2] S_reflexive[OF 1] 3
  by blast

text \<open>
  If @{text w} is reachable from visited node @{text v}, but
  no unvisited successor of a node reachable from @{text v}
  can reach @{text w}, then @{text w} must be visited.
\<close>
lemma reachable_visited:
  assumes e: "wf_env e"
      and v: "v \<in> visited e"
      and w: "reachable v w"
      and s: "\<forall>n \<in> visited e. \<forall>m \<in> successors n - vsuccs e n. 
                 reachable v n \<longrightarrow> \<not> reachable m w"
  shows "w \<in> visited e"
using w v s proof (induction)
  case (reachable_refl x)
  then show ?case by simp
next
  case (reachable_succ x y z)
  then have "y \<in> vsuccs e x" by blast
  with e have "y \<in> visited e" 
    unfolding wf_env_def by (meson le_infE subset_eq)
  with reachable_succ reachable.reachable_succ show ?case
    by blast
qed

text \<open>
  Edges towards explored nodes do not contribute to reachability
  of unexplored nodes avoiding some set of edges.
\<close>
lemma avoiding_explored:
  assumes e: "wf_env e"
      and xy: "reachable_avoiding x y E"
      and y: "y \<notin> explored e"
      and w: "w \<in> explored e"
    shows "reachable_avoiding x y (E \<union> {(v,w)})"
using xy y proof (induction)
  case (ra_refl x E)
  then show ?case by simp
next
  case (ra_succ x y E z)
  from e \<open>z \<in> successors y\<close> \<open>z \<notin> explored e\<close>
  have "y \<notin> explored e"
    unfolding wf_env_def by (meson reachable_edge)
  with ra_succ.IH have "reachable_avoiding x y (E \<union> {(v,w)})" .
  moreover
  from w \<open>(y,z) \<notin> E\<close> \<open>z \<notin> explored e\<close> have "(y,z) \<notin> E \<union> {(v,w)}"
    by auto
  ultimately show ?case 
    using  \<open>z \<in> successors y\<close> by auto
qed

subsection \<open>Pre- and post-conditions of function @{text dfs}\<close>

text \<open>
  Function @{text dfs} should be called for a well-formed
  environment and a node @{text v} that has not yet been
  visited and that is reachable from the root node, 
  as well as from all nodes in the stack. No outgoing edges
  from node @{text v} have yet been followed.
\<close>

definition pre_dfs where 
  "pre_dfs v e \<equiv> 
     wf_env e
   \<and> v \<notin> visited e
   \<and> reachable (root e) v
   \<and> vsuccs e v = {}
   \<and> (\<forall>n \<in> set (stack e). reachable n v)"

text \<open>
  Function @{text dfs} maintains the invariant
  @{text wf_env} and returns an environment @{text e'} that
  extends the input environment @{text e}. Node @{text v} has been 
  visited and all its outgoing edges have been followed.
  Because the algorithm works in depth-first fashion, no 
  new outgoing edges of nodes that had already been
  visited in the input environment have been followed, and
  the stack of @{text e'} is a suffix of the one of @{text e}
  such that @{text v} is still reachable from all nodes on the
  stack. The stack may have been shortened because SCCs
  represented at the top of the stack may have been
  merged. The call stack is reestablished as it was in @{text e}.
  There are two possible outcomes of the algorithm:
  \begin{itemize}
  \item Either @{text v} has been fully explored, in which case
    the stacks of @{text e} and @{text e'} are the same, and
    the equivalence classes of all nodes represented on the
    stack are unchanged. This corresponds to the case where
    @{text v} is the root node of its (maximal) SCC.
  \item Alternatively, the stack of @{text e'} must be
    non-empty and @{text v} must be represented by the node at
    the top of the stack. The SCCs of the nodes
    lower on the stack are unchanged. This corresponds to the
    case where @{text v} is not the root node of its SCC, but
    some SCCs at the top of the stack may have been merged.
  \end{itemize}
\<close>
definition post_dfs where 
  "post_dfs v e e' \<equiv> 
     wf_env e'
   \<and> v \<in> visited e'
   \<and> sub_env e e'
   \<and> vsuccs e' v = successors v
   \<and> (\<forall>w \<in> visited e. vsuccs e' w = vsuccs e w)
   \<and> (\<forall>n \<in> set (stack e'). reachable n v)
   \<and> (\<exists>ns. stack e = ns @ (stack e'))
   \<and> (  (v \<in> explored e' \<and> stack e' = stack e 
         \<and> (\<forall>n \<in> set (stack e'). \<S> e' n = \<S> e n)) 
     \<or> (stack e' \<noteq> [] \<and> v \<in> \<S> e' (hd (stack e')) 
         \<and> (\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n)))
   \<and> cstack e' = cstack e"

text \<open>
  The initial environment is easily seen to satisfy @{text dfs}'s
  pre-condition.
\<close>
lemma init_env_pre_dfs: "pre_dfs v (init_env v)"
  by (auto simp: pre_dfs_def wf_env_def init_env_def is_subscc_def 
           dest: precedes_mem)

text \<open>
  Any node represented by the top stack element of the
  input environment is still represented by the top
  element of the output stack.
\<close>
lemma dfs_S_hd_stack:
  assumes wf: "wf_env e"
      and post: "post_dfs v e e'"
      and n: "stack e \<noteq> []" "n \<in> \<S> e (hd (stack e))"
    shows "stack e' \<noteq> []" "n \<in> \<S> e' (hd (stack e'))"
proof -
  have 1: "stack e' \<noteq> [] \<and> n \<in> \<S> e' (hd (stack e'))"
  proof (cases "stack e' = stack e \<and> (\<forall>n \<in> set (stack e'). \<S> e' n = \<S> e n)")
    case True
    with n show ?thesis 
      by auto
  next
    case 2: False
    with post have "stack e' \<noteq> []"
      by (simp add: post_dfs_def)
    from n have "hd (stack e) \<in> set (stack e)"
      by simp
    with 2 n post obtain u where
      u: "u \<in> set (stack e')" "n \<in> \<S> e' u"
      unfolding post_dfs_def sub_env_def by blast
    show ?thesis
    proof (cases "u = hd (stack e')")
      case True
      with u \<open>stack e' \<noteq> []\<close> show ?thesis
        by simp
    next
      case False
      with u have "u \<in> set (tl (stack e'))"
        by (metis empty_set equals0D list.collapse set_ConsD)
      with u 2 post have "u \<in> set (tl (stack e)) \<and> n \<in> \<S> e u"
        unfolding post_dfs_def
        by (metis Un_iff append_self_conv2 set_append tl_append2)
      with n wf \<open>hd (stack e) \<in> set (stack e)\<close> show ?thesis
        unfolding wf_env_def
        by (metis (no_types, opaque_lifting) disjoint_iff_not_equal distinct.simps(2) list.collapse list.set_sel(2))
    qed
  qed
  from 1 show "stack e' \<noteq> []" by simp
  from 1 show "n \<in> \<S> e' (hd (stack e'))" by simp
qed

text \<open>
  Function @{text dfs} leaves the SCCs represented
  by elements in the (new) tail of the @{text stack} unchanged.
\<close>
lemma dfs_S_tl_stack:
  assumes post: "post_dfs v e e'"
    and nempty: "stack e \<noteq> []"
  shows "stack e' \<noteq> []" "\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n"
proof -
  have 1: "stack e' \<noteq> [] \<and> (\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n)"
  proof (cases "stack e' = stack e \<and> (\<forall>n \<in> set (stack e'). \<S> e' n = \<S> e n)")
    case True
    with nempty show ?thesis
      by (simp add: list.set_sel(2))
  next
    case False
    with post show ?thesis
      by (auto simp: post_dfs_def)
  qed
  from 1 show "stack e' \<noteq> []"
    by simp
  from 1 show "\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n"
    by simp
qed

subsection \<open>Pre- and post-conditions of function @{text dfss}\<close>

text \<open>
  The pre- and post-conditions of function @{text dfss}
  correspond to the invariant of the loop over all outgoing
  edges from node @{text v}. The environment must be
  well-formed, node @{text v} must be visited and represented
  by the top element of the (non-empty) stack. Node @{text v}
  must be reachable from all nodes on the stack, and it must be
  the top node on the call stack. All outgoing
  edges of node @{text v} that have already been followed must
  either lead to completely explored nodes (that are no longer
  represented on the stack) or to nodes that are part of the
  same SCC as @{text v}.
\<close>
definition pre_dfss where 
  "pre_dfss v e \<equiv> 
     wf_env e 
   \<and> v \<in> visited e
   \<and> (stack e \<noteq> [])
   \<and> (v \<in> \<S> e (hd (stack e)))
   \<and> (\<forall>w \<in> vsuccs e v. w \<in> explored e \<union> \<S> e (hd (stack e)))
   \<and> (\<forall>n \<in> set (stack e). reachable n v)
   \<and> (\<exists>ns. cstack e = v # ns)"

text \<open>
  The post-condition establishes that all outgoing edges
  of node @{text v} have been followed. As for function
  @{text dfs}, no new outgoing edges of previously visited
  nodes have been followed. Also as before, the new stack
  is a suffix of the old one, and the call stack is restored.
  In case node @{text v} is still on the stack (and therefore
  is the root node of its SCC), no node that is lower on the stack
  can be reachable from @{text v}. This condition guarantees
  the maximality of the computed SCCs.
\<close>
definition post_dfss where 
  "post_dfss v e e' \<equiv> 
     wf_env e'
   \<and> vsuccs e' v = successors v
   \<and> (\<forall>w \<in> visited e - {v}. vsuccs e' w = vsuccs e w)
   \<and> sub_env e e'
   \<and> (\<forall>w \<in> successors v. w \<in> explored e' \<union> \<S> e' (hd (stack e')))
   \<and> (\<forall>n \<in> set (stack e'). reachable n v)
   \<and> (stack e' \<noteq> [])
   \<and> (\<exists>ns. stack e = ns @ (stack e'))
   \<and> v \<in> \<S> e' (hd (stack e'))
   \<and> (\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n)
   \<and> (hd (stack e') = v \<longrightarrow> (\<forall>n \<in> set (tl (stack e')). \<not> reachable v n))
   \<and> cstack e' = cstack e"


section \<open>Proof of partial correctness\<close>

subsection \<open>Lemmas about function @{text unite}\<close>

text \<open>
  We start by establishing a few lemmas about function @{text unite}
  in the context where it is called.
\<close>
lemma unite_stack:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  assumes wf: "wf_env e"
      and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
  obtains pfx where "stack e = pfx @ (stack e')" 
                    "stack e' \<noteq> []"
                    "let cc = \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}
                     in \<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
                    "w \<in> \<S> e' (hd (stack e'))"
proof -
  define pfx where "pfx = takeWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
  define sfx where "sfx = dropWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
  define cc where "cc = \<Union> {\<S> e x |x. x \<in> set pfx \<union> {hd sfx}}"

  have "stack e = pfx @ sfx"
    by (simp add: pfx_def sfx_def)
  moreover
  have "stack e' = sfx"
    by (simp add: e'_def unite_def sfx_def)
  moreover
  from wf w have "w \<in> \<Union> {\<S> e n | n. n \<in> set (stack e)}"
    by (simp add: wf_env_def)
  then obtain n where "n \<in> set (stack e)" "w \<in> \<S> e n"
    by auto
  hence sfx: "sfx \<noteq> [] \<and> w \<in> \<S> e (hd sfx)"
    unfolding sfx_def
    by (metis dropWhile_eq_Nil_conv hd_dropWhile)
  moreover
  have "\<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
    by (rule,
        auto simp add: e'_def unite_def pfx_def sfx_def cc_def)
  moreover
  from sfx have "w \<in> cc"
    by (auto simp: cc_def)
  from S_reflexive[OF wf, of "hd sfx"]
  have "hd sfx \<in> cc"
    by (auto simp: cc_def)
  with \<open>w \<in> cc\<close> \<open>\<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)\<close>
  have "w \<in> \<S> e' (hd sfx)"
    by simp
  ultimately show ?thesis
    using that e'_def unite_def pfx_def sfx_def cc_def
    by meson
qed

text \<open>
  Function @{text unite} leaves intact the equivalence classes
  represented by the tail of the new stack.
\<close>
lemma unite_S_tl:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  assumes wf: "wf_env e"
      and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
      and n: "n \<in> set (tl (stack e'))"
  shows "\<S> e' n = \<S> e n"
proof -
  from assms obtain pfx where
    pfx: "stack e = pfx @ (stack e')" "stack e' \<noteq> []"
         "let cc = \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}
          in \<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
    by (blast dest: unite_stack)
  define cc where "cc \<equiv> \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}"

  have "n \<notin> cc"
  proof
    assume "n \<in> cc"
    then obtain m where
      "m \<in> set pfx \<union> {hd (stack e')}" "n \<in> \<S> e m"
      by (auto simp: cc_def)
    with S_reflexive[OF wf, of n] n wf \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
    show "False"
      unfolding wf_env_def
      by (smt (z3) Diff_triv Un_iff Un_insert_right append.right_neutral disjoint_insert(1) 
                   distinct.simps(2) distinct_append empty_set insertE insert_Diff list.exhaust_sel 
                   list.simps(15) set_append)
  qed
  with pfx show "\<S> e' n = \<S> e n"
    by (auto simp add: cc_def)
qed

text \<open>
  The stack of the result of @{text unite} represents the
  same vertices as the input stack, potentially in fewer
  equivalence classes.
\<close>
lemma unite_S_equal:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  assumes wf: "wf_env e"
      and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
  shows "(\<Union> {\<S> e' n | n. n \<in> set (stack e')}) = (\<Union> {\<S> e n | n. n \<in> set (stack e)})"
proof -
  from assms obtain pfx where
    pfx: "stack e = pfx @ (stack e')" "stack e' \<noteq> []"
         "let cc = \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}
          in \<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
    by (blast dest: unite_stack)
  define cc where "cc \<equiv> \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}"

  from pfx have Se': "\<forall>x. \<S> e' x = (if x \<in> cc then cc else \<S> e x)"
    by (auto simp: cc_def)
  from S_reflexive[OF wf, of "hd (stack e')"]
  have S_hd: "\<S> e' (hd (stack e')) = cc"
    by (auto simp: Se' cc_def)
  from \<open>stack e' \<noteq> []\<close>
  have ste': "set (stack e') = {hd (stack e')} \<union> set (tl (stack e'))"
    by (metis insert_is_Un list.exhaust_sel list.simps(15))

  from \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
  have "stack e = pfx @ (hd (stack e') # tl (stack e'))"
    by auto
  hence "\<Union> {\<S> e n | n. n \<in> set (stack e)}
        = cc \<union> (\<Union> {\<S> e n | n. n \<in> set (tl (stack e'))})"
    by (auto simp add: cc_def)
  also from S_hd unite_S_tl[OF wf w]
  have "\<dots> = \<S> e' (hd (stack e')) \<union> (\<Union> {\<S> e' n | n. n \<in> set (tl (stack e'))})"
    by (auto simp: e'_def)
  also from ste'
  have "\<dots> = \<Union> {\<S> e' n | n. n \<in> set (stack e')}"
    by auto
  finally show ?thesis
    by simp
qed

text \<open>
  The head of the stack represents a (not necessarily maximal) SCC.
\<close>
lemma unite_subscc:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  assumes pre: "pre_dfss v e"
      and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
    shows "is_subscc (\<S> e' (hd (stack e')))"
proof -
  from pre have wf: "wf_env e"
    by (simp add: pre_dfss_def)
  from assms obtain pfx where
    pfx: "stack e = pfx @ (stack e')" "stack e' \<noteq> []"
         "let cc = \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}
          in \<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
    by (blast dest: unite_stack[OF wf])

  define cc where "cc \<equiv> \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}"

  from wf w have "w \<in> \<Union> {\<S> e n | n. n \<in> set (stack e)}"
    by (simp add: wf_env_def)
  hence "w \<in> \<S> e (hd (stack e'))"
    apply (simp add: e'_def unite_def)
    by (metis dropWhile_eq_Nil_conv hd_dropWhile)

  have "is_subscc cc"
  proof (clarsimp simp: is_subscc_def)
    fix x y
    assume "x \<in> cc" "y \<in> cc"
    then obtain nx ny where
      nx: "nx \<in> set pfx \<union> {hd (stack e')}" "x \<in> \<S> e nx" and
      ny: "ny \<in> set pfx \<union> {hd (stack e')}" "y \<in> \<S> e ny"
      by (auto simp: cc_def)
    with wf have "reachable x nx" "reachable ny y"
      by (auto simp: wf_env_def is_subscc_def)
    from w pre have "reachable v w"
      by (auto simp: pre_dfss_def)
    from pre have "reachable (hd (stack e)) v"
      by (auto simp: pre_dfss_def wf_env_def is_subscc_def)
    from pre have "stack e = hd (stack e) # tl (stack e)"
      by (auto simp: pre_dfss_def)
    with nx \<open>stack e = pfx @ (stack e')\<close> \<open>stack e' \<noteq> []\<close>
    have "hd (stack e) \<preceq> nx in stack e"
      by (metis Un_iff Un_insert_right head_precedes list.exhaust_sel list.simps(15) 
                set_append sup_bot.right_neutral)
    with wf have "reachable nx (hd (stack e))"
      by (auto simp: wf_env_def)
    from \<open>stack e = pfx @ (stack e')\<close> \<open>stack e' \<noteq> []\<close> ny
    have "ny \<preceq> hd (stack e') in stack e" 
      by (metis List.set_insert empty_set insert_Nil list.exhaust_sel set_append split_list_precedes)
    with wf have "reachable (hd (stack e')) ny"
      by (auto simp: wf_env_def is_subscc_def)
    from wf \<open>stack e' \<noteq> []\<close> \<open>w \<in> \<S> e (hd (stack e'))\<close>
    have "reachable w (hd (stack e'))"
      by (auto simp: wf_env_def is_subscc_def)

    from \<open>reachable x nx\<close> \<open>reachable nx (hd (stack e))\<close>
         \<open>reachable (hd (stack e)) v\<close> \<open>reachable v w\<close>
         \<open>reachable w (hd (stack e'))\<close> 
         \<open>reachable (hd (stack e')) ny\<close> \<open>reachable ny y\<close>
    show "reachable x y"
      using reachable_trans by meson
  qed
  with S_reflexive[OF wf, of "hd (stack e')"] pfx
  show ?thesis
    by (auto simp: cc_def)
qed

text \<open>
  The environment returned by function @{text unite} extends the input environment.
\<close>

lemma unite_sub_env:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  assumes pre: "pre_dfss v e"
        and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
  shows "sub_env e e'"
proof -
  from pre have wf: "wf_env e"
    by (simp add: pre_dfss_def)
  from assms obtain pfx where
    pfx: "stack e = pfx @ (stack e')" "stack e' \<noteq> []"
         "let cc = \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}
          in \<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
    by (blast dest: unite_stack[OF wf])
  define cc where "cc \<equiv> \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}"
  have "\<forall>n. \<S> e n \<subseteq> \<S> e' n"
  proof (clarify)
    fix n u
    assume u: "u \<in> \<S> e n"
    show "u \<in> \<S> e' n"
    proof (cases "n \<in> cc")
      case True
      then obtain m where
        m: "m \<in> set pfx \<union> {hd (stack e')}" "n \<in> \<S> e m"
        by (auto simp: cc_def)
      with wf S_reflexive[OF wf, of n] u have "u \<in> \<S> e m"
        by (auto simp: wf_env_def)
      with m pfx show ?thesis 
        by (auto simp: cc_def)
    next
      case False
      with pfx u show ?thesis
        by (auto simp: cc_def)
    qed
  qed
  moreover
  have "root e' = root e \<and> visited e' = visited e
      \<and> explored e' = explored e \<and> vsuccs e' = vsuccs e"
    by (simp add: e'_def unite_def)
  ultimately show ?thesis
    using unite_S_equal[OF wf w]
    by (simp add: e'_def sub_env_def)
qed

text \<open>
  The environment returned by function @{text unite} is well-formed.
\<close>
lemma unite_wf_env:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  assumes pre: "pre_dfss v e"
      and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
  shows "wf_env e'"
proof -
  from pre have wf: "wf_env e"
    by (simp add: pre_dfss_def)
  from assms obtain pfx where
    pfx: "stack e = pfx @ (stack e')" "stack e' \<noteq> []"
         "let cc = \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}
          in \<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
    by (blast dest: unite_stack[OF wf])
  define cc where "cc \<equiv> \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}"

  from pfx have Se': "\<forall>x. \<S> e' x = (if x \<in> cc then cc else \<S> e x)"
    by (auto simp add: cc_def)

  have cc_Un: "cc = \<Union> {\<S> e x | x. x \<in> cc}"
  proof
    from S_reflexive[OF wf]
    show "cc \<subseteq> \<Union> {\<S> e x | x. x \<in> cc}"
      by (auto simp: cc_def)
  next
    {
      fix n x
      assume "x \<in> cc" "n \<in> \<S> e x"
      with wf have "n \<in> cc"
        unfolding wf_env_def cc_def
        by (smt (verit) Union_iff mem_Collect_eq)
    }
    thus "(\<Union> {\<S> e x | x. x \<in> cc}) \<subseteq> cc"
      by blast
  qed

  from S_reflexive[OF wf, of "hd (stack e')"]
  have hd_cc: "\<S> e' (hd (stack e')) = cc"
    by (auto simp: cc_def Se')

  {
    fix n m
    assume n: "n \<in> set (tl (stack e'))"
       and m: "m \<in> \<S> e n \<inter> cc"
    from m obtain l where
      "l \<in> set pfx \<union> {hd (stack e')}" "m \<in> \<S> e l"
      by (auto simp: cc_def)
    with n m wf \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
    have "False"
      unfolding wf_env_def
      by (metis (no_types, lifting) Int_iff UnCI UnE disjoint_insert(1) distinct.simps(2) 
                distinct_append emptyE hd_Cons_tl insert_iff list.set_sel(1) list.set_sel(2) 
                mk_disjoint_insert set_append)
  }
  hence tl_cc: "\<forall>n \<in> set (tl (stack e')). \<S> e n \<inter> cc = {}"
    by blast

  from wf 
  have "\<forall>n \<in> visited e'. reachable (root e') n"
       "distinct (cstack e')"
       "explored e' \<subseteq> visited e'"
       "set (cstack e') \<subseteq> visited e'"
       "\<forall>n \<in> explored e'. \<forall>m. reachable n m \<longrightarrow> m \<in> explored e'"
       "\<forall>n. vsuccs e' n \<subseteq> successors n \<inter> visited e'"
       "\<forall>n. n \<notin> visited e' \<longrightarrow> vsuccs e' n = {}"
       "\<forall>n \<in> explored e'. vsuccs e' n = successors n"
       "\<forall>n \<in> visited e' - set (cstack e'). vsuccs e' n = successors n"
       "\<forall>S \<in> sccs e'. is_scc S"
       "\<Union> (sccs e') = explored e'"
    by (auto simp: wf_env_def e'_def unite_def)

  moreover
  from wf \<open>stack e = pfx @ stack e'\<close>
  have "distinct (stack e')"
    by (auto simp: wf_env_def)

  moreover
  have "\<forall>n m. n \<preceq> m in stack e' \<longrightarrow> n \<preceq> m in cstack e'"
  proof (clarify)
    fix n m
    assume "n \<preceq> m in stack e'"
    with \<open>stack e = pfx @ stack e'\<close> wf
    have "n \<preceq> m in cstack e"
      unfolding wf_env_def
      by (metis precedes_append_left)
    thus "n \<preceq> m in cstack e'"
      by (simp add: e'_def unite_def)
  qed

  moreover
  from wf \<open>stack e = pfx @ stack e'\<close>
  have "\<forall>n m. n \<preceq> m in stack e' \<longrightarrow> reachable m n"
    unfolding wf_env_def by (metis precedes_append_left)

  moreover
  have "\<forall>n m. m \<in> \<S> e' n \<longleftrightarrow> (\<S> e' n = \<S> e' m)"
  proof (clarify)
    fix n m
    show "m \<in> \<S> e' n \<longleftrightarrow> (\<S> e' n = \<S> e' m)"
    proof
      assume l: "m \<in> \<S> e' n"
      show "\<S> e' n = \<S> e' m"
      proof (cases "n \<in> cc")
        case True
        with l show ?thesis
          by (simp add: Se')
      next
        case False
        with l wf have "\<S> e n = \<S> e m"
          by (simp add: wf_env_def Se')
        with False cc_Un wf have "m \<notin> cc"
          unfolding wf_env_def e'_def
          by (smt (verit, best) Union_iff mem_Collect_eq)
        with \<open>\<S> e n = \<S> e m\<close> False show ?thesis
          by (simp add: Se')
      qed
    next
      assume r: "\<S> e' n = \<S> e' m"
      show "m \<in> \<S> e' n"
      proof (cases "n \<in> cc")
        case True
        with r pfx have "\<S> e' m = cc"
          by (auto simp: cc_def)
        have "m \<in> cc"
        proof (rule ccontr)
          assume "m \<notin> cc"
          with pfx have "\<S> e' m = \<S> e m"
            by (auto simp: cc_def)
          with S_reflexive[OF wf, of m] \<open>\<S> e' m = cc\<close> \<open>m \<notin> cc\<close>
          show "False"
            by simp
        qed
        with pfx True show "m \<in> \<S> e' n"
          by (auto simp: cc_def)
      next
        case False
        hence "\<S> e' n = \<S> e n"
          by (simp add: Se')
        have "m \<notin> cc"
        proof
          assume m: "m \<in> cc"
          with \<open>\<S> e' n = \<S> e n\<close> r have "\<S> e n = cc"
            by (simp add: Se')
          with S_reflexive[OF wf, of n] have "n \<in> cc"
            by simp
          with \<open>n \<notin> cc\<close> show "False" ..
        qed
        with r \<open>\<S> e' n = \<S> e n\<close> have "\<S> e m = \<S> e n"
          by (simp add: Se')
        with S_reflexive[OF wf, of m] have "m \<in> \<S> e n"
          by simp
        with \<open>\<S> e' n = \<S> e n\<close> show ?thesis
          by simp
      qed
    qed
  qed

  moreover
  have "\<forall>n. n \<notin> visited e' \<longrightarrow> \<S> e' n = {n}"
  proof (clarify)
    fix n
    assume "n \<notin> visited e'"
    hence "n \<notin> visited e"
      by (simp add: e'_def unite_def)
    moreover have "n \<notin> cc"
    proof
      assume "n \<in> cc"
      then obtain m where "m \<in> set pfx \<union> {hd (stack e')}" "n \<in> \<S> e m"
        by (auto simp: cc_def)
      with \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
      have "m \<in> set (stack e)"
        by auto
      with stack_class[OF wf this \<open>n \<in> \<S> e m\<close>] \<open>n \<notin> visited e\<close>
      show "False"
        by simp
    qed
    ultimately show "\<S> e' n = {n}"
      using wf by (auto simp: wf_env_def Se')
  qed

  moreover
  have "\<forall>n \<in> set (stack e'). \<forall>m \<in> set (stack e'). n \<noteq> m \<longrightarrow> \<S> e' n \<inter> \<S> e' m = {}"
  proof (clarify)
    fix n m
    assume "n \<in> set (stack e')" "m \<in> set (stack e')" "n \<noteq> m"
    show "\<S> e' n \<inter> \<S> e' m = {}"
    proof (cases "n = hd (stack e')")
      case True
      with \<open>m \<in> set (stack e')\<close> \<open>n \<noteq> m\<close> \<open>stack e' \<noteq> []\<close>
      have "m \<in> set (tl (stack e'))"
        by (metis hd_Cons_tl set_ConsD)
      with True hd_cc tl_cc unite_S_tl[OF wf w]
      show ?thesis
        by (auto simp: e'_def)
    next
      case False
      with \<open>n \<in> set (stack e')\<close> \<open>stack e' \<noteq> []\<close>
      have "n \<in> set (tl (stack e'))"
        by (metis hd_Cons_tl set_ConsD)
      show ?thesis
      proof (cases "m = hd (stack e')")
        case True
        with \<open>n \<in> set (tl (stack e'))\<close> hd_cc tl_cc unite_S_tl[OF wf w]
        show ?thesis
          by (auto simp: e'_def)
      next
        case False
        with \<open>m \<in> set (stack e')\<close> \<open>stack e' \<noteq> []\<close>
        have "m \<in> set (tl (stack e'))"
          by (metis hd_Cons_tl set_ConsD)
        with \<open>n \<in> set (tl (stack e'))\<close>
        have "\<S> e' m = \<S> e m \<and> \<S> e' n = \<S> e n"
          by (auto simp: e'_def unite_S_tl[OF wf w])
        moreover
        from \<open>m \<in> set (stack e')\<close> \<open>n \<in> set (stack e')\<close> \<open>stack e = pfx @ stack e'\<close>
        have "m \<in> set (stack e) \<and> n \<in> set (stack e)"
          by auto
        ultimately show ?thesis
          using wf \<open>n \<noteq> m\<close> by (auto simp: wf_env_def)
      qed
    qed
  qed

  moreover
  {
    from unite_S_equal[OF wf w]
    have "\<Union> {\<S> e' n | n. n \<in> set (stack e')} = \<Union> {\<S> e n | n. n \<in> set (stack e)}"
      by (simp add: e'_def)
    with wf
    have "\<Union> {\<S> e' n | n. n \<in> set (stack e')} = visited e - explored e"
      by (simp add: wf_env_def)
  }
  hence "\<Union> {\<S> e' n | n. n \<in> set (stack e')} = visited e' - explored e'"
    by (simp add: e'_def unite_def)

  moreover
  have "\<forall>n \<in> set (stack e'). \<forall>m \<in> \<S> e' n. 
           m \<in> set (cstack e') \<longrightarrow> m \<preceq> n in cstack e'"
  proof (clarify)
    fix n m
    assume "n \<in> set (stack e')" "m \<in> \<S> e' n" "m \<in> set (cstack e')"
    from \<open>m \<in> set (cstack e')\<close> have "m \<in> set (cstack e)"
      by (simp add: e'_def unite_def)
    have "m \<preceq> n in cstack e"
    proof (cases "n = hd (stack e')")
      case True
      with \<open>m \<in> \<S> e' n\<close> have "m \<in> cc"
        by (simp add: hd_cc)
      then obtain l where 
        "l \<in> set pfx \<union> {hd (stack e')}" "m \<in> \<S> e l"
        by (auto simp: cc_def)
      with \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
      have "l \<in> set (stack e)"
        by auto
      with \<open>m \<in> \<S> e l\<close> \<open>m \<in> set (cstack e)\<close> wf
      have "m \<preceq> l in cstack e"
        by (auto simp: wf_env_def)
      moreover
      from \<open>l \<in> set pfx \<union> {hd (stack e')}\<close> True 
           \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
      have "l \<preceq> n in stack e"
        by (metis List.set_insert empty_set hd_Cons_tl insert_Nil set_append split_list_precedes)
      with wf have "l \<preceq> n in cstack e"
        by (auto simp: wf_env_def)
      ultimately show ?thesis
        using wf unfolding wf_env_def
        by (meson precedes_trans)
    next
      case False
      with \<open>n \<in> set (stack e')\<close> \<open>stack e' \<noteq> []\<close>
      have "n \<in> set (tl (stack e'))"
        by (metis list.collapse set_ConsD)
      with unite_S_tl[OF wf w] \<open>m \<in> \<S> e' n\<close>
      have "m \<in> \<S> e n"
        by (simp add: e'_def)
      with \<open>n \<in> set (stack e')\<close> \<open>stack e = pfx @ stack e'\<close>
           \<open>m \<in> set (cstack e)\<close> wf
      show ?thesis
        by (auto simp: wf_env_def)
    qed
    thus "m \<preceq> n in cstack e'"
      by (simp add: e'_def unite_def)
  qed

  moreover
  have "\<forall>n m. n \<preceq> m in stack e' \<and> n \<noteq> m \<longrightarrow>
        (\<forall>u \<in> \<S> e' n. \<not> reachable_avoiding u m (unvisited e' n))"
  proof (clarify)
    fix x y u
    assume xy: "x \<preceq> y in stack e'" "x \<noteq> y"
       and u: "u \<in> \<S> e' x" "reachable_avoiding u y (unvisited e' x)"
    show "False"
    proof (cases "x = hd (stack e')")
      case True
      hence "\<S> e' x = cc" 
        by (simp add: hd_cc)
      with \<open>u \<in> \<S> e' x\<close> obtain x' where
        x': "x' \<in> set pfx \<union> {hd (stack e')}" "u \<in> \<S> e x'"
        by (auto simp: cc_def)
      from \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
      have "stack e = pfx @ (hd (stack e') # tl (stack e'))"
        by auto
      with x' True have "x' \<preceq> x in stack e"
        by (simp add: split_list_precedes)
      moreover
      from xy \<open>stack e = pfx @ stack e'\<close> have "x \<preceq> y in stack e"
        by (simp add: precedes_append_left)
      ultimately have "x' \<preceq> y in stack e"
        using wf by (auto simp: wf_env_def elim: precedes_trans)
      from \<open>x' \<preceq> x in stack e\<close> \<open>x \<preceq> y in stack e\<close> wf \<open>x \<noteq> y\<close>
      have "x' \<noteq> y"
        by (auto simp: wf_env_def dest: precedes_antisym)
      let ?unv = "\<Union> {unvisited e y | y. y \<in> set pfx \<union> {hd (stack e')}}"
      from \<open>\<S> e' x = cc\<close> have "?unv = unvisited e' x"
        by (auto simp: unvisited_def cc_def e'_def unite_def)
      with \<open>reachable_avoiding u y (unvisited e' x)\<close>
      have "reachable_avoiding u y ?unv"
        by simp
      with x' have "reachable_avoiding u y (unvisited e x')"
        by (blast intro: ra_mono)
      with \<open>x' \<preceq> y in stack e\<close> \<open>x' \<noteq> y\<close> \<open>u \<in> \<S> e x'\<close> wf
      show ?thesis
        by (auto simp: wf_env_def)
    next
      case False
      with \<open>x \<preceq> y in stack e'\<close> \<open>stack e' \<noteq> []\<close>
      have "x \<in> set (tl (stack e'))"
        by (metis list.exhaust_sel precedes_mem(1) set_ConsD)
      with \<open>u \<in> \<S> e' x\<close> have "u \<in> \<S> e x"
        by (auto simp add: unite_S_tl[OF wf w] e'_def)
      moreover
      from \<open>x \<preceq> y in stack e'\<close> \<open>stack e = pfx @ stack e'\<close>
      have "x \<preceq> y in stack e"
        by (simp add: precedes_append_left)
      moreover
      from unite_S_tl[OF wf w] \<open>x \<in> set (tl (stack e'))\<close>
      have "unvisited e' x = unvisited e x"
        by (auto simp: unvisited_def e'_def unite_def)
      ultimately show ?thesis
        using \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e' x)\<close> wf
        by (auto simp: wf_env_def)
    qed
  qed


  moreover
  have "\<forall>n. is_subscc (\<S> e' n)"
  proof
    fix n
    show "is_subscc (\<S> e' n)"
    proof (cases "n \<in> cc")
      case True
      hence "\<S> e' n = cc"
        by (simp add: Se')
      with unite_subscc[OF pre w] hd_cc
      show ?thesis
        by (auto simp: e'_def)
    next
      case False
      with wf show ?thesis
        by (simp add: Se' wf_env_def)
    qed
  qed

  ultimately show ?thesis
    unfolding wf_env_def by blast
qed

subsection \<open>Lemmas establishing the pre-conditions\<close>

text \<open>
  The precondition of function @{text dfs} ensures the precondition
  of @{text dfss} at the call of that function.
\<close>
lemma pre_dfs_pre_dfss:
  assumes "pre_dfs v e"
  shows "pre_dfss v (e\<lparr>visited := visited e \<union> {v}, 
                       stack := v # stack e, 
                       cstack := v # cstack e\<rparr>)"
        (is "pre_dfss v ?e'")
proof -
  from assms have wf: "wf_env e"
    by (simp add: pre_dfs_def)

  from assms have v: "v \<notin> visited e"
    by (simp add: pre_dfs_def)

  from assms stack_visited[OF wf]
  have "\<forall>n \<in> visited ?e'. reachable (root ?e') n"
       "distinct (stack ?e')"
       "distinct (cstack ?e')"
       "explored ?e' \<subseteq> visited ?e'"
       "set (cstack ?e') \<subseteq> visited ?e'"
       "\<forall>n \<in> explored ?e'. \<forall>m. reachable n m \<longrightarrow> m \<in> explored ?e'"
       "\<forall>n. vsuccs ?e' n \<subseteq> successors n"
       "\<forall>n \<in> explored ?e'. vsuccs ?e' n = successors n"
       "\<forall>n \<in> visited ?e' - set(cstack ?e'). vsuccs ?e' n = successors n"
       "\<forall>n. n \<notin> visited ?e' \<longrightarrow> vsuccs ?e' n = {}"
       "(\<forall>n m. m \<in> \<S> ?e' n \<longleftrightarrow> (\<S> ?e' n = \<S> ?e' m))"
       "(\<forall>n. n \<notin> visited ?e' \<longrightarrow> \<S> ?e' n = {n})"
       "\<forall>n. is_subscc (\<S> ?e' n)"
       "\<forall>S \<in> sccs ?e'. is_scc S"
       "\<Union> (sccs ?e') = explored ?e'"
    by (auto simp: pre_dfs_def wf_env_def)

  moreover
  have "\<forall>n m. n \<preceq> m in stack ?e' \<longrightarrow> reachable m n"
  proof (clarify)
    fix x y
    assume "x \<preceq> y in stack ?e'"
    show "reachable y x"
    proof (cases "x=v")
      assume "x=v"
      with \<open>x \<preceq> y in stack ?e'\<close> assms show ?thesis
        apply (simp add: pre_dfs_def)
        by (metis insert_iff list.simps(15) precedes_mem(2) reachable_refl)
    next
      assume "x \<noteq> v"
      with \<open>x \<preceq> y in stack ?e'\<close> wf show ?thesis
        by (simp add: pre_dfs_def wf_env_def precedes_in_tail)
    qed
  qed

  moreover
  from wf v have "\<forall>n. vsuccs ?e' n \<subseteq> visited ?e'"
    by (auto simp: wf_env_def)

  moreover
  from wf v 
  have "(\<forall>n \<in> set (stack ?e'). \<forall> m \<in> set (stack ?e'). n \<noteq> m \<longrightarrow> \<S> ?e' n \<inter> \<S> ?e' m = {})"
    apply (simp add: wf_env_def)
    by (metis singletonD)

  moreover
  have "\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = visited ?e' - explored ?e'"
  proof -
    have "\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = 
          (\<Union> {\<S> e v | v . v \<in> set (stack e)}) \<union> \<S> e v"
      by auto
    also from wf v have "\<dots> = visited ?e' - explored ?e'"
      by (auto simp: wf_env_def)
    finally show ?thesis .
  qed

  moreover
  have "\<forall>n m. n \<preceq> m in stack ?e' \<and> n \<noteq> m \<longrightarrow>
           (\<forall>u \<in> \<S> ?e' n. \<not> reachable_avoiding u m (unvisited ?e' n))"
  proof (clarify)
    fix x y u
    assume asm: "x \<preceq> y in stack ?e'" "x \<noteq> y" "u \<in> \<S> ?e' x"
                "reachable_avoiding u y (unvisited ?e' x)"
    show "False"
    proof (cases "x = v")
      case True
      with wf v \<open>u \<in> \<S> ?e' x\<close> have "u = v" "vsuccs ?e' v = {}"
        by (auto simp: wf_env_def)
      with \<open>reachable_avoiding u y (unvisited ?e' x)\<close>[THEN ra_cases]
           True \<open>x \<noteq> y\<close> wf
      show ?thesis
        by (auto simp: wf_env_def unvisited_def)
    next
      case False
      with asm wf show ?thesis
        by (auto simp: precedes_in_tail wf_env_def unvisited_def)
    qed
  qed

  moreover 
  have "\<forall>n m. n \<preceq> m in stack ?e' \<longrightarrow> n \<preceq> m in cstack ?e'"
  proof (clarsimp)
    fix n m
    assume "n \<preceq> m in (v # stack e)"
    with assms show "n \<preceq> m in (v # cstack e)"
      unfolding pre_dfs_def wf_env_def
      by (metis head_precedes insertI1 list.simps(15) precedes_in_tail precedes_mem(2) precedes_refl)
  qed

  moreover 
  have "\<forall>n \<in> set (stack ?e'). \<forall>m \<in> \<S> ?e' n. m \<in> set (cstack ?e') \<longrightarrow> m \<preceq> n in cstack ?e'"
  proof (clarify)
    fix n m
    assume "n \<in> set (stack ?e')" "m \<in> \<S> ?e' n" "m \<in> set (cstack ?e')"
    show "m \<preceq> n in cstack ?e'"
    proof (cases "n = v")
      case True
      with wf v \<open>m \<in> \<S> ?e' n\<close> show ?thesis
        by (auto simp: wf_env_def)
    next
      case False
      with \<open>n \<in> set (stack ?e')\<close> \<open>m \<in> \<S> ?e' n\<close>
      have "n \<in> set (stack e)" "m \<in> \<S> e n"
        by auto
      with wf v False \<open>m \<in> \<S> e n\<close> \<open>m \<in> set (cstack ?e')\<close>
      show ?thesis
        apply (simp add: wf_env_def)
        by (metis (mono_tags, lifting) precedes_in_tail singletonD)
    qed
  qed

  ultimately have "wf_env ?e'"
    unfolding wf_env_def by (meson le_inf_iff)

  moreover
  from assms 
  have "\<forall>w \<in> vsuccs ?e' v. w \<in> explored ?e' \<union> \<S> ?e' (hd (stack ?e'))"
    by (simp add: pre_dfs_def)

  moreover
  from \<open>\<forall>n m. n \<preceq> m in stack ?e' \<longrightarrow> reachable m n\<close>
  have "\<forall>n \<in> set (stack ?e'). reachable n v"
    by (simp add: head_precedes)

  moreover
  from wf v have "\<S> ?e' (hd (stack ?e')) = {v}"
    by (simp add: pre_dfs_def wf_env_def)

  ultimately show ?thesis
    by (auto simp: pre_dfss_def)
qed

text \<open>
  Similarly, we now show that the pre-conditions of the different
  function calls in the body of function @{text dfss} are satisfied.
  First, it is very easy to see that the pre-condition of @{text dfs}
  holds at the call of that function.
\<close>
lemma pre_dfss_pre_dfs:
  assumes "pre_dfss v e" and "w \<notin> visited e" and "w \<in> successors v"
  shows "pre_dfs w e" 
  using assms unfolding pre_dfss_def pre_dfs_def wf_env_def
  by (meson succ_reachable)

text \<open>
  The pre-condition of @{text dfss} holds when the successor
  considered in the current iteration has already been explored.
\<close>
lemma pre_dfss_explored_pre_dfss:
  fixes e v w
  defines "e'' \<equiv> e\<lparr>vsuccs := (\<lambda>x. if x=v then vsuccs e v \<union> {w} else vsuccs e x)\<rparr>"
  assumes 1: "pre_dfss v e" and 2: "w \<in> successors v" and 3: "w \<in> explored e"
  shows "pre_dfss v e''"
proof -
  from 1 have v: "v \<in> visited e"
    by (simp add: pre_dfss_def)
  have "wf_env e''"
  proof -
    from 1 have wf: "wf_env e"
      by (simp add: pre_dfss_def)
    hence "\<forall>v \<in> visited e''. reachable (root e'') v"
          "distinct (stack e'')"
          "distinct (cstack e'')"
          "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
          "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> reachable m n"
          "explored e'' \<subseteq> visited e''"
          "set (cstack e'') \<subseteq> visited e''"
          "\<forall>n \<in> explored e''. \<forall>m. reachable n m \<longrightarrow> m \<in> explored e''"
          "\<forall>n m. m \<in> \<S> e'' n \<longleftrightarrow> (\<S> e'' n = \<S> e'' m)"
          "\<forall>n. n \<notin> visited e'' \<longrightarrow> \<S> e'' n = {n}"
          "\<forall>n \<in> set (stack e''). \<forall> m \<in> set (stack e''). 
                n \<noteq> m \<longrightarrow> \<S> e'' n \<inter> \<S> e'' m = {}"
          "\<Union> {\<S> e'' n | n. n \<in> set (stack e'')} = visited e'' - explored e''"
          "\<forall>n \<in> set (stack e''). \<forall>m \<in> \<S> e'' n. 
              m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
          "\<forall>n. is_subscc (\<S> e'' n)"
          "\<forall>S \<in> sccs e''. is_scc S"
          "\<Union> (sccs e'') = explored e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf 2 3 have "\<forall>v. vsuccs e'' v \<subseteq> successors v \<inter> visited e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf v have "\<forall>n. n \<notin> visited e'' \<longrightarrow> vsuccs e'' n = {}"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf 2
    have "\<forall>v. v \<in> explored e'' \<longrightarrow> vsuccs e'' v = successors v"
      by (auto simp: wf_env_def e''_def)
    moreover
    have "\<forall>x y. x \<preceq> y in stack e'' \<and> x \<noteq> y \<longrightarrow>
             (\<forall>u \<in> \<S> e'' x. \<not> reachable_avoiding u y (unvisited e'' x))"
    proof (clarify)
      fix x y u
      assume "x \<preceq> y in stack e''" "x \<noteq> y" 
             "u \<in> \<S> e'' x"
             "reachable_avoiding u y (unvisited e'' x)"
      hence prec: "x \<preceq> y in stack e" "u \<in> \<S> e x"
        by (auto simp: e''_def)
      with stack_unexplored[OF wf] have "y \<notin> explored e"
        by (blast dest: precedes_mem)
      have "(unvisited e x = unvisited e'' x)
          \<or> (unvisited e x = unvisited e'' x \<union> {(v,w)})"
        by (auto simp: e''_def unvisited_def split: if_splits)
      thus "False"
      proof
        assume "unvisited e x = unvisited e'' x"
        with prec \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e'' x)\<close> wf
        show ?thesis
          unfolding wf_env_def by metis
      next
        assume "unvisited e x = unvisited e'' x \<union> {(v,w)}"
        with wf \<open>reachable_avoiding u y (unvisited e'' x)\<close>
             \<open>y \<notin> explored e\<close> \<open>w \<in> explored e\<close> prec \<open>x \<noteq> y\<close>
        show ?thesis
          using avoiding_explored[OF wf] unfolding wf_env_def
          by (metis (no_types, lifting))
      qed
    qed
    moreover 
    from wf 2
    have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
      by (auto simp: e''_def wf_env_def)
    ultimately show ?thesis
      unfolding wf_env_def by meson
  qed
  with 1 3 show ?thesis
    by (auto simp: pre_dfss_def e''_def)
qed

text \<open>
  The call to @{text dfs} establishes the pre-condition for the
  recursive call to @{text dfss} in the body of @{text dfss}.
\<close>
lemma pre_dfss_post_dfs_pre_dfss:
  fixes e v w
  defines "e' \<equiv> dfs w e"
  defines "e'' \<equiv> e'\<lparr>vsuccs := (\<lambda>x. if x=v then vsuccs e' v \<union> {w} else vsuccs e' x)\<rparr>"
  assumes pre: "pre_dfss v e"
      and w: "w \<in> successors v" "w \<notin> visited e"
      and post: "post_dfs w e e'"
  shows "pre_dfss v e''"
proof -
  from pre 
  have "wf_env e" "v \<in> visited e" "stack e \<noteq> []" "v \<in> \<S> e (hd (stack e))"
    by (auto simp: pre_dfss_def)
  with post have "stack e' \<noteq> []" "v \<in> \<S> e' (hd (stack e'))"
    by (auto dest: dfs_S_hd_stack)
  
  from post have "w \<in> visited e'"
    by (simp add: post_dfs_def)

  have "wf_env e''"
  proof -
    from post have wf': "wf_env e'"
      by (simp add: post_dfs_def)
    hence "\<forall>n \<in> visited e''. reachable (root e'') n"
          "distinct (stack e'')"
          "distinct (cstack e'')"
          "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
          "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> reachable m n"
          "explored e'' \<subseteq> visited e''"
          "set (cstack e'') \<subseteq> visited e''"
          "\<forall>n \<in> explored e''. \<forall>m. reachable n m \<longrightarrow> m \<in> explored e''"
          "\<forall>n m. m \<in> \<S> e'' n \<longleftrightarrow> (\<S> e'' n = \<S> e'' m)"
          "\<forall>n. n \<notin> visited e'' \<longrightarrow> \<S> e'' n = {n}"
          "\<forall>n \<in> set (stack e''). \<forall> m \<in> set (stack e''). 
              n \<noteq> m \<longrightarrow> \<S> e'' n \<inter> \<S> e'' m = {}"
          "\<Union> {\<S> e'' n | n. n \<in> set (stack e'')} = visited e'' - explored e''"
          "\<forall>n \<in> set (stack e''). \<forall> m \<in> \<S> e'' n. m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
          "\<forall>n. is_subscc (\<S> e'' n)"
          "\<forall>S \<in> sccs e''. is_scc S"
          "\<Union> (sccs e'') = explored e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf' w have "\<forall>n. vsuccs e'' n \<subseteq> successors n"
      by (auto simp: wf_env_def e''_def)
    moreover 
    from wf' \<open>w \<in> visited e'\<close> have "\<forall>n. vsuccs e'' n \<subseteq> visited e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from post \<open>v \<in> visited e\<close>
    have "\<forall>n. n \<notin> visited e'' \<longrightarrow> vsuccs e'' n = {}"
      apply (simp add: post_dfs_def wf_env_def sub_env_def e''_def)
      by (meson subsetD)
    moreover
    from wf' w
    have "\<forall>n \<in> explored e''. vsuccs e'' n = successors n"
      by (auto simp: wf_env_def e''_def)
    moreover
    have "\<forall>n m. n \<preceq> m in stack e'' \<and> n \<noteq> m \<longrightarrow>
             (\<forall>u \<in> \<S> e'' n. \<not> reachable_avoiding u m (unvisited e'' n))"
    proof (clarify)
      fix x y u
      assume "x \<preceq> y in stack e''" "x \<noteq> y"
             "u \<in> \<S> e'' x"
             "reachable_avoiding u y (unvisited e'' x)"
      hence 1: "x \<preceq> y in stack e'" "u \<in> \<S> e' x"
        by (auto simp: e''_def)
      with stack_unexplored[OF wf'] have "y \<notin> explored e'"
        by (auto dest: precedes_mem)
      have "(unvisited e' x = unvisited e'' x)
          \<or> (unvisited e' x = unvisited e'' x \<union> {(v,w)})"
        by (auto simp: e''_def unvisited_def split: if_splits)
      thus "False"
      proof
        assume "unvisited e' x = unvisited e'' x"
        with 1 \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e'' x)\<close> wf'
        show ?thesis
          unfolding wf_env_def by metis
      next
        assume unv: "unvisited e' x = unvisited e'' x \<union> {(v,w)}"
        from post
        have "w \<in> explored e' 
           \<or> (w \<in> \<S> e' (hd (stack e')) \<and> (\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n))"
          by (auto simp: post_dfs_def)
        thus ?thesis
        proof
          assume "w \<in> explored e'"
          with wf' unv \<open>reachable_avoiding u y (unvisited e'' x)\<close>
               \<open>y \<notin> explored e'\<close> 1 \<open>x \<noteq> y\<close>
          show ?thesis
            using avoiding_explored[OF wf'] unfolding wf_env_def
            by (metis (no_types, lifting))
        next
          assume w: "w \<in> \<S> e' (hd (stack e'))
                  \<and> (\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n)"
          from \<open>reachable_avoiding u y (unvisited e'' x)\<close>[THEN ra_add_edge]
               unv
          have "reachable_avoiding u y (unvisited e' x)
              \<or> reachable_avoiding w y (unvisited e' x)"
            by auto
          thus ?thesis
          proof
            assume "reachable_avoiding u y (unvisited e' x)"
            with \<open>x \<preceq> y in stack e''\<close> \<open>x \<noteq> y\<close> \<open>u \<in> \<S> e'' x\<close> wf'
            show ?thesis
              by (auto simp: e''_def wf_env_def)
          next
            assume "reachable_avoiding w y (unvisited e' x)"
            from unv have "v \<in> \<S> e' x"
              by (auto simp: unvisited_def)
            from \<open>x \<preceq> y in stack e''\<close> have "x \<in> set (stack e')"
              by (simp add: e''_def precedes_mem)
            have "x = hd (stack e')"
            proof (rule ccontr)
              assume "x \<noteq> hd (stack e')"
              with \<open>x \<in> set (stack e')\<close> \<open>stack e' \<noteq> []\<close>
              have "x \<in> set (tl (stack e'))"
                by (metis hd_Cons_tl set_ConsD)
              with w \<open>v \<in> \<S> e' x\<close> have "v \<in> \<S> e x"
                by auto
              moreover
              from post \<open>stack e' \<noteq> []\<close> \<open>x \<in> set (stack e')\<close> \<open>x \<in> set (tl (stack e'))\<close>
              have "x \<in> set (tl (stack e))"
                unfolding post_dfs_def
                by (metis Un_iff self_append_conv2 set_append tl_append2)
              moreover
              from pre have "wf_env e" "stack e \<noteq> []" "v \<in> \<S> e (hd (stack e))"
                by (auto simp: pre_dfss_def)
              ultimately show "False"
                unfolding wf_env_def
                by (metis (no_types, lifting) distinct.simps(2) hd_Cons_tl insert_disjoint(2) 
                          list.set_sel(1) list.set_sel(2) mk_disjoint_insert)
            qed
            with \<open>reachable_avoiding w y (unvisited e' x)\<close>
                 \<open>x \<preceq> y in stack e''\<close> \<open>x \<noteq> y\<close> w wf'
            show ?thesis
              by (auto simp add: e''_def wf_env_def)
          qed
        qed
      qed
    qed

    moreover
    from wf' \<open>\<forall>n. vsuccs e'' n \<subseteq> successors n\<close>
    have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
      by (auto simp: wf_env_def e''_def split: if_splits)
    ultimately show ?thesis
      unfolding wf_env_def by (meson le_inf_iff)
  qed

  show "pre_dfss v e''"
  proof -
    from pre post
    have "v \<in> visited e''"
      by (auto simp: pre_dfss_def post_dfs_def sub_env_def e''_def)
    moreover
    {
      fix u
      assume u: "u \<in> vsuccs e'' v"
      have "u \<in> explored e'' \<union> \<S> e'' (hd (stack e''))"
      proof (cases "u = w")
        case True
        with post show ?thesis
          by (auto simp: post_dfs_def e''_def)
      next
        case False
        with u pre post
        have "u \<in> explored e \<union> \<S> e (hd (stack e))"
          by (auto simp: pre_dfss_def post_dfs_def e''_def)
        then show ?thesis
        proof
          assume "u \<in> explored e"
          with post show ?thesis
            by (auto simp: post_dfs_def sub_env_def e''_def)
        next
          assume "u \<in> \<S> e (hd (stack e))"
          with \<open>wf_env e\<close> post \<open>stack e \<noteq> []\<close>
          show ?thesis
            by (auto simp: e''_def dest: dfs_S_hd_stack)
        qed
      qed
    }
    moreover
    from pre post
    have "\<forall>n \<in> set (stack e''). reachable n v"
      unfolding pre_dfss_def post_dfs_def
      using e''_def by force
    moreover
    from \<open>stack e' \<noteq> []\<close> have "stack e'' \<noteq> []"
      by (simp add: e''_def)
    moreover
    from \<open>v \<in> \<S> e' (hd (stack e'))\<close> have "v \<in> \<S> e'' (hd (stack e''))"
      by (simp add: e''_def)
    moreover
    from pre post have "\<exists>ns. cstack e'' = v # ns"
      by (auto simp: pre_dfss_def post_dfs_def e''_def)
    ultimately show ?thesis
      using \<open>wf_env e''\<close> unfolding pre_dfss_def by blast
  qed
qed

text \<open>
  Finally, the pre-condition for the recursive call to @{text dfss}
  at the end of the body of function @{text dfss} also holds if
  @{text unite} was applied.
\<close>

lemma pre_dfss_unite_pre_dfss:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  defines "e'' \<equiv> e'\<lparr>vsuccs := (\<lambda>x. if x=v then vsuccs e' v \<union> {w} else vsuccs e' x)\<rparr>"
  assumes pre: "pre_dfss v e"
      and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
  shows "pre_dfss v e''"
proof -
  from pre have wf: "wf_env e"
    by (simp add: pre_dfss_def)
  from pre have "v \<in> visited e"
    by (simp add: pre_dfss_def)
  from pre w have "v \<notin> explored e"
    unfolding pre_dfss_def wf_env_def
    by (meson reachable_edge)

  from unite_stack[OF wf w] obtain pfx where
    pfx: "stack e = pfx @ stack e'" "stack e' \<noteq> []"
         "let cc = \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}
          in \<S> e' = (\<lambda>x. if x \<in> cc then cc else \<S> e x)"
         "w \<in> \<S> e' (hd (stack e'))"
    by (auto simp: e'_def)
  define cc where "cc \<equiv> \<Union> {\<S> e n |n. n \<in> set pfx \<union> {hd (stack e')}}"

  from unite_wf_env[OF pre w] have wf': "wf_env e'"
    by (simp add: e'_def)

  from \<open>stack e = pfx @ stack e'\<close> \<open>stack e' \<noteq> []\<close>
  have "hd (stack e) \<in> set pfx \<union> {hd (stack e')}"
    by (simp add: hd_append)
  with pre have "v \<in> cc"
    by (auto simp: pre_dfss_def cc_def)
  from S_reflexive[OF wf, of "hd (stack e')"]
  have "hd (stack e') \<in> cc"
    by (auto simp: cc_def)
  with pfx \<open>v \<in> cc\<close> have "v \<in> \<S> e' (hd (stack e'))"
    by (auto simp: cc_def)

  from unite_sub_env[OF pre w] have "sub_env e e'"
    by (simp add: e'_def)

  have "wf_env e''"
  proof -
    from wf'
    have "\<forall>n \<in> visited e''. reachable (root e'') n"
         "distinct (stack e'')" 
         "distinct (cstack e'')"
         "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
         "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> reachable m n"
         "explored e'' \<subseteq> visited e''"
         "set (cstack e'') \<subseteq> visited e''"
         "\<forall>n \<in> explored e''. \<forall>m. reachable n m \<longrightarrow> m \<in> explored e''"
         "\<forall>n m. m \<in> \<S> e'' n \<longleftrightarrow> (\<S> e'' n = \<S> e'' m)"
         "\<forall>n. n \<notin> visited e'' \<longrightarrow> \<S> e'' n = {n}"
         "\<forall>n \<in> set (stack e''). \<forall>m \<in> set (stack e''). 
             n \<noteq> m \<longrightarrow> \<S> e'' n \<inter> \<S> e'' m = {}"
         "\<Union> {\<S> e'' n | n. n \<in> set (stack e'')} = visited e'' - explored e''"
         "\<forall>n \<in> set (stack e''). \<forall>m \<in> \<S> e'' n. 
             m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
         "\<forall>n. is_subscc (\<S> e'' n)"
         "\<forall>S \<in> sccs e''. is_scc S"
         "\<Union> (sccs e'') = explored e''"
      by (auto simp: wf_env_def e''_def)

    moreover
    from wf' w \<open>sub_env e e'\<close>
    have "\<forall>n. vsuccs e'' n \<subseteq> successors n \<inter> visited e''"
      by (auto simp: wf_env_def sub_env_def e''_def)

    moreover
    from wf' \<open>v \<in> visited e\<close> \<open>sub_env e e'\<close>
    have "\<forall>n. n \<notin> visited e'' \<longrightarrow> vsuccs e'' n = {}"
      by (auto simp: wf_env_def sub_env_def e''_def)

    moreover
    from wf' \<open>v \<notin> explored e\<close>
    have "\<forall>n \<in> explored e''. vsuccs e'' n = successors n"
      by (auto simp: wf_env_def e''_def e'_def unite_def)

    moreover
    from wf' \<open>w \<in> successors v\<close>
    have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
      by (auto simp: wf_env_def e''_def e'_def unite_def)

    moreover
    have "\<forall>x y. x \<preceq> y in stack e'' \<and> x \<noteq> y \<longrightarrow>
                (\<forall>u \<in> \<S> e'' x. \<not> reachable_avoiding u y (unvisited e'' x))"
    proof (clarify)
      fix x y u
      assume xy: "x \<preceq> y in stack e''" "x \<noteq> y"
         and u: "u \<in> \<S> e'' x" "reachable_avoiding u y (unvisited e'' x)"
      hence prec: "x \<preceq> y in stack e'" "u \<in> \<S> e' x"
        by (simp add: e''_def)+
      show "False"
      proof (cases "x = hd (stack e')")
        case True
        with \<open>v \<in> \<S> e' (hd (stack e'))\<close>
        have "unvisited e' x = unvisited e'' x
            \<or> (unvisited e' x = unvisited e'' x \<union> {(v,w)})"
          by (auto simp: e''_def unvisited_def split: if_splits)
        thus "False"
        proof
          assume "unvisited e' x = unvisited e'' x"
          with prec \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e'' x)\<close> wf'
          show ?thesis
            unfolding wf_env_def by metis
        next
          assume "unvisited e' x = unvisited e'' x \<union> {(v,w)}"
          with \<open>reachable_avoiding u y (unvisited e'' x)\<close>[THEN ra_add_edge]
          have "reachable_avoiding u y (unvisited e' x)
              \<or> reachable_avoiding w y (unvisited e' x)"
            by auto
          thus ?thesis
          proof
            assume "reachable_avoiding u y (unvisited e' x)"
            with prec \<open>x \<noteq> y\<close> wf' show ?thesis
              by (auto simp: wf_env_def)
          next
            assume "reachable_avoiding w y (unvisited e' x)"
            with \<open>x = hd (stack e')\<close> \<open>w \<in> \<S> e' (hd (stack e'))\<close> 
                 \<open>x \<preceq> y in stack e'\<close> \<open>x \<noteq> y\<close> wf'
            show ?thesis
              by (auto simp: wf_env_def)
          qed
        qed
      next
        case False
        with \<open>x \<preceq> y in stack e'\<close> \<open>stack e' \<noteq> []\<close>
        have "x \<in> set (tl (stack e'))"
          by (metis list.exhaust_sel precedes_mem(1) set_ConsD)
        with unite_S_tl[OF wf w] \<open>u \<in> \<S> e' x\<close>
        have "u \<in> \<S> e x"
          by (simp add: e'_def)
        moreover
        from \<open>x \<preceq> y in stack e'\<close> \<open>stack e = pfx @ stack e'\<close>
        have "x \<preceq> y in stack e"
          by (simp add: precedes_append_left)
        moreover
        from \<open>v \<in> \<S> e' (hd (stack e'))\<close> \<open>x \<in> set (tl (stack e'))\<close>
             \<open>stack e' \<noteq> []\<close> wf'
        have "v \<notin> \<S> e' x"
          unfolding wf_env_def
          by (metis (no_types, lifting) Diff_cancel Diff_triv distinct.simps(2) insert_not_empty 
                    list.exhaust_sel list.set_sel(1) list.set_sel(2) mk_disjoint_insert)
        hence "unvisited e'' x = unvisited e' x"
          by (auto simp: unvisited_def e''_def split: if_splits)
        moreover
        from \<open>x \<in> set (tl (stack e'))\<close> unite_S_tl[OF wf w]
        have "unvisited e' x = unvisited e x"
          by (simp add: unvisited_def e'_def unite_def)
        ultimately show ?thesis
          using \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e'' x)\<close> wf
          by (auto simp: wf_env_def)
      qed
    qed
      
    ultimately show ?thesis
      unfolding wf_env_def by meson
  qed

  show "pre_dfss v e''"
  proof -
    from pre have "v \<in> visited e''"
      by (simp add: pre_dfss_def e''_def e'_def unite_def)

    moreover
    {
      fix u
      assume u: "u \<in> vsuccs e'' v"
      have "u \<in> explored e'' \<union> \<S> e'' (hd (stack e''))"
      proof (cases "u = w")
        case True
        with \<open>w \<in> \<S> e' (hd (stack e'))\<close> show ?thesis 
          by (simp add: e''_def)
      next
        case False
        with u have "u \<in> vsuccs e v"
          by (simp add: e''_def e'_def unite_def)
        with pre have "u \<in> explored e \<union> \<S> e (hd (stack e))"
          by (auto simp: pre_dfss_def)
        then show ?thesis
        proof
          assume "u \<in> explored e"
          thus ?thesis
            by (simp add: e''_def e'_def unite_def)
        next
          assume "u \<in> \<S> e (hd (stack e))"
          with \<open>hd (stack e) \<in> set pfx \<union> {hd (stack e')}\<close>
          have "u \<in> cc"
            by (auto simp: cc_def)
          moreover
          from S_reflexive[OF wf, of "hd (stack e')"] pfx
          have "\<S> e' (hd (stack e')) = cc"
            by (auto simp: cc_def)
          ultimately show ?thesis
            by (simp add: e''_def)
        qed
      qed
    }
    hence "\<forall>w \<in> vsuccs e'' v. w \<in> explored e'' \<union> \<S> e'' (hd (stack e''))"
      by blast

    moreover
    from pre \<open>stack e = pfx @ stack e'\<close>
    have "\<forall>n \<in> set (stack e''). reachable n v"
      by (auto simp: pre_dfss_def e''_def)

    moreover
    from \<open>stack e' \<noteq> []\<close> have "stack e'' \<noteq> []"
      by (simp add: e''_def)

    moreover
    from \<open>v \<in> \<S> e' (hd (stack e'))\<close> have "v \<in> \<S> e'' (hd (stack e''))"
      by (simp add: e''_def)

    moreover
    from pre have "\<exists>ns. cstack e'' = v # ns"
      by (auto simp: pre_dfss_def e''_def e'_def unite_def)

    ultimately show ?thesis
      using \<open>wf_env e''\<close> unfolding pre_dfss_def by blast
  qed
qed

subsection \<open>Lemmas establishing the post-conditions\<close>

text \<open>
  Assuming the pre-condition of function @{text dfs} and the post-condition of
  the call to @{text dfss} in the body of that function, the post-condition of
  @{text dfs} is established.
\<close>
lemma pre_dfs_implies_post_dfs:
  fixes v e
  defines "e1 \<equiv> e\<lparr>visited := visited e \<union> {v}, 
                  stack := (v # stack e), 
                  cstack:=(v # cstack e)\<rparr>"
  defines "e' \<equiv> dfss v e1"
  defines "e'' \<equiv> e'\<lparr> cstack := tl(cstack e')\<rparr>"
  assumes 1: "pre_dfs v e"
      and 2: "dfs_dfss_dom (Inl(v, e))"
      and 3: "post_dfss v e1 e'"
  shows "post_dfs v e (dfs v e)"
proof -
  from 1 have wf: "wf_env e"
    by (simp add: pre_dfs_def)
  from 1 have v: "v \<notin> visited e"
    by (simp add: pre_dfs_def)
  from 3 have wf': "wf_env e'"
    by (simp add: post_dfss_def)
  from 3 have cst': "cstack e' = v # cstack e"
    by (simp add: post_dfss_def e1_def)
  show ?thesis
  proof (cases "v = hd(stack e')")
    case True
    have notempty: "stack e' = v # stack e"
    proof -
      from 3 obtain ns where 
        ns: "stack e1 = ns @ (stack e')" "stack e' \<noteq> []"
        by (auto simp: post_dfss_def)
      have "ns = []"
      proof (rule ccontr)
        assume "ns \<noteq> []"
        with ns have "hd ns = v"
          apply (simp add: e1_def)
          by (metis hd_append2 list.sel(1))
        with True ns \<open>ns \<noteq> []\<close> have "\<not> distinct (stack e1)"
          by (metis disjoint_iff_not_equal distinct_append hd_in_set) 
        with wf v stack_visited[OF wf] show False
          by (auto simp: wf_env_def e1_def)
      qed
      with ns show ?thesis
        by (simp add: e1_def)
    qed
    have e2: "dfs v e = e'\<lparr>sccs := sccs e' \<union> {\<S> e' v}, 
                           explored := explored e' \<union> (\<S> e' v), 
                           stack := tl (stack e'),
                           cstack := tl (cstack e')\<rparr>" (is "_ = ?e2")
      using True 2 dfs.psimps[of v e] unfolding e1_def e'_def 
      by (fastforce simp: e1_def e'_def)

    have sub: "sub_env e e1"
      by (auto simp: sub_env_def e1_def)

    from notempty have stack2: "stack ?e2 = stack e"
      by (simp add: e1_def)

    moreover from 3 have "v \<in> visited ?e2"
      by (auto simp: post_dfss_def sub_env_def e1_def)

    moreover
    from sub 3 have "sub_env e e'"
      unfolding post_dfss_def by (auto elim: sub_env_trans)
    with stack2 have subenv: "sub_env e ?e2"
      by (fastforce simp: sub_env_def)

    moreover have "wf_env ?e2"
    proof -
      from wf' 
      have "\<forall>n \<in> visited ?e2. reachable (root ?e2) n"
           "distinct (stack ?e2)"
           "\<forall>n. vsuccs ?e2 n \<subseteq> successors n \<inter> visited ?e2"
           "\<forall>n. n \<notin> visited ?e2 \<longrightarrow> vsuccs ?e2 n = {}"
           "\<forall>n m. m \<in> \<S> ?e2 n \<longleftrightarrow> (\<S> ?e2 n = \<S> ?e2 m)"
           "\<forall>n. n \<notin> visited ?e2 \<longrightarrow> \<S> ?e2 n = {n}"
           "\<forall>n. is_subscc (\<S> ?e2 n)"
           "\<Union> (sccs ?e2) = explored ?e2"
        by (auto simp: wf_env_def distinct_tl)

      moreover
      from 1 cst' have "distinct (cstack ?e2)"
        by (auto simp: pre_dfs_def wf_env_def)

      moreover
      from 1 stack2 have "\<forall>n m. n \<preceq> m in stack ?e2 \<longrightarrow> reachable m n"
        by (auto simp: pre_dfs_def wf_env_def)

      moreover
      from 1 stack2 cst'
      have "\<forall>n m. n \<preceq> m in stack ?e2 \<longrightarrow> n \<preceq> m in cstack ?e2"
        by (auto simp: pre_dfs_def wf_env_def)

      moreover 
      from notempty wf' have "explored ?e2 \<subseteq> visited ?e2"
        apply (simp add: wf_env_def)
        using stack_class[OF wf']
        by (smt (verit, del_insts) Diff_iff insert_subset list.simps(15) subset_eq)
  
      moreover
      from 3 cst' have "set (cstack ?e2) \<subseteq> visited ?e2"
        by (simp add: post_dfss_def wf_env_def e1_def)

      moreover
      {
        fix u
        assume "u \<in> explored ?e2"
        have "vsuccs ?e2 u = successors u"
        proof (cases "u \<in> explored e'")
          case True
          with wf' show ?thesis
            by (auto simp: wf_env_def)
        next
          case False
          with \<open>u \<in> explored ?e2\<close> have "u \<in> \<S> e' v"
            by simp
          show ?thesis
          proof (cases "u = v")
            case True
            with 3 show ?thesis
              by (auto simp: post_dfss_def)
          next
            case False
            have "u \<in> visited e' - set (cstack e')"
            proof
              from notempty \<open>u \<in> \<S> e' v\<close> stack_class[OF wf'] False
              show "u \<in> visited e'"
                by auto
            next
              show "u \<notin> set (cstack e')"
              proof
                assume u: "u \<in> set (cstack e')"
                with notempty \<open>u \<in> \<S> e' v\<close> \<open>wf_env e'\<close> have "u \<preceq> v in cstack e'"
                  by (auto simp: wf_env_def)
                with cst' u False wf' show "False"
                  unfolding wf_env_def
                  by (metis head_precedes precedes_antisym)
              qed
            qed
            with 3 show ?thesis
              by (auto simp: post_dfss_def wf_env_def)
          qed
        qed
      }
      note explored_vsuccs = this

      moreover have "\<forall>n \<in> explored ?e2. \<forall>m. reachable n m \<longrightarrow> m \<in> explored ?e2"
      proof (clarify)
        fix x y
        assume asm: "x \<in> explored ?e2" "reachable x y"
        show "y \<in> explored ?e2"
        proof (cases "x \<in> explored e'")
          case True
          with \<open>wf_env e'\<close> \<open>reachable x y\<close> show ?thesis
            by (simp add: wf_env_def)
        next
          case False
          with asm have "x \<in> \<S> e' v"
             by simp
          with \<open>explored ?e2 \<subseteq> visited ?e2\<close> have "x \<in> visited e'"
            by auto
          from \<open>x \<in> \<S> e' v\<close> wf' have "reachable v x"
            by (auto simp: wf_env_def is_subscc_def)
          have "y \<in> visited e'"
          proof (rule ccontr)
            assume "y \<notin> visited e'"
            with reachable_visited[OF wf' \<open>x \<in> visited e'\<close> \<open>reachable x y\<close>]
            obtain n m where
              "n \<in> visited e'" "m \<in> successors n - vsuccs e' n"
              "reachable x n" "reachable m y"
              by blast
            from wf' \<open>m \<in> successors n - vsuccs e' n\<close>
            have "n \<notin> explored e'"
              by (auto simp: wf_env_def)
            obtain n' where
              "n' \<in> set (stack e')" "n \<in> \<S> e' n'"
              by (rule visited_unexplored[OF wf' \<open>n \<in> visited e'\<close> \<open>n \<notin> explored e'\<close>])
            have "n' = v"
            proof (rule ccontr)
              assume "n' \<noteq> v"
              with \<open>n' \<in> set (stack e')\<close> \<open>v = hd (stack e')\<close>
              have "n' \<in> set (tl (stack e'))"
                by (metis emptyE hd_Cons_tl set_ConsD set_empty)
              moreover
              from \<open>n \<in> \<S> e' n'\<close> \<open>wf_env e'\<close> have "reachable n n'"
                by (auto simp: wf_env_def is_subscc_def)
              with \<open>reachable v x\<close> \<open>reachable x n\<close> reachable_trans 
              have "reachable v n'"
                by blast
              ultimately show "False"
                using 3 \<open>v = hd (stack e')\<close> 
                by (auto simp: post_dfss_def)
            qed
            with \<open>n \<in> \<S> e' n'\<close> \<open>m \<in> successors n - vsuccs e' n\<close> explored_vsuccs
            show "False"
              by auto
          qed
          show ?thesis
          proof (cases "y \<in> explored e'")
            case True
            then show ?thesis
              by simp
          next
            case False
            obtain n where ndef: "n \<in> set (stack e')" "(y \<in> \<S> e' n)"
              by (rule visited_unexplored[OF wf' \<open>y \<in> visited e'\<close> False])
            show ?thesis
            proof (cases "n = v")
              case True
              with ndef show ?thesis by simp
            next
              case False
              with ndef notempty have "n \<in> set (tl (stack e'))"
                by simp
              moreover
              from wf' ndef have "reachable y n"
                by (auto simp: wf_env_def is_subscc_def)
              with \<open>reachable v x\<close> \<open>reachable x y\<close>
              have "reachable v n"
                by (meson reachable_trans)
              ultimately show ?thesis
                using \<open>v = hd (stack e')\<close> 3 
                by (simp add: post_dfss_def)
            qed
          qed
        qed
      qed

      moreover
      from 3 cst'
      have "\<forall>n \<in> visited ?e2 - set (cstack ?e2). vsuccs ?e2 n = successors n"
        apply (simp add: post_dfss_def wf_env_def)
        by (metis (no_types, lifting) Diff_empty Diff_iff empty_set insertE 
                  list.exhaust_sel list.sel(1) list.simps(15))

      moreover
      from wf' notempty
      have "\<forall>n m. n \<in> set (stack ?e2) \<and> m \<in> set (stack ?e2) \<and> n \<noteq> m 
                  \<longrightarrow> (\<S> ?e2 n \<inter> \<S> ?e2 m = {})"
        by (simp add: wf_env_def)

      moreover 
      have "\<Union> {\<S> ?e2 n | n . n \<in> set (stack ?e2)} = visited ?e2 - explored ?e2"
      proof -
        from wf' notempty
        have "(\<Union> {\<S> ?e2 n | n . n \<in> set (stack ?e2)}) \<inter> \<S> e' v = {}"
          by (auto simp: wf_env_def)
        with notempty
        have "\<Union> {\<S> ?e2 n | n . n \<in> set (stack ?e2)} =
              (\<Union> {\<S> e' n | n . n \<in> set (stack e')}) - \<S> e' v"
          by auto
        also from wf' 
        have "\<dots> = (visited e' - explored e') - \<S> e' v"
          by (simp add: wf_env_def)
        finally show ?thesis
          by auto
      qed

      moreover
      have "\<forall>n \<in> set (stack ?e2). \<forall>m \<in> \<S> ?e2 n. m \<in> set (cstack ?e2) \<longrightarrow> m \<preceq> n in cstack ?e2"
      proof (clarsimp simp: cst')
        fix n m
        assume "n \<in> set (tl (stack e'))"
               "m \<in> \<S> e' n" "m \<in> set (cstack e)"
        with 3 have "m \<in> \<S> e n"
          by (auto simp: post_dfss_def e1_def)
        with wf notempty \<open>n \<in> set (tl (stack e'))\<close> \<open>m \<in> set (cstack e)\<close>
        show "m \<preceq> n in cstack e"
          by (auto simp: wf_env_def)
      qed

      moreover
      {
        fix x y u
        assume xy: "x \<preceq> y in stack ?e2" "x \<noteq> y"
           and u: "u \<in> \<S> ?e2 x" "reachable_avoiding u y (unvisited ?e2 x)"
        from xy notempty stack2
        have "x \<preceq> y in stack e'"
          by (metis head_precedes insert_iff list.simps(15) precedes_in_tail precedes_mem(2))
        with wf' \<open>x \<noteq> y\<close> u have "False"
          by (auto simp: wf_env_def unvisited_def)
      }

      moreover have "\<forall>S \<in> sccs ?e2. is_scc S"
      proof (clarify)
        fix S
        assume asm: "S \<in> sccs ?e2"
        show "is_scc S"
        proof (cases "S = \<S> e' v")
          case True
          with S_reflexive[OF wf'] have "S \<noteq> {}"
            by blast
          from wf' True have subscc: "is_subscc S"
            by (simp add: wf_env_def)
          {
            assume "\<not> is_scc S"
            with \<open>S \<noteq> {}\<close> \<open>is_subscc S\<close> obtain S' where
              S'_def: "S' \<noteq> S" "S \<subseteq> S'" "is_subscc S'" 
              unfolding is_scc_def by blast
            then obtain x where "x \<in> S' \<and> x \<notin> S"
              by blast
            with True S'_def wf'
            have xv: "reachable v x \<and> reachable x v"
              unfolding wf_env_def is_subscc_def by (metis in_mono)
            from \<open>\<forall>v w. w \<in> \<S> ?e2 v \<longleftrightarrow> (\<S> ?e2 v = \<S> ?e2 w)\<close>
            have "v \<in> explored ?e2"
              by auto
            with \<open>\<forall>x \<in> explored ?e2. \<forall>y. reachable x y \<longrightarrow> y \<in> explored ?e2\<close>
                 xv \<open>S = \<S> e' v\<close> \<open>x \<in> S' \<and> x \<notin> S\<close>
            have "x \<in> explored e'"
              by auto
            with wf' xv have "v \<in> explored e'"
              by (auto simp: wf_env_def)
            with notempty have "False"
              by (auto intro: stack_unexplored[OF wf'])
          }
          then show ?thesis
            by blast
        next
          case False
          with asm wf' show ?thesis
            by (auto simp: wf_env_def)
        qed
      qed

      ultimately show ?thesis
        unfolding wf_env_def by meson
    qed

    moreover 
    from \<open>wf_env ?e2\<close> have "v \<in> explored ?e2"
      by (auto simp: wf_env_def)

    moreover
    from 3 have "vsuccs ?e2 v = successors v"
      by (simp add: post_dfss_def)

    moreover
    from 1 3 have "\<forall>w \<in> visited e. vsuccs ?e2 w = vsuccs e w"
      by (auto simp: pre_dfs_def post_dfss_def e1_def)

    moreover 
    from stack2 1 
    have "\<forall>n \<in> set (stack ?e2). reachable n v"
      by (simp add: pre_dfs_def)

    moreover 
    from stack2 have "\<exists>ns. stack e = ns @ (stack ?e2)"
      by auto

    moreover
    from 3 have "\<forall>n \<in> set (stack ?e2). \<S> ?e2 n = \<S> e n"
      by (auto simp: post_dfss_def e1_def)

    moreover
    from cst' have "cstack ?e2 = cstack e"
      by simp

    ultimately show ?thesis
      unfolding post_dfs_def using e2 by simp
  next
    case False
    with 2 have e': "dfs v e = e''"
      by (simp add: dfs.psimps e''_def e'_def e1_def)

    moreover have "wf_env e''"
    proof -
      from wf'
      have "\<forall>n \<in> visited e''. reachable (root e'') n"
           "distinct (stack e'')"
           "distinct (cstack e'')"
           "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> reachable m n"
           "explored e'' \<subseteq> visited e''"
           "\<forall>n \<in> explored e''. \<forall>m. reachable n m \<longrightarrow> m \<in> explored e''"
           "\<forall>n. vsuccs e'' n \<subseteq> successors n \<inter> visited e''"
           "\<forall>n. n \<notin> visited e'' \<longrightarrow> vsuccs e'' n = {}"
           "\<forall>n \<in> explored e''. vsuccs e'' n = successors n"
           "\<forall>n m. m \<in> \<S> e'' n \<longleftrightarrow> (\<S> e'' n = \<S> e'' m)"
           "\<forall>n. n \<notin> visited e'' \<longrightarrow> \<S> e'' n = {n}"
           "\<forall>n \<in> set (stack e''). \<forall>m \<in> set (stack e''). 
               n \<noteq> m \<longrightarrow> \<S> e'' n \<inter> \<S> e'' m = {}"
           "\<Union> {\<S> e'' n | n. n \<in> set (stack e'')} = visited e'' - explored e''"
           "\<forall>n. is_subscc (\<S> e'' n)"
           "\<forall>S \<in> sccs e''. is_scc S"
           "\<Union> (sccs e'') = explored e''"
        by (auto simp: e''_def wf_env_def distinct_tl)

      moreover have "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
      proof (clarsimp simp add: e''_def)
        fix n m
        assume nm: "n \<preceq> m in stack e'"
        with 3 have "n \<preceq> m in cstack e'"
          unfolding post_dfss_def wf_env_def 
          by meson
        moreover
        have "n \<noteq> v"
        proof
          assume "n = v"
          with nm have "n \<in> set (stack e')"
            by (simp add: precedes_mem)
          with 3 \<open>n = v\<close> have "v = hd (stack e')"
            unfolding post_dfss_def wf_env_def
            by (metis (no_types, opaque_lifting) IntI equals0D list.set_sel(1))
          with \<open>v \<noteq> hd (stack e')\<close> show "False"
            by simp
        qed
        ultimately show "n \<preceq> m in tl (cstack e')"
          by (simp add: cst' precedes_in_tail)
      qed

      moreover
      from 3 have "set (cstack e'') \<subseteq> visited e''"
        by (simp add: post_dfss_def wf_env_def e''_def e1_def subset_eq)

      moreover 
      from 3
      have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
        apply (simp add: post_dfss_def wf_env_def e''_def e1_def)
        by (metis (no_types, opaque_lifting) DiffE DiffI set_ConsD)

      moreover 
      have "\<forall>n \<in> set (stack e''). \<forall>m \<in> \<S> e'' n. 
               m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
      proof (clarsimp simp: e''_def)
        fix m n
        assume asm: "n \<in> set (stack e')" "m \<in> \<S> e' n" 
                    "m \<in> set (tl (cstack e'))"
        with wf' cst' have "m \<noteq> v" "m \<preceq> n in cstack e'"
          by (auto simp: wf_env_def)
        with cst' show "m \<preceq> n in tl (cstack e')"
          by (simp add: precedes_in_tail)
      qed

      moreover
      from wf'
      have "(\<forall>x y. x \<preceq> y in stack e'' \<and> x \<noteq> y \<longrightarrow>
                (\<forall>u \<in> \<S> e'' x. \<not> reachable_avoiding u y (unvisited e'' x)))"
        by (force simp: e''_def wf_env_def unvisited_def)

      ultimately show ?thesis
        unfolding wf_env_def by blast
    qed

    moreover
    from 3 have "v \<in> visited e''"
      by (auto simp: post_dfss_def sub_env_def e''_def e1_def)

    moreover
    have subenv: "sub_env e e''"
    proof -
      have "sub_env e e1"
        by (auto simp: sub_env_def e1_def)
      with 3 have "sub_env e e'"
        by (auto simp: post_dfss_def elim: sub_env_trans)
      thus ?thesis
        by (auto simp add: sub_env_def e''_def)
    qed

    moreover
    from 3 have "vsuccs e'' v = successors v"
      by (simp add: post_dfss_def e''_def)

    moreover
    from 1 3 have "\<forall>w \<in> visited e. vsuccs e'' w = vsuccs e w"
      by (auto simp: pre_dfs_def post_dfss_def e1_def e''_def)

    moreover 
    from 3 have "\<forall>n \<in> set (stack e''). reachable n v"
      by (auto simp: e''_def post_dfss_def)

    moreover 
    from 3 \<open>v \<noteq> hd (stack e')\<close>
    have "\<exists>ns. stack e = ns @ (stack e'')"
      apply (simp add: post_dfss_def e''_def e1_def)
      by (metis append_Nil list.sel(1) list.sel(3) tl_append2)

    moreover
    from 3
    have "stack e'' \<noteq> []" "v \<in> \<S> e'' (hd (stack e''))"
         "\<forall>n \<in> set (tl (stack e'')). \<S> e'' n = \<S> e n"
      by (auto simp: post_dfss_def e1_def e''_def)

    moreover 
    from cst' have "cstack e'' = cstack e"
      by (simp add: e''_def)

    ultimately show ?thesis unfolding post_dfs_def
      by blast
  qed
qed

text \<open>
  The following lemma is central for proving
  partial correctness: assuming termination (represented by
  the predicate @{text dfs_dfss_dom}) and the pre-condition
  of the functions, both @{text dfs} and @{text dfss}
  establish their post-conditions. The first part of the
  theorem follows directly from the preceding lemma and the
  computational induction rule generated by Isabelle, the
  second part is proved directly, distinguishing the different
  cases in the definition of function @{text dfss}.
\<close>
lemma pre_post:
  shows
  "\<lbrakk>dfs_dfss_dom (Inl(v,e)); pre_dfs v e\<rbrakk> \<Longrightarrow> post_dfs v e (dfs v e)"
  "\<lbrakk>dfs_dfss_dom (Inr(v,e)); pre_dfss v e\<rbrakk> \<Longrightarrow> post_dfss v e (dfss v e)"
proof (induct rule: dfs_dfss.pinduct)
  fix v e
  assume dom: "dfs_dfss_dom (Inl(v,e))"
     and predfs: "pre_dfs v e"
     and prepostdfss: "\<And>e1. \<lbrakk> e1 = e \<lparr>visited := visited e \<union> {v}, stack := v # stack e,
                                      cstack := v # cstack e\<rparr>; pre_dfss v e1 \<rbrakk>
                            \<Longrightarrow> post_dfss v e1 (dfss v e1)"
  then show "post_dfs v e (dfs v e)"
    using pre_dfs_implies_post_dfs pre_dfs_pre_dfss by auto
next
  fix v e
  assume dom: "dfs_dfss_dom (Inr(v,e))"
     and predfss: "pre_dfss v e"
     and prepostdfs: 
           "\<And>vs w. 
             \<lbrakk> vs = successors v - vsuccs e v; vs \<noteq> {}; w = (SOME x. x \<in> vs); 
               w \<notin> explored e; w \<notin> visited e; pre_dfs w e \<rbrakk>
             \<Longrightarrow> post_dfs w e (dfs w e)"
     and prepostdfss:
           "\<And>vs w e' e''. 
             \<lbrakk> vs = successors v - vsuccs e v; vs \<noteq> {}; w = (SOME x. x \<in> vs); 
               e' = (if w \<in> explored e then e 
                     else if w \<notin> visited e then dfs w e 
                     else unite v w e); 
               e'' = e'\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs e' v \<union> {w} 
                                      else vsuccs e' x\<rparr> ;
               pre_dfss v e'' \<rbrakk>
             \<Longrightarrow> post_dfss v e'' (dfss v e'')"
  show "post_dfss v e (dfss v e)"
  proof -
    let ?vs = "successors v - vsuccs e v"
    from predfss have wf: "wf_env e"
      by (simp add: pre_dfss_def)
    from predfss have "v \<in> visited e"
      by (simp add: pre_dfss_def)
    from predfss have "v \<notin> explored e"
      by (meson DiffD2 list.set_sel(1) pre_dfss_def stack_class)

    show ?thesis
    proof (cases "?vs = {}") 
      case True
      with dom have "dfss v e = e" 
        by (simp add: dfss.psimps)
      moreover 
      from True wf have "vsuccs e v = successors v"
        unfolding wf_env_def
        by (meson Diff_eq_empty_iff le_infE subset_antisym)
      moreover 
      have "sub_env e e"
        by (simp add: sub_env_def)
      moreover 
      from predfss \<open>vsuccs e v = successors v\<close>
      have "\<forall>w \<in> successors v. w \<in> explored e \<union> \<S> e (hd (stack e))"
           "\<forall>n \<in> set (stack e). reachable n v"
           "stack e \<noteq> []"
           "v \<in> \<S> e (hd (stack e))"
        by (auto simp: pre_dfss_def)
      moreover have "\<exists>ns. stack e = ns @ (stack e)"
        by simp
      moreover
      {
        fix n
        assume asm: "hd (stack e) = v"
                    "n \<in> set (tl (stack e))"
                    "reachable v n"
        with \<open>stack e \<noteq> []\<close> have "v \<preceq> n in stack e"
          by (metis head_precedes hd_Cons_tl list.set_sel(2))
        moreover
        from wf \<open>stack e \<noteq> []\<close> asm have "v \<noteq> n"
          unfolding wf_env_def
          by (metis distinct.simps(2) list.exhaust_sel)
        moreover
        from wf have "v \<in> \<S> e v"
          by (rule S_reflexive)
        moreover
        {
          fix a b
          assume "a \<in> \<S> e v" "b \<in> successors a - vsuccs e a"
          with \<open>vsuccs e v = successors v\<close> have "a \<noteq> v"
            by auto
          from \<open>stack e \<noteq> []\<close> \<open>hd (stack e) = v\<close> 
          have "v \<in> set (stack e)"
            by auto
          with \<open>a \<noteq> v\<close> \<open>a \<in> \<S> e v\<close> wf have "a \<in> visited e"
            unfolding wf_env_def by (metis singletonD)
          have "False"
          proof (cases "a \<in> set (cstack e)")
            case True
            with \<open>v \<in> set (stack e)\<close> \<open>a \<in> \<S> e v\<close> \<open>wf_env e\<close>
            have "a \<preceq> v in cstack e"
              by (auto simp: wf_env_def)
            moreover
            from predfss obtain ns where "cstack e = v # ns"
              by (auto simp: pre_dfss_def)
            moreover
            from wf have "distinct (cstack e)"
              by (simp add: wf_env_def)
            ultimately have "a = v"
              using tail_not_precedes by force 
            with \<open>a \<noteq> v\<close> show ?thesis ..
          next
            case False
            with \<open>a \<in> visited e\<close> wf have "vsuccs e a = successors a"
              by (auto simp: wf_env_def)
            with \<open>b \<in> successors a - vsuccs e a\<close> show ?thesis
              by simp
          qed
        }
        hence "unvisited e v = {}"
          by (auto simp: unvisited_def)

        ultimately have "\<not> reachable_avoiding v n {}"
          using wf unfolding wf_env_def by metis
        with \<open>reachable v n\<close> have "False"
          by (simp add: ra_empty)
      }
      ultimately show ?thesis
        using wf by (auto simp: post_dfss_def)
    next
      case vs_case: False
      define w where "w = (SOME x. x \<in> ?vs)"
      define e' where "e' = (if w \<in> explored e then e 
                             else if w \<notin> visited e then dfs w e 
                             else unite v w e)"
      define e'' where "e'' = (e'\<lparr>vsuccs := \<lambda>x. if x=v then vsuccs e' v \<union> {w} else vsuccs e' x\<rparr>)"

      from dom vs_case have dfss: "dfss v e = dfss v e''"
        apply (simp add: dfss.psimps e''_def)
        using e'_def w_def by auto

      from vs_case have wvs: "w \<in> ?vs"
        unfolding w_def by (metis some_in_eq)
      show ?thesis
      proof (cases "w \<in> explored e")
        case True
        hence e': "e' = e"
          by (simp add: e'_def)
        with predfss wvs True
        have "pre_dfss v e''"
          by (auto simp: e''_def pre_dfss_explored_pre_dfss)
        with prepostdfss vs_case 
        have post'': "post_dfss v e'' (dfss v e'')"
          by (auto simp: w_def e'_def e''_def)

        moreover
        from post''
        have "\<forall>u \<in> visited e - {v}. vsuccs (dfss v e'') u = vsuccs e u"
          by (auto simp: post_dfss_def e' e''_def)

        moreover
        have "sub_env e e''"
          by (auto simp: sub_env_def e' e''_def)
        with post'' have "sub_env e (dfss v e'')"
          by (auto simp: post_dfss_def elim: sub_env_trans)

        moreover
        from e' have "stack e'' = stack e" "\<S> e'' = \<S> e"
          by (auto simp add: e''_def)

        moreover
        have "cstack e'' = cstack e"
          by (simp add: e''_def e')

        ultimately show ?thesis
          by (auto simp: dfss post_dfss_def)
      next
        case notexplored: False
        then show ?thesis
        proof (cases "w \<notin> visited e")
          case True
          with e'_def notexplored have "e' = dfs w e"
            by auto
          with True notexplored pre_dfss_pre_dfs predfss 
               prepostdfs vs_case w_def
          have postdfsw: "post_dfs w e e'"
            by (metis DiffD1 some_in_eq)
          with predfss wvs True \<open>e' = dfs w e\<close>
          have "pre_dfss v e''"
            by (auto simp: e''_def pre_dfss_post_dfs_pre_dfss)
          with prepostdfss vs_case 
          have post'': "post_dfss v e'' (dfss v e'')"
            by (auto simp: w_def e'_def e''_def)

          moreover
          have "\<forall>u \<in> visited e - {v}. vsuccs (dfss v e'') u = vsuccs e u"
          proof
            fix u
            assume "u \<in> visited e - {v}"
            with postdfsw 
            have u: "vsuccs e' u = vsuccs e u" "u \<in> visited e'' - {v}"
              by (auto simp: post_dfs_def sub_env_def e''_def)
            with post'' have "vsuccs (dfss v e'') u = vsuccs e'' u"
              by (auto simp: post_dfss_def)
            with u show "vsuccs (dfss v e'') u = vsuccs e u"
              by (simp add: e''_def)
          qed

          moreover
          have "sub_env e (dfss v e'')"
          proof -
            from postdfsw have "sub_env e e'"
              by (simp add: post_dfs_def)
            moreover
            have "sub_env e' e''"
              by (auto simp: sub_env_def e''_def)
            moreover
            from post'' have "sub_env e'' (dfss v e'')"
              by (simp add: post_dfss_def)
            ultimately show ?thesis
              by (metis sub_env_trans)
          qed

          moreover
          from postdfsw post''
          have "\<exists>ns. stack e = ns @ (stack (dfss v e''))"
            by (auto simp: post_dfs_def post_dfss_def e''_def)

          moreover
          {
            fix n
            assume n: "n \<in> set (tl (stack (dfss v e'')))"
            with post'' have "\<S> (dfss v e'') n = \<S> e' n"
              by (simp add: post_dfss_def e''_def)
            moreover
            from \<open>pre_dfss v e''\<close> n post'' 
            have "stack e' \<noteq> [] \<and> n \<in> set (tl (stack e''))"
              apply (simp add: pre_dfss_def post_dfss_def e''_def)
              by (metis (no_types, lifting) Un_iff list.set_sel(2) self_append_conv2 set_append tl_append2)
            with postdfsw have "\<S> e' n = \<S> e n"
              apply (simp add: post_dfs_def e''_def)
              by (metis list.set_sel(2))
            ultimately have "\<S> (dfss v e'') n = \<S> e n"
              by simp
          }

          moreover
          from postdfsw have "cstack e'' = cstack e"
            by (auto simp: post_dfs_def e''_def)

          ultimately show ?thesis
            by (auto simp: dfss post_dfss_def)

        next
          case False
          hence e': "e' = unite v w e" using notexplored
            using e'_def by simp
          from False have "w \<in> visited e"
            by simp
          from wf wvs notexplored False obtain pfx where
            pfx: "stack e = pfx @ (stack e')" "stack e' \<noteq> []"
            unfolding e' by (blast dest: unite_stack)

          from predfss wvs notexplored False \<open>e' = unite v w e\<close>
          have "pre_dfss v e''"
            by (auto simp: e''_def pre_dfss_unite_pre_dfss)

          with prepostdfss vs_case \<open>e' = unite v w e\<close>  \<open>w \<notin> explored e\<close> \<open>w \<in> visited e\<close>
          have post'': "post_dfss v e'' (dfss v e'')"
            by (auto simp: w_def e''_def)

          moreover
          from post''
          have "\<forall>u \<in> visited e - {v}. vsuccs (dfss v e'') u = vsuccs e u"
            by (auto simp: post_dfss_def e''_def e' unite_def)

          moreover
          have "sub_env e (dfss v e'')"
          proof -
            from predfss wvs \<open>w \<in> visited e\<close> notexplored
            have "sub_env e e'"
              unfolding e' by (blast dest: unite_sub_env)
            moreover
            have "sub_env e' e''"
              by (auto simp: sub_env_def e''_def)
            moreover
            from post'' have "sub_env e'' (dfss v e'')"
              by (simp add: post_dfss_def)
            ultimately show ?thesis
              by (metis sub_env_trans)
          qed

          moreover
          from post'' \<open>stack e = pfx @ stack e'\<close>
          have "\<exists>ns. stack e = ns @ (stack (dfss v e''))"
            by (auto simp: post_dfss_def e''_def)

          moreover
          {
            fix n
            assume n: "n \<in> set (tl (stack (dfss v e'')))"
            with post'' have "\<S> (dfss v e'') n = \<S> e'' n"
              by (simp add: post_dfss_def)
            moreover
            from n post'' \<open>stack e' \<noteq> []\<close> 
            have "n \<in> set (tl (stack e''))"
              apply (simp add: post_dfss_def e''_def)
              by (metis (no_types, lifting) Un_iff list.set_sel(2) self_append_conv2 set_append tl_append2)
            with wf wvs \<open>w \<in> visited e\<close> notexplored
            have "\<S> e'' n = \<S> e n"
              by (auto simp: e''_def e' dest: unite_S_tl)
            ultimately have "\<S> (dfss v e'') n = \<S> e n"
              by simp
          }

          moreover
          from post'' have "cstack (dfss v e'') = cstack e"
            by (simp add: post_dfss_def e''_def e' unite_def)

          ultimately show ?thesis
            by (simp add: dfss post_dfss_def)
        qed
      qed
    qed
  qed
qed

text \<open>
  We can now show partial correctness of the algorithm:
  applied to some node @{text "v"} and the empty environment,
  it computes the set of strongly connected components in
  the subgraph reachable from node @{text "v"}. In particular,
  if @{text "v"} is a root of the graph, the algorithm computes
  the set of SCCs of the graph.
\<close>

theorem partial_correctness:
  fixes v
  defines "e \<equiv> dfs v (init_env v)"
  assumes "dfs_dfss_dom (Inl (v, init_env v))"
  shows "sccs e = {S . is_scc S \<and> (\<forall>n\<in>S. reachable v n)}"
    (is "_ = ?rhs")
proof -
  from assms init_env_pre_dfs[of v]
  have post: "post_dfs v (init_env v) e"
    by (auto dest: pre_post)
  hence wf: "wf_env e"
    by (simp add: post_dfs_def)
  from post have "cstack e = []"
    by (auto simp: post_dfs_def init_env_def)
  have "stack e = []"
  proof (rule ccontr)
    assume "stack e \<noteq> []"
    hence "hd (stack e) \<preceq> hd (stack e) in stack e"
      by simp
    with wf \<open>cstack e = []\<close> show "False"
      unfolding wf_env_def
      by (metis empty_iff empty_set precedes_mem(2))
  qed
  with post have vexp: "v \<in> explored e"
    by (simp add: post_dfs_def)
  from wf \<open>stack e = []\<close> have "explored e = visited e"
    by (auto simp: wf_env_def)
  have "sccs e \<subseteq> ?rhs"
  proof
    fix S
    assume S: "S \<in> sccs e"
    with wf have "is_scc S"
      by (simp add: wf_env_def)
    moreover
    from S wf have "S \<subseteq> explored e"
      unfolding wf_env_def
      by blast
    with post \<open>explored e = visited e\<close> have "\<forall>n\<in>S. reachable v n"
      by (auto simp: post_dfs_def wf_env_def sub_env_def init_env_def)
    ultimately show "S \<in> ?rhs"
      by auto
  qed
  moreover
  {
    fix S
    assume "is_scc S" "\<forall>n\<in>S. reachable v n"
    from \<open>\<forall>n\<in>S. reachable v n\<close> vexp wf
    have "S \<subseteq> \<Union> (sccs e)"
      unfolding wf_env_def by (metis subset_eq)
    with \<open>is_scc S\<close> obtain S' where S': "S' \<in> sccs e \<and> S \<inter> S' \<noteq> {}"
      unfolding is_scc_def
      by (metis Union_disjoint inf.absorb_iff2 inf_commute)
    with wf have "is_scc S'"
      by (simp add: wf_env_def)
    with S' \<open>is_scc S\<close> have "S \<in> sccs e"
      by (auto dest: scc_partition)
  }
  ultimately show ?thesis by blast
qed

section \<open>Proof of termination and total correctness\<close>

text \<open>
  We define a binary relation on the arguments of functions @{text dfs} and @{text dfss},
  and prove that this relation is well-founded and that all calls within
  the function bodies respect the relation, assuming that the pre-conditions
  of the initial function call are satisfied. By well-founded induction,
  we conclude that the pre-conditions of the functions are sufficient to
  ensure termination.

  Following the internal representation of the two mutually recursive
  functions in Isabelle as a single function on the disjoint sum of the
  types of arguments, our relation is defined as a set of argument pairs
  injected into the sum type. The left injection @{text Inl} takes
  arguments of function @{text dfs}, the right injection @{text Inr}
  takes arguments of function @{text dfss}.\footnote{Note that the
    types of the arguments of @{text dfs} and @{text dfss} are actually
    identical. We nevertheless use the sum type in order to remember
    the function that was called.}
  The conditions on the arguments in the definition of the relation
  overapproximate the arguments in the actual calls.
\<close>

definition dfs_dfss_term::"(('v \<times> 'v env + 'v \<times> 'v env) \<times> ('v \<times> 'v env + 'v \<times> 'v env)) set" where
  "dfs_dfss_term \<equiv>
    { (Inr(v, e1), Inl(v, e)) | v e e1. 
      v \<in> vertices - visited e \<and> visited e1 = visited e \<union> {v} }
  \<union> { (Inl(w, e), Inr(v, e)) | v w e. v \<in> vertices}
  \<union> { (Inr(v, e''), Inr(v, e)) | v e e''. 
       v \<in> vertices \<and> sub_env e e'' 
     \<and> (\<exists>w \<in> vertices. w \<notin> vsuccs e v \<and> w \<in> vsuccs e'' v)}"

text \<open>
  Informally, termination is ensured because at each call,
  either a new vertex is visited (hence the complement of
  the set of visited nodes w.r.t. the finite set of vertices
  decreases) or a new successor is added to the set 
  @{text "vsuccs e v"} of some vertex @{text v}.

  In order to make this argument formal, we inject the argument
  tuples that appear in our relation into tuples consisting of
  the sets mentioned in the informal argument. However, there is
  one added complication because the call of @{text dfs} from
  @{text dfss} does not immediately add the vertex to the set
  of visited nodes (this happens only at the beginning of
  function @{text dfs}). We therefore add a third component of
  $0$ or $1$ to these tuples, reflecting the fact that there
  can only be one call of @{text dfs} from @{text dfss} for a
  given vertex @{text v}.
\<close>

fun dfs_dfss_to_tuple where
  "dfs_dfss_to_tuple (Inl(v::'v, e::'v env)) = 
   (vertices - visited e, vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e u}, 0)"
| "dfs_dfss_to_tuple (Inr(v::'v, e::'v env)) = 
   (vertices - visited e, vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e u}, 1::nat)"


text \<open>
  The triples defined in this way can be ordered lexicographically
  (with the first two components ordered as finite subsets and the
  third one following the predecessor relation on natural numbers).
  We prove that the injection of the above relation into sets
  of triples respects the lexicographic ordering and conclude that
  our relation is well-founded.
\<close>

lemma wf_term: "wf dfs_dfss_term"
proof -
  let ?r = "(finite_psubset :: ('v set \<times> 'v set) set)
            <*lex*> (finite_psubset :: ((('v \<times> 'v) set) \<times> ('v \<times> 'v) set) set)
            <*lex*> pred_nat"
  have "wf (finite_psubset :: ('v set \<times> 'v set) set)"
    by (rule wf_finite_psubset)
  moreover
  have "wf (finite_psubset :: ((('v \<times> 'v) set) \<times> ('v \<times> 'v) set) set)"
    by (rule wf_finite_psubset)
  ultimately have "wf ?r"
    using wf_pred_nat by blast
  moreover
  have "dfs_dfss_term \<subseteq> inv_image ?r dfs_dfss_to_tuple"
  proof (clarify)
    fix a b
    assume "(a,b) \<in> dfs_dfss_term"
    hence "(\<exists>v w e e''. a = Inr(v,e'') \<and> b = Inr(v,e) \<and> v \<in> vertices \<and> sub_env e e''
                      \<and> w \<in> vertices \<and> w \<notin> vsuccs e v \<and> w \<in> vsuccs e'' v)
         \<or> (\<exists>v e e1. a = Inr(v,e1) \<and> b = Inl(v,e) \<and> v \<in> vertices - visited e 
                   \<and> visited e1 = visited e \<union> {v})
         \<or> (\<exists>v w e. a = Inl(w,e) \<and> b = Inr(v,e))"
         (is "?c1 \<or> ?c2 \<or> ?c3")
      by (auto simp: dfs_dfss_term_def)
    then show "(a,b) \<in> inv_image ?r dfs_dfss_to_tuple"
    proof
      assume "?c1"
      then obtain v w e e'' where
        ab: "a = Inr(v, e'')" "b = Inr(v,e)" and
        vw: "v \<in> vertices" "w \<in> vertices" "w \<in> vsuccs e'' v" "w \<notin> vsuccs e v" and
        sub: "sub_env e e''"
        by blast
      from sub have "vertices - visited e'' \<subseteq> vertices - visited e"
        by (auto simp: sub_env_def)
      moreover
      from sub vw
      have "(vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e'' u})
          \<subset> (vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e u})"
        by (auto simp: sub_env_def)
      ultimately show ?thesis
        using vfin ab by auto
    next
      assume "?c2 \<or> ?c3"
      with vfin show ?thesis
        by (auto simp: pred_nat_def)
    qed
  qed
  ultimately show ?thesis
    using wf_inv_image wf_subset by blast
qed

text \<open>
  The following theorem establishes sufficient conditions that ensure
  termination of the two functions @{text dfs} and @{text dfss}. 
  The proof proceeds by well-founded induction using the relation 
  @{text dfs_dfss_term}. Isabelle represents the termination domains
  of the functions by the predicate @{text dfs_dfss_dom} and
  generates a theorem @{text dfs_dfss.domintros} for proving
  membership of arguments in the termination domains. The
  actual formulation is a litte technical because the mutual
  induction must again be encoded in a single induction argument
  over the sum type representing the arguments of both functions.
\<close>

theorem dfs_dfss_termination:
  "\<lbrakk>v \<in> vertices ; pre_dfs v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inl(v, e))"
  "\<lbrakk>v \<in> vertices ; pre_dfss v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inr(v, e))"
proof -
  { fix args
    have "(case args
          of Inl(v,e) \<Rightarrow> 
            v \<in> vertices \<and> pre_dfs v e
          |  Inr(v,e) \<Rightarrow> 
             v \<in> vertices \<and> pre_dfss v e)
        \<longrightarrow> dfs_dfss_dom args" (is "?P args \<longrightarrow> ?Q args")
    proof (rule wf_induct[OF wf_term])
      fix arg :: "('v \<times> 'v env) + ('v \<times> 'v env)"
      assume ih: "\<forall> arg'. (arg', arg) \<in> dfs_dfss_term \<longrightarrow> (?P arg' \<longrightarrow> ?Q arg')"
      show "?P arg \<longrightarrow> ?Q arg"
      proof
        assume P: "?P arg"
        show "?Q arg"
        proof (cases arg)
          case (Inl a)
          then obtain v e where a: "arg = Inl(v, e)" 
            using dfs.cases by metis
          with P have pre: "v \<in> vertices \<and> pre_dfs v e"
            by simp
          let ?e1 = "e\<lparr>visited := visited e \<union> {v}, stack := v # stack e, cstack := v # cstack e\<rparr>"
          let ?recarg = "Inr(v, ?e1)"

          from a pre
          have "(?recarg, arg) \<in> dfs_dfss_term"
            by (auto simp: pre_dfs_def dfs_dfss_term_def)
          moreover
          from pre have "?P ?recarg"
            by (auto dest: pre_dfs_pre_dfss)
          ultimately have "?Q ?recarg"
            using ih a by auto
          then have "?Q (Inl(v, e))"
            by (auto intro: dfs_dfss.domintros)
          then show ?thesis
            by (simp add: a)
        next
          case (Inr b)
          then obtain v e where b: "arg = Inr(v, e)" 
            using dfs.cases by metis
          with P have pre: "v \<in> vertices \<and> pre_dfss v e"
            by simp
          let ?sw = "SOME w. w \<in> successors v \<and> w \<notin> vsuccs e v"
          have "?Q (Inr(v, e))"
          proof (rule dfs_dfss.domintros)
            fix w
            assume "w \<in> successors v"
                   "?sw \<notin> explored e"
                   "?sw \<notin> visited e"
                   "\<not> dfs_dfss_dom (Inl (?sw, e))"
            show "w \<in> vsuccs e v"
            proof (rule ccontr)
              assume "w \<notin> vsuccs e v"
              with \<open>w \<in> successors v\<close> have sw: "?sw \<in> successors v - vsuccs e v"
                by (metis (mono_tags, lifting) Diff_iff some_eq_imp)
              with pre \<open>?sw \<notin> visited e\<close> have "pre_dfs ?sw e"
                by (blast intro: pre_dfss_pre_dfs)
              moreover
              from pre sw sclosed have "?sw \<in> vertices"
                by blast
              moreover
              from pre have "(Inl(?sw,e), Inr(v,e)) \<in> dfs_dfss_term"
                by (simp add: dfs_dfss_term_def)
              ultimately have "dfs_dfss_dom (Inl(?sw,e))"
                using ih b by auto
              with \<open>\<not> dfs_dfss_dom (Inl (?sw, e))\<close> 
              show "False" ..
            qed
          next
            let ?e' = "dfs ?sw e"
            let ?e''= "?e'\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs ?e' v \<union> {?sw} 
                                         else vsuccs ?e' x\<rparr>"
            fix w
            assume asm: "w \<in> successors v" "w \<notin> vsuccs e v"
                        "?sw \<notin> visited e" "?sw \<notin> explored e"
            from \<open>w \<in> successors v\<close> \<open>w \<notin> vsuccs e v\<close>
            have sw: "?sw \<in> successors v - vsuccs e v"
              by (metis (no_types, lifting) Diff_iff some_eq_imp)
            with pre \<open>?sw \<notin> visited e\<close> have "pre_dfs ?sw e"
              by (blast intro: pre_dfss_pre_dfs)
            moreover
            from pre sw sclosed have "?sw \<in> vertices"
              by blast
            moreover
            from pre have "(Inl(?sw, e), Inr(v,e)) \<in> dfs_dfss_term"
              by (simp add: dfs_dfss_term_def)
            ultimately have "dfs_dfss_dom (Inl(?sw, e))"
              using ih b by auto
            from this \<open>pre_dfs ?sw e\<close> have post: "post_dfs ?sw e ?e'"
              by (rule pre_post)
            hence "sub_env e ?e'"
              by (simp add: post_dfs_def)
            moreover
            have "sub_env ?e' ?e''"
              by (auto simp: sub_env_def)
            ultimately have "sub_env e ?e''"
              by (rule sub_env_trans)
            with pre \<open>?sw \<in> vertices\<close> sw
            have "(Inr(v, ?e''), Inr(v, e)) \<in> dfs_dfss_term"
              by (auto simp: dfs_dfss_term_def)
            moreover
            from pre post sw \<open>?sw \<notin> visited e\<close> have "pre_dfss v ?e''"
              by (blast intro: pre_dfss_post_dfs_pre_dfss)
            ultimately show "dfs_dfss_dom(Inr(v, ?e''))"
              using pre ih b by auto
          next
            let ?e'' =  "e\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs e v \<union> {?sw} else vsuccs e x\<rparr>"
            fix w
            assume "w \<in> successors v" "w \<notin> vsuccs e v"
                   "?sw \<notin> visited e" "?sw \<in> explored e"
            with pre have "False"
              unfolding pre_dfss_def wf_env_def
              by (meson subsetD)
            thus "?Q (Inr(v, ?e''))"
              by simp 
          next
            fix w
            assume asm: "w \<in> successors v" "w \<notin> vsuccs e v"
                        "?sw \<in> visited e" "?sw \<in> explored e"
            let ?e'' =  "e\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs e v \<union> {?sw} else vsuccs e x\<rparr>"
            let ?recarg = "Inr(v, ?e'')"

            from \<open>w \<in> successors v\<close> \<open>w \<notin> vsuccs e v\<close>
            have sw: "?sw \<in> successors v - vsuccs e v"
              by (metis (no_types, lifting) Diff_iff some_eq_imp)

            have "(?recarg, arg) \<in> dfs_dfss_term"
            proof -
              have "sub_env e ?e''"
                by (auto simp: sub_env_def)
              moreover 
              from sw pre sclosed
              have "\<exists>u \<in> vertices. u \<notin> vsuccs e v \<and> u \<in> vsuccs ?e'' v"
                by auto
              ultimately show ?thesis
                using pre b unfolding dfs_dfss_term_def by blast
            qed
            
            moreover 
            from pre sw \<open>?sw \<in> explored e\<close> have "?P ?recarg"
              by (auto dest: pre_dfss_explored_pre_dfss)

            ultimately show "?Q ?recarg"
              using ih b by blast
          next
            fix w
            assume asm: "w \<in> successors v" "w \<notin> vsuccs e v"
                        "?sw \<in> visited e" "?sw \<notin> explored e"
            let ?eu = "unite v ?sw e"
            let ?e'' = "?eu\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs ?eu v \<union> {?sw} else vsuccs ?eu x\<rparr>"
            let ?recarg = "Inr(v, ?e'')"

            from \<open>w \<in> successors v\<close> \<open>w \<notin> vsuccs e v\<close>
            have sw: "?sw \<in> successors v - vsuccs e v"
              by (metis (no_types, lifting) Diff_iff some_eq_imp)

            have "(?recarg, arg) \<in> dfs_dfss_term"
            proof -
              from pre asm sw have "sub_env e ?eu"
                by (blast dest: unite_sub_env)
              hence "sub_env e ?e''"
                by (auto simp: sub_env_def)
              moreover 
              from sw pre sclosed
              have "\<exists>u \<in> vertices. u \<notin> vsuccs e v \<and> u \<in> vsuccs ?e'' v"
                by auto
              ultimately show ?thesis
                using pre b unfolding dfs_dfss_term_def by blast
            qed

            moreover 
            from pre sw \<open>?sw \<in> visited e\<close> \<open>?sw \<notin> explored e\<close> have "?P ?recarg"
              by (auto dest: pre_dfss_unite_pre_dfss)

            ultimately show "?Q ?recarg"
              using ih b by auto
          qed
          then show ?thesis
            by (simp add: b)
        qed
      qed
    qed
  }
  note dom=this
  from dom
  show "\<lbrakk> v \<in> vertices ; pre_dfs v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inl(v, e))"
    by auto
  from dom
  show "\<lbrakk> v \<in> vertices ; pre_dfss v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inr(v, e))"
    by auto
qed

text \<open>
  Putting everything together, we prove the total correctness of
  the algorithm when applied to some (root) vertex.
\<close>
theorem correctness:
  assumes "v \<in> vertices"
  shows "sccs (dfs v (init_env v)) = {S . is_scc S \<and> (\<forall>n\<in>S. reachable v n)}"
  using assms init_env_pre_dfs[of v]
  by (simp add: dfs_dfss_termination partial_correctness)


end
end
