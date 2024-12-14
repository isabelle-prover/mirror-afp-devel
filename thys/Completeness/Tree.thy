theory Tree 
  imports Main

begin
subsection "Tree"

inductive_set
  tree :: "['a \<Rightarrow> 'a set,'a] \<Rightarrow> (nat * 'a) set"
  for subs :: "'a \<Rightarrow> 'a set" and \<gamma> :: 'a
    \<comment>\<open>This set represents the nodes in a tree which may represent a proof of @{term \<gamma>}.
   Only storing the annotation and its level.\<close>
  where
    tree0: "(0,\<gamma>) \<in> tree subs \<gamma>"

  | tree1: "\<lbrakk>(n,delta) \<in> tree subs \<gamma>; sigma \<in> subs delta\<rbrakk>
            \<Longrightarrow> (Suc n,sigma) \<in> tree subs \<gamma>"

declare tree.cases [elim]
declare tree.intros [intro]

lemma tree0Eq: "(0,y) \<in> tree subs \<gamma> = (y = \<gamma>)"
  by auto

lemma tree1Eq:
    "(Suc n,Y) \<in> tree subs \<gamma> \<longleftrightarrow> (\<exists>sigma \<in> subs \<gamma> . (n,Y) \<in> tree subs sigma)"
  by (induct n arbitrary: Y) force+
    \<comment> \<open>moving down a tree\<close>

definition
  incLevel :: "nat * 'a \<Rightarrow> nat * 'a" where
  "incLevel = (% (n,a). (Suc n,a))"

lemma injIncLevel: "inj incLevel"
  by (simp add: incLevel_def inj_on_def)

lemma treeEquation: "tree subs \<gamma> = insert (0,\<gamma>) (\<Union>delta\<in>subs \<gamma>. incLevel ` tree subs delta)"
proof -
  have "a = 0 \<and> b = \<gamma>"
    if "(a, b) \<in> tree subs \<gamma>"
      and "\<forall>x\<in>subs \<gamma>. \<forall>(n, x) \<in>tree subs x. (a, b) \<noteq> (Suc n, x)"
    for a b
    using that Zero_not_Suc
    by (smt (verit) case_prod_conv tree.cases tree1Eq)
  then show ?thesis
    by (auto simp: incLevel_def image_iff tree1Eq case_prod_unfold)
qed

definition
  fans :: "['a \<Rightarrow> 'a set] \<Rightarrow> bool" where
  "fans subs \<equiv> (\<forall>x. finite (subs x))"


subsection "Terminal"

definition
  terminal :: "['a \<Rightarrow> 'a set,'a] \<Rightarrow> bool" where
  "terminal subs delta \<equiv> subs(delta) = {}"

lemma terminalD: "terminal subs \<Gamma> \<Longrightarrow> x ~: subs \<Gamma>"
  by(simp add: terminal_def)
  \<comment> \<open>not a good dest rule\<close>

lemma terminalI: "x \<in> subs \<Gamma> \<Longrightarrow> \<not> terminal subs \<Gamma>"
  by(auto simp add: terminal_def)
  \<comment> \<open>not a good intro rule\<close>


subsection "Inherited"

definition
  inherited :: "['a \<Rightarrow> 'a set,(nat * 'a) set \<Rightarrow> bool] \<Rightarrow> bool" where
  "inherited subs P \<equiv> (\<forall>A B. (P A \<and> P B) = P (A Un B))
                    \<and> (\<forall>A. P A = P (incLevel ` A))
                    \<and> (\<forall>n \<Gamma> A. \<not>(terminal subs \<Gamma>) \<longrightarrow> P A = P (insert (n,\<Gamma>) A))
                    \<and> (P {})"

    (******
     inherited properties:
        - preserved under: dividing into 2, join 2 parts
                           moving up/down levels
                           inserting non terminal nodes
        - hold on empty node set
     ******)

  \<comment> \<open>FIXME tjr why does it have to be invariant under inserting nonterminal nodes?\<close>

lemma inheritedUn[rule_format]:"inherited subs P \<longrightarrow> P A \<longrightarrow> P B \<longrightarrow> P (A Un B)"
  by (auto simp add: inherited_def)

lemma inheritedIncLevel[rule_format]: "inherited subs P \<longrightarrow> P A \<longrightarrow> P (incLevel ` A)"
  by (auto simp add: inherited_def)

lemma inheritedEmpty[rule_format]: "inherited subs P \<longrightarrow> P {}"
  by (auto simp add: inherited_def)

lemma inheritedInsert[rule_format]:
  "inherited subs P \<longrightarrow> ~(terminal subs \<Gamma>) \<longrightarrow> P A \<longrightarrow> P (insert (n,\<Gamma>) A)"
  by (auto simp add: inherited_def)

lemma inheritedI[rule_format]: "\<lbrakk>\<forall>A B . (P A \<and> P B) = P (A Un B);
  \<forall>A . P A = P (incLevel ` A);
  \<forall>n \<Gamma> A . ~(terminal subs \<Gamma>) \<longrightarrow> P A = P (insert (n,\<Gamma>) A);
  P {}\<rbrakk> \<Longrightarrow> inherited subs P"
  by (simp add: inherited_def)

(* These only for inherited join, and a few more places... *)
lemma inheritedUnEq[rule_format, symmetric]: "inherited subs P \<longrightarrow> (P A \<and> P B) = P (A Un B)"
  by (auto simp add: inherited_def)

lemma inheritedIncLevelEq[rule_format, symmetric]: "inherited subs P \<longrightarrow> P A = P (incLevel ` A)"
  by (auto simp add: inherited_def)

lemma inheritedInsertEq[rule_format, symmetric]: "inherited subs P \<longrightarrow> ~(terminal subs \<Gamma>) \<longrightarrow> P A = P (insert (n,\<Gamma>) A)"
  by (auto simp add: inherited_def)

lemmas inheritedUnD = iffD1[OF inheritedUnEq]

lemmas inheritedInsertD = inheritedInsertEq[THEN iffD1]

lemmas inheritedIncLevelD = inheritedIncLevelEq[THEN iffD1]

lemma inheritedUNEq:
  "finite A \<Longrightarrow> inherited subs P \<Longrightarrow> (\<forall>x\<in>A. P (B x)) = P (\<Union> a\<in>A. B a)"
  by (induction rule: finite_induct) (simp_all add: inherited_def)

lemmas inheritedUN  = inheritedUNEq[THEN iffD1]

lemmas inheritedUND[rule_format] = inheritedUNEq[THEN iffD2]

lemma inheritedPropagateEq: 
  assumes "inherited subs P"
  and "fans subs"
  and "\<not> (terminal subs delta)"
shows "P(tree subs delta) = (\<forall>sigma\<in>subs delta. P(tree subs sigma))"
  using assms unfolding fans_def
  by (metis (mono_tags, lifting) inheritedIncLevelEq inheritedInsertEq inheritedUNEq treeEquation)

lemma inheritedPropagate:
 " \<lbrakk>\<not> P (tree subs delta); inherited subs P; fans subs; \<not> terminal subs delta\<rbrakk>
    \<Longrightarrow> \<exists>sigma\<in>subs delta. \<not> P (tree subs sigma)"
  by (simp add: inheritedPropagateEq)

lemma inheritedViaSub:
  "\<lbrakk>inherited subs P; fans subs; P (tree subs delta); sigma \<in> subs delta\<rbrakk> \<Longrightarrow> P (tree subs sigma)"
  by (simp add: inheritedPropagateEq terminalI)

lemma inheritedJoin:
    "\<lbrakk>inherited subs P; inherited subs Q\<rbrakk> \<Longrightarrow> inherited subs (\<lambda>x. P x \<and> Q x)"
  by (smt (verit, best) inherited_def)

lemma inheritedJoinI:
  "\<lbrakk>inherited subs P; inherited subs Q; R = (\<lambda>x. P x \<and> Q x)\<rbrakk>
    \<Longrightarrow> inherited subs R"
  by (simp add: inheritedJoin)


subsection "bounded, boundedBy"

definition
  boundedBy :: "nat \<Rightarrow> (nat * 'a) set \<Rightarrow> bool" where
  "boundedBy N A \<equiv> (\<forall>(n,delta) \<in> A. n < N)"

definition
  bounded :: "(nat * 'a) set \<Rightarrow> bool" where
  "bounded A \<equiv> (\<exists>N . boundedBy N A)"

lemma boundedByEmpty[simp]: "boundedBy N {}"
  by(simp add: boundedBy_def)

lemma boundedByInsert: "boundedBy N (insert (n,delta) B)     = (n < N \<and> boundedBy N B)"
  by(simp add: boundedBy_def)

lemma boundedByUn: "boundedBy N (A Un B) = (boundedBy N A \<and> boundedBy N B)"
  by(auto simp add: boundedBy_def)

lemma boundedByIncLevel': "boundedBy (Suc N) (incLevel ` A) = boundedBy N A"
  by(auto simp add: incLevel_def boundedBy_def)

lemma boundedByAdd1: "boundedBy N B \<Longrightarrow> boundedBy (N+M) B"
  by(auto simp add: boundedBy_def)

lemma boundedByAdd2: "boundedBy M B \<Longrightarrow> boundedBy (N+M) B"
  by(auto simp add: boundedBy_def)

lemma boundedByMono: "boundedBy m B \<Longrightarrow> m < M \<Longrightarrow> boundedBy M B"
  by(auto simp: boundedBy_def)

lemmas boundedByMonoD  = boundedByMono

lemma boundedBy0: "boundedBy 0 A = (A = {})"
  by (auto simp add: boundedBy_def)

lemma boundedBySuc': "boundedBy N A \<Longrightarrow> boundedBy (Suc N) A"
  by (auto simp add: boundedBy_def)

lemma boundedByIncLevel: "boundedBy n (incLevel ` (tree subs \<gamma>)) \<longleftrightarrow> (\<exists>m . n = Suc m \<and> boundedBy m (tree subs \<gamma>))"
  by (metis boundedBy0 boundedByIncLevel' boundedBySuc' emptyE old.nat.exhaust
      tree.tree0)

lemma boundedByUN: "boundedBy N (UN x:A. B x) = (!x:A. boundedBy N (B x))"
  by(simp add: boundedBy_def)

lemma boundedBySuc[rule_format]: "sigma \<in> subs \<Gamma> \<Longrightarrow> boundedBy (Suc n) (tree subs \<Gamma>) \<Longrightarrow> boundedBy n (tree subs sigma)"
  by (metis boundedByIncLevel' boundedByInsert boundedByUN treeEquation)


subsection "Inherited Properties- bounded"

lemma boundedEmpty: "bounded {}"
  by(simp add: bounded_def)

lemma boundedUn: "bounded (A Un B) \<longleftrightarrow> (bounded A \<and> bounded B)"
  by (metis boundedByAdd1 boundedByAdd2 boundedByUn bounded_def)

lemma boundedIncLevel: "bounded (incLevel` A) \<longleftrightarrow> (bounded A)"
  by (meson boundedByIncLevel' boundedBySuc' bounded_def)

lemma boundedInsert: "bounded (insert a B) \<longleftrightarrow> (bounded B)"
proof (cases a)
  case (Pair a b)
  then show ?thesis
  by (metis Un_insert_left Un_insert_right boundedByEmpty boundedByInsert boundedUn
      bounded_def lessI)
qed

lemma inheritedBounded: "inherited subs bounded"
  by(blast intro!: inheritedI boundedUn[symmetric] boundedIncLevel[symmetric]
    boundedInsert[symmetric] boundedEmpty)


subsection "founded"

definition
  founded :: "['a \<Rightarrow> 'a set,'a \<Rightarrow> bool,(nat * 'a) set] \<Rightarrow> bool" where
  "founded subs Pred = (%A. !(n,delta):A. terminal subs delta \<longrightarrow> Pred delta)"

lemma foundedD: "founded subs P (tree subs delta) \<Longrightarrow> terminal subs delta \<Longrightarrow> P delta"
  by(simp add: treeEquation [of _ delta] founded_def)

lemma foundedMono: "\<lbrakk>founded subs P A; \<forall>x. P x \<longrightarrow> Q x\<rbrakk> \<Longrightarrow> founded subs Q A"
  by (auto simp: founded_def)

lemma foundedSubs: "founded subs P (tree subs \<Gamma>) \<Longrightarrow> sigma \<in> subs \<Gamma> \<Longrightarrow> founded subs P (tree subs sigma)"
  using tree1Eq by (fastforce simp: founded_def)


subsection "Inherited Properties- founded"

lemma foundedInsert: "\<not> terminal subs delta \<Longrightarrow> founded subs P (insert (n,delta) B) = (founded subs P B)"
  by (simp add: terminal_def founded_def) 

lemma foundedUn: "(founded subs P (A Un B)) = (founded subs P A \<and> founded subs P B)"
  by(force simp add: founded_def)

lemma foundedIncLevel: "founded subs P (incLevel ` A) = (founded subs P A)"
  by (simp add: case_prod_unfold founded_def incLevel_def)

lemma foundedEmpty: "founded subs P {}"
  by(auto simp add: founded_def)

lemma inheritedFounded: "inherited subs (founded subs P)"
  by (simp add: foundedEmpty foundedIncLevel foundedInsert foundedUn inherited_def)


subsection "Inherited Properties- finite"

lemma finiteUn: "finite (A Un B) = (finite A \<and> finite B)"
  by simp

lemma finiteIncLevel: "finite (incLevel ` A) = finite A"
  by (meson finite_imageD finite_imageI injIncLevel inj_on_subset subset_UNIV)

lemma inheritedFinite: "inherited subs finite"
  by (simp add: finiteIncLevel inherited_def)



subsection "path: follows a failing inherited property through tree"

definition
  failingSub :: "['a \<Rightarrow> 'a set,(nat * 'a) set \<Rightarrow> bool,'a] \<Rightarrow> 'a" where
  "failingSub subs P \<gamma> \<equiv> (SOME sigma. (sigma:subs \<gamma> \<and> ~P(tree subs sigma)))"

lemma failingSubProps: 
  "\<lbrakk>inherited subs P; \<not> P (tree subs \<gamma>); \<not> terminal subs \<gamma>; fans subs\<rbrakk>
   \<Longrightarrow> failingSub subs P \<gamma> \<in> subs \<gamma> \<and> \<not> P (tree subs (failingSub subs P \<gamma>))"
  unfolding failingSub_def
  by (metis (mono_tags, lifting) inheritedPropagateEq some_eq_ex)

lemma failingSubFailsI: 
  "\<lbrakk>inherited subs P; \<not> P (tree subs \<gamma>); \<not> terminal subs \<gamma>; fans subs\<rbrakk>
   \<Longrightarrow> \<not> P (tree subs (failingSub subs P \<gamma>))"
  by (simp add: failingSubProps)

lemmas failingSubFailsE = failingSubFailsI[THEN notE]

lemma failingSubSubs: 
  "\<lbrakk>inherited subs P; \<not> P (tree subs \<gamma>); \<not> terminal subs \<gamma>; fans subs\<rbrakk>
    \<Longrightarrow> failingSub subs P \<gamma> \<in> subs \<gamma>"
  by (simp add: failingSubProps)


primrec path :: "['a \<Rightarrow> 'a set,'a,(nat * 'a) set \<Rightarrow> bool,nat] \<Rightarrow> 'a"
where
  path0:   "path subs \<gamma> P 0       = \<gamma>"
| pathSuc: "path subs \<gamma> P (Suc n) = (if terminal subs (path subs \<gamma> P n)
                                          then path subs \<gamma> P n
                                          else failingSub subs P (path subs \<gamma> P n))"

lemma pathFailsP: 
  "\<lbrakk>inherited subs P; fans subs; \<not> P (tree subs \<gamma>)\<rbrakk>
    \<Longrightarrow> \<not> P (tree subs (path subs \<gamma> P n))"
  by (induction n) (simp_all add: failingSubProps)

lemmas PpathE = pathFailsP[THEN notE]

lemma pathTerminal:
  "\<lbrakk>inherited subs P; fans subs; terminal subs \<gamma>\<rbrakk>
   \<Longrightarrow> terminal subs (path subs \<gamma> P n)"
  by (induct n, simp_all)

lemma pathStarts:  "path subs \<gamma> P 0 = \<gamma>"
  by simp

lemma pathSubs: 
  "\<lbrakk>inherited subs P; fans subs; \<not> P (tree subs \<gamma>); \<not> terminal subs (path subs \<gamma> P n)\<rbrakk>
    \<Longrightarrow> path subs \<gamma> P (Suc n) \<in> subs (path subs \<gamma> P n)"
  by (metis PpathE failingSubSubs pathSuc)

lemma pathStops: "terminal subs (path subs \<gamma> P n) \<Longrightarrow> path subs \<gamma> P (Suc n) = path subs \<gamma> P n"
  by simp


subsection "Branch"

definition
  branch :: "['a \<Rightarrow> 'a set,'a,nat \<Rightarrow> 'a] \<Rightarrow> bool" where
  "branch subs \<Gamma> f \<longleftrightarrow> f 0 = \<Gamma>
    \<and> (!n . terminal subs (f n) \<longrightarrow> f (Suc n) = f n)
    \<and> (!n . \<not> terminal subs (f n) \<longrightarrow> f (Suc n) \<in> subs (f n))"

lemma branch0: "branch subs \<Gamma> f \<Longrightarrow> f 0 = \<Gamma>"
  by (simp add: branch_def)

lemma branchStops: "branch subs \<Gamma> f \<Longrightarrow> terminal subs (f n) \<Longrightarrow> f (Suc n) = f n"
  by (simp add: branch_def)

lemma branchSubs: "branch subs \<Gamma> f \<Longrightarrow> \<not> terminal subs (f n) \<Longrightarrow> f (Suc n) \<in> subs (f n)"
  by (simp add: branch_def)

lemma branchI: "\<lbrakk>f 0 = \<Gamma>;
  \<forall>n . terminal subs (f n) \<longrightarrow> f (Suc n) = f n;
  \<forall>n . \<not> terminal subs (f n) \<longrightarrow> f (Suc n) \<in> subs (f n)\<rbrakk> \<Longrightarrow> branch subs \<Gamma> f"
  by (simp add: branch_def)

lemma branchTerminalPropagates: "branch subs \<Gamma> f \<Longrightarrow> terminal subs (f m) \<Longrightarrow> terminal subs (f (m + n))"
  by (induct n, simp_all add: branchStops)

lemma branchTerminalMono: 
  "branch subs \<Gamma> f \<Longrightarrow> m < n \<Longrightarrow> terminal subs (f m) \<Longrightarrow> terminal subs (f n)"
  by (metis branchTerminalPropagates
      canonically_ordered_monoid_add_class.lessE)

lemma branchPath:
      "\<lbrakk>inherited subs P; fans subs; \<not> P(tree subs \<gamma>)\<rbrakk>
       \<Longrightarrow> branch subs \<gamma> (path subs \<gamma> P)"
  by(auto intro!: branchI pathStarts pathSubs pathStops)



subsection "failing branch property: abstracts path defn"

lemma failingBranchExistence:  
  "\<lbrakk>inherited subs P; fans subs; ~P(tree subs \<gamma>)\<rbrakk>
  \<Longrightarrow> \<exists>f . branch subs \<gamma> f \<and> (\<forall>n . \<not> P(tree subs (f n)))"
  by (metis PpathE branchPath)

definition
  infBranch :: "['a \<Rightarrow> 'a set,'a,nat \<Rightarrow> 'a] \<Rightarrow> bool" where
  "infBranch subs \<Gamma> f \<longleftrightarrow> f 0 = \<Gamma> \<and> (\<forall>n. f (Suc n) \<in> subs (f n))"

lemma infBranchI: "\<lbrakk>f 0 = \<Gamma>; \<forall>n . f (Suc n) \<in> subs (f n)\<rbrakk> \<Longrightarrow> infBranch subs \<Gamma> f"
  by (simp add: infBranch_def)


subsection "Tree induction principles"

  \<comment> \<open>we work hard to use nothing fancier than induction over naturals\<close>

lemma boundedTreeInduction':
 "\<lbrakk> fans subs;
    \<forall>delta. \<not> terminal subs delta \<longrightarrow> (\<forall>sigma \<in> subs delta. P sigma) \<longrightarrow> P delta \<rbrakk>
  \<Longrightarrow> \<forall>\<Gamma>. boundedBy m (tree subs \<Gamma>) \<longrightarrow>  founded subs P (tree subs \<Gamma>) \<longrightarrow> P \<Gamma>"
proof (induction m)
  case 0
  then show ?case by (metis boundedBy0 empty_iff tree.tree0)
next
  case (Suc m)
  then show ?case by (metis boundedBySuc foundedD foundedSubs)
qed
  
 
  \<comment> \<open>tjr tidied and introduced new lemmas\<close>

lemma boundedTreeInduction:
   "\<lbrakk>fans subs;
     bounded (tree subs \<Gamma>); founded subs P (tree subs \<Gamma>);
  \<And>delta. \<lbrakk>\<not> terminal subs delta; (\<forall>sigma \<in> subs delta. P sigma)\<rbrakk> \<Longrightarrow> P delta
  \<rbrakk> \<Longrightarrow> P \<Gamma>"
  by (metis boundedTreeInduction' bounded_def)

lemma boundedTreeInduction2:
 "\<lbrakk>fans subs;
    \<forall>delta. (\<forall>sigma \<in> subs delta. P sigma) \<longrightarrow> P delta\<rbrakk>
  \<Longrightarrow> boundedBy m (tree subs \<Gamma>) \<longrightarrow> P \<Gamma>"
proof (induction m arbitrary: \<Gamma>)
  case 0
  then show ?case by (metis boundedBy0 empty_iff tree.tree0)
next
  case (Suc m)
  then show ?case by (metis boundedBySuc)
qed

end
