section "Appendix"

theory Submodularity
imports
  StronglyJoinableRBT
begin

text \<open>
  \<^cite>\<open>blelloch2022joinable\<close> states the submodularity rule in two parts, a decreasing
  and an increasing side. The locale below states both verbatim as \<open>rule_dec\<close> and
  \<open>rule_inc\<close>; in particular the increasing side bounds the rank of the join from
  below as well as from above.
\<close>

locale PaperJoinable =
  Set2_Join join inv +
  BalancedTree rank c\<^sub>l c\<^sub>u inv
  for rank :: "('a::linorder * 'b) tree \<Rightarrow> real"
  and c\<^sub>l c\<^sub>u :: real
  and join :: "('a*'b) tree \<Rightarrow> 'a \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree"
  and inv :: "('a*'b) tree \<Rightarrow> bool"
  +
  assumes join_size: "\<lbrakk>inv l; inv r\<rbrakk> \<Longrightarrow> size (join l a r) = size l + size r + 1"
  assumes rule_dec:
    "\<lbrakk> rank l' \<le> rank l; rank r' \<le> rank r; inv l'; inv r'; inv (Node l (a,b) r) \<rbrakk> \<Longrightarrow>
       rank (join l' a r') \<le> rank (Node l (a,b) r)"
  assumes rule_inc:
    "\<lbrakk> rank l \<le> rank l'; rank l' \<le> rank l + x; rank r \<le> rank r'; rank r' \<le> rank r + x;
       inv l'; inv r'; inv (Node l (a,b) r) \<rbrakk> \<Longrightarrow>
       rank (Node l (a,b) r) \<le> rank (join l' a r') \<and>
       rank (join l' a r') \<le> rank (Node l (a,b) r) + x"
begin
end

text \<open>
  The main locale recovers the decreasing side verbatim and the upper bound of 
  the increasing side.
\<close>

lemma (in StronglyJoinable) rule_sub_inc_upper:
  "\<lbrakk> rank l \<le> rank l'; rank l' \<le> rank l + x; rank r \<le> rank r'; rank r' \<le> rank r + x;
     inv l'; inv r'; inv (Node l (a,b) r) \<rbrakk> \<Longrightarrow>
     rank (join l' a r') \<le> rank (Node l (a,b) r) + x"
  by (blast intro: rule_sub)

text \<open>
  The lower bound of the increasing side is not recovered, and it cannot be. Red-black
  trees are an instance of @{locale StronglyJoinable}, but over red-black trees the two
  bounds of the increasing rule contradict each other already at a singleton, for any
  \<open>join\<close> of the type fixed by @{locale Set2_Join}.

  Conversely, the rules of \<^cite>\<open>blelloch2022joinable\<close> do not imply \<open>rule_sub\<close>
  either, which is stated for arbitrary real \<open>x\<close> and thus also covers mixed and strictly
  decreasing rank changes. A counterexample can be constructed but is outside the scope
  of this formalization.
\<close>

lemma no_join_satisfies_paper_inc_rule:
  fixes J :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
  assumes inc:
    "\<And>l l' r r' a b x.
       \<lbrakk> real (rk l) \<le> real (rk l'); real (rk l') \<le> real (rk l) + x;
         real (rk r) \<le> real (rk r'); real (rk r') \<le> real (rk r) + x;
         rbt l'; rbt r'; rbt (Node l (a,b) r) \<rbrakk> \<Longrightarrow>
       real (rk (Node l (a,b) r)) \<le> real (rk (J l' a r')) \<and>
       real (rk (J l' a r')) \<le> real (rk (Node l (a,b) r)) + x"
  shows False
proof -
  let ?t_red = "Node Leaf (a::'a, (Red, 0)) Leaf"
  let ?t_black = "Node Leaf (a, (Black, Suc 0)) Leaf"
  let ?join = "J Leaf a Leaf"

  have "rbt ?t_red" and "rbt ?t_black"
    by auto

  have "real (rk ?t_red) \<le> real (rk ?join) \<and>
        real (rk ?join) \<le> real (rk ?t_red) + 0"
    by (intro inc) auto
  then have upper: "real (rk ?join) \<le> 1"
    by simp

  have "real (rk ?t_black) \<le> real (rk ?join) \<and>
        real (rk ?join) \<le> real (rk ?t_black) + 0"
    by (intro inc) auto
  then have lower: "2 \<le> real (rk ?join)"
    by simp

  from upper lower show False
    by linarith
qed

text \<open>
  Stated against the locale; no \<open>join\<close> whatsoever makes red-black trees an instance of
  the rules of \<^cite>\<open>blelloch2022joinable\<close>.
\<close>

corollary no_PaperJoinable_rbt:
  fixes J :: "('a::linorder) rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
  shows "\<not> PaperJoinable (\<lambda>t. real (rk t)) 1 2 J rbt"
proof
  assume A: "PaperJoinable (\<lambda>t. real (rk t)) 1 2 J rbt"
  show False
    by (rule no_join_satisfies_paper_inc_rule[of J]) (rule PaperJoinable.rule_inc[OF A])
qed

text \<open>
  The flag of the paper resolves the contradiction. Ported to this setting, the
  flagged join receives the colour of the node being rebuilt and consults it in the
  case of equal black heights, where a flag-free \<open>join\<close> has to commit to one colour.
\<close>

fun join\<^sub>f :: "color \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"join\<^sub>f c l x r =
  (if bh r < bh l then blacken (joinR l x r)
   else if bh l < bh r then blacken (joinL l x r)
   else if c = Red \<and> col l = Black \<and> col r = Black then R l x r else B l x r)"

corollary join\<^sub>f_rebuilds:
  assumes "rbt (Node l (a, (c, h)) r)"
  shows "join\<^sub>f c l a r = Node l (a, (c, h)) r"
using assms by auto

text \<open>
  In particular the two anchors of \<open>no_join_satisfies_paper_inc_rule\<close> now constrain
  two distinct calls, and both are satisfied exactly.
\<close>

corollary join\<^sub>f_resolves_singletons:
  "join\<^sub>f Red Leaf a Leaf = Node Leaf (a, (Red, 0)) Leaf"
  "join\<^sub>f Black Leaf a Leaf = Node Leaf (a, (Black, Suc 0)) Leaf"
  by auto

text \<open>
  The author concedes, that this appendix does not represent a comprehensive 
  argument for stating the submodularity rule(s) one way or another. In 
  particular, it might be possible to define @{term rk} or the @{term rbt} 
  variant in a way that resolves the problem at hand, but this direction was
  not explored thoroughly.
  Rather, the aim is to provide an argument for why the submodularity rule 
  was modified and why the author considers it sound to have done so.
\<close>

end