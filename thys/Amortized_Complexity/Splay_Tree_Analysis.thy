theory Splay_Tree_Analysis
imports
  "../Splay_Tree/Splay_Tree"
  Amor
  "~~/src/HOL/Library/Sum_of_Squares"
begin

section "Splay Tree Analysis"

text{* This analysis follows Schoenmakers~\cite{Schoenmakers-IPL93}. *}


subsection "Time"

fun t_splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_splay a Leaf = 0" |
"t_splay a (Node l b r) =
  (if a=b
   then 0
   else if a < b
        then case l of
          Leaf \<Rightarrow> 0 |
          Node ll c lr \<Rightarrow>
            (if a=c then 0
             else if a < c then if ll = Leaf then 0 else t_splay a ll + 1
                  else if lr = Leaf then 0 else t_splay a lr + 1)
        else case r of
          Leaf \<Rightarrow> 0 |
          Node rl c rr \<Rightarrow>
            (if a=c then 0
             else if a < c then if rl = Leaf then 0 else t_splay a rl + 1
                  else if rr = Leaf then 0 else t_splay a rr + 1))"

lemma t_splay_simps[simp]:
  "t_splay a (Node l a r) = 0"
  "a<b \<Longrightarrow> t_splay a (Node Leaf b r) = 0"
  "a<b \<Longrightarrow> t_splay a (Node (Node ll a lr) b r) = 0"
  "a<b \<Longrightarrow> a<c \<Longrightarrow> t_splay a (Node (Node ll c lr) b r) =
   (if ll = Leaf then 0 else t_splay a ll + 1)"
  "a<b \<Longrightarrow> c<a \<Longrightarrow> t_splay a (Node (Node ll c lr) b r) =
   (if lr = Leaf then 0 else t_splay a lr + 1)"
  "b<a \<Longrightarrow> t_splay a (Node l b Leaf) = 0"
  "b<a \<Longrightarrow> t_splay a (Node l b (Node rl a rr)) = 0"
  "b<a \<Longrightarrow> a<c \<Longrightarrow> t_splay a (Node l b (Node rl c rr)) =
  (if rl=Leaf then 0 else t_splay a rl + 1)"
  "b<a \<Longrightarrow> c<a \<Longrightarrow> t_splay a (Node l b (Node rl c rr)) =
  (if rr=Leaf then 0 else t_splay a rr + 1)"
by auto

declare t_splay.simps(2)[simp del]

subsection "Wlog in tree"

lemma ex_in_set_tree: "t \<noteq> Leaf \<Longrightarrow> bst t \<Longrightarrow>
  \<exists>a' \<in> set_tree t. splay a' t = splay a t \<and> t_splay a' t = t_splay a t"
proof(induction a t rule: splay.induct)
  case 1 thus ?case by simp
next
  case (2 a l b r)
  show ?case
  proof cases
    assume "a=b" thus ?thesis using "2.prems" by auto
  next
    assume "a\<noteq>b"
    hence "a<b \<or> b<a" by (metis neqE)
    thus ?thesis
    proof
      assume "a<b"
      show ?thesis
      proof(cases l)
        case Leaf thus ?thesis using `a<b` by(auto)
      next
        case (Node ll c lr)[simp]
        have "c < b" using "2.prems" by (auto)
        show ?thesis
        proof cases
          assume "a=c" thus ?thesis using `a<b` by auto
        next
          assume "a\<noteq>c"
          hence "a<c \<or> c<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<c"
            show ?thesis
            proof cases
              assume "ll = Leaf" thus ?thesis using `a<b` `a<c` `c<b` by(auto)
            next
              assume "ll \<noteq> Leaf"
              hence "splay a ll \<noteq> Leaf" by simp
              then obtain lll u llr where [simp]: "splay a ll = Node lll u llr"
                by (metis tree.exhaust)
              have "bst ll" using "2.prems" by simp
              from "2.IH"(1)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `a<c` `ll \<noteq> Leaf` `ll \<noteq> Leaf` `bst ll`]
              obtain e where "e \<in> set_tree ll" "splay e ll = splay a ll" "t_splay e ll = t_splay a ll"
                by blast
              moreover hence "e<c" using "2.prems"(2) by auto
              ultimately show ?thesis using `a<b` `a<c` `c<b` `bst ll` by force
            qed
          next
            assume "c<a" hence "\<not> a<c" by simp
            show ?thesis
            proof cases
              assume "lr = Leaf" thus ?thesis using `a<b` `c<a` by(auto)
            next
              assume "lr \<noteq> Leaf"
              hence "splay a lr \<noteq> Leaf" by simp
              then obtain lrl u lrr where [simp]: "splay a lr = Node lrl u lrr"
                by (metis tree.exhaust)
              have "bst lr" using "2.prems" by simp
              from "2.IH"(2)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `\<not>a<c` `lr \<noteq> Leaf` `lr \<noteq> Leaf` `bst lr`]
              obtain e where "e \<in> set_tree lr" "splay e lr = splay a lr" "t_splay e lr = t_splay a lr"
                by blast
              moreover hence "c<e & e<b" using "2.prems"(2) by simp
              ultimately show ?thesis using `a<b` `c<a` `c<b` `bst lr` by force
            qed
          qed
        qed
      qed
    next
      assume "b<a" hence "\<not>a<b" by simp
      show ?thesis
      proof(cases r)
        case Leaf thus ?thesis using `b<a` by(auto)
      next
        case (Node rl c rr)[simp]
        have "b < c" using "2.prems" by (auto)
        show ?thesis
        proof cases
          assume "a=c" thus ?thesis using `b<a` by auto
        next
          assume "a\<noteq>c"
          hence "a<c \<or> c<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<c" hence "\<not> c<a" by simp
            show ?thesis
            proof cases
              assume "rl = Leaf" thus ?thesis using `b<a` `a<c` by(auto)
            next
              assume "rl \<noteq> Leaf"
              hence "splay a rl \<noteq> Leaf" by simp
              then obtain rll u rlr where [simp]: "splay a rl = Node rll u rlr"
                by (metis tree.exhaust)
              have "bst rl" using "2.prems" by simp
              from "2.IH"(3)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `a<c` `rl \<noteq> Leaf` `rl \<noteq> Leaf` `bst rl`]
              obtain e where "e \<in> set_tree rl" "splay e rl = splay a rl" "t_splay e rl = t_splay a rl"
                by blast
              moreover hence "b<e & e<c" using "2.prems"(2) by simp
              ultimately show ?thesis using `b<a` `a<c` `b<c` `bst rl` by force
            qed
          next
            assume "c<a" hence "\<not>a<c" by simp
            show ?thesis
            proof cases
              assume "rr = Leaf" thus ?thesis using `b<a` `c<a` `b<c` by(auto)
            next
              assume "rr \<noteq> Leaf"
              hence "splay a rr \<noteq> Leaf" by simp
              then obtain rrl u rrr where [simp]: "splay a rr = Node rrl u rrr"
                by (metis tree.exhaust)
              have "bst rr" using "2.prems" by simp
              from "2.IH"(4)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `\<not>a<c` `rr \<noteq> Leaf` `rr \<noteq> Leaf` `bst rr`]
              obtain e where "e \<in> set_tree rr" "splay e rr = splay a rr" "t_splay e rr = t_splay a rr"
                by blast
              moreover hence "c<e" using "2.prems"(2) by simp
              ultimately show ?thesis using `b<a` `c<a` `b<c` `bst rr` by force
            qed
          qed
        qed
      qed
    qed
  qed
qed


fun t_splay_max :: "'a::linorder tree \<Rightarrow> nat" where
"t_splay_max Leaf = 0" |
"t_splay_max (Node l b Leaf) = 0" |
"t_splay_max (Node l b (Node rl c Leaf)) = 0" |
"t_splay_max (Node l b (Node rl c rr)) = t_splay_max rr + 1"

definition "size1(t::'a tree) = size t + 1"
declare size1_def[simp]


subsection "Analysis of splay"

locale Splay_Analysis =
fixes \<alpha> :: real and \<beta> :: real
assumes a1[arith]: "\<alpha> > 1"
assumes A1: "\<lbrakk>1 \<le> x; 1 \<le> y; 1 \<le> z\<rbrakk> \<Longrightarrow>
 (x+y) * (y+z) powr \<beta> \<le> (x+y) powr \<beta> * (x+y+z)"
assumes A2: "\<lbrakk>1 \<le> l'; 1 \<le> r'; 1 \<le> lr; 1 \<le> r\<rbrakk> \<Longrightarrow>
   \<alpha> * (l'+r') * (lr+r) powr \<beta> * (lr+r'+r) powr \<beta>
    \<le> (l'+r') powr \<beta> * (l'+lr+r') powr \<beta> * (l'+lr+r'+r)"
assumes A3: "\<lbrakk>1 \<le> l'; 1 \<le> r'; 1 \<le> ll; 1 \<le> r\<rbrakk> \<Longrightarrow>
  \<alpha> * (l'+r') * (l'+ll) powr \<beta> * (r'+r) powr \<beta>
  \<le> (l'+r') powr \<beta> * (l'+ll+r') powr \<beta> * (l'+ll+r'+r)"
begin

lemma nl2: "\<lbrakk> ll \<ge> 1; lr \<ge> 1; r \<ge> 1 \<rbrakk> \<Longrightarrow>
  log \<alpha> (ll + lr) + \<beta> * log \<alpha> (lr + r)
  \<le> \<beta> * log \<alpha> (ll + lr) + log \<alpha> (ll + lr + r)"
apply(rule powr_le_cancel_iff[THEN iffD1, OF a1])
apply(simp add: powr_add mult.commute[of \<beta>] powr_powr[symmetric] A1)
done


definition \<phi> :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> real" where
"\<phi> t1 t2 = \<beta> * log \<alpha> (size1 t1 + size1 t2)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l _ r) = \<Phi> l + \<Phi> r + \<phi> l r"

definition A :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> real" where
"A a t = t_splay a t + \<Phi>(splay a t) - \<Phi> t"

lemma A_simps[simp]: "A a (Node l a r) = 0"
 "a<b \<Longrightarrow> A a (Node (Node ll a lr) b r) = \<phi> lr r - \<phi> lr ll"
 "b<a \<Longrightarrow> A a (Node l b (Node rl a rr)) = \<phi> rl l - \<phi> rr rl"
by(auto simp add: A_def \<phi>_def algebra_simps real_of_nat_Suc)


lemma A_simp3: "\<lbrakk> a<b; b<c; bst ll; a \<in> set_tree ll\<rbrakk> \<Longrightarrow>
  A a (Node (Node ll b lr) c r) =
  (case splay a ll of Node lll _ llr \<Rightarrow>
   A a ll + \<phi> llr (Node lr c r) + \<phi> lr r - \<phi> ll lr - \<phi> lll llr + 1)"
by(auto simp: A_def \<phi>_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)

lemma A_simp3': "\<lbrakk> b<a; c<b; bst rr; a \<in> set_tree rr\<rbrakk> \<Longrightarrow>
  A a (Node l c (Node rl b rr)) =
  (case splay a rr of Node rrl _ rrr \<Rightarrow>
   A a rr + \<phi> rrl (Node l c rl) + \<phi> l rl - \<phi> rl rr - \<phi> rrl rrr + 1)"
by(auto simp: A_def \<phi>_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)

lemma A_simp4: "\<lbrakk> b<a; a<c; bst lr; a \<in> set_tree lr\<rbrakk> \<Longrightarrow>
  A a (Node (Node ll b lr) c r) =
  (case splay a lr of Node lrl _ lrr \<Rightarrow>
   A a lr + \<phi> ll lrl + \<phi> lrr r - \<phi> ll lr - \<phi> lrl lrr + 1)"
by(auto simp: A_def \<phi>_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)

lemma A_simp4': "\<lbrakk> c<a; a<b; bst rl; a \<in> set_tree rl\<rbrakk> \<Longrightarrow>
  A a (Node l c (Node rl b rr)) =
  (case splay a rl of Node rll _ rlr \<Rightarrow>
   A a rl + \<phi> rr rlr + \<phi> rll l - \<phi> rl rr - \<phi> rll rlr + 1)"
by(auto simp: A_def \<phi>_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)

lemma A_ub: "\<lbrakk> bst t; Node la a ra : subtrees t \<rbrakk>
  \<Longrightarrow> A a t \<le> log \<alpha> ((size1 t)/(size1 la + size1 ra))"
proof(induction a t rule: splay.induct)
  case 1 thus ?case by simp
next
  case (2 a l b r)
  let ?r = "real (size1 r)" let ?l = "real (size1 l)"
  have a: "a : insert b (set_tree l Un set_tree r)" using "2.prems"(2)
    by (metis Node_notin_subtrees_if set_tree_Node2)
  show ?case
  proof cases
    assume "a=b"
    thus ?thesis using "2.prems" by (auto simp: real_of_nat_Suc)
  next
    assume "a\<noteq>b"
    hence "a<b \<or> b<a" by (metis neqE)
    thus ?thesis
    proof
      assume "a<b"
      then obtain ll c lr where [simp]: "l = Node ll c lr"
        using "2.prems"(1,2)
        by (cases l) (auto, metis in_set_tree_if less_asym)
      let ?ll = "real (size1 ll)" let ?lr = "real (size1 lr)"
      have "c < b" using "2.prems"(1,2) by (auto)
      hence "c \<notin> set_tree r" using "2.prems"(1) by auto
      show ?thesis
      proof cases
        assume "a=c"
        thus ?thesis using "2.prems"(1,2) `a<b` `c \<notin> set_tree r` nl2[of ?ll ?lr ?r]
          by (auto simp: real_of_nat_Suc \<phi>_def log_divide field_simps)
      next
        assume "a\<noteq>c"
        hence "a<c \<or> c<a" by (metis neqE)
        thus ?thesis
        proof
          assume "a<c"
          hence 0: "a \<notin> set_tree lr \<and> a \<notin> set_tree r"
            using "2.prems"(1) by auto
          hence 1: "a \<in> set_tree ll" using "2.prems" `a<c` by (auto)
          then obtain l' u r' where sp: "splay a ll = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a ll") auto
          have "ll \<noteq> Leaf" using 1 by auto
          let ?l' = "real (size1 l')" let ?r' = "real (size1 r')"
          have "1 + log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?lr + ?r) + \<beta> * log \<alpha> (?lr + ?r' + ?r) \<le>
               \<beta> * log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?lr + ?r') + log \<alpha> (?l' + ?lr + ?r' + ?r)" (is "?L\<le>?R")
          proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
            show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A2[of ?l' ?r' ?lr ?r]
              by(simp add: powr_add add_ac mult.commute[of \<beta>] powr_powr[symmetric])
          qed
          thus ?thesis
            using "2.IH"(1)[OF `a\<noteq>b` `a<b` `l = Node ll c lr` `a\<noteq>c`] `ll \<noteq> Leaf` `a<c` `c<b` "2.prems" 0 1 sp
            by(auto simp: A_simp3 size_if_splay real_of_nat_Suc \<phi>_def log_divide algebra_simps)
       next
          assume "c<a"
          hence 0: "a \<notin> set_tree ll \<and> a \<notin> set_tree r"
            using "2.prems"(1) `a < b` by(auto)
          hence 1: "a \<in> set_tree lr" using "2.prems" `c<a` `a<b` by (auto)
          then obtain l' u r' where sp: "splay a lr = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a lr") auto
          have "lr \<noteq> Leaf" using 1 by auto
          let ?l' = "real (size1 l')" let ?r' = "real (size1 r')"
          have "1 + log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?ll) + \<beta> * log \<alpha> (?r' + ?r) \<le>
               \<beta> * log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?ll + ?r') + log \<alpha> (?l' + ?ll + ?r' + ?r)" (is "?L\<le>?R")
          proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
            show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A3[of ?l' ?r' ?ll ?r]
              by(simp add: powr_add mult.commute[of \<beta>] powr_powr[symmetric])
          qed
          thus ?thesis
            using "2.IH"(2)[OF `a\<noteq>b` `a<b` `l = Node ll c lr` `a\<noteq>c`] `lr \<noteq> Leaf` `c<a` `a<b` "2.prems" 0 1 sp
            by(auto simp add: A_simp4 size_if_splay real_of_nat_Suc \<phi>_def log_divide algebra_simps)
        qed
      qed
    next
      assume "b<a"
      then obtain rl c rr where [simp]: "r = Node rl c rr"
        using "2.prems"(1,2)
        by (cases r) (auto, metis in_set_tree_if less_asym)
      let ?rl = "real (size1 rl)" let ?rr = "real (size1 rr)"
      have "b < c" using "2.prems"(1,2) by (auto)
      hence "c \<notin> set_tree l" using "2.prems"(1) by auto
      show ?thesis
      proof cases
        assume "a=c"
        thus ?thesis using "2.prems"(1,2) `b<a` `c \<notin> set_tree l` nl2[of ?rr ?rl ?l]
          by (auto simp add: real_of_nat_Suc \<phi>_def log_divide algebra_simps)
      next
        assume "a\<noteq>c"
        hence "a<c \<or> c<a" by (metis neqE)
        thus ?thesis
        proof
          assume "a<c"
          hence 0: "a \<notin> set_tree rr \<and> a \<notin> set_tree l"
            using "2.prems"(1) `b<a` by (auto)
          hence 1: "a \<in> set_tree rl" using "2.prems" `b<a` `a<c` by (auto)
          then obtain l' u r' where sp: "splay a rl = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a rl") auto
          have "rl \<noteq> Leaf" using 1 by auto
          let ?l' = "real (size1 l')" let ?r' = "real (size1 r')"
          have "1 + log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?l) + \<beta> * log \<alpha> (?r' + ?rr) \<le>
               \<beta> * log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?r' + ?rr) + log \<alpha> (?l' + ?l + ?r' + ?rr)" (is "?L\<le>?R")
          proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
            show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A3[of ?r' ?l' ?rr ?l]
              by(simp add: powr_add mult.commute[of \<beta>] powr_powr[symmetric])
                (simp add: algebra_simps)
          qed
          thus ?thesis
            using "2.IH"(3)[OF `a\<noteq>b` order_less_not_sym[OF`b<a`] `r = Node rl c rr` `a\<noteq>c`] `rl \<noteq> Leaf` `b<a` `a<c` "2.prems" 0 1 sp
            by(auto simp add: A_simp4' size_if_splay real_of_nat_Suc \<phi>_def log_divide algebra_simps)
        next
          assume "c<a"
          hence 0: "a \<notin> set_tree rl \<and> a \<notin> set_tree l"
            using "2.prems"(1) `c<a` by(auto)
          hence 1: "a \<in> set_tree rr" using "2.prems" `c<a` `b<a` by (auto)
          then obtain l' u r' where sp: "splay a rr = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a rr") auto
          have "rr \<noteq> Leaf" using 1 by auto
          let ?l' = "real (size1 l')" let ?r' = "real (size1 r')"
          have "1 + log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l + ?rl) + \<beta> * log \<alpha> (?l' + ?l + ?rl) \<le>
               \<beta> * log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?rl + ?r') + log \<alpha> (?l' + ?rl + ?r' + ?l)" (is "?L\<le>?R")
          proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
            show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A2[of ?r' ?l' ?rl ?l]
              by(simp add: powr_add add_ac mult.commute[of \<beta>] powr_powr[symmetric])
          qed
          thus ?thesis
            using "2.IH"(4)[OF `a\<noteq>b` order_less_not_sym[OF `b<a`] `r = Node rl c rr` `a\<noteq>c`] `rr \<noteq> Leaf` `c<a` `b<a` "2.prems" 0 1 sp
            by(auto simp add: A_simp3' size_if_splay real_of_nat_Suc \<phi>_def log_divide algebra_simps)
        qed
      qed
    qed
  qed
qed


lemma A_ub2: assumes "bst t" "a : set_tree t"
shows "A a t \<le> log \<alpha> ((size1 t)/2)"
proof -
  from assms(2) obtain la ra where N: "Node la a ra : subtrees t"
    by (metis set_treeE)
  let ?T = "(size1 t)/(size1 la + size1 ra)"
  have "A a t \<le> log \<alpha> ?T" by(rule A_ub[OF assms(1) N])
  also have "\<dots> \<le> log \<alpha> ((size1 t)/2)" by(simp add: field_simps)
  finally show ?thesis by simp
qed

lemma A_ub3: assumes "bst t" shows "A a t \<le> log \<alpha> (size1 t)"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: A_def)
next
  assume "t \<noteq> Leaf"
  from ex_in_set_tree[OF this assms] obtain a' where
    a': "a' \<in> set_tree t"  "splay a' t = splay a t"  "t_splay a' t = t_splay a t"
    by blast
  have [arith]: "log \<alpha> 2 > 0" by simp
  show ?thesis using A_ub2[OF assms a'(1)] by(simp add: A_def a' log_divide)
qed


definition Am :: "'a::linorder tree \<Rightarrow> real" where
"Am t = t_splay_max t + \<Phi>(splay_max t) - \<Phi> t"

lemma Am_simp3': "\<lbrakk> c<b; bst rr; rr \<noteq> Leaf\<rbrakk> \<Longrightarrow>
  Am (Node l c (Node rl b rr)) =
  (case splay_max rr of Node rrl _ rrr \<Rightarrow>
   Am rr + \<phi> rrl (Node l c rl) + \<phi> l rl - \<phi> rl rr - \<phi> rrl rrr + 1)"
by(auto simp: Am_def \<phi>_def size_if_splay_max algebra_simps real_of_nat_Suc neq_Leaf_iff split: tree.split)

lemma Am_ub: "\<lbrakk> bst t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> Am t \<le> log \<alpha> ((size1 t)/2)"
proof(induction t rule: splay_max.induct)
  case 1 thus ?case by (simp)
next
  case 2 thus ?case by (simp add: Am_def)
next
  case (3 l b rl c)
  thus ?case
    using nl2[of 1 "size1 rl" "size1 l"] log_le_cancel_iff[of \<alpha> 2 "2 + real(size rl)"]
    by (auto simp: real_of_nat_Suc Am_def \<phi>_def log_divide field_simps
      simp del: log_le_cancel_iff)
next
  case (4 l b rl c rrl d rrr)
  let ?rr = "Node rrl d rrr"
  obtain l' u r' where sp: "splay_max ?rr = Node l' u r'"
    using splay_max_Leaf_iff tree.exhaust by blast
  hence 1: "real(size rrl) + real(size rrr) = real(size l') + real(size r')"
    using size_splay_max[of ?rr] by(simp)
  let ?l = "real (size1 l)" let ?rl = "real (size1 rl)"
  let ?l' = "real (size1 l')" let ?r' = "real (size1 r')"
  have "1 + log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l + ?rl) + \<beta> * log \<alpha> (?l' + ?l + ?rl) \<le>
        \<beta> * log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?rl + ?r') + log \<alpha> (?l' + ?rl + ?r' + ?l)" (is "?L\<le>?R")
  proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
    show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A2[of ?r' ?l' ?rl ?l]
    by(simp add: powr_add add.commute add.left_commute mult.commute[of \<beta>] powr_powr[symmetric])
  qed
  thus ?case using 4 sp 1
    by(auto simp add: Am_simp3' real_of_nat_Suc \<phi>_def log_divide algebra_simps)
qed

lemma Am_ub3: assumes "bst t" shows "Am t \<le> log \<alpha> (size1 t)"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: Am_def)
next
  assume "t \<noteq> Leaf"
  have [arith]: "log \<alpha> 2 > 0" by simp
  show ?thesis using Am_ub[OF assms `t \<noteq> Leaf`] by(simp add: Am_def log_divide)
qed

end


subsection "Optimal Interpretation"

lemma mult_root_eq_root:
  "n>0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> root n x * y = root n (x * (y ^ n))"
by(simp add: real_root_mult real_root_pos2)

lemma mult_root_eq_root2:
  "n>0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> y * root n x = root n ((y ^ n) * x)"
by(simp add: real_root_mult real_root_pos2)

lemma powr_inverse_numeral:
  "0 < x \<Longrightarrow> x powr (1 / numeral n) = root (numeral n) x"
by (simp add: root_powr_inverse)

lemmas root_simps = mult_root_eq_root mult_root_eq_root2 powr_inverse_numeral


lemma nl31: "\<lbrakk> (l'::real) \<ge> 1; r' \<ge> 1; lr \<ge> 1; r \<ge> 1 \<rbrakk> \<Longrightarrow>
  4 * (l' + r') * (lr + r) \<le> (l' + lr + r' + r)^2"
by (sos_cert "(((A<0 * R<1) + (R<1 * (R<1 * [r + ~1*l' + lr + ~1*r']^2))))")

lemma nl32: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "lr \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r') * (lr + r) * (lr + r' + r) \<le> (l' + lr + r' + r)^3"
proof -
  have 1: "lr + r' + r \<le> l' + lr + r' + r" using assms by arith
  have 2: "0 \<le> (l' + lr + r' + r)^2" by (rule zero_le_power2)
  have 3: "0 \<le> lr + r' + r" using assms by arith
  from mult_mono[OF nl31[OF assms] 1 2 3] show ?thesis
    by(simp add: ac_simps numeral_eq_Suc)
qed

lemma nl3: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "lr \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r')^2 * (lr + r) * (lr + r' + r)
       \<le> (l' + lr + r') * (l' + lr + r' + r)^3"
proof-
  have 1: "l' + r' \<le> l' + lr + r'" using assms by arith
  have 2: "0 \<le> (l' + lr + r' + r)^3" using assms by simp
  have 3: "0 \<le> l' + r'" using assms by arith
  from mult_mono[OF nl32[OF assms] 1 2 3] show ?thesis
    unfolding power2_eq_square by (simp only: ac_simps)
qed


lemma nl41: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "ll \<ge> 1" "r \<ge> 1"
shows "4 * (l' + ll) * (r' + r) \<le> (l' + ll + r' + r)^2"
using assms by (sos_cert "(((A<0 * R<1) + (R<1 * (R<1 * [r + ~1*l' + ~1*ll + r']^2))))")

lemma nl42: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "ll \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r') * (l' + ll) * (r' + r) \<le> (l' + ll + r' + r)^3"
proof -
  have 1: "l' + r' \<le> l' + ll + r' + r" using assms by arith
  have 2: "0 \<le> (l' + ll + r' + r)^2" by (rule zero_le_power2)
  have 3: "0 \<le> l' + r'" using assms by arith
  from mult_mono[OF nl41[OF assms] 1 2 3] show ?thesis
    by(simp add: ac_simps numeral_eq_Suc del: distrib_right_numeral)
qed

lemma nl4: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "ll \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r')^2 * (l' + ll) * (r' + r)
    \<le> (l' + ll + r') * (l' + ll + r' + r)^3"
proof-
  have 1: "l' + r' \<le> l' + ll + r'" using assms by arith
  have 2: "0 \<le> (l' + ll + r' + r)^3" using assms by simp
  have 3: "0 \<le> l' + r'" using assms by arith
  from mult_mono[OF nl42[OF assms] 1 2 3] show ?thesis
    unfolding power2_eq_square by (simp only: ac_simps)
qed

lemma cancel: "x>(0::real) \<Longrightarrow> c * x ^ 2 * y * z \<le> u * v \<Longrightarrow> c * x ^ 3 * y * z \<le> x * u * v"
by(simp add: power2_eq_square power3_eq_cube)

interpretation S34: Splay_Analysis "root 3 4" "1/3"
proof
  case goal2 thus ?case
    by(simp add: root_simps)
      (auto simp: powr_numeral numeral_eq_Suc split_mult_pos_le intro!: mult_mono)
next
  case goal3 thus ?case by(simp add: root_simps cancel nl3)
next
  case goal4 thus ?case by(simp add: root_simps cancel nl4)
qed simp


lemma log4_log2: "log 4 x = log 2 x / 2"
proof -
  have "log 4 x = log (2^2) x" by simp
  also have "\<dots> = log 2 x / 2" by(simp only: log_base_pow)
  finally show ?thesis .
qed

declare log_base_root[simp] real_of_nat_Suc[simp]

lemma A34_ub: assumes "bst t"
shows "S34.A a t \<le> (3/2) * log 2 (size1 t)"
proof -
  have "S34.A a t \<le> log (root 3 4) (size1 t)" by(rule S34.A_ub3[OF assms])
  also have "\<dots> = (3/2) * log 2 (size t + 1)" by(simp add: log4_log2)
  finally show ?thesis by simp
qed

lemma Am34_ub: assumes "bst t"
shows "S34.Am t \<le> (3/2) * log 2 (size1 t)"
proof -
  have "S34.Am t \<le> log (root 3 4) (size1 t)" by(rule S34.Am_ub3[OF assms])
  also have "\<dots> = (3/2) * log 2 (size1 t)" by(simp add: log4_log2)
  finally show ?thesis by simp
qed

subsection "Overall analysis"

fun t_delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_delete a Leaf = 0" |
"t_delete a t = t_splay a t + (case splay a t of
  Node l x r \<Rightarrow>
    if x=a then case l of Leaf \<Rightarrow> 0 | _ \<Rightarrow> t_splay_max l
    else 0)"

datatype 'a op\<^sub>s\<^sub>t = Splay 'a | Insert 'a | Delete 'a

fun nxt\<^sub>s\<^sub>t :: "'a::linorder op\<^sub>s\<^sub>t \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"nxt\<^sub>s\<^sub>t (Splay a) t = splay a t" |
"nxt\<^sub>s\<^sub>t (Insert a) t = Splay_Tree.insert a t" |
"nxt\<^sub>s\<^sub>t (Delete a) t = Splay_Tree.delete a t"

fun t\<^sub>s\<^sub>t :: "'a::linorder op\<^sub>s\<^sub>t \<Rightarrow> 'a tree \<Rightarrow> real" where
"t\<^sub>s\<^sub>t (Splay a) t = t_splay a t" |
"t\<^sub>s\<^sub>t (Insert a) t = t_splay a t" |
"t\<^sub>s\<^sub>t (Delete a) t = t_delete a t"

interpretation ST: amor
where init = Leaf and nxt = nxt\<^sub>s\<^sub>t and inv = bst
and t = t\<^sub>s\<^sub>t and \<Phi> = S34.\<Phi>
and U = "\<lambda>f t. case f of
  Splay _ \<Rightarrow> (3/2) * log 2 (size1 t) |
  Insert _ \<Rightarrow> 2 * log 2 (size1 t) + 1/2 |
  Delete _ \<Rightarrow> 3 * log 2 (size1 t)"
proof
  case goal1 show ?case by simp
next
  case goal2 show ?case
  proof (cases f)
    case (Splay a)
    with bst_splay[OF goal2, of a] show ?thesis by (auto split: tree.split)
  next
    case (Insert a)
    with bst_splay[OF goal2, of a] show ?thesis
      by (auto simp: splay_bstL[OF goal2] splay_bstR[OF goal2] split: tree.split)
  next
    case (Delete a)[simp]
    with goal2 show ?thesis by(simp add: bst_delete)
  qed
next
  case goal3 show ?case
    by(induction s)(simp_all add: S34.\<phi>_def)
next
  case goal4 show ?case by simp
next
  case goal5
  show ?case (is "?l \<le> ?r")
  proof(cases f)
    case (Splay a)
    thus ?thesis using S34.A_ub3[OF goal5] by(simp add: S34.A_def log4_log2)
  next
    case (Insert a)[simp]
    show ?thesis
    proof cases
      assume "s = Leaf" thus ?thesis by(simp add: S34.\<phi>_def log4_log2)
    next
      assume "s \<noteq> Leaf"
      then obtain l e r where [simp]: "splay a s = Node l e r"
        by (metis tree.exhaust splay_Leaf_iff)
      let ?t = "real(t_splay a s)"
      let ?Plr = "S34.\<Phi> l + S34.\<Phi> r"  let ?Ps = "S34.\<Phi> s"
      let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
      have opt: "?t + S34.\<Phi> (splay a s) - ?Ps  \<le> 3/2 * log 2 (real (size1 s))"
        using S34.A_ub3[OF goal5, simplified S34.A_def, of a]
        by (simp add: log4_log2)
      from less_linear[of e a]
      show ?thesis
      proof (elim disjE)
        assume "e=a"
        have nneg: "log 2 (1 + real (size s)) \<ge> 0" by simp
        thus ?thesis using `s \<noteq> Leaf` opt `e=a`
          apply(simp add: field_simps) using nneg by arith
      next
        let ?L = "log 2 (real(size1 l) + 1)"
        assume "e<a" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?L / 2 + ?LR / 2"
          using  `s \<noteq> Leaf` `e<a` by(simp add: S34.\<phi>_def log4_log2)
        also have "?t + ?Plr - ?Ps \<le> log 2 ?slr"
          using opt size_splay[of a s,symmetric]
          by(simp add: S34.\<phi>_def log4_log2)
        also have "?L/2 \<le> log 2 ?slr / 2" by(simp)
        also have "?LR/2 \<le> log 2 ?slr / 2 + 1/2"
        proof -
          have "?LR/2 \<le> log 2 (2 * ?slr) / 2" by simp
          also have "\<dots> \<le> log 2 ?slr / 2 + 1/2"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a s,symmetric] by simp
      next
        let ?R = "log 2 (2 + real(size r))"
        assume "a<e" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?R / 2 + ?LR / 2"
          using  `s \<noteq> Leaf` `a<e` by(simp add: S34.\<phi>_def log4_log2)
        also have "?t + ?Plr - ?Ps \<le> log 2 ?slr"
          using opt size_splay[of a s,symmetric]
          by(simp add: S34.\<phi>_def log4_log2)
        also have "?R/2 \<le> log 2 ?slr / 2" by(simp)
        also have "?LR/2 \<le> log 2 ?slr / 2 + 1/2"
        proof -
          have "?LR/2 \<le> log 2 (2 * ?slr) / 2" by simp
          also have "\<dots> \<le> log 2 ?slr / 2 + 1/2"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a s,symmetric] by simp
      qed
    qed
  next
    case (Delete a)[simp]
    show ?thesis
    proof (cases s)
      case Leaf thus ?thesis by(simp add: S34.\<phi>_def log4_log2)
    next
      case (Node ls x rs)[simp]
      then obtain l e r where sp[simp]: "splay a (Node ls x rs) = Node l e r"
        by (metis tree.exhaust splay_Leaf_iff)
      let ?t = "real(t_splay a s)"
      let ?Plr = "S34.\<Phi> l + S34.\<Phi> r"  let ?Ps = "S34.\<Phi> s"
      let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
      let ?lslr = "log 2 (2 + (real (size ls) + real (size rs)))"
      have "?lslr \<ge> 0" by simp
      have opt: "?t + S34.\<Phi> (splay a s) - ?Ps  \<le> 3/2 * log 2 (real (size1 s))"
        using S34.A_ub3[OF goal5, simplified S34.A_def, of a]
        by (simp add: log4_log2 field_simps)
      show ?thesis
      proof (cases "e=a")
        case False thus ?thesis
        using opt apply(simp add: field_simps) using `?lslr \<ge> 0` by arith
      next
        case True[simp]
        show ?thesis
        proof (cases l)
          case Leaf
          have "S34.\<phi> Leaf r \<ge> 0" by(simp add: S34.\<phi>_def)
          thus ?thesis
            using Leaf opt apply(simp add: field_simps)
            using `?lslr \<ge> 0` by arith
        next
          case (Node ll y lr)
          then obtain l' y' r' where [simp]:
            "splay_max (Node ll y lr) = Node l' y' r'"
            using splay_max_Leaf_iff tree.exhaust by blast
          have "bst l" using bst_splay[OF goal5, of a] by simp
          have "S34.\<Phi> r' \<ge> 0" apply (induction r') by (auto simp add: S34.\<phi>_def)
          have optm: "real(t_splay_max l) + S34.\<Phi> (splay_max l) - S34.\<Phi> l  \<le> 3/2 * log 2 (real (size1 l))"
            using S34.Am_ub3[OF `bst l`, simplified S34.Am_def]
            by (simp add: log4_log2 field_simps Node)
          have 1: "log 4 (2+(real(size l')+real(size r))) \<le> log 4 (2+(real(size l)+real(size r)))"
            using size_splay_max[of l] Node by simp
          have 2: "log 4 (2 + (real (size l') + real (size r'))) \<ge> 0" by simp
          have 3: "S34.\<phi> l' r \<le> S34.\<phi> l' r' + S34.\<phi> l r"
            apply(simp add: S34.\<phi>_def) using 1 2 by arith
          have 4: "log 2 (2 + (real(size ll) + real(size lr))) \<le> ?lslr"
            using size_if_splay[OF sp] Node by simp
          show ?thesis using add_mono[OF opt optm] Node 3
            apply(simp add: field_simps) using 4 `S34.\<Phi> r' \<ge> 0` by arith
        qed
      qed
    qed
  qed
qed

end
