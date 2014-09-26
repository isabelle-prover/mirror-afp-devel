theory Splay_Tree_Analysis_Base
imports Complex_Main "../Splay_Tree/Splay_Tree"
begin

section "Splay Tree Analysis Basics"

declare size1_def[simp]

abbreviation "\<phi> t == log 2 (size1 t)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l a r) = \<Phi> l + \<Phi> r + \<phi> (Node l a r)"

lemma add_log_log1:
  assumes "x > 0" "y > 0" shows "1 + log 2 x + log 2 y < 2 * log 2 (x+y)"
proof -
  have 1: "2*x*y < (x+y)^2" using assms
    by(simp add: numeral_eq_Suc algebra_simps add_pos_pos)
  show ?thesis
    apply(rule powr_less_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add log_powr[symmetric] powr_numeral)
qed


subsection "Time"

fun t_splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_splay a Leaf = 1" |
"t_splay a (Node l b r) =
  (if a=b
   then 1
   else if a < b
        then case l of
          Leaf \<Rightarrow> 1 |
          Node ll c lr \<Rightarrow>
            (if a=c then 1
             else if a < c then if ll = Leaf then 1 else t_splay a ll + 1
                  else if lr = Leaf then 1 else t_splay a lr + 1)
        else case r of
          Leaf \<Rightarrow> 1 |
          Node rl c rr \<Rightarrow>
            (if a=c then 1
             else if a < c then if rl = Leaf then 1 else t_splay a rl + 1
                  else if rr = Leaf then 1 else t_splay a rr + 1))"

lemma t_splay_simps[simp]:
  "t_splay a (Node l a r) = 1"
  "a<b \<Longrightarrow> t_splay a (Node Leaf b r) = 1"
  "a<b \<Longrightarrow> t_splay a (Node (Node ll a lr) b r) = 1"
  "a<b \<Longrightarrow> a<c \<Longrightarrow> t_splay a (Node (Node ll c lr) b r) =
   (if ll = Leaf then 1 else t_splay a ll + 1)"
  "a<b \<Longrightarrow> c<a \<Longrightarrow> t_splay a (Node (Node ll c lr) b r) =
   (if lr = Leaf then 1 else t_splay a lr + 1)"
  "b<a \<Longrightarrow> t_splay a (Node l b Leaf) = 1"
  "b<a \<Longrightarrow> t_splay a (Node l b (Node rl a rr)) = 1"
  "b<a \<Longrightarrow> a<c \<Longrightarrow> t_splay a (Node l b (Node rl c rr)) =
  (if rl=Leaf then 1 else t_splay a rl + 1)"
  "b<a \<Longrightarrow> c<a \<Longrightarrow> t_splay a (Node l b (Node rl c rr)) =
  (if rr=Leaf then 1 else t_splay a rr + 1)"
by auto

declare t_splay.simps(2)[simp del]

fun t_splay_max :: "'a::linorder tree \<Rightarrow> nat" where
"t_splay_max Leaf = 1" |
"t_splay_max (Node l b Leaf) = 1" |
"t_splay_max (Node l b (Node rl c rr)) = (if rr=Leaf then 1 else t_splay_max rr + 1)"

definition t_delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_delete a t = (if t = Leaf then 0 else t_splay a t + (case splay a t of
  Node l x r \<Rightarrow>
    if x=a then case l of Leaf \<Rightarrow> 0 | _ \<Rightarrow> t_splay_max l
    else 0))"

lemma ex_in_set_tree: "t \<noteq> Leaf \<Longrightarrow> bst t \<Longrightarrow>
  \<exists>a' \<in> set_tree t. splay a' t = splay a t \<and> t_splay a' t = t_splay a t"
proof(induction a t rule: splay.induct)
  case 1 thus ?case by simp
next
  case (2 a l c r)
  show ?case
  proof cases
    assume "a=c" thus ?thesis using "2.prems" by auto
  next
    assume "a\<noteq>c"
    hence "a<c \<or> c<a" by (metis neqE)
    thus ?thesis
    proof
      assume "a<c"
      show ?thesis
      proof(cases l)
        case Leaf thus ?thesis using `a<c` by(auto)
      next
        case (Node ll b lr)[simp]
        have "b < c" using "2.prems" by (auto)
        show ?thesis
        proof cases
          assume "a=b" thus ?thesis using `a<c` by auto
        next
          assume "a\<noteq>b"
          hence "a<b \<or> b<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<b"
            show ?thesis
            proof cases
              assume "ll = Leaf" thus ?thesis using `a<c` `a<b` `b<c` by(auto)
            next
              assume "ll \<noteq> Leaf"
              hence "splay a ll \<noteq> Leaf" by simp
              then obtain lll u llr where [simp]: "splay a ll = Node lll u llr"
                by (metis tree.exhaust)
              have "bst ll" using "2.prems" by simp
              from "2.IH"(1)[OF `a\<noteq>c` `a<c` Node `a\<noteq>b` `a<b` `ll \<noteq> Leaf` `ll \<noteq> Leaf` `bst ll`]
              obtain e where "e \<in> set_tree ll" "splay e ll = splay a ll" "t_splay e ll = t_splay a ll"
                by blast
              moreover hence "e<b" using "2.prems"(2) by auto
              ultimately show ?thesis using `a<c` `a<b` `b<c` `bst ll` by force
            qed
          next
            assume "b<a" hence "\<not> a<b" by simp
            show ?thesis
            proof cases
              assume "lr = Leaf" thus ?thesis using `a<c` `b<a` by(auto)
            next
              assume "lr \<noteq> Leaf"
              hence "splay a lr \<noteq> Leaf" by simp
              then obtain lrl u lrr where [simp]: "splay a lr = Node lrl u lrr"
                by (metis tree.exhaust)
              have "bst lr" using "2.prems" by simp
              from "2.IH"(2)[OF `a\<noteq>c` `a<c` Node `a\<noteq>b` `\<not>a<b` `lr \<noteq> Leaf` `lr \<noteq> Leaf` `bst lr`]
              obtain e where "e \<in> set_tree lr" "splay e lr = splay a lr" "t_splay e lr = t_splay a lr"
                by blast
              moreover hence "b<e & e<c" using "2.prems"(2) by simp
              ultimately show ?thesis using `a<c` `b<a` `b<c` `bst lr` by force
            qed
          qed
        qed
      qed
    next
      assume "c<a" hence "\<not>a<c" by simp
      show ?thesis
      proof(cases r)
        case Leaf thus ?thesis using `c<a` by(auto)
      next
        case (Node rl b rr)[simp]
        have "c < b" using "2.prems" by (auto)
        show ?thesis
        proof cases
          assume "a=b" thus ?thesis using `c<a` by auto
        next
          assume "a\<noteq>b"
          hence "a<b \<or> b<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<b" hence "\<not> b<a" by simp
            show ?thesis
            proof cases
              assume "rl = Leaf" thus ?thesis using `c<a` `a<b` by(auto)
            next
              assume "rl \<noteq> Leaf"
              hence "splay a rl \<noteq> Leaf" by simp
              then obtain rll u rlr where [simp]: "splay a rl = Node rll u rlr"
                by (metis tree.exhaust)
              have "bst rl" using "2.prems" by simp
              from "2.IH"(3)[OF `a\<noteq>c` `\<not>a<c` Node `a\<noteq>b` `a<b` `rl \<noteq> Leaf` `rl \<noteq> Leaf` `bst rl`]
              obtain e where "e \<in> set_tree rl" "splay e rl = splay a rl" "t_splay e rl = t_splay a rl"
                by blast
              moreover hence "c<e & e<b" using "2.prems"(2) by simp
              ultimately show ?thesis using `c<a` `a<b` `c<b` `bst rl` by force
            qed
          next
            assume "b<a" hence "\<not>a<b" by simp
            show ?thesis
            proof cases
              assume "rr = Leaf" thus ?thesis using `c<a` `b<a` `c<b` by(auto)
            next
              assume "rr \<noteq> Leaf"
              hence "splay a rr \<noteq> Leaf" by simp
              then obtain rrl u rrr where [simp]: "splay a rr = Node rrl u rrr"
                by (metis tree.exhaust)
              have "bst rr" using "2.prems" by simp
              from "2.IH"(4)[OF `a\<noteq>c` `\<not>a<c` Node `a\<noteq>b` `\<not>a<b` `rr \<noteq> Leaf` `rr \<noteq> Leaf` `bst rr`]
              obtain e where "e \<in> set_tree rr" "splay e rr = splay a rr" "t_splay e rr = t_splay a rr"
                by blast
              moreover hence "b<e" using "2.prems"(2) by simp
              ultimately show ?thesis using `c<a` `b<a` `c<b` `bst rr` by force
            qed
          qed
        qed
      qed
    qed
  qed
qed


datatype 'a op\<^sub>s\<^sub>t = Splay 'a | Insert 'a | Delete 'a

fun nxt\<^sub>s\<^sub>t :: "'a::linorder op\<^sub>s\<^sub>t \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"nxt\<^sub>s\<^sub>t (Splay a) t = splay a t" |
"nxt\<^sub>s\<^sub>t (Insert a) t = Splay_Tree.insert a t" |
"nxt\<^sub>s\<^sub>t (Delete a) t = Splay_Tree.delete a t"

fun t\<^sub>s\<^sub>t :: "'a::linorder op\<^sub>s\<^sub>t \<Rightarrow> 'a tree \<Rightarrow> real" where
"t\<^sub>s\<^sub>t (Splay a) t = t_splay a t" |
"t\<^sub>s\<^sub>t (Insert a) t = t_splay a t" |
"t\<^sub>s\<^sub>t (Delete a) t = t_delete a t"

end
