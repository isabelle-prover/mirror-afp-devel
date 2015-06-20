theory Splay_Tree
imports "~~/src/HOL/Library/Tree"
begin

section "Splay Tree"

text{* Splay trees were invented by Sleator and
Tarjan~\cite{SleatorT-JACM85}. *}

text{* This compensates for an incompleteness of the partial order prover: *}
setup {*
let

fun prp t thm = Thm.prop_of thm = t;

val eq_False_if_not = @{thm eq_False} RS iffD2

fun prove_less_False ctxt ((less as Const(_,T)) $ r $ s) =
  let val prems = Simplifier.prems_of ctxt;
      val le = Const (@{const_name less_eq}, T);
      val t = HOLogic.mk_Trueprop(le $ s $ r);
  in case find_first (prp t) prems of
       NONE =>
         let val t = HOLogic.mk_Trueprop(less $ s $ r)
         in case find_first (prp t) prems of
              NONE => NONE
            | SOME thm => SOME(mk_meta_eq((thm RS @{thm less_not_sym}) RS eq_False_if_not))
         end
     | SOME thm => NONE
  end;

fun add_simprocs procs thy =
  map_theory_simpset (fn ctxt => ctxt
    addsimprocs (map (fn (name, raw_ts, proc) =>
      Simplifier.simproc_global thy name raw_ts proc) procs)) thy;

in
  add_simprocs [
       ("less False", ["(x::'a::order) < y"], prove_less_False) ]
end
*}

subsection "Function @{text splay}"

function splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"splay a Leaf = Leaf" |
"splay a (Node l a r) = Node l a r" |
"a<b \<Longrightarrow> splay a (Node (Node ll a lr) b r) = Node ll a (Node lr b r)" |
"a<b \<Longrightarrow> splay a (Node Leaf b r) = Node Leaf b r" |
"a<c \<Longrightarrow> a<b \<Longrightarrow> splay a (Node (Node Leaf b lr) c r) = Node Leaf b (Node lr c r)" |
"a<c \<Longrightarrow> a<b \<Longrightarrow> ll \<noteq> Leaf \<Longrightarrow>
 splay a (Node (Node ll b lr) c r) =
 (case splay a ll of Node lll u llr \<Rightarrow> Node lll u (Node llr b (Node lr c r)))" |
"a<c \<Longrightarrow> b<a \<Longrightarrow> splay a (Node (Node ll b Leaf) c r) = Node ll b (Node Leaf c r)" |
"a<c \<Longrightarrow> b<a \<Longrightarrow> lr \<noteq> Leaf \<Longrightarrow>
 splay a (Node (Node ll b lr) c r) =
 (case splay a lr of Node lrl u lrr \<Rightarrow> Node (Node ll b lrl) u (Node lrr c r))" |
"b<a \<Longrightarrow> splay a (Node l b (Node rl a rr)) = Node (Node l b rl) a rr" |
"b<a \<Longrightarrow> splay a (Node l b Leaf) = Node l b Leaf" |
"c<a \<Longrightarrow> a<b \<Longrightarrow>  rl \<noteq> Leaf \<Longrightarrow>
 splay a (Node l c (Node rl b rr)) =
 (case splay a rl of Node rll u rlr \<Rightarrow> Node (Node l c rll) u (Node rlr b rr))" |
"c<a \<Longrightarrow> a<b \<Longrightarrow> splay a (Node l c (Node Leaf b rr)) = Node (Node l c Leaf) b rr" |
"c<a \<Longrightarrow> b<a \<Longrightarrow> splay a (Node l c (Node rl b Leaf)) = Node (Node l c rl) b Leaf" |
"c<a \<Longrightarrow> b<a \<Longrightarrow>  rr \<noteq> Leaf \<Longrightarrow>
 splay a (Node l c (Node rl b rr)) =
 (case splay a rr of Node rrl u rrr \<Rightarrow> Node (Node (Node l c rl) b rrl) u rrr)"
apply(atomize_elim)
apply(auto)
(* 1 subgoal *)
apply (subst (asm) neq_Leaf_iff)
apply(auto)
apply (metis tree.exhaust le_less_linear less_linear)+
done

termination splay
by lexicographic_order

lemma splay_induct_old: (* until all old proofs have been updated *)
  "\<lbrakk>\<And>a. P a \<langle>\<rangle>;
 \<And>a cl c cr.
    \<lbrakk>\<And>x21 x22 x23. \<lbrakk>a \<noteq> c; a < c; cl = \<langle>x21, x22, x23\<rangle>; a \<noteq> x22; a < x22; x21 \<noteq> \<langle>\<rangle>\<rbrakk> \<Longrightarrow> P a x21;
     \<And>x21 x22 x23. \<lbrakk>a \<noteq> c; a < c; cl = \<langle>x21, x22, x23\<rangle>; a \<noteq> x22; \<not> a < x22; x23 \<noteq> \<langle>\<rangle>\<rbrakk> \<Longrightarrow> P a x23;
     \<And>x21 x22 x23. \<lbrakk>a \<noteq> c; \<not> a < c; cr = \<langle>x21, x22, x23\<rangle>; a \<noteq> x22; a < x22; x21 \<noteq> \<langle>\<rangle>\<rbrakk> \<Longrightarrow> P a x21;
     \<And>x21 x22 x23. \<lbrakk>a \<noteq> c; \<not> a < c; cr = \<langle>x21, x22, x23\<rangle>; a \<noteq> x22; \<not> a < x22; x23 \<noteq> \<langle>\<rangle>\<rbrakk> \<Longrightarrow> P a x23\<rbrakk>
    \<Longrightarrow> P a \<langle>cl, c, cr\<rangle>\<rbrakk>
\<Longrightarrow> P a t"
by induction_schema (pat_completeness, lexicographic_order)

lemma splay_code: "splay a (Node cl c cr) =
  (if a=c
   then Node cl c cr
   else if a < c
        then case cl of
          Leaf \<Rightarrow> Node cl c cr |
          Node bl b br \<Rightarrow>
            (if a=b then Node bl a (Node br c cr)
             else if a < b
                  then if bl = Leaf then Node bl b (Node br c cr)
                       else case splay a bl of
                         Node al a' ar \<Rightarrow> Node al a' (Node ar b (Node br c cr))
                  else if br = Leaf then Node bl b (Node br c cr)
                       else case splay a br of
                         Node al a' ar \<Rightarrow> Node (Node bl b al) a' (Node ar c cr))
        else case cr of
          Leaf \<Rightarrow> Node cl c cr |
          Node bl b br \<Rightarrow>
            (if a=b then Node (Node cl c bl) a br
             else if a < b
                  then if bl = Leaf then Node (Node cl c bl) b br
                       else case splay a bl of
                         Node al a' ar \<Rightarrow> Node (Node cl c al) a' (Node ar b br)
                  else if br=Leaf then Node (Node cl c bl) b br
                       else case splay a br of
                         Node al a' ar \<Rightarrow> Node (Node (Node cl c bl) b al) a' ar))"
by(auto split: tree.split)

lemma splay_Leaf_iff[simp]: "(splay a t = Leaf) = (t = Leaf)"
apply(induction a t rule: splay.induct)
apply auto
 apply(auto split: tree.splits)
done

lemma size_splay[simp]: "size (splay a t) = size t"
apply(induction a t rule: splay.induct)
apply auto
 apply(force split: tree.split)+
done

lemma size_if_splay: "splay a t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay tree.size(4))

lemma splay_not_Leaf: "t \<noteq> Leaf \<Longrightarrow> \<exists>l x r. splay a t = Node l x r"
by (metis neq_Leaf_iff splay_Leaf_iff)

lemma set_splay: "set_tree(splay a t) = set_tree t"
proof(induction a t rule: splay.induct)
  case (6 a)
  with splay_not_Leaf[OF 6(3), of a] show ?case by(fastforce)
next
  case (8 a)
  with splay_not_Leaf[OF 8(3), of a] show ?case by(fastforce)
next
  case (11 _ a)
  with splay_not_Leaf[OF 11(3), of a] show ?case by(fastforce)
next
  case (14 _ a)
  with splay_not_Leaf[OF 14(3), of a] show ?case by(fastforce)
qed auto

lemma splay_bstL: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree l \<Longrightarrow> x < a"
apply(induction a t arbitrary: l x r rule: splay.induct)
apply (auto split: tree.splits)
apply auto
done

lemma splay_bstR: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree r \<Longrightarrow> a < x"
apply(induction a t arbitrary: l e x r rule: splay.induct)
apply auto
apply (fastforce split: tree.splits)+
done

lemma bst_splay: "bst t \<Longrightarrow> bst(splay a t)"
proof(induction a t rule: splay.induct)
  case (6 a _ _ ll)
  with splay_not_Leaf[OF 6(3), of a] set_splay[of a ll,symmetric]
  show ?case by (fastforce)
next
  case (8 a _ _ t)
  with splay_not_Leaf[OF 8(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
next
  case (11 _ a _ t)
  with splay_not_Leaf[OF 11(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
next
  case (14 _ a _ t)
  with splay_not_Leaf[OF 14(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
qed auto

lemma splay_to_root: "\<lbrakk> bst t;  splay a t = t' \<rbrakk> \<Longrightarrow>
  a \<in> set_tree t \<longleftrightarrow> (\<exists>l r. t' = Node l a r)"
proof(induction a t arbitrary: t' rule: splay.induct)
  case (6 a)
  with splay_not_Leaf[OF 6(3), of a] show ?case by auto
next
  case (8 a)
  with splay_not_Leaf[OF 8(3), of a] show ?case by auto
next
  case (11 _ a)
  with splay_not_Leaf[OF 11(3), of a] show ?case by auto
next
  case (14 _ a)
  with splay_not_Leaf[OF 14(3), of a] show ?case by auto
qed fastforce+


subsection "Is-in Test"

text{* To test if an element @{text a} is in @{text t}, first perform
@{term"splay a t"}, then check if the root is @{text a}. One could
put this into one function that returns both a new tree and the test result. *}

(* FIXME mv *)
definition is_root :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool" where
"is_root a t = (case t of Leaf \<Rightarrow> False | Node _ x _ \<Rightarrow> x = a)"

lemma is_root_splay: "bst t \<Longrightarrow> is_root a (splay a t) \<longleftrightarrow> a \<in> set_tree t"
by(auto simp add: is_root_def splay_to_root split: tree.split)


subsection "Function @{text insert}"

context
begin

qualified fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert a t =  (if t = Leaf then Node Leaf a Leaf
  else case splay a t of
    Node l a' r \<Rightarrow> if a=a' then Node l a r
      else if a<a' then Node l a (Node Leaf a' r) else Node (Node l a' Leaf) a r)"

end

lemma set_insert: "set_tree(Splay_Tree.insert a t) = insert a (set_tree t)"
apply(cases t)
 apply simp
using set_splay[of a t]
by(simp split: tree.split) fastforce

lemma bst_insert: "bst t \<Longrightarrow> bst(Splay_Tree.insert a t)"
apply(cases t)
 apply simp
using bst_splay[of t a] splay_bstL[of t a] splay_bstR[of t a]
by(auto simp: ball_Un split: tree.split)


subsection "Function @{text splay_max}"

fun splay_max :: "'a::linorder tree \<Rightarrow> 'a tree" where
"splay_max Leaf = Leaf" |
"splay_max (Node l b Leaf) = Node l b Leaf" |
"splay_max (Node l b (Node rl c rr)) =
  (if rr = Leaf then Node (Node l b rl) c Leaf
   else case splay_max rr of
     Node rrl m rrr \<Rightarrow> Node (Node (Node l b rl) c rrl) m rrr)"

lemma splay_max_Leaf_iff[simp]: "(splay_max t = Leaf) = (t = Leaf)"
apply(induction t rule: splay_max.induct)
  apply(auto split: tree.splits)
done

lemma splay_max_code: "splay_max t = (case t of
  Leaf \<Rightarrow> t |
  Node l b r \<Rightarrow> (case r of
    Leaf \<Rightarrow> t |
    Node rl c rr \<Rightarrow>
      (if rr=Leaf then Node (Node l b rl) c rr
       else case splay_max rr of
              Node rrl u rrr \<Rightarrow> Node (Node (Node l b rl) c rrl) u rrr)))"
by(auto simp: neq_Leaf_iff split: tree.split)

lemma size_splay_max: "size(splay_max t) = size t"
apply(induction t rule: splay_max.induct)
  apply(simp)
 apply(simp)
apply(clarsimp split: tree.split)
done

lemma size_if_splay_max: "splay_max t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay_max tree.size(4))

lemma set_splay_max: "set_tree(splay_max t) = set_tree t"
apply(induction t rule: splay_max.induct)
   apply(simp)
  apply(simp)
apply(force split: tree.split)
done

lemma bst_splay_max: "bst t \<Longrightarrow> bst (splay_max t)"
proof(induction t rule: splay_max.induct)
  case (3 l b rl c rr)
  { fix rrl' d' rrr'
    have "splay_max rr = Node rrl' d' rrr'
       \<Longrightarrow> !x : set_tree(Node rrl' d' rrr'). c < x" 
      using "3.prems" set_splay_max[of rr]
      by (clarsimp split: tree.split simp: ball_Un)
  }
  with 3 show ?case by (fastforce split: tree.split simp: ball_Un)
qed auto

lemma splay_max_Leaf: "splay_max t = Node l a r \<Longrightarrow> r = Leaf"
by(induction t arbitrary: l rule: splay_max.induct)
  (auto split: tree.splits if_splits)

text{* For sanity purposes only: *}

lemma splay_max_eq_splay:
  "bst t \<Longrightarrow> \<forall>x \<in> set_tree t. x \<le> a \<Longrightarrow> splay_max t = splay a t"
proof(induction a t rule: splay.induct)
  case (2 a l r)
  show ?case
  proof (cases r)
    case Leaf with 2 show ?thesis by simp
  next
    case Node with 2 show ?thesis by(auto)
  qed
qed (auto simp: neq_Leaf_iff)

lemma splay_max_eq_splay_ex: assumes "bst t" shows "\<exists>a. splay_max t = splay a t"
proof(cases t)
  case Leaf thus ?thesis by simp
next
  case Node
  hence "splay_max t = splay (Max(set_tree t)) t"
    using assms by (auto simp: splay_max_eq_splay)
  thus ?thesis by auto
qed


subsection "Function @{text delete}"

context
begin

qualified definition delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete a t = (if t=Leaf then Leaf
  else case splay a t of Node l a' r \<Rightarrow>
    if a=a'
    then if l = Leaf then r else case splay_max l of Node l' m r' \<Rightarrow> Node l' m r
    else Node l a' r)"

lemma set_delete: assumes "bst t"
shows "set_tree (delete a t) = set_tree t - {a}"
proof(cases t)
  case Leaf thus ?thesis by(simp add: delete_def)
next
  case (Node l x r)
  obtain l' x' r' where sp[simp]: "splay a (Node l x r) = Node l' x' r'"
    by (metis neq_Leaf_iff splay_Leaf_iff)
  show ?thesis
  proof cases
    assume [simp]: "x' = a"
    show ?thesis
    proof cases
      assume "l' = Leaf"
      thus ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
        by(simp add: delete_def split: tree.split prod.split)(fastforce)
    next
      assume "l' \<noteq> Leaf"
      moreover then obtain l'' m r'' where "splay_max l' = Node l'' m r''"
        using splay_max_Leaf_iff tree.exhaust by blast
      moreover have "a \<notin> set_tree l'"
        by (metis (no_types) Node assms less_irrefl sp splay_bstL)
      ultimately show ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          splay_max_Leaf[of l' l'' m r''] set_splay_max[of l']
        by(clarsimp simp: delete_def split: tree.split) auto
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms set_splay[of a "Node l x r"] splay_to_root[OF _ sp]
      by (simp add: delete_def)
  qed
qed

lemma bst_delete: assumes "bst t" shows "bst (delete a t)"
proof(cases t)
  case Leaf thus ?thesis by(simp add: delete_def)
next
  case (Node l x r)
  obtain l' x' r' where sp[simp]: "splay a (Node l x r) = Node l' x' r'"
    by (metis neq_Leaf_iff splay_Leaf_iff)
  show ?thesis
  proof cases
    assume [simp]: "x' = a"
    show ?thesis
    proof cases
      assume "l' = Leaf"
      thus ?thesis using Node assms bst_splay[of "Node l x r" a]
        by(simp add: delete_def split: tree.split prod.split)
    next
      assume "l' \<noteq> Leaf"
      thus ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          bst_splay_max[of l'] set_splay_max[of l']
        by(clarsimp simp: delete_def split: tree.split)
          (metis (no_types) insertI1 less_trans)
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms bst_splay[of "Node l x r" a]
      by(auto simp: delete_def split: tree.split prod.split)
  qed
qed

end

end
