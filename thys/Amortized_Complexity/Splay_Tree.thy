theory Splay_Tree
imports Complex_Main "~~/src/HOL/Library/Tree"
begin

section "Splay Tree"

text{* Splay trees were invented by Sleator and
Tarjan~\cite{SleatorT-JACM85}. *}

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

fun splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"splay a Leaf = Leaf" |
"splay a (Node l b r) =
  (if a=b
   then Node l b r
   else if a < b
        then case l of
          Leaf \<Rightarrow> Node l b r |
          Node ll c lr \<Rightarrow>
            (if a=c then Node ll a (Node lr b r)
             else if a < c
                  then if ll = Leaf then Node ll c (Node lr b r)
                       else case splay a ll of
                         Node lll u llr \<Rightarrow> Node lll u (Node llr c (Node lr b r))
                  else if lr = Leaf then Node ll c (Node lr b r)
                       else case splay a lr of
                         Node lrl u lrr \<Rightarrow> Node (Node ll c lrl) u (Node lrr b r))
        else case r of
          Leaf \<Rightarrow> Node l b r |
          Node rl c rr \<Rightarrow>
            (if a=c then Node (Node l b rl) a rr
             else if a < c
                  then if rl = Leaf then Node (Node l b rl) c rr
                       else case splay a rl of
                         Node rll u rlr \<Rightarrow> Node (Node l b rll) u (Node rlr c rr)
                  else if rr=Leaf then Node (Node l b rl) c rr
                       else case splay a rr of
                         Node rrl u rrr \<Rightarrow> Node (Node (Node l b rl) c rrl) u rrr))"

value "splay (5::int) (Node (Node A 5 B) 10 C)"
value "splay (5::int) (Node (Node (Node A 5 B) 10 C) 15 D)"
value "splay (5::int) (Node (Node A 0 (Node B 5 C)) 10 D)"

value "splay (7::int) (Node L 5 (Node (Node A 6 B) 7 R))"

value "splay (0::int) (Node (Node (Node (Node (Node (Node (Node A 0 B) 1 C) 2 D) 3 E) 4 F) 5 G) 6 H)"

value "splay (74::int) (Node (Node (Node (Node A 70 (Node (Node B 71 (Node C 72 (Node D 73 (Node E 74 F)))) 79 G)) 80 H) 90 I) 100 J)"

value "splay (6::int) (Node (Node A 0 (Node (Node B 1 (Node (Node C 2 (Node D 6 E)) 7 F)) 8 G)) 9 H)"

value "splay (70::int) (Node L 50 (Node A 60 (Node (Node B 70 C) 90 D)))"

lemma splay_simps[simp]:
  "splay a (Node l a r) = Node l a r"
  "a<b \<Longrightarrow> splay a (Node (Node ll a lr) b r) = Node ll a (Node lr b r)"
  "a<b \<Longrightarrow> splay a (Node Leaf b r) = Node Leaf b r"
  "a<b \<Longrightarrow> a\<le>c \<Longrightarrow> splay a (Node (Node Leaf c lr) b r) = Node Leaf c (Node lr b r)"
  "a<b \<Longrightarrow> a<c \<Longrightarrow> splay a ll = Node lll u llr
   \<Longrightarrow> splay a (Node (Node ll c lr) b r) = Node lll u (Node llr c (Node lr b r))"
  "a<b \<Longrightarrow> c<a \<Longrightarrow> splay a (Node (Node ll c Leaf) b r) = Node ll c (Node Leaf b r)"
  "a<b \<Longrightarrow> c<a \<Longrightarrow> splay a lr = Node lrl u lrr
   \<Longrightarrow> splay a (Node (Node ll c lr) b r) = Node (Node ll c lrl) u (Node lrr b r)"
  "b<a \<Longrightarrow> splay a (Node l b (Node rl a rr)) = Node (Node l b rl) a rr"
  "b<a \<Longrightarrow> splay a (Node l b Leaf) = Node l b Leaf"
  "b<a \<Longrightarrow> a<c \<Longrightarrow> splay a rl = Node rll u rlr
   \<Longrightarrow> splay a (Node l b (Node rl c rr)) = Node (Node l b rll) u (Node rlr c rr)"
  "b<a \<Longrightarrow> a<c \<Longrightarrow> splay a (Node l b (Node Leaf c rr)) = Node (Node l b Leaf) c rr"
  "b<a \<Longrightarrow> c\<le>a \<Longrightarrow> splay a (Node l b (Node rl c Leaf)) = Node (Node l b rl) c Leaf"
  "b<a \<Longrightarrow> c<a \<Longrightarrow> splay a rr = Node rrl u rrr
   \<Longrightarrow> splay a (Node l b (Node rl c rr)) = Node (Node (Node l b rl) c rrl) u rrr"
by auto

declare splay.simps(2)[simp del]

lemma splay_Leaf_iff[simp]: "(splay a t = Leaf) = (t = Leaf)"
apply(induction a t rule: splay.induct)
 apply(simp)
apply(subst splay.simps(2))
apply auto
 apply(auto split: tree.splits if_splits)
done

lemma size_splay[simp]: "size (splay a t) = size t"
apply(induction a t rule: splay.induct)
 apply simp
apply (subst splay.simps)
apply auto
 apply(force split: tree.split)+
done

lemma size_if_splay: "splay a t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay tree.size(4))

lemma set_splay: "set_tree(splay a t) = set_tree t"
proof(induction a t rule: splay.induct)
  case 1 thus ?case by simp
next
  case (2 a l b r)
  show ?case
  proof cases
    assume "a=b" thus ?thesis by simp
  next
    assume "a\<noteq>b"
    hence "a<b \<or> b<a" by (metis neqE)
    thus ?thesis
    proof
      assume "a<b"
      show ?thesis
      proof(cases l)
        case Leaf thus ?thesis using `a<b` by simp
      next
        case (Node ll c lr)[simp]
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
              assume "ll = Leaf" thus ?thesis using `a<b` `a<c` by auto
            next
              assume "ll \<noteq> Leaf"
              hence "splay a ll \<noteq> Leaf" by simp
              then obtain lll u llr where [simp]: "splay a ll = Node lll u llr"
                by (metis tree.exhaust)
              from "2.IH"(1)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `a<c` `ll \<noteq> Leaf`]
              show ?thesis using `a<b` `a<c` by auto
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
              from "2.IH"(2)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `\<not>a<c` `lr \<noteq> Leaf`]
              show ?thesis using `a<b` `c<a` by auto
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
              from "2.IH"(3)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `a<c` `rl \<noteq> Leaf`]
              show ?thesis using `b<a` `a<c` by auto
            qed
          next
            assume "c<a" hence "\<not>a<c" by simp
            show ?thesis
            proof cases
              assume "rr = Leaf" thus ?thesis using `b<a` `c<a` by(auto)
            next
              assume "rr \<noteq> Leaf"
              hence "splay a rr \<noteq> Leaf" by simp
              then obtain rrl u rrr where [simp]: "splay a rr = Node rrl u rrr"
                by (metis tree.exhaust)
              from "2.IH"(4)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `\<not>a<c` `rr \<noteq> Leaf`]
              show ?thesis using `b<a` `c<a` by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma splay_bstL: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree l \<Longrightarrow> x < a"
apply(induction a t arbitrary: l x r rule: splay.induct)
 apply simp
apply (subst (asm) splay.simps)
apply (auto split: if_splits tree.splits)
 apply auto
done

lemma splay_bstR: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree r \<Longrightarrow> a < x"
apply(induction a t arbitrary: l e x r rule: splay.induct)
 apply simp
apply (subst (asm) splay.simps)
using [[simp_depth_limit = 3]] apply (fastforce split: if_splits tree.splits)
done

lemma bst_splay: "bst t \<Longrightarrow> bst(splay a t)"
proof(induction a t rule: splay.induct)
  case 1 show ?case by simp
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
        case Leaf thus ?thesis using "2.prems" `a<b` by(auto)
      next
        case (Node ll c lr)[simp]
        have "c < b" using "2.prems" by (auto)
        show ?thesis
        proof cases
          assume "a=c" thus ?thesis using "2.prems" `a<b` by auto
        next
          assume "a\<noteq>c"
          hence "a<c \<or> c<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<c"
            show ?thesis
            proof cases
              assume "ll = Leaf" thus ?thesis using `a<b` `a<c` `c<b` "2.prems" by(auto)
            next
              assume "ll \<noteq> Leaf"
              hence "splay a ll \<noteq> Leaf" by simp
              then obtain lll u llr where [simp]: "splay a ll = Node lll u llr"
                by (metis tree.exhaust)
              have "bst ll" using "2.prems" by simp
              from "2.IH"(1)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `a<c` `ll \<noteq> Leaf` `bst ll`]
              show ?thesis using `a<b` `a<c` `c<b` "2.prems" set_splay[of a ll]
                by auto (metis insertI1 less_trans)+
            qed
          next
            assume "c<a" hence "\<not> a<c" by simp
            show ?thesis
            proof cases
              assume "lr = Leaf" thus ?thesis using `a<b` `c<a` "2.prems" by(auto)
            next
              assume "lr \<noteq> Leaf"
              hence "splay a lr \<noteq> Leaf" by simp
              then obtain lrl u lrr where [simp]: "splay a lr = Node lrl u lrr"
                by (metis tree.exhaust)
              have "bst lr" using "2.prems" by simp
              from "2.IH"(2)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `\<not>a<c` `lr \<noteq> Leaf`]
              show ?thesis using `a<b` `c<a` `c<b` "2.prems" set_splay[of a lr]
                by auto (metis Un_iff insertI1 less_trans)+
            qed
          qed
        qed
      qed
    next
      assume "a>b" hence "\<not>a<b" by simp
      show ?thesis
      proof(cases r)
        case Leaf thus ?thesis using "2.prems" `a>b` by(auto)
      next
        case (Node rl c rr)[simp]
        have "c > b" using "2.prems" by (auto)
        show ?thesis
        proof cases
          assume "a=c" thus ?thesis using "2.prems" `a>b` by auto
        next
          assume "a\<noteq>c"
          hence "a<c \<or> c<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<c"
            show ?thesis
            proof cases
              assume "rl = Leaf" thus ?thesis using `a>b` `a<c` `c>b` "2.prems" by(auto)
            next
              assume "rl \<noteq> Leaf"
              hence "splay a rl \<noteq> Leaf" by simp
              then obtain rll u rlr where [simp]: "splay a rl = Node rll u rlr"
                by (metis tree.exhaust)
              have "bst rl" using "2.prems" by simp
              from "2.IH"(3)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `a<c` `rl \<noteq> Leaf` `bst rl`]
              show ?thesis using `a>b` `a<c` `c>b` "2.prems" set_splay[of a rl]
                by auto (metis Un_iff insertI1 less_trans)+
            qed
          next
            assume "c<a" hence "\<not> a<c" by simp
            show ?thesis
            proof cases
              assume "rr = Leaf" thus ?thesis using `a>b` `c<a` "2.prems" by(auto)
            next
              assume "rr \<noteq> Leaf"
              hence "splay a rr \<noteq> Leaf" by simp
              then obtain rrl u rrr where [simp]: "splay a rr = Node rrl u rrr"
                by (metis tree.exhaust)
              have "bst rr" using "2.prems" by simp
              from "2.IH"(4)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `\<not>a<c` `rr \<noteq> Leaf`]
              show ?thesis using `a>b` `c<a` `c>b` "2.prems" set_splay[of a rr]
                by auto (metis insertI1 less_trans)+
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma splay_to_root: "\<lbrakk> bst t;  splay a t = t' \<rbrakk> \<Longrightarrow>
  a \<in> set_tree t \<longleftrightarrow> (\<exists>l r. t' = Node l a r)"
proof(induction a t arbitrary: t' rule: splay.induct)
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
        case Leaf thus ?thesis using `a<b` "2.prems" by fastforce
      next
        case (Node ll c lr)[simp]
        show ?thesis
        proof cases
          assume "a=c" thus ?thesis using `a<b` "2.prems" by auto
        next
          assume "a\<noteq>c"
          hence "a<c \<or> c<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<c"
            show ?thesis
            proof cases
              assume "ll = Leaf" thus ?thesis using `a<b` `a<c` "2.prems" by auto
            next
              assume "ll \<noteq> Leaf"
              hence "splay a ll \<noteq> Leaf" by simp
              then obtain lll u llr where [simp]: "splay a ll = Node lll u llr"
                by (metis tree.exhaust)
              from "2.IH"(1)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `a<c` `ll \<noteq> Leaf`]
              show ?thesis using `a<b` `a<c` "2.prems" by auto
            qed
          next
            assume "c<a" hence "\<not> a<c" by simp
            show ?thesis
            proof cases
              assume "lr = Leaf" thus ?thesis using `a<b` `c<a` "2.prems" by(auto)
            next
              assume "lr \<noteq> Leaf"
              hence "splay a lr \<noteq> Leaf" by simp
              then obtain lrl u lrr where [simp]: "splay a lr = Node lrl u lrr"
                by (metis tree.exhaust)
              from "2.IH"(2)[OF `a\<noteq>b` `a<b` Node `a\<noteq>c` `\<not>a<c` `lr \<noteq> Leaf`]
              show ?thesis using `a<b` `c<a` "2.prems" by auto
            qed
          qed
        qed
      qed
    next
      assume "b<a" hence "\<not>a<b" by simp
      show ?thesis
      proof(cases r)
        case Leaf thus ?thesis using `b<a` `\<not>a<b` "2.prems" by fastforce
      next
        case (Node rl c rr)[simp]
        show ?thesis
        proof cases
          assume "a=c" thus ?thesis using `b<a` "2.prems" by auto
        next
          assume "a\<noteq>c"
          hence "a<c \<or> c<a" by (metis neqE)
          thus ?thesis
          proof
            assume "a<c" hence "\<not> c<a" by simp
            show ?thesis
            proof cases
              assume "rl = Leaf" thus ?thesis using `b<a` `a<c` "2.prems" by(auto)
            next
              assume "rl \<noteq> Leaf"
              hence "splay a rl \<noteq> Leaf" by simp
              then obtain rll u rlr where [simp]: "splay a rl = Node rll u rlr"
                by (metis tree.exhaust)
              from "2.IH"(3)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `a<c` `rl \<noteq> Leaf`]
              show ?thesis using `b<a` `a<c` "2.prems" by auto
            qed
          next
            assume "c<a" hence "\<not>a<c" by simp
            show ?thesis
            proof cases
              assume "rr = Leaf" thus ?thesis using `b<a` `c<a` "2.prems" by(auto)
            next
              assume "rr \<noteq> Leaf"
              hence "splay a rr \<noteq> Leaf" by simp
              then obtain rrl u rrr where [simp]: "splay a rr = Node rrl u rrr"
                by (metis tree.exhaust)
              from "2.IH"(4)[OF `a\<noteq>b` `\<not>a<b` Node `a\<noteq>c` `\<not>a<c` `rr \<noteq> Leaf`]
              show ?thesis using `b<a` `c<a` "2.prems" by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed


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

fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert a t =  (if t = Leaf then Node Leaf a Leaf
  else case splay a t of
    Node l e r \<Rightarrow> if a=e then Node l e r
      else if a<e then Node l a (Node Leaf e r) else Node (Node l e Leaf) a r)"

hide_const (open) Splay_Tree.insert

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
"splay_max (Node l b (Node rl c Leaf)) = Node (Node l b rl) c Leaf" |
"splay_max (Node l b (Node rl c rr)) = (case splay_max rr of
   Node rrl u rrr \<Rightarrow> Node (Node (Node l b rl) c rrl) u rrr)"

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
 apply fastforce
apply(clarsimp split: tree.split)
done

lemma size_if_splay_max: "splay_max t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay_max tree.size(4))

lemma set_splay_max: "set_tree(splay_max t) = set_tree t"
apply(induction t rule: splay_max.induct)
   apply(simp)
  apply(simp)
 apply fastforce
apply(clarsimp split: tree.split)
by blast

lemma bst_splay_max: "bst t \<Longrightarrow> bst (splay_max t)"
proof(induction t rule: splay_max.induct)
  case (4 l b rl c rrl d rrr)
  { fix rrl' d' rrr'
    have "splay_max (Node rrl d rrr) = Node rrl' d' rrr'
       \<Longrightarrow> !x : set_tree(Node rrl' d' rrr'). c < x" 
      using "4.prems" set_splay_max[of "Node rrl d rrr"]
      by (clarsimp split: tree.split simp: ball_Un)
  }
  with 4 show ?case by (fastforce split: tree.split simp: ball_Un)
qed auto

lemma splay_max_Leaf: "splay_max t = Node l a r \<Longrightarrow> r = Leaf"
by(induction t arbitrary: l rule: splay_max.induct)
  (auto split: tree.splits)

text{* For sanity purposes only: *}

lemma splay_max_eq_splay:
  "bst t \<Longrightarrow> \<forall>x \<in> set_tree t. x \<le> a \<Longrightarrow> splay_max t = splay a t"
proof(induction a t rule: splay.induct)
  case 1 thus ?case by simp
next
  case (2 a l b r)
  have "b = a \<or> b < a" using "2.prems"(2) by auto
  thus ?case
  proof
    assume [simp]: "b = a"
    have "r = Leaf"
      apply(rule ccontr)
      using  "2.prems" by (auto simp: ball_Un neq_Leaf_iff)
    thus ?thesis by simp
  next
    assume "b < a"
    hence "a \<noteq> b" by simp
    show ?thesis
    proof(cases r)
      case Leaf thus ?thesis using `b<a` by(auto)
    next
      case (Node rl c rr)[simp]
      have "c = a \<or> c< a" using "2.prems" by auto
      thus ?thesis
      proof
        assume [simp]: "c = a"
        have "rr = Leaf"
          apply(rule ccontr)
          using  "2.prems" by (auto simp: ball_Un neq_Leaf_iff)
        thus ?thesis using `b<a` by simp
      next
        assume "c < a"
        hence "a \<noteq> c" by simp
        show ?thesis
        proof cases
          assume "rr = Leaf" thus ?thesis using `b<a` `c<a` by(auto)
        next
          assume "rr \<noteq> Leaf"
          then obtain rrl u rrr where [simp]: "rr = Node rrl u rrr"
            by (auto simp: neq_Leaf_iff)
          hence "splay a rr \<noteq> Leaf" by simp
          then obtain rrl' u' rrr' where [simp]: "splay a rr = Node rrl' u' rrr'"
            by (metis tree.exhaust)
          from "2.IH"(4)[OF `a\<noteq>b` _ Node `a\<noteq>c` _ `rr \<noteq> Leaf`] "2.prems"
          show ?thesis using `b<a` `c<a` by (auto split: tree.split)
        qed
      qed
    qed
  qed
qed

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

fun delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete a Leaf = Leaf" |
"delete a t = (case splay a t of
  Node l x r \<Rightarrow>
    if x=a
    then case l of Leaf \<Rightarrow> r
         | _ \<Rightarrow> case splay_max l of Node l' m _ \<Rightarrow> Node l' m r
    else Node l x r)"

hide_const (open) delete

lemma set_delete: assumes "bst t"
shows "set_tree (Splay_Tree.delete a t) = set_tree t - {a}"
proof(cases t)
  case Leaf thus ?thesis by(simp)
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
        by(simp split: tree.split prod.split)(fastforce)
    next
      assume "l' \<noteq> Leaf"
      moreover then obtain l'' m r'' where "splay_max l' = Node l'' m r''"
        using splay_max_Leaf_iff tree.exhaust by blast
      moreover have "a \<notin> set_tree l'"
        by (metis (no_types) Node assms less_irrefl sp splay_bstL)
      ultimately show ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          splay_max_Leaf[of l' l'' m r''] set_splay_max[of l']
        by(clarsimp split: tree.split) auto
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms set_splay[of a "Node l x r"] splay_to_root[OF _ sp]
      by simp
  qed
qed

lemma bst_delete: assumes "bst t" shows "bst (Splay_Tree.delete a t)"
proof(cases t)
  case Leaf thus ?thesis by(simp)
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
        by(simp split: tree.split prod.split)
    next
      assume "l' \<noteq> Leaf"
      thus ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          bst_splay_max[of l'] set_splay_max[of l']
        by(clarsimp split: tree.split) (metis (no_types) insertE insertI1 less_trans)
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms bst_splay[of "Node l x r" a]
      by(auto split: tree.split prod.split)
  qed
qed

end
