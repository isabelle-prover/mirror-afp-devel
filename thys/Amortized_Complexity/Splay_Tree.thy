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

function splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
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
by pat_completeness auto
termination
by (relation "measure (\<lambda>(_,t). size t)") auto

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
  "a<b \<Longrightarrow> a<c \<Longrightarrow> splay a (Node (Node Leaf c lr) b r) = Node Leaf c (Node lr b r)"
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
  "b<a \<Longrightarrow> c<a \<Longrightarrow> splay a (Node l b (Node rl c Leaf)) = Node (Node l b rl) c Leaf"
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


lemma set_tree_splay: "set_tree(splay a t) = set_tree t"
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
              show ?thesis using `a<b` `a<c` `c<b` "2.prems" set_tree_splay[of a ll]
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
              show ?thesis using `a<b` `c<a` `c<b` "2.prems" set_tree_splay[of a lr]
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
              show ?thesis using `a>b` `a<c` `c>b` "2.prems" set_tree_splay[of a rl]
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
              show ?thesis using `a>b` `c<a` `c>b` "2.prems" set_tree_splay[of a rr]
                by auto (metis insertI1 less_trans)+
            qed
          qed
        qed
      qed
    qed
  qed
qed

end
