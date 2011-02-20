header {* \isaheader{Specification of Sequences} *}
theory ListSpec 
imports Main "common/Misc"
begin

subsection "Definition"
locale list =
  -- "Abstraction to HOL-lists"
  fixes \<alpha> :: "'s \<Rightarrow> 'x list"
  -- "Invariant"
  fixes invar :: "'s \<Rightarrow> bool"

subsection "Functions"

locale list_empty = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes empty :: "'s"
  assumes empty_correct:
    "\<alpha> empty = []"
    "invar empty"


locale list_isEmpty = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct:
    "invar s \<Longrightarrow> isEmpty s \<longleftrightarrow> \<alpha> s = []"


subsubsection "Iterators"

text {* We first define interruptible foldl and foldr functionals on
  lists. The iterators are implementations of these functionals. *}

fun foldli :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 'x list \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  where
  "foldli c f [] \<sigma> = \<sigma>" |
  "foldli c f (x#l) \<sigma> = (if c \<sigma> then foldli c f l (f x \<sigma>) else \<sigma>)"

lemma foldli_rule_aux: 
  assumes I0: "I l \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I (x#l2) \<sigma> \<rbrakk> \<Longrightarrow> I l2 (f x \<sigma>)"
  shows "I [] (foldli c f l \<sigma>0) \<or> (\<exists>l1 l2. l2\<noteq>[] \<and> l=l1@l2 \<and> \<not> c (foldli c f l \<sigma>0) \<and> I l2 (foldli c f l \<sigma>0))"
  using I0 IP
proof (induct l arbitrary: \<sigma>0)
  case Nil thus ?case by simp
next
  case (Cons x l)
  show ?case 
  proof (cases "c \<sigma>0")
    case False
    hence [simp]: "foldli c f (x#l) \<sigma>0 = \<sigma>0" by simp
    from Cons.prems have "x#l\<noteq>[]" "x#l=[]@(x#l)" "I (x#l) \<sigma>0" by auto
    with False show ?thesis by auto
  next
    case True
    hence FF[simp]: "foldli c f (x#l) \<sigma>0 = foldli c f l (f x \<sigma>0)" by simp
    from Cons.prems(2)[of "[]" x l, OF _ True Cons.prems(1)] have I': "I l (f x \<sigma>0)" by simp
    have "I [] (foldli c f l (f x \<sigma>0)) 
          \<or> (\<exists>l1 l2. l2 \<noteq> [] \<and> l = l1 @ l2 
              \<and> \<not> c (foldli c f l (f x \<sigma>0)) \<and> I l2 (foldli c f l (f x \<sigma>0)))"
      (is "?C1 \<or> ?C2")
    proof (rule Cons.hyps[OF I'])
      fix l1 xx l2 \<sigma>
      assume A: "l=l1@xx#l2" "c \<sigma>" "I (xx#l2) \<sigma>"
      hence B: "x#l = (x#l1)@xx#l2" by simp
      from Cons.prems(2)[OF B A(2,3)] show "I l2 (f xx \<sigma>)" .
    qed
    moreover have "?C1 \<Longrightarrow> ?thesis" by (simp only: FF) simp
    moreover {
      assume ?C2
      then obtain l1 l2 where 
        A: "l2 \<noteq> []" "l = l1 @ l2" 
           "\<not> c (foldli c f l (f x \<sigma>0))" 
           "I l2 (foldli c f l (f x \<sigma>0))"
        by blast
      hence B: "x#l = (x#l1)@l2" by simp
      from B A(1,3,4) have ?thesis 
        apply (simp (no_asm_use) only: FF) 
        apply blast
        done
    } ultimately show ?thesis by blast
  qed
qed

lemma foldli_rule_aux_P: 
  assumes I0: "I l \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I (x#l2) \<sigma> \<rbrakk> \<Longrightarrow> I l2 (f x \<sigma>)"
  assumes IF: "!!\<sigma>. I [] \<sigma> \<Longrightarrow> P \<sigma>"
  assumes II: "!!l1 l2 \<sigma>. \<lbrakk>l2\<noteq>[]; l=l1@l2; \<not> c \<sigma>; I l2 \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (foldli c f l \<sigma>0)"
proof -
  have 
    "I [] (foldli c f l \<sigma>0) 
     \<or> (\<exists>l1 l2. l2\<noteq>[] \<and> l=l1@l2 
        \<and> \<not> c (foldli c f l \<sigma>0) \<and> I l2 (foldli c f l \<sigma>0))"
    apply (rule foldli_rule_aux)
    apply (blast intro!: I0 IP)+
    done
  with IF II show ?thesis by auto
qed

lemma foldli_rule:
  assumes I0: "I [] l \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I l1 (x#l2) \<sigma> \<rbrakk> \<Longrightarrow> I (l1@[x]) l2 (f x \<sigma>)"
  shows "I l [] (foldli c f l \<sigma>0) \<or> (\<exists>l1 l2. l2\<noteq>[] \<and> l=l1@l2 \<and> \<not> c (foldli c f l \<sigma>0) \<and> I l1 l2 (foldli c f l \<sigma>0))"
  using I0 IP
  apply (rule_tac I="\<lambda>l2 \<sigma>. \<exists>l1. l=l1@l2 \<and> I l1 l2 \<sigma>" in foldli_rule_aux_P)
  apply auto
  done

lemma foldli_rule_P:
  assumes I0: "I [] l \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I l1 (x#l2) \<sigma> \<rbrakk> \<Longrightarrow> I (l1@[x]) l2 (f x \<sigma>)"
  assumes IF: "!!\<sigma>. I l [] \<sigma> \<Longrightarrow> P \<sigma>"
  assumes II: "!!l1 l2 \<sigma>. \<lbrakk>l2\<noteq>[]; l=l1@l2; \<not> c \<sigma>; I l1 l2 \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (foldli c f l \<sigma>0)"
proof -
  have "I l [] (foldli c f l \<sigma>0) \<or> (\<exists>l1 l2. l2\<noteq>[] \<and> l=l1@l2 \<and> \<not> c (foldli c f l \<sigma>0) \<and> I l1 l2 (foldli c f l \<sigma>0))"
    apply (rule foldli_rule)
    apply (blast intro!: I0 IP)+
    done
  with IF II show ?thesis by auto
qed

lemma foldli_false[simp]: "\<not>c \<sigma> \<Longrightarrow> foldli c f l \<sigma> = \<sigma>"
  by (cases l) simp_all

lemma foldli_append [simp]:
  "foldli c f (xs @ ys) \<sigma> = foldli c f ys (foldli c f xs \<sigma>)"
by(induct xs arbitrary: \<sigma>) simp_all

lemma foldli_concat: "foldli c f (concat xs) = foldli c (foldli c f) xs"
by(induct xs)(auto intro: ext)


function foldri :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 'x list \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  where
  "foldri c f [] \<sigma> = \<sigma>" |
  "foldri c f (l@[x]) \<sigma> = (if c \<sigma> then foldri c f l (f x \<sigma>) else \<sigma>)"
  apply (case_tac x)
  apply simp
  apply (case_tac c rule: rev_cases)
  apply blast
  apply simp
  apply blast
  apply auto
  done
termination by lexicographic_order

lemma foldri_rule_aux: 
  assumes I0: "I l \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I (l1@[x]) \<sigma> \<rbrakk> \<Longrightarrow> I l1 (f x \<sigma>)"
  shows "I [] (foldri c f l \<sigma>0) \<or> (\<exists>l1 l2. l1\<noteq>[] \<and> l=l1@l2 \<and> \<not> c (foldri c f l \<sigma>0) \<and> I l1 (foldri c f l \<sigma>0))"
  using I0 IP
proof (induct l arbitrary: \<sigma>0 rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x l)
  show ?case 
  proof (cases "c \<sigma>0")
    case False
    hence [simp]: "foldri c f (l@[x]) \<sigma>0 = \<sigma>0" by simp
    from snoc.prems have "l@[x]\<noteq>[]" "l@[x]=l@x#[]" "I (l@[x]) \<sigma>0" by auto
    with False show ?thesis by auto
  next
    case True
    hence FF[simp]: "foldri c f (l@[x]) \<sigma>0 = foldri c f l (f x \<sigma>0)" by simp
    from snoc.prems(2)[of l x "[]", OF _ True snoc.prems(1)] have I': "I l (f x \<sigma>0)" by simp
    have "I [] (foldri c f l (f x \<sigma>0)) 
          \<or> (\<exists>l1 l2. l1 \<noteq> [] \<and> l = l1 @ l2 
              \<and> \<not> c (foldri c f l (f x \<sigma>0)) \<and> I l1 (foldri c f l (f x \<sigma>0)))"
      (is "?C1 \<or> ?C2")
    proof (rule snoc.hyps[OF I'])
      fix l1 xx l2 \<sigma>
      assume A: "l=l1@xx#l2" "c \<sigma>" "I (l1@[xx]) \<sigma>"
      hence B: "l@[x] = l1@xx#(l2@[x])" by simp
      from snoc.prems(2)[OF B A(2,3)] show "I l1 (f xx \<sigma>)" .
    qed
    moreover have "?C1 \<Longrightarrow> ?thesis" by (simp only: FF) simp
    moreover {
      assume ?C2
      then obtain l1 l2 where 
        A: "l1 \<noteq> []" "l = l1 @ l2" 
           "\<not> c (foldri c f l (f x \<sigma>0))" 
           "I l1 (foldri c f l (f x \<sigma>0))"
        by blast
      hence B: "l@[x] = l1@(l2@[x])" by simp
      from B A(1,3,4) have ?thesis 
        apply (simp (no_asm_use) only: FF) 
        apply blast
        done
    } ultimately show ?thesis by blast
  qed
qed
    
lemma foldri_rule_aux_P: 
  assumes I0: "I l \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I (l1@[x]) \<sigma> \<rbrakk> \<Longrightarrow> I l1 (f x \<sigma>)"
  assumes IF: "!!\<sigma>. I [] \<sigma> \<Longrightarrow> P \<sigma>"
  assumes II: "!!l1 l2 \<sigma>. \<lbrakk>l1\<noteq>[]; l=l1@l2; \<not> c \<sigma>; I l1 \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (foldri c f l \<sigma>0)"
proof -
  have 
    "I [] (foldri c f l \<sigma>0) 
     \<or> (\<exists>l1 l2. l1\<noteq>[] \<and> l=l1@l2 
        \<and> \<not> c (foldri c f l \<sigma>0) \<and> I l1 (foldri c f l \<sigma>0))"
    apply (rule foldri_rule_aux)
    apply (blast intro!: I0 IP)+
    done
  with IF II show ?thesis by auto
qed


lemma foldri_rule:
  assumes I0: "I l [] \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I (l1@[x]) l2 \<sigma> \<rbrakk> \<Longrightarrow> I l1 (x#l2) (f x \<sigma>)"
  shows "I [] l (foldri c f l \<sigma>0) \<or> (\<exists>l1 l2. l1\<noteq>[] \<and> l=l1@l2 \<and> \<not> c (foldri c f l \<sigma>0) \<and> I l1 l2 (foldri c f l \<sigma>0))"
  using I0 IP
  apply (rule_tac I="\<lambda>l1 \<sigma>. \<exists>l2. l=l1@l2 \<and> I l1 l2 \<sigma>" in foldri_rule_aux_P)
  apply auto
  done

lemma foldri_rule_P:
  assumes I0: "I l [] \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; c \<sigma>; I (l1@[x]) l2 \<sigma> \<rbrakk> \<Longrightarrow> I l1 (x#l2) (f x \<sigma>)"
  assumes IF: "!!\<sigma>. I [] l \<sigma> \<Longrightarrow> P \<sigma>"
  assumes II: "!!l1 l2 \<sigma>. \<lbrakk>l1\<noteq>[]; l=l1@l2; \<not> c \<sigma>; I l1 l2 \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (foldri c f l \<sigma>0)"
proof -
  have "I [] l (foldri c f l \<sigma>0) \<or> (\<exists>l1 l2. l1\<noteq>[] \<and> l=l1@l2 \<and> \<not> c (foldri c f l \<sigma>0) \<and> I l1 l2 (foldri c f l \<sigma>0))"
    apply (rule foldri_rule)
    apply (blast intro!: I0 IP)+
    done
  with IF II show ?thesis by auto
qed

lemma foldri_false[simp]: "\<not>c \<sigma> \<Longrightarrow> foldri c f l \<sigma> = \<sigma>"
  by (cases l rule: rev_cases) simp_all


text {* We can write @{const foldl} and @{const foldr} as special cases of @{const foldli} and @{const foldri}: 
  (Unfortunately, the parameter ordering is different for @{const foldl})
*}
lemma foldli_foldl: "foldli (\<lambda>x. True) f l \<sigma> = foldl (\<lambda>\<sigma> x. f x \<sigma>) \<sigma> l"
  by (induct l arbitrary: \<sigma>) auto

lemma foldri_foldr: "foldri (\<lambda>x. True) f l \<sigma> = foldr f l \<sigma>"
  by (induct l arbitrary: \<sigma> rule: rev_induct) auto


(* A similar lemma is already in Misc.thy 
  TODO: Resolve naming conflict.
        Perhaps move the whole folding stuff to Misc \<dots> or in a separate List_fold theory inside the collections library.

*)
lemma foldl_rule_P:
  assumes I0: "I [] l \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; I l1 (x#l2) \<sigma> \<rbrakk> \<Longrightarrow> I (l1@[x]) l2 (f \<sigma> x)"
  assumes IF: "!!\<sigma>. I l [] \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (foldl f \<sigma>0 l)"
  apply (rule foldli_rule_P[
    where 
      c="\<lambda>x. True" and 
      f="\<lambda>x \<sigma>. f \<sigma> x" and 
      I=I, 
    OF I0, 
    unfolded foldli_foldl])
  apply (auto simp add: IP IF)
  done

lemma foldr_rule_P:
  assumes I0: "I l [] \<sigma>0"
  assumes IP: "!!l1 x l2 \<sigma>. \<lbrakk> l=l1@x#l2; I (l1@[x]) l2 \<sigma> \<rbrakk> \<Longrightarrow> I l1 (x#l2) (f x \<sigma>)"
  assumes IF: "!!\<sigma>. I [] l \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (foldr f l \<sigma>0)"
  apply (rule foldri_rule_P[
    where 
      c="\<lambda>x. True" and 
      f=f and 
      I=I, 
    OF I0, 
    unfolded foldri_foldr])
  apply (auto simp add: IP IF)
  done

type_synonym ('s,'x,'\<sigma>) list_iteratori = "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 's \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
type_synonym ('s,'x,'\<sigma>) list_iterator = "('x \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 's \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"

locale list_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes iteratei :: "('s,'x,'\<sigma>) list_iteratori"
  assumes iteratei_correct:
    "invar s \<Longrightarrow> iteratei c f s \<sigma> = foldli c f (\<alpha> s) \<sigma>"

locale list_iterate = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes iterate :: "('s,'x,'\<sigma>) list_iterator"
  assumes iterate_correct:
    "invar s \<Longrightarrow> iterate f s \<sigma> = foldl (\<lambda>\<sigma> x. f x \<sigma>) \<sigma> (\<alpha> s)"

locale list_reverse_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes reverse_iteratei :: "('s,'x,'\<sigma>) list_iteratori"
  assumes reverse_iteratei_correct:
    "invar s \<Longrightarrow> reverse_iteratei c f s \<sigma> = foldri c f (\<alpha> s) \<sigma>"

locale list_reverse_iterate = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes reverse_iterate :: "('s,'x,'\<sigma>) list_iterator"
  assumes reverse_iterate_correct:
    "invar s \<Longrightarrow> reverse_iterate f s \<sigma> = foldr f (\<alpha> s) \<sigma>"

locale list_size = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes size :: "'s \<Rightarrow> nat"
  assumes size_correct:
    "invar s \<Longrightarrow> size s = length (\<alpha> s)"
  
subsubsection "Stack"

locale list_push = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes push :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes push_correct:
    "invar s \<Longrightarrow> \<alpha> (push x s) = x#\<alpha> s"
    "invar s \<Longrightarrow> invar (push x s)"

locale list_pop = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes pop :: "'s \<Rightarrow> ('x \<times> 's)"
  assumes pop_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> fst (pop s) = hd (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> \<alpha> (snd (pop s)) = tl (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> invar (snd (pop s))"
begin
  lemma popE: 
    assumes I: "invar s" "\<alpha> s \<noteq> []" 
    obtains s' where "pop s = (hd (\<alpha> s), s')" "invar s'" "\<alpha> s' = tl (\<alpha> s)"
  proof -
    from pop_correct(1,2,3)[OF I] have 
      C: "fst (pop s) = hd (\<alpha> s)"
         "\<alpha> (snd (pop s)) = tl (\<alpha> s)"
         "invar (snd (pop s))" .
    from that[of "snd (pop s)", OF _ C(3,2), folded C(1)] show thesis
      by simp
  qed

  text {* The following shortcut notations are not meant for generating efficient code,
    but solely to simplify reasoning *}
  definition "head s == fst (pop s)"
  definition "tail s == snd (pop s)"

  lemma tail_correct: "\<lbrakk>invar F; \<alpha> F \<noteq> []\<rbrakk> \<Longrightarrow> \<alpha> (tail F) = tl (\<alpha> F)"
    by (simp add: tail_def pop_correct)

  lemma head_correct: "\<lbrakk>invar F; \<alpha> F \<noteq> []\<rbrakk> \<Longrightarrow> (head F) = hd (\<alpha> F)"
    by (simp add: head_def pop_correct)

  lemma pop_split: "pop F = (head F, tail F)"
    apply (cases "pop F")
    apply (simp add: head_def tail_def)
    done

end

locale list_top = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes top :: "'s \<Rightarrow> 'x"
  assumes top_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> top s = hd (\<alpha> s)"

subsubsection {* Queue *}
locale list_enqueue = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes enqueue :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes enqueue_correct: 
    "invar s \<Longrightarrow> \<alpha> (enqueue x s) = \<alpha> s @ [x]"
    "invar s \<Longrightarrow> invar (enqueue x s)"

  -- "Same specification as pop"
locale list_dequeue = list_pop
begin
  lemmas dequeue_correct = pop_correct
  lemmas dequeueE = popE
  lemmas dequeue_split=pop_split
end

  -- "Same specification as top"
locale list_next = list_top
begin
  lemmas next_correct = top_correct
end

subsubsection "Indexing"
locale list_get = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes get :: "'s \<Rightarrow> nat \<Rightarrow> 'x"
  assumes get_correct:
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> get s i = \<alpha> s ! i"

locale list_set = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes set :: "'s \<Rightarrow> nat \<Rightarrow> 'x \<Rightarrow> 's"
  assumes set_correct:
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> \<alpha> (set s i x) = \<alpha> s [i := x]"
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> invar (set s i x)"

  -- "Same specification as enqueue"
locale list_add = list_enqueue
begin
  lemmas add_correct = enqueue_correct
end

    
end
