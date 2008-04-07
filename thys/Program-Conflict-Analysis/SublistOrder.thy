(*  Title:       Conflict analysis/Sublist Ordering
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
header "Sublist Ordering"
theory SublistOrder
imports Main Misc
begin
text_raw {*\label{thy:SublistOrder}*}

text {*
  This theory defines sublist ordering on lists. A list @{text "l'"} is a sublist of a list @{text "l"}, iff one obtains @{text "l'"} by erasing some elements from @{text "l"}.
*}

subsection "Definitions"

instantiation list :: (type) order
begin

inductive less_eq_list where
  "[] \<le> l"
  | "l \<le> l' \<Longrightarrow> l \<le> a # l'"
  | "l \<le> l' \<Longrightarrow> a # l \<le> a # l'"

definition
  ilt_def: "(l \<Colon> 'a list) < la \<longleftrightarrow> l \<le> la \<and> l \<noteq> la"

abbreviation ileq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ileq \<equiv> op \<le>"

abbreviation ilt :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ilt \<equiv> op <"

notation (xsymbols)
  ileq (infix "\<preceq>" 50)

notation (output)
  ileq (infix "\<preceq>" 50)

notation (xsymbols)
  ilt (infix "\<prec>" 50)

notation (output)
  ilt (infix "\<prec>" 50)


subsection "Basic lemmas"

lemma ileq_cases [cases set, case_names empty drop take]: "\<lbrakk>
    l1\<preceq>l2; 
    l1=[] \<Longrightarrow> P; 
    \<And>a l2'. \<lbrakk>l2=a#l2'; l1\<preceq>l2'\<rbrakk> \<Longrightarrow> P; 
    \<And>a l1' l2'. \<lbrakk>l1=a#l1'; l2=a#l2'; l1'\<preceq>l2'\<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (blast elim: less_eq_list.cases)

lemma ileq_induct[induct set, case_names empty drop take]: "\<lbrakk>
    l1\<preceq>l2; 
    \<And>l. P [] l; 
    \<And>a l l'. \<lbrakk>l'\<preceq>l; P l' l\<rbrakk> \<Longrightarrow> P l' (a # l); 
    \<And>a l l'. \<lbrakk>l'\<preceq>l; P l' l\<rbrakk> \<Longrightarrow> P (a # l') (a # l)
  \<rbrakk> \<Longrightarrow> P l1 l2" 
  by (induct rule: less_eq_list.induct) (blast+)

lemma ileq_empty[simp, intro!]: "[]\<preceq>l"
  by (blast intro: less_eq_list.intros)
lemma ileq_drop: "l'\<preceq>l \<Longrightarrow> l'\<preceq>a#l"
  by (blast intro: less_eq_list.intros)
lemma ileq_take: "l'\<preceq>l \<Longrightarrow> a#l'\<preceq>a#l"
  by (blast intro: less_eq_list.intros)
lemmas ileq_intros = ileq_empty ileq_drop ileq_take
lemma ileq_drop_many: "a\<preceq>c \<Longrightarrow> a\<preceq>b@c"
  by (induct b) (auto intro: ileq_drop)
lemma ileq_take_many: "a\<preceq>c \<Longrightarrow> b@a\<preceq>b@c"
  by (induct b) (auto intro: ileq_take)

lemma ileq_length: "l \<preceq> l' \<Longrightarrow> length l \<le> length l'"
  by (induct rule: ileq_induct) auto
lemma ileq_below_empty[simp]: "(l\<preceq>[]) = (l=[])"
  by (auto dest: ileq_length)

lemma ileq_same_length: "\<lbrakk>l\<preceq>l'; length l = length l'\<rbrakk> \<Longrightarrow> l=l'"
  by (induct rule: ileq_induct) (auto dest: ileq_length)
lemma ileq_same_append[simp]: "(e#a \<preceq> a) = False"
  by (auto dest: ileq_length)

lemma ilt_length[intro]: "x<y \<Longrightarrow> length x < length y"
  apply(unfold ilt_def)
  apply (subgoal_tac "length x \<le> length y")
  apply(auto intro: ileq_length ileq_same_length)
done

lemma ilt_empty[simp]: "([] \<prec> l) = (l\<noteq>[])"
  by (unfold ilt_def, auto)
lemma ilt_emptyI: "l~=[] \<Longrightarrow> [] \<prec> l"
  by (unfold ilt_def, auto)
lemma ilt_emptyD: "[]\<prec>l \<Longrightarrow> l\<noteq>[]"
  by (unfold ilt_def, auto)
lemma ilt_below_empty[simp]: "l \<prec> [] \<Longrightarrow> False"
  by (auto dest: ilt_length)
lemma ilt_drop: "a\<prec>b \<Longrightarrow> a \<prec> e#b"
  by (unfold ilt_def) (auto intro: ileq_intros)
lemma ilt_take: "a\<prec>b \<Longrightarrow> e#a \<prec> e#b"
  by (unfold ilt_def) (auto intro: ileq_intros)
lemma ilt_drop_many: "a\<prec>c \<Longrightarrow> a\<prec>b@c"
  by (induct b) (auto intro: ilt_drop)
lemma ilt_take_many: "a\<prec>c \<Longrightarrow> b@a\<prec>b@c"
  by (induct b) (auto intro: ilt_take)


subsection "Ordering properties"
lemma ileq_refl: "l \<preceq> l"
  by (induct l) (auto intro!: ileq_intros)
lemma ileq_antisym: 
  assumes A: "l \<preceq> l'" 
             "l' \<preceq> l"  
  shows "l=l'" 
proof -
  (* TODO: Is there a simpler proof ? *)
  { fix n
    have "!!l l'. \<lbrakk>l\<preceq>l'; l'\<preceq>l; n=length l + length l'\<rbrakk> \<Longrightarrow> l=l'"
    proof (induct n rule: nat_less_induct)
      case (1 n l l') from "1.prems"(1) show ?case proof (cases rule: ileq_cases)
        case empty with "1.prems"(2) show ?thesis by auto 
      next
        case (drop a l2') with "1.prems"(2) have "length l'\<le>length l" "length l \<le> length l2'" "1+length l2' = length l'" by (auto dest: ileq_length)
        hence False by simp thus ?thesis ..
      next
        case (take a l1' l2') hence LEN': "length l1' + length l2' < length l + length l'" by simp
        from "1.prems" have LEN: "length l' = length l" by (auto dest!: ileq_length)
        from "1.prems"(2) show ?thesis proof (cases rule: ileq_cases[case_names empty' drop' take'])
          case empty' with take LEN show ?thesis by simp 
        next
          case (drop' ah l2h) with take LEN have "length l1' \<le> length l2h" "1+length l2h = length l2'" "length l2' = length l1'" by (auto dest: ileq_length)
          hence False by simp thus ?thesis ..
        next
          case (take' ah l1h l2h)
          with take have 2: "ah=a" "l1h=l2'" "l2h=l1'" "l1' \<preceq> l2'" "l2' \<preceq> l1'" by auto
          with LEN' "1.hyps" "1.prems"(3) have "l1'=l2'" by blast
          with take 2 show ?thesis by simp
        qed
      qed
    qed
  }
  moreover 
  note A 
  ultimately show ?thesis by blast
qed

lemma ileq_trans: 
  assumes A: "x \<preceq> y" 
             "y \<preceq> z" 
  shows "x \<preceq> z" 
proof -
  {
    fix n
    have "!!x y z. \<lbrakk>x \<preceq> y; y \<preceq> z; n=length x + length y + length z\<rbrakk> \<Longrightarrow> x \<preceq> z" 
    proof (induct rule: nat_less_induct[case_names I])
      case (I n x y z)
      from I.prems(2) show ?case proof (cases rule: ileq_cases)
        case empty with I.prems(1) show ?thesis by auto
      next
        case (drop a z') hence "length x + length y + length z' < length x + length y + length z" by simp
        with I.hyps I.prems(3,1) drop(2) have "x\<preceq>z'" by blast
        with drop(1) show ?thesis by (auto intro: ileq_drop)
      next
        case (take a y' z') from I.prems(1) show ?thesis proof (cases rule: ileq_cases[case_names empty' drop' take'])
          case empty' thus ?thesis by auto
        next
          case (drop' ah y'h) with take have "x\<preceq>y'" "y'\<preceq>z'" "length x + length y' + length z' < length x + length y + length z" by auto
          with I.hyps I.prems(3) have "x\<preceq>z'" by (blast)
          with take(2) show ?thesis  by (auto intro: ileq_drop)
        next
          case (take' ah x' y'h) with take have 2: "x=a#x'" "x'\<preceq>y'" "y'\<preceq>z'" "length x' + length y' + length z' < length x + length y + length z" by auto
          with I.hyps I.prems(3) have "x'\<preceq>z'" by blast
          with 2 take(2) show ?thesis by (auto intro: ileq_take)
        qed
      qed
    qed
  } moreover 
  note A
  ultimately show ?thesis by blast
qed

instance by default
  (auto intro: ileq_refl ileq_trans ileq_antisym simp add: ilt_def)
  
end

(*lemma ileq_empty_antisym: "l\<preceq>[] \<Longrightarrow> l=[]" using order_antisym[OF ileq_empty] by blast -- "Superseded by ileq_below_empty"*)

subsection "Appending elements"
lemma ileq_rev_take: "a\<preceq>b \<Longrightarrow> a@[e] \<preceq> b@[e]"
  by (induct rule: ileq_induct) (auto intro: ileq_intros ileq_drop_many)
lemma ilt_rev_take: "a\<prec>b \<Longrightarrow> a@[e] \<prec> b@[e]"
  by (unfold ilt_def) (auto dest: ileq_rev_take)
lemma ileq_rev_drop: "a\<preceq>b \<Longrightarrow> a\<preceq>b@[e]"
  by (induct rule: ileq_induct) (auto intro: ileq_intros)
lemma ileq_rev_drop_many: "a\<preceq>c \<Longrightarrow> a\<preceq>c@d"
  by (induct d rule: rev_induct) (auto dest: ileq_rev_drop)

subsection "Relation to standard list operations"
lemma ileq_map: "w1\<preceq>w2 \<Longrightarrow> map f w1 \<preceq> map f w2"
  by (induct rule: ileq_induct) (auto intro: ileq_intros)
lemma ileq_filter_left[simp]: "filter f w \<preceq> w"
  by (induct w) (auto intro: ileq_intros)
lemma ileq_filter: "w1\<preceq>w2 \<Longrightarrow> filter f w1 \<preceq> filter f w2"
  by (induct rule: ileq_induct) (auto intro: ileq_intros) 

end
