theory Generic_Term
  imports Main
begin

type_synonym position = "nat list"

locale subterms = 
  fixes subterms :: "'t \<Rightarrow> 't list"
begin

primrec subterm_at :: "'t \<Rightarrow> position \<Rightarrow> 't" (infixl \<open>!\<^sub>t\<close> 64) where
  "t !\<^sub>t [] = t" 
| "t !\<^sub>t i # p = subterms t ! i !\<^sub>t p"

end

locale smaller_subterms = subterms where subterms = subterms 
  for subterms :: "'t \<Rightarrow> 't list" +
  notes conj_cong [fundef_cong]
  fixes size  :: "'t \<Rightarrow> nat" and is_var :: "'t \<Rightarrow> bool"
  assumes subterms_smaller: "\<And>t' t. t' \<in> set (subterms t) \<Longrightarrow> size t' < size t"
begin

function positions :: "'t \<Rightarrow> position set" where
  "positions t =
     {[]} \<union> {i # p | i p.
              \<not>is_var t \<and>
              i < length (subterms t) \<and>
              p \<in> positions ((subterms t) ! i)}"
  by auto

termination
proof (relation "measure size")
  fix t p i p'
  assume "p = i # p'" "i < length (subterms t)"

  then show "(subterms t ! i, t) \<in> measure size"
    using subterms_smaller
    by simp  
qed auto

declare positions.simps [simp del]

lemma empty_positions [simp]: "[] \<in> positions t"
  by (subst positions.simps) blast

lemma nonempty_positions [simp]:
  "i # p \<in> positions t \<longleftrightarrow> \<not>is_var t \<and> i < length (subterms t) \<and> p \<in> positions ((subterms t) ! i)"
  by (subst positions.simps) auto

end

locale term_interpretation = smaller_subterms where subterms = subterms
for subterms :: "'t \<Rightarrow> 't list" +
fixes 
  Fun :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 't" and
  fun_sym :: "'t \<Rightarrow> 'f" and 
  extra :: "'t \<Rightarrow> 'e"
assumes
  term_fun_sym [simp]: "\<And>f e ts. fun_sym (Fun f e ts) = f" and
  term_extra [simp]: "\<And>f e ts. extra (Fun f e ts) = e" and
  subterms [simp]: "\<And>f e ts. subterms (Fun f e ts) = ts" and
  is_var_subterms [simp]: "\<And>t. is_var t \<Longrightarrow> subterms t = []" and
  term_destruct: "\<And>t. \<not>is_var t \<longleftrightarrow> (\<exists>f e ts. t = Fun f e ts)" and
  term_inject [intro]:
    "\<And>f\<^sub>1 e\<^sub>1 ts\<^sub>1 f\<^sub>2 e\<^sub>2 ts\<^sub>2. Fun f\<^sub>1 e\<^sub>1 ts\<^sub>1 = Fun f\<^sub>2 e\<^sub>2 ts\<^sub>2 \<Longrightarrow> f\<^sub>1 = f\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2 \<and> ts\<^sub>1 = ts\<^sub>2"
begin

lemma interpret_term [simp]: 
  assumes "\<not>is_var t"
  shows "Fun (fun_sym t) (extra t) (subterms t) = t"
  by (metis assms subterms term_destruct term_extra term_fun_sym)

inductive is_subterm_eq :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix \<open>\<unlhd>\<close> 55) where
  subterm_refl [simp, intro]: "is_subterm_eq t t" |
  subterm [intro]: "t' \<in> set (subterms t) \<Longrightarrow> is_subterm_eq t'' t' \<Longrightarrow> is_subterm_eq t'' t"

function all_subterms_eq :: "'t \<Rightarrow> 't set" where
  "all_subterms_eq t = {t} \<union> \<Union>(all_subterms_eq ` set (subterms t))"
  by auto

termination
proof (relation "measure size")
  fix t t'
  assume "t' \<in> set (subterms t)"

  then show "(t', t) \<in> measure size"
    using subterms_smaller
    by simp  
qed auto

declare all_subterms_eq.simps [simp del]

lemmas term_induct = all_subterms_eq.induct

lemma all_subterms_eq_refl [simp]: "t \<in> all_subterms_eq t"
  by (subst all_subterms_eq.simps) simp

lemma all_subterms_eq_is_var [simp]: "is_var t \<Longrightarrow> all_subterms_eq t = {t}"
  by (subst all_subterms_eq.simps) simp

lemma all_subterms_eq_Fun [simp]: 
  "all_subterms_eq (Fun f e ts) = {Fun f e ts} \<union> \<Union>(all_subterms_eq ` set ts)"
  by (subst all_subterms_eq.simps) simp

lemma all_subterms_eq_is_subterm_eq: "all_subterms_eq t = {t'. t' \<unlhd> t}"
proof -

  have "t' \<in> all_subterms_eq t \<Longrightarrow> t' \<unlhd> t" for t'
    by 
      (induction t rule: all_subterms_eq.induct)
      (metis (mono_tags, opaque_lifting) UN_iff Un_insert_left all_subterms_eq.simps insert_iff 
        subterm_refl subterm sup_bot_left)

  moreover have "t' \<unlhd> t \<Longrightarrow> t' \<in> all_subterms_eq t" for t'
  proof (induction t' t rule: is_subterm_eq.induct)
    case (subterm_refl t)

    then show ?case
      by simp
  next
    case (subterm t' t t'')
    
    then show ?case
      by (metis UN_I UnCI all_subterms_eq.elims)
  qed

  ultimately show ?thesis
    by blast
qed

end

end
