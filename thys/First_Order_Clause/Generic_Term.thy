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
  by pat_completeness auto

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

locale term_interpretation = 
  subterms where subterms = subterms
for subterms :: "'t \<Rightarrow> 't list" +
fixes 
  Fun :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 't" and
  fun_sym :: "'t \<Rightarrow> 'f" and 
  extra :: "'t \<Rightarrow> 'e" and
  is_var :: "'t \<Rightarrow> bool"
assumes
  term_fun_sym [simp]: "\<And>f e ts. fun_sym (Fun f e ts) = f" and
  term_extra [simp]: "\<And>f e ts. extra (Fun f e ts) = e" and
  subterms [simp]: "\<And>f e ts. subterms (Fun f e ts) = ts" and
  term_destruct: "\<And>t. \<not>is_var t \<longleftrightarrow> (\<exists>f e ts. t = Fun f e ts)" and
  term_inject [intro]:
    "\<And>f\<^sub>1 e\<^sub>1 ts\<^sub>1 f\<^sub>2 e\<^sub>2 ts\<^sub>2. Fun f\<^sub>1 e\<^sub>1 ts\<^sub>1 = Fun f\<^sub>2 e\<^sub>2 ts\<^sub>2 \<Longrightarrow> f\<^sub>1 = f\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2 \<and> ts\<^sub>1 = ts\<^sub>2"
begin

lemma interpret_term [simp]: 
  assumes "\<not>is_var t"
  shows "Fun (fun_sym t) (extra t) (subterms t) = t"
  by (metis assms subterms term_destruct term_extra term_fun_sym)

end

end
