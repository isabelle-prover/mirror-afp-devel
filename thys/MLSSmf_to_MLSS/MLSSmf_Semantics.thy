theory MLSSmf_Semantics imports
  MLSSmf_Defs HereditarilyFinite.Finitary
begin

fun I\<^sub>t :: "('v \<Rightarrow> hf) \<Rightarrow> ('f \<Rightarrow> hf \<Rightarrow> hf) \<Rightarrow> ('v, 'f) MLSSmf_term \<Rightarrow> hf" where
  "I\<^sub>t M\<^sub>v M\<^sub>f (\<emptyset>\<^sub>m _) = 0" |
  "I\<^sub>t M\<^sub>v M\<^sub>f (Var\<^sub>m x) = M\<^sub>v x" |
  "I\<^sub>t M\<^sub>v M\<^sub>f (t\<^sub>1 \<squnion>\<^sub>m t\<^sub>2) = I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>1 \<squnion> I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>2" |
  "I\<^sub>t M\<^sub>v M\<^sub>f (t\<^sub>1 \<sqinter>\<^sub>m t\<^sub>2) = I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>1 \<sqinter> I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>2" |
  "I\<^sub>t M\<^sub>v M\<^sub>f (t\<^sub>1 -\<^sub>m t\<^sub>2) = I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>1 - I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>2" |
  "I\<^sub>t M\<^sub>v M\<^sub>f (Single\<^sub>m t) = HF {I\<^sub>t M\<^sub>v M\<^sub>f t}" |
  "I\<^sub>t M\<^sub>v M\<^sub>f (App f t) = (M\<^sub>f f) (I\<^sub>t M\<^sub>v M\<^sub>f t)"

fun I\<^sub>a :: "('v \<Rightarrow> hf) \<Rightarrow> ('f \<Rightarrow> hf \<Rightarrow> hf) \<Rightarrow> ('v, 'f) MLSSmf_atom \<Rightarrow> bool" where
  "I\<^sub>a M\<^sub>v M\<^sub>f (t\<^sub>1 \<in>\<^sub>m t\<^sub>2) \<longleftrightarrow> I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>1 \<^bold>\<in> I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>2" |
  "I\<^sub>a M\<^sub>v M\<^sub>f (t\<^sub>1 =\<^sub>m t\<^sub>2) \<longleftrightarrow> I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>1 = I\<^sub>t M\<^sub>v M\<^sub>f t\<^sub>2" |
  "I\<^sub>a M\<^sub>v M\<^sub>f (inc(f)) = (\<forall>s t. s \<le> t \<longrightarrow> (M\<^sub>f f) s \<le> (M\<^sub>f f) t)" |
  "I\<^sub>a M\<^sub>v M\<^sub>f (dec(f)) = (\<forall>s t. s \<le> t \<longrightarrow> (M\<^sub>f f) t \<le> (M\<^sub>f f) s)" |
  "I\<^sub>a M\<^sub>v M\<^sub>f (add(f)) = (\<forall>s t. (M\<^sub>f f) (s \<squnion> t) = (M\<^sub>f f) s \<squnion> (M\<^sub>f f) t)" |
  "I\<^sub>a M\<^sub>v M\<^sub>f (mul(f)) = (\<forall>s t. (M\<^sub>f f) (s \<sqinter> t) = (M\<^sub>f f) s \<sqinter> (M\<^sub>f f) t)" |
  "I\<^sub>a M\<^sub>v M\<^sub>f (f \<preceq>\<^sub>m g) = (\<forall>s. (M\<^sub>f f) s \<le> (M\<^sub>f g) s)"

fun I\<^sub>l :: "('v \<Rightarrow> hf) \<Rightarrow> ('f \<Rightarrow> hf \<Rightarrow> hf) \<Rightarrow> ('v, 'f) MLSSmf_literal \<Rightarrow> bool" where
  "I\<^sub>l M\<^sub>v M\<^sub>f (AT\<^sub>m a) = I\<^sub>a M\<^sub>v M\<^sub>f a" |
  "I\<^sub>l M\<^sub>v M\<^sub>f (AF\<^sub>m a) = (\<not> I\<^sub>a M\<^sub>v M\<^sub>f a)"

fun I\<^sub>c\<^sub>l :: "('v \<Rightarrow> hf) \<Rightarrow> ('f \<Rightarrow> hf \<Rightarrow> hf) \<Rightarrow> ('v, 'f) MLSSmf_clause \<Rightarrow> bool" where
  "I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f [] = True" |
  "I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f (l # ls) = (I\<^sub>l M\<^sub>v M\<^sub>f l \<and> I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f ls)"

lemma cl_is_true_iff_all_literals_true[iff]:
  "I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C> \<longleftrightarrow> (\<forall>l \<in> set \<C>. I\<^sub>l M\<^sub>v M\<^sub>f l)"
proof
  assume "I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>"
  then show "\<forall>l\<in>set \<C>. I\<^sub>l M\<^sub>v M\<^sub>f l"
    by (induction \<C>) auto
next
  assume "\<forall>l\<in>set \<C>. I\<^sub>l M\<^sub>v M\<^sub>f l"
  then show "I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>"
    by (induction \<C>) auto
qed

end