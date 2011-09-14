header {*  Well founded and transitive relations  *}

theory WellFoundedTransitive
imports Preliminaries
begin

class well_founded_transitive = ord +
  assumes order_trans1: "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  and less_eq_def: "x \<le> y <-> x = y \<or> x < y"
  and less_induct1 [case_names less]: "(!!x . (!!y . y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"

begin

lemma eq_less_eq [simp]:
  "x = y \<Longrightarrow> x \<le> y"
  by (simp add: less_eq_def)

lemma order_trans2 [simp]:
  "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  apply (simp add: less_eq_def)
  apply auto
  apply (erule less_eq_def order_trans1)
  by assumption

lemma order_trans3:
  "x < y \<Longrightarrow> y \<le> z \<Longrightarrow> x < z"
  apply (simp add: less_eq_def)
  apply auto
  apply (erule less_eq_def order_trans1)
  by assumption


definition
  "SUP_L P w = SUPR {v . v < w} P"

lemma SUP_L_upper:
  "v < w \<Longrightarrow> P v \<le> SUP_L P w"
  by (simp add: SUP_L_def SUP_upper2)

lemma SUP_L_least:
  "(!! v . v < w \<Longrightarrow> P v \<le> Q) \<Longrightarrow> SUP_L P w \<le> Q"
  by (auto simp add: SUP_L_def intro: SUP_least)

lemma SUP_L_fun_eq:
  "((SUP_L P w) i) = (SUP_L (\<lambda> v . P v i)) w"
  by (simp add: SUP_L_def SUP_apply)

end

instantiation prod:: (well_founded_transitive, well_founded_transitive) well_founded_transitive
begin

definition
  less_pair_def: "a < b <->  fst a  < fst b \<or> (fst a = fst b \<and> snd a < snd b)"

definition
  less_eq_pair_def: "(a::('a::well_founded_transitive * 'b::well_founded_transitive)) <= b <-> a = b \<or> a < b"

instance proof
  fix x y z :: "('a::well_founded_transitive * 'b::well_founded_transitive)"
  assume "x < y" and "y < z" then  show  "x < z"
    apply (simp add: less_pair_def)
    apply auto
    apply (drule  order_trans1)
    apply auto
    apply (drule  order_trans1)
    apply auto
    apply (drule  order_trans1)
    apply auto
    done
next
  fix x y :: "'a * 'b"
  show  "x \<le> y <-> x = y \<or> x < y"
    by (simp add: less_eq_pair_def)
next
  fix P::"('a * 'b) \<Rightarrow> bool"
  have a:  "!P . (!x::'a . (!y . y < x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (!a . P a)"
    apply safe
    apply (rule less_induct1)
    by blast
  have b:  "!P . (!x::'b . (!y . y < x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (!a . P a)"
    apply safe
    apply (rule less_induct1)
    by blast
  from a and b have c: "(!x . (!y . y < x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (!a . P a)"
    apply (unfold less_pair_def)
    apply (rule impI)
    apply (simp (no_asm_use) only: split_paired_All)
    apply (unfold fst_conv snd_conv)
    apply (drule spec)
    apply (erule mp)
    apply (rule allI)
    apply (rule impI)
    apply (drule spec)
    apply (erule mp)
    by blast
  from c show "!! a . (!! x. (!! y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
    by blast
next
qed (blast)
end

instantiation "nat":: well_founded_transitive
begin

instance proof
  fix x y z::nat
  assume "x < y" and "y < z" then show "x < z" by simp
  next
  fix x y::nat show "(x \<le> y) <-> (x = y \<or> x < y)"
    apply (unfold le_less)
    by safe
  next
  show "!!P (a::nat) . (!!x . (!!y . y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
   apply (rule less_induct)
   by blast
  qed blast

end

end
