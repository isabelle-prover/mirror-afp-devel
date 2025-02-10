theory Collect_Extra
  imports Main
begin

lemma Collect_if_eq: "{x. if b x then P x else Q x } = {x. b x \<and> P x } \<union> {x. \<not>b x \<and> Q x}"
  by auto

lemma Collect_not_mem_conj_eq: "{x. x \<notin> X \<and> P x} = {x. P x} - X"
  by auto

end
