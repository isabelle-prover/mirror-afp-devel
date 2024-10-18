theory Prefix_Util
  imports Prefix "../order/Suffix_Util"
begin

lemma prefix_suffix_not_suffix:
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "i \<noteq> j"
  shows "\<not>(\<exists>k. prefix (suffix s i) k = suffix s j)"
  using suffix_has_no_prefix_suffix assms
  by (metis append_take_drop_id)

end