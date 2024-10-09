theory Code_Extraction
  imports "../abs-proof/Abs_SAIS_Verification"
          "../proof/SAIS_Verification"
begin

lemma [code]:
"abs_is_lms T i =
  (if i > 0 then
    if suffix_type T i = S_type \<and> suffix_type T (i - 1) = L_type
    then True
    else False
   else False)"
  by (metis abs_is_lms_0 One_nat_def Suc_pred bot_nat_0.not_eq_extremum 
            i_s_type_imp_Suc_i_not_lms abs_is_lms_def suffix_type_def)

definition 
  bucket_upt_code :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set"
where
  "bucket_upt_code \<alpha> T b \<equiv> 
    set (filter (\<lambda>x. \<alpha> (T ! x) < b) [0..<length T])"

lemma [code]:
  "bucket_upt \<alpha> T b = bucket_upt_code \<alpha> T b"
proof(safe)
  fix x
  assume "x \<in> bucket_upt \<alpha> T b"
  hence "x < length T" "\<alpha> (T ! x) < b"
    by (simp add: bucket_upt_def)+
  then show "x \<in> bucket_upt_code \<alpha> T b"
    by (simp add: bucket_upt_code_def)
next
  fix x
  assume "x \<in> bucket_upt_code \<alpha> T b"
  hence "x < length T" "\<alpha> (T ! x) < b"
    by (simp add: bucket_upt_code_def)+
  then show "x \<in> bucket_upt \<alpha> T b"
    by (simp add: bucket_upt_def)
qed


export_code abs_sais in Haskell
  module_name SAIS file_prefix abs_sais

export_code sais in Haskell
  module_name SAIS_REF file_prefix sais

end