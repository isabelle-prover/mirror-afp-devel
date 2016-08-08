section \<open>Generic Collection Framework (Internal)\<close>
theory GenCF_No_Comp
imports
  "../../Collections/GenCF/Impl/Impl_List_Set"
  "../../Collections/GenCF/Impl/Impl_List_Map"
  "../../Collections/GenCF/Impl/Impl_RBT_Map"
  "../../Collections/GenCF/Impl/Impl_Array_Map"
  "../../Collections/GenCF/Impl/Impl_Array_Hash_Map"
  "../../Collections/GenCF/Impl/Impl_Array_Stack"
  "../../Collections/GenCF/Impl/Impl_Cfun_Set"
  "../../Collections/GenCF/Impl/Impl_Bit_Set"
  "../../Collections/GenCF/Impl/Impl_Uv_Set"
  "../../Collections/GenCF/Gen/Gen_Set"
  "../../Collections/GenCF/Gen/Gen_Map"
  "../../Collections/GenCF/Gen/Gen_Map2Set"
  "../../Collections/GenCF/Gen/Gen_Hash"
  "../../Collections/Lib/Code_Target_ICF"
  "../../Automatic_Refinement/Lib/Refine_Lib"
  "~~/src/HOL/Analysis/Analysis"
begin

  text \<open>TODO: need to keep in sync with \<open>../../Collections/GenCF/CenCF\<close> ...\<close>

  text \<open> Use one of the \<open>Refine_Dflt\<close>-theories as entry-point! \<close>

  text \<open> Useful Abbreviations \<close>
  abbreviation "dflt_rs_rel \<equiv> map2set_rel dflt_rm_rel"
  abbreviation "iam_set_rel \<equiv> map2set_rel iam_map_rel"
  abbreviation "dflt_ahs_rel \<equiv> map2set_rel dflt_ahm_rel"

  abbreviation ahs_rel where "ahs_rel bhc \<equiv> (map2set_rel (ahm_rel bhc))"

end
