theory DBM_Examples
  imports 
    DBM_Operations_Impl_Refine 
    FW_More 
    Show.Show_Instances
begin

section \<open>Examples\<close>

no_notation Ref.update (\<open>_ := _\<close> 62)

text \<open>Let us represent the zone \<open>y \<le> x \<and> x − y \<le> 2 \<and> y \<ge> 1\<close> as a DBM:\<close>
definition test_dbm :: "int DBM'" where
  "test_dbm = ((((\<lambda>(i, j). Le 0)((1,2) := Le 2))((0, 2) := Le (-1)))((1, 0) := \<infinity>))((2, 0) := \<infinity>)"

\<comment> \<open>Pretty-printing\<close>
definition show_test_dbm where
  "show_test_dbm M = String.implode (
    show_dbm 2
      (\<lambda>i. if i = 1 then ''x'' else if i = 2 then ''y'' else ''f'') show
      M
    )"

\<comment> \<open>Pretty-printing\<close>
value [code] "show_test_dbm test_dbm"

\<comment> \<open>Canonical form\<close>
value [code] "show_test_dbm (FW' test_dbm 2)"

\<comment> \<open>Projection onto \<open>x\<close> axis\<close>
value [code] "show_test_dbm (reset'_upd (FW' test_dbm 2) 2 [2] 0)"
\<comment> \<open>Note that if \<^term>\<open>reset'_upd\<close> is not applied to the canonical form, the result is incorrect:\<close>
value [code] "show_test_dbm (reset'_upd test_dbm 2 [2] 0)"
\<comment> \<open>In this case, we already obtained a new canonical form after reset:\<close>
value [code] "show_test_dbm (FW' (reset'_upd (FW' test_dbm 2) 2 [2] 0) 2)"
\<comment> \<open>Note that \<^term>\<open>FWI\<close> can be used to restore the canonical form without running a full \<^term>\<open>FW'\<close>.\<close>

\<comment> \<open>Relaxation, a.k.a computing the "future", or "letting time elapse":\<close>
value [code] "show_test_dbm (up_canonical_upd (reset'_upd (FW' test_dbm 2) 2 [2] 0) 2)"
\<comment> \<open>Note that \<^term>\<open>up_canonical_upd\<close> always preservers canonical form.\<close>

\<comment> \<open>Intersection\<close>
value [code] "show_test_dbm (FW' (And_upd 2
    (up_canonical_upd (reset'_upd (FW' test_dbm 2) 2 [2] 0) 2)
    ((\<lambda>(i, j). \<infinity>)((1, 0):=Lt 1))) 2)"
\<comment> \<open>Note that \<^term>\<open>up_canonical_upd\<close> always preservers canonical form.\<close>

\<comment> \<open>Checking if DBM represents the empty zone\<close>
value [code] "check_diag 2 (FW' (And_upd 2
    (up_canonical_upd (reset'_upd (FW' test_dbm 2) 2 [2] 0) 2)
    ((\<lambda>(i, j). \<infinity>)((1, 0):=Lt 1))) 2)"

\<comment> \<open>Instead of \<^term>\<open>\<lambda>(i, j). \<infinity>\<close> we could also have been using \<^term>\<open>unbounded_dbm\<close>.\<close>

end