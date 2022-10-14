section\<open>Basic relativization of cardinality\<close>

theory Discipline_Cardinal
  imports
    Discipline_Function
begin

relativize functional "cardinal" "cardinal_rel" external
relationalize "cardinal_rel" "is_cardinal"
synthesize "is_cardinal" from_definition assuming "nonempty"

notation is_cardinal_fm (\<open>cardinal'(_') is _\<close>)

abbreviation
  cardinal_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(M,x)"

abbreviation
  cardinal_r_set :: "[i,i]\<Rightarrow>i"  (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(##M,x)"

context M_trivial
begin
rel_closed for "cardinal"
  using Least_closed'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"]
  unfolding cardinal_rel_def
  by simp
end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

manual_arity intermediate for "is_Int_fm"
  unfolding is_Int_fm_def
  using arity pred_Un_distrib
  by (simp)

arity_theorem for "is_Int_fm"

arity_theorem for "is_funspace_fm"

arity_theorem for "is_function_space_fm"

arity_theorem for "surjP_rel_fm"

arity_theorem intermediate for "is_surj_fm"

lemma arity_is_surj_fm [arity] :
  "A \<in> nat \<Longrightarrow> B \<in> nat \<Longrightarrow> I \<in> nat \<Longrightarrow> arity(is_surj_fm(A, B, I)) = succ(A) \<union> succ(B) \<union> succ(I)"
  using arity_is_surj_fm' pred_Un_distrib
  by auto

arity_theorem for "injP_rel_fm"

arity_theorem intermediate for "is_inj_fm"

lemma arity_is_inj_fm [arity]:
  "A \<in> nat \<Longrightarrow> B \<in> nat \<Longrightarrow> I \<in> nat \<Longrightarrow> arity(is_inj_fm(A, B, I)) = succ(A) \<union> succ(B) \<union> succ(I)"
  using arity_is_inj_fm' pred_Un_distrib
  by auto

arity_theorem for "is_bij_fm"

arity_theorem for "is_eqpoll_fm"

arity_theorem for "is_cardinal_fm"

context M_Perm
begin
is_iff_rel for "cardinal"
  using least_abs'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"]
    is_eqpoll_iff
  unfolding is_cardinal_def cardinal_rel_def
  by simp
end \<comment> \<open>\<^locale>\<open>M_Perm\<close>\<close>

reldb_add functional "Ord" "Ord"
reldb_add relational "Ord" "ordinal"
reldb_add functional "lt" "lt"
reldb_add relational "lt" "lt_rel"
synthesize "lt_rel" from_definition
notation lt_rel_fm (\<open>\<cdot>_ < _\<cdot>\<close>)
arity_theorem intermediate for "lt_rel_fm"

lemma arity_lt_rel_fm[arity]: "a \<in> nat \<Longrightarrow> b \<in> nat \<Longrightarrow> arity(lt_rel_fm(a, b)) = succ(a) \<union> succ(b)"
  using arity_lt_rel_fm'
  by auto

relativize functional "Card" "Card_rel" external
relationalize "Card_rel" "is_Card"
synthesize "is_Card" from_definition assuming "nonempty"
notation is_Card_fm (\<open>\<cdot>Card'(_')\<cdot>\<close>)
arity_theorem for "is_Card_fm"

notation Card_rel (\<open>Card\<^bsup>_\<^esup>'(_')\<close>)

lemma (in M_Perm) is_Card_iff: "M(A) \<Longrightarrow> is_Card(M, A) \<longleftrightarrow> Card\<^bsup>M\<^esup>(A)"
  using is_cardinal_iff
  unfolding is_Card_def Card_rel_def by simp

abbreviation
  Card_r_set  :: "[i,i]\<Rightarrow>o"  (\<open>Card\<^bsup>_\<^esup>'(_')\<close>) where
  "Card\<^bsup>M\<^esup>(i) \<equiv> Card_rel(##M,i)"

relativize functional "InfCard" "InfCard_rel" external
relationalize "InfCard_rel" "is_InfCard"
synthesize "is_InfCard" from_definition assuming "nonempty"
notation is_InfCard_fm (\<open>\<cdot>InfCard'(_')\<cdot>\<close>)
arity_theorem for "is_InfCard_fm"

notation InfCard_rel (\<open>InfCard\<^bsup>_\<^esup>'(_')\<close>)

abbreviation
  InfCard_r_set  :: "[i,i]\<Rightarrow>o"  (\<open>InfCard\<^bsup>_\<^esup>'(_')\<close>) where
  "InfCard\<^bsup>M\<^esup>(i) \<equiv> InfCard_rel(##M,i)"

subsection\<open>Disicpline for \<^term>\<open>cadd\<close>\<close>
relativize functional "cadd" "cadd_rel" external

abbreviation
  cadd_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<oplus>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<oplus>\<^bsup>M\<^esup> B \<equiv> cadd_rel(M,A,B)"

context M_basic
begin
rel_closed for "cadd"
  using cardinal_rel_closed
  unfolding cadd_rel_def
  by simp
end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

relationalize "cadd_rel" "is_cadd"

manual_schematic for "is_cadd" assuming "nonempty"
  unfolding is_cadd_def
  by (rule iff_sats sum_iff_sats | simp)+
synthesize "is_cadd" from_schematic

arity_theorem for "sum_fm"

arity_theorem for "is_cadd_fm"

context M_Perm
begin
is_iff_rel for "cadd"
  using is_cardinal_iff
  unfolding is_cadd_def cadd_rel_def
  by simp

end  \<comment> \<open>\<^locale>\<open>M_Perm\<close>\<close>

subsection\<open>Disicpline for \<^term>\<open>cmult\<close>\<close>

relativize functional "cmult" "cmult_rel" external

abbreviation
  cmult_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<otimes>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<otimes>\<^bsup>M\<^esup> B \<equiv> cmult_rel(M,A,B)"

relationalize "cmult_rel" "is_cmult"

declare cartprod_iff_sats [iff_sats]

synthesize "is_cmult" from_definition assuming "nonempty"

arity_theorem for "is_cmult_fm"

context M_Perm
begin
rel_closed for "cmult"
  using cardinal_rel_closed
  unfolding cmult_rel_def
  by simp

is_iff_rel for "cmult"
  using is_cardinal_iff
  unfolding is_cmult_def cmult_rel_def
  by simp

end \<comment> \<open>\<^locale>\<open>M_Perm\<close>\<close>

end