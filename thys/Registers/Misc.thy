section \<open>Miscellaneous facts\<close>

text \<open>This theory proves various facts that are not directly related to this developments 
but do not occur in the imported theories.\<close>

theory Misc
  imports
    Complex_Bounded_Operators.Cblinfun_Code
    "HOL-Library.Z2"
    Jordan_Normal_Form.Matrix
    Hilbert_Space_Tensor_Product.Weak_Star_Topology
begin

\<comment> \<open>Remove notation that collides with the notation we use\<close>
no_notation Order.top ("\<top>\<index>")
unbundle no m_inv_syntax
unbundle no vec_syntax
unbundle no inner_syntax

\<comment> \<open>Import notation from Bounded Operator and Jordan Normal Form libraries\<close>
unbundle cblinfun_syntax
unbundle jnf_syntax

(* abbreviation "butterfly (ket i) (ket j) \<equiv> butterfly (ket i) (ket j)" *)
(* abbreviation "butterfly (ket i) (ket i) \<equiv> butterfly (ket i) (ket i)" *)

text \<open>The following declares the ML antiquotation \<^verbatim>\<open>fact\<close>. In ML code,
  \<^verbatim>\<open>@{fact f}\<close> for a theorem/fact name f is replaced by an ML string
  containing a printable(!) representation of fact. (I.e.,
  if you print that string using writeln, the user can ctrl-click on it.)

  This is useful when constructing diagnostic messages in ML code, e.g., 
  \<^verbatim>\<open>"Use the theorem " ^ @{fact thmname} ^ "here."\<close>\<close>

setup \<open>ML_Antiquotation.inline_embedded \<^binding>\<open>fact\<close>
((Args.context -- Scan.lift Args.name_position) >> (fn (ctxt,namepos) => let
  val facts = Proof_Context.facts_of ctxt
  val fullname = Facts.check (Context.Proof ctxt) facts namepos
  val (markup, shortname) = Proof_Context.markup_extern_fact ctxt fullname
  val string = Markup.markups markup shortname
  in ML_Syntax.print_string string end
))
\<close>


instantiation bit :: enum begin
definition "enum_bit = [0::bit,1]"
definition "enum_all_bit P \<longleftrightarrow> P (0::bit) \<and> P 1"
definition "enum_ex_bit P \<longleftrightarrow> P (0::bit) \<or> P 1"
instance
proof intro_classes
  show \<open>(UNIV :: bit set) = set enum_class.enum\<close>
    by (auto simp: enum_bit_def)
  show \<open>distinct (enum_class.enum :: bit list)\<close>
    by (auto simp: enum_bit_def)
  show \<open>enum_class.enum_all P = Ball UNIV P\<close> for P :: \<open>bit \<Rightarrow> bool\<close>
    apply (simp add: enum_bit_def enum_all_bit_def enum_ex_bit_def)
    by (metis bit.exhaust)
  show \<open>enum_class.enum_ex P = Bex UNIV P\<close> for P :: \<open>bit \<Rightarrow> bool\<close>
    apply (simp add: enum_bit_def enum_all_bit_def enum_ex_bit_def)
    by (metis bit.exhaust)
qed
end

lemma card_bit[simp]: "CARD(bit) = 2"
  using card_2_iff' by force

instantiation bit :: card_UNIV begin
definition "finite_UNIV = Phantom(bit) True"
definition "card_UNIV = Phantom(bit) 2"
instance
  apply intro_classes
  by (simp_all add: finite_UNIV_bit_def card_UNIV_bit_def)
end

lemma mat_of_rows_list_carrier[simp]:
  "mat_of_rows_list n vs \<in> carrier_mat (length vs) n"
  "dim_row (mat_of_rows_list n vs) = length vs"
  "dim_col (mat_of_rows_list n vs) = n"
  unfolding mat_of_rows_list_def by auto

lemma mat_of_rows_list_carrier2xn[iff]:
  "mat_of_rows_list n [a,b] \<in> carrier_mat 2 n"
  by auto

lemma mat_of_rows_list_carrier4xn[iff]:
  "mat_of_rows_list n [a,b,c,d] \<in> carrier_mat 4 n"
  by auto


(* text \<open>Overriding \<^theory>\<open>Complex_Bounded_Operators.Complex_Bounded_Linear_Function\<close>.\<^term>\<open>sandwich\<close>.
      The latter is the same function but defined as a \<^typ>\<open>(_,_) cblinfun\<close> which is less convenient for us.\<close>
definition sandwich where \<open>sandwich a b = a o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L a*\<close> *)

(* lemma clinear_sandwich[simp]: \<open>clinear (sandwich a)\<close>
  apply (rule clinearI)
   apply (simp add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose bounded_cbilinear.add_right sandwich_def)
  by (simp add: sandwich_apply)

lemma bounded_clinear_sandwich[simp]: \<open>bounded_clinear (sandwich a)\<close>
  apply (rule bounded_clinearI[where K=\<open>norm a * norm a\<close>])
   apply (auto simp add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose bounded_cbilinear.add_right sandwich_def)
  by (smt (verit, ccfv_SIG) mult.commute mult_right_mono norm_adj norm_cblinfun_compose norm_ge_zero ordered_field_class.sign_simps(32)) *)

(* lemma sandwich_id[simp]: \<open>sandwich id_cblinfun = id_cblinfun\<close>
  by (auto simp: sandwich_apply) *)

(* lemma mat_of_cblinfun_sandwich:
  fixes a :: "(_::onb_enum, _::onb_enum) cblinfun"
  shows \<open>mat_of_cblinfun (sandwich a b) = (let a' = mat_of_cblinfun a in a' * mat_of_cblinfun b * mat_adjoint a')\<close>
  by (simp add: mat_of_cblinfun_compose sandwich_def Let_def mat_of_cblinfun_adj)
 *)

lemma prod_cases3' [cases type]:
  obtains (fields) a b c where "y = ((a, b), c)"
  by (cases y, case_tac a) blast

text \<open>We define the following abbreviations:
\<^item> \<open>mutually f (x\<^sub>1,x\<^sub>2,\<dots>,x\<^sub>n)\<close> expands to the conjuction of all \<^term>\<open>f x\<^sub>i x\<^sub>j\<close> with \<^term>\<open>i\<noteq>j\<close>.
\<^item> \<open>each f (x\<^sub>1,x\<^sub>2,\<dots>,x\<^sub>n)\<close> expands to the conjuction of all \<^term>\<open>f x\<^sub>i\<close>.\<close>

syntax "_mutually" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("mutually _ '(_')")
syntax "_mutually2" :: "'a \<Rightarrow> 'b \<Rightarrow> args \<Rightarrow> args \<Rightarrow> 'c"

translations "mutually f (x)" => "CONST True"
translations "mutually f (_args x y)" => "f x y \<and> f y x"
translations "mutually f (_args x (_args x' xs))" => "_mutually2 f x (_args x' xs) (_args x' xs)"
translations "_mutually2 f x y zs" => "f x y \<and> f y x \<and> _mutually f zs"
translations "_mutually2 f x (_args y ys) zs" => "f x y \<and> f y x \<and> _mutually2 f x ys zs"

syntax "_each" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("each _ '(_')")
translations "each f (x)" => "f x"
translations "_each f (_args x xs)" => "f x \<and> _each f xs"



lemma dim_col_mat_adjoint[simp]: "dim_col (mat_adjoint m) = dim_row m"
  unfolding mat_adjoint_def by simp
lemma dim_row_mat_adjoint[simp]: "dim_row (mat_adjoint m) = dim_col m"
  unfolding mat_adjoint_def by simp

lemma invI: 
  assumes \<open>inj f\<close>
  assumes \<open>x = f y\<close>
  shows \<open>inv f x = y\<close>
  by (simp add: assms(1) assms(2))

instantiation prod :: (default,default) default begin
definition \<open>default_prod = (default, default)\<close>
instance..
end

instance bit :: default..

lemma surj_from_comp:
  assumes \<open>surj (g o f)\<close>
  assumes \<open>inj g\<close>
  shows \<open>surj f\<close>
  by (metis assms(1) assms(2) f_inv_into_f fun.set_map inj_image_mem_iff iso_tuple_UNIV_I surj_iff_all)

lemma double_exists: \<open>(\<exists>x y. Q x y) \<longleftrightarrow> (\<exists>z. Q (fst z) (snd z))\<close>
  by simp

lemma Ex_iffI:
  assumes \<open>\<And>x. P x \<Longrightarrow> Q (f x)\<close>
  assumes \<open>\<And>x. Q x \<Longrightarrow> P (g x)\<close>
  shows \<open>Ex P \<longleftrightarrow> Ex Q\<close>
  using assms(1) assms(2) by auto

(* TODO move to Bounded_Operators *)
lemma cspan_space_as_set[simp]: \<open>cspan (space_as_set X) = space_as_set X\<close>
  by auto

(* TODO integrate into lift_cblinfun_comp *)
(* TODO In doc of lift_cblinfun_comp, mention that it works specifically after cblinfun_assoc_left *)
thm lift_cblinfun_comp
lemma lift_cblinfun_comp2: 
  assumes \<open>a o\<^sub>C\<^sub>L b = c\<close>
  shows \<open>(d o\<^sub>C\<^sub>L a) o\<^sub>C\<^sub>L b = d o\<^sub>C\<^sub>L c\<close>
  by (simp add: assms cblinfun_assoc_right)
lemmas lift_cblinfun_comp = lift_cblinfun_comp lift_cblinfun_comp2

unbundle no cblinfun_syntax
unbundle no jnf_syntax

end
