section \<open> Variables as Lenses \<close>

theory Variables
  imports "Optics.Optics"
begin

text \<open> Here, we implement foundational constructors and syntax translations for state variables,
  using lens manipulations, for use in shallow expressions. \<close>

subsection \<open> Constructors \<close>

text \<open> The following bundle allows us to override the colon operator, which we use for variable
  namespaces. \<close>

bundle Expression_Syntax
begin

no_notation   
  Set.member  (\<open>'(:')\<close>) and
  Set.member  (\<open>(\<open>notation=\<open>infix :\<close>\<close>_/ : _)\<close> [51, 51] 50)

end

unbundle Expression_Syntax

declare fst_vwb_lens [simp] and snd_vwb_lens [simp]

text \<open> Lenses~\cite{Foster2020-IsabelleUTP} can also be used to effectively define sets of variables. Here we define the
  the universal alphabet ($\Sigma$) to be the bijective lens @{term "1\<^sub>L"}. This characterises
  the whole of the source type, and thus is effectively the set of all alphabet variables. \<close>

definition univ_var :: "('\<alpha> \<Longrightarrow> '\<alpha>)" ("\<^bold>v") where
[lens_defs]: "univ_var = 1\<^sub>L"

lemma univ_var_vwb [simp]: "vwb_lens univ_var"
  by (simp add: univ_var_def)

definition univ_alpha :: "'s scene" where
[lens_defs]: "univ_alpha = \<top>\<^sub>S"

definition emp_alpha :: "'s scene" where
[lens_defs]: "emp_alpha = \<bottom>\<^sub>S"

definition var_alpha :: "('a \<Longrightarrow> 's) \<Rightarrow> 's scene" where
[lens_defs]: "var_alpha x = lens_scene x"

definition ns_alpha :: "('b \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Longrightarrow> 'c" where
[lens_defs]: "ns_alpha a x = x ;\<^sub>L a"

definition var_fst :: "('a \<times> 'b \<Longrightarrow> 's) \<Rightarrow> ('a \<Longrightarrow> 's)" where
[lens_defs]: "var_fst x = fst\<^sub>L ;\<^sub>L x" 

definition var_snd :: "('a \<times> 'b \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's)" where
[lens_defs]: "var_snd x = snd\<^sub>L ;\<^sub>L x" 

definition var_pair :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> ('a \<times> 'b \<Longrightarrow> 's)" where
[lens_defs]: "var_pair x y = x +\<^sub>L y"

abbreviation var_member :: "('a \<Longrightarrow> 's) \<Rightarrow> 's scene \<Rightarrow> bool" (infix "\<in>\<^sub>v" 50) where
"x \<in>\<^sub>v A \<equiv> var_alpha x \<le> A"

lemma ns_alpha_weak [simp]: "\<lbrakk> weak_lens a; weak_lens x \<rbrakk> \<Longrightarrow> weak_lens (ns_alpha a x)"
  by (simp add: ns_alpha_def comp_weak_lens)

lemma ns_alpha_mwb [simp]: "\<lbrakk> mwb_lens a; mwb_lens x \<rbrakk> \<Longrightarrow> mwb_lens (ns_alpha a x)"
  by (simp add: ns_alpha_def comp_mwb_lens)

lemma ns_alpha_vwb [simp]: "\<lbrakk> vwb_lens a; vwb_lens x \<rbrakk> \<Longrightarrow> vwb_lens (ns_alpha a x)"
  by (simp add: ns_alpha_def comp_vwb_lens)

lemma ns_alpha_indep_1 [simp]: "a \<bowtie> b \<Longrightarrow> ns_alpha a x \<bowtie> ns_alpha b y"
  by (simp add: lens_indep_left_ext lens_indep_right_ext ns_alpha_def)

lemma ns_alpha_indep_2 [simp]: "a \<bowtie> y \<Longrightarrow> ns_alpha a x \<bowtie> y"
  by (simp add: lens_indep_left_ext ns_alpha_def)

lemma ns_alpha_indep_3 [simp]: "x \<bowtie> b \<Longrightarrow> x \<bowtie> ns_alpha b y"
  by (simp add: lens_indep_sym)

lemma ns_alpha_indep_4 [simp]: "\<lbrakk> mwb_lens a; x \<bowtie> y \<rbrakk> \<Longrightarrow> ns_alpha a x \<bowtie> ns_alpha a y"
  by (simp add: ns_alpha_def)

lemma var_fst_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (var_fst x)"
  by (simp add: var_fst_def comp_mwb_lens)

lemma var_snd_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (var_snd x)"
  by (simp add: var_snd_def comp_mwb_lens)

lemma var_fst_vwb [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (var_fst x)"
  by (simp add: var_fst_def comp_vwb_lens)

lemma var_snd_vwb [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (var_snd x)"
  by (simp add: var_snd_def comp_vwb_lens)

lemma var_fst_indep_1 [simp]: "x \<bowtie> y \<Longrightarrow> var_fst x \<bowtie> y"
  by (simp add: var_fst_def lens_indep_left_ext)

lemma var_fst_indep_2 [simp]: "x \<bowtie> y \<Longrightarrow> x \<bowtie> var_fst y"
  by (simp add: var_fst_def lens_indep_right_ext)

lemma var_snd_indep_1 [simp]: "x \<bowtie> y \<Longrightarrow> var_snd x \<bowtie> y"
  by (simp add: var_snd_def lens_indep_left_ext)

lemma var_snd_indep_2 [simp]: "x \<bowtie> y \<Longrightarrow> x \<bowtie> var_snd y"
  by (simp add: var_snd_def lens_indep_right_ext)

lemma mwb_var_pair [simp]: "\<lbrakk> mwb_lens x; mwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> mwb_lens (var_pair x y)"
  by (simp add: var_pair_def plus_mwb_lens)

lemma vwb_var_pair [simp]: "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> vwb_lens (var_pair x y)"
  by (simp add: var_pair_def)

lemma var_pair_pres_indep [simp]:
  "\<lbrakk> x \<bowtie> y; x \<bowtie> z \<rbrakk> \<Longrightarrow> x \<bowtie> var_pair y z"
  "\<lbrakk> x \<bowtie> y; x \<bowtie> z \<rbrakk> \<Longrightarrow> var_pair y z \<bowtie> x"
  by (simp_all add: var_pair_def lens_indep_sym)

definition res_alpha :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('c \<Longrightarrow> 'b) \<Rightarrow> 'a \<Longrightarrow> 'c" where
[lens_defs]: "res_alpha x a = x /\<^sub>L a"

lemma idem_scene_var [simp]:
  "vwb_lens x \<Longrightarrow> idem_scene (var_alpha x)"
  by (simp add: lens_defs)

lemma var_alpha_combine: "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> var_alpha x \<squnion>\<^sub>S var_alpha y = var_alpha (x +\<^sub>L y)"
  by (simp add: lens_plus_scene var_alpha_def)

lemma var_alpha_indep [simp]: 
  assumes "vwb_lens x" "vwb_lens y"
  shows "var_alpha x \<bowtie>\<^sub>S var_alpha y \<longleftrightarrow> x \<bowtie> y"
  by (simp add: assms(1) assms(2) lens_indep_scene var_alpha_def)

lemma pre_var_indep_prod [simp]: "x \<bowtie> a \<Longrightarrow> ns_alpha fst\<^sub>L x \<bowtie> a \<times>\<^sub>L b"
  using lens_indep.lens_put_irr2
  by (unfold_locales, force simp add: lens_defs prod.case_eq_if lens_indep_comm)+

lemma post_var_indep_prod [simp]: "x \<bowtie> b \<Longrightarrow> ns_alpha snd\<^sub>L x \<bowtie> a \<times>\<^sub>L b"
  using lens_indep.lens_put_irr2
  by (unfold_locales, force simp add: lens_defs prod.case_eq_if lens_indep_comm)+

lemma lens_indep_impl_scene_indep_var [simp]:
  "(X \<bowtie> Y) \<Longrightarrow> var_alpha X \<bowtie>\<^sub>S var_alpha Y"
  by (simp add: var_alpha_def)

declare lens_scene_override [simp]
declare uminus_scene_twice [simp]

lemma var_alpha_override [simp]: 
  "mwb_lens X \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on var_alpha X = s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X"
  by (simp add: var_alpha_def)

(* Some extra Scene laws; should be moved to Optics at some point *)

lemma var_alpha_indep_compl [simp]: 
  assumes "vwb_lens x" "vwb_lens y"
  shows "var_alpha x \<bowtie>\<^sub>S - var_alpha y \<longleftrightarrow> x \<subseteq>\<^sub>L y"
  by (simp add: assms scene_le_iff_indep_inv sublens_iff_subscene var_alpha_def)

lemma var_alpha_subset [simp]:
  assumes "vwb_lens x" "vwb_lens y"
  shows "var_alpha x \<le> var_alpha y \<longleftrightarrow> x \<subseteq>\<^sub>L y"
  by (simp add: assms(1) assms(2) sublens_iff_subscene var_alpha_def)

subsection \<open> Syntax Translations \<close>

text \<open> In order to support nice syntax for variables, we here set up some translations. The first
  step is to introduce a collection of non-terminals. \<close>
  
nonterminal svid and svids and salpha and sframe_enum and sframe

text \<open> These non-terminals correspond to the following syntactic entities. Non-terminal 
  @{typ "svid"} is an atomic variable identifier, and @{typ "svids"} is a list of identifier. 
  @{typ "salpha"} is an alphabet or set of variables. @{typ "sframe"} is a frame. Such sets can 
  be constructed only through lens composition due to typing restrictions. Next we introduce some 
  syntax constructors. \<close>
   
syntax \<comment> \<open> Identifiers \<close>
  "_svid"         :: "id_position \<Rightarrow> svid" ("_" [999] 999)
  "_svlongid"     :: "longid_position \<Rightarrow> svid" ("_" [999] 999)
  ""              :: "svid \<Rightarrow> svids" ("_")
  "_svid_list"    :: "svid \<Rightarrow> svids \<Rightarrow> svids" ("_,/ _")
  "_svid_alpha"   :: "svid" ("\<^bold>v")
  "_svid_index"   :: "id_position \<Rightarrow> logic \<Rightarrow> svid" ("_'(_')" [999] 999)
  "_svid_tuple"   :: "svids \<Rightarrow> svid" ("'(_')")
  "_svid_dot"     :: "svid \<Rightarrow> svid \<Rightarrow> svid" ("_:_" [999,998] 998)
  "_svid_res"     :: "svid \<Rightarrow> svid \<Rightarrow> svid" ("_\<restriction>_" [999,998] 998)
  "_svid_pre"     :: "svid \<Rightarrow> svid" ("_\<^sup><" [997] 997)
  "_svid_post"    :: "svid \<Rightarrow> svid" ("_\<^sup>>" [997] 997)
  "_svid_fst"     :: "svid \<Rightarrow> svid" ("_.1" [997] 997)
  "_svid_snd"     :: "svid \<Rightarrow> svid" ("_.2" [997] 997)
  "_mk_svid_list" :: "svids \<Rightarrow> logic" \<comment> \<open> Helper function for summing a list of identifiers \<close>
  "_of_svid_list"   :: "logic \<Rightarrow> svids" \<comment> \<open> Reverse of the above \<close>
  "_svid_view"    :: "logic \<Rightarrow> svid" ("\<V>[_]") \<comment> \<open> View of a symmetric lens \<close>
  "_svid_coview"  :: "logic \<Rightarrow> svid" ("\<C>[_]") \<comment> \<open> Coview of a symmetric lens \<close>
  "_svid_prod"    :: "svid \<Rightarrow> svid \<Rightarrow> svid" (infixr "\<times>" 85)
  "_svid_pow2"    :: "svid \<Rightarrow> svid" ("_\<^sup>2" [999] 999)

text \<open> A variable can be decorated with an ampersand, to indicate it is a predicate variable, with 
  a dollar to indicate its an unprimed relational variable, or a dollar and ``acute'' symbol to 
  indicate its a primed relational variable. Isabelle's parser is extensible so additional
  decorations can be and are added later. \<close>

syntax \<comment> \<open> Variable sets \<close>
  "_salphaid"    :: "id_position \<Rightarrow> salpha" ("_" [990] 990)
  "_salphavar"   :: "svid \<Rightarrow> salpha" ("$_" [990] 990)
  "_salphaparen" :: "salpha \<Rightarrow> salpha" ("'(_')")
  "_salphaunion" :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr "\<union>" 75)
  "_salphainter" :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr "\<inter>" 75)
  "_salphaminus" :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixl "-" 65)
  "_salphacompl" :: "salpha \<Rightarrow> salpha" ("- _" [81] 80)
  "_salpha_all"  :: "salpha" ("\<Sigma>")
  "_salpha_none" :: "salpha" ("\<emptyset>")
(*  "_salpha_pre"  :: "salpha \<Rightarrow> salpha" ("_\<^sup><" [989] 989)
  "_salpha_post" :: "salpha \<Rightarrow> salpha" ("_\<^sup>>" [989] 989) *)
  "_salphaset"   :: "svids \<Rightarrow> salpha" ("{_}")
  "_sframeid"    :: "id \<Rightarrow> sframe" ("_")
  "_sframeset"   :: "svids \<Rightarrow> sframe_enum" ("\<lbrace>_\<rbrace>")
  "_sframeunion" :: "sframe \<Rightarrow> sframe \<Rightarrow> sframe" (infixr "\<union>" 75)
  "_sframeinter" :: "sframe \<Rightarrow> sframe \<Rightarrow> sframe" (infixr "\<inter>" 75)
  "_sframeminus" :: "sframe \<Rightarrow> sframe \<Rightarrow> sframe" (infixl "-" 65)
  "_sframecompl" :: "sframe \<Rightarrow> sframe" ("- _" [81] 80)
  "_sframe_all"  :: "sframe" ("\<Sigma>")
  "_sframe_none" :: "sframe" ("\<emptyset>")
  "_sframe_pre"  :: "sframe \<Rightarrow> sframe" ("_\<^sup><" [989] 989)
  "_sframe_post" :: "sframe \<Rightarrow> sframe" ("_\<^sup>>" [989] 989)
  "_sframe_enum" :: "sframe_enum \<Rightarrow> sframe" ("_")
  "_sframe_alpha" :: "sframe_enum \<Rightarrow> salpha" ("_")
  "_salphamk"    :: "logic \<Rightarrow> salpha"
  "_mk_alpha_list" :: "svids \<Rightarrow> logic"
  "_mk_frame_list" :: "svids \<Rightarrow> logic"

text \<open> The terminals of an alphabet are either HOL identifiers or UTP variable identifiers. 
  We support two ways of constructing alphabets; by composition of smaller alphabets using
  a semi-colon or by a set-style construction $\{a,b,c\}$ with a list of UTP variables. \<close>

syntax \<comment> \<open> Quotations \<close>
  "_svid_set"    :: "svids \<Rightarrow> logic" ("{_}\<^sub>v")
  "_svid_empty"  :: "logic" ("{}\<^sub>v")
  "_svar"        :: "svid \<Rightarrow> logic" ("'(_')\<^sub>v")
  
text \<open> For various reasons, the syntax constructors above all yield specific grammar categories and
  will not parser at the HOL top level (basically this is to do with us wanting to reuse the syntax
  for expressions). As a result we provide some quotation constructors above. 

  Next we need to construct the syntax translations rules. Finally, we set up the translations rules. \<close>

translations
  \<comment> \<open> Identifiers \<close>
  "_svid x" \<rightharpoonup> "x"
  "_svlongid x" \<rightharpoonup> "x"
  "_svid_alpha" \<rightleftharpoons> "CONST univ_var"
  "_svid_tuple xs" \<rightharpoonup> "_mk_svid_list xs"
  "_svid_dot x y" \<rightleftharpoons> "CONST ns_alpha x y"
  "_svid_index x i" \<rightharpoonup> "x i"
  "_svid_res x y" \<rightleftharpoons> "x /\<^sub>L y" 
  "_svid_pre x" \<rightleftharpoons> "_svid_dot fst\<^sub>L x"
  "_svid_post x" \<rightleftharpoons> "_svid_dot snd\<^sub>L x"
  "_svid_fst x" \<rightleftharpoons> "CONST var_fst x"
  "_svid_snd x" \<rightleftharpoons> "CONST var_snd x"
  "_svid_prod x y" \<rightleftharpoons> "x \<times>\<^sub>L y"
  "_svid_pow2 x" \<rightharpoonup> "x \<times>\<^sub>L x"
  "_mk_svid_list (_svid_list x xs)" \<rightharpoonup> "CONST var_pair x (_mk_svid_list xs)"
  "_mk_svid_list x" \<rightharpoonup> "x"
  "_mk_alpha_list (_svid_list x xs)" \<rightharpoonup> "CONST var_alpha x \<squnion>\<^sub>S _mk_alpha_list xs"
  "_mk_alpha_list x" \<rightharpoonup> "CONST var_alpha x"

  "_svid_view a" => "\<V>\<^bsub>a\<^esub>"
  "_svid_coview a" => "\<C>\<^bsub>a\<^esub>"

  "_svid_list (_svid_tuple (_of_svid_list (CONST var_pair x y))) (_of_svid_list z)" \<leftharpoondown> "_of_svid_list (CONST var_pair (CONST var_pair x y) z)"
  "_svid_list x (_of_svid_list y)"    \<leftharpoondown> "_of_svid_list (CONST var_pair x y)"
  "x"                                 \<leftharpoondown> "_of_svid_list x"

  "_svid_tuple (_svid_list x y)" \<leftharpoondown> "CONST var_pair x y"
  "_svid_list x ys" \<leftharpoondown> "_svid_list x (_svid_tuple ys)"

  \<comment> \<open> Alphabets \<close>
  "_salphaparen a" \<rightharpoonup> "a"
  "_salphaid x" \<rightharpoonup> "x"
  "_salphaunion x y" \<rightharpoonup> "x \<squnion>\<^sub>S y"
  "_salphainter x y" \<rightharpoonup> "x \<sqinter>\<^sub>S y"
  "_salphaminus x y" \<rightharpoonup> "x - y"
  "_salphacompl x"  \<rightharpoonup> "- x"
(*  "_salpha_pre A" \<rightharpoonup> "A ;\<^sub>S fst\<^sub>L"
  "_salpha_post A" \<rightharpoonup> "A ;\<^sub>S snd\<^sub>L" *)
(*  "_salphaprod a b" \<rightleftharpoons> "a \<times>\<^sub>L b" *)
  "_salphavar x" \<rightleftharpoons> "CONST var_alpha x"
  "_salphaset A" \<rightharpoonup> "_mk_alpha_list A"  
  "_sframeid A" \<rightharpoonup> "A"
  "(_svid_list x (_salphamk y))" \<leftharpoondown> "_salphamk (x +\<^sub>L y)" 
  "x" \<leftharpoondown> "_salphamk x"
  "_salpha_all" \<rightleftharpoons> "CONST univ_alpha"
  "_salpha_none" \<rightleftharpoons> "CONST emp_alpha"

  \<comment> \<open> Quotations \<close>
  "_svid_set A" \<rightharpoonup> "_mk_alpha_list A"
  "_svid_empty" \<rightharpoonup> "0\<^sub>L"
  "_svar x" \<rightharpoonup> "x"

text \<open> The translation rules mainly convert syntax into lens constructions, using a mixture
  of lens operators and the bespoke variable definitions. Notably, a colon variable identifier
  qualification becomes a lens composition, and variable sets are constructed using len sum. 
  The translation rules are carefully crafted to ensure both parsing and pretty printing. 

  Finally we create the following useful utility translation function that allows us to construct a 
  UTP variable (lens) type given a return and alphabet type. \<close>

syntax
  "_uvar_ty"      :: "type \<Rightarrow> type \<Rightarrow> type"

parse_translation \<open>
let
  fun uvar_ty_tr [ty] = Syntax.const @{type_syntax lens} $ ty $ Syntax.const @{type_syntax dummy}
    | uvar_ty_tr ts = raise TERM ("uvar_ty_tr", ts);
in [(@{syntax_const "_uvar_ty"}, K uvar_ty_tr)] end
\<close>

subsection \<open> Simplifications \<close>

lemma get_pre [simp]: "get\<^bsub>(x\<^sup><)\<^sub>v\<^esub> (s\<^sub>1, s\<^sub>2) = get\<^bsub>x\<^esub> s\<^sub>1"
  by (simp add: lens_defs)

lemma get_post [simp]: "get\<^bsub>(x\<^sup>>)\<^sub>v\<^esub> (s\<^sub>1, s\<^sub>2) = get\<^bsub>x\<^esub> s\<^sub>2"
  by (simp add: lens_defs)

lemma get_prod_decomp: "get\<^bsub>x\<^esub> s = (get\<^bsub>var_fst x\<^esub> s, get\<^bsub>var_snd x\<^esub> s)"
  by (simp add: lens_defs)

end