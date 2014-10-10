(*
  Theory: PDF_Values.thy
  Author: Manuel Eberl

  Defines the values and types in the PDF language and the corresponding stock measure spaces.
  Additionally, some functions and lemmas for lifting functions on the HOL types (int, real, \<dots>)
  to PDF values are provided.
*)

header {* Source Language Values *}

theory PDF_Values
imports Giry_Monad Density_Predicates Measure_Embeddings PDF_Misc
begin

subsection {* Values and stock measures *}

datatype pdf_type =  UNIT | BOOL | INTEG | REAL | PRODUCT pdf_type pdf_type

datatype val = UnitVal | BoolVal bool | IntVal int | RealVal real | 
               PairVal val val  ("<|_, _|>"  [0,  61] 1000)

abbreviation "TRUE \<equiv> BoolVal True"
abbreviation "FALSE \<equiv> BoolVal False"

type_synonym vname = "nat"
type_synonym state = "vname \<Rightarrow> val"

definition "RealPairVal \<equiv> \<lambda>(x,y). <|RealVal x, RealVal y|>"
definition "extract_real_pair \<equiv> \<lambda><|RealVal x, RealVal y|> \<Rightarrow> (x,y)"
definition "IntPairVal \<equiv> \<lambda>(x,y). <|IntVal x, IntVal y|>"
definition "extract_int_pair \<equiv> \<lambda><|IntVal x, IntVal y|> \<Rightarrow> (x,y)"

lemma inj_RealPairVal: "inj RealPairVal" by (auto simp: RealPairVal_def intro!: injI)
lemma inj_IntPairVal: "inj IntPairVal" by (auto simp: IntPairVal_def intro!: injI)

primrec stock_measure :: "pdf_type \<Rightarrow> val measure" where
  "stock_measure UNIT = count_space {UnitVal}"
| "stock_measure INTEG = count_space (range IntVal)"
| "stock_measure BOOL = count_space (range BoolVal)"
| "stock_measure REAL = embed_measure lborel RealVal"
| "stock_measure (PRODUCT t1 t2) = 
       embed_measure (stock_measure t1 \<Otimes>\<^sub>M stock_measure t2) (\<lambda>(a, b). PairVal a b)"

lemma sigma_finite_stock_measure[simp]: "sigma_finite_measure (stock_measure t)"
  by (induction t)
     (auto intro!: sigma_finite_measure_count_space_countable sigma_finite_pair_measure 
                   sigma_finite_embed_measure injI sigma_finite_lborel)

fun val_type :: "val \<Rightarrow> pdf_type" where
  "val_type (BoolVal b) = BOOL"
| "val_type (IntVal i) = INTEG"
| "val_type UnitVal = UNIT"
| "val_type (RealVal r) = REAL"
| "val_type (<|v1 , v2|>) = (PRODUCT (val_type v1) (val_type v2))"

definition "type_universe t = {v. val_type v = t}"


lemma space_stock_measure[simp]: 
    "space (stock_measure t) = type_universe t"
  by (induction t) (auto simp: space_embed_measure space_pair_measure type_universe_def 
                         elim: val_type.elims)

lemma val_in_type_universe[simp]:
    "v \<in> type_universe (val_type v)"
  by (simp add: type_universe_def)

lemma type_universe_type[simp]:
    "w \<in> type_universe t \<Longrightarrow> val_type w = t"
  by (simp add: type_universe_def)

lemma type_universe_nonempty[simp]:
    "type_universe t \<noteq> {}"
  by (subst space_stock_measure[symmetric], induction t) 
     (auto simp: space_pair_measure space_embed_measure simp del: space_stock_measure)


lemma inj_RealVal[simp]: "inj RealVal" by (auto intro!: inj_onI)
lemma inj_IntVal[simp]: "inj IntVal" by (auto intro!: inj_onI)
lemma inj_BoolVal[simp]: "inj BoolVal" by (auto intro!: inj_onI)
lemma inj_PairVal: "inj (\<lambda>(x, y). <| x ,  y |>)" by (auto intro: injI)

lemma nn_integral_BoolVal:
  assumes "\<And>x. x \<in> space (stock_measure BOOL) \<Longrightarrow> f x \<ge> 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>stock_measure BOOL) = f (BoolVal True) + f (BoolVal False)"
proof-
  have A: "range BoolVal = {BoolVal True, BoolVal False}" by auto
  from assms show ?thesis
    by (subst stock_measure.simps, subst A, subst nn_integral_count_space_finite)
       (simp_all add: max_def A)
qed

lemma nn_integral_RealVal:
  assumes "f \<in> borel_measurable (embed_measure lborel RealVal)"
  shows "(\<integral>\<^sup>+x. f x \<partial>embed_measure lborel RealVal) = (\<integral>\<^sup>+x. f (RealVal x) \<partial>lborel)"
  using assms by (subst embed_measure_eq_distr, simp, subst nn_integral_distr) simp_all

lemma nn_integral_IntVal:
  "(\<integral>\<^sup>+x. f x \<partial>count_space (range IntVal)) = (\<integral>\<^sup>+x. f (IntVal x) \<partial>count_space UNIV)"
  by (subst embed_measure_count_space[symmetric], simp, subst embed_measure_eq_distr,
       simp, subst nn_integral_distr) (simp_all add: space_embed_measure)


definition extract_pair where "extract_pair \<equiv> \<lambda> <|v,w|> \<Rightarrow> (v,w)"
definition extract_bool where "extract_bool \<equiv> \<lambda> BoolVal v \<Rightarrow> v"
definition extract_real where "extract_real \<equiv> \<lambda> RealVal v \<Rightarrow> v | _ \<Rightarrow> 0"
definition extract_int where "extract_int \<equiv> \<lambda> IntVal v \<Rightarrow> v | _ \<Rightarrow> 0"

lemma BOOL_E: "\<lbrakk>val_type v = BOOL; \<And>b. v = BoolVal b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
   using assms by (cases v) auto

lemma REAL_E: "\<lbrakk>val_type v = REAL; \<And>b. v = RealVal b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
   using assms by (cases v) auto

lemma measurable_extract_pair[measurable]:
    "extract_pair \<in> measurable (embed_measure (M \<Otimes>\<^sub>M N) (\<lambda>(x,y). <|x,y|>)) (M  \<Otimes>\<^sub>M N)"
  apply (rule measurable_embed_measure1)
  apply (subst measurable_cong[of _ _ "\<lambda>x. x"])
  apply (auto simp: extract_pair_def)
  done

lemma measurable_extract_real[measurable]:
    "extract_real \<in> measurable (embed_measure lborel RealVal) borel"
  apply (rule measurable_embed_measure1)
  apply (subst measurable_cong[of _ _ "\<lambda>x. x"])
  apply (auto simp: extract_real_def)
  done

lemma measurable_extract_int_pair[measurable]:
  "extract_int_pair \<in> measurable (embed_measure (count_space (range IntVal \<times> range IntVal))
                          (\<lambda>(x, y). <|x, y|>)) (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)"
  unfolding extract_int_pair_def by (simp add: pair_measure_countable)

lemma measurable_extract_int[measurable]:
    "extract_int \<in> measurable (count_space (range IntVal)) (count_space UNIV)"
    by (rule measurable_count_space)

lemma measurable_extract_bool[measurable]:
    "extract_bool \<in> measurable (count_space (range BoolVal)) (count_space UNIV)"
    by (rule measurable_count_space)


lemma count_space_IntVal_prod[simp]:
    "count_space (range IntVal) \<Otimes>\<^sub>M count_space (range IntVal) = 
         count_space (range IntVal \<times> range IntVal)"
    by (rule pair_measure_countable) simp_all

lemma count_space_BoolVal_prod[simp]:
    "count_space (range BoolVal) \<Otimes>\<^sub>M count_space (range BoolVal) = 
         count_space (range BoolVal \<times> range BoolVal)"
    by (rule pair_measure_countable) simp_all

lemma measurable_PairVal1:
  assumes "x \<in> space (stock_measure t1)"
  shows "PairVal x \<in> measurable (stock_measure t2) 
                      (embed_measure (stock_measure t1 \<Otimes>\<^sub>M stock_measure t2) (split PairVal))"
using assms inj_PairVal by simp

lemma measurable_stock_measure_val_type:
  assumes "f \<in> measurable M (stock_measure t)" "x \<in> space M"
  shows "val_type (f x) = t"
  using assms by (auto dest!: measurable_space)

lemma type_universe_eq_imp_type_eq: 
  assumes "type_universe t1 = type_universe t2"
  shows "t1 = t2"
proof-
  from type_universe_nonempty obtain v where A: "v \<in> type_universe t1" by blast
  hence "t1 = val_type v" by simp
  also from A and assms have "v \<in> type_universe t2" by simp
  hence "val_type v = t2" by simp
  finally show ?thesis .
qed

lemma type_universe_eq_iff[simp]: "type_universe t1 = type_universe t2 \<longleftrightarrow> t1 = t2"
  by (blast intro: type_universe_eq_imp_type_eq)

lemma singleton_in_stock_measure[simp]:
  "{v} \<in> sets (stock_measure (val_type v))"
proof (induction v)
  case (PairVal v1 v2)
  have A: "{<|v1, v2|>} = (\<lambda>(v1,v2). <|v1,v2|>) ` ({v1}\<times>{v2})" by simp
  from pair_measureI[OF PairVal.IH] show ?case
    by (simp only: val_type.simps stock_measure.simps A in_sets_embed_measure)
qed (auto simp: sets_embed_measure)

lemma emeasure_stock_measure_singleton_finite[simp]:
    "emeasure (stock_measure (val_type v)) {v} \<noteq> \<infinity>"
proof (induction v)
  case (RealVal r)
  have A: "{RealVal r} = RealVal ` {r}" by simp
  have "RealVal ` {r} \<in> sets (embed_measure lborel RealVal)"
      by (rule in_sets_embed_measure) simp
  thus ?case by (simp only: A val_type.simps stock_measure.simps emeasure_embed_measure 
                            inj_RealVal inj_vimage_image_eq) simp
next
  case (PairVal v1 v2)
    let ?M = "\<lambda>x. stock_measure (val_type x)"
    interpret sigma_finite_measure "stock_measure (val_type v2)"
      by (rule sigma_finite_stock_measure)
    have A: "{<|v1, v2|>} = (\<lambda>(v1,v2). <|v1,v2|>) ` ({v1}\<times>{v2})" by simp
    have B: "{v1}\<times>{v2} \<in> ?M v1 \<Otimes>\<^sub>M ?M v2"
      by (intro pair_measureI singleton_in_stock_measure)
    hence "emeasure (?M (<|v1,v2|>)) {<|v1,v2|>} = emeasure (?M v1) {v1} * emeasure (?M v2) {v2}"
      by (simp only: stock_measure.simps val_type.simps A emeasure_embed_measure_image inj_PairVal 
                     inj_vimage_image_eq emeasure_pair_measure_Times singleton_in_stock_measure B)
    with PairVal.IH show ?case by simp
qed simp_all


subsection {* Measures on states *}

definition state_measure :: "vname set \<Rightarrow> (vname \<Rightarrow> pdf_type) \<Rightarrow> state measure" where
  "state_measure V \<Gamma> \<equiv> \<Pi>\<^sub>M y\<in>V. stock_measure (\<Gamma> y)"

lemma state_measure_nonempty[simp]: "space (state_measure V \<Gamma>) \<noteq> {}"
  by (simp add: state_measure_def space_PiM PiE_eq_empty_iff)

lemma state_measure_var_type:
    "\<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> x \<in> V \<Longrightarrow> val_type (\<sigma> x) = \<Gamma> x"
  by (auto simp: state_measure_def space_PiM dest!: PiE_mem)

lemma merge_in_state_measure:
  "x \<in> space (state_measure A \<Gamma>) \<Longrightarrow> y \<in> space (state_measure B \<Gamma>) \<Longrightarrow> 
      merge A B (x, y) \<in> space (state_measure (A\<union>B) \<Gamma>)" unfolding state_measure_def
  by (rule measurable_space, rule measurable_merge) (simp add: space_pair_measure)

lemma comp_in_state_measure:
    assumes "\<sigma> \<in> space (state_measure V \<Gamma>)"
    shows "\<sigma> \<circ> f \<in> space (state_measure (f -` V) (\<Gamma> \<circ> f))"
  using assms by (auto simp: state_measure_def space_PiM)

lemma sigma_finite_state_measure[intro]:
    "finite V \<Longrightarrow> sigma_finite_measure (state_measure V \<Gamma>)" unfolding state_measure_def
  by (auto intro!: product_sigma_finite.sigma_finite simp: product_sigma_finite_def)


subsection {* Equalities of measure embeddings *}

lemma embed_measure_RealPairVal:
   "stock_measure (PRODUCT REAL REAL) = embed_measure lborel RealPairVal"
proof-
  have [simp]: "(\<lambda>(x, y). <| x ,  y |>) \<circ> (\<lambda>(x, y). (RealVal x, RealVal y)) = RealPairVal"
    unfolding RealPairVal_def by auto
  have "stock_measure (PRODUCT REAL REAL) = 
            embed_measure (embed_measure lborel (\<lambda>(x, y). (RealVal x, RealVal y))) (split PairVal)"
    by (auto simp: embed_measure_prod sigma_finite_lborel lborel_prod)
  also have "... = embed_measure lborel RealPairVal"
    by (subst embed_measure_comp) (auto intro!: injI)
  finally show ?thesis .
qed

lemma embed_measure_IntPairVal:
   "stock_measure (PRODUCT INTEG INTEG) = (count_space (range IntPairVal))"
proof-
  have [simp]: "(\<lambda>(x, y). <| x ,  y |>) ` (range IntVal \<times> range IntVal) = range IntPairVal"
    by (auto simp: IntPairVal_def)
  show ?thesis by (auto simp: embed_measure_prod embed_measure_count_space inj_PairVal)
qed

subsection {* Monadic operations on values *}

definition "return_val x = return (stock_measure (val_type x)) x"

lemma sets_return_val: "sets (return_val x) = sets (stock_measure (val_type x))"
    by (simp add: return_val_def)

lemma measurable_return_val[simp]:
    "return_val \<in> measurable (stock_measure t) (kernel_space (stock_measure t))"
  unfolding return_val_def[abs_def]
  apply (subst measurable_cong)
  apply (subst (asm) space_stock_measure, subst type_universe_type, assumption, rule refl)
  apply (rule return_measurable)
  done
  
lemma bind_return_val:
  assumes "space M \<noteq> {}" "f \<in> measurable M (stock_measure t')"
  shows "M \<guillemotright>= (\<lambda>x. return_val (f x)) = distr M (stock_measure t') f"
  using assms
  by (subst bind_return_distr[symmetric])
     (auto simp: return_val_def intro!: bind_cong dest: measurable_stock_measure_val_type)

lemma bind_return_val':
  assumes "val_type x = t" "f \<in> measurable (stock_measure t) (stock_measure t')"
  shows "return_val x \<guillemotright>= (\<lambda>x. return_val (f x)) = return_val (f x)"
proof-
  have "return_val x \<guillemotright>= (\<lambda>x. return_val (f x)) = return (stock_measure t') (f x)"
    apply (subst bind_return_val, unfold return_val_def, simp)
    apply (insert assms, simp cong: measurable_cong_sets) []
    apply (subst distr_return, simp_all add: assms type_universe_def 
                                        del: type_universe_type)
    done
  also from assms(2) have "f x \<in> space (stock_measure t')"
    by (rule measurable_space) 
       (simp add: assms(1) type_universe_def del: type_universe_type)
  hence "return (stock_measure t') (f x) = return_val (f x)" 
    by (simp add: return_val_def)
  finally show ?thesis .
qed

lemma bind_return_val'':
  assumes "f \<in> measurable (stock_measure (val_type x)) (kernel_space M)"
  shows "return_val x \<guillemotright>= f = f x"
unfolding return_val_def by (subst bind_return[OF assms]) simp_all

lemma bind_assoc_return_val:
  assumes sets_M: "sets M = sets (stock_measure t)"
  assumes Mf: "f \<in> measurable (stock_measure t) (stock_measure t')"
  assumes Mg: "g \<in> measurable (stock_measure t') (stock_measure t'')"
  shows "(M \<guillemotright>= (\<lambda>x. return_val (f x))) \<guillemotright>= (\<lambda>x. return_val (g x)) =
             M \<guillemotright>= (\<lambda>x. return_val (g (f x)))"
proof-
  have "(M \<guillemotright>= (\<lambda>x. return_val (f x))) \<guillemotright>= (\<lambda>x. return_val (g x)) = 
           M \<guillemotright>= (\<lambda>x. return_val (f x) \<guillemotright>= (\<lambda>x. return_val (g x)))"
    apply (subst bind_assoc)
    apply (rule measurable_compose[OF _ measurable_return_val])
    apply (subst measurable_cong_sets[OF sets_M refl], rule Mf)
    apply (rule measurable_compose[OF Mg measurable_return_val], rule refl)
    done
  also have "... = M \<guillemotright>= (\<lambda>x. return_val (g (f x)))"
    apply (intro bind_cong ballI)
    apply (subst (asm) sets_eq_imp_space_eq[OF sets_M])
    apply (drule measurable_space[OF Mf])
    apply (subst bind_return_val'[where t = t' and t' = t''])
    apply (simp_all add: Mg)
    done
  finally show ?thesis .
qed

lemma bind_return_val_distr:
  assumes sets_M: "sets M = sets (stock_measure t)"
  assumes Mf: "f \<in> measurable (stock_measure t) (stock_measure t')"
  shows "M \<guillemotright>= return_val \<circ> f = distr M (stock_measure t') f"
proof-
  have "M \<guillemotright>= return_val \<circ> f = M \<guillemotright>= return (stock_measure t') \<circ> f"
    apply (intro bind_cong ballI)
    apply (subst (asm) sets_eq_imp_space_eq[OF sets_M])
    apply (drule measurable_space[OF Mf])
    apply (simp add: return_val_def o_def)
    done
  also have "... = distr M (stock_measure t') f"
    apply (rule bind_return_distr)
    apply (simp add: sets_eq_imp_space_eq[OF sets_M])
    apply (subst measurable_cong_sets[OF sets_M refl], rule Mf)
    done
  finally show ?thesis .
qed


subsection {* Lifting of functions *}

definition lift_RealVal where 
  "lift_RealVal f \<equiv> \<lambda> RealVal v \<Rightarrow> RealVal (f v) | _ \<Rightarrow> RealVal (f 0)"
definition lift_IntVal where 
  "lift_IntVal f \<equiv> \<lambda> IntVal v \<Rightarrow> IntVal (f v) | _ \<Rightarrow> IntVal (f 0)"
definition lift_RealIntVal where 
  "lift_RealIntVal f g \<equiv> \<lambda> IntVal v \<Rightarrow> IntVal (f v) | RealVal v \<Rightarrow> RealVal (g v)"
definition lift_RealIntVal2 where 
  "lift_RealIntVal2 f g \<equiv> \<lambda> <|IntVal v, IntVal w|> \<Rightarrow> IntVal (f v w) 
                          | <|RealVal v, RealVal w|> \<Rightarrow> RealVal (g v w)"
definition lift_Comp where
  "lift_Comp f g \<equiv> \<lambda> <|IntVal v, IntVal w|> \<Rightarrow> BoolVal (f v w) 
                   | <|RealVal v, RealVal w|> \<Rightarrow> BoolVal (g v w)"

lemma lift_RealIntVal_Real:
  "x \<in> space (stock_measure REAL) \<Longrightarrow> lift_RealIntVal f g x = lift_RealVal g x"
  by (auto simp: space_embed_measure lift_RealIntVal_def lift_RealVal_def)

lemma lift_RealIntVal_Int:
  "x \<in> space (stock_measure INTEG) \<Longrightarrow> lift_RealIntVal f g x = lift_IntVal f x"
  by (auto simp: space_embed_measure lift_RealIntVal_def lift_IntVal_def)

lemma measurable_lift_RealVal[measurable]:
  assumes "f \<in> borel_measurable borel"
  shows "lift_RealVal f \<in> measurable (embed_measure lborel RealVal) (embed_measure lborel RealVal)"
    (is "_ \<in> measurable ?M _")
proof-
  have "lift_RealVal f = RealVal \<circ> f \<circ> extract_real"
    unfolding lift_RealVal_def extract_real_def by (intro ext) (auto split: val.split)
  also have "RealVal \<in> measurable borel ?M" by simp
  hence "RealVal \<circ> f \<circ> extract_real \<in> measurable ?M ?M"
    by (intro measurable_comp) (blast intro!: measurable_extract_real assms)+
  finally show ?thesis .
qed

lemma measurable_lift_IntVal[simp]:
    "lift_IntVal f \<in> range IntVal \<rightarrow> range IntVal"
  by (auto simp: lift_IntVal_def)

lemma measurable_lift_Comp_RealVal[measurable]:
  assumes "Measurable.pred (borel \<Otimes>\<^sub>M borel) (split g)"
  shows "lift_Comp f g \<in> measurable (embed_measure (embed_measure lborel RealVal \<Otimes>\<^sub>M 
                                        embed_measure lborel RealVal) (split PairVal))
                                    (count_space (range BoolVal))" 
    (is "_ \<in> measurable ?M ?N")
proof- 
  have "\<And>x. x \<in> space ?M \<Longrightarrow> lift_Comp f g x = 
                (BoolVal \<circ> (\<lambda>x. g (fst x) (snd x)) \<circ> 
                (\<lambda>(x,y). (extract_real x, extract_real y)) \<circ> extract_pair) x"
    by (auto simp: o_def extract_real_def extract_pair_def 
             lift_Comp_def space_pair_measure space_embed_measure split: val.split)
  moreover have "... \<in> measurable ?M ?N"
    by (intro measurable_comp, rule measurable_extract_pair, subst measurable_split_conv,
        rule measurable_Pair, rule measurable_compose[OF measurable_fst measurable_extract_real],
        rule measurable_compose[OF measurable_snd measurable_extract_real],
        subst measurable_split_conv[symmetric], rule assms, simp)
  ultimately show ?thesis by (simp cong: measurable_cong)
qed

lemma measurable_lift_Comp_IntVal[simp]:
    "lift_Comp f g \<in> measurable (embed_measure (count_space (range IntVal) \<Otimes>\<^sub>M 
                                    count_space (range IntVal)) (split PairVal))
                                (count_space (range BoolVal))"
  by (auto simp: lift_Comp_def embed_measure_count_space inj_PairVal)

lemma measurable_lift_RealIntVal_IntVal[simp]:
    "lift_RealIntVal f g \<in> range IntVal \<rightarrow> range IntVal"
  by (auto simp: embed_measure_count_space lift_RealIntVal_def)

lemma measurable_lift_RealIntVal_RealVal[measurable]:
  assumes "g \<in> borel_measurable borel"
  shows "lift_RealIntVal f g \<in> 
           measurable (embed_measure lborel RealVal) (embed_measure lborel RealVal)"
    (is "_ \<in> measurable ?M _")
proof-
  have "\<And>x. x \<in> space ?M \<Longrightarrow> lift_RealIntVal f g x = lift_RealVal g x"
    unfolding lift_RealVal_def lift_RealIntVal_def 
    by (auto split: val.split simp: space_embed_measure)
  with assms and measurable_lift_RealVal show ?thesis by (simp cong: measurable_cong)
qed

lemma measurable_lift_RealIntVal2_IntVal[measurable]:
    "lift_RealIntVal2 f g \<in> measurable (embed_measure (count_space (range IntVal) \<Otimes>\<^sub>M 
                                          count_space (range IntVal)) (split PairVal))
                                       (count_space (range IntVal))"
  by (auto simp: lift_RealIntVal2_def embed_measure_count_space inj_PairVal)

lemma measurable_lift_RealIntVal2_RealVal[measurable]:
  assumes "(\<lambda>x. g (fst x) (snd x)) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
  shows "lift_RealIntVal2 f g \<in> measurable (embed_measure (embed_measure lborel RealVal \<Otimes>\<^sub>M 
                                                embed_measure lborel RealVal) (split PairVal))
                                           (embed_measure lborel RealVal)"
    (is "_ \<in> measurable ?M ?N")
proof- 
  have "\<And>x. x \<in> space ?M \<Longrightarrow> lift_RealIntVal2 f g x = 
                (RealVal \<circ> (\<lambda>x. g (fst x) (snd x)) \<circ> 
                (\<lambda>(x,y). (extract_real x, extract_real y)) \<circ> extract_pair) x"
    by (auto simp: o_def extract_real_def extract_pair_def 
             lift_RealIntVal2_def space_pair_measure space_embed_measure split: val.split)
  moreover have "... \<in> measurable ?M ?N"
    by (intro measurable_comp, rule measurable_extract_pair, subst measurable_split_conv,
        rule measurable_Pair, rule measurable_compose[OF measurable_fst measurable_extract_real],
        rule measurable_compose[OF measurable_snd measurable_extract_real], rule assms,
        subst measurable_lborel2[symmetric], rule measurable_embed_measure2, rule inj_RealVal)
  ultimately show ?thesis by (simp cong: measurable_cong)
qed

lemma distr_lift_RealVal: 
  fixes f
  assumes Mf: "f \<in> borel_measurable borel"
  assumes pdens: "has_subprob_density M (stock_measure REAL) \<delta>"
  assumes dens': "\<And>M \<delta>. has_subprob_density M lborel \<delta> \<Longrightarrow> has_density (distr M borel f) lborel (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure REAL) (lift_RealVal f)"
  shows "has_density N (stock_measure REAL) (g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real)"
proof (rule has_densityI)
  from assms(2) have dens: "has_density M (stock_measure REAL) \<delta>" 
    unfolding has_subprob_density_def by simp
  have MRV: "RealVal \<in> measurable borel (embed_measure lborel RealVal)"
    by (subst measurable_lborel2[symmetric], rule measurable_embed_measure2) simp
  from dens have sets_M: "sets M = sets (embed_measure lborel RealVal)" by (auto dest: has_densityD)
  
  have "N = distr M (stock_measure REAL) (lift_RealVal f)" by (simp add: N_def)
  also have "lift_RealVal f = RealVal \<circ> f \<circ> extract_real" 
    unfolding lift_RealVal_def extract_real_def by (intro ext) (auto simp: o_def split: val.split)
  also have "distr M (stock_measure REAL) ... = 
               distr (distr (distr M lborel extract_real) borel f) (stock_measure REAL) RealVal"
    apply (subst distr_distr[symmetric], intro measurable_comp, rule assms(1), simp add: MRV)
    apply (subst measurable_cong_sets[OF sets_M refl], rule measurable_extract_real)
    apply (subst distr_distr[symmetric], subst stock_measure.simps, rule MRV, 
           simp_all add: assms(1) cong: distr_cong)
    done
  also have dens'': "has_density (distr (distr M lborel extract_real) borel f) lborel (g (\<delta> \<circ> RealVal))"
    by (intro dens' has_subprob_density_embed_measure'') (insert pdens, simp_all add: extract_real_def)
  hence "distr (distr M lborel extract_real) borel f = density lborel (g (\<delta> \<circ> RealVal))"
    by (rule has_densityD)
  also have "distr ... (stock_measure REAL) RealVal = embed_measure ... RealVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_RealVal], intro distr_cong)
       (simp_all add: sets_embed_measure)
  also have "... = density (embed_measure lborel RealVal) (g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real)"
    using dens''[unfolded o_def]
    apply (subst density_embed_measure', simp, simp add: extract_real_def)
    apply (erule has_densityD, simp add: o_def)
    done
  finally show "N = density (stock_measure REAL) (g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real)" by simp

  from dens''[unfolded o_def] 
    show "g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real \<in> borel_measurable (stock_measure REAL)"
    by (intro measurable_comp, subst stock_measure.simps)
       (rule measurable_extract_real, subst measurable_lborel2[symmetric], erule has_densityD)
  fix x assume "x \<in> space (stock_measure REAL)"
  thus "(g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real) x \<ge> 0" unfolding o_def
    by (intro has_densityD(2)[OF dens''[unfolded o_def]]) auto
qed (subst space_stock_measure, simp)

lemma distr_lift_IntVal: 
  fixes f
  assumes pdens: "has_density M (stock_measure INTEG) \<delta>"
  assumes dens': "\<And>M \<delta>. has_density M (count_space UNIV) \<delta> \<Longrightarrow> 
                            has_density (distr M (count_space UNIV) f) (count_space UNIV) (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure INTEG) (lift_IntVal f)"
  shows "has_density N (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int)"
proof (rule has_densityI)
  let ?R = "count_space UNIV" and ?S = "count_space (range IntVal)"
  have Mf: "f \<in> measurable ?R ?R" by simp
  have MIV: "IntVal \<in> measurable ?R ?S" by simp
  from assms(1) have dens: "has_density M (stock_measure INTEG) \<delta>" 
    unfolding has_subprob_density_def by simp
  from dens have sets_M: "sets M = sets ?S" by (auto dest!: has_densityD(3))
  
  have "N = distr M (stock_measure INTEG) (lift_IntVal f)" by (simp add: N_def)
  also have "lift_IntVal f = IntVal \<circ> f \<circ> extract_int" 
    unfolding lift_IntVal_def extract_int_def by (intro ext) (auto simp: o_def split: val.split)
  also have "distr M (stock_measure INTEG) ... = 
               distr (distr (distr M ?R extract_int) ?R f) (stock_measure INTEG) IntVal"
    apply (subst distr_distr[symmetric], intro measurable_comp, rule Mf, simp)
    apply (subst measurable_cong_sets[OF sets_M refl], simp)
    apply (subst distr_distr[symmetric], subst stock_measure.simps, rule MIV, simp_all add: Mf)
    done
  also have dens'': "has_density (distr (distr M ?R extract_int) ?R f) ?R (g (\<delta> \<circ> IntVal))"
    by (intro dens' has_density_embed_measure'') 
       (insert dens, simp_all add: extract_int_def embed_measure_count_space)
  hence "distr (distr M ?R extract_int) ?R f = density ?R (g (\<delta> \<circ> IntVal))"
    by (rule has_densityD)
  also have "distr ... (stock_measure INTEG) IntVal = embed_measure ... IntVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_IntVal], intro distr_cong)
       (auto simp: sets_embed_measure subset_image_iff)
  also have "... = density (embed_measure ?R IntVal) (g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int)"
    using dens''[unfolded o_def]
    apply (subst density_embed_measure', simp, simp add: extract_int_def)
    apply (erule has_densityD, simp add: o_def)
    done
  finally show "N = density (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int)" 
    by (simp add: embed_measure_count_space)

  from dens''[unfolded o_def] 
    show "g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int \<in> borel_measurable (stock_measure INTEG)"
    by (simp add: embed_measure_count_space)
  fix x assume "x \<in> space (stock_measure INTEG)"
  thus "(g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int) x \<ge> 0" unfolding o_def
    by (intro has_densityD(2)[OF dens''[unfolded o_def]]) auto
qed (subst space_stock_measure, simp)

lemma measurable_extract_real_pair[measurable]:
  "extract_real_pair \<in> borel_measurable (stock_measure (PRODUCT REAL REAL))"
proof-
  let ?f = "\<lambda>x. (extract_real (fst (extract_pair x)), extract_real (snd (extract_pair x)))"
  have "?f \<in> borel_measurable (stock_measure (PRODUCT REAL REAL))" by simp
  also have "?f \<in> borel_measurable (stock_measure (PRODUCT REAL REAL)) \<longleftrightarrow>
                  extract_real_pair \<in> borel_measurable (stock_measure (PRODUCT REAL REAL))"
    by (intro measurable_cong) 
       (auto simp: extract_real_pair_def space_embed_measure 
                   space_pair_measure extract_real_def extract_pair_def)
  finally show ?thesis .
qed

lemma distr_lift_RealPairVal: 
  fixes f f' g
  assumes Mf: "split f \<in> borel_measurable borel"
  assumes pdens: "has_subprob_density M (stock_measure (PRODUCT REAL REAL)) \<delta>"
  assumes dens': "\<And>M \<delta>. has_subprob_density M lborel \<delta> \<Longrightarrow> has_density (distr M borel (split f)) lborel (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure REAL) (lift_RealIntVal2 f' f)"
  shows "has_density N (stock_measure REAL) (g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real)"
proof (rule has_densityI)
  from assms(2) have dens: "has_density M (stock_measure (PRODUCT REAL REAL)) \<delta>" 
    unfolding has_subprob_density_def by simp
  have sets_M: "sets M = sets (stock_measure (PRODUCT REAL REAL))"
    by (auto simp: has_subprob_densityD[OF pdens])
  hence [simp]: "space M = space (stock_measure (PRODUCT REAL REAL))"
    by (rule sets_eq_imp_space_eq)
  have meas_M[simp]: "measurable M = measurable (stock_measure (PRODUCT REAL REAL))"
    by (intro ext measurable_cong_sets) (simp_all add: sets_M)
  have MRV: "RealVal \<in> measurable borel (embed_measure lborel RealVal)"
    by (subst measurable_lborel2[symmetric], rule measurable_embed_measure2) simp
    
  have "N = distr M (stock_measure REAL) (lift_RealIntVal2 f' f)" by (simp add: N_def)
  also have "... = distr M (stock_measure REAL) (RealVal \<circ> split f \<circ> extract_real_pair)"
    by (intro distr_cong) (auto simp: lift_RealIntVal2_def extract_real_pair_def 
                                       space_embed_measure space_pair_measure)
  also have "... = distr (distr (distr M lborel extract_real_pair) borel (split f)) 
                        (stock_measure REAL) RealVal"
    apply (subst distr_distr[symmetric], intro measurable_comp, rule assms(1), simp add: MRV)
    apply (subst meas_M, rule measurable_extract_real_pair)
    apply (subst distr_distr[symmetric], subst stock_measure.simps, rule MRV, 
           simp_all add: assms(1) cong: distr_cong)
    done
  also have dens'': "has_density (distr (distr M lborel extract_real_pair) borel (split f)) lborel 
                      (g (\<delta> \<circ> RealPairVal))" using inj_RealPairVal embed_measure_RealPairVal
    by (intro dens' has_subprob_density_embed_measure'') 
       (insert pdens, simp_all add: extract_real_pair_def RealPairVal_def split: prod.split)
  hence "distr (distr M lborel extract_real_pair) borel (split f) = 
             density lborel (g (\<delta> \<circ> RealPairVal))" by (rule has_densityD)
  also have "distr ... (stock_measure REAL) RealVal = embed_measure ... RealVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_RealVal], intro distr_cong)
       (simp_all add: sets_embed_measure)
  also have "... = density (embed_measure lborel RealVal) (g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real)"
    using dens''[unfolded o_def]
    by (subst density_embed_measure', simp, simp add: extract_real_def)
       (erule has_densityD, simp add: o_def)
  finally show "N = density (stock_measure REAL) (g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real)" by simp

  from dens''[unfolded o_def] 
    show "g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real \<in> borel_measurable (stock_measure REAL)"
    by (intro measurable_comp, subst stock_measure.simps)
       (rule measurable_extract_real, subst measurable_lborel2[symmetric], erule has_densityD)
  fix x assume "x \<in> space (stock_measure REAL)"
  thus "(g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real) x \<ge> 0" unfolding o_def
    by (intro has_densityD(2)[OF dens''[unfolded o_def]]) auto
qed (subst space_stock_measure, simp)

lemma distr_lift_IntPairVal: 
  fixes f f'
  assumes pdens: "has_density M (stock_measure (PRODUCT INTEG INTEG)) \<delta>"
  assumes dens': "\<And>M \<delta>. has_density M (count_space UNIV) \<delta> \<Longrightarrow> 
                            has_density (distr M (count_space UNIV) (split f)) 
                                        (count_space UNIV) (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure INTEG) (lift_RealIntVal2 f f')"
  shows "has_density N (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int)"
proof (rule has_densityI)
  let ?R = "count_space UNIV" and ?S = "count_space (range IntVal)" 
  and ?T = "count_space (range IntPairVal)" and ?tp = "PRODUCT INTEG INTEG"
  have Mf: "f \<in> measurable ?R ?R" by simp
  have MIV: "IntVal \<in> measurable ?R ?S" by simp
  from assms(1) have dens: "has_density M (stock_measure ?tp) \<delta>" 
    unfolding has_subprob_density_def by simp
  from dens have "M = density (stock_measure ?tp) \<delta>" by (rule has_densityD)
  hence sets_M: "sets M = sets ?T" by (subst embed_measure_IntPairVal[symmetric]) auto
  hence [simp]: "space M = space ?T" by (rule sets_eq_imp_space_eq)
  from sets_M have [simp]: "measurable M = measurable (count_space (range IntPairVal))"
    by (intro ext measurable_cong_sets) simp_all
  
  have "N = distr M (stock_measure INTEG) (lift_RealIntVal2 f f')" by (simp add: N_def)

  also have "... = distr M (stock_measure INTEG) (IntVal \<circ> split f \<circ> extract_int_pair)"
    by (intro distr_cong) (auto simp: lift_RealIntVal2_def extract_int_pair_def 
                                       space_embed_measure space_pair_measure IntPairVal_def)
  also have "... = distr (distr (distr M (count_space UNIV) extract_int_pair) 
                        (count_space UNIV) (split f)) (stock_measure INTEG) IntVal"
    apply (subst distr_distr[of _ ?R, symmetric], simp, simp)
    apply (subst distr_distr[symmetric], subst stock_measure.simps, rule MIV, 
           simp_all add: assms(1) cong: distr_cong)
    done
  also have dens'': "has_density (distr (distr M (count_space UNIV) extract_int_pair) ?R (split f)) ?R 
                      (g (\<delta> \<circ> IntPairVal))" using inj_IntPairVal embed_measure_IntPairVal
    by (intro dens' has_density_embed_measure'') 
       (insert dens, simp_all add: extract_int_def embed_measure_count_space 
                         extract_int_pair_def IntPairVal_def split: prod.split)
  hence "distr (distr M (count_space UNIV) extract_int_pair) ?R (split f) = 
             density ?R (g (\<delta> \<circ> IntPairVal))" by (rule has_densityD)
  also have "distr ... (stock_measure INTEG) IntVal = embed_measure ... IntVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_IntVal], intro distr_cong)
       (auto simp: sets_embed_measure subset_image_iff)
  also have "... = density (embed_measure ?R IntVal) (g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int)"
    using dens''[unfolded o_def]
    by (subst density_embed_measure', simp, simp add: extract_int_def)
       (erule has_densityD, simp add: o_def)
  finally show "N = density (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int)" 
    by (simp add: embed_measure_count_space)

  from dens''[unfolded o_def] 
    show "g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int \<in> borel_measurable (stock_measure INTEG)"
    by (simp add: embed_measure_count_space)
  fix x assume "x \<in> space (stock_measure INTEG)"
  thus "(g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int) x \<ge> 0" unfolding o_def
    by (intro has_densityD(2)[OF dens''[unfolded o_def]]) auto
qed (subst space_stock_measure, simp)

end
