(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Implem.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Implem.thy 132885 2016-12-23 18:41:32Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Parametric channel message implementation
  - definition of 'valid' implementations
  - assumptions for channel implementations (formulated as locales)

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section {* Assumptions for Channel Message Implementation *}

text {* We define a series of locales capturing our assumptions on channel message 
implementations. *}

theory Implem
imports Channels Payloads
begin

subsection {* First step: basic implementation locale *}
(**************************************************************************************************)

text {* This locale has no assumptions, it only fixes an implementation function and 
defines some useful abbreviations (impl*, impl*Set) and @{text "valid"}.
*}

locale basic_implem =
  fixes implem :: "chan \<Rightarrow> msg"
begin

abbreviation "implInsec A B M \<equiv> implem (Insec A B M)"
abbreviation "implConfid A B M \<equiv> implem (Confid A B M)"
abbreviation "implAuth A B M \<equiv> implem (Auth A B M)"
abbreviation "implSecure A B M \<equiv> implem (Secure A B M)"

abbreviation implInsecSet :: "msg set \<Rightarrow> msg set"
where "implInsecSet G \<equiv> {implInsec A B M | A B M. M \<in> G}"

abbreviation implConfidSet :: "(agent * agent) set \<Rightarrow> msg set \<Rightarrow> msg set"
where "implConfidSet Ag G \<equiv> {implConfid A B M | A B M.  (A, B) \<in> Ag \<and> M \<in> G}"

abbreviation implAuthSet :: "msg set \<Rightarrow> msg set"
where "implAuthSet G \<equiv> {implAuth A B M | A B M. M \<in> G}"

abbreviation implSecureSet :: "(agent * agent) set \<Rightarrow> msg set \<Rightarrow> msg set"
where "implSecureSet Ag G \<equiv> {implSecure A B M | A B M. (A, B) \<in> Ag \<and> M \<in> G}"

definition
  valid :: "msg set"
where
  "valid \<equiv> {implem (Chan x A B M) | x A B M. M \<in> payload}"

lemma validI:
  "M \<in> payload \<Longrightarrow> implem (Chan x A B M) \<in> valid"
by (auto simp add: valid_def)

lemma validE:
  "X \<in> valid \<Longrightarrow> (\<And> x A B M. X = implem (Chan x A B M) \<Longrightarrow> M \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
by (auto simp add: valid_def)

lemma valid_cases:
fixes X P
assumes "X \<in> valid"
        "(\<And>A B M. X = implInsec A B M \<Longrightarrow> M \<in> payload \<Longrightarrow> P)"
        "(\<And>A B M. X = implConfid A B M \<Longrightarrow> M \<in> payload \<Longrightarrow> P)"
        "(\<And>A B M. X = implAuth A B M \<Longrightarrow> M \<in> payload \<Longrightarrow> P)"
        "(\<And>A B M. X = implSecure A B M \<Longrightarrow> M \<in> payload \<Longrightarrow> P)"
shows "P"
proof -
  from assms have "(\<And> x A B M. X = implem (Chan x A B M) \<Longrightarrow> M \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto elim: validE)
  moreover from assms have "\<And> x A B M. X = implem (Chan x A B M) \<Longrightarrow> M \<in> payload \<Longrightarrow> P"
    proof -
      fix x A B M
      assume "X = implem (Chan x A B M)" "M \<in> payload"
      with assms show "P" by (cases x, auto)
    qed
  ultimately show ?thesis .
qed

end

subsection {* Second step: basic and analyze assumptions *}
(**************************************************************************************************)

text {* This locale contains most of the assumptions on implem, i.e.:
\begin{itemize}
\item @{text "impl_inj"}: injectivity
\item @{text "parts_impl_inj"}: injectivity through parts
\item @{text "Enc_parts_valid_impl"}: if Enc X Y appears in parts of an implem, then it is 
  in parts of the payload, or the key is either long term or payload
\item @{text "impl_composed"}: the implementations are composed (not nonces, agents, tags etc.)
\item @{text "analz_Un_implXXXSet"}: move the impl*Set out of the analz (only keep the payloads)
\item @{text "impl_Impl"}: implementations contain implementation material
\item @{text "LtK_parts_impl"}: no exposed long term keys in the implementations 
  (i.e., they are only used as keys, or under hashes)
\end{itemize}
*}

locale semivalid_implem = basic_implem +
-- {* injectivity *}
assumes impl_inj:
  "implem (Chan x A B M) = implem (Chan x' A' B' M') 
   \<longleftrightarrow> x = x' \<and> A = A' \<and> B = B' \<and> M = M'"
-- {* implementations and parts *}
and parts_impl_inj:
  "M' \<in> payload \<Longrightarrow>
   implem (Chan x A B M) \<in> parts {implem (Chan x' A' B' M')} \<Longrightarrow> 
   x = x' \<and> A = A' \<and> B = B' \<and> M = M'"
and Enc_keys_clean_valid: "I \<subseteq> valid \<Longrightarrow> Enc_keys_clean I"
and impl_composed: "composed (implem Z)"
and impl_Impl: "implem (Chan x A B M) \<notin> payload"
-- {* no ltk in the parts of an implementation *}
and LtK_parts_impl: "X \<in> valid \<Longrightarrow> LtK K \<notin> parts {X}"

-- {* analyze assumptions: *}
and analz_Un_implInsecSet:
  "\<lbrakk> G \<subseteq> payload; Enc_keys_clean H \<rbrakk> 
 \<Longrightarrow> analz (implInsecSet G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
and analz_Un_implConfidSet:
  "\<lbrakk> G \<subseteq> payload; Enc_keys_clean H \<rbrakk> 
 \<Longrightarrow> analz (implConfidSet Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
and analz_Un_implConfidSet_2:
  "\<lbrakk> G \<subseteq> payload; Enc_keys_clean H; Ag \<inter> broken (parts H \<inter> range LtK) = {} \<rbrakk>
 \<Longrightarrow> analz (implConfidSet Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
and analz_Un_implAuthSet:
  "\<lbrakk> G \<subseteq> payload; Enc_keys_clean H \<rbrakk>
 \<Longrightarrow> analz (implAuthSet G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
and analz_Un_implSecureSet:
  "\<lbrakk> G \<subseteq> payload; Enc_keys_clean H \<rbrakk>
 \<Longrightarrow> analz (implSecureSet Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
and analz_Un_implSecureSet_2:
  "\<lbrakk> G \<subseteq> payload; Enc_keys_clean H; Ag \<inter> broken (parts H \<inter> range LtK) = {} \<rbrakk>
 \<Longrightarrow> analz (implSecureSet Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"

begin
-- {*declare some attributes and abbreviations for the hypotheses *}
-- {*and prove some simple consequences of the hypotheses*}
declare impl_inj [simp]

lemmas parts_implE [elim] = parts_impl_inj [rotated 1]

declare impl_composed [simp, intro]

lemma composed_arg_cong: "X = Y \<Longrightarrow> composed X \<longleftrightarrow> composed Y"
by (rule arg_cong)

lemma implem_Tags_aux: "implem (Chan x A B M) \<notin> Tags" by (cases x, auto dest: composed_arg_cong)
lemma implem_Tags [simp]: "implem x \<notin> Tags" by (cases x, auto simp add: implem_Tags_aux)
lemma implem_LtK_aux: "implem (Chan x A B M) \<noteq> LtK K" by (cases x, auto dest: composed_arg_cong)
lemma implem_LtK [simp]: "implem x \<noteq> LtK K" by (cases x, auto simp add: implem_LtK_aux)
lemma implem_LtK2 [simp]: "implem x \<notin> range LtK" by (cases x, auto simp add: implem_LtK_aux)

declare impl_Impl [simp]

lemma LtK_parts_impl_insert:
  "LtK K \<in> parts (insert (implem (Chan x A B M)) S) \<Longrightarrow> M \<in> payload \<Longrightarrow> LtK K \<in> parts S"
apply (simp add: parts_insert [of _ S], clarify)
apply (auto dest: validI LtK_parts_impl)
done


declare LtK_parts_impl_insert [dest]
declare Enc_keys_clean_valid [simp, intro]

lemma valid_composed [simp,dest]: "M \<in> valid \<Longrightarrow> composed M"
by (auto elim: validE)

-- {* lemmas: valid/payload are mutually exclusive *}
lemma valid_payload [dest]: "\<lbrakk> X \<in> valid; X \<in> payload \<rbrakk> \<Longrightarrow> P"
by (auto elim!: validE)
    
-- {* valid/LtK are mutually exclusive *}
lemma valid_isLtKey [dest]: "\<lbrakk> X \<in> valid; X \<in> range LtK \<rbrakk> \<Longrightarrow> P"
by (auto)

lemma analz_valid:
  "H \<subseteq> payload \<union> valid \<union> range LtK \<union> Tags \<Longrightarrow>
   implem (Chan x A B M) \<in> analz H \<Longrightarrow>
   implem (Chan x A B M) \<in> H"
apply (drule analz_into_parts, 
       drule parts_monotone [of _ H "payload \<union> H \<inter> valid \<union> range LtK \<union> Tags"], auto)
apply (drule parts_singleton, auto elim!:validE dest: parts_impl_inj)
done

lemma parts_valid_LtKeys_disjoint:
  "I \<subseteq> valid \<Longrightarrow> parts I \<inter> range LtK = {}"
apply (safe, drule parts_singleton, clarsimp)
apply (auto dest: subsetD LtK_parts_impl)
done

lemma analz_LtKeys:
  "H \<subseteq> payload \<union> valid \<union> range LtK \<union> Tags \<Longrightarrow>
   analz H \<inter> range LtK \<subseteq> H"
apply auto
apply (drule analz_into_parts, drule parts_monotone [of _ H "payload \<union> valid \<union> H \<inter> range LtK \<union> Tags"], auto)
apply (drule parts_singleton, auto elim!:validE dest: parts_impl_inj)
done

end


subsection {* Third step: @{text "valid_implem"} *}
(**************************************************************************************************)

text {* This extends @{locale "semivalid_implem"} with four new assumptions, which under certain 
  conditions give information on $A$, $B$, $M$ when @{term "implXXX A B M \<in> synth (analz Z)"}.
  These assumptions are separated because interpretations are more easily proved, if the 
  conclusions that follow from the @{locale "semivalid_implem"} assumptions are already 
  available.
*}

locale valid_implem = semivalid_implem +

-- {* Synthesize assumptions: conditions on payloads $M$ implied by derivable *}
-- {* channel messages with payload $M$. *}
assumes implInsec_synth_analz:
  "H \<subseteq> payload \<union> valid \<union> range LtK \<union> Tags \<Longrightarrow>
   implInsec A B M \<in> synth (analz H) \<Longrightarrow>
   implInsec A B M \<in> H \<or> M \<in> synth (analz H)"
and implConfid_synth_analz:
  "H \<subseteq> payload \<union> valid \<union> range LtK \<union> Tags \<Longrightarrow>
   implConfid A B M \<in> synth (analz H) \<Longrightarrow>
   implConfid A B M \<in> H \<or> M \<in> synth (analz H)"
and implAuth_synth_analz:
  "H \<subseteq> payload \<union> valid \<union> range LtK \<union> Tags \<Longrightarrow>
   implAuth A B M \<in> synth (analz H) \<Longrightarrow>
   implAuth A B M \<in> H \<or> (M \<in> synth (analz H) \<and> (A, B) \<in> broken H)"
and implSecure_synth_analz:
  "H \<subseteq> payload \<union> valid \<union> range LtK \<union> Tags \<Longrightarrow>
   implSecure A B M \<in> synth (analz H) \<Longrightarrow>
   implSecure A B M \<in> H \<or> (M \<in> synth (analz H) \<and> (A, B) \<in> broken H)"

end
