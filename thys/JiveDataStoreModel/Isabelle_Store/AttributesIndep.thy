(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>  and  
                 Nicole Rauch <rauch at informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section {* Program-Independent Lemmas on Attributes *}

theory AttributesIndep
imports "../Isa_Counter_Store/Attributes"
begin

text {* The following lemmas validate the functions defined in the Attributes theory.
They also aid in subsequent proving tasks. Since they are
program-independent, it is of no use to add them to the generation process of
Attributes.thy. Therefore, they have been extracted to this theory.
*}

lemma cls_catt [simp]: 
  "CClassT c \<le> dtype f \<Longrightarrow> cls (catt c f) = c"
  apply (case_tac c)
  apply (case_tac [!] f)
  apply simp_all
   --{* solves all goals where @{text "CClassT c \<le> dtype f"} *}
  apply (fastforce elim: subtype_wrong_elims simp add: subtype_defs)+
   --{* solves all the rest where @{text "\<not> CClassT c \<le> dtype f"} can be derived
     *}
  done

lemma att_catt [simp]: 
  "CClassT c \<le> dtype f \<Longrightarrow> att (catt c f) = f"
  apply (case_tac c)
  apply (case_tac [!] f)
  apply simp_all
   --{* solves all goals where @{text "CClassT c \<le> dtype f"} *}
  apply (fastforce elim: subtype_wrong_elims simp add: subtype_defs)+
   --{* solves all the rest where @{text "\<not> CClassT c \<le> dtype f"} can be 
        derived *}
  done

text {* The following lemmas are just a demonstration of simplification. *}

lemma rtype_att_catt: 
  "CClassT c \<le> dtype f \<Longrightarrow> rtype (att (catt c f)) = rtype f"
  by simp

lemma widen_cls_dtype_att [simp,intro]: 
  "(CClassT (cls cf) \<le> dtype (att cf)) "
  by (cases cf, simp_all)

end
