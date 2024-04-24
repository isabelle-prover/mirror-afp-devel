section \<open>ZFC\_in\_HOL lives up to CakeML's set theory specification\<close>

theory ZFC_in_HOL_Set_Theory imports ZFC_in_HOL.ZFC_in_HOL Set_Theory begin

interpretation set_theory "\<lambda>x y. x \<in> elts y" "\<lambda>x::V. \<lambda>P. (inv elts) ({y. y \<in> elts x \<and> P y})" VPow
  "(\<lambda>Y. SOME Z. elts Z = \<Union>(elts ` (elts Y)))" "\<lambda>x y::V. (inv elts) {x, y}"
  apply unfold_locales
  subgoal for x y
    apply blast
    done
  subgoal for x P a
    by (rule iffI) (metis (no_types, lifting) down_raw f_inv_into_f mem_Collect_eq subsetI)+
  subgoal for x a
    apply blast
    done
  subgoal for x a
    apply (metis (mono_tags) UN_iff elts_Sup small_elts tfl_some)
    done
  subgoal for x y a
    apply (metis ZFC_in_HOL.set_def elts_of_set insert_iff singletonD small_upair)
    done
  done

end
