theory Sepref_Misc
imports 
  "../../Refine_Monadic/Refine_Monadic"
  PO_Normalizer
  "../../List-Index/List_Index"
  "../../Separation_Logic_Imperative_HOL/Sep_Main"
  Named_Theorems_Rev
  "~~/src/HOL/Eisbach/Eisbach"
  "../../Separation_Logic_Imperative_HOL/Examples/Array_Blit"
begin

  hide_const (open) CONSTRAINT





  (* Misc: General *)
  lemma fun_neq_ext_iff: "m\<noteq>m' \<longleftrightarrow> (\<exists>x. m x \<noteq> m' x)" by auto  

  definition [simp]: "CODE_ABORT f = f ()"
  declare [[code abort: CODE_ABORT]]

  (* TODO: Move *)  
  lemma atomize_Trueprop_eq[atomize]: "(Trueprop x \<equiv> Trueprop y) \<equiv> Trueprop (x=y)"
    apply rule
    apply (rule)
    apply (erule equal_elim_rule1)
    apply assumption
    apply (erule equal_elim_rule2)
    apply assumption
    apply simp
    done
     
  (* TODO: Move lemma to HOL! *)  
  lemma cnv_conj_to_meta: "(P \<and> Q \<Longrightarrow> PROP X) \<equiv> (\<lbrakk>P;Q\<rbrakk> \<Longrightarrow> PROP X)"
    by (rule BNF_Fixpoint_Base.conj_imp_eq_imp_imp)

  (* TODO: Move, and merge with other such tags! *)  
  definition [simp]: "CNV x y \<equiv> x=y"
  lemma CNV_I: "CNV x x" by simp
  lemma CNV_eqD: "CNV x y \<Longrightarrow> x=y" by simp
  lemma CNV_meqD: "CNV x y \<Longrightarrow> x\<equiv>y" by simp
  
  (*  TODO: Move *)
  definition [code_unfold, simp]: "swap_args2 f x y \<equiv> f y x"



  (* Misc: nat *)
  (* TODO: Move to Misc *)  
  lemma nz_le_conv_less: "0<k \<Longrightarrow> k \<le> m \<Longrightarrow> k - Suc 0 < m"
    by auto
  (* TODO: Move to Misc *)
  lemma min_Suc_gt[simp]: 
    "a<b \<Longrightarrow> min (Suc a) b = Suc a"  
    "a<b \<Longrightarrow> min b (Suc a) = Suc a"  
    by auto

  (* Misc: Ordering *)  
  lemma zero_comp_diff_simps[simp]: 
    "(0::'a::linordered_idom) \<le> a - b \<longleftrightarrow> b \<le> a" 
    "(0::'a::linordered_idom) < a - b \<longleftrightarrow> b < a" 
    by auto


  (* Misc: List/map *)
  lemma map_distinct_upd_conv: 
    "\<lbrakk>i<length l; distinct l\<rbrakk> \<Longrightarrow> map f l [i := x] = map (f(l!i := x)) l"
    -- \<open>Updating a mapped distinct list is equal to updating the 
      mapping function\<close>
    by (simp add: nth_eq_iff_index_eq nth_equalityI)  

  (* Misc: List *)  
  lemma length_Suc_rev_conv: "length xs = Suc n \<longleftrightarrow> (\<exists>ys y. xs=ys@[y] \<and> length ys = n)"
    by (cases xs rule: rev_cases) auto


  (* Additions for List_Index *)  
  lemma index_of_last_distinct[simp]: 
    "distinct l \<Longrightarrow> index l (last l) = length l - 1"  
    apply (cases l rule: rev_cases)
    apply (auto simp: index_append)
    done

  lemma index_eqlen_conv[simp]: "index l x = length l \<longleftrightarrow> x\<notin>set l"
    by (auto simp: index_size_conv)

  (* TODO: Move *)
  context begin
  private definition "SPLIT_ACCORDING m l \<equiv> length l = length m"
  
  private lemma SPLIT_ACCORDINGE: 
    assumes "length m = length l"
    obtains "SPLIT_ACCORDING m l"
    unfolding SPLIT_ACCORDING_def using assms by auto
  
  private lemma SPLIT_ACCORDING_simp:
    "SPLIT_ACCORDING m (l1@l2) \<longleftrightarrow> (\<exists>m1 m2. m=m1@m2 \<and> SPLIT_ACCORDING m1 l1 \<and> SPLIT_ACCORDING m2 l2)"
    "SPLIT_ACCORDING m (x#l') \<longleftrightarrow> (\<exists>y m'. m=y#m' \<and> SPLIT_ACCORDING m' l')"
    apply (fastforce simp: SPLIT_ACCORDING_def intro: exI[where x = "take (length l1) m"] exI[where x = "drop (length l1) m"])
    apply (cases m;auto simp: SPLIT_ACCORDING_def)
    done
  
  text \<open>Split structure of list @{term m} according to structure of list @{term l}.\<close>
  method split_list_according for m :: "'a list" and l :: "'b list" =
    (rule SPLIT_ACCORDINGE[of m l],
      (simp; fail),
      ( simp only: SPLIT_ACCORDING_simp,
        elim exE conjE, 
        simp only: SPLIT_ACCORDING_def
      )
    ) 
  end

  lemma upt_merge[simp]: "i\<le>j \<and> j\<le>k \<Longrightarrow> [i..<j]@[j..<k] = [i..<k]"
    by (metis le_Suc_ex upt_add_eq_append)
  
  lemma upt_eq_append_conv: "i\<le>j \<Longrightarrow> [i..<j] = xs@ys \<longleftrightarrow> (\<exists>k. i\<le>k \<and> k\<le>j \<and> [i..<k] = xs \<and> [k..<j] = ys)"
  proof (rule iffI)
    assume "[i..<j] = xs @ ys"  
    and "i\<le>j"
    thus "\<exists>k\<ge>i. k \<le> j \<and> [i..<k] = xs \<and> [k..<j] = ys"
      apply (induction xs arbitrary: i)
      apply (auto; fail)
      apply (clarsimp simp: upt_eq_Cons_conv)
      by (meson Suc_le_eq less_imp_le_nat)
  qed auto
  

  (* Misc: Relations *)  
  (* TODO: Move to Misc *)
  lemma single_valued_inter1: "single_valued R \<Longrightarrow> single_valued (R\<inter>S)"
    by (auto intro: single_valuedI dest: single_valuedD)
  
  lemma single_valued_inter2: "single_valued R \<Longrightarrow> single_valued (S\<inter>R)"
    by (auto intro: single_valuedI dest: single_valuedD)

  (* TODO: Move *)
  lemma single_valued_below_Id: "R\<subseteq>Id \<Longrightarrow> single_valued R"
    by (auto intro: single_valuedI)
  
  lemma below_Id_inv[simp]: "R\<inverse>\<subseteq>Id \<longleftrightarrow> R\<subseteq>Id" by (auto)


  (* TODO: Move *)
  text \<open>Lexicographic measure, assuming upper bound for second component\<close>
  lemma mlex_fst_decrI:
    fixes a a' b b' N :: nat
    assumes "a<a'"
    assumes "b<N" "b'<N"
    shows "a*N + b < a'*N + b'"
  proof -  
    have "a*N + b + 1 \<le> a*N + N" using \<open>b<N\<close> by linarith 
    also have "\<dots> \<le> a'*N" using \<open>a<a'\<close>
      by (metis Suc_leI ab_semigroup_add_class.add.commute 
        ab_semigroup_mult_class.mult.commute mult_Suc_right mult_le_mono2) 
    also have "\<dots> \<le> a'*N + b'" by auto
    finally show ?thesis by auto
  qed      
    
  lemma mlex_leI:
    fixes a a' b b' N :: nat
    assumes "a\<le>a'"
    assumes "b\<le>b'"
    shows "a*N + b \<le> a'*N + b'"
    using assms
    by (auto intro!: add_mono)
      
  lemma mlex_snd_decrI:
    fixes a a' b b' N :: nat
    assumes "a=a'"
    assumes "b<b'"
    shows "a*N + b < a'*N + b'"
    using assms
    by (auto)

  lemma mlex_bound:  
    fixes a b :: nat
    assumes "a<A"
    assumes "b<N"
    shows "a*N + b < A*N"
    using assms
    using mlex_fst_decrI by fastforce


  (* TODO: Move to Misc, close to finite_psupset, theme: termination orderings *)
  definition "less_than_bool \<equiv> {(a,b). a<(b::bool)}"
  lemma wf_less_than_bool[simp, intro!]: "wf (less_than_bool)"
    unfolding less_than_bool_def
    by (auto simp: wf_def)
  lemma less_than_bool_iff[simp]:
    "(x,y)\<in>less_than_bool \<longleftrightarrow> x=False \<and> y=True"  
    by (auto simp: less_than_bool_def)

  definition "greater_bounded N \<equiv> inv_image less_than (\<lambda>x. N-x)" 
  lemma wf_greater_bounded[simp, intro!]: "wf (greater_bounded N)" by (auto simp: greater_bounded_def)

  lemma greater_bounded_Suc_iff[simp]: "(Suc x,x)\<in>greater_bounded N \<longleftrightarrow> Suc x \<le> N"
    by (auto simp: greater_bounded_def)


  (* Misc: Set *)  
  lemma remove_subset: "x\<in>S \<Longrightarrow> S-{x} \<subset> S" by auto

  (* TODO: Move to HOL/Finite_set *)  
  lemma card_inverse[simp]: "card (R\<inverse>) = card R"
  proof -
    have "finite (R\<inverse>) \<longleftrightarrow> finite R" by auto
    have [simp]: "\<And>R. prod.swap`R = R\<inverse>" by auto
    {
      assume "\<not>finite R"
      hence ?thesis
        by auto
    } moreover {
      assume "finite R"
      with card_image_le[of R prod.swap] card_image_le[of "R\<inverse>" prod.swap]
      have ?thesis by auto
    } ultimately show ?thesis by blast
  qed  

  (* Misc: Map *)

  subsubsection \<open>Simultaneous Map Update\<close>
  definition "map_mmupd m K v k \<equiv> if k\<in>K then Some v else m k"
  lemma map_mmupd_empty[simp]: "map_mmupd m {} v = m"
    by (auto simp: map_mmupd_def)

  lemma mmupd_in_upd[simp]: "k\<in>K \<Longrightarrow> map_mmupd m K v k = Some v"
    by (auto simp: map_mmupd_def)

  lemma mmupd_notin_upd[simp]: "k\<notin>K \<Longrightarrow> map_mmupd m K v k = m k"
    by (auto simp: map_mmupd_def)

  lemma map_mmupdE:
    assumes "map_mmupd m K v k = Some x"
    obtains "k\<notin>K" "m k = Some x"
          | "k\<in>K" "x=v"
    using assms by (auto simp: map_mmupd_def split: if_split_asm)      

  lemma dom_mmupd[simp]: "dom (map_mmupd m K v) = dom m \<union> K"  
    by (auto simp: map_mmupd_def split: if_split_asm)      

  lemma le_map_mmupd_not_dom[simp, intro!]: "m \<subseteq>\<^sub>m map_mmupd m (K-dom m) v" 
    by (auto simp: map_le_def)

  lemma map_mmupd_update_less: "K\<subseteq>K' \<Longrightarrow> map_mmupd m (K - dom m) v \<subseteq>\<^sub>m map_mmupd m (K'-dom m) v"
    by (auto simp: map_le_def map_mmupd_def)

  (* Misc: Fun. Or Refine_Util *)  
  ML \<open>
    fun mk_compN1 _   0 f g = f$g
      | mk_compN1 env 1 f g = @{mk_term env: "?f o ?g"}
      | mk_compN1 env n f g = let
          val T = fastype_of1 (env, g) |> domain_type
          val g = incr_boundvars 1 g $ Bound 0
          val env = T::env
        in
          Abs ("x"^string_of_int n,T,mk_compN1 env (n-1) f g)
        end
    val mk_compN = mk_compN1 []    
  \<close>

  (***************************************)  
  (* Move to Sep_Misc, near uncurry2  *)
  lemma fold_partial_uncurry: "uncurry (\<lambda>(ps, cf). f ps cf) = uncurry2 f" by auto

  definition "uncurry0 c \<equiv> \<lambda>_::unit. c"
  definition curry0 :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a" where "curry0 f = f ()"

  lemma uncurry0_apply[simp]: "uncurry0 c x = c" by (simp add: uncurry0_def)

  lemma curry_uncurry0_id[simp]: "curry0 (uncurry0 f) = f" by (simp add: curry0_def)
  lemma uncurry_curry0_id[simp]: "uncurry0 (curry0 g) = g" by (auto simp: curry0_def)

  (* TODO: Move *)  
  lemma param_uncurry[param]: "(uncurry,uncurry) \<in> (A\<rightarrow>B\<rightarrow>C) \<rightarrow> A\<times>\<^sub>rB\<rightarrow>C"
    unfolding uncurry_def[abs_def] by parametricity
  lemma param_uncurry0[param]: "(uncurry0,uncurry0) \<in> A \<rightarrow> (unit_rel\<rightarrow>A)" by auto


  abbreviation "uncurry3 f \<equiv> uncurry (uncurry2 f)"
  abbreviation "curry3 f \<equiv> curry (curry2 f)"
  abbreviation "uncurry4 f \<equiv> uncurry (uncurry3 f)"
  abbreviation "curry4 f \<equiv> curry (curry3 f)"
  abbreviation "uncurry5 f \<equiv> uncurry (uncurry4 f)"
  abbreviation "curry5 f \<equiv> curry (curry4 f)"
  

  (* TODO: Move *)  
  lemma curry_shl: 
    "\<And>g f. (g \<equiv> curry f) \<equiv> (uncurry g \<equiv> f)"
    "\<And>g f. (g \<equiv> curry0 f) \<equiv> (uncurry0 g \<equiv> f)"
    by (atomize (full); auto)+

  lemma curry_shr: 
    "\<And>f g. (curry f \<equiv> g) \<equiv> (f \<equiv> uncurry g)"
    "\<And>f g. (curry0 f \<equiv> g) \<equiv> (f \<equiv> uncurry0 g)"
    by (atomize (full); auto)+

  lemmas uncurry_shl = curry_shr[symmetric]  
  lemmas uncurry_shr = curry_shl[symmetric]  

  lemma shift_lambda_left: "(f \<equiv> \<lambda>x. g x) \<Longrightarrow> (\<And>x. f x \<equiv> g x)" by simp


  (***************************************)
  (* Move to Refine_Util *)

  ML \<open>
    signature BASIC_REFINE_UTIL = sig
      include BASIC_REFINE_UTIL

      val split: ('a -> bool) -> 'a list -> 'a list * 'a list
      val split_matching: ('a -> 'b -> bool) -> 'a list -> 'b list -> ('b list * 'b list) option

      (* Only consider results that solve subgoal. If none, return all results unchanged. *)
      val TRY_SOLVED': tactic' -> tactic'

      (* Case distinction with tactics. Generalization of THEN_ELSE to lists. *)
      val CASES': (tactic' * tactic) list -> tactic'

      (* Tactic that depends on subgoal term structure *)
      val WITH_subgoal: (term -> tactic') -> tactic'
      (* Tactic that depends on subgoal's conclusion term structure *)
      val WITH_concl: (term -> tactic') -> tactic'

      (* Tactic version of Variable.trade. Import, apply tactic, and export results.
        One effect is that schematic variables in the goal are fixed, and thus cannot 
        be instantiated by the tactic.
      *)
      val TRADE: (Proof.context -> tactic') -> Proof.context -> tactic'
    end

    signature REFINE_UTIL = sig
      include REFINE_UTIL

      (* Miscellaneous *)
      val dest_itselfT: typ -> typ
      val dummify_tvars: term -> term

      (* a\<equiv>\<lambda>x. f x  \<mapsto>  a ?x \<equiv> f ?x *)
      val shift_lambda_left: thm -> thm
      val shift_lambda_leftN: int -> thm -> thm


      (* Parsing *)
      (* 2-step configuration parser *)
      (* Parse boolean config, name or no_name. *)
      val parse_bool_config': string -> bool Config.T -> Token.T list -> (bool Config.T * bool) * Token.T list
      (* Parse optional (p1,...,pn). Empty list if nothing parsed. *)
      val parse_paren_list': 'a parser -> Token.T list -> 'a list * Token.T list
      (* Apply list of (config,value) pairs *)
      val apply_configs: ('a Config.T * 'a) list -> Proof.context -> Proof.context


      (* Conversion combinators to choose first matching position *)
      (* Try argument, then function *)
      val fcomb_conv: conv -> conv
      (* Descend over function or abstraction *)
      val fsub_conv: (Proof.context -> conv) -> Proof.context -> conv 
      (* Apply to topmost matching position *)
      val ftop_conv: (Proof.context -> conv) -> Proof.context -> conv
    

      (* Rule combinators *)
      
      (* Iterate rule on theorem until it fails *)  
      val repeat_rule: (thm -> thm) -> thm -> thm
      (* Apply rule on theorem and assert that theorem was changed *)
      val changed_rule: (thm -> thm) -> thm -> thm
      (* Try rule on theorem, return theorem unchanged if rule fails *)
      val try_rule: (thm -> thm) -> thm -> thm
      (* Singleton version of Variable.trade *)
      val trade_rule: (Proof.context -> thm -> thm) -> Proof.context -> thm -> thm
      (* Combine with first matching theorem *)
      val RS_fst: thm -> thm list -> thm
      (* Instantiate first matching theorem *)
      val OF_fst: thm list -> thm list -> thm


      (* Left-Bracketed Structures *)

      (* Map [] to z, and [x1,...,xN] to f(...f(f(x1,x2),x3)...) *)
      val list_binop_left: 'a -> ('a * 'a -> 'a) -> 'a list -> 'a
      (* Map [] to z, [x] to i x, [x1,...,xN] to f(...f(f(x1,x2),x3)...), thread state *)
      val fold_binop_left: ('c -> 'b * 'c) -> ('a -> 'c -> 'b * 'c) -> ('b * 'b -> 'b) 
            -> 'a list -> 'c -> 'b * 'c

      (* Tuples, handling () as empty tuple *)      
      val strip_prodT_left: typ -> typ list
      val list_prodT_left: typ list -> typ
      val mk_ltuple: term list -> term
      (* Fix a tuple of new frees *)
      val fix_left_tuple_from_Ts: string -> typ list -> Proof.context -> term * Proof.context

      (* HO-Patterns with tuples *)
      (* Lambda-abstraction over list of terms, recognizing tuples *)
      val lambda_tuple: term list -> term -> term
      (* Instantiate tuple-types in specified variables *)
      val instantiate_tuples: Proof.context -> (indexname*typ) list -> thm -> thm
      (* Instantiate tuple-types in variables from given term *)
      val instantiate_tuples_from_term_tac: Proof.context -> term -> tactic
      (* Instantiate tuple types in variables of subgoal *)
      val instantiate_tuples_subgoal_tac: Proof.context -> tactic'


    end

    structure Basic_Refine_Util: BASIC_REFINE_UTIL = struct
      open Basic_Refine_Util
  
      fun split P l = (filter P l, filter_out P l)

      fun split_matching R xs ys = let
        exception EXC
    
        fun fs _ [] = raise EXC
          | fs x (y::ys) = 
              if R x y then (y,ys) 
              else let val (y',ys) = fs x ys in (y',y::ys) end
    
        fun fm [] ys = ([],ys)      
          | fm (x::xs) ys = let
              val (y,ys) = fs x ys
              val (ys1,ys2) = fm xs ys
            in
              (y::ys1,ys2)
            end
      in
        try (fm xs) ys
      end
    


      (* Filter alternatives that solve a subgoal. 
        If no alternative solves goal, return result sequence unchanged *)
      fun TRY_SOLVED' tac i st = let
        val res = tac i st
        val solved = Seq.filter (fn st' => Thm.nprems_of st' < Thm.nprems_of st) res
      in 
        case Seq.pull solved of
          SOME _ => solved
        | NONE => res  
      end
    
      local
        fun CASES_aux [] = no_tac
          | CASES_aux ((tac1, tac2)::cs) = tac1 1 THEN_ELSE (tac2, CASES_aux cs)    
      in
        (* 
          Accepts a list of pairs of (pattern_tac', worker_tac), and applies
          worker_tac to results of first successful pattern_tac'.
        *)
        val CASES' = SELECT_GOAL o CASES_aux
      end    

      (* TODO/FIXME: There seem to be no guarantees when eta-long forms are introduced by unification.
        So, we have to expect eta-long forms everywhere, which may be a problem when matching terms
        syntactically.
      *)
      fun WITH_subgoal tac = 
        CONVERSION Thm.eta_conversion THEN' 
        IF_EXGOAL (fn i => fn st => tac (nth (Thm.prems_of st) (i - 1)) i st)
  
      fun WITH_concl tac = 
        CONVERSION Thm.eta_conversion THEN' 
        IF_EXGOAL (fn i => fn st => 
          tac (Logic.concl_of_goal (Thm.prop_of st) i) i st
        )

      fun TRADE tac ctxt i st = let
        val orig_ctxt = ctxt
        val (st,ctxt) = yield_singleton (apfst snd oo Variable.import true) st ctxt
        val seq = tac ctxt i st
          |> Seq.map (singleton (Variable.export ctxt orig_ctxt))
      in
        seq
      end
    end
    open Basic_Refine_Util
    

    structure Refine_Util: REFINE_UTIL = struct
      open Refine_Util

      (* Try argument, then function *)
      fun fcomb_conv conv = let open Conv in
        arg_conv conv else_conv fun_conv conv
      end
  
      (* Descend over function or abstraction *)
      fun fsub_conv conv ctxt = let 
        open Conv 
      in
        fcomb_conv (conv ctxt) else_conv
        abs_conv (conv o snd) ctxt else_conv
        no_conv
      end
  
      (* Apply to topmost matching position *)
      fun ftop_conv conv ctxt ct = 
        (conv ctxt else_conv fsub_conv (ftop_conv conv) ctxt) ct
  
      (* Iterate rule on theorem until it fails *)  
      fun repeat_rule n thm = case try n thm of
        SOME thm => repeat_rule n thm
      | NONE => thm
  
      (* Apply rule on theorem and assert that theorem was changed *)
      fun changed_rule n thm = let
        val thm' = n thm
      in
        if Thm.eq_thm_prop (thm, thm') then raise THM ("Same",~1,[thm,thm'])
        else thm'
      end

      (* Try rule on theorem *)
      fun try_rule n thm = case try n thm of
        SOME thm => thm | NONE => thm

      fun trade_rule f ctxt thm = 
        singleton (Variable.trade (map o f) ctxt) thm

      fun RS_fst thm thms = let
        fun r [] = raise THM ("RS_fst, no matches",~1,thm::thms)
          | r (thm'::thms) = case try (op RS) (thm,thm') of
              NONE => r thms | SOME thm => thm
  
      in
        r thms
      end

      fun OF_fst thms insts = let
        fun r [] = raise THM ("OF_fst, no matches",length thms,thms@insts)
          | r (thm::thms) = case try (op OF) (thm,insts) of
              NONE => r thms | SOME thm => thm
      in
        r thms
      end

      (* Map [] to z, and [x1,...,xN] to f(...f(f(x1,x2),x3)...) *)
      fun list_binop_left z f = let
        fun r [] = z
          | r [T] = T
          | r (T::Ts) = f (r Ts,T)
      in
        fn l => r (rev l)
      end    

      (* Map [] to z, [x] to i x, [x1,...,xN] to f(...f(f(x1,x2),x3)...), thread state *)
      fun fold_binop_left z i f = let
        fun r [] ctxt = z ctxt
          | r [T] ctxt = i T ctxt
          | r (T::Ts) ctxt = let 
              val (Ti,ctxt) = i T ctxt
              val (Tsi,ctxt) = r Ts ctxt
            in
              (f (Tsi,Ti),ctxt)
            end
      in
        fn l => fn ctxt => r (rev l) ctxt
      end    

  
  
      fun strip_prodT_left (Type (@{type_name Product_Type.prod},[A,B])) = strip_prodT_left A @ [B]
        | strip_prodT_left (Type (@{type_name Product_Type.unit},[])) = []
        | strip_prodT_left T = [T]
  
      val list_prodT_left = list_binop_left HOLogic.unitT HOLogic.mk_prodT

      (* Make tuple with left-bracket structure *)
      val mk_ltuple = list_binop_left HOLogic.unit HOLogic.mk_prod


  
      (* Fix a tuple of new frees *)
      fun fix_left_tuple_from_Ts name = fold_binop_left
        (fn ctxt => (@{term "()"},ctxt))
        (fn T => fn ctxt => let 
            val (x,ctxt) = yield_singleton Variable.variant_fixes name ctxt
            val x = Free (x,T)
          in 
            (x,ctxt)
          end)
        HOLogic.mk_prod  

      (* Replace all type-vars by dummyT *)
      val dummify_tvars = map_types (map_type_tvar (K dummyT))

      fun dest_itselfT (Type (@{type_name itself},[A])) = A
        | dest_itselfT T = raise TYPE("dest_itselfT",[T],[])


      fun shift_lambda_left thm = thm RS @{thm shift_lambda_left}
      fun shift_lambda_leftN i = funpow i shift_lambda_left
  

      (* TODO: Naming should be without ' for basic parse, and with ' for context_parser! *)
      fun parse_bool_config' name cfg =
           (Args.$$$ name #>> K (cfg,true))
        || (Args.$$$ ("no_"^name) #>> K (cfg,false))  
  
      fun parse_paren_list' p = Scan.optional (Args.parens (Parse.enum1 "," p)) []
  
      fun apply_configs l ctxt = fold (fn (cfg,v) => fn ctxt => Config.put cfg v ctxt) l ctxt
      
      fun lambda_tuple [] t = t
        | lambda_tuple (@{mpat "(?a,?b)"}::l) t = let
            val body = lambda_tuple (a::b::l) t
          in
            @{mk_term "case_prod ?body"}
          end
        | lambda_tuple (x::l) t = lambda x (lambda_tuple l t)
  
      fun get_tuple_inst ctxt (iname,T) = let
        val (argTs,T) = strip_type T
  
        fun cr (Type (@{type_name prod},[T1,T2])) ctxt = let
              val (x1,ctxt) = cr T1 ctxt
              val (x2,ctxt) = cr T2 ctxt
            in
              (HOLogic.mk_prod (x1,x2), ctxt)
            end
          | cr T ctxt = let
              val (name, ctxt) = yield_singleton Variable.variant_fixes "x" ctxt
            in
              (Free (name,T),ctxt)
            end
  
        val ctxt = Variable.set_body false ctxt (* Prevent generation of skolem-names *)

        val (args,ctxt) = fold_map cr argTs ctxt
        fun fl (@{mpat "(?x,?y)"}) = fl x @ fl y
          | fl t = [t]
  
        val fargs = flat (map fl args)
        val fTs = map fastype_of fargs
  
        val v = Var (iname,fTs ---> T)
        val v = list_comb (v,fargs)
        val v = lambda_tuple args v
      in 
        Thm.cterm_of ctxt v
      end
  
      fun instantiate_tuples ctxt inTs = let
        val inst = inTs ~~ map (get_tuple_inst ctxt) inTs
      in
        Thm.instantiate ([],inst)
      end
  
      val _ = COND'
  
      fun instantiate_tuples_from_term_tac ctxt t st = let
        val vars = Term.add_vars t []
      in
        PRIMITIVE (instantiate_tuples ctxt vars) st
      end
  
      fun instantiate_tuples_subgoal_tac ctxt = WITH_subgoal (fn t => K (instantiate_tuples_from_term_tac ctxt t))


    end    
  \<close>

  (***************************************)
  (* Additions to Autoref *)
    

definition "rel2p R x y \<equiv> (x,y)\<in>R"
definition "p2rel P \<equiv> {(x,y). P x y}"

lemma rel2pD: "\<lbrakk>rel2p R a b\<rbrakk> \<Longrightarrow> (a,b)\<in>R" by (auto simp: rel2p_def)
lemma p2relD: "\<lbrakk>(a,b) \<in> p2rel R\<rbrakk> \<Longrightarrow> R a b" by (auto simp: p2rel_def)

lemma rel2p_inv[simp]:
  "rel2p (p2rel P) = P"
  "p2rel (rel2p R) = R"
  by (auto simp: rel2p_def[abs_def] p2rel_def)

named_theorems rel2p
named_theorems p2rel

lemma rel2p_dflt[rel2p]:
  "rel2p Id = op ="
  "rel2p (A\<rightarrow>B) = rel_fun (rel2p A) (rel2p B)"
  "rel2p (A\<times>\<^sub>rB) = rel_prod (rel2p A) (rel2p B)"
  "rel2p (\<langle>A,B\<rangle>sum_rel) = rel_sum (rel2p A) (rel2p B)"
  "rel2p (\<langle>A\<rangle>option_rel) = rel_option (rel2p A)"
  "rel2p (\<langle>A\<rangle>list_rel) = list_all2 (rel2p A)"
  by (auto 
    simp: rel2p_def[abs_def] 
    intro!: ext
    simp: fun_rel_def rel_fun_def 
    simp: sum_rel_def elim: rel_sum.cases
    simp: option_rel_def elim: option.rel_cases
    simp: list_rel_def
    simp: set_rel_def rel_set_def Image_def
    )

 
  
lemma p2rel_dflt[p2rel]: 
  "p2rel op= = Id"
  "p2rel (rel_fun A B) = p2rel A \<rightarrow> p2rel B"
  "p2rel (rel_prod A B) = p2rel A \<times>\<^sub>r p2rel B"
  "p2rel (rel_sum A B) = \<langle>p2rel A, p2rel B\<rangle>sum_rel"
  "p2rel (rel_option A) = \<langle>p2rel A\<rangle>option_rel"
  "p2rel (list_all2 A) = \<langle>p2rel A\<rangle>list_rel"
  by (auto 
    simp: p2rel_def[abs_def] 
    simp: fun_rel_def rel_fun_def 
    simp: sum_rel_def elim: rel_sum.cases
    simp: option_rel_def elim: option.rel_cases
    simp: list_rel_def
    )

(* TODO: Discrepancy between rel_set and set_rel! *)
lemma [rel2p]: "single_valued A \<Longrightarrow> rel2p (\<langle>A\<rangle>set_rel) = rel_set (rel2p A)"
  unfolding set_rel_def rel_set_def rel2p_def[abs_def]
  by (auto intro!: ext; blast dest: single_valuedD)
    
lemma [p2rel]: "left_unique A \<Longrightarrow> p2rel (rel_set A) = (\<langle>p2rel A\<rangle>set_rel)"
  unfolding set_rel_def rel_set_def p2rel_def[abs_def]
  apply (auto intro!: ext)
  oops (* TODO! *)

lemma rel2p_comp: "rel2p A OO rel2p B = rel2p (A O B)"  
  by (auto simp: rel2p_def[abs_def] intro!: ext)

lemma rel2p_inj[simp]: "rel2p A = rel2p B \<longleftrightarrow> A=B"  
  by (auto simp: rel2p_def[abs_def]; meson)

lemma rel2p_nres_RETURN[rel2p]: "rel2p (\<langle>A\<rangle>nres_rel) (RETURN x) (RETURN y) = rel2p A x y"   
  by (auto simp: rel2p_def dest: nres_relD intro: nres_relI)

  (* TODO: Move, do compp-lemmas for other standard relations *)
  lemma list_rel_compp: "\<langle>A O B\<rangle>list_rel = \<langle>A\<rangle>list_rel O \<langle>B\<rangle>list_rel"
    using list.rel_compp[of "rel2p A" "rel2p B"]
    by (auto simp: rel2p(2-)[symmetric] rel2p_comp) (* TODO: Not very systematic proof *)



  lemma in_br_conv: "(c,a)\<in>br \<alpha> I \<longleftrightarrow> a=\<alpha> c \<and> I c"  
    by (auto simp: br_def)

  (* TODO: Move *)
  lemma fold_is_None: "x=None \<longleftrightarrow> is_None x" by (cases x) auto
  (* TODO: Move *)
  declare autoref_is_None[param]


  (* TODO: Move *)
  lemma option_rel_inter[simp]: "\<langle>R1 \<inter> R2\<rangle>option_rel = \<langle>R1\<rangle>option_rel \<inter> \<langle>R2\<rangle>option_rel"
    by (auto simp: option_rel_def)
  
  lemma option_rel_constraint[simp]: 
    "(x,x)\<in>\<langle>UNIV\<times>C\<rangle>option_rel \<longleftrightarrow> (\<forall>v. x=Some v \<longrightarrow> v\<in>C)"
    by (auto simp: option_rel_def)

  lemma (in -) param_map_option[param]: "(map_option, map_option) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>B\<rangle>option_rel"
    apply (intro fun_relI)
    apply (auto elim!: option_relE dest: fun_relD)
    done
  

  lemma param_member[param]:
    "single_valued (K\<inverse>) \<Longrightarrow> (op \<in>, op \<in>) \<in> K \<rightarrow> \<langle>K\<rangle>set_rel \<rightarrow> bool_rel"  
    by (auto simp: set_rel_def dest: single_valuedD)

  lemma param_list_all[param]: "(list_all,list_all) \<in> (A\<rightarrow>bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
    by (fold rel2p_def) (simp add: rel2p List.list_all_transfer)

  context begin
  private primrec list_all2_alt :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool" where
    "list_all2_alt P [] ys \<longleftrightarrow> (case ys of [] \<Rightarrow> True | _ \<Rightarrow> False)"
  | "list_all2_alt P (x#xs) ys \<longleftrightarrow> (case ys of [] \<Rightarrow> False | y#ys \<Rightarrow> P x y \<and> list_all2_alt P xs ys)"
  
  private lemma list_all2_alt: "list_all2 P xs ys = list_all2_alt P xs ys"
    by (induction xs arbitrary: ys) (auto split: list.splits)
  
  lemma param_list_all2[param]: "(list_all2, list_all2) \<in> (A\<rightarrow>B\<rightarrow>bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>B\<rangle>list_rel \<rightarrow> bool_rel"
    unfolding list_all2_alt[abs_def] 
    unfolding list_all2_alt_def[abs_def] 
    by parametricity
  
  end
  


  (* TODO: Move *)
  lemma param_hd[param]: "l\<noteq>[] \<Longrightarrow> (l',l)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> (hd l', hd l)\<in>A"
    unfolding hd_def by (auto split: list.splits)
  
  lemma param_last[param]: 
    assumes "y \<noteq> []" 
    assumes "(x, y) \<in> \<langle>A\<rangle>list_rel"  
    shows "(last x, last y) \<in> A"
    using assms(2,1)
    by (induction rule: list_rel_induct) auto
  
  lemma param_rotate1[param]: "(rotate1, rotate1) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"
    unfolding rotate1_def by parametricity
  
  lemma param_prod_swap[param]: "(prod.swap, prod.swap)\<in>A\<times>\<^sub>rB \<rightarrow> B\<times>\<^sub>rA" by auto

  (* TODO: Move to Relators *)  
  lemma in_Domain_prod_rel_iff[iff]: "(a,b)\<in>Domain (A\<times>\<^sub>rB) \<longleftrightarrow> a\<in>Domain A \<and> b\<in>Domain B"
    by (auto simp: prod_rel_def)

  (* TODO: Move to Relators *)  
  lemma prod_rel_comp: "(A \<times>\<^sub>r B) O (C \<times>\<^sub>r D) = (A O C) \<times>\<^sub>r (B O D)"
    unfolding prod_rel_def
    by auto

  (* TODO: Move *)
  lemma set_rel_empty_iff[simp]: 
    "({},y)\<in>\<langle>A\<rangle>set_rel \<longleftrightarrow> y={}" 
    "(x,{})\<in>\<langle>A\<rangle>set_rel \<longleftrightarrow> x={}" 
    by (auto simp: set_rel_def; fastforce)+

  (* TODO: Move*)
  lemma param_Collect[param]: "Range A = UNIV \<Longrightarrow> Domain A = UNIV \<Longrightarrow> (Collect,Collect)\<in>(A\<rightarrow>bool_rel) \<rightarrow> \<langle>A\<rangle>set_rel"
    unfolding set_rel_def
    by (force dest: fun_relD)

  lemma param_and_cong1: "\<lbrakk> (a,a')\<in>bool_rel; \<lbrakk>a; a'\<rbrakk> \<Longrightarrow> (b,b')\<in>bool_rel \<rbrakk> \<Longrightarrow> (a\<and>b,a'\<and>b')\<in>bool_rel"
    by blast
  lemma param_and_cong2: "\<lbrakk> (a,a')\<in>bool_rel; \<lbrakk>a; a'\<rbrakk> \<Longrightarrow> (b,b')\<in>bool_rel \<rbrakk> \<Longrightarrow> (b\<and>a,b'\<and>a')\<in>bool_rel"
    by blast

  (* TODO: Move *)
  lemma list_rel_split_right_iff: 
    "(x#xs,l)\<in>\<langle>R\<rangle>list_rel \<longleftrightarrow> (\<exists>y ys. l=y#ys \<and> (x,y)\<in>R \<and> (xs,ys)\<in>\<langle>R\<rangle>list_rel)"
    by (cases l) auto
  lemma list_rel_split_left_iff: 
    "(l,y#ys)\<in>\<langle>R\<rangle>list_rel \<longleftrightarrow> (\<exists>x xs. l=x#xs \<and> (x,y)\<in>R \<and> (xs,ys)\<in>\<langle>R\<rangle>list_rel)"
    by (cases l) auto
  

  ML \<open> (* TODO: Add to Relators*)
    signature RELATORS = sig
      include RELATORS

      val list_rel: term list -> term -> term

      val rel_absT: term -> typ
      val rel_concT: term -> typ

      val mk_prodrel: term * term -> term
      val is_prodrel: term -> bool
      val dest_prodrel: term -> term * term

      val strip_prodrel_left: term -> term list
      val list_prodrel_left: term list -> term
    end

    structure Relators : RELATORS = struct
      open Relators

  
      val rel_absT = fastype_of #> HOLogic.dest_setT #> HOLogic.dest_prodT #> snd
      val rel_concT = fastype_of #> HOLogic.dest_setT #> HOLogic.dest_prodT #> fst
      
      val list_rel = fold_rev mk_fun_rel

      fun mk_prodrel (A,B) = @{mk_term "?A \<times>\<^sub>r ?B"}
      fun is_prodrel @{mpat "_ \<times>\<^sub>r _"} = true | is_prodrel _ = false
      fun dest_prodrel @{mpat "?A \<times>\<^sub>r ?B"} = (A,B) | dest_prodrel t = raise TERM("dest_prodrel",[t])
  
      fun strip_prodrel_left @{mpat "?A \<times>\<^sub>r ?B"} = strip_prodrel_left A @ [B]
        | strip_prodrel_left @{mpat "unit_rel"} = []
        | strip_prodrel_left R = [R]
  
      val list_prodrel_left = Refine_Util.list_binop_left @{term unit_rel} mk_prodrel


    end


    \<close>




    ML \<open> (* TODO: Change in Refine_Automation! 
        The change is: Let extract_concrete_fun return definition and refinement theorem.
      *)
      structure Refine_Automation = struct
        open Refine_Automation

(* Recognize pattern of conclusion and extract term to make definition of *)
fun extract_concrete_fun _ [] concl = 
  raise TERM ("Conclusion does not match any extraction pattern",[concl])
  | extract_concrete_fun thy (pat::pats) concl = (
      case Refine_Util.fo_matchp thy pat concl of
        NONE => extract_concrete_fun thy pats concl
        | SOME [t] => t
        | SOME (t::_) => (
          warning ("concrete_definition: Pattern has multiple holes, taking "
            ^ "first one: " ^ @{make_string} pat
          ); t)
        | _ => (warning ("concrete_definition: Ignoring invalid pattern " 
             ^ @{make_string} pat);
             extract_concrete_fun thy pats concl)
    )
fun mk_qualified basename q = Binding.qualify true basename (Binding.name q);


      (* Define concrete function from refinement lemma *)
      fun define_concrete_fun gen_code fun_name attribs_raw param_names thm pats
        (orig_lthy:local_theory) = 
      let
        val lthy = orig_lthy;
        val ((inst,thm'),lthy) = yield_singleton2 (Variable.import true) thm lthy;
      
        val concl = thm' |> Thm.concl_of
      
        (*val ((typ_subst,term_subst),lthy) 
          = Variable.import_inst true [concl] lthy;
        val concl = Term_Subst.instantiate (typ_subst,term_subst) concl;
        *)
      
        val term_subst = #2 inst |> map (apsnd Thm.term_of) 
      
        val param_terms = map (fn name =>
          case AList.lookup (fn (n,v) => n = #1 v) term_subst name of
            NONE => raise TERM ("No such variable: "
                                 ^Term.string_of_vname name,[concl])
          | SOME t => t
        ) param_names;
      
        val f_term = extract_concrete_fun (Proof_Context.theory_of lthy) pats concl;
      
        val lhs_type = map Term.fastype_of param_terms ---> Term.fastype_of f_term;
        val lhs_term 
          = list_comb ((Free (Binding.name_of fun_name,lhs_type)),param_terms);
        val def_term = Logic.mk_equals (lhs_term,f_term) 
          |> fold Logic.all param_terms;
      
        val attribs = map (Attrib.check_src lthy) attribs_raw;
      
        val ((_,(_,def_thm)),lthy) = Specification.definition 
          (SOME (fun_name,NONE,Mixfix.NoSyn)) [] [] ((Binding.empty,attribs),def_term) lthy;
      
        val folded_thm = Local_Defs.fold lthy [def_thm] thm';
      
        val (_,lthy) 
          = Local_Theory.note 
             ((mk_qualified (Binding.name_of fun_name) "refine",[]),[folded_thm]) 
             lthy;
      
        val lthy = case gen_code of
          NONE => lthy
        | SOME modes => 
            extract_recursion_eqs modes (Binding.name_of fun_name) def_thm lthy
      
      in
        ((def_thm,folded_thm),lthy)
      end;


      end
    \<close>  

  (***************************************)
  (* Additions to Refine_Monadic *)
  (* TODO: Move to Refine_Basic *)  
  lemma nres_rel_comp: "\<langle>A\<rangle>nres_rel O \<langle>B\<rangle>nres_rel = \<langle>A O B\<rangle>nres_rel"
    by (auto simp: nres_rel_def conc_fun_chain[symmetric] conc_trans)

  (* TODO: Move to Refine_Basic:Convenience lemmas *)  
  lemma (in -) ret_le_down_conv: 
    "nofail m \<Longrightarrow> RETURN c \<le> \<Down>R m \<longleftrightarrow> (\<exists>a. (c,a)\<in>R \<and> RETURN a \<le> m)"
    by (auto simp: pw_le_iff refine_pw_simps)
    
  (* TODO: Move to Refine_Basic *)  
  lemma param_ASSERT_bind[param]: "\<lbrakk> (\<Phi>,\<Psi>) \<in> bool_rel; \<lbrakk> \<Phi>; \<Psi> \<rbrakk> \<Longrightarrow> (f,g)\<in>\<langle>R\<rangle>nres_rel
    \<rbrakk> \<Longrightarrow> (ASSERT \<Phi> \<then> f, ASSERT \<Psi> \<then> g) \<in> \<langle>R\<rangle>nres_rel"
    by (auto intro: nres_relI)

  (* TODO: Move to Refine_Basic, convenience lemmas. Add to simpset?*)  
  lemma ASSERT_same_eq_conv: "(ASSERT \<Phi> \<then> m) = (ASSERT \<Phi> \<then> n) \<longleftrightarrow> (\<Phi> \<longrightarrow> m=n)"  
    by auto


  lemma case_prod_bind_simp[simp]: "
    (\<lambda>x. (case x of (a, b) \<Rightarrow> f a b) \<le> SPEC \<Phi>) = (\<lambda>(a,b). f a b \<le> SPEC \<Phi>)"
    by auto



  (* TODO: Move. More complete than leofD *)
  lemma (in -) le_by_leofI: "\<lbrakk> nofail m' \<Longrightarrow> nofail m; m\<le>\<^sub>nm' \<rbrakk> \<Longrightarrow> m \<le> m'"
    by (auto simp: pw_le_iff pw_leof_iff)

  (* TODO: Move *)  
  lemma (in -) leof_FAIL[simp]: "m \<le>\<^sub>n FAIL" by (auto simp: pw_leof_iff)

  lemma (in -) leof_fun_conv_le: 
    "(f x \<le>\<^sub>n M x) \<longleftrightarrow> (f x \<le> (if nofail (f x) then M x else FAIL))"
    by (auto simp: pw_le_iff pw_leof_iff)
    
  (* TODO: Move *)  
  lemma (in -) leof_add_nofailI: "\<lbrakk> nofail m \<Longrightarrow> m\<le>\<^sub>nm' \<rbrakk> \<Longrightarrow> m\<le>\<^sub>nm'"
    by (auto simp: pw_le_iff pw_leof_iff)
    

  lemma (in -) nofail_antimono_fun: "f \<le> g \<Longrightarrow> (nofail (g x) \<longrightarrow> nofail (f x))"
    by (auto simp: pw_le_iff pw_leof_iff dest: le_funD)

  (* TODO: Move near ASSERT_leof_rule *)  
  lemma (in -) leof_ASSERT_rule[refine_vcg]: "\<lbrakk>\<Phi> \<Longrightarrow> m \<le>\<^sub>n m'\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n ASSERT \<Phi> \<then> m'"  
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma (in -) leof_ASSERT_refine_rule[refine]: "\<lbrakk>\<Phi> \<Longrightarrow> m \<le>\<^sub>n \<Down>R m'\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n \<Down>R (ASSERT \<Phi> \<then> m')"  
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma pw_nres_rel_iff: "(a,b)\<in>\<langle>A\<rangle>nres_rel \<longleftrightarrow> nofail (\<Down> A b) \<longrightarrow> nofail a \<and> (\<forall>x. inres a x \<longrightarrow> inres (\<Down> A b) x)"
    by (simp add: pw_le_iff nres_rel_def)

  (* TODO: Move near RETURN_as_SPEC_refine *)  
  lemma RETURN_as_SPEC_refine_leof[refine2]:
    assumes "M \<le>\<^sub>n SPEC (\<lambda>c. (c,a)\<in>R)"
    shows "M \<le>\<^sub>n \<Down>R (RETURN a)"
    using assms
    by (simp add: pw_leof_iff refine_pw_simps)


  -- \<open>Order matters! \<close>
  lemmas [refine_vcg] = ASSERT_leI 
  lemmas [refine_vcg] = le_ASSUMEI 
  lemmas [refine_vcg] = le_ASSERTI 
  lemmas [refine_vcg] = ASSUME_leI


  (* TODO: Move to RefineG_Recursion (at least the removal of trimono-assumption) *)
  lemma RECT_eq_REC': "nofail (RECT B x) \<Longrightarrow> RECT B x = REC B x"
    apply (cases "trimono B")
    apply (subst RECT_eq_REC; simp_all add: nofail_def)
    unfolding RECT_def REC_def by simp

  (* TODO: Replace *)    
  thm REC_rule
  lemma REC_rule:
    fixes x::"'x"
    assumes M: "trimono body"
    assumes I0: "pre x"
    assumes IS: "\<And>f x. \<lbrakk> \<And>x. pre x \<Longrightarrow> f x \<le> M x; pre x; f \<le> REC body \<rbrakk> 
      \<Longrightarrow> body f x \<le> M x"
    shows "REC body x \<le> M x"
    by (rule REC_rule_arb[where pre="\<lambda>_. pre" and M="\<lambda>_. M", OF assms])


  (* TODO: Move to Refine_Basic convenience, near build_rel_SPEC *)  
  lemma build_rel_SPEC_conv: "\<Down>(br \<alpha> I) (SPEC \<Phi>) = SPEC (\<lambda>x. I x \<and> \<Phi> (\<alpha> x))"  
    by (auto simp: br_def pw_eq_iff refine_pw_simps)

  lemma build_rel_SPEC_leof: 
    assumes "m \<le>\<^sub>n SPEC (\<lambda>x. I x \<and> \<Phi> (\<alpha> x))"  
    shows "m \<le>\<^sub>n \<Down>(br \<alpha> I) (SPEC \<Phi>)"
    using assms by (auto simp: build_rel_SPEC_conv)
  
  (* TODO: Move to convenince lemmas ? *)
  lemma return_refine_prop_return:
    assumes "nofail m"
    assumes "RETURN x \<le> \<Down>R m"
    obtains x' where "(x,x')\<in>R" "RETURN x' \<le> m"
    using assms
    by (auto simp: refine_pw_simps pw_le_iff)

  (* TODO: Move to Refine_Basic:Convenience *)  
  lemma ignore_snd_refine_conv: 
    "(m \<le> \<Down>(R\<times>\<^sub>rUNIV) m') \<longleftrightarrow> m\<bind>(RETURN o fst) \<le>\<Down>R (m'\<bind>(RETURN o fst))"
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move to Refine_Basic:Convenience *)  
  lemma If_bind_distrib[simp]:
    fixes t e :: "'a nres"
    shows "(If b t e \<bind> (\<lambda>x. f x)) = (If b (t\<bind>(\<lambda>x. f x)) (e\<bind>(\<lambda>x. f x)))"  
    by simp

  (* TODO: Move to Refine_Basic: pw-reasoning *)  
  abbreviation "no_succ m \<equiv> (\<exists>x. inres m x)"

  (* TODO: Move to Refine_Basic: Convenience. 
    Can we make this a simproc, using NO_MATCH? *)  
  lemma unused_bind_conv: 
    assumes "NO_MATCH (ASSERT \<Phi>) m"
    assumes "NO_MATCH (ASSUME \<Phi>) m"
    shows "(m\<bind>(\<lambda>x. c))  = (ASSERT (nofail m) \<bind> (\<lambda>_. ASSUME (no_succ m) \<bind> (\<lambda>x. c)))" 
    by (auto simp: pw_eq_iff refine_pw_simps)


  (* TODO: Move *)  
  lemma FAIL_leof[simp, intro!]: "FAIL \<le>\<^sub>n m"  
    by (auto simp: le_or_fail_def)


lemma RECT_rule_leof:
  (*assumes M: "trimono body"*)
  assumes WF: "wf (V::('x\<times>'x) set)"
  assumes I0: "pre (x::'x)"
  assumes IS: "\<And>f x. \<lbrakk> \<And>x'. \<lbrakk>pre x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le>\<^sub>n M x'; pre x; 
                        RECT body = f
    \<rbrakk> \<Longrightarrow> body f x \<le>\<^sub>n M x"
  shows "RECT body x \<le>\<^sub>n M x"
    apply (cases "\<not>trimono body")
    apply (simp add: RECT_def)
    using assms
    unfolding leof_fun_conv_le
    apply -
    apply (rule RECT_rule[where pre=pre and V=V])
    apply simp_all
    apply auto
    using gen_code_thm_RECT by fastforce

  (* TODO: REC_rule_leof! (However, this may require some fix 
       to the domain theory model of Refine_Monadic!) *)


  (* TODO: Move/Remove? *)
  lemma RELATES_nres_rel[refine_dref_RELATES]: "RELATES R \<Longrightarrow> RELATES (\<langle>R\<rangle>nres_rel)"
    by (simp add: RELATES_def)



  (* TODO: Move to Refine_Basic: Convenience. *)
  lemma bind_sim_select_rule:
    assumes "m\<bind>f' \<le> SPEC \<Psi>"
    assumes "\<And>x. \<lbrakk>nofail m; inres m x; f' x\<le>SPEC \<Psi>\<rbrakk> \<Longrightarrow> f x\<le>SPEC \<Phi>"
    shows "m\<bind>f \<le> SPEC \<Phi>"
    -- \<open>Simultaneously select a result from assumption and verification goal.
      Useful to work with assumptions that restrict the current program to 
      be verified.\<close>
    using assms 
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move to Refine_Basic: Convenience. *)
  lemma assert_bind_spec_conv: "ASSERT \<Phi> \<then> m \<le> SPEC \<Psi> \<longleftrightarrow> (\<Phi> \<and> m \<le> SPEC \<Psi>)"  
    -- \<open>Simplify a bind-assert verification condition. 
      Useful if this occurs in the assumptions, and considerably faster than 
      using pointwise reasoning, which may causes a blowup for many chained 
      assertions.\<close>
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move to Refine_Basic: Convenience. *)
  lemma summarize_ASSERT_conv: "do {ASSERT \<Phi>; ASSERT \<Psi>; m} = do {ASSERT (\<Phi> \<and> \<Psi>); m}"
    by (auto simp: pw_eq_iff refine_pw_simps)
  
  (* TODO: Move: Refine_Basic: Convenience Lemmas *)
  lemma bind_ASSERT_eq_if: "do { ASSERT \<Phi>; m } = (if \<Phi> then m else FAIL)"
    by auto
  

lemmas [refine] = nres_relI fun_relI (* TODO: Test this as default setup! *)

  (***************************************)
  (* Additions to Separation_Logic_Imperative_HOL *)

(* TODO: Move to Imperative/HOL. It's missing there! *)
lemma run_make[run_elims]:
  assumes "run (Array.make n f) \<sigma> \<sigma>' r"
          "\<not>is_exn \<sigma>"
  obtains "\<sigma>' = Some (snd (Array.alloc (map f [0 ..< n]) (the_state \<sigma>)))"
          "r = fst (Array.alloc (map f [0 ..< n]) (the_state \<sigma>))"
          "Array.get (the_state \<sigma>') r = (map f [0 ..< n])"
  using assms
  apply (cases \<sigma>)
  apply simp
  apply (auto simp add: run.simps)
  apply (simp add: execute_simps)
  apply (simp add: Array.get_alloc)
  apply hypsubst_thin
proof -
  case goal1
  from goal1(2) have "h' = snd (Array.alloc (map f [0 ..< n]) a)" 
    "r = fst (Array.alloc (map f [0 ..< n]) a)" by (auto simp add: execute_simps)
  from goal1(1)[OF this] show ?case .
qed

(* TODO: Move *)
lemma make_rule: "<emp> Array.make n f <\<lambda>r. r \<mapsto>\<^sub>a (map f [0 ..< n])>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done

lemmas [sep_heap_rules] = make_rule

(* Move to Array_Blit. Are there system-calls for array-copy? *)
definition "array_copy a \<equiv> do {
  l\<leftarrow>Array.len a;
  if l=0 then 
    Array.of_list []
  else do {
    s \<leftarrow> Array.nth a 0;
    a'\<leftarrow>Array.new l s;
    blit a 0 a' 0 l;
    return a'
  }
}"

lemma array_copy_rule[sep_heap_rules]:
  "
    < a\<mapsto>\<^sub>al> 
      array_copy a 
    <\<lambda>a'. a\<mapsto>\<^sub>al * a'\<mapsto>\<^sub>a l>"
  unfolding array_copy_def
  by sep_auto


lemma mod_starD: "h\<Turnstile>A*B \<Longrightarrow> \<exists>h1 h2. h1\<Turnstile>A \<and> h2\<Turnstile>B"
  by (auto simp: mod_star_conv)

(* TODO: Move *)  
lemma star_or_dist1: 
  "(A \<or>\<^sub>A B)*C = (A*C \<or>\<^sub>A B*C)"  
  apply (rule ent_iffI) 
  unfolding entails_def
  by (auto simp add: mod_star_conv) 
  
lemma star_or_dist2: 
  "C*(A \<or>\<^sub>A B) = (C*A \<or>\<^sub>A C*B)"  
  apply (rule ent_iffI) 
  unfolding entails_def
  by (auto simp add: mod_star_conv) 

lemmas star_or_dist = star_or_dist1 star_or_dist2  

lemma ent_disjI1': "A\<Longrightarrow>\<^sub>AB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)

lemma ent_disjI2': "A\<Longrightarrow>\<^sub>AC \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)

lemma ent_star_mono_true: 
  assumes "A \<Longrightarrow>\<^sub>A A' * true"
  assumes "B \<Longrightarrow>\<^sub>A B' * true"
  shows "A*B*true \<Longrightarrow>\<^sub>A A'*B'*true"
  using ent_star_mono[OF assms] apply simp
  using ent_true_drop(1) by blast

lemma ent_refl_true: "A \<Longrightarrow>\<^sub>A A * true"
  by (simp add: ent_true_drop(2)) 

(* TODO: Move, this is a quite general concept *)
text \<open>Weakening of entails to allow arbitrary unspecified memory in conclusion\<close>
definition entailst :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>t" 10)
  where "entailst A B \<equiv> A \<Longrightarrow>\<^sub>A B * true"

lemma enttI: "A\<Longrightarrow>\<^sub>AB*true \<Longrightarrow> A\<Longrightarrow>\<^sub>tB" unfolding entailst_def .
lemma enttD: "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB*true" unfolding entailst_def .

(* TODO: Can we change the patterns of assn_simproc to add this pattern? *)
simproc_setup assn_simproc_entt ("\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>'")
  = {*K Seplogic_Auto.assn_simproc_fun*}


lemma entt_trans:
  "entailst A B \<Longrightarrow> entailst B C \<Longrightarrow> entailst A C"
  unfolding entailst_def
  apply (erule ent_trans)
  apply (erule ent_frame_fwd)
  apply (rule ent_refl)
  apply solve_entails
  done

lemma entt_refl[simp, intro!]: "entailst A A"
  unfolding entailst_def by sep_auto

lemma entt_true[simp, intro!]:
  "entailst A true"
  unfolding entailst_def by sep_auto

lemma entt_emp[simp, intro!]:
  "entailst A emp"
  unfolding entailst_def by sep_auto

lemma entt_star_true_simp[simp]:
  "entailst A (B*true) \<longleftrightarrow> entailst A B"
  "entailst (A*true) B \<longleftrightarrow> entailst A B"
  unfolding entailst_def 
    apply -
    apply sep_auto
    subgoal 
      apply (rule iffI)
      subgoal using ent_refl_true ent_trans by blast
      subgoal by (erule ent_frame_fwd, frame_inference) solve_entails
    done  
  done

lemma entt_star_mono: "\<lbrakk>entailst A B; entailst C D\<rbrakk> \<Longrightarrow> entailst (A*C) (B*D)"
  unfolding entailst_def
  apply (erule ent_frame_fwd, frame_inference)
  apply (erule ent_frame_fwd, frame_inference)
  by solve_entails

lemma entt_frame_fwd:
  assumes "entailst P Q"
  assumes "entailst A (P*F)"
  assumes "entailst (Q*F) B"
  shows "entailst A B"
  using assms
  by (metis entt_refl entt_star_mono entt_trans)

lemma enttI_true: "P*true \<Longrightarrow>\<^sub>A Q*true \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ"
  by (drule enttI) simp

lemma entt_def_true: "(P\<Longrightarrow>\<^sub>tQ) \<equiv> (P*true \<Longrightarrow>\<^sub>A Q*true)"
  unfolding entailst_def
  apply (rule eq_reflection)
  subgoal 
    apply (rule iffI)
    subgoal by (erule ent_frame_fwd, frame_inference) solve_entails
    subgoal using ent_refl_true ent_trans by blast
  done  
  done

lemma ent_imp_entt: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ" 
  apply (rule enttI)
  apply (erule ent_trans)
  by sep_auto

lemma cons_rulet: "\<lbrakk>P\<Longrightarrow>\<^sub>tP'; \<And>x. Q x \<Longrightarrow>\<^sub>t Q' x; <P'> c <Q>\<^sub>t \<rbrakk> \<Longrightarrow> <P> c <Q'>\<^sub>t"
  unfolding entailst_def
  apply (rule cons_pre_rule)
  apply assumption
  apply (rule cons_post_rule)
  apply (erule frame_rule)
  apply simp
  subgoal for x
    apply (rule ent_frame_fwd[of "Q x"])
    apply assumption
    apply (rule ent_refl)
    apply solve_entails
  done  
  done

lemmas cons_pre_rulet = cons_rulet[OF _ entt_refl]
lemmas cons_post_rulet = cons_rulet[OF entt_refl, rotated]

lemma entt_fr_refl: "F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*A \<Longrightarrow>\<^sub>t F'*A" by (rule entt_star_mono) auto
lemma entt_fr_drop: "F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*A \<Longrightarrow>\<^sub>t F'"
  using ent_true_drop(1) enttD enttI by blast 


(* TODO: Naming scheme of these thms is chaotic *)

lemma ent_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entails_def)

lemma ent_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entails_def)

lemma entt_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI1_direct])

lemma entt_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI2_direct])

lemma entt_disjI1': "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC"
  by (auto simp: entailst_def entails_def star_or_dist)

lemma entt_disjI2': "A\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC"
  by (auto simp: entailst_def entails_def star_or_dist)

lemma entt_disjE: "\<lbrakk> A\<Longrightarrow>\<^sub>tM; B\<Longrightarrow>\<^sub>tM \<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>t M"
  using ent_disjE enttD enttI by blast  
    
lemma entt_disjD1: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tC"
  using entt_disjI1_direct entt_trans by blast

lemma entt_disjD2: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> B\<Longrightarrow>\<^sub>tC"
  using entt_disjI2_direct entt_trans by blast



definition "is_pure_assn a \<equiv> \<exists>P. a=\<up>P"
lemma is_pure_assnE: assumes "is_pure_assn a" obtains P where "a=\<up>P"
  using assms
  by (auto simp: is_pure_assn_def)

lemma is_pure_assn_pure[simp, intro!]: "is_pure_assn (\<up>P)" by (simp add: is_pure_assn_def)

lemma is_pure_assn_basic_simps[simp]:
  "is_pure_assn false"
  "is_pure_assn emp"
proof -
  have "is_pure_assn (\<up>False)" by rule thus "is_pure_assn false" by simp
  have "is_pure_assn (\<up>True)" by rule thus "is_pure_assn emp" by simp
qed  

lemma is_pure_assn_starI[simp,intro!]: "\<lbrakk>is_pure_assn a; is_pure_assn b\<rbrakk> \<Longrightarrow> is_pure_assn (a*b)"
  by (auto elim!: is_pure_assnE)







end
