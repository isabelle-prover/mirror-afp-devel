section\<open>More Instances of Replacement\<close>

theory Replacement_Instances
  imports
    Separation_Instances
    Transitive_Models.Pointed_DC_Relative
begin

synthesize "setdiff" from_definition "setdiff" assuming "nonempty"
arity_theorem for "setdiff_fm"

relationalize  "first_rel" "is_first" external
synthesize "first_fm" from_definition "is_first" assuming "nonempty"

relationalize  "minimum_rel" "is_minimum" external
definition is_minimum' where
  "is_minimum'(M,R,X,u) \<equiv> (M(u) \<and> u \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> u \<longrightarrow> a \<in> R) \<and> pair(M, u, v, a))) \<and>
    (\<exists>x[M].
        (M(x) \<and> x \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> x \<longrightarrow> a \<in> R) \<and> pair(M, x, v, a))) \<and>
        (\<forall>y[M]. M(y) \<and> y \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> y \<longrightarrow> a \<in> R) \<and> pair(M, y, v, a)) \<longrightarrow> y = x)) \<or>
    \<not> (\<exists>x[M]. (M(x) \<and> x \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> x \<longrightarrow> a \<in> R) \<and> pair(M, x, v, a))) \<and>
               (\<forall>y[M]. M(y) \<and> y \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> y \<longrightarrow> a \<in> R) \<and> pair(M, y, v, a)) \<longrightarrow> y = x)) \<and>
    empty(M, u)"

synthesize "minimum" from_definition "is_minimum'" assuming "nonempty"
arity_theorem for "minimum_fm"

lemma composition_fm_type[TC]: "a0 \<in> \<omega> \<Longrightarrow> a1 \<in> \<omega> \<Longrightarrow> a2 \<in> \<omega> \<Longrightarrow>
   composition_fm(a0,a1,a2) \<in> formula"
  unfolding composition_fm_def by simp

arity_theorem for "composition_fm"

definition is_omega_funspace :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o" where
  "is_omega_funspace(N,B,n,z) \<equiv>  \<exists>o[N]. omega(N,o) \<and> n\<in>o \<and> is_funspace(N, n, B, z)"

synthesize "omega_funspace" from_definition "is_omega_funspace" assuming "nonempty"
arity_theorem for "omega_funspace_fm"

definition HAleph_wfrec_repl_body where
  "HAleph_wfrec_repl_body(N,mesa,x,z) \<equiv> \<exists>y[N].
                   pair(N, x, y, z) \<and>
                   (\<exists>f[N].
                       (\<forall>z[N].
                           z \<in> f \<longleftrightarrow>
                           (\<exists>xa[N].
                               \<exists>y[N].
                                  \<exists>xaa[N].
                                     \<exists>sx[N].
                                        \<exists>r_sx[N].
                                           \<exists>f_r_sx[N].
                                              pair(N, xa, y, z) \<and>
                                              pair(N, xa, x, xaa) \<and>
                                              upair(N, xa, xa, sx) \<and>
                                              pre_image(N, mesa, sx, r_sx) \<and> restriction(N, f, r_sx, f_r_sx) \<and> xaa \<in> mesa \<and> is_HAleph(N, xa, f_r_sx, y))) \<and>
                       is_HAleph(N, x, f, y))"

(* MOVE THIS to an appropriate place *)
arity_theorem for "ordinal_fm"
arity_theorem for "is_Limit_fm"
arity_theorem for "empty_fm"
arity_theorem for "fun_apply_fm"

synthesize "HAleph_wfrec_repl_body" from_definition assuming "nonempty"
arity_theorem for "HAleph_wfrec_repl_body_fm"

definition dcwit_repl_body where
  "dcwit_repl_body(N,mesa,A,a,s,R) \<equiv> \<lambda>x z. \<exists>y[N]. pair(N, x, y, z) \<and>
                                is_wfrec
                                 (N, \<lambda>n f. is_nat_case
                                             (N, a,
                                              \<lambda>m bmfm.
                                                 \<exists>fm[N].
                                                    \<exists>cp[N].
                                                       is_apply(N, f, m, fm) \<and>
                                                       is_Collect(N, A, \<lambda>x. \<exists>fmx[N]. (N(x) \<and> fmx \<in> R) \<and> pair(N, fm, x, fmx), cp) \<and>
                                                       is_apply(N, s, cp, bmfm),
                                              n),
                                  mesa, x, y)"

manual_schematic for "dcwit_repl_body" assuming "nonempty"
  unfolding dcwit_repl_body_def
  by (rule iff_sats is_nat_case_iff_sats is_eclose_iff_sats sep_rules | simp)+

synthesize "dcwit_repl_body" from_schematic

definition dcwit_aux_fm where
  "dcwit_aux_fm(A,s,R) \<equiv> (\<cdot>\<exists>\<cdot>\<cdot>4`2 is 0\<cdot> \<and>
               (\<cdot>\<exists>\<cdot>Collect_fm
                   (succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(A)))))))))),
                    (\<cdot>\<exists>\<cdot>\<cdot>0 \<in>
                       succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(R)))))))))))) \<cdot> \<and>
                       pair_fm(3, 1, 0) \<cdot>\<cdot>),
                    0) \<and>
                  \<cdot> succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(s))))))))))`0 is 2\<cdot>\<cdot>\<cdot>)\<cdot>\<cdot>)"

arity_theorem for "dcwit_aux_fm"

lemma dcwit_aux_fm_type[TC]: "A \<in> \<omega> \<Longrightarrow> s \<in> \<omega> \<Longrightarrow> R \<in> \<omega> \<Longrightarrow> dcwit_aux_fm(A,s,R) \<in> formula"
  by (simp_all add: dcwit_aux_fm_def)

definition is_nat_case_dcwit_aux_fm where
  "is_nat_case_dcwit_aux_fm(A,a,s,R) \<equiv> is_nat_case_fm
           (succ(succ(succ(succ(succ(succ(a)))))),dcwit_aux_fm(A,s,R),
            2, 0)"

lemma is_nat_case_dcwit_aux_fm_type[TC]: "A \<in> \<omega> \<Longrightarrow> a \<in> \<omega> \<Longrightarrow> s \<in> \<omega> \<Longrightarrow> R \<in> \<omega> \<Longrightarrow> is_nat_case_dcwit_aux_fm(A,a,s,R) \<in> formula"
  by (simp_all add: is_nat_case_dcwit_aux_fm_def)

manual_arity for "is_nat_case_dcwit_aux_fm"
  unfolding is_nat_case_dcwit_aux_fm_def
  by (rule arity_dcwit_aux_fm[THEN [6] arity_is_nat_case_fm]) simp_all

manual_arity for "dcwit_repl_body_fm"
  using arity_is_nat_case_dcwit_aux_fm[THEN [6] arity_is_wfrec_fm]
  unfolding dcwit_repl_body_fm_def  is_nat_case_dcwit_aux_fm_def dcwit_aux_fm_def
  by (auto simp add: arity(1-33))

lemma arity_dcwit_repl_body: "arity(dcwit_repl_body_fm(6,5,4,3,2,0,1)) = 7"
  by (simp_all add: FOL_arities arity_dcwit_repl_body_fm ord_simp_union)

definition fst2_snd2
  where "fst2_snd2(x) \<equiv> \<langle>fst(fst(x)), snd(snd(x))\<rangle>"

relativize functional "fst2_snd2" "fst2_snd2_rel"
relationalize "fst2_snd2_rel" "is_fst2_snd2"

lemma (in M_trivial) fst2_snd2_abs:
  assumes "M(x)" "M(res)"
  shows "is_fst2_snd2(M, x, res) \<longleftrightarrow> res = fst2_snd2(x)"
  unfolding is_fst2_snd2_def fst2_snd2_def
  using fst_rel_abs[symmetric] snd_rel_abs[symmetric] fst_abs snd_abs assms
  by simp

synthesize "is_fst2_snd2" from_definition assuming "nonempty"
arity_theorem for "is_fst2_snd2_fm"

definition sndfst_fst2_snd2
  where "sndfst_fst2_snd2(x) \<equiv> \<langle>snd(fst(x)), fst(fst(x)), snd(snd(x))\<rangle>"

relativize functional "sndfst_fst2_snd2" "sndfst_fst2_snd2_rel"
relationalize "sndfst_fst2_snd2_rel" "is_sndfst_fst2_snd2"
synthesize "is_sndfst_fst2_snd2" from_definition assuming "nonempty"
arity_theorem for "is_sndfst_fst2_snd2_fm"

definition RepFun_body :: "i \<Rightarrow> i \<Rightarrow> i"where
  "RepFun_body(u,v) \<equiv> {{\<langle>v, x\<rangle>} . x \<in> u}"

relativize functional "RepFun_body" "RepFun_body_rel"
relationalize "RepFun_body_rel" "is_RepFun_body"
synthesize "is_RepFun_body" from_definition assuming "nonempty"
arity_theorem for "is_RepFun_body_fm"

lemma arity_body_repfun:
  "arity((\<cdot>\<exists>\<cdot>cons_fm(0, 3, 2) \<and> pair_fm(5, 1, 0) \<cdot>\<cdot>)) = 5"
  using arity_cons_fm arity_pair_fm pred_Un_distrib union_abs1 FOL_arities
  by auto

lemma arity_RepFun: "arity(is_RepFun_body_fm(0, 1, 2)) = 3"
  unfolding is_RepFun_body_fm_def
  using arity_Replace_fm[OF _ _ _ _ arity_body_repfun] arity_fst_fm arity_snd_fm arity_empty_fm
    pred_Un_distrib union_abs2 union_abs1 FOL_arities
  by simp

definition order_eq_map where
  "order_eq_map(M,A,r,a,z) \<equiv> \<exists>x[M]. \<exists>g[M]. \<exists>mx[M]. \<exists>par[M].
             ordinal(M,x) & pair(M,a,x,z) & membership(M,x,mx) &
             pred_set(M,A,a,r,par) & order_isomorphism(M,par,r,x,mx,g)"

synthesize "order_eq_map" from_definition assuming "nonempty"
arity_theorem for "is_ord_iso_fm"
arity_theorem for "order_eq_map_fm"

(* Banach *)
synthesize "is_banach_functor" from_definition assuming "nonempty"
arity_theorem for "is_banach_functor_fm"

definition banach_body_iterates where
  "banach_body_iterates(M,X,Y,f,g,W,n,x,z) \<equiv>
\<exists>y[M].
                   pair(M, x, y, z) \<and>
                   (\<exists>fa[M].
                       (\<forall>z[M].
                           z \<in> fa \<longleftrightarrow>
                           (\<exists>xa[M].
                               \<exists>y[M].
                                  \<exists>xaa[M].
                                     \<exists>sx[M].
                                        \<exists>r_sx[M].
                                           \<exists>f_r_sx[M]. \<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) \<and>
                                              membership(M,sn,msn) \<and>
                                              pair(M, xa, y, z) \<and>
                                              pair(M, xa, x, xaa) \<and>
                                              upair(M, xa, xa, sx) \<and>
                                              pre_image(M, msn, sx, r_sx) \<and>
                                              restriction(M, fa, r_sx, f_r_sx) \<and>
                                              xaa \<in> msn \<and>
                                              (empty(M, xa) \<longrightarrow> y = W) \<and>
                                              (\<forall>m[M].
                                                  successor(M, m, xa) \<longrightarrow>
                                                  (\<exists>gm[M].
                                                      is_apply(M, f_r_sx, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                                              (is_quasinat(M, xa) \<or> empty(M, y)))) \<and>
                       (empty(M, x) \<longrightarrow> y = W) \<and>
                       (\<forall>m[M].
                           successor(M, m, x) \<longrightarrow>
                           (\<exists>gm[M]. is_apply(M, fa, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                       (is_quasinat(M, x) \<or> empty(M, y)))"

synthesize "is_quasinat" from_definition assuming "nonempty"
arity_theorem for "is_quasinat_fm"

synthesize "banach_body_iterates" from_definition assuming "nonempty"
arity_theorem for "banach_body_iterates_fm"

definition banach_is_iterates_body where
  "banach_is_iterates_body(M,X,Y,f,g,W,n,y) \<equiv> \<exists>om[M]. omega(M,om) \<and> n \<in> om \<and>
             (\<exists>sn[M].
                 \<exists>msn[M].
                    successor(M, n, sn) \<and>
                    membership(M, sn, msn) \<and>
                    (\<exists>fa[M].
                        (\<forall>z[M].
                            z \<in> fa \<longleftrightarrow>
                            (\<exists>x[M].
                                \<exists>y[M].
                                   \<exists>xa[M].
                                      \<exists>sx[M].
                                         \<exists>r_sx[M].
                                            \<exists>f_r_sx[M].
                                               pair(M, x, y, z) \<and>
                                               pair(M, x, n, xa) \<and>
                                               upair(M, x, x, sx) \<and>
                                               pre_image(M, msn, sx, r_sx) \<and>
                                               restriction(M, fa, r_sx, f_r_sx) \<and>
                                               xa \<in> msn \<and>
                                               (empty(M, x) \<longrightarrow> y = W) \<and>
                                               (\<forall>m[M].
                                                   successor(M, m, x) \<longrightarrow>
                                                   (\<exists>gm[M].
                                                       fun_apply(M, f_r_sx, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                                               (is_quasinat(M, x) \<or> empty(M, y)))) \<and>
                        (empty(M, n) \<longrightarrow> y = W) \<and>
                        (\<forall>m[M].
                            successor(M, m, n) \<longrightarrow>
                            (\<exists>gm[M]. fun_apply(M, fa, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                        (is_quasinat(M, n) \<or> empty(M, y))))"

synthesize "banach_is_iterates_body" from_definition assuming "nonempty"
arity_theorem for "banach_is_iterates_body_fm"

(* (##M)(f) \<Longrightarrow> strong_replacement(##M, \<lambda>x y. y = \<langle>x, transrec(x, \<lambda>a g. f ` (g `` a))\<rangle>) *)

definition trans_apply_image where
  "trans_apply_image(f) \<equiv> \<lambda>a g. f ` (g `` a)"

relativize functional "trans_apply_image" "trans_apply_image_rel"
relationalize "trans_apply_image" "is_trans_apply_image"

(* MOVE THIS to an appropriate place *)
schematic_goal arity_is_recfun_fm[arity]:
  "p \<in> formula \<Longrightarrow> a \<in> \<omega> \<Longrightarrow> z \<in> \<omega> \<Longrightarrow> r \<in> \<omega> \<Longrightarrow> arity(is_recfun_fm(p, a, z ,r)) = ?ar"
  unfolding is_recfun_fm_def
  by (simp add:arity) (* clean simpset from arities, use correct attrib *)
    (* Don't know why it doesn't use the theorem at \<^file>\<open>Arities\<close> *)
schematic_goal arity_is_wfrec_fm[arity]:
  "p \<in> formula \<Longrightarrow> a \<in> \<omega> \<Longrightarrow> z \<in> \<omega> \<Longrightarrow> r \<in> \<omega> \<Longrightarrow> arity(is_wfrec_fm(p, a, z ,r)) = ?ar"
  unfolding is_wfrec_fm_def
  by (simp add:arity)
schematic_goal arity_is_transrec_fm[arity]:
  "p \<in> formula \<Longrightarrow> a \<in> \<omega> \<Longrightarrow> z \<in> \<omega> \<Longrightarrow> arity(is_transrec_fm(p, a, z)) = ?ar"
  unfolding is_transrec_fm_def
  by (simp add:arity)

synthesize "is_trans_apply_image" from_definition assuming "nonempty"
arity_theorem for "is_trans_apply_image_fm"


definition transrec_apply_image_body where
  "transrec_apply_image_body(M,f,mesa,x,z) \<equiv>  \<exists>y[M]. pair(M, x, y, z) \<and>
                                (\<exists>fa[M].
                                    (\<forall>z[M].
                                        z \<in> fa \<longleftrightarrow>
                                        (\<exists>xa[M].
                                            \<exists>y[M].
                                               \<exists>xaa[M].
                                                  \<exists>sx[M].
                                                     \<exists>r_sx[M].
                                                        \<exists>f_r_sx[M].
                                                           pair(M, xa, y, z) \<and>
                                                           pair(M, xa, x, xaa) \<and>
                                                           upair(M, xa, xa, sx) \<and>
                                                           pre_image(M, mesa, sx, r_sx) \<and>
                                                           restriction(M, fa, r_sx, f_r_sx) \<and>
                                                           xaa \<in> mesa \<and> is_trans_apply_image(M, f, xa, f_r_sx, y))) \<and>
                                    is_trans_apply_image(M, f, x, fa, y))"

synthesize "transrec_apply_image_body" from_definition assuming "nonempty"
arity_theorem for "transrec_apply_image_body_fm"

definition is_trans_apply_image_body where
  "is_trans_apply_image_body(M,f,\<beta>,a,w) \<equiv> \<exists>z[M]. pair(M,a,z,w) \<and> a\<in>\<beta> \<and> (\<exists>sa[M].
                \<exists>esa[M].
                   \<exists>mesa[M].
                      upair(M, a, a, sa) \<and>
                      is_eclose(M, sa, esa) \<and>
                      membership(M, esa, mesa) \<and>
                      (\<exists>fa[M].
                          (\<forall>z[M].
                              z \<in> fa \<longleftrightarrow>
                              (\<exists>x[M].
                                  \<exists>y[M].
                                     \<exists>xa[M].
                                        \<exists>sx[M].
                                           \<exists>r_sx[M].
                                              \<exists>f_r_sx[M].
                                                 pair(M, x, y, z) \<and>
                                                 pair(M, x, a, xa) \<and>
                                                 upair(M, x, x, sx) \<and>
                                                 pre_image(M, mesa, sx, r_sx) \<and>
                                                 restriction(M, fa, r_sx, f_r_sx) \<and>
                                                 xa \<in> mesa \<and> is_trans_apply_image(M, f, x, f_r_sx, y))) \<and>
                          is_trans_apply_image(M, f, a, fa, z)))"

manual_schematic "is_trans_apply_image_body_schematic" for "is_trans_apply_image_body"assuming "nonempty"
  unfolding is_trans_apply_image_body_def
  by (rule sep_rules is_eclose_iff_sats is_trans_apply_image_iff_sats | simp)+

synthesize "is_trans_apply_image_body" from_schematic "is_trans_apply_image_body_schematic"
arity_theorem for "is_trans_apply_image_body_fm"

synthesize "is_converse" from_definition assuming "nonempty"
arity_theorem for "is_converse_fm"

definition replacement_is_omega_funspace_fm where "replacement_is_omega_funspace_fm \<equiv>  omega_funspace_fm(2,0,1)"
definition replacement_HAleph_wfrec_repl_body_fm where "replacement_HAleph_wfrec_repl_body_fm \<equiv>  HAleph_wfrec_repl_body_fm(2,0,1)"
definition replacement_is_fst2_snd2_fm where "replacement_is_fst2_snd2_fm \<equiv>  is_fst2_snd2_fm(0,1)"
definition replacement_is_sndfst_fst2_snd2_fm where "replacement_is_sndfst_fst2_snd2_fm \<equiv>  is_sndfst_fst2_snd2_fm(0,1)"
definition replacement_is_order_eq_map_fm where "replacement_is_order_eq_map_fm \<equiv>  order_eq_map_fm(2,3,0,1)"
definition replacement_transrec_apply_image_body_fm where "replacement_transrec_apply_image_body_fm \<equiv>  transrec_apply_image_body_fm(3,2,0,1)"
definition banach_replacement_iterates_fm where "banach_replacement_iterates_fm \<equiv> banach_is_iterates_body_fm(6,5,4,3,2,0,1)"
definition replacement_is_trans_apply_image_fm where "replacement_is_trans_apply_image_fm \<equiv> is_trans_apply_image_body_fm(3,2,0,1)"
definition banach_iterates_fm where "banach_iterates_fm \<equiv> banach_body_iterates_fm(7,6,5,4,3,2,0,1)"
definition replacement_dcwit_repl_body_fm where "replacement_dcwit_repl_body_fm \<equiv> dcwit_repl_body_fm(6,5,4,3,2,0,1)"

locale M_ZF2 = M_ZF1 +
  assumes
    replacement_ax2:
    "replacement_assm(M,env,replacement_is_omega_funspace_fm)"
    "replacement_assm(M,env,replacement_HAleph_wfrec_repl_body_fm)"
    "replacement_assm(M,env,replacement_is_fst2_snd2_fm)"
    "replacement_assm(M,env,replacement_is_sndfst_fst2_snd2_fm)"
    "replacement_assm(M,env,replacement_is_order_eq_map_fm)"
    "replacement_assm(M,env,replacement_transrec_apply_image_body_fm)"
    "replacement_assm(M,env,banach_replacement_iterates_fm)"
    "replacement_assm(M,env,replacement_is_trans_apply_image_fm)"
    "replacement_assm(M,env,banach_iterates_fm)"
    "replacement_assm(M,env,replacement_dcwit_repl_body_fm)"
    and
    Lambda_in_M_replacement2:
    "replacement_assm(M,env,Lambda_in_M_fm(fst_fm(0,1),0))"
    "replacement_assm(M,env,Lambda_in_M_fm(domain_fm(0,1),0))"
    "replacement_assm(M,env,Lambda_in_M_fm(snd_fm(0,1),0))"
    "replacement_assm(M,env,Lambda_in_M_fm(big_union_fm(0,1),0))"
    "replacement_assm(M,env,Lambda_in_M_fm(is_cardinal_fm(0,1),0))"
    "replacement_assm(M,env,Lambda_in_M_fm(is_converse_fm(0,1),0))"
    and
    LambdaPair_in_M_replacement2:
    "replacement_assm(M,env,LambdaPair_in_M_fm(image_fm(0,1,2),0))"
    "replacement_assm(M,env,LambdaPair_in_M_fm(setdiff_fm(0,1,2),0))"
    "replacement_assm(M,env,LambdaPair_in_M_fm(minimum_fm(0,1,2),0))"
    "replacement_assm(M,env,LambdaPair_in_M_fm(upair_fm(0,1,2),0))"
    "replacement_assm(M,env,LambdaPair_in_M_fm(is_RepFun_body_fm(0,1,2),0))"
    "replacement_assm(M,env,LambdaPair_in_M_fm(composition_fm(0,1,2),0))"

definition instances2_fms where "instances2_fms \<equiv>
  { replacement_is_omega_funspace_fm,
    replacement_HAleph_wfrec_repl_body_fm,
    replacement_is_fst2_snd2_fm,
    replacement_is_sndfst_fst2_snd2_fm,
    replacement_is_order_eq_map_fm,
    replacement_transrec_apply_image_body_fm,
    banach_replacement_iterates_fm,
    replacement_is_trans_apply_image_fm,
    banach_iterates_fm,
    replacement_dcwit_repl_body_fm,
    Lambda_in_M_fm(fst_fm(0,1),0),
    Lambda_in_M_fm(domain_fm(0,1),0),
    Lambda_in_M_fm(snd_fm(0,1),0),
    Lambda_in_M_fm(big_union_fm(0,1),0),
    Lambda_in_M_fm(is_cardinal_fm(0,1),0),
    Lambda_in_M_fm(is_converse_fm(0,1),0),
    LambdaPair_in_M_fm(image_fm(0,1,2),0),
    LambdaPair_in_M_fm(setdiff_fm(0,1,2),0),
    LambdaPair_in_M_fm(minimum_fm(0,1,2),0),
    LambdaPair_in_M_fm(upair_fm(0,1,2),0),
    LambdaPair_in_M_fm(is_RepFun_body_fm(0,1,2),0),
    LambdaPair_in_M_fm(composition_fm(0,1,2),0) }"

txt\<open>This set has 22 internalized formulas.\<close>

lemmas replacement_instances2_defs =
  replacement_is_omega_funspace_fm_def
  replacement_HAleph_wfrec_repl_body_fm_def
  replacement_is_fst2_snd2_fm_def
  replacement_is_sndfst_fst2_snd2_fm_def
  replacement_is_order_eq_map_fm_def
  replacement_transrec_apply_image_body_fm_def
  banach_replacement_iterates_fm_def
  replacement_is_trans_apply_image_fm_def
  banach_iterates_fm_def
  replacement_dcwit_repl_body_fm_def

declare (in M_ZF2) replacement_instances2_defs [simp]

lemma instances2_fms_type[TC]: "instances2_fms \<subseteq> formula"
  unfolding replacement_instances2_defs instances2_fms_def
  by (simp del:Lambda_in_M_fm_def)

locale M_ZF2_trans = M_ZF1_trans + M_ZF2

locale M_ZFC2 = M_ZFC1 + M_ZF2

locale M_ZFC2_trans = M_ZFC1_trans + M_ZF2_trans + M_ZFC2

lemma (in M_ZF2_trans) lam_replacement_domain : "lam_replacement(##M, domain)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of domain]
    Lambda_in_M[where \<phi>="domain_fm(0,1)" and env="[]"] domain_type domain_abs
    Lambda_in_M_replacement2(2)
    arity_domain_fm[of 0 1] ord_simp_union transitivity domain_closed
  by simp

lemma (in M_ZF2_trans) lam_replacement_converse : "lam_replacement(##M, converse)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of converse] nonempty
    Lambda_in_M[where \<phi>="is_converse_fm(0,1)" and env="[]"]
    is_converse_fm_type converse_abs
    arity_is_converse_fm[of 0 1] ord_simp_union transitivity converse_closed
    Lambda_in_M_replacement2(6)
  by simp

lemma (in M_ZF2_trans) lam_replacement_fst : "lam_replacement(##M, fst)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of fst]
    Lambda_in_M[where \<phi>="fst_fm(0,1)" and env="[]"]
    fst_iff_sats[symmetric] fst_abs fst_type
    arity_fst_fm[of 0 1] ord_simp_union transitivity fst_closed
    Lambda_in_M_replacement2(1)
  by simp

lemma (in M_ZF2_trans) lam_replacement_snd : "lam_replacement(##M, snd)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of snd]
    Lambda_in_M[where \<phi>="snd_fm(0,1)" and env="[]"]
    snd_iff_sats[symmetric] snd_abs snd_type
    arity_snd_fm[of 0 1] ord_simp_union transitivity snd_closed
    Lambda_in_M_replacement2(3)
  by simp

lemma (in M_ZF2_trans) lam_replacement_Union : "lam_replacement(##M, Union)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of Union]
    Lambda_in_M[where \<phi>="big_union_fm(0,1)" and env="[]"] Union_abs
    union_fm_def big_union_iff_sats[symmetric]
    arity_big_union_fm[of 0 1] ord_simp_union transitivity Union_closed
    Lambda_in_M_replacement2(4)
  by simp

lemma (in M_ZF2_trans) lam_replacement_image:
  "lam_replacement(##M, \<lambda>p. fst(p) `` snd(p))"
  using lam_replacement2_in_ctm[where \<phi>="image_fm(0,1,2)" and env="[]"]
    image_type image_iff_sats image_abs
    arity_image_fm[of 0 1 2] ord_simp_union transitivity image_closed fst_snd_closed
    LambdaPair_in_M_replacement2(1)
  by simp

lemma (in M_ZF2_trans) lam_replacement_Diff:
  "lam_replacement(##M, \<lambda>p. fst(p) - snd(p))"
  using lam_replacement2_in_ctm[where \<phi>="setdiff_fm(0,1,2)" and env="[]"]
    setdiff_fm_type setdiff_iff_sats setdiff_abs
    arity_setdiff_fm[of 0 1 2] ord_simp_union transitivity Diff_closed fst_snd_closed
    nonempty LambdaPair_in_M_replacement2(2)
  by simp

lemma is_minimum_eq :
  "M(R) \<Longrightarrow> M(X) \<Longrightarrow> M(u) \<Longrightarrow> is_minimum(M,R,X,u) \<longleftrightarrow> is_minimum'(M,R,X,u)"
  unfolding is_minimum_def is_minimum'_def is_The_def is_first_def by simp

context M_trivial
begin

lemma first_closed:
  "M(B) \<Longrightarrow> M(r) \<Longrightarrow> first(u,r,B) \<Longrightarrow> M(u)"
  using transM[OF first_is_elem] by simp

is_iff_rel for "first"
  unfolding is_first_def first_rel_def by auto

is_iff_rel for "minimum"
  unfolding is_minimum_def minimum_rel_def
  using is_first_iff The_abs nonempty
  by force

end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

lemma (in M_ZF2_trans) lam_replacement_minimum:
  "lam_replacement(##M, \<lambda>p. minimum(fst(p), snd(p)))"
  using lam_replacement2_in_ctm[where \<phi>="minimum_fm(0,1,2)" and env="[]"]
    minimum_iff_sats[symmetric] is_minimum_iff minimum_abs is_minimum_eq
    arity_minimum_fm[of 0 1 2] ord_simp_union minimum_fm_type
    minimum_closed zero_in_M LambdaPair_in_M_replacement2(3)
  by simp

lemma (in M_ZF2_trans) lam_replacement_Upair: "lam_replacement(##M, \<lambda>p. Upair(fst(p), snd(p)))"
  using lam_replacement2_in_ctm[where \<phi>="upair_fm(0,1,2)" and env="[]" and f="Upair"]
    Upair_closed upair_type upair_iff_sats Upair_eq_cons
    arity_upair_fm[of 0 1 2,simplified] ord_simp_union LambdaPair_in_M_replacement2(4)
  by simp

lemma (in M_ZF2_trans) lam_replacement_comp:
  "lam_replacement(##M, \<lambda>p. comp(fst(p), snd(p)))"
  using lam_replacement2_in_ctm[where \<phi>="composition_fm(0,1,2)" and env="[]" and f="comp"]
    comp_closed composition_fm_type composition_iff_sats
    arity_composition_fm[of 0 1 2] ord_simp_union LambdaPair_in_M_replacement2(6)
  by simp

lemma (in M_ZF2_trans) omega_funspace_abs:
  "B\<in>M \<Longrightarrow> n\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> is_omega_funspace(##M,B,n,z) \<longleftrightarrow> n\<in>\<omega> \<and> is_funspace(##M,n,B,z)"
  unfolding is_omega_funspace_def using nat_in_M by simp

lemma (in M_ZF2_trans) replacement_is_omega_funspace:
  "B\<in>M \<Longrightarrow> strong_replacement(##M, is_omega_funspace(##M,B))"
  using strong_replacement_rel_in_ctm[where \<phi>="omega_funspace_fm(2,0,1)" and env="[B]"]
    zero_in_M arity_omega_funspace_fm ord_simp_union replacement_ax2(1)
  by simp

lemma (in M_ZF2_trans) replacement_omega_funspace:
  "b\<in>M\<Longrightarrow>strong_replacement(##M, \<lambda>n z. n\<in>\<omega> \<and> is_funspace(##M,n,b,z))"
  using strong_replacement_cong[THEN iffD2,OF _ replacement_is_omega_funspace[of b]]
    omega_funspace_abs[of b] setclass_iff[THEN iffD1]
  by (simp del:setclass_iff)

lemma (in M_ZF2_trans) replacement_HAleph_wfrec_repl_body:
  "B\<in>M \<Longrightarrow> strong_replacement(##M, HAleph_wfrec_repl_body(##M,B))"
  using strong_replacement_rel_in_ctm[where \<phi>="HAleph_wfrec_repl_body_fm(2,0,1)" and env="[B]"]
    zero_in_M arity_HAleph_wfrec_repl_body_fm replacement_ax2(2) ord_simp_union
  by simp

lemma (in M_ZF2_trans) HAleph_wfrec_repl:
  "(##M)(sa) \<Longrightarrow>
        (##M)(esa) \<Longrightarrow>
        (##M)(mesa) \<Longrightarrow>
        strong_replacement
         (##M,
          \<lambda>x z. \<exists>y[##M].
                   pair(##M, x, y, z) \<and>
                   (\<exists>f[##M].
                       (\<forall>z[##M].
                           z \<in> f \<longleftrightarrow>
                           (\<exists>xa[##M].
                               \<exists>y[##M].
                                  \<exists>xaa[##M].
                                     \<exists>sx[##M].
                                        \<exists>r_sx[##M].
                                           \<exists>f_r_sx[##M].
                                              pair(##M, xa, y, z) \<and>
                                              pair(##M, xa, x, xaa) \<and>
                                              upair(##M, xa, xa, sx) \<and>
                                              pre_image(##M, mesa, sx, r_sx) \<and> restriction(##M, f, r_sx, f_r_sx) \<and> xaa \<in> mesa \<and> is_HAleph(##M, xa, f_r_sx, y))) \<and>
                       is_HAleph(##M, x, f, y)))"
  using replacement_HAleph_wfrec_repl_body unfolding HAleph_wfrec_repl_body_def by simp

lemma dcwit_replacement:"Ord(na) \<Longrightarrow>
    N(na) \<Longrightarrow>
    N(A) \<Longrightarrow>
    N(a) \<Longrightarrow>
    N(s) \<Longrightarrow>
    N(R) \<Longrightarrow>
    transrec_replacement
     (N, \<lambda>n f ntc.
            is_nat_case
             (N, a,
              \<lambda>m bmfm.
                 \<exists>fm[N]. \<exists>cp[N].
                    is_apply(N, f, m, fm) \<and>
                    is_Collect(N, A, \<lambda>x. \<exists>fmx[N]. (N(x) \<and> fmx \<in> R) \<and> pair(N, fm, x, fmx), cp) \<and>
                    is_apply(N, s, cp, bmfm),
              n, ntc),na)"
  unfolding transrec_replacement_def wfrec_replacement_def oops

lemma (in M_ZF2_trans) replacement_dcwit_repl_body:
  "(##M)(mesa) \<Longrightarrow> (##M)(A) \<Longrightarrow> (##M)(a) \<Longrightarrow> (##M)(s) \<Longrightarrow> (##M)(R) \<Longrightarrow>
   strong_replacement(##M, dcwit_repl_body(##M,mesa,A,a,s,R))"
  using strong_replacement_rel_in_ctm[where \<phi>="dcwit_repl_body_fm(6,5,4,3,2,0,1)"
      and env="[R,s,a,A,mesa]" and f="dcwit_repl_body(##M,mesa,A,a,s,R)"]
    zero_in_M arity_dcwit_repl_body replacement_ax2(10)
  by simp

lemma (in M_ZF2_trans) dcwit_repl:
  "(##M)(sa) \<Longrightarrow>
        (##M)(esa) \<Longrightarrow>
        (##M)(mesa) \<Longrightarrow> (##M)(A) \<Longrightarrow> (##M)(a) \<Longrightarrow> (##M)(s) \<Longrightarrow> (##M)(R) \<Longrightarrow>
        strong_replacement
              ((##M), \<lambda>x z. \<exists>y[(##M)]. pair((##M), x, y, z) \<and>
                                is_wfrec
                                 ((##M), \<lambda>n f. is_nat_case
                                             ((##M), a,
                                              \<lambda>m bmfm.
                                                 \<exists>fm[(##M)].
                                                    \<exists>cp[(##M)].
                                                       is_apply((##M), f, m, fm) \<and>
                                                       is_Collect((##M), A, \<lambda>x. \<exists>fmx[(##M)]. ((##M)(x) \<and> fmx \<in> R) \<and> pair((##M), fm, x, fmx), cp) \<and>
                                                       is_apply((##M), s, cp, bmfm),
                                              n),
                                  mesa, x, y))"
  using replacement_dcwit_repl_body unfolding dcwit_repl_body_def by simp

lemma (in M_ZF2_trans) replacement_fst2_snd2: "strong_replacement(##M, \<lambda>x y. y = \<langle>fst(fst(x)), snd(snd(x))\<rangle>)"
  using strong_replacement_in_ctm[where \<phi>="is_fst2_snd2_fm(0,1)" and env="[]"]
    zero_in_M fst_snd_closed pair_in_M_iff
    arity_is_fst2_snd2_fm ord_simp_union fst2_snd2_abs replacement_ax2(3)
  unfolding fst2_snd2_def
  by simp

lemma (in M_trivial) sndfst_fst2_snd2_abs:
  assumes "M(x)" "M(res)"
  shows "is_sndfst_fst2_snd2(M, x, res) \<longleftrightarrow> res = sndfst_fst2_snd2(x)"
  unfolding is_sndfst_fst2_snd2_def sndfst_fst2_snd2_def
  using fst_rel_abs[symmetric] snd_rel_abs[symmetric] fst_abs snd_abs assms
  by simp

lemma (in M_ZF2_trans) replacement_sndfst_fst2_snd2:
  "strong_replacement(##M, \<lambda>x y. y = \<langle>snd(fst(x)), fst(fst(x)), snd(snd(x))\<rangle>)"
  using strong_replacement_in_ctm[where \<phi>="is_sndfst_fst2_snd2_fm(0,1)" and env="[]"]
    zero_in_M fst_snd_closed pair_in_M_iff
    arity_is_sndfst_fst2_snd2_fm ord_simp_union sndfst_fst2_snd2_abs replacement_ax2(4)
  unfolding sndfst_fst2_snd2_def
  by simp

lemmas (in M_ZF2_trans) M_replacement_ZF_instances = lam_replacement_domain
  lam_replacement_fst lam_replacement_snd lam_replacement_Union
  lam_replacement_Upair lam_replacement_image
  lam_replacement_Diff lam_replacement_converse
  replacement_fst2_snd2 replacement_sndfst_fst2_snd2
  lam_replacement_comp

lemmas (in M_ZF2_trans) M_separation_ZF_instances =  separation_fstsnd_in_sndsnd
  separation_sndfst_eq_fstsnd

sublocale M_ZF2_trans \<subseteq> M_replacement "##M"
  using M_replacement_ZF_instances M_separation_ZF_instances
  by unfold_locales simp

lemma (in M_ZF1_trans) separation_is_dcwit_body:
  assumes "(##M)(A)" "(##M)(a)" "(##M)(g)" "(##M)(R)"
  shows "separation(##M,is_dcwit_body(##M, A, a, g, R))"
  using assms separation_in_ctm[where env="[A,a,g,R]" and \<phi>="is_dcwit_body_fm(1,2,3,4,0)",
      OF _ _ _ is_dcwit_body_iff_sats[symmetric],
      of "\<lambda>_.A" "\<lambda>_.a" "\<lambda>_.g" "\<lambda>_.R" "\<lambda>x. x"]
    nonempty arity_is_dcwit_body_fm is_dcwit_body_fm_type
  by (simp add:ord_simp_union)

lemma (in M_trivial) RepFun_body_abs:
  assumes "M(u)" "M(v)" "M(res)"
  shows "is_RepFun_body(M, u, v, res) \<longleftrightarrow> res = RepFun_body(u,v)"
  unfolding is_RepFun_body_def RepFun_body_def
  using fst_rel_abs[symmetric] snd_rel_abs[symmetric] fst_abs snd_abs assms
    Replace_abs[where P="\<lambda>xa a. a = {\<langle>v, xa\<rangle>}" and A="u"]
    univalent_triv transM[of _ u]
  by auto

lemma (in M_ZF2_trans) RepFun_SigFun_closed: "x \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow> {{\<langle>z, x\<rangle>} . x \<in> x} \<in> M"
  using lam_replacement_sing_const_id lam_replacement_imp_strong_replacement RepFun_closed
    transitivity singleton_in_M_iff pair_in_M_iff
  by simp

lemma (in M_ZF2_trans) replacement_RepFun_body:
  "lam_replacement(##M, \<lambda>p . {{\<langle>snd(p), x\<rangle>} . x \<in> fst(p)})"
  using lam_replacement2_in_ctm[where \<phi>="is_RepFun_body_fm(0,1,2)" and env="[]" and f="\<lambda>p q . {{\<langle>q, x\<rangle>} . x \<in> p}"]
    RepFun_SigFun_closed[OF fst_snd_closed[THEN conjunct1,simplified] fst_snd_closed[THEN conjunct2,simplified]]
    arity_RepFun ord_simp_union transitivity zero_in_M RepFun_body_def RepFun_body_abs RepFun_SigFun_closed
    LambdaPair_in_M_replacement2(5)
  by simp

sublocale M_ZF2_trans \<subseteq> M_replacement_extra "##M"
  by unfold_locales (simp_all add: replacement_RepFun_body
      lam_replacement_minimum del:setclass_iff)

sublocale M_ZF2_trans \<subseteq> M_Perm "##M"
  using separation_PiP_rel separation_injP_rel separation_surjP_rel
    lam_replacement_imp_strong_replacement[OF
      lam_replacement_Sigfun[OF lam_replacement_constant]]
    Pi_replacement1 unfolding Sigfun_def
  by unfold_locales simp_all

lemma (in M_ZF2_trans) replacement_is_order_eq_map:
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> strong_replacement(##M, order_eq_map(##M,A,r))"
  using strong_replacement_rel_in_ctm[where \<phi>="order_eq_map_fm(2,3,0,1)" and env="[A,r]"  and f="order_eq_map(##M,A,r)"]
    order_eq_map_iff_sats[where env="[_,_,A,r]"] zero_in_M fst_snd_closed pair_in_M_iff
    arity_order_eq_map_fm ord_simp_union replacement_ax2(5)
  by simp

lemma (in M_ZF2_trans) banach_iterates:
  assumes "X\<in>M" "Y\<in>M" "f\<in>M" "g\<in>M" "W\<in>M"
  shows "iterates_replacement(##M, is_banach_functor(##M,X,Y,f,g), W)"
proof -
  have "strong_replacement(##M, \<lambda> x z . banach_body_iterates(##M,X,Y,f,g,W,n,x,z))" if "n\<in>\<omega>" for n
    using assms that arity_banach_body_iterates_fm ord_simp_union nat_into_M
      strong_replacement_rel_in_ctm[where \<phi>="banach_body_iterates_fm(7,6,5,4,3,2,0,1)"
        and env="[n,W,g,f,Y,X]"] replacement_ax2(9)
    by simp
  then
  show ?thesis
    using assms nat_into_M Memrel_closed
    unfolding iterates_replacement_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
      is_nat_case_def iterates_MH_def banach_body_iterates_def
    by simp
qed

lemma (in M_ZF2_trans) banach_replacement_iterates:
  assumes "X\<in>M" "Y\<in>M" "f\<in>M" "g\<in>M" "W\<in>M"
  shows "strong_replacement(##M, \<lambda>n y. n\<in>\<omega> \<and> is_iterates(##M,is_banach_functor(##M,X, Y, f, g),W,n,y))"
proof -
  have "strong_replacement(##M, \<lambda> n z . banach_is_iterates_body(##M,X,Y,f,g,W,n,z))"
    using assms arity_banach_is_iterates_body_fm ord_simp_union nat_into_M
      strong_replacement_rel_in_ctm[where \<phi>="banach_is_iterates_body_fm(6,5,4,3,2,0,1)"
        and env="[W,g,f,Y,X]"] replacement_ax2(7)
    by simp
  then
  show ?thesis
    using assms nat_in_M
    unfolding is_iterates_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
      is_nat_case_def iterates_MH_def banach_is_iterates_body_def
    by simp
qed

lemma (in M_ZF2_trans) banach_replacement:
  assumes "(##M)(X)" "(##M)(Y)" "(##M)(f)" "(##M)(g)"
  shows "strong_replacement(##M, \<lambda>n y. n\<in>nat \<and> y = banach_functor(X, Y, f, g)^n (0))"
  using iterates_abs[OF banach_iterates banach_functor_abs,of X Y f g]
    assms banach_functor_closed zero_in_M
    strong_replacement_cong[THEN iffD1,OF _ banach_replacement_iterates[of X Y f g 0]]
  by simp

lemma (in M_ZF2_trans) lam_replacement_cardinal : "lam_replacement(##M, cardinal_rel(##M))"
  using lam_replacement_iff_lam_closed[THEN iffD2,of "cardinal_rel(##M)"]
    cardinal_rel_closed is_cardinal_iff
    Lambda_in_M[where \<phi>="is_cardinal_fm(0,1)" and env="[]",OF is_cardinal_fm_type[of 0 1]]
    arity_is_cardinal_fm[of 0 1] ord_simp_union cardinal_rel_closed transitivity zero_in_M
    Lambda_in_M_replacement2(5)
  by simp_all

lemma (in M_basic) rel2_trans_apply:
  "M(f) \<Longrightarrow> relation2(M,is_trans_apply_image(M,f),trans_apply_image(f))"
  unfolding is_trans_apply_image_def trans_apply_image_def relation2_def
  by auto

lemma (in M_basic) apply_image_closed:
  shows "M(f) \<Longrightarrow> \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(trans_apply_image(f, x, g))"
  unfolding trans_apply_image_def by simp

lemma (in M_basic) apply_image_closed':
  shows "M(f) \<Longrightarrow> \<forall>x[M]. \<forall>g[M]. M(trans_apply_image(f, x, g))"
  unfolding trans_apply_image_def by simp

lemma (in M_ZF2_trans) replacement_transrec_apply_image_body :
  "(##M)(f) \<Longrightarrow> (##M)(mesa) \<Longrightarrow> strong_replacement(##M,transrec_apply_image_body(##M,f,mesa))"
  using strong_replacement_rel_in_ctm[where \<phi>="transrec_apply_image_body_fm(3,2,0,1)" and env="[mesa,f]"]
    zero_in_M arity_transrec_apply_image_body_fm ord_simp_union
    replacement_ax2(6)
  by simp

lemma (in M_ZF2_trans) transrec_replacement_apply_image:
  assumes "(##M)(f)" "(##M)(\<alpha>)"
  shows "transrec_replacement(##M, is_trans_apply_image(##M, f), \<alpha>)"
  unfolding transrec_replacement_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
  using replacement_transrec_apply_image_body[unfolded transrec_apply_image_body_def] assms
    Memrel_closed singleton_closed eclose_closed
  by simp

lemma (in M_ZF2_trans) rec_trans_apply_image_abs:
  assumes "(##M)(f)" "(##M)(x)" "(##M)(y)" "Ord(x)"
  shows "is_transrec(##M,is_trans_apply_image(##M, f),x,y) \<longleftrightarrow> y = transrec(x,trans_apply_image(f))"
  using transrec_abs[OF transrec_replacement_apply_image rel2_trans_apply] assms apply_image_closed
  by simp

lemma (in M_ZF2_trans) replacement_is_trans_apply_image:
  "(##M)(f) \<Longrightarrow> (##M)(\<beta>) \<Longrightarrow> strong_replacement(##M, \<lambda> x z .
    \<exists>y[##M]. pair(##M,x,y,z) \<and> x\<in>\<beta> \<and> (is_transrec(##M,is_trans_apply_image(##M, f),x,y)))"
  unfolding is_transrec_def is_wfrec_def M_is_recfun_def
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x z. M,[x,z,\<beta>,f] \<Turnstile> is_trans_apply_image_body_fm(3,2,0,1)",THEN iffD1])
   apply(rule_tac is_trans_apply_image_body_iff_sats[symmetric,unfolded is_trans_apply_image_body_def,where env="[_,_,\<beta>,f]"])
            apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax2(8)[unfolded replacement_assm_def, rule_format, where env="[\<beta>,f]",simplified])
    apply(simp_all add: arity_is_trans_apply_image_body_fm is_trans_apply_image_body_fm_type ord_simp_union)
  done

lemma (in M_ZF2_trans) trans_apply_abs:
  "(##M)(f) \<Longrightarrow> (##M)(\<beta>) \<Longrightarrow> Ord(\<beta>) \<Longrightarrow> (##M)(x) \<Longrightarrow> (##M)(z) \<Longrightarrow>
    (x\<in>\<beta> \<and> z = \<langle>x, transrec(x, \<lambda>a g. f ` (g `` a)) \<rangle>) \<longleftrightarrow>
    (\<exists>y[##M]. pair(##M,x,y,z) \<and> x\<in>\<beta> \<and> (is_transrec(##M,is_trans_apply_image(##M, f),x,y)))"
  using rec_trans_apply_image_abs Ord_in_Ord
    transrec_closed[OF transrec_replacement_apply_image rel2_trans_apply,of f,simplified]
    apply_image_closed'[of f]
  unfolding trans_apply_image_def
  by auto

lemma (in M_ZF2_trans) replacement_trans_apply_image:
  "(##M)(f) \<Longrightarrow> (##M)(\<beta>) \<Longrightarrow> Ord(\<beta>) \<Longrightarrow>
  strong_replacement(##M, \<lambda>x y. x\<in>\<beta> \<and> y = \<langle>x, transrec(x, \<lambda>a g. f ` (g `` a))\<rangle>)"
  using strong_replacement_cong[THEN iffD1,OF _ replacement_is_trans_apply_image,simplified]
    trans_apply_abs Ord_in_Ord
  by simp

definition ifrFb_body where
  "ifrFb_body(M,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then
  if M(converse(f) ` i) then converse(f) ` i else 0 else 0 else if M(i) then i else 0)"

relativize functional "ifrFb_body" "ifrFb_body_rel"
relationalize "ifrFb_body_rel" "is_ifrFb_body"

synthesize "is_ifrFb_body" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body_fm"

definition ifrangeF_body :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body(M,A,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body(M,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body" "ifrangeF_body_rel"
relationalize "ifrangeF_body_rel" "is_ifrangeF_body"

synthesize "is_ifrangeF_body" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body_fm"

lemma (in M_Z_trans) separation_is_ifrangeF_body:
  "(##M)(A) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body(##M,A,r,s))"
  using separation_in_ctm[where \<phi>="is_ifrangeF_body_fm(1,2,3,0)" and env="[A,r,s]"]
    zero_in_M arity_is_ifrangeF_body_fm ord_simp_union is_ifrangeF_body_fm_type
  by simp

lemma (in M_basic) is_ifrFb_body_closed: "M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body(M, r, s, x, i) \<Longrightarrow> M(i)"
  unfolding ifrangeF_body_def is_ifrangeF_body_def is_ifrFb_body_def If_abs
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF1_trans) ifrangeF_body_abs:
  assumes "(##M)(A)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body(##M,A,r,s,x) \<longleftrightarrow> ifrangeF_body(##M,A,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body(##M, r, s, z, i))= (\<mu> i. is_ifrFb_body(##M, r, s, z, i))" for z
      using is_ifrFb_body_closed[of r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body(##M,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body(##M, r, s, z, i))= (\<mu> i. ifrFb_body(##M, r, s, z, i))" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body(##M,r,s,z,i)" "\<lambda>i. ifrFb_body(##M,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close>
      show "is_ifrFb_body(##M, r, s, z, y) \<longleftrightarrow> ifrFb_body(##M, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body_def is_ifrFb_body_def
        by (cases "y\<in>M"; cases "y\<in>range(s)"; cases "converse(s)`y \<in> M";
            auto dest:transM split del: split_if del:iffI)
          (auto simp flip:setclass_iff; (force simp only:setclass_iff))+
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body(##M, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body(##M, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body(##M,r,s,z,i)" a]
      by simp
    ultimately
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body(##M, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body(##M, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body_def is_ifrangeF_body_def
    by (auto dest:transM)
qed

lemma (in M_ZF1_trans) separation_ifrangeF_body:
  "(##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow> separation
        (##M, \<lambda>y.  \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. if (##M)(x) then x else 0, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body ifrangeF_body_abs
    separation_cong[where P="is_ifrangeF_body(##M,A,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body_def if_range_F_def if_range_F_else_F_def ifrFb_body_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. if (##M)(a) then G`a else 0, b, f, i)\<rangle>) *)

definition ifrFb_body2 where
  "ifrFb_body2(M,G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then
  if M(converse(f) ` i) then G`(converse(f) ` i) else 0 else 0 else if M(i) then G`i else 0)"

relativize functional "ifrFb_body2" "ifrFb_body2_rel"
relationalize "ifrFb_body2_rel" "is_ifrFb_body2"

synthesize "is_ifrFb_body2" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body2_fm"

definition ifrangeF_body2 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body2(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body2(M,G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body2" "ifrangeF_body2_rel"
relationalize "ifrangeF_body2_rel" "is_ifrangeF_body2"

synthesize "is_ifrangeF_body2" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body2_fm"

lemma (in M_Z_trans) separation_is_ifrangeF_body2:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body2(##M,A,G,r,s))"
  using separation_in_ctm[where \<phi>="is_ifrangeF_body2_fm(1,2,3,4,0)" and env="[A,G,r,s]"]
    zero_in_M arity_is_ifrangeF_body2_fm ord_simp_union is_ifrangeF_body2_fm_type
  by simp

lemma (in M_basic) is_ifrFb_body2_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body2(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  unfolding ifrangeF_body2_def is_ifrangeF_body2_def is_ifrFb_body2_def If_abs
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF1_trans) ifrangeF_body2_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body2(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body2(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body2(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body2(##M, G, r, s, z, i))" for z
      using is_ifrFb_body2_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body2(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body2(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body2(##M, G, r, s, z, i))" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body2(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body2(##M,G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close>
      show "is_ifrFb_body2(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body2(##M, G, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body2_def is_ifrFb_body2_def
        by (cases "y\<in>M"; cases "y\<in>range(s)"; cases "converse(s)`y \<in> M";
            auto dest:transM split del: split_if del:iffI)
          (auto simp flip:setclass_iff; (force simp only:setclass_iff))+
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body2(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body2(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body2(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body2(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body2(##M, G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body2_def is_ifrangeF_body2_def
    by (auto dest:transM)
qed

lemma (in M_ZF1_trans) separation_ifrangeF_body2:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation
        (##M,
         \<lambda>y. \<exists>x\<in>A.
                y =
                \<langle>x, \<mu> i. x \<in>
                         if_range_F_else_F(\<lambda>a. if (##M)(a) then G ` a else 0, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body2 ifrangeF_body2_abs
    separation_cong[where P="is_ifrangeF_body2(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body2_def if_range_F_def if_range_F_else_F_def ifrFb_body2_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow> (##M)(F) \<Longrightarrow>
  separation(##M,
    \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. if (##M)(a) then F -`` {a} else 0, b, f, i)\<rangle>) *)

definition ifrFb_body3 where
  "ifrFb_body3(M,G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then
  if M(converse(f) ` i) then G-``{converse(f) ` i} else 0 else 0 else if M(i) then G-``{i} else 0)"

relativize functional "ifrFb_body3" "ifrFb_body3_rel"
relationalize "ifrFb_body3_rel" "is_ifrFb_body3"

synthesize "is_ifrFb_body3" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body3_fm"

definition ifrangeF_body3 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body3(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body3(M,G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body3" "ifrangeF_body3_rel"
relationalize "ifrangeF_body3_rel" "is_ifrangeF_body3"

synthesize "is_ifrangeF_body3" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body3_fm"

lemma (in M_Z_trans) separation_is_ifrangeF_body3:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body3(##M,A,G,r,s))"
  using separation_in_ctm[where \<phi>="is_ifrangeF_body3_fm(1,2,3,4,0)" and env="[A,G,r,s]"]
    zero_in_M arity_is_ifrangeF_body3_fm ord_simp_union is_ifrangeF_body3_fm_type
  by simp

lemma (in M_basic) is_ifrFb_body3_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body3(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  unfolding ifrangeF_body3_def is_ifrangeF_body3_def is_ifrFb_body3_def If_abs
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF1_trans) ifrangeF_body3_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body3(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body3(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body3(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body3(##M, G, r, s, z, i))" for z
      using is_ifrFb_body3_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body3(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body3(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body3(##M, G, r, s, z, i))" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body3(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body3(##M,G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close>
      show "is_ifrFb_body3(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body3(##M, G, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body3_def is_ifrFb_body3_def
        by (cases "y\<in>M"; cases "y\<in>range(s)"; cases "converse(s)`y \<in> M";
            auto dest:transM split del: split_if del:iffI)
          (auto simp flip:setclass_iff; (force simp only:setclass_iff))+
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body3(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body3(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body3(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body3(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body3(##M, G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body3_def is_ifrangeF_body3_def
    by (auto dest:transM)
qed

lemma (in M_ZF1_trans) separation_ifrangeF_body3:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation
        (##M,
         \<lambda>y. \<exists>x\<in>A.
                y =
                \<langle>x, \<mu> i. x \<in>
                         if_range_F_else_F(\<lambda>a. if (##M)(a) then G-``{a} else 0, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body3 ifrangeF_body3_abs
    separation_cong[where P="is_ifrangeF_body3(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body3_def if_range_F_def if_range_F_else_F_def ifrFb_body3_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow> (##M)(A') \<Longrightarrow>
    separation(##M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F((`)(A), b, f, i)\<rangle>) *)

definition ifrFb_body4 where
  "ifrFb_body4(G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then G`(converse(f) ` i) else 0 else G`i)"

relativize functional "ifrFb_body4" "ifrFb_body4_rel"
relationalize "ifrFb_body4_rel" "is_ifrFb_body4"

synthesize "is_ifrFb_body4" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body4_fm"

definition ifrangeF_body4 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body4(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body4(G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body4" "ifrangeF_body4_rel"
relationalize "ifrangeF_body4_rel" "is_ifrangeF_body4"

synthesize "is_ifrangeF_body4" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body4_fm"

lemma (in M_Z_trans) separation_is_ifrangeF_body4:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body4(##M,A,G,r,s))"
  using separation_in_ctm[where \<phi>="is_ifrangeF_body4_fm(1,2,3,4,0)" and env="[A,G,r,s]"]
    zero_in_M arity_is_ifrangeF_body4_fm ord_simp_union is_ifrangeF_body4_fm_type
  by simp

lemma (in M_basic) is_ifrFb_body4_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body4(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body4_def is_ifrangeF_body4_def is_ifrFb_body4_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF1_trans) ifrangeF_body4_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body4(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body4(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body4(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body4(##M, G, r, s, z, i))" for z
      using is_ifrFb_body4_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body4(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body4(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body4(G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body4(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body4(G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      show "is_ifrFb_body4(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body4(G, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body4_def is_ifrFb_body4_def
        apply (cases "y\<in>M"; cases "y\<in>range(s)"; cases "r=0"; cases "y\<in>domain(G)";
            auto dest:transM split del: split_if del:iffI)
        by (auto simp flip:setclass_iff; (force simp only: fun_apply_def setclass_iff))
          (auto simp flip:setclass_iff simp: fun_apply_def )
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body4(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body4(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body4(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body4(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body4(G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body4_def is_ifrangeF_body4_def
    by (auto dest:transM)
qed

lemma (in M_ZF1_trans) separation_ifrangeF_body4:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F((`)(G), b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body4 ifrangeF_body4_abs
    separation_cong[where P="is_ifrangeF_body4(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body4_def if_range_F_def if_range_F_else_F_def ifrFb_body4_def
  by simp

(* (##M)(G) \<Longrightarrow> (##M)(A) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. {xa \<in> G . x \<in> xa}, b, f, i)\<rangle>) *)

definition ifrFb_body5 where
  "ifrFb_body5(G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then {xa \<in> G . converse(f) ` i \<in> xa} else 0 else {xa \<in> G . i \<in> xa})"

relativize functional "ifrFb_body5" "ifrFb_body5_rel"
relationalize "ifrFb_body5_rel" "is_ifrFb_body5"

synthesize "is_ifrFb_body5" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body5_fm"

definition ifrangeF_body5 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body5(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body5(G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body5" "ifrangeF_body5_rel"
relationalize "ifrangeF_body5_rel" "is_ifrangeF_body5"

synthesize "is_ifrangeF_body5" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body5_fm"

lemma (in M_Z_trans) separation_is_ifrangeF_body5:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body5(##M,A,G,r,s))"
  using separation_in_ctm[where \<phi>="is_ifrangeF_body5_fm(1,2,3,4,0)" and env="[A,G,r,s]"]
    zero_in_M arity_is_ifrangeF_body5_fm ord_simp_union is_ifrangeF_body5_fm_type
  by simp

lemma (in M_basic) is_ifrFb_body5_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body5(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body5_def is_ifrangeF_body5_def is_ifrFb_body5_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF1_trans) ifrangeF_body5_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body5(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body5(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body5(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body5(##M, G, r, s, z, i))" for z
      using is_ifrFb_body5_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body5(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body5(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body5(G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body5(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body5(G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      show "is_ifrFb_body5(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body5(G, r, s, z, y)"
        using If_abs apply_0 separation_in_constant separation_in_rev
        unfolding ifrFb_body5_def is_ifrFb_body5_def
        apply (cases "y\<in>M"; cases "y\<in>range(s)"; cases "r=0"; cases "y\<in>domain(G)";
            auto dest:transM split del: split_if del:iffI)
              apply (auto simp flip:setclass_iff; (force simp only: fun_apply_def setclass_iff))
             apply (auto simp flip:setclass_iff simp: fun_apply_def)
        apply (auto dest:transM)
        done
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body5(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body5(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body5(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body5(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body5(G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body5_def is_ifrangeF_body5_def
    by (auto dest:transM)
qed

lemma (in M_ZF1_trans) separation_ifrangeF_body5:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. {xa \<in> G . x \<in> xa}, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body5 ifrangeF_body5_abs
    separation_cong[where P="is_ifrangeF_body5(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body5_def if_range_F_def if_range_F_else_F_def ifrFb_body5_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. {p \<in> A . domain(p) = a}, b, f, i)\<rangle>) *)

definition ifrFb_body6 where
  "ifrFb_body6(G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then {p\<in>G . domain(p) = converse(f) ` i} else 0 else {p\<in>G . domain(p) = i})"

relativize functional "ifrFb_body6" "ifrFb_body6_rel"
relationalize "ifrFb_body6_rel" "is_ifrFb_body6"

synthesize "is_ifrFb_body6" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body6_fm"

definition ifrangeF_body6 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body6(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body6(G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body6" "ifrangeF_body6_rel"
relationalize "ifrangeF_body6_rel" "is_ifrangeF_body6"

synthesize "is_ifrangeF_body6" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body6_fm"

lemma (in M_Z_trans) separation_is_ifrangeF_body6:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body6(##M,A,G,r,s))"
  using separation_in_ctm[where \<phi>="is_ifrangeF_body6_fm(1,2,3,4,0)" and env="[A,G,r,s]"]
    zero_in_M arity_is_ifrangeF_body6_fm ord_simp_union is_ifrangeF_body6_fm_type
  by simp

lemma (in M_basic) ifrFb_body6_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> ifrFb_body6(G, r, s, x, i) \<longleftrightarrow>  M(i) \<and> ifrFb_body6(G, r, s, x, i)"
  using If_abs
  unfolding ifrangeF_body6_def is_ifrangeF_body6_def ifrFb_body6_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_basic) is_ifrFb_body6_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body6(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body6_def is_ifrangeF_body6_def is_ifrFb_body6_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF2_trans) ifrangeF_body6_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body6(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body6(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body6(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body6(##M, G, r, s, z, i))" for z
      using is_ifrFb_body6_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body6(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. i\<in>M \<and> is_ifrFb_body6(##M, G, r, s, z, i))= (\<mu> i. i\<in>M \<and>  ifrFb_body6(G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body6(##M,G,r,s,z,i)" "\<lambda>i. i\<in>M \<and> ifrFb_body6(G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      show "y\<in>M \<and> is_ifrFb_body6(##M, G, r, s, z, y) \<longleftrightarrow> y\<in>M \<and> ifrFb_body6(G, r, s, z, y)"
        using If_abs apply_0 separation_in_constant transitivity[of _ G]
          separation_closed converse_closed apply_closed range_closed zero_in_M
          separation_cong[OF eq_commute,THEN iffD1,OF domain_eq_separation]
        unfolding ifrFb_body6_def is_ifrFb_body6_def
        by auto
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body6(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body6(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body6(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body6(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body6(G, r, s, z,i))" for z
      using Least_cong[OF ifrFb_body6_closed[of G r s]] assms
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body6_def is_ifrangeF_body6_def
    by (auto dest:transM)
qed

lemma (in M_ZF2_trans) separation_ifrangeF_body6:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. {p \<in> G . domain(p) = a}, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body6 ifrangeF_body6_abs
    separation_cong[where P="is_ifrangeF_body6(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body6_def if_range_F_def if_range_F_else_F_def ifrFb_body6_def
  by simp



(* (##M)(A) \<Longrightarrow> (##M)(f) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(D) \<Longrightarrow> (##M)(r') \<Longrightarrow> (##M)(A') \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(drSR_Y(r', D, A), b, f, i)\<rangle>) *)

definition ifrFb_body7 where
  "ifrFb_body7(B,D,A,b,f,x,i) \<equiv> x \<in>
    (if b = 0 then if i \<in> range(f) then
        {d \<in> D . \<exists>r\<in>A. restrict(r, B) = converse(f) ` i \<and> d = domain(r)} else 0
       else {d \<in> D . \<exists>r\<in>A. restrict(r, B) = i \<and> d = domain(r)})"

relativize functional "ifrFb_body7" "ifrFb_body7_rel"
relationalize "ifrFb_body7_rel" "is_ifrFb_body7"

synthesize "is_ifrFb_body7" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body7_fm"

definition ifrangeF_body7 :: "[i\<Rightarrow>o,i,i,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body7(M,A,B,D,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body7(B,D,G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body7" "ifrangeF_body7_rel"
relationalize "ifrangeF_body7_rel" "is_ifrangeF_body7"

synthesize "is_ifrangeF_body7" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body7_fm"

lemma (in M_Z_trans) separation_is_ifrangeF_body7:
  "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> (##M)(D) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body7(##M,A,B,D,G,r,s))"
  using separation_in_ctm[where \<phi>="is_ifrangeF_body7_fm(1,2,3,4,5,6,0)" and env="[A,B,D,G,r,s]"]
    zero_in_M arity_is_ifrangeF_body7_fm ord_simp_union is_ifrangeF_body7_fm_type
  by simp

lemma (in M_basic) ifrFb_body7_closed: "M(B) \<Longrightarrow> M(D) \<Longrightarrow> M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow>
  ifrFb_body7(B,D,G, r, s, x, i) \<longleftrightarrow>  M(i) \<and> ifrFb_body7(B,D,G, r, s, x, i)"
  using If_abs
  unfolding ifrangeF_body7_def is_ifrangeF_body7_def ifrFb_body7_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_basic) is_ifrFb_body7_closed: "M(B) \<Longrightarrow> M(D) \<Longrightarrow> M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow>
  is_ifrFb_body7(M, B,D,G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body7_def is_ifrangeF_body7_def is_ifrFb_body7_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF2_trans) ifrangeF_body7_abs:
  assumes "(##M)(A)"  "(##M)(B)" "(##M)(D)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body7(##M,A,B,D,G,r,s,x) \<longleftrightarrow> ifrangeF_body7(##M,A,B,D,G,r,s,x)"
proof -
  from assms
  have sep_dr: "y\<in>M \<Longrightarrow> separation(##M, \<lambda>d . \<exists>r\<in>M . r\<in>G\<and> y = restrict(r, B) \<and> d = domain(r))" for y
    by(rule_tac separation_cong[where P'="\<lambda>d . \<exists>r\<in> M . r\<in>G \<and> y = restrict(r, B) \<and> d = domain(r)",THEN iffD1,OF _
          separation_restrict_eq_dom_eq[rule_format,of G B y]],auto simp:transitivity[of _ G])

  from assms
  have sep_dr'': "y\<in>M \<Longrightarrow> separation(##M, \<lambda>d . \<exists>r\<in>M. r \<in> G \<and> d = domain(r) \<and> converse(s) ` y = restrict(r, B))" for y
    apply(rule_tac separation_cong[where P'="\<lambda>d . \<exists>r\<in> M . r\<in>G \<and> d = domain(r) \<and> converse(s) ` y = restrict(r, B)",THEN iffD1,OF _ separation_restrict_eq_dom_eq[rule_format,of G B "converse(s) ` y "]])
    by(auto simp:transitivity[of _ G] apply_closed[simplified] converse_closed[simplified])
  from assms
  have sep_dr':"separation(##M, \<lambda>x. \<exists>r\<in>M. r \<in> G \<and> x = domain(r) \<and> 0 = restrict(r, B))"
    apply(rule_tac separation_cong[where P'="\<lambda>d . \<exists>r\<in> M . r\<in>G \<and> d = domain(r) \<and> 0 = restrict(r, B)",THEN iffD1,OF _ separation_restrict_eq_dom_eq[rule_format,of G B 0]])
    by(auto simp:transitivity[of _ G] zero_in_M)
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body7(##M, B,D,G, r, s, z, i))= (\<mu> i. is_ifrFb_body7(##M,B,D, G, r, s, z, i))" for z
      using is_ifrFb_body7_closed[of B D G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body7(##M,B,D,G,r,s,z,i)"]) auto
    moreover from this
    have "(\<mu> i. i\<in>M \<and> is_ifrFb_body7(##M, B,D,G, r, s, z, i))= (\<mu> i. i\<in>M \<and>  ifrFb_body7(B,D,G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body7(##M,B,D,G,r,s,z,i)" "\<lambda>i. i\<in>M \<and> ifrFb_body7(B,D,G,r,s,z,i)"])
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      have "is_ifrFb_body7(##M, B,D,G, r, s, z, y) \<longleftrightarrow> ifrFb_body7(B,D,G, r, s, z, y)" if "y\<in>M" for y
        using If_abs apply_0
          separation_closed converse_closed apply_closed range_closed zero_in_M
          separation_restrict_eq_dom_eq
          transitivity[of _ D] transitivity[of _ G]  that sep_dr sep_dr' sep_dr''
        unfolding ifrFb_body7_def is_ifrFb_body7_def
        by auto
      then
      show " y \<in> M \<and> is_ifrFb_body7(##M, B, D, G, r, s, z, y) \<longleftrightarrow> y \<in> M \<and> ifrFb_body7(B, D, G, r, s, z, y)" for y
        using conj_cong
        by simp
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body7(##M, B,D,G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body7(##M,B,D,G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body7(##M,B,D,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body7(##M,B,D,G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body7(B,D,G, r, s, z,i))" for z
      using Least_cong[OF ifrFb_body7_closed[of B D G r s]] assms
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body7_def is_ifrangeF_body7_def
    by (auto dest:transM)
qed

lemma (in M_ZF2_trans) separation_ifrangeF_body7:
  "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> (##M)(D) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(drSR_Y(B, D, G), b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body7 ifrangeF_body7_abs drSR_Y_equality
    separation_cong[where P="is_ifrangeF_body7(##M,A,B,D,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body7_def if_range_F_def if_range_F_else_F_def ifrFb_body7_def
  by simp

end