section\<open>More Instances of Replacement\<close>

theory Replacement_Instances
  imports
    Separation_Instances
    Transitive_Models.Pointed_DC_Relative
begin

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
                   (\<exists>g[N].
                       (\<forall>u[N].
                           u \<in> g \<longleftrightarrow>
                           (\<exists>a[N].
                               \<exists>y[N].
                                  \<exists>ax[N].
                                     \<exists>sx[N].
                                        \<exists>r_sx[N].
                                           \<exists>f_r_sx[N].
                                              pair(N, a, y, u) \<and>
                                              pair(N, a, x, ax) \<and>
                                              upair(N, a, a, sx) \<and>
                                              pre_image(N, mesa, sx, r_sx) \<and>
      restriction(N, g, r_sx, f_r_sx) \<and> ax \<in> mesa \<and> is_HAleph(N, a, f_r_sx, y))) \<and>
                       is_HAleph(N, x, g, y))"

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
  using fst_rel_abs snd_rel_abs fst_abs snd_abs assms
  by simp

synthesize "is_fst2_snd2" from_definition assuming "nonempty"
arity_theorem for "is_fst2_snd2_fm"

definition sndfst_fst2_snd2
  where "sndfst_fst2_snd2(x) \<equiv> \<langle>snd(fst(x)), fst(fst(x)), snd(snd(x))\<rangle>"

relativize functional "sndfst_fst2_snd2" "sndfst_fst2_snd2_rel"
relationalize "sndfst_fst2_snd2_rel" "is_sndfst_fst2_snd2"
synthesize "is_sndfst_fst2_snd2" from_definition assuming "nonempty"
arity_theorem for "is_sndfst_fst2_snd2_fm"

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


synthesize "is_trans_apply_image_body" from_definition assuming "nonempty"
arity_theorem for "is_trans_apply_image_body_fm"

definition replacement_is_omega_funspace_fm where "replacement_is_omega_funspace_fm \<equiv>  omega_funspace_fm(2,0,1)"
definition wfrec_Aleph_fm where "wfrec_Aleph_fm \<equiv>  HAleph_wfrec_repl_body_fm(2,0,1)"
definition replacement_is_fst2_snd2_fm where "replacement_is_fst2_snd2_fm \<equiv>  is_fst2_snd2_fm(0,1)"
definition replacement_is_sndfst_fst2_snd2_fm where "replacement_is_sndfst_fst2_snd2_fm \<equiv>  is_sndfst_fst2_snd2_fm(0,1)"
definition omap_replacement_fm where "omap_replacement_fm \<equiv>  order_eq_map_fm(2,3,0,1)"
definition rec_constr_abs_fm where "rec_constr_abs_fm \<equiv>  transrec_apply_image_body_fm(3,2,0,1)"
definition banach_replacement_iterates_fm where "banach_replacement_iterates_fm \<equiv> banach_is_iterates_body_fm(6,5,4,3,2,0,1)"
definition rec_constr_fm where "rec_constr_fm \<equiv> is_trans_apply_image_body_fm(3,2,0,1)"
(* definition banach_iterates_fm where "banach_iterates_fm \<equiv> banach_body_iterates_fm(7,6,5,4,3,2,0,1)" *)
definition dc_abs_fm where "dc_abs_fm \<equiv> dcwit_repl_body_fm(6,5,4,3,2,0,1)"
definition lam_replacement_check_fm where "lam_replacement_check_fm \<equiv> Lambda_in_M_fm(check_fm(2,0,1),1)"

text\<open>The following instances are needed only on the ground model. The
first one corresponds to the recursive definition of forces for atomic
formulas; the next two corresponds to \<^term>\<open>PHcheck\<close>; the following
is used to get a generic filter using some form of choice.\<close>

locale M_ZF_ground = M_ZF1 +
  assumes
    ZF_ground_replacements:
    "replacement_assm(M,env,wfrec_Hfrc_at_fm)"
    "replacement_assm(M,env,wfrec_Hcheck_fm)"
    "replacement_assm(M,env,lam_replacement_check_fm)"

locale M_ZF_ground_trans = M_ZF1_trans + M_ZF_ground

definition instances_ground_fms where "instances_ground_fms \<equiv>
  { wfrec_Hfrc_at_fm,
    wfrec_Hcheck_fm,
    lam_replacement_check_fm }"

lemmas replacement_instances_ground_defs =
  wfrec_Hfrc_at_fm_def wfrec_Hcheck_fm_def lam_replacement_check_fm_def

declare (in M_ZF_ground) replacement_instances_ground_defs [simp]

lemma instances_ground_fms_type[TC]: "instances_ground_fms \<subseteq> formula"
  using Lambda_in_M_fm_type
  unfolding instances_ground_fms_def replacement_instances_ground_defs
  by simp

locale M_ZF_ground_notCH = M_ZF_ground +
  assumes
    ZF_ground_notCH_replacements:
    "replacement_assm(M,env,rec_constr_abs_fm)"
    "replacement_assm(M,env,rec_constr_fm)"

definition instances_ground_notCH_fms where "instances_ground_notCH_fms \<equiv>
  { rec_constr_abs_fm,
    rec_constr_fm }"

lemma instances_ground_notCH_fms_type[TC]: "instances_ground_notCH_fms \<subseteq> formula"
  unfolding instances_ground_notCH_fms_def rec_constr_abs_fm_def
    rec_constr_fm_def
  by simp

declare (in M_ZF_ground_notCH) rec_constr_abs_fm_def[simp]
  rec_constr_fm_def[simp]

locale M_ZF_ground_notCH_trans = M_ZF_ground_trans + M_ZF_ground_notCH

locale M_ZF_ground_CH = M_ZF_ground_notCH +
  assumes
    dcwit_replacement: "replacement_assm(M,env,dc_abs_fm)"

declare (in M_ZF_ground_CH) dc_abs_fm_def [simp]

locale M_ZF_ground_CH_trans = M_ZF_ground_notCH_trans + M_ZF_ground_CH

locale M_ctm1 = M_ZF1_trans + M_ZF_ground_trans +
  fixes enum
  assumes M_countable:      "enum\<in>bij(nat,M)"

locale M_ctm1_AC = M_ctm1 + M_ZFC1_trans

context M_ZF_ground_CH_trans
begin

lemma replacement_dcwit_repl_body:
  "(##M)(mesa) \<Longrightarrow> (##M)(A) \<Longrightarrow> (##M)(a) \<Longrightarrow> (##M)(s) \<Longrightarrow> (##M)(R) \<Longrightarrow>
   strong_replacement(##M, dcwit_repl_body(##M,mesa,A,a,s,R))"
  using strong_replacement_rel_in_ctm[where \<phi>="dcwit_repl_body_fm(6,5,4,3,2,0,1)"
      and env="[R,s,a,A,mesa]" and f="dcwit_repl_body(##M,mesa,A,a,s,R)"]
    zero_in_M arity_dcwit_repl_body dcwit_replacement
  unfolding dc_abs_fm_def
  by simp

lemma dcwit_repl:
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

end \<comment> \<open>\<^locale>\<open>M_ZF_ground_CH_trans\<close>\<close>

context M_ZF1_trans
begin

lemmas M_replacement_ZF_instances = lam_replacement_fst lam_replacement_snd
  lam_replacement_Union lam_replacement_Image
  lam_replacement_middle_del lam_replacement_prodRepl

lemmas M_separation_ZF_instances = separation_fstsnd_in_sndsnd separation_sndfst_eq_fstsnd

lemma separation_is_dcwit_body:
  assumes "(##M)(A)" "(##M)(a)" "(##M)(g)" "(##M)(R)"
  shows "separation(##M,is_dcwit_body(##M, A, a, g, R))"
  using assms separation_in_ctm[where env="[A,a,g,R]" and \<phi>="is_dcwit_body_fm(1,2,3,4,0)",
      OF _ _ _ is_dcwit_body_iff_sats[symmetric],
      of "\<lambda>_.A" "\<lambda>_.a" "\<lambda>_.g" "\<lambda>_.R" "\<lambda>x. x"]
    nonempty arity_is_dcwit_body_fm is_dcwit_body_fm_type
  by (simp add:ord_simp_union)

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

sublocale M_ZF1_trans \<subseteq> M_replacement "##M"
  using M_replacement_ZF_instances M_separation_ZF_instances
  by unfold_locales simp

context M_ZF1_trans
begin

lemma separation_Pow_rel: "A\<in>M \<Longrightarrow>
    separation(##M, \<lambda>y. \<exists>x \<in> M . x\<in>A \<and> y = \<langle>x, Pow\<^bsup>##M\<^esup>(x)\<rangle>)"
  using separation_assm_sats[of "is_Pow_fm(0,1)"] arity_is_Pow_fm ord_simp_union
    Pow_rel_closed nonempty Pow_rel_iff
  by simp

lemma strong_replacement_Powapply_rel:
  "f\<in>M \<Longrightarrow> strong_replacement(##M, \<lambda>x y. y = Powapply\<^bsup>##M\<^esup>(f,x))"
  using Powapply_rel_replacement separation_Pow_rel transM
  by simp

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

sublocale M_ZF1_trans \<subseteq> M_Vfrom "##M"
  using power_ax strong_replacement_Powapply_rel phrank_repl trans_repl_HVFrom wfrec_rank
  by unfold_locales auto

sublocale M_ZF1_trans \<subseteq> M_Perm "##M"
  using separation_PiP_rel separation_injP_rel separation_surjP_rel
    lam_replacement_imp_strong_replacement[OF
      lam_replacement_Sigfun[OF lam_replacement_constant]]
    Pi_replacement1 unfolding Sigfun_def
  by unfold_locales simp_all

sublocale M_ZF1_trans \<subseteq> M_pre_seqspace "##M"
  by unfold_locales

context M_ZF1_trans
begin

lemma separation_inj_rel: "A\<in>M \<Longrightarrow>
     separation(##M, \<lambda>y. \<exists>x\<in>M. x \<in> A \<and> y = \<langle>x, inj_rel(##M,fst(x), snd(x))\<rangle>)"
  using arity_is_inj_fm ord_simp_union
    nonempty inj_rel_closed[simplified] inj_rel_iff[simplified]
  by (rule_tac separation_assm_bin_sats[of "is_inj_fm(0,1,2)"])
    (simp_all add:setclass_def)

lemma lam_replacement_inj_rel: "lam_replacement(##M, \<lambda>x . inj_rel(##M,fst(x),snd(x)))"
  using lam_replacement_inj_rel' separation_inj_rel
  by simp

(*

These lemmas were required for the original proof of Schröder-Bernstein.

lemma banach_iterates:
  assumes "X\<in>M" "Y\<in>M" "f\<in>M" "g\<in>M" "W\<in>M"
  shows "iterates_replacement(##M, is_banach_functor(##M,X,Y,f,g), W)"
proof -
  have "strong_replacement(##M, \<lambda> x z . banach_body_iterates(##M,X,Y,f,g,W,n,x,z))" if "n\<in>\<omega>" for n
    using assms that arity_banach_body_iterates_fm ord_simp_union nat_into_M
      strong_replacement_rel_in_ctm[where \<phi>="banach_body_iterates_fm(7,6,5,4,3,2,0,1)"
        and env="[n,W,g,f,Y,X]"] replacement_ax2(3)
    by simp
  then
  show ?thesis
    using assms nat_into_M Memrel_closed
    unfolding iterates_replacement_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
      is_nat_case_def iterates_MH_def banach_body_iterates_def
    by simp
qed

lemma separation_banach_functor_iterates:
  assumes "X\<in>M" "Y\<in>M" "f\<in>M" "g\<in>M" "A\<in>M"
  shows "separation(##M, \<lambda>b. \<exists>x\<in>A. x \<in> \<omega> \<and> b = banach_functor(X, Y, f, g)^x (0))"
proof -
  have " (\<exists>xa\<in>M. xa \<in> A \<and> xa \<in> \<omega> \<and> banach_is_iterates_body(##M, X, Y, f, g, 0, xa, x)) \<longleftrightarrow>
         (\<exists>n\<in>A. n \<in> \<omega> \<and> banach_is_iterates_body(##M, X, Y, f, g, 0, n, x))" if "x\<in>M" for x
    using assms nat_into_M nat_in_M transM[of _ A] transM[of _ \<omega>] that
    by auto
  then
  have "separation(##M, \<lambda> z . \<exists>n\<in>A . n\<in>\<omega> \<and> banach_is_iterates_body(##M,X,Y,f,g,0,n,z))"
    using assms nat_into_M nat_in_M
      arity_banach_is_iterates_body_fm[of 6 5 4 3 2 0 1] ord_simp_union
      separation_in_ctm[where \<phi>="(\<cdot>\<exists> \<cdot>\<cdot>0\<in>7\<cdot> \<and> \<cdot>\<cdot>0\<in>8\<cdot> \<and> banach_is_iterates_body_fm(6,5,4,3,2,0,1) \<cdot>\<cdot>\<cdot>)"
        and env="[0,g,f,Y,X,A,\<omega>]"]
    by (simp add:arity_Exists arity_And)
  moreover from assms
  have "(\<exists>x\<in>A. x \<in> \<omega> \<and> is_iterates(##M,is_banach_functor(##M,X, Y, f, g),0,x,z)) \<longleftrightarrow>
          (\<exists>n\<in>A . n\<in>\<omega> \<and> banach_is_iterates_body(##M,X,Y,f,g,0,n,z))" if "z\<in>M" for z
    using nat_in_M nat_into_M transM[of _ A] transM[of _ \<omega>]
    unfolding is_iterates_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
      is_nat_case_def iterates_MH_def banach_body_iterates_def banach_is_iterates_body_def
    by simp
  moreover from assms
  have "(\<exists>x\<in>A. x \<in> \<omega> \<and> is_iterates(##M,is_banach_functor(##M,X, Y, f, g),0,x,z)) \<longleftrightarrow>
          (\<exists>x\<in>A. x \<in> \<omega> \<and> z = banach_functor(X, Y, f, g)^x (0))" if "z\<in>M" for z
    using transM[of _ A] nat_in_M nat_into_M that
      iterates_abs[OF banach_iterates banach_functor_abs] banach_functor_closed
    by auto
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2],auto)
qed

lemma banach_replacement:
  assumes "X\<in>M" "Y\<in>M" "f\<in>M" "g\<in>M"
  shows "strong_replacement(##M, \<lambda>n y. n\<in>nat \<and> y = banach_functor(X, Y, f, g)^n (0))"
  using assms banach_repl_iter' separation_banach_functor_iterates
  by simp

*)

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

lemma (in M_basic) rel2_trans_apply:
  "M(f) \<Longrightarrow> relation2(M,is_trans_apply_image(M,f),trans_apply_image(f))"
  unfolding is_trans_apply_image_def trans_apply_image_def relation2_def
  by auto

lemma (in M_basic) apply_image_closed:
  shows "M(f) \<Longrightarrow> \<forall>x[M]. \<forall>g[M]. M(trans_apply_image(f, x, g))"
  unfolding trans_apply_image_def by simp

context M_ZF_ground_notCH_trans
begin

lemma replacement_transrec_apply_image_body :
  "(##M)(f) \<Longrightarrow> (##M)(mesa) \<Longrightarrow> strong_replacement(##M,transrec_apply_image_body(##M,f,mesa))"
  using strong_replacement_rel_in_ctm[where \<phi>="transrec_apply_image_body_fm(3,2,0,1)" and env="[mesa,f]"]
    zero_in_M arity_transrec_apply_image_body_fm ord_simp_union
    ZF_ground_notCH_replacements(1)
  by simp

lemma transrec_replacement_apply_image:
  assumes "(##M)(f)" "(##M)(\<alpha>)"
  shows "transrec_replacement(##M, is_trans_apply_image(##M, f), \<alpha>)"
  using replacement_transrec_apply_image_body[unfolded transrec_apply_image_body_def] assms
    Memrel_closed singleton_closed eclose_closed
  unfolding transrec_replacement_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
  by simp

lemma rec_trans_apply_image_abs:
  assumes "(##M)(f)" "(##M)(x)" "(##M)(y)" "Ord(x)"
  shows "is_transrec(##M,is_trans_apply_image(##M, f),x,y) \<longleftrightarrow> y = transrec(x,trans_apply_image(f))"
  using transrec_abs[OF transrec_replacement_apply_image rel2_trans_apply] assms apply_image_closed
  by simp

lemma replacement_is_trans_apply_image:
  "(##M)(f) \<Longrightarrow> (##M)(\<beta>) \<Longrightarrow> strong_replacement(##M, \<lambda> x z .
    \<exists>y[##M]. pair(##M,x,y,z) \<and> x\<in>\<beta> \<and> (is_transrec(##M,is_trans_apply_image(##M, f),x,y)))"
  unfolding is_transrec_def is_wfrec_def M_is_recfun_def
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x z. M,[x,z,\<beta>,f] \<Turnstile> is_trans_apply_image_body_fm(3,2,0,1)",THEN iffD1])
   apply(rule_tac is_trans_apply_image_body_iff_sats[symmetric,unfolded is_trans_apply_image_body_def,where env="[_,_,\<beta>,f]"])
            apply(simp_all add:zero_in_M)
  apply(rule_tac ZF_ground_notCH_replacements(2)[unfolded replacement_assm_def, rule_format, where env="[\<beta>,f]",simplified])
    apply(simp_all add: arity_is_trans_apply_image_body_fm is_trans_apply_image_body_fm_type ord_simp_union)
  done

lemma trans_apply_abs:
  "(##M)(f) \<Longrightarrow> (##M)(\<beta>) \<Longrightarrow> Ord(\<beta>) \<Longrightarrow> (##M)(x) \<Longrightarrow> (##M)(z) \<Longrightarrow>
    (x\<in>\<beta> \<and> z = \<langle>x, transrec(x, \<lambda>a g. f ` (g `` a)) \<rangle>) \<longleftrightarrow>
    (\<exists>y[##M]. pair(##M,x,y,z) \<and> x\<in>\<beta> \<and> (is_transrec(##M,is_trans_apply_image(##M, f),x,y)))"
  using rec_trans_apply_image_abs Ord_in_Ord
    transrec_closed[OF transrec_replacement_apply_image rel2_trans_apply,of f,simplified]
    apply_image_closed
  unfolding trans_apply_image_def
  by auto

lemma replacement_trans_apply_image:
  "(##M)(f) \<Longrightarrow> (##M)(\<beta>) \<Longrightarrow> Ord(\<beta>) \<Longrightarrow>
  strong_replacement(##M, \<lambda>x y. x\<in>\<beta> \<and> y = \<langle>x, transrec(x, \<lambda>a g. f ` (g `` a))\<rangle>)"
  using strong_replacement_cong[THEN iffD1,OF _ replacement_is_trans_apply_image,simplified]
    trans_apply_abs Ord_in_Ord
  by simp

end \<comment> \<open>\<^locale>\<open>M_ZF_ground_notCH_trans\<close>\<close>

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

lemma (in M_ZF1_trans) ifrangeF_body6_abs:
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

lemma (in M_ZF1_trans) separation_ifrangeF_body6:
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

lemma (in M_ZF1_trans) ifrangeF_body7_abs:
  assumes "(##M)(A)"  "(##M)(B)" "(##M)(D)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body7(##M,A,B,D,G,r,s,x) \<longleftrightarrow> ifrangeF_body7(##M,A,B,D,G,r,s,x)"
proof -
  from assms
  have sep_dr: "y\<in>M \<Longrightarrow> separation(##M, \<lambda>d . \<exists>r\<in>M . r\<in>G \<and> y = restrict(r, B) \<and> d = domain(r))" for y
    by(rule_tac separation_cong[where P'="\<lambda>d . \<exists>r\<in> M . r\<in>G \<and> y = restrict(r, B) \<and> d = domain(r)",THEN iffD1,OF _
          separation_restrict_eq_dom_eq[rule_format,of G B y]],auto simp:transitivity[of _ G])
  from assms
  have sep_dr'': "y\<in>M \<Longrightarrow> separation(##M, \<lambda>d . \<exists>r\<in>M. r \<in> G \<and> d = domain(r) \<and> converse(s) ` y = restrict(r, B))" for y
    by(rule_tac separation_cong[THEN iffD1,OF _ separation_restrict_eq_dom_eq[rule_format,of G B "converse(s) ` y "]],
        auto simp:transitivity[of _ G] apply_closed[simplified] converse_closed[simplified])
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
          transitivity[of _ D] transitivity[of _ G] that sep_dr sep_dr''
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

lemma (in M_ZF1_trans) separation_ifrangeF_body7:
  "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> (##M)(D) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(drSR_Y(B, D, G), b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body7 ifrangeF_body7_abs drSR_Y_equality
    separation_cong[where P="is_ifrangeF_body7(##M,A,B,D,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body7_def if_range_F_def if_range_F_else_F_def ifrFb_body7_def
  by simp

definition omfunspace :: "[i,i] \<Rightarrow> o" where
  "omfunspace(B) \<equiv> \<lambda>z. \<exists>x. \<exists>n\<in>\<omega>. z\<in>x \<and> x = n\<rightarrow>B"
relativize functional "omfunspace" "omfunspace_rel"
relationalize "omfunspace_rel" "is_omfunspace"
synthesize "is_omfunspace" from_definition assuming "nonempty"
arity_theorem for "is_omfunspace_fm"

context M_pre_seqspace
begin

is_iff_rel for "omfunspace"
  using is_function_space_iff
  unfolding omfunspace_rel_def is_omfunspace_def
  by (simp add:absolut)

end \<comment> \<open>\<^locale>\<open>M_pre_seqspace\<close>\<close>

context M_ZF1_trans
begin

lemma separation_omfunspace:
  assumes "(##M)(B)"
  shows "separation(##M, \<lambda>z. \<exists>x[##M]. \<exists>n[##M]. n \<in> \<omega> \<and> z \<in> x \<and> x = n \<rightarrow>\<^bsup>M\<^esup> B)"
  using assms separation_in_ctm[where env="[B]" and \<phi>="is_omfunspace_fm(1,0)"
      and Q="is_omfunspace(##M,B)"]
    nonempty is_omfunspace_iff[of B, THEN separation_cong, of "##M"]
    arity_is_omfunspace_fm is_omfunspace_fm_type
  unfolding omfunspace_rel_def
  by (auto simp add:ord_simp_union)

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

sublocale M_ZF1_trans \<subseteq> M_seqspace "##M"
  using separation_omfunspace by unfold_locales

definition cdltgamma :: "[i,i] \<Rightarrow> o" where
  "cdltgamma(\<gamma>) \<equiv> \<lambda>Z . |Z| < \<gamma>"
relativize functional "cdltgamma" "cdltgamma_rel"
relationalize "cdltgamma_rel" "is_cdltgamma"
synthesize "is_cdltgamma" from_definition assuming "nonempty"
arity_theorem for "is_cdltgamma_fm"

definition cdeqgamma :: "[i] \<Rightarrow> o" where
  "cdeqgamma \<equiv> \<lambda>Z . |fst(Z)| = snd(Z)"
relativize functional "cdeqgamma" "cdeqgamma_rel"
relationalize "cdeqgamma_rel" "is_cdeqgamma"
synthesize "is_cdeqgamma" from_definition assuming "nonempty"
arity_theorem for "is_cdeqgamma_fm"

context M_Perm
begin

is_iff_rel for "cdltgamma"
  using is_cardinal_iff
  unfolding cdltgamma_rel_def is_cdltgamma_def
  by (simp add:absolut)

is_iff_rel for "cdeqgamma"
  using is_cardinal_iff fst_rel_abs snd_rel_abs
  unfolding cdeqgamma_rel_def is_cdeqgamma_def
  by (auto simp add:absolut)

lemma is_cdeqgamma_iff_split: "M(Z) \<Longrightarrow> cdeqgamma_rel(M, Z) \<longleftrightarrow> (\<lambda>\<langle>x,y\<rangle>. |x|\<^bsup>M\<^esup> = y)(Z)"
  using  fst_rel_abs snd_rel_abs
  unfolding cdeqgamma_rel_def split_def
  by simp

end

context M_ZF1_trans
begin

lemma separation_cdltgamma:
  assumes "(##M)(\<gamma>)"
  shows "separation(##M, \<lambda>Z . cardinal_rel(##M,Z) < \<gamma>)"
  using assms separation_in_ctm[where env="[\<gamma>]" and \<phi>="is_cdltgamma_fm(1,0)"
      and Q="cdltgamma_rel(##M,\<gamma>)"]
    nonempty is_cdltgamma_iff[of \<gamma>] arity_is_cdltgamma_fm is_cdltgamma_fm_type
  unfolding cdltgamma_rel_def
  by (auto simp add:ord_simp_union)

lemma separation_cdeqgamma:
  shows "separation(##M, \<lambda>Z. (\<lambda>\<langle>x,y\<rangle> . cardinal_rel(##M,x) = y)(Z))"
  using separation_in_ctm[where env="[]" and \<phi>="is_cdeqgamma_fm(0)"
      and Q="cdeqgamma_rel(##M)"] is_cdeqgamma_iff_split
    nonempty is_cdeqgamma_iff arity_is_cdeqgamma_fm is_cdeqgamma_fm_type
    separation_cong[OF is_cdeqgamma_iff_split, of "##M"]
  unfolding cdeqgamma_rel_def
  by (simp add:ord_simp_union)

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

end