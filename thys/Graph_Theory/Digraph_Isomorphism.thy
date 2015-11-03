theory Digraph_Isomorphism imports
  Arc_Walk
  Digraph
  Digraph_Component
begin

section {* Isomorphisms of Digraphs *}

record ('a,'b,'aa,'bb) digraph_isomorphism =
  iso_verts :: "'a \<Rightarrow> 'aa"
  iso_arcs :: "'b \<Rightarrow> 'bb"
  iso_head :: "'bb \<Rightarrow> 'aa"
  iso_tail :: "'bb \<Rightarrow> 'aa"

definition (in pre_digraph) digraph_isomorphism :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> bool" where 
  "digraph_isomorphism hom \<equiv>
    wf_digraph G \<and>
    inj_on (iso_verts hom) (verts G) \<and>
    inj_on (iso_arcs hom) (arcs G) \<and>
    (\<forall>a \<in> arcs G. 
    iso_verts hom (tail G a) = iso_tail hom (iso_arcs hom a) \<and>
    iso_verts hom (head G a) = iso_head hom (iso_arcs hom a))"

definition (in pre_digraph) inv_iso :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> ('aa,'bb,'a,'b) digraph_isomorphism" where
  "inv_iso hom \<equiv> \<lparr>
    iso_verts = the_inv_into (verts G) (iso_verts hom),
    iso_arcs = the_inv_into (arcs G) (iso_arcs hom),
    iso_head = head G,
    iso_tail = tail G
    \<rparr>"

definition app_iso
    :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> ('aa,'bb) pre_digraph" where
  "app_iso hom G \<equiv> \<lparr> verts = iso_verts hom ` verts G, arcs = iso_arcs hom ` arcs G,
    tail = iso_tail hom, head = iso_head hom \<rparr>"

lemma verts_app_iso: "verts (app_iso hom G) = iso_verts hom ` verts G"
  and arcs_app_iso: "arcs (app_iso hom G) = iso_arcs hom `arcs G"
  and tail_app_iso: "tail (app_iso hom G) = iso_tail hom"
  and head_app_iso: "head (app_iso hom G) = iso_head hom"
  by (auto simp: app_iso_def)

lemmas app_iso_simps[simp] = verts_app_iso arcs_app_iso tail_app_iso head_app_iso

context pre_digraph begin

lemma
  assumes "digraph_isomorphism hom"
  shows iso_verts_inv_iso: "\<And>u. u \<in> verts G \<Longrightarrow> iso_verts (inv_iso hom) (iso_verts hom u) = u"
    and iso_arcs_inv_iso: "\<And>a. a \<in> arcs G \<Longrightarrow> iso_arcs (inv_iso hom) (iso_arcs hom a) = a"
    and iso_verts_iso_inv: "\<And>u. u \<in> verts (app_iso hom G) \<Longrightarrow> iso_verts hom (iso_verts (inv_iso hom) u) = u"
    and iso_arcs_iso_inv: "\<And>a. a \<in> arcs (app_iso hom G) \<Longrightarrow> iso_arcs hom (iso_arcs (inv_iso hom) a) = a"
    and iso_tail_inv_iso: "iso_tail (inv_iso hom) = tail G"
    and iso_head_inv_iso: "iso_head (inv_iso hom) = head G"
    and verts_app_inv_iso:"iso_verts (inv_iso hom) ` iso_verts hom ` verts G = verts G"
    and arcs_app_inv_iso:"iso_arcs (inv_iso hom) ` iso_arcs hom ` arcs G = arcs G"
  using assms by (auto simp: inv_iso_def digraph_isomorphism_def the_inv_into_f_f)

lemmas iso_inv_simps[simp] =
   iso_verts_inv_iso iso_verts_iso_inv
   iso_arcs_inv_iso iso_arcs_iso_inv
   verts_app_inv_iso arcs_app_inv_iso
   iso_tail_inv_iso iso_head_inv_iso

lemma app_iso_inv[simp]:
  assumes "digraph_isomorphism hom"
  shows "app_iso (inv_iso hom) (app_iso hom G) = G"
  using assms by (intro pre_digraph.equality) (auto intro: rev_image_eqI)

lemma iso_verts_eq_iff[simp]:
  assumes "digraph_isomorphism hom" "u \<in> verts G" "v \<in> verts G"
  shows "iso_verts hom u = iso_verts hom v \<longleftrightarrow> u = v"
  using assms by (auto simp: digraph_isomorphism_def dest: inj_onD)

lemma iso_arcs_eq_iff[simp]:
  assumes "digraph_isomorphism hom" "e1 \<in> arcs G" "e2 \<in> arcs G"
  shows "iso_arcs hom e1 = iso_arcs hom e2 \<longleftrightarrow> e1 = e2"
  using assms by (auto simp: digraph_isomorphism_def dest: inj_onD)

lemma
  assumes "digraph_isomorphism hom" "e \<in> arcs G"
  shows iso_verts_tail: "iso_tail hom (iso_arcs hom e) = iso_verts hom (tail G e)"
    and iso_verts_head: "iso_head hom (iso_arcs hom e) = iso_verts hom (head G e)"
  using assms unfolding digraph_isomorphism_def by auto

end

lemma (in wf_digraph) wf_digraphI_app_iso[intro?]:
  assumes "digraph_isomorphism hom"
  shows "wf_digraph (app_iso hom G)"
proof unfold_locales
  fix e assume "e \<in> arcs (app_iso hom G)"
  then obtain e' where e': "e' \<in> arcs G" "iso_arcs hom e' = e"
    by auto
  then have "iso_verts hom (head G e') \<in> verts (app_iso hom G)"
      "iso_verts hom (tail G e') \<in> verts (app_iso hom G)"
    by auto
  then show "tail (app_iso hom G) e \<in> verts (app_iso hom G)"
      "head (app_iso hom G) e \<in> verts (app_iso hom G)"
    using e' assms by (auto simp: iso_verts_tail iso_verts_head)
qed

lemma (in fin_digraph) fin_digraphI_app_iso[intro?]:
  assumes "digraph_isomorphism hom"
  shows "fin_digraph (app_iso hom G)"
proof -
  interpret H: wf_digraph "app_iso hom G" using assms ..
  show ?thesis by unfold_locales auto
qed

context wf_digraph begin

lemma digraph_isomorphism_invI:
  assumes "digraph_isomorphism hom" shows "pre_digraph.digraph_isomorphism (app_iso hom G) (inv_iso hom)"
proof (unfold pre_digraph.digraph_isomorphism_def, safe)
  show "inj_on (iso_verts (inv_iso hom)) (verts (app_iso hom G))"
      "inj_on (iso_arcs (inv_iso hom)) (arcs (app_iso hom G))"
    using assms unfolding pre_digraph.digraph_isomorphism_def inv_iso_def
    by (auto intro: inj_on_the_inv_into)
next
  show "wf_digraph (app_iso hom G)" using assms ..
next
  fix a assume "a \<in> arcs (app_iso hom G)"
  then obtain b where B: "a = iso_arcs hom b" "b \<in> arcs G"
    by auto

  with assms have [simp]:
      "iso_tail hom (iso_arcs hom b) = iso_verts hom (tail G b)"
      "iso_head hom (iso_arcs hom b) = iso_verts hom (head G b)"
      "inj_on (iso_arcs hom) (arcs G)"
      "inj_on (iso_verts hom) (verts G)"
    by (auto simp: digraph_isomorphism_def)

  from B show "iso_verts (inv_iso hom) (tail (app_iso hom G) a)
      = iso_tail (inv_iso hom) (iso_arcs (inv_iso hom) a)"
    by (auto simp: inv_iso_def the_inv_into_f_f)
  from B show "iso_verts (inv_iso hom) (head (app_iso hom G) a)
      = iso_head (inv_iso hom) (iso_arcs (inv_iso hom) a)"
    by (auto simp: inv_iso_def the_inv_into_f_f)
qed


lemma awalk_app_isoI:
  assumes "awalk u p v" and hom: "digraph_isomorphism hom"
  shows "pre_digraph.awalk (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from assms show ?thesis
    by (induct p arbitrary: u)
       (auto simp: awalk_simps H.awalk_simps iso_verts_head iso_verts_tail)
qed

lemma awalk_app_isoD:
  assumes w: "pre_digraph.awalk (app_iso hom G) u p v" and hom: "digraph_isomorphism hom"
  shows "awalk (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p) (iso_verts (inv_iso hom) v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from assms show ?thesis
    by (induct p arbitrary: u)
       (force simp: awalk_simps H.awalk_simps iso_verts_head iso_verts_tail)+
qed

lemma awalk_verts_app_iso_eq:
  assumes "digraph_isomorphism hom" and "awalk u p v"
  shows "pre_digraph.awalk_verts (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p)
    = map (iso_verts hom) (awalk_verts u p)"
  using assms
  by (induct p arbitrary: u)
     (auto simp: pre_digraph.awalk_verts.simps iso_verts_head iso_verts_tail awalk_Cons_iff)

(*
lemma awalk_verts_app_iso_eq':
  assumes hom: "digraph_isomorphism hom" and w: "pre_digraph.awalk (app_iso hom G) u p v"
  shows "pre_digraph.awalk_verts (app_iso hom G) u p
    = map (iso_verts hom) (awalk_verts (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p))"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  have w': "awalk (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p) (iso_verts (inv_iso hom) v)"
    using w hom by (rule awalk_app_isoD)
  have "pre_digraph.awalk_verts (app_iso hom G) u p =
      pre_digraph.awalk_verts (app_iso hom G) (iso_verts hom (iso_verts (inv_iso hom) u)) (map (iso_arcs hom) (map (iso_arcs (inv_iso hom)) p))"
    using hom w by (auto simp add: o_def set_mp cong: map_cong)
  also have "\<dots> = map (iso_verts hom) (awalk_verts (iso_verts (inv_iso hom) u) (map (iso_arcs (inv_iso hom)) p))"
    using hom w' by (rule awalk_verts_app_iso_eq)
  finally show ?thesis .
qed
*)

lemma arcs_ends_app_iso_eq:
  assumes "digraph_isomorphism hom"
  shows "arcs_ends (app_iso hom G) = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` arcs_ends G"
  using assms by (auto simp: arcs_ends_conv image_image iso_verts_head iso_verts_tail
      intro!: rev_image_eqI)

lemma in_arcs_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "in_arcs (app_iso hom G) (iso_verts hom u) = iso_arcs hom ` in_arcs G u"
  using assms unfolding in_arcs_def by (auto simp: iso_verts_head)

lemma out_arcs_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "out_arcs (app_iso hom G) (iso_verts hom u) = iso_arcs hom ` out_arcs G u"
  using assms unfolding out_arcs_def by (auto simp: iso_verts_tail)

lemma in_degree_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "in_degree (app_iso hom G) (iso_verts hom u) = in_degree G u"
  unfolding in_degree_def in_arcs_app_iso_eq[OF assms]
proof (rule card_image)
  from assms show "inj_on (iso_arcs hom) (in_arcs G u)"
    unfolding digraph_isomorphism_def by - (rule subset_inj_on, auto)
qed

lemma out_degree_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "out_degree (app_iso hom G) (iso_verts hom u) = out_degree G u"
  unfolding out_degree_def out_arcs_app_iso_eq[OF assms]
proof (rule card_image)
  from assms show "inj_on (iso_arcs hom) (out_arcs G u)"
    unfolding digraph_isomorphism_def by - (rule subset_inj_on, auto)
qed

lemma in_arcs_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "in_arcs (app_iso hom G) u = iso_arcs hom ` in_arcs G (iso_verts (inv_iso hom) u)"
  using assms in_arcs_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemma out_arcs_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "out_arcs (app_iso hom G) u = iso_arcs hom ` out_arcs G (iso_verts (inv_iso hom) u)"
  using assms out_arcs_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemma in_degree_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "in_degree (app_iso hom G) u = in_degree G (iso_verts (inv_iso hom) u)"
  using assms in_degree_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemma out_degree_app_iso_eq':
  assumes "digraph_isomorphism hom" and "u \<in> verts (app_iso hom G)"
  shows "out_degree (app_iso hom G) u = out_degree G (iso_verts (inv_iso hom) u)"
  using assms out_degree_app_iso_eq[of hom "iso_verts (inv_iso hom) u"] by auto

lemmas app_iso_eq =
  awalk_verts_app_iso_eq
  arcs_ends_app_iso_eq
  in_arcs_app_iso_eq'
  out_arcs_app_iso_eq'
  in_degree_app_iso_eq'
  out_degree_app_iso_eq'

lemma reachableI_app_iso:
  assumes r: "u \<rightarrow>\<^sup>* v" and hom: "digraph_isomorphism hom"
  shows "(iso_verts hom u) \<rightarrow>\<^sup>*\<^bsub>app_iso hom G\<^esub> (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from r obtain p where "awalk u p v" by (auto simp: reachable_awalk)
  then have "H.awalk (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
    using hom by (rule awalk_app_isoI)
  then show ?thesis by (auto simp: H.reachable_awalk)
qed

lemma connectedI_app_iso:
  assumes c: "connected G" and hom: "digraph_isomorphism hom"
  shows "connected (app_iso hom G)"
proof -
  have *: "symcl (arcs_ends (app_iso hom G)) = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` symcl (arcs_ends G)"
    using hom by (auto simp add: app_iso_eq symcl_def)
  { fix u v assume "(u,v) \<in> rtrancl_on (verts G) (symcl (arcs_ends G))"
    then have "(iso_verts hom u, iso_verts hom v) \<in> rtrancl_on (verts (app_iso hom G)) (symcl (arcs_ends (app_iso hom G)))"
    proof induct
      case (step x y)
      have "(iso_verts hom x, iso_verts hom y)
          \<in> rtrancl_on (verts (app_iso hom G)) (symcl (arcs_ends (app_iso hom G)))"
        using step by (rule_tac rtrancl_on_into_rtrancl_on[where b="iso_verts hom x"]) (auto simp: *)
      then show ?case
        by (rule rtrancl_on_trans) (rule step)
    qed auto }
  with c show ?thesis unfolding connected_conv by auto
qed

end



end
