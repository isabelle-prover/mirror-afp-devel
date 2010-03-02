(*  Author:     Tobias Nipkow
*)

header{* All About Finalizing Triangles *}

theory Plane3Props
imports Plane1Props Generator TameProps
begin


subsection{* Correctness *}


lemma decomp_nonFinal3:
assumes mgp: "minGraphProps g"
and ffs: "f#fs = [f \<leftarrow> faces g. \<not> final f \<and> triangle f]"
shows "f = minimalFace(nonFinals g) &
       fs = [f \<leftarrow> faces(makeFaceFinal (minimalFace(nonFinals g)) g).
             \<not> final f \<and> triangle f]" (is "?A & ?B")
proof -
  have 3: "\<forall>f \<in> \<F> g. 3 \<le> |vertices f|"
    using minGraphProps2[OF mgp] by fastsimp
  have ffs': "f#fs = [f \<leftarrow> nonFinals g. triangle f]" using ffs
    by (simp add:nonFinals_def)
  from Cons_eq_filterD[OF ffs'] obtain us vs where
    [simp]: "nonFinals g = us @ f # vs" "triangle f"
      "fs = [f\<leftarrow>vs . triangle f]" and us: "\<forall>u\<in>set us. \<not> triangle u"
    by blast
  have "\<forall>u \<in> set(nonFinals g). u \<in> \<F> g" by(simp add:nonFinals_def)
  hence usg: "\<forall>u\<in>set us. u \<in> \<F> g"
    and vsg: "\<forall>u\<in>set vs. u \<in> \<F> g" by simp+
  let ?m = "size o vertices"
  have us3: "\<forall>u\<in>set us. |vertices u| > 3"
  proof
    fix f' assume "f' \<in> set us"
    thus "|vertices f'| > 3"
      using bspec[OF us, of f'] bspec[OF 3, of f'] bspec[OF usg, of f']
      by simp
  qed
  have A: ?A
  proof -
    have "minimal ?m (us @ f # vs) = minimal ?m (f # vs)"
      using us3 by(simp add: minimal_append2)
    also have "\<dots> = f" using 3 vsg
      by (rule_tac minimal_Cons1) simp
    finally show ?A by(simp add: minimalFace_def)
  qed
  moreover have ?B (is "?l = ?r")
  proof -
    have "?r = [h \<leftarrow> faces (makeFaceFinal f g) . \<not> final h \<and> triangle h]"
      using A by simp
    also have "\<dots> = [h \<leftarrow> nonFinals (makeFaceFinal f g). triangle h]"
      by(simp add:nonFinals_def)
    also have "\<dots> = [h \<leftarrow> remove1 f (nonFinals g). triangle h]"
      by(simp add:nonFins_mkFaceFin)
    also have "\<dots> = [h \<leftarrow> vs. triangle h]"
    proof -
      have "f \<notin> set us" using us by auto
      thus ?thesis using us by(simp add:remove1_append)
    qed
    finally show ?B by simp
  qed
  ultimately show ?thesis ..
qed


lemma noDupEdge3:
 "\<lbrakk> minGraphProps g; f \<in> \<F> g; triangle f; v \<in> \<V> f \<rbrakk>
 \<Longrightarrow> \<not> containsDuplicateEdge g f v [0..<3]"
apply(frule (1) minGraphProps3)
apply(drule length3D)
apply auto
apply(simp add: containsDuplicateEdge_eq containsDuplicateEdge'_def
                nat_number nextVertices_def nextVertex_def
        duplicateEdge_is_duplicateEdge_eq is_duplicateEdge_def is_nextElem_def)
apply(simp add:is_sublist_rec[where 'a = nat])
apply(simp add: containsDuplicateEdge_eq containsDuplicateEdge'_def
                nat_number nextVertices_def nextVertex_def
        duplicateEdge_is_duplicateEdge_eq is_duplicateEdge_def is_nextElem_def)
apply(simp add: containsDuplicateEdge_eq containsDuplicateEdge'_def
                nat_number nextVertices_def nextVertex_def
        duplicateEdge_is_duplicateEdge_eq is_duplicateEdge_def is_nextElem_def)
apply(simp add:is_sublist_rec[where 'a = nat])
done

lemma indexToVs3:
 "\<lbrakk> triangle f; distinct(vertices f); v \<in> \<V> f \<rbrakk>
 \<Longrightarrow> indexToVertexList f v [0..<3] = [Some v, Some(f \<bullet> v), Some(f \<bullet> (f \<bullet> v))]"
apply(auto dest!: length3D)
apply(auto simp:indexToVertexList_def nat_number
                nextVertices_def nextVertex_def)
done

lemma upt3_in_enumerator: "[0..<3] \<in> set (enumerator 3 3)"
apply(simp only:enumerator_def incrIndexList_def enumBase_def)
apply(simp add:nat_number)
done

lemma mkFaceFin3_in_succs1:
assumes mgp: "minGraphProps g"
and ffs: "f#fs = [f \<leftarrow> faces g. \<not> final f \<and> triangle f]"
shows "Graph (makeFaceFinalFaceList f (faces g)) (countVertices g)
        (map (makeFaceFinalFaceList f) (faceListAt g)) (heights g)
    \<in> set (next_plane\<^bsub>p\<^esub> g)" (is "?g' \<in> _")
proof -
  have "\<not> final g" using Cons_eq_filterD[OF ffs]
    by(auto simp: finalGraph_def nonFinals_def)
  moreover have "?g' \<in> set (generatePolygon 3 (minimalVertex g f) f g)"
  proof -
    have [simp]: "|vertices f| = 3" and fg: "f \<in> \<F> g"
      using Cons_eq_filterD[OF ffs] by auto
    have "vertices f \<noteq> []" by (auto simp:length_0_conv[symmetric])
    hence min: "minimalVertex g f \<in> \<V> f"  by(simp add:minimalVertex_def)
    note upt3_in_enumerator noDupEdge3[OF mgp fg _ min]
    moreover have
      "?g' = subdivFace g f (indexToVertexList f (minimalVertex g f) [0..<3])"
      using min minGraphProps3[OF mgp fg]
	by(simp add:indexToVs3 makeFaceFinal_def subdivFace_def)
    ultimately show ?thesis
      by (fastsimp simp:generatePolygon_def image_def del:enumerator_equiv)
  qed
  moreover have "f = minimalFace (nonFinals g)"
    using decomp_nonFinal3[OF mgp ffs] by simp
  ultimately show ?thesis by(auto simp add:next_plane_def finalGraph_def)
qed


lemma mkFaceFin3_in_rtrancl:
 "minGraphProps g \<Longrightarrow> f#fs = [f \<leftarrow> faces g . \<not> final f \<and> triangle f] \<Longrightarrow>
  g [next_plane\<^bsub>p\<^esub>]\<rightarrow>* makeFaceFinal f g"
apply(simp add:makeFaceFinal_def)
apply(rule RTranCl.succs[OF _ RTranCl.refl])
apply(erule (1) mkFaceFin3_in_succs1)
done

lemma mk3Fin_lem:
  "\<And>g. minGraphProps g \<Longrightarrow> fs = [f \<leftarrow> faces g. \<not> final f \<and> triangle f] \<Longrightarrow>
  g [next_plane\<^bsub>p\<^esub>]\<rightarrow>* foldl (%g f. makeFaceFinal f g) g fs"
proof(induct fs)
  case Nil show ?case by (simp add:RTranCl.refl)
next
  case (Cons f fs)
  let ?g = "makeFaceFinal f g"
  note mkFaceFin3_in_rtrancl[OF Cons(2-3)] moreover
  have "?g [next_plane\<^bsub>p\<^esub>]\<rightarrow>* foldl (%g f. makeFaceFinal f g) ?g fs"
    using Cons_eq_filterD[OF Cons(3)] Cons(2)
    by(rule_tac Cons(1)[OF MakeFaceFinal_minGraphProps])
    (auto simp: makeFaceFinal_def makeFaceFinalFaceList_def pre_subdivFace'_def)
  ultimately show ?case by(rule_tac RTranCl_compose) auto
qed

lemma mk3Fin_in_RTranCl:
 "inv g \<Longrightarrow> g [next_plane\<^bsub>p\<^esub>]\<rightarrow>* makeTrianglesFinal g"
by(simp add:makeTrianglesFinal_def mk3Fin_lem)



subsection "Completeness"

definition
  "in2finals g a b \<equiv>
 \<exists>f \<in> set(finals g). \<exists>f' \<in> set(finals g). (a,b) \<in> \<E> f \<and> (b,a) \<in> \<E> f'"

definition untame\<^isub>2 :: "graph \<Rightarrow> bool" where
"untame\<^isub>2 g \<equiv> \<exists>a b c. is_cycle g [a,b,c] \<and> distinct[a,b,c] \<and>
     (\<forall>f \<in> \<F> g. \<E> f \<noteq> {(c,a), (a,b), (b,c)} \<and>
                   \<E> f \<noteq> {(a,c), (c,b), (b,a)}) \<and>
    in2finals g a b"


lemma untame2: "untame(untame\<^isub>2)"
apply(auto simp:untame_def untame\<^isub>2_def tame_def tame\<^isub>2_def Edges_Cons)
apply(erule allE,erule allE,erule allE,erule impE,assumption)
apply(bestsimp dest!:edges_conv_Edges_if_cong simp: Edges_Cons)
done

lemma mk3Fin_id: "final g \<Longrightarrow> makeTrianglesFinal g = g"
apply(subgoal_tac "[f\<leftarrow>faces g . \<not> final f \<and> triangle f] = []")
 apply(simp add: makeTrianglesFinal_def)
apply(simp add: finalGraph_def nonFinals_def filter_empty_conv)
done


lemma inv_untame2:
 "invariant (\<lambda>g. inv g \<and> untame\<^isub>2 g) next_plane\<^bsub>p\<^esub>"
proof (clarsimp simp:invariant_def invariantE[OF inv_inv_next_plane])
  fix g g' assume g': "g [next_plane\<^bsub>p\<^esub>]\<rightarrow> g'"
    and inv: "inv g" and un: "untame\<^isub>2 g"
  note mgp' = inv_mgp[OF invariantE[OF inv_inv_next_plane, OF g' inv]]
  show "untame\<^isub>2 g'" using un
  proof(clarsimp simp:untame\<^isub>2_def)
    fix a b c
    assume 3: "is_cycle g [a,b,c]" and abc: "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
      and untame: "\<forall>f\<in> \<F> g.
           \<E> f \<noteq> {(c, a), (a, b), (b, c)} \<and>
           \<E> f \<noteq> {(a, c), (c, b), (b, a)}" (is "?P g a b c")
      and in2: "in2finals g a b"
    from in2 obtain f\<^isub>1 f\<^isub>2 :: face
      where f\<^isub>1: "f\<^isub>1 \<in> \<F> g \<and> final f\<^isub>1 \<and> (a,b) \<in> \<E> f\<^isub>1"
      and   f\<^isub>2: "f\<^isub>2 \<in> \<F> g \<and> final f\<^isub>2 \<and> (b,a) \<in> \<E> f\<^isub>2"
      by(auto simp:finals_def in2finals_def)+
    note mgp = inv_mgp[OF inv]
    note g'1 = mgp_next_plane0_if_next_plane[OF mgp g']
    have f\<^isub>1': "f\<^isub>1 \<in> \<F> g'" and f\<^isub>2': "f\<^isub>2 \<in> \<F> g'"
      using next_plane0_finals_incr[OF g'1] f\<^isub>1 f\<^isub>2 by(auto simp:finals_def)
    have "is_cycle g' [a,b,c]"
      using 3 next_plane0_set_edges_subset[OF mgp g'1]
      by(auto simp:is_cycle_def edges_graph_def
	neighbors_edges[OF mgp] neighbors_edges[OF mgp'])
    moreover have "?P g' a b c"
    proof (rule ccontr, auto)
      fix f assume fg: "f \<in> \<F> g'" and Ef: "\<E> f = {(c,a), (a,b), (b,c)}"
      moreover have "f \<noteq> f\<^isub>1" using untame f\<^isub>1 Ef by blast
      ultimately show False
	using f\<^isub>1 f\<^isub>1' by(blast dest: mgp_edges_disj[OF mgp'])
    next
      fix f assume fg: "f \<in> \<F> g'" and Ef: "\<E> f = {(a,c), (c,b), (b,a)}"
      moreover have "f \<noteq> f\<^isub>2" using untame f\<^isub>2 Ef by blast
      ultimately show False
	using f\<^isub>2 f\<^isub>2' by(blast dest: mgp_edges_disj[OF mgp'])
    qed
    moreover have "in2finals g' a b" using in2 next_plane0_finals_subset[OF g'1]
      by(auto simp:in2finals_def)
    ultimately
    show "\<exists>a b c. is_cycle g' [a,b,c] \<and> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<and> ?P g' a b c \<and> in2finals g' a b"
      using abc by blast
  qed
qed


lemma mk3Fin_id2:
assumes mgp: "minGraphProps g" and nf: "nonFinals g \<noteq> []"
and n3: "\<not> triangle(minimalFace(nonFinals g))"
shows "makeTrianglesFinal g = g"
proof -
  have "\<forall>f\<in>set (nonFinals g). 3 \<le> |vertices f|"
    using mgp_vertices3[OF mgp] by(simp add:nonFinals_def)
  with n3 have "\<forall>f \<in> set(nonFinals g). \<not> triangle f"
    by(rule_tac minimal_neq_lowerbound[OF nf])
      (auto simp:minimalFace_def o_def)
  hence "\<forall>f \<in> set(faces g). final f \<or> \<not> triangle f"
    by(auto simp:nonFinals_def)
  thus ?thesis  by(simp add:makeTrianglesFinal_def)
qed



lemma mk3Fin_mkFaceFin:
assumes mgp: "minGraphProps g" and nf: "nonFinals g \<noteq> []"
and 3: "triangle(minimalFace(nonFinals g))"
shows "makeTrianglesFinal (makeFaceFinal (minimalFace (nonFinals g)) g) =
       makeTrianglesFinal g"
proof -
  let ?f = "minimalFace (nonFinals g)"
  from nf 3 have "minimalFace(nonFinals g) \<in> set(nonFinals g)"
    by (simp add:minimalFace_def)
  with 3 have "[f \<leftarrow> faces g. \<not> final f \<and> triangle f] \<noteq> []"
    by (auto simp: filter_empty_conv nonFinals_def)
  then obtain f fs where ffs: "f#fs = [f \<leftarrow> faces g. \<not> final f \<and> triangle f]"
    by(fastsimp simp add:neq_Nil_conv)
  with decomp_nonFinal3[OF mgp ffs]
  have "[f \<leftarrow> faces g. \<not> final f \<and> triangle f] =
        ?f # [f \<leftarrow> faces(makeFaceFinal ?f g). \<not> final f \<and> triangle f]" by(simp)
  thus ?thesis by(simp add:makeTrianglesFinal_def)
qed


lemma next_plane_mk3Fin_alternatives:
assumes inv: "inv g" and 2: "|faces g| \<noteq> 2" and 1: "g [next_plane\<^bsub>p\<^esub>]\<rightarrow> g'"
shows "untame\<^isub>2 g' \<or> makeTrianglesFinal g = g \<or>
       makeTrianglesFinal g' = makeTrianglesFinal g"
proof -
  note mgp = inv_mgp[OF inv]
  note mgp' = inv_mgp[OF invariantE[OF inv_inv_next_plane, OF 1 inv]]
  have nf: "nonFinals g \<noteq> []" using 1 by(auto simp:next_plane_def)
  note gg' = mgp_next_plane0_if_next_plane[OF mgp 1]
  show ?thesis
  proof (cases "triangle(minimalFace(nonFinals g))")
    case True
    let ?f = "minimalFace(nonFinals g)"
    have f: "?f \<in> set(nonFinals g)" using nf by (simp add:minimalFace_def)
    hence fg: "?f \<in> \<F> g" by(simp add:nonFinals_def)
    from f have fnf: "\<not> final ?f" by(simp add:nonFinals_def)
    note distf = minGraphProps3[OF mgp fg]
    def a \<equiv> "minimalVertex g ?f"
    from mgp_vertices_nonempty[OF mgp fg]
    have v: "a \<in> set(vertices ?f)" by (simp add:a_def minimalVertex_def)
    from 1 obtain i e
      where g'0: "g' = subdivFace g ?f (indexToVertexList ?f a e)"
      and e: "e \<in> set (enumerator i |vertices ?f| )" and i: "2 < i"
      and containsNot: "\<not> containsDuplicateEdge g ?f a e"
      by (auto simp: a_def next_plane_def generatePolygon_def image_def
               split:split_if_asm)
    note pre_add = pre_subdivFace_indexToVertexList[OF mgp f v e containsNot i]
    with g'0 have g': "g' = subdivFace' g ?f a 0 (tl(indexToVertexList ?f a e))"
      by (simp  add: subdivFace_subdivFace'_eq)
    from pre_add have "indexToVertexList ?f a e \<noteq> []"
      by (simp add: pre_subdivFace_def pre_subdivFace_face_def)
    with pre_add v
    have pre: "pre_subdivFace' g ?f a a 0 (tl(indexToVertexList ?f a e))"
      by(fastsimp simp add:neq_Nil_conv elim:pre_subdivFace_pre_subdivFace')
    have "g' = makeFaceFinal ?f g \<or>
          (\<forall>f' \<in> \<F> g' - (\<F> g - {?f}). \<E> f' \<noteq> \<E> ?f)" (is "?A \<or> ?B")
      by(simp only:g')(rule dist_edges_subdivFace'[OF pre mgp fg])
    thus ?thesis
    proof
      assume ?A
      hence "makeTrianglesFinal g' = makeTrianglesFinal g"
	by(simp add:mk3Fin_mkFaceFin[OF mgp nf True])
      thus ?thesis by blast
    next
      assume B: ?B
      obtain b c where fabs: "vertices ?f = [a,b,c] \<or> vertices ?f = [c,a,b] \<or>
                        vertices ?f = [b,c,a]"
	using v True by(fastsimp simp: nat_number length_Suc_conv)
      hence Ef: "\<E> ?f = {(a,b), (b,c), (c,a)}"
	by(fastsimp simp: edges_conv_Edges[OF distf] Edges_Cons)
      hence "{(a,b), (b,c), (c,a)} \<subseteq> \<E> g'"
	using fg next_plane0_set_edges_subset[OF mgp gg']
	by(unfold edges_graph_def) blast
      hence 3: "is_cycle g' [c,a,b]"
	by(auto simp: is_cycle_def neighbors_edges[OF mgp'])
      have abc: "distinct[a,b,c]" using distf fabs by auto
      obtain f' where f': "f' \<in> \<F> g \<and> final f' \<and> (a,c) \<in> \<E> f'"
	using Ef inv_one_finalD'[OF inv fg fnf]
	by blast
      hence f'g': "f' \<in> \<F> g'"
	using f' next_plane0_finals_subset[OF gg'] by (simp add:finals_def)blast
      have "?f\<^bsup>-1\<^esup> \<bullet> a = c" using fabs abc by(auto simp:prevVertex_def)
      then obtain f'' where f'': "f'' \<in> \<F> g' \<and> final f'' \<and> (c,a)\<in> \<E> f''"
	using g' subdivFace'_final_base[OF mgp pre fg] by simp blast
      { fix ff assume ffg': "ff \<in> \<F> g'"
	assume "\<E> ff = {(b,c), (c,a), (a,b)} \<or>
                \<E> ff = {(c,b), (b,a), (a,c)}" (is "?ab \<or> ?ba")
	hence False
	proof
	  assume Eff: ?ab
	  have "ff \<notin> \<F> g - {?f}"
	  proof
	    assume "ff \<in> \<F> g - {?f}"
	    hence ffg: "ff \<in> \<F> g" and neq: "ff \<noteq> ?f" by auto
	    note distff = minGraphProps3[OF mgp ffg]
	    have "ff = ?f" using Ef Eff
	      by(blast intro: face_eq_if_normFace_eq[OF mgp ffg fg]
                       normFace_eq_if_edges_eq[OF distff distf])
	    with neq show False by fast
	  qed
	  with B ffg' have "\<E> ff \<noteq> \<E> ?f" by blast
	  with Eff Ef show False by blast
	next
	  assume Eff: ?ba
	  obtain h\<^isub>1 :: face where h\<^isub>1g: "h\<^isub>1 \<in> \<F> g" and fh\<^isub>1: "final h\<^isub>1"
	    and ach\<^isub>1: "(a,c) : \<E> h\<^isub>1"
	    using inv_one_finalD'[OF inv fg fnf] Ef by blast
	  obtain h\<^isub>2 :: face where h\<^isub>2g: "h\<^isub>2 \<in> \<F> g" and fh\<^isub>2: "final h\<^isub>2"
	    and cbh\<^isub>2: "(c,b) : \<E> h\<^isub>2"
	    using inv_one_finalD'[OF inv fg fnf] Ef by blast
	  obtain h\<^isub>3 :: face where h\<^isub>3g: "h\<^isub>3 \<in> \<F> g" and fh\<^isub>3: "final h\<^isub>3"
	    and bah\<^isub>3: "(b,a) : \<E> h\<^isub>3"
	    using inv_one_finalD'[OF inv fg fnf] Ef by blast
	  have h\<^isub>1g': "h\<^isub>1 \<in> \<F> g'"
	    using h\<^isub>1g fh\<^isub>1 subdivFace_pres_finals[OF _ fnf] g'0 fg
	    by(simp add:finals_def)
	  have h\<^isub>2g': "h\<^isub>2 \<in> \<F> g'"
	    using h\<^isub>2g fh\<^isub>2 subdivFace_pres_finals[OF _ fnf] g'0 fg
	    by(simp add:finals_def)
	  have h\<^isub>3g': "h\<^isub>3 \<in> \<F> g'"
	    using h\<^isub>3g fh\<^isub>3 subdivFace_pres_finals[OF _ fnf] g'0 fg
	    by(simp add:finals_def)
	  note mgp' = inv_mgp[OF inv_inv_next_plane0[THEN invariantE, OF gg' inv]]
	  note disth\<^isub>1 = minGraphProps3[OF mgp h\<^isub>1g]
	  have "\<not>(h\<^isub>1 = h\<^isub>2 \<and> h\<^isub>1 = h\<^isub>3 \<and> h\<^isub>2 = h\<^isub>3)"
	  proof
	    assume [simp]: "h\<^isub>1 = h\<^isub>2 \<and> h\<^isub>1 = h\<^isub>3 \<and> h\<^isub>2 = h\<^isub>3"
	    have "face_face_op g" using mgp by(simp add:minGraphProps_def)
	    moreover have "h\<^isub>1 \<noteq> ?f" using fnf fh\<^isub>1 by auto
	    ultimately have "\<E> h\<^isub>1 \<noteq> (\<E> ?f)\<inverse>" using 2 h\<^isub>1g fg
	      by(simp add:face_face_op_def)
	    moreover have "\<E> h\<^isub>1 = {(c,b),(b,a),(a,c)}"
	      using abc ach\<^isub>1 cbh\<^isub>2 bah\<^isub>3
	      by(rule_tac triangle_if_3circular[OF _ disth\<^isub>1])auto
	    ultimately show False using Ef by fastsimp
	  qed
	  hence "\<not>(h\<^isub>1 = ff \<and> h\<^isub>2 = ff \<and> h\<^isub>3 = ff)" by blast
	  thus False using Eff
	    mgp_edges_disj[OF mgp' _ h\<^isub>1g' ffg' ach\<^isub>1]
	    mgp_edges_disj[OF mgp' _ h\<^isub>2g' ffg' cbh\<^isub>2]
	    mgp_edges_disj[OF mgp' _ h\<^isub>3g' ffg' bah\<^isub>3]
	    by blast
	qed }
      with 3 abc f' f'g' f'' have "untame\<^isub>2 g'"
	by(simp add: untame\<^isub>2_def in2finals_def finals_def) blast
      thus ?thesis by blast
    qed
  next
    case False 
    thus ?thesis by(simp add:mk3Fin_id2[OF mgp nf])
  qed
qed


theorem make3Fin_complete:
 "\<lbrakk> invariant inv (succ p);
    \<And>g. inv g \<Longrightarrow> set (succ p g) \<subseteq> set (next_plane p g);
   tame g; final g; Seed\<^bsub>p\<^esub> [succ p]\<rightarrow>* g \<rbrakk> \<Longrightarrow>
 Seed\<^bsub>p\<^esub> [map makeTrianglesFinal o succ p]\<rightarrow>* g"
apply(rule comp_map_tame_pres[OF _ _ untame2])
        apply assumption
       apply(rule inv_subset[OF inv_untame2[where p=p]])
       apply blast
      apply(erule mk3Fin_id)
     apply(rule inv_RTranCl_subset[OF inv_untame2[where p=p]])
     apply(rule mk3Fin_in_RTranCl)
     apply blast
    defer
    apply assumption
   apply(rule inv_Seed)
  apply assumption
 apply assumption
apply(rule next_plane_mk3Fin_alternatives)
  apply(rule invariantE[OF inv_inv_next_plane])
   apply blast
  apply assumption
 apply(rule step_outside2)
   apply assumption
  apply(rule mgp_next_plane0_if_next_plane[OF inv_mgp])
   apply assumption
  apply blast
 apply(simp add:finalGraph_def)
 apply(rule next_plane0_nonfinals)
 apply(rule mgp_next_plane0_if_next_plane[OF inv_mgp])
  apply(rule invariantE[OF inv_inv_next_plane])
   apply blast
  apply assumption
 apply (blast dest:invariantE)
apply (blast dest:invariantE)
done

end
