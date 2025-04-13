subsection\<open>Abstract Rewriting\<close>

theory Abstract_Rewriting_Impl
  imports 
    "Abstract-Rewriting.Abstract_Rewriting"
begin

partial_function (option) compute_NF :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a option"
  where [simp,code]: "compute_NF f a = (case f a of None \<Rightarrow> Some a | Some b \<Rightarrow> compute_NF f b)"

lemma compute_NF_sound: assumes res: "compute_NF f a = Some b"
  and f_sound: "\<And> a b. f a = Some b \<Longrightarrow> (a,b) \<in> r"
shows "(a,b) \<in> r^*"
proof (induct rule: compute_NF.raw_induct[OF _ res, of "\<lambda> g a b. g = f \<longrightarrow> (a,b) \<in> r^*", THEN mp[OF _ refl]])
  case (1 cnf g a b)
  show ?case
  proof
    assume "g = f"
    note 1 = 1[unfolded this]
    show "(a,b) \<in> r^*"
    proof (cases "f a")
      case None
      with 1(2) show ?thesis by simp
    next
      case (Some c)
      from 1(2)[unfolded this] have "cnf f c = Some b" by simp
      from 1(1)[OF this] have "(c,b) \<in> r^*" by auto
      with f_sound[OF Some] show ?thesis by auto
    qed
  qed
qed

lemma compute_NF_complete: assumes res: "compute_NF f a = Some b"
  and f_complete: "\<And> a. f a = None \<Longrightarrow> a \<in> NF r"
shows "b \<in> NF r"
proof (induct rule: compute_NF.raw_induct[OF _ res, of "\<lambda> g a b. g = f \<longrightarrow> b \<in> NF r", THEN mp[OF _ refl]])
  case (1 cnf g a b)
  show ?case
  proof
    assume "g = f"
    note 1 = 1[unfolded this]
    show "b \<in> NF r"
    proof (cases "f a")
      case None
      with f_complete[OF None] 1(2)
      show ?thesis by simp
    next
      case (Some c)
      from 1(2)[unfolded this] have "cnf f c = Some b" by simp
      from 1(1)[OF this] show ?thesis by simp
    qed
  qed
qed

lemma compute_NF_SN: assumes SN: "SN r"
  and f_sound: "\<And> a b. f a = Some b \<Longrightarrow> (a,b) \<in> r"
shows "\<exists> b. compute_NF f a = Some b" (is "?P a")
proof -
  let ?r = "{(a,b). f a = Some b}"
  have "?r \<subseteq> r" using f_sound by auto
  from SN_subset[OF SN this] have SNr: "SN ?r" .
  show ?thesis
  proof (induct rule: SN_induct[OF SNr, of "\<lambda> a. ?P a"])
    case (1 a)
    show ?case
    proof (cases "f a")
      case None then show ?thesis by auto
    next
      case (Some b)
      then have "(a,b) \<in> ?r" by simp
      from 1[OF this] f_sound[OF Some] show ?thesis 
        using Some by auto
    qed
  qed
qed

definition "compute_trancl A R = R^+ `` A"
lemma compute_trancl_rtrancl[code_unfold]: "{b. (a,b) \<in> R^*} = insert a (compute_trancl {a} R)"
proof -
  have id: "R^* = (Id \<union> R^+)" by regexp
  show ?thesis unfolding id compute_trancl_def by auto
qed

lemma compute_trancl_code[code]: "compute_trancl A R = (let B = R `` A in 
  if B \<subseteq> {} then {} else B \<union> compute_trancl B { ab \<in> R . fst ab \<notin> A \<and> snd ab \<notin> B})"
proof -
  have R: "R^+ = R O R^*" by regexp
  define B where "B = R `` A"
  define R' where "R' = {ab \<in> R. fst ab \<notin> A \<and> snd ab \<notin> B}"
  note d = compute_trancl_def
  show ?thesis unfolding Let_def B_def[symmetric] R'_def[symmetric] d
  proof (cases "B \<subseteq> {}")
    case True
    then show "R\<^sup>+ `` A = (if B \<subseteq> {} then {} else B \<union> R'^+ `` B)" unfolding B_def R by auto
  next
    case False
    have "R' \<subseteq> R" unfolding R'_def by auto 
    then have "R'^+ \<subseteq> R^+" by (rule trancl_mono_set)
    also have "\<dots> \<subseteq> R^*" by auto
    finally have mono: "R'^+ \<subseteq> R^*" .
    have "B \<union> R'\<^sup>+ `` B = R\<^sup>+ `` A"  
    proof
      show "B \<union> R'\<^sup>+ `` B \<subseteq> R^+ `` A" unfolding B_def R using mono
        by blast
    next
      show "R^+ `` A \<subseteq> B \<union> R'^+ `` B"
      proof
        fix x
        assume "x \<in> R^+ `` A"
        then obtain a where a: "a \<in> A" and ax: "(a,x) \<in> R^+" by auto
        from ax a show "x \<in> B \<union> R'^+ `` B"
        proof (induct)
          case base
          then show ?case unfolding B_def by auto
        next
          case (step x y)
          from step(3)[OF step(4)] have x: "x \<in> B \<union> R'^+ `` B" .
          show ?case
          proof (cases "y \<in> B")
            case False note y = this
            show ?thesis
            proof (cases "x \<in> A")
              case True
              with y step(2) show ?thesis unfolding B_def by auto
            next
              case False
              with y step(2) have "(x,y) \<in> R'" unfolding R'_def by auto
              with x have "y \<in>  (R' \<union> (R'^+ O R')) `` B" by blast
              also have "R' \<union> (R'^+ O R') = R'^+" by regexp
              finally show ?thesis by blast
            qed
          qed auto
        qed
      qed 
    qed      
    with False show "R\<^sup>+ `` A = (if B \<subseteq> {} then {} else B \<union> R'^+ `` B)" by auto
  qed 
qed

lemma trancl_image_code[code_unfold]: "R^+ `` A = compute_trancl A R" unfolding compute_trancl_def by auto
lemma compute_rtrancl[code_unfold]: "R^* `` A = A \<union> compute_trancl A R"
proof -
  have id: "R^* = (Id \<union> R^+)" by regexp
  show ?thesis unfolding id compute_trancl_def by auto
qed
lemma trancl_image_code'[code_unfold]: "(a,b) \<in> R^+ \<longleftrightarrow> b \<in> compute_trancl {a} R" unfolding compute_trancl_def by auto
lemma rtrancl_image_code[code_unfold]: "(a,b) \<in> R^* \<longleftrightarrow> b = a \<or> b \<in> compute_trancl {a} R"
  using compute_rtrancl[of R "{a}"] by auto

end