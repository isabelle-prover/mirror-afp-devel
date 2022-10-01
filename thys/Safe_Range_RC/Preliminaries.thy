section \<open>Preliminaries\<close>

(*<*)
theory Preliminaries
imports "List-Index.List_Index"
begin
(*>*)

subsection \<open>Iterated Function Update\<close>

abbreviation fun_upds ("_[_ :=\<^sup>* _]" [90, 0, 0] 91) where
  "f[xs :=\<^sup>* ys] \<equiv> fold (\<lambda>(x, y) f. f(x := y)) (zip xs ys) f"

fun restrict where
  "restrict A (x # xs) (y # ys) = (if x \<in> A then y # restrict (A - {x}) xs ys else restrict A xs ys)"
| "restrict A _ _ = []"

fun extend :: "nat set \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
  "extend A (x # xs) ys = (if x \<in> A
     then (\<Union>zs \<in> extend (A - {x}) xs (tl ys). {hd ys # zs})
     else (\<Union>z \<in> UNIV. \<Union>zs \<in> extend A xs ys. {z # zs}))"
| "extend A _ _ = {[]}"

fun lookup where
  "lookup (x # xs) (y # ys) z = (if x = z then y else lookup xs ys z)"
| "lookup _ _ _ = undefined"

lemma extend_nonempty: "extend A xs ys \<noteq> {}"
  by (induct xs arbitrary: A ys) auto

lemma length_extend: "zs \<in> extend A xs ys \<Longrightarrow> length zs = length xs"
  by (induct xs arbitrary: A ys zs) (auto split: if_splits)

lemma ex_lookup_extend: "x \<notin> A \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>zs \<in> extend A xs ys. lookup xs zs x = d"
proof (induct xs arbitrary: A ys)
  case (Cons a xs)
  from Cons(1)[of "A - {a}" "tl ys"] Cons(1)[of A ys] Cons(2-) show ?case
    by (auto simp: ex_in_conv extend_nonempty)
qed simp

lemma restrict_extend: "A \<subseteq> set xs \<Longrightarrow> length ys = card A \<Longrightarrow> zs \<in> extend A xs ys \<Longrightarrow> restrict A xs zs = ys"
proof (induct xs arbitrary: A ys zs)
  case (Cons a xs)
  then have "finite A"
    by (elim finite_subset) auto
  with Cons(1)[of "A - {a}" "tl ys" "tl zs"] Cons(1)[of A ys "tl zs"] Cons(2-) show ?case
    by (cases ys) (auto simp: subset_insert_iff split: if_splits)
qed simp

lemma fun_upds_notin[simp]: "length xs = length ys \<Longrightarrow> x \<notin> set xs \<Longrightarrow> (\<sigma>[xs :=\<^sup>* ys]) x = \<sigma> x"
  by (induct xs ys arbitrary: \<sigma> rule: list_induct2) auto

lemma fun_upds_twist: "length xs = length ys \<Longrightarrow> a \<notin> set xs \<Longrightarrow> \<sigma>(a := x)[xs :=\<^sup>* ys] = (\<sigma>[xs :=\<^sup>* ys])(a := x)"
  by (induct xs ys arbitrary: \<sigma> rule: list_induct2) (auto simp: fun_upd_twist)

lemma fun_upds_twist_apply: "length xs = length ys \<Longrightarrow> a \<notin> set xs \<Longrightarrow> a \<noteq> b \<Longrightarrow> (\<sigma>(a := x)[xs :=\<^sup>* ys]) b = (\<sigma>[xs :=\<^sup>* ys]) b"
  by (induct xs ys arbitrary: \<sigma> rule: list_induct2) (auto simp: fun_upd_twist)

lemma fun_upds_extend:
  "x \<in> A \<Longrightarrow> A \<subseteq> set xs \<Longrightarrow> distinct xs \<Longrightarrow> sorted xs \<Longrightarrow> length ys = card A \<Longrightarrow> zs \<in> extend A xs ys \<Longrightarrow>
    (\<sigma>[xs :=\<^sup>* zs]) x = (\<sigma>[sorted_list_of_set A :=\<^sup>* ys]) x"
proof (induct xs arbitrary: A ys zs \<sigma>)
  case (Cons a xs)
  then have fin[simp]: "finite A"
    by (elim finite_subset) auto
  from Cons(2-) have "a \<in> A \<Longrightarrow> Min A = a" if "a \<in> A"
    by (intro Min_eqI) auto
  with Cons(2) fin have *: "a \<in> A \<Longrightarrow> sorted_list_of_set A = a # sorted_list_of_set (A - {a})"
    by (subst sorted_list_of_set_nonempty) auto
  show ?case
    using Cons(1)[of "A - {a}" "tl ys"] Cons(1)[of A ys] Cons(2-)
    by (cases ys; cases "x = a")
      (auto simp add: subset_insert_iff * fun_upds_twist_apply length_extend simp del: fun_upd_apply split: if_splits)
qed simp

lemma fun_upds_map_self: "\<sigma>[xs :=\<^sup>* map \<sigma> xs] = \<sigma>"
  by (induct xs arbitrary: \<sigma>) auto

lemma fun_upds_single: "distinct xs \<Longrightarrow> \<sigma>[xs :=\<^sup>* map (\<sigma>(y := d)) xs] = (if y \<in> set xs then \<sigma>(y := d) else \<sigma>)"
  by (induct xs arbitrary: \<sigma>) (auto simp: fun_upds_twist)

subsection \<open>Lists and Sets\<close>

lemma find_index_less_size: "\<exists>x \<in> set xs. P x \<Longrightarrow> find_index P xs < size xs"
  by (induct xs) auto

lemma index_less_size: "x \<in> set xs \<Longrightarrow> index xs x < size xs"
  by (simp add: index_def find_index_less_size)

lemma fun_upds_in: "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<sigma>[xs :=\<^sup>* ys]) x = ys ! index xs x"
  by (induct xs ys arbitrary: \<sigma> rule: list_induct2) auto

lemma remove_nth_index: "remove_nth (index ys y) ys = remove1 y ys"
  by (induct ys) auto

lemma index_remove_nth: "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> index (remove_nth i xs) x = (if index xs x < i then index xs x else if i = index xs x then length xs - 1 else index xs x - 1)"
  by (induct i xs rule: remove_nth.induct) (auto simp: not_less intro!: Suc_pred split: if_splits)

lemma insert_nth_nth_index:
  "y \<noteq> z \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set ys \<Longrightarrow> length ys = Suc (length xs) \<Longrightarrow> distinct ys \<Longrightarrow>
  insert_nth (index ys y) x xs ! index ys z =
  xs ! index (remove1 y ys) z"
  by (subst nth_insert_nth;
      auto simp: remove_nth_index[symmetric] index_remove_nth dest: index_less_size intro!: arg_cong[of _ _ "nth xs"] index_eqI)

lemma index_lt_index_remove: "index xs x < index xs y \<Longrightarrow> index xs x = index (remove1 y xs) x"
  by (induct xs) auto

lemma index_gt_index_remove: "index xs x > index xs y \<Longrightarrow> index xs x = Suc (index (remove1 y xs) x)"
proof (induct xs)
  case (Cons z xs)
  then show ?case
    by (cases "z = x") auto
qed simp

lemma lookup_map[simp]: "x \<in> set xs \<Longrightarrow> lookup xs (map f xs) x = f x"
  by (induct xs) auto

lemma in_set_remove_cases: "P z \<Longrightarrow> (\<forall>x \<in> set (remove1 z xs). P x) \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x"
  by (cases "x = z") auto

lemma insert_remove_id: "x \<in> X \<Longrightarrow> X = insert x (X - {x})"
  by auto

lemma infinite_surj: "infinite A \<Longrightarrow> A \<subseteq> f ` B \<Longrightarrow> infinite B"
  by (elim contrapos_nn finite_surj)

class infinite =
  fixes to_nat :: "'a \<Rightarrow> nat"
  assumes surj_to_nat: "surj to_nat"
begin

lemma infinite_UNIV: "infinite (UNIV :: 'a set)"
  using surj_to_nat by (intro infinite_surj[of UNIV to_nat]) auto

end

instantiation nat :: infinite begin
definition to_nat_nat :: "nat \<Rightarrow> nat" where "to_nat_nat = id"
instance by standard (auto simp: to_nat_nat_def)
end

instantiation list :: (type) infinite begin
definition to_nat_list :: "'a list \<Rightarrow> nat" where "to_nat_list = length"
instance by standard (auto simp: image_iff to_nat_list_def intro!: exI[of _ "replicate _ _"])
end

subsection \<open>Equivalence Closure and Classes\<close>

definition symcl where
  "symcl r = {(x, y). (x, y) \<in> r \<or> (y, x) \<in> r}"

definition transymcl where
  "transymcl r = trancl (symcl r)"

lemma symclp_symcl_eq[pred_set_conv]: "symclp (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x y. (x, y) \<in> symcl r)"
  by (auto simp: symclp_def symcl_def fun_eq_iff)

definition "classes Qeq = quotient (Field Qeq) (transymcl Qeq)"

lemma Field_symcl[simp]: "Field (symcl r) = Field r"
  unfolding symcl_def Field_def by auto

lemma Domain_symcl[simp]: "Domain (symcl r) = Field r"
  unfolding symcl_def Field_def by auto

lemma Field_trancl[simp]: "Field (trancl r) = Field r"
  unfolding Field_def by auto

lemma Field_transymcl[simp]: "Field (transymcl r) = Field r"
  unfolding transymcl_def by auto

lemma eqclass_empty_iff[simp]: "r `` {x} = {} \<longleftrightarrow> x \<notin> Domain r"
  by auto

lemma sym_symcl[simp]: "sym (symcl r)"
  unfolding symcl_def sym_def by auto

lemma in_symclI:
  "(a,b) \<in> r \<Longrightarrow> (a,b) \<in> symcl r"
  "(a,b) \<in> r \<Longrightarrow> (b,a) \<in> symcl r"
  by (auto simp: symcl_def)

lemma sym_transymcl: "sym (transymcl r)"
  by (simp add: sym_trancl transymcl_def)

lemma symcl_insert:
  "symcl (insert (x, y) Qeq) = insert (y, x) (insert (x, y) (symcl Qeq))"
  by (auto simp: symcl_def)

lemma equiv_transymcl: "Equiv_Relations.equiv (Field Qeq) (transymcl Qeq)"
  by (auto simp: Equiv_Relations.equiv_def sym_trancl refl_on_def transymcl_def
    dest: FieldI1 FieldI2 Field_def[THEN equalityD1, THEN set_mp]
    intro: r_r_into_trancl[of x _ _ x for x]  elim!: in_symclI)

lemma equiv_quotient_no_empty_class: "Equiv_Relations.equiv A r \<Longrightarrow> {} \<notin> A // r"
  by (auto simp: quotient_def refl_on_def sym_def Equiv_Relations.equiv_def)

lemma classes_cover: "\<Union>(classes Qeq) = Field Qeq"
  by (simp add: Union_quotient classes_def equiv_transymcl)

lemma classes_disjoint: "X \<in> classes Qeq \<Longrightarrow> Y \<in> classes Qeq \<Longrightarrow> X = Y \<or> X \<inter> Y = {}"
  using quotient_disj[OF equiv_transymcl]
  by (auto simp: classes_def)

lemma classes_nonempty: "{} \<notin> classes Qeq"
  using equiv_quotient_no_empty_class[OF equiv_transymcl]
  by (auto simp: classes_def)

definition "class x Qeq = (if \<exists>X \<in> classes Qeq. x \<in> X then Some (THE X. X \<in> classes Qeq \<and> x \<in> X) else None)"

lemma class_Some_eq: "class x Qeq = Some X \<longleftrightarrow> X \<in> classes Qeq \<and> x \<in> X"
  unfolding class_def
  by (auto 0 3 dest: classes_disjoint del: conjI intro!: the_equality[of _ X]
   conjI[of "(\<exists>X\<in>classes Qeq. x \<in> X)"] intro: theI[where P="\<lambda>X. X \<in> classes Qeq \<and> x \<in> X"])

lemma class_None_eq: "class x Qeq = None \<longleftrightarrow> x \<notin> Field Qeq"
  by (simp add: class_def classes_cover[symmetric] split: if_splits)

lemma insert_Image_triv: "x \<notin> r \<Longrightarrow> insert (x, y) Qeq `` r = Qeq `` r"
  by auto

lemma Un1_Image_triv: "Domain B \<inter> r = {} \<Longrightarrow> (A \<union> B) `` r = A `` r"
  by auto

lemma Un2_Image_triv: "Domain A \<inter> r = {} \<Longrightarrow> (A \<union> B) `` r = B `` r"
  by auto

lemma classes_empty: "classes {} = {}"
  unfolding classes_def by auto

lemma ex_class: "x \<in> Field Qeq \<Longrightarrow> \<exists>X. class x Qeq = Some X \<and> x \<in> X"
  by (metis Union_iff class_Some_eq classes_cover)

lemma equivD:
  "Equiv_Relations.equiv A r \<Longrightarrow> refl_on A r"
  "Equiv_Relations.equiv A r \<Longrightarrow> sym r"
  "Equiv_Relations.equiv A r \<Longrightarrow> trans r"
  by (blast elim: Equiv_Relations.equivE)+

lemma transymcl_into:
  "(x, y) \<in> r \<Longrightarrow> (x, y) \<in> transymcl r"
  "(x, y) \<in> r \<Longrightarrow> (y, x) \<in> transymcl r"
  unfolding transymcl_def by (blast intro: in_symclI r_into_trancl')+

lemma transymcl_self:
  "(x, y) \<in> r \<Longrightarrow> (x, x) \<in> transymcl r"
  "(x, y) \<in> r \<Longrightarrow> (y, y) \<in> transymcl r"
  unfolding transymcl_def by (blast intro: in_symclI(1) in_symclI(2) r_r_into_trancl)+

lemma transymcl_trans: "(x, y) \<in> transymcl r \<Longrightarrow> (y, z) \<in> transymcl r \<Longrightarrow> (x, z) \<in> transymcl r"
  using equiv_transymcl[THEN equivD(3), THEN transD] .

lemma transymcl_sym: "(x, y) \<in> transymcl r \<Longrightarrow> (y, x) \<in> transymcl r"
  using equiv_transymcl[THEN equivD(2), THEN symD] .

lemma edge_same_class: "X \<in> classes Qeq \<Longrightarrow> (a, b) \<in> Qeq \<Longrightarrow> a \<in> X \<longleftrightarrow> b \<in> X"
  unfolding classes_def by (elim quotientE) (auto elim!: transymcl_trans transymcl_into)

lemma Field_transymcl_self: "a \<in> Field Qeq \<Longrightarrow> (a, a) \<in> transymcl Qeq"
  by (auto simp: Field_def transymcl_def[symmetric] transymcl_self)

lemma transymcl_insert: "transymcl (insert (a, b) Qeq) = transymcl Qeq \<union> {(a,a),(b,b)} \<union>
   ((transymcl Qeq \<union> {(a, a), (b, b)}) O {(a, b), (b, a)} O (transymcl Qeq \<union> {(a, a), (b, b)}) - transymcl Qeq)"
  by (auto simp: relcomp_def relcompp_apply transymcl_def symcl_insert trancl_insert2 dest: trancl_trans)

lemma transymcl_insert_both_new: "a \<notin> Field Qeq \<Longrightarrow> b \<notin> Field Qeq \<Longrightarrow>
  transymcl (insert (a, b) Qeq) = transymcl Qeq \<union> {(a,a),(b,b),(a,b),(b,a)}"
  unfolding transymcl_insert
  by (auto dest: FieldI1 FieldI2)

lemma transymcl_insert_same_class: "(x, y) \<in> transymcl Qeq \<Longrightarrow> transymcl (insert (x, y) Qeq) = transymcl Qeq"
  by (auto 0 3 simp: transymcl_insert intro: transymcl_sym transymcl_trans)

lemma classes_insert: "classes (insert (x, y) Qeq) =
  (case (class x Qeq, class y Qeq) of
    (Some X, Some Y) \<Rightarrow> if X = Y then classes Qeq else classes Qeq - {X, Y} \<union> {X \<union> Y}
  | (Some X, None) \<Rightarrow> classes Qeq - {X} \<union> {insert y X}
  | (None, Some Y) \<Rightarrow> classes Qeq - {Y} \<union> {insert x Y}
  | (None, None) \<Rightarrow> classes Qeq \<union> {{x,y}})"
proof ((cases "class x Qeq"; cases "class y Qeq"), goal_cases NN NS SN SS)
  case NN
  then have "classes (insert (x, y) Qeq) = classes Qeq \<union> {{x, y}}"
    by (fastforce simp: class_None_eq classes_def transymcl_insert_both_new insert_Image_triv quotientI
      elim!: quotientE dest: FieldI1  intro: quotient_def[THEN Set.equalityD2, THEN set_mp] intro!: disjI1)
  with NN show ?case
    by auto
next
  case (NS Y)
  then have "insert x Y = transymcl (insert (x, y) Qeq) `` {x}"
    unfolding transymcl_insert using FieldI1[of x _ "transymcl Qeq"]
    relcompI[OF insertI1 relcompI[OF insertI1 insertI2[OF insertI2[OF transymcl_trans[OF transymcl_sym]]]],
      of _ y Qeq _ x x "insert (y,y) (transymcl Qeq)" "{(y,x)}" "(x, x)" "(y, y)"]
    by (auto simp: class_None_eq class_Some_eq classes_def
      dest: FieldI1 FieldI2 elim!: quotientE intro: transymcl_sym transymcl_trans)
  then have *: "insert x Y \<in> classes (insert (x, y) Qeq)"
    by (auto simp: class_None_eq class_Some_eq classes_def  intro!: quotientI)
  moreover from * NS have "Y \<notin> classes (insert (x, y) Qeq)"
    using classes_disjoint[of Y "insert (x, y) Qeq" "insert x Y"] classes_cover[of Qeq]
    by (auto simp: class_None_eq class_Some_eq)
  moreover {
    fix Z
    assume Z: "Z \<noteq> Y" "Z \<in> classes Qeq"
    then obtain z where z: "z \<in> Field Qeq" "Z = transymcl Qeq `` {z}"
      by (auto elim!: quotientE simp: classes_def)
    with NS Z have "z \<in> Z" "z \<noteq> x" "z \<noteq> y" "(z, x) \<notin> transymcl Qeq" "(z, y) \<notin> transymcl Qeq"
      using classes_disjoint[of Z "Qeq" Y] classes_nonempty[of Qeq]
      by (auto simp: class_None_eq class_Some_eq disjoint_iff Field_transymcl_self
        dest: FieldI2 intro: transymcl_trans)
    with NS Z * have "transymcl Qeq `` {z} = transymcl (insert (x, y) Qeq) `` {z}"
      unfolding transymcl_insert
      by (intro trans[OF _ Un1_Image_triv[symmetric]]) (auto simp: class_None_eq class_Some_eq)
    with z have "Z \<in> classes (insert (x, y) Qeq)"
      by (auto simp: classes_def intro!: quotientI)
  }
  moreover {
    fix Z
    assume Z: "Z \<noteq> insert x Y" "Z \<in> classes (insert (x, y) Qeq)"
    then obtain z where z: "z \<in> Field (insert (x, y) Qeq)" "Z = transymcl (insert (x, y) Qeq) `` {z}"
      by (auto elim!: quotientE simp: classes_def)
    with NS Z * have "z \<in> Z" "z \<noteq> x" "z \<noteq> y" "(z, x) \<notin> transymcl (insert (x, y) Qeq)" "(z, y) \<notin> transymcl (insert (x, y) Qeq)"
      using classes_disjoint[of Z "insert (x, y) Qeq" "insert x Y"] classes_nonempty[of "insert (x, y) Qeq"]
      by (auto simp: class_None_eq class_Some_eq Field_transymcl_self transymcl_into(2)
        intro: transymcl_trans)
    with NS Z * have "transymcl (insert (x, y) Qeq) `` {z} = transymcl Qeq `` {z}"
      unfolding transymcl_insert
      by (intro trans[OF Un1_Image_triv]) (auto simp: class_None_eq class_Some_eq)
    with z \<open>z \<noteq> x\<close> \<open>z \<noteq> y\<close> have "Z \<in> classes Qeq"
      by (auto simp: classes_def intro!: quotientI)
  }
  ultimately have "classes (insert (x, y) Qeq) = classes Qeq - {Y} \<union> {insert x Y}"
    by blast
  with NS show ?case
    by auto
next
  case (SN X)
  then have "insert y X = transymcl (insert (x, y) Qeq) `` {x}"
    unfolding transymcl_insert using FieldI1[of x _ "transymcl Qeq"]
    by (auto simp: class_None_eq class_Some_eq classes_def
      dest: FieldI1 FieldI2 elim!: quotientE intro: transymcl_sym transymcl_trans)
  then have *: "insert y X \<in> classes (insert (x, y) Qeq)"
    by (auto simp: class_None_eq class_Some_eq classes_def  intro!: quotientI)
  moreover from * SN have "X \<notin> classes (insert (x, y) Qeq)"
    using classes_disjoint[of X "insert (x, y) Qeq" "insert y X"] classes_cover[of Qeq]
    by (auto simp: class_None_eq class_Some_eq)
  moreover {
    fix Z
    assume Z: "Z \<noteq> X" "Z \<in> classes Qeq"
    then obtain z where z: "z \<in> Field Qeq" "Z = transymcl Qeq `` {z}"
      by (auto elim!: quotientE simp: classes_def)
    with SN Z have "z \<in> Z" "z \<noteq> x" "z \<noteq> y" "(z, x) \<notin> transymcl Qeq" "(z, y) \<notin> transymcl Qeq"
      using classes_disjoint[of Z "Qeq" X] classes_nonempty[of Qeq]
      by (auto simp: class_None_eq class_Some_eq disjoint_iff Field_transymcl_self
        dest: FieldI2 intro: transymcl_trans)
    with SN Z * have "transymcl Qeq `` {z} = transymcl (insert (x, y) Qeq) `` {z}"
      unfolding transymcl_insert
      by (intro trans[OF _ Un1_Image_triv[symmetric]]) (auto simp: class_None_eq class_Some_eq)
    with z have "Z \<in> classes (insert (x, y) Qeq)"
      by (auto simp: classes_def intro!: quotientI)
  }
  moreover {
    fix Z
    assume Z: "Z \<noteq> insert y X" "Z \<in> classes (insert (x, y) Qeq)"
    then obtain z where z: "z \<in> Field (insert (x, y) Qeq)" "Z = transymcl (insert (x, y) Qeq) `` {z}"
      by (auto elim!: quotientE simp: classes_def)
    with SN Z * have "z \<in> Z" "z \<noteq> x" "z \<noteq> y" "(z, x) \<notin> transymcl (insert (x, y) Qeq)" "(z, y) \<notin> transymcl (insert (x, y) Qeq)"
      using classes_disjoint[of Z "insert (x, y) Qeq" "insert y X"] classes_nonempty[of "insert (x, y) Qeq"]
      by (auto simp: class_None_eq class_Some_eq Field_transymcl_self transymcl_into(2)
        intro: transymcl_trans)
    with SN Z * have "transymcl (insert (x, y) Qeq) `` {z} = transymcl Qeq `` {z}"
      unfolding transymcl_insert
      by (intro trans[OF Un1_Image_triv]) (auto simp: class_None_eq class_Some_eq)
    with z \<open>z \<noteq> x\<close> \<open>z \<noteq> y\<close> have "Z \<in> classes Qeq"
      by (auto simp: classes_def intro!: quotientI)
  }
  ultimately have "classes (insert (x, y) Qeq) = classes Qeq - {X} \<union> {insert y X}"
    by blast
  with SN show ?case
    by auto
next
  case (SS X Y)
  moreover from SS have XY: "X \<in> classes Qeq" "Y \<in> classes Qeq" "x \<in> X" "y \<in> Y" "x \<in> Field Qeq" "y \<in> Field Qeq"
    using class_None_eq[of x Qeq] class_None_eq[of y Qeq] class_Some_eq[of x Qeq X] class_Some_eq[of y Qeq Y]
    by auto
  moreover from XY have "X = Y \<Longrightarrow> classes (insert (x, y) Qeq) = classes Qeq"
    unfolding classes_def
    by (subst transymcl_insert_same_class)
      (auto simp: classes_def insert_absorb elim!: quotientE intro: transymcl_sym transymcl_trans)
  moreover
  {
    assume neq: "X \<noteq> Y"
    from XY have "X = transymcl Qeq `` {x}" "Y = transymcl Qeq `` {y}"
      by (auto simp: classes_def elim!: quotientE intro: transymcl_sym transymcl_trans)
    with XY have XY_eq:
      "X \<union> Y = transymcl (insert (x, y) Qeq) `` {x}" 
      "X \<union> Y = transymcl (insert (x, y) Qeq) `` {y}"
      unfolding transymcl_insert by auto
    then have *: "X \<union> Y \<in> classes (insert (x, y) Qeq)"
      by (auto simp: classes_def quotientI)
    moreover
    from * XY neq have **: "X \<notin> classes (insert (x, y) Qeq)" "Y \<notin> classes (insert (x, y) Qeq)"
      using classes_disjoint[OF *, of X] classes_disjoint[OF *, of Y] classes_disjoint[of X Qeq Y]
      by auto
    moreover {
      fix Z
      assume Z: "Z \<noteq> X" "Z \<noteq> Y" "Z \<in> classes Qeq"
      then obtain z where z: "z \<in> Field Qeq" "Z = transymcl Qeq `` {z}"
        by (auto elim!: quotientE simp: classes_def)
      with XY Z have "z \<in> Z" "z \<noteq> x" "z \<noteq> y" "(z, x) \<notin> transymcl Qeq" "(z, y) \<notin> transymcl Qeq"
        using classes_disjoint[of Z Qeq X] classes_disjoint[of Z Qeq Y] classes_nonempty[of Qeq]
        by (auto simp: disjoint_iff Field_transymcl_self dest: FieldI2 intro: transymcl_trans)
      with XY Z * have "transymcl Qeq `` {z} = transymcl (insert (x, y) Qeq) `` {z}"
        unfolding transymcl_insert
        by (intro trans[OF _ Un1_Image_triv[symmetric]]) (auto simp: class_None_eq class_Some_eq)
      with z have "Z \<in> classes (insert (x, y) Qeq)"
        by (auto simp: classes_def intro!: quotientI)
    }
    moreover {
      fix Z
      assume Z: "Z \<noteq> X \<union> Y" "Z \<in> classes (insert (x, y) Qeq)"
      then obtain z where z: "z \<in> Field (insert (x, y) Qeq)" "Z = transymcl (insert (x, y) Qeq) `` {z}"
        by (auto elim!: quotientE simp: classes_def)
      with XY Z neq XY_eq have "z \<in> Z" "z \<noteq> x" "z \<noteq> y" "(z, x) \<notin> transymcl (insert (x, y) Qeq)" "(z, y) \<notin> transymcl (insert (x, y) Qeq)"
        using classes_disjoint[OF *, of Z] classes_disjoint[of X Qeq Y]
        by (auto simp: Field_transymcl_self)
      with XY Z * have "transymcl (insert (x, y) Qeq) `` {z} = transymcl Qeq `` {z}"
        unfolding transymcl_insert
        by (intro trans[OF Un1_Image_triv]) (auto simp: class_None_eq class_Some_eq)
      with z \<open>z \<noteq> x\<close> \<open>z \<noteq> y\<close> have "Z \<in> classes Qeq"
        by (auto simp: classes_def intro!: quotientI)
    }
    ultimately have "classes (insert (x, y) Qeq) = classes Qeq - {X, Y} \<union> {X \<union> Y}"
      by blast
  }
  ultimately show ?case
    by auto
qed

lemma classes_intersect_find_not_None:
  assumes "\<forall>V\<in>classes (set xys). V \<inter> A \<noteq> {}" "xys \<noteq> []"
  shows "find (\<lambda>(x, y). x \<in> A \<or> y \<in> A) xys \<noteq> None"
proof -
  from assms(2) obtain x y where "(x, y) \<in> set xys" by (cases xys) auto
  with assms(1) obtain X where x: "class x (set xys) = Some X" "X \<inter> A \<noteq> {}"
    using ex_class[of "x" "set xys"]
    by (auto simp: class_Some_eq Field_def)
  then obtain a where "a \<in> A" "a \<in> X"
    by blast
  with x have "(a, x) \<in> transymcl (set xys)"
    using equiv_class_eq[OF equiv_transymcl, of _ _ "set xys"]
    by (fastforce simp: class_Some_eq classes_def elim!: quotientE)
  then obtain b where "(a, b) \<in> symcl (set xys)"
    by (auto simp: transymcl_def elim: converse_tranclE)
  with \<open>a \<in> A\<close> show ?thesis
    by (auto simp: find_None_iff symcl_def)
qed

(*<*)
end
(*>*)