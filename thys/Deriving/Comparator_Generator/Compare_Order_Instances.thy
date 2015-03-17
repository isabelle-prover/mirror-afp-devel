subsection \<open>Defining Compare-Order-Instances for Common Types\<close>

theory Compare_Order_Instances
imports
  Compare_Instances
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_Lexorder"
begin

text \<open>We now also instantiate class @{class compare_order} and not only @{class compare}.
  Here, we also prove that our definitions do not clash with existing orders on
  @{type list} and @{type prod}.
  
  For @{type sum} and @{type option} we just define the linear orders via their comparator.\<close>

derive compare_order sum option

instance list :: (compare_order)compare_order
proof
  note [simp] = le_of_comp_def lt_of_comp_def comparator_of_def
  show "le_of_comp (compare :: 'a list comparator) = op \<le>" 
    unfolding compare_list_def compare_is_comparator_of 
  proof (intro ext)
    fix xs ys :: "'a list"
    show "le_of_comp (comparator_list comparator_of) xs ys = (xs \<le> ys)"
    proof (induct xs arbitrary: ys)
      case (Nil ys)
      show ?case
        by (cases ys, simp_all)
    next
      case (Cons x xs yys) note IH = this
      thus ?case
      proof (cases yys)
        case Nil
        thus ?thesis by auto
      next
        case (Cons y ys)
        show ?thesis unfolding Cons
          using IH[of ys]
          by (cases x y rule: linorder_cases, auto)
      qed
    qed
  qed
  show "lt_of_comp (compare :: 'a list comparator) = op <" 
    unfolding compare_list_def compare_is_comparator_of 
  proof (intro ext)
    fix xs ys :: "'a list"
    show "lt_of_comp (comparator_list comparator_of) xs ys = (xs < ys)"
    proof (induct xs arbitrary: ys)
      case (Nil ys)
      show ?case
        by (cases ys, simp_all)
    next
      case (Cons x xs yys) note IH = this
      thus ?case
      proof (cases yys)
        case Nil
        thus ?thesis by auto
      next
        case (Cons y ys)
        show ?thesis unfolding Cons
          using IH[of ys]
          by (cases x y rule: linorder_cases, auto)
      qed
    qed
  qed
qed

instance prod :: (compare_order, compare_order)compare_order
proof
  note [simp] = le_of_comp_def lt_of_comp_def comparator_of_def
  show "le_of_comp (compare :: ('a,'b)prod comparator) = op \<le>" 
    unfolding compare_prod_def compare_is_comparator_of 
  proof (intro ext)
    fix xy1 xy2 :: "('a,'b)prod"
    show "le_of_comp (comparator_prod comparator_of comparator_of) xy1 xy2 = (xy1 \<le> xy2)"
      by (cases xy1, cases xy2, auto)
  qed
  show "lt_of_comp (compare :: ('a,'b)prod comparator) = op <" 
    unfolding compare_prod_def compare_is_comparator_of 
  proof (intro ext)
    fix xy1 xy2 :: "('a,'b)prod"
    show "lt_of_comp (comparator_prod comparator_of comparator_of) xy1 xy2 = (xy1 < xy2)"
      by (cases xy1, cases xy2, auto)
  qed
qed

end