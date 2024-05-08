subsection "Denotational equalities regarding reduction" 

theory DenotEqualitiesFSet
  imports DenotCongruenceFSet
begin

theorem eval_prim[simp]: assumes e1:"E e1 = E (ENat n1)" and e2:"E e2 = E (ENat n2)" 
  shows "E(EPrim f e1 e2)=E(ENat (f n1 n2))"
    using e1 e2 by auto 

theorem eval_ifz[simp]: assumes e1: "E e1  = E(ENat 0)" shows "E(EIf e1 e2 e3) = E(e3)"
  using e1 by auto 
 
theorem eval_ifnz[simp]: assumes e1: "E(e1) = E(ENat n)" and nz: "n \<noteq> 0"
  shows "E(EIf e1 e2 e3) = E(e2)"
  using e1 nz by auto 

theorem eval_app_lam: assumes vv: "is_val v"
  shows "E(EApp (ELam x e) v) = E (subst x v e)"
  using beta reduce_pres_denot vv by auto

end
