theory LaunchburyNoBH
imports Terms Heap
begin

inductive reds :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ [\<Down>] _" [50,50] 50)
where
  Lambda: "(x, (Lam [y]. e)) # \<Gamma> [\<Down>] (x, (Lam [y]. e)) # \<Gamma>" 
 | Application: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,delete x \<Delta>,x,e,y,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,delete x \<Delta>,x,e,y,\<Theta>);
      (n, e) # (x, App (Var n) y) # \<Gamma> [\<Down>] (n, Lam [z]. e') # \<Delta>;
      (x, e'[z ::= y]) # delete x \<Delta> [\<Down>] \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> [\<Down>] \<Theta>" 
 | Variable: "\<lbrakk>
      (y, e) \<in> set ((x, Var y) # \<Gamma>);
      (y, e) # delete y ((x, Var y) # \<Gamma>) [\<Down>] (y, z) # \<Delta>;
      set \<Delta>' = set ((y,z) # \<Delta>)
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # \<Gamma> [\<Down>] (x,z) # delete x \<Delta>'"
 | Let: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, Let as body);
      distinctVars (asToHeap as);
      set \<Gamma>' = set (asToHeap as @ \<Gamma>);
      (x, body) # \<Gamma>' [\<Down>] \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Let as body) # \<Gamma> [\<Down>] \<Delta>"

equivariance reds

nominal_inductive reds
  avoids Application: "n" and "z"
  by (auto simp add: fresh_star_def fresh_Cons fresh_Pair exp_assn.fresh)

lemma VariableI:
  "\<lbrakk>
      (y, e) \<in> set ((x, Var y) # \<Gamma>);
      (y, e) # delete y ((x, Var y) # \<Gamma>) [\<Down>] (y, z) # \<Delta>;
      \<Delta>' = delete x ((y,z) # \<Delta>)
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # \<Gamma> [\<Down>] (x,z) # \<Delta>'"
      by (metis Variable)

lemma eval_test:
  "y \<noteq> x \<Longrightarrow> [(x, Let (ACons y (Lam [z]. Var z) ANil) (Var y))] [\<Down>] [(x, (Lam [z]. Var z)), (y, Lam [z]. Var z)]"
apply(auto intro!: Lambda Application VariableI Let
 simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_star_def exp_assn.bn_defs fresh_at_base)
done

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> z \<noteq> x \<Longrightarrow> [(x,  Let (ACons y (Lam [z]. Var z) ANil) (App (Var y) y))] [\<Down>] [(x, (Lam [z]. Var z)), (y, Lam [z]. Var z)]"
  apply (rule Let)
    apply (simp add: fresh_Pair fresh_Cons fresh_at_base  fresh_Nil exp_assn.fresh fresh_star_def exp_assn.bn_defs)
    apply simp
    apply (rule refl)
  apply (rule obtain_fresh[where x = "(asToHeap (ACons y (Lam [z]. Var z) ANil) @ [], [(y, Lam [z]. Var z)], x, Var y, y,
                        [(x, Lam [z]. Var z), (y, Lam [z]. Var z)], z)", standard])
  apply (rule Application[where z = z])
    apply (auto simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh)[1]
    defer
    defer
    apply (rule VariableI)
    apply auto[1]
   
    apply (auto simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_at_base)[1]
    apply (rule Lambda)
    apply (auto simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_at_base)[1]
    apply (auto simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_at_base)[1]
    apply (rule VariableI)
    apply simp
    apply (rule Lambda)
    apply (auto simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_at_base)[1]
    apply (auto simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_at_base)[1]
    apply (auto simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_at_base)[1]
  done

inductive distinct_reds :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ [\<Down>]d _" [50,50] 50)
where
  DLambda: "(x, (Lam [y]. e)) # \<Gamma> [\<Down>]d (x, (Lam [y]. e)) # \<Gamma>" 
 | DApplication: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,delete x \<Delta>,x,e,y,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,delete x \<Delta>,x,e,y,\<Theta>);

      (n, e) # (x, App (Var n) y) # \<Gamma> [\<Down>]d (n, Lam [z]. e') # \<Delta>;
      (x, e'[z ::= y]) # delete x \<Delta> [\<Down>]d \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> [\<Down>]d \<Theta>" 
 | DVariable: "\<lbrakk>
      (y, e) \<in> set ((x, Var y) # \<Gamma>);
      (y, e) # delete y ((x, Var y) # \<Gamma>) [\<Down>]d (y, z) # \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # \<Gamma> [\<Down>]d (x,z) # delete x ((y,z) # \<Delta>)"
 | DLet: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, Let as body);
      distinctVars (asToHeap as);
      (x, body) # asToHeap as @ \<Gamma> [\<Down>]d \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Let as body) # \<Gamma> [\<Down>]d \<Delta>"

equivariance distinct_reds

nominal_inductive distinct_reds
  avoids DApplication: "n" and "z"
  by (auto simp add: fresh_star_def fresh_Cons fresh_Pair exp_assn.fresh)


end
