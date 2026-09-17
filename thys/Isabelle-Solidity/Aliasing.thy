theory Aliasing
  imports Mcalc
begin

section \<open>Running Example\<close>

(*
  bool[1][1] memory x = [[false]];
  bool[1][1] memory y = [[false]];
  x[0] = y[0];
  y[0][0] = true;
  assert (x[0][0] == true);
*)

lemma (in Contract) example:
  "wp (do {
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''x'');
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad 0] (stackLookup (STR ''y'') [sint_monad 0]);
        assign_stack_monad (STR ''y'') [sint_monad 0,sint_monad 0] (true_monad)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint 0, Uint 0] cd = Some (adata.Value (Bool True))))
      (K (K True))
      s"
  apply wp+
              apply (auto simp add: is_Array_write alookup.simps)
  apply wp+
     apply (auto simp add: pred_memory_def)

  (*Aliasing*)
  apply (drule_tac ?is3.0 = "[Uint 0]" and ?l1.0=l in aliasing_1, simp, simp)
     apply (erule mlookup_mupdate, simp)
      apply (erule locations_write_1, simp add:alookup.simps)
     apply (erule mlookup_locations_write_2, simp add:alookup.simps)
      apply (erule mlookup_some_write_1, simp add:alookup.simps)
     apply (erule mlookup_loc_write_1, simp add:alookup.simps)
    apply (erule nth_some, simp)
    apply (rule mlookup_neq_write_1, assumption, simp)
     apply (erule mlookup_some_write_1, simp add:alookup.simps)
    apply (erule mlookup_loc_write_1, simp add:alookup.simps)
   apply (erule mlookup_nth_mupdate, simp)
   apply (erule mlookup_locations_write_4)
     apply (erule mlookup_some_write_1, simp add:alookup.simps)
    apply (erule locations_write_1,simp add: alookup.simps)
   apply (erule mlookup_locations_write_1,simp add: alookup.simps)
  (*Aliasing*)

  apply (rule pred_some_read)
   apply (erule read_mupdate_value)
    apply (erule disjoint_mupdate_1, simp, simp)
        apply (erule range_range_write_2)
        apply (erule range_range_write_1)
       apply (erule disjoint_range_write_2)
        apply (erule range_range_write_1)
       apply (erule disjoint_range_write_1)
      apply (erule range_range_write_1)
     apply (erule disjoint_range_write_1)
    apply (erule range_range_disj_write)
    apply (erule range_range_write_1)
   apply (erule read_mupdate_1, simp, simp)
      apply (erule disjoint_range_write_2)
       apply (erule range_range_write_1)
      apply (erule disjoint_range_write_1)
     apply (erule range_range_disj_write)
     apply (erule range_range_write_1)
    apply (erule write_read_2)
    apply (erule write_read_1)
   apply (erule write_read_1)
  by (simp add:alookup.simps)

lemma (in Contract) example_short:
  "wp (do {
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''x'');
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad 0] (stackLookup (STR ''y'') [sint_monad 0]);
        assign_stack_monad (STR ''y'') [sint_monad 0,sint_monad 0] (true_monad)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint 0, Uint 0] cd = Some (adata.Value (Bool True))))
      (K (K True))
      s"
  apply wp+
              apply (auto simp add: is_Array_write alookup.simps)
  apply wp+
     apply (auto simp add: pred_memory_def)

  (*Aliasing*)
  apply (drule_tac ?is3.0 = "[Uint 0]" and ?l1.0=l in aliasing_1, simp, simp)
     apply (mc+, (auto simp add:alookup.simps)[1])+
  apply (rule pred_some_read)
   apply mc+
  by (simp add:alookup.simps)

end