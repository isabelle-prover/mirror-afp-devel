theory HF_SetCat_Interp
imports HF_SetCat
begin

  text\<open>
    Here we demonstrate the possibility of making a top-level interpretation of
    the \<open>ZFC_set_cat\<close> locale.  See theory \<open>SetCat_Interp\<close> for further discussion on
    why we do this.
\<close>

  interpretation HF_Sets: hfsetcat .

end
