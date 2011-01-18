with Rmd;
--# inherit Rmd;

--# main_program;
procedure Main
   --# derives ;
is
   subtype MsgIdx is Rmd.Message_Index Range 1..1;
   subtype Msg is Rmd.Message(MsgIdx);
   X: Msg;
   H: Rmd.Chain;
begin
   X := Msg'(others => Rmd.Block'(others => 0));
   Rmd.Hash(X, H);
end Main;
