structure Ltl_Dt : sig 
  datatype 'a ltlc = LTLcTrue 
                   | LTLcFalse 
                   | LTLcProp of 'a 
                   | LTLcNeg of 'a ltlc
                   | LTLcAnd of 'a ltlc * 'a ltlc 
                   | LTLcOr of 'a ltlc * 'a ltlc 
                   | LTLcImplies of 'a ltlc * 'a ltlc 
                   | LTLcIff of 'a ltlc * 'a ltlc
                   | LTLcNext of 'a ltlc 
                   | LTLcFinal of 'a ltlc 
                   | LTLcGlobal of 'a ltlc 
                   | LTLcUntil of 'a ltlc * 'a ltlc 
                   | LTLcRelease of 'a ltlc * 'a ltlc;
end = struct
  open LTL;
end;
