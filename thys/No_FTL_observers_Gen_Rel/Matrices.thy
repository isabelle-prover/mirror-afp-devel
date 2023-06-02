(*
   Mike Stannett
   Date: June 2020
   Updated: Jan 2023
*)

section \<open> Matrices \<close>

text \<open>This theory defines $4 \times 4$ matrices.\<close>

theory Matrices
  imports Vectors
begin


record 'a Matrix =
  trow :: "'a Point"
  xrow :: "'a Point"
  yrow :: "'a Point"
  zrow :: "'a Point"

class Matrices = Vectors
begin

fun applyMatrix :: "'a Matrix \<Rightarrow> 'a Point \<Rightarrow> 'a Point"
  where "applyMatrix m p = \<lparr> tval = dot (trow m) p, xval = dot (xrow m) p,
                             yval = dot (yrow m) p, zval = dot (zrow m) p \<rparr>"

fun tcol :: "'a Matrix \<Rightarrow> 'a Point"
  where "tcol m = \<lparr> tval = tval (trow m), xval = tval (xrow m), 
                    yval = tval (yrow m), zval = tval (zrow m) \<rparr>"

fun xcol :: "'a Matrix \<Rightarrow> 'a Point"
  where "xcol m = \<lparr> tval = xval (trow m), xval = xval (xrow m), 
                    yval = xval (yrow m), zval = xval (zrow m) \<rparr>" 

fun ycol :: "'a Matrix \<Rightarrow> 'a Point"
  where "ycol m = \<lparr> tval = yval (trow m), xval = yval (xrow m), 
                    yval = yval (yrow m), zval = yval (zrow m) \<rparr>"

fun zcol :: "'a Matrix \<Rightarrow> 'a Point"
  where "zcol m = \<lparr> tval = zval (trow m), xval = zval (xrow m), 
                    yval = zval (yrow m), zval = zval (zrow m) \<rparr>"

fun transpose :: "'a Matrix \<Rightarrow> 'a Matrix"
  where "transpose m = \<lparr> trow = (tcol m), xrow = (xcol m), 
                         yrow = (ycol m), zrow = (zcol m) \<rparr>"

fun mprod :: "'a Matrix \<Rightarrow> 'a Matrix \<Rightarrow> 'a Matrix"
  where "mprod m1 m2 = 
           transpose \<lparr> trow = applyMatrix m1 (tcol m2), xrow = applyMatrix m1 (xcol m2),
                       yrow = applyMatrix m1 (ycol m2), zrow = applyMatrix m1 (zcol m2) \<rparr>"

end (* of class Matrices *)


end (* of theory Matrices *)

