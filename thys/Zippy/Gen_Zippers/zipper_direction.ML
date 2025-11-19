(*  Title:      Zippy/zipper_direction.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_DIRECTION =
sig
  datatype direction = Zip | Unzip | Left | Right | Up | Down
end

structure Zipper_Direction : ZIPPER_DIRECTION =
struct
datatype direction = Zip | Unzip | Left | Right | Up | Down
end
