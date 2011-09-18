{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Natural where {

import Data.Array.ST;

newtype Natural = Natural Integer deriving (Eq, Show, Read);

instance Num Natural where {
  fromInteger k = Natural (if k >= 0 then k else 0);
  Natural n + Natural m = Natural (n + m);
  Natural n - Natural m = fromInteger (n - m);
  Natural n * Natural m = Natural (n * m);
  abs n = n;
  signum _ = 1;
  negate n = error "negate Natural";
};

instance Ord Natural where {
  Natural n <= Natural m = n <= m;
  Natural n < Natural m = n < m;
};

instance Ix Natural where {
  range (Natural n, Natural m) = map Natural (range (n, m));
  index (Natural n, Natural m) (Natural q) = index (n, m) q;
  inRange (Natural n, Natural m) (Natural q) = inRange (n, m) q;
  rangeSize (Natural n, Natural m) = rangeSize (n, m);
};

instance Real Natural where {
  toRational (Natural n) = toRational n;
};

instance Enum Natural where {
  toEnum k = fromInteger (toEnum k);
  fromEnum (Natural n) = fromEnum n;
};

instance Integral Natural where {
  toInteger (Natural n) = n;
  divMod n m = quotRem n m;
  quotRem (Natural n) (Natural m)
    | (m == 0) = (0, Natural n)
    | otherwise = (Natural k, Natural l) where (k, l) = quotRem n m;
};

}
