module Analysis.Common where
import qualified Data.Set as D

cartesian p s1 s2 = D.unions $ D.toList $ D.map (\x -> D.map (p x) s2) s1
